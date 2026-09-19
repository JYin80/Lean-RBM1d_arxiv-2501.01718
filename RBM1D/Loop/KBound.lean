/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.SumZero
import RBM1D.Propagator.LongDiff

/-!
# Lemma 3.11: the bound on `K^(π)`

Paper pp.41, 45–48.

**(3.43)**, the short-range property of the single-molecule self-energy: for `π = ∅` every
internal edge joins equal charges, so it is a short edge `Θ_{t m²} - 1`, which decays
exponentially on the scale of the bulk gap `|1 - t m²| ≥ √k`.  The self-energy is the tree value
with *identity* boundary edges (`selfW_eq_treeValW_one`), so the tree bound of Corollary 3.5
applies verbatim (`norm_SigmaPi_empty_le`).
-/

namespace RBM

open Finset Cor35

section SelfDecay

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The self-energy is the tree value with identity boundary edges. -/
theorem selfW_eq_treeValW_one (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (d : Fin n → ZMod L) :
    selfW L F E d = treeValW L F d (fun _ => 1) E := by
  simp only [selfW, treeValW, Matrix.one_apply]

variable (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
include hL hE

/-- The internal edges of a single-molecule tree (`π = ∅`) are short: both ends carry the same
charge, and the edge `Θ_{t m(s)²} - 1` decays on the scale of the bulk gap. -/
theorem norm_selfEdge_le {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (s : Bool) (x y : ZMod L) :
    ‖(thetaEdge L (mSigma E) t s s - 1) x y‖ ≤
      (2 * cTwo52 / Real.sqrt k + 1) *
        Real.exp (-(cZero * Real.sqrt (Real.sqrt k) * zdist L (x - y))) := by
  have hm1 := norm_mSigma_le_one hE
  let m' : Bool → ℂ := fun b => mSigma E (if b then s else !s)
  have hm1' : ∀ b, ‖m' b‖ ≤ 1 := fun b => hm1 _
  have hgap' : Real.sqrt k ≤ ‖1 - (t : ℂ) * (m' true * m' true)‖ := by
    simp only [m', ite_true]
    exact gap_mSigma hk0 hk1 hEk ht0 ht1.le s
  have h := (norm_thetaEdge_le hL hm1' ht0 ht1 (Real.sqrt_pos.2 hk0) hgap' x y).2
  have e : thetaEdge L (mSigma E) t s s = thetaEdge L m' t true true := by
    simp only [thetaEdge, m', ite_true]
  rw [e]
  exact h

/-- **(3.43)**: the single-molecule self-energy is short-ranged,
`|Σ^(∅)(t,σ,d)| ≤ C e^{-c ‖d_i - d_j‖}` for every pair `i, j`, with `C, c` depending only on `n`
and the bulk parameter `k` (`|E| ≤ 2 - k`), uniformly in `L` and `0 ≤ t < 1`. -/
theorem norm_SigmaPi_empty_le {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Fin n → Bool) (hn : 2 ≤ n) (d : Fin n → ZMod L)
    (i j : Fin n) :
    ‖SigmaPi L (mSigma E) t σ ∅ d‖ ≤
      cor35Const n (Real.sqrt k) *
        Real.exp (-(cor35Rate (Real.sqrt k) * zdist L (d i - d j))) := by
  set δ := Real.sqrt k with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.2 hk0
  have hκ : 0 < cZero * Real.sqrt δ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hB : 1 ≤ 2 * cTwo52 / δ + 1 := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / δ := by positivity
    linarith
  set X := (2 * cTwo52 / δ + 1) ^ (n + n * n) *
    (2 / (1 - Real.exp (-(cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))))) ^ (n * n) *
    Real.exp (-(cZero * Real.sqrt δ / 4 * zdist L (d i - d j)))
  have hF : ∀ F ∈ TSPlong n σ ∅, ‖selfE L (mSigma E) t σ F d‖ ≤ X := by
    intro F hF
    obtain ⟨hFT, hFl⟩ := mem_TSPlong.1 hF
    rw [selfE, selfW_eq_treeValW_one]
    refine norm_treeValW_le (isTSP_of_mem_TSP hFT) hn d _ _ hB hκ (fun v x y => ?_)
      (fun e x y => ?_) i j
    · exact (norm_one_apply_le _ x y).trans (le_mul_of_one_le_left (Real.exp_pos _).le hB)
    · have hs : σ e.1.1 = σ e.1.2 := by
        by_contra hne
        have : e.1 ∈ Flong F σ := mem_Flong.2 ⟨e.2, hne⟩
        rw [hFl] at this
        simp at this
      rw [← hs]
      exact norm_selfEdge_le hL hE hk0 hk1 hEk ht0 ht1 _ x y
  have hX : 0 ≤ X := by
    have := one_le_two_div (lam := cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))
      (by have : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
            have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
          have := cZero_pos
          positivity)
    positivity
  have hcard : ((TSPlong n σ ∅).card : ℝ) ≤ (TSP n).card := by
    exact_mod_cast card_le_card (TSPlong_subset σ ∅)
  calc ‖SigmaPi L (mSigma E) t σ ∅ d‖
      ≤ ∑ F ∈ TSPlong n σ ∅, ‖selfE L (mSigma E) t σ F d‖ := norm_sum_le _ _
    _ ≤ ∑ _F ∈ TSPlong n σ ∅, X := sum_le_sum hF
    _ = (TSPlong n σ ∅).card * X := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (TSP n).card * X := by gcongr
    _ = _ := by simp only [X, cor35Const, cor35Rate]; ring

end SelfDecay

section Taylor

/-! ### A discrete Taylor split on the cycle

For `f : ZMod L → ℂ`, a centre `c` and a shift `s`:
`f(c+s) = f(c) + o(c,s) + e(c,s)`, with the odd part `o = (f(c+s) - f(c-s))/2` and the even
remainder `e = (f(c+s) + f(c-s))/2 - f(c)`.  With `k = ‖s‖`, `|o| ≤ k sup|∇f|` and
`e = ½ ∑_{j<k} ∑_{i<2j+1} Δf(c-j+i)` (a double telescoping sum of second differences). -/

variable {L : ℕ}

/-- The odd part of `f` at `c` in the direction `s`. -/
noncomputable def oddPart (f : ZMod L → ℂ) (c s : ZMod L) : ℂ := (f (c + s) - f (c - s)) / 2

/-- The even remainder of `f` at `c` in the direction `s`. -/
noncomputable def evenPart (f : ZMod L → ℂ) (c s : ZMod L) : ℂ :=
  (f (c + s) + f (c - s)) / 2 - f c

/-- The second difference `Δf(u) = f(u+1) + f(u-1) - 2f(u)`. -/
noncomputable def lap (f : ZMod L → ℂ) (u : ZMod L) : ℂ := f (u + 1) + f (u - 1) - 2 * f u

theorem apply_add_eq (f : ZMod L → ℂ) (c s : ZMod L) :
    f (c + s) = f c + oddPart f c s + evenPart f c s := by
  unfold oddPart evenPart; ring

theorem oddPart_neg (f : ZMod L → ℂ) (c s : ZMod L) : oddPart f c (-s) = -oddPart f c s := by
  unfold oddPart; rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring

theorem evenPart_neg (f : ZMod L → ℂ) (c s : ZMod L) : evenPart f c (-s) = evenPart f c s := by
  unfold evenPart; rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring

@[simp] theorem oddPart_zero (f : ZMod L → ℂ) (c : ZMod L) : oddPart f c 0 = 0 := by
  simp [oddPart]

@[simp] theorem evenPart_zero (f : ZMod L → ℂ) (c : ZMod L) : evenPart f c 0 = 0 := by
  simp [evenPart]

/-- Telescoping along the cycle. -/
theorem apply_add_natCast_sub (f : ZMod L → ℂ) (c : ZMod L) (k : ℕ) :
    f (c + k) - f c = ∑ j ∈ range k, (f (c + j + 1) - f (c + j)) := by
  have h := Finset.sum_range_sub (fun j : ℕ => f (c + (j : ZMod L))) k
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at h
  exact h.symm

/-- Every shift is `±‖s‖`. -/
theorem eq_natCast_or_neg [NeZero L] (s : ZMod L) :
    s = ((zdist L s : ℕ) : ZMod L) ∨ s = -((zdist L s : ℕ) : ZMod L) := by
  unfold zdist
  rcases min_cases s.val (L - s.val) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · left; exact (ZMod.natCast_zmod_val s).symm
  · right
    have hle : s.val ≤ L := (ZMod.val_lt s).le
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, neg_neg, ZMod.natCast_zmod_val]

/-- `|o(c,s)| ≤ ‖s‖ · M` if every first difference is at most `M`. -/
theorem norm_oddPart_le [NeZero L] (f : ZMod L → ℂ) {M : ℝ} (hM : ∀ u, ‖f (u + 1) - f u‖ ≤ M)
    (c s : ZMod L) : ‖oddPart f c s‖ ≤ zdist L s * M := by
  have key : ∀ k : ℕ, ‖oddPart f c (k : ZMod L)‖ ≤ k * M := by
    intro k
    have h := apply_add_natCast_sub f (c - k) (2 * k)
    rw [show c - (k : ZMod L) + ((2 * k : ℕ) : ZMod L) = c + k by push_cast; ring] at h
    unfold oddPart
    rw [h, norm_div, Complex.norm_ofNat]
    calc ‖∑ j ∈ range (2 * k), (f (c - k + j + 1) - f (c - k + j))‖ / 2
        ≤ (∑ _j ∈ range (2 * k), M) / 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun j _ => hM _)
      _ = k * M := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  rcases eq_natCast_or_neg s with h | h
  · calc ‖oddPart f c s‖ = ‖oddPart f c ((zdist L s : ℕ) : ZMod L)‖ := by conv_lhs => rw [h]
      _ ≤ _ := key _
  · calc ‖oddPart f c s‖ = ‖oddPart f c ((zdist L s : ℕ) : ZMod L)‖ := by
          conv_lhs => rw [h]
          rw [oddPart_neg, norm_neg]
      _ ≤ _ := key _

/-- The even remainder as a double telescoping sum of second differences. -/
theorem evenPart_natCast_eq (f : ZMod L → ℂ) (c : ZMod L) (k : ℕ) :
    evenPart f c (k : ZMod L) =
      (1 / 2 : ℂ) * ∑ j ∈ range k, ∑ i ∈ range (2 * j + 1), lap f (c - j + i) := by
  induction k with
  | zero => simp [evenPart]
  | succ k ih =>
    rw [sum_range_succ, mul_add, ← ih]
    set D : ZMod L → ℂ := fun u => f (u + 1) - f u
    have h := apply_add_natCast_sub D (c - k - 1) (2 * k + 1)
    have e1 : c - k - 1 + ((2 * k + 1 : ℕ) : ZMod L) = c + k := by push_cast; ring
    rw [e1] at h
    have e2 : ∀ i : ℕ, lap f (c - k + i)
        = D (c - k - 1 + i + 1) - D (c - k - 1 + i) := by
      intro i
      have h1 : c - (k : ZMod L) - 1 + i + 1 = c - k + i := by ring
      have h2 : c - (k : ZMod L) - 1 + i = c - k + i - 1 := by ring
      rw [h1, h2]
      simp only [D, lap, sub_add_cancel]
      ring
    simp only [e2, Nat.cast_succ]
    rw [← h]
    simp only [D, evenPart]
    rw [show c + ((k : ZMod L) + 1) = c + k + 1 by ring, show c - ((k : ZMod L) + 1) = c - k - 1 by
      ring, show c - k - 1 + 1 = c - (k : ZMod L) by ring]
    ring

/-- `|e(c,s)| ≤ ½ ∑_{j<k} ∑_{i<2j+1} M(c-j+i)` for any pointwise bound `M` on the second
differences, `k = ‖s‖`. -/
theorem norm_evenPart_le [NeZero L] (f : ZMod L → ℂ) (M : ZMod L → ℝ)
    (hM : ∀ u, ‖lap f u‖ ≤ M u) (c s : ZMod L) :
    ‖evenPart f c s‖ ≤
      (1 / 2 : ℝ) * ∑ j ∈ range (zdist L s), ∑ i ∈ range (2 * j + 1), M (c - j + i) := by
  have key : ∀ k : ℕ, ‖evenPart f c (k : ZMod L)‖ ≤
      (1 / 2 : ℝ) * ∑ j ∈ range k, ∑ i ∈ range (2 * j + 1), M (c - j + i) := by
    intro k
    rw [evenPart_natCast_eq, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    gcongr
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
    exact (norm_sum_le _ _).trans (sum_le_sum fun i _ => hM _)
  rcases eq_natCast_or_neg s with h | h
  · calc ‖evenPart f c s‖ = ‖evenPart f c ((zdist L s : ℕ) : ZMod L)‖ := by conv_lhs => rw [h]
      _ ≤ _ := key _
  · calc ‖evenPart f c s‖ = ‖evenPart f c ((zdist L s : ℕ) : ZMod L)‖ := by
          conv_lhs => rw [h]
          rw [evenPart_neg]
      _ ≤ _ := key _

theorem sum_range_two_mul_add_one (k : ℕ) : ∑ j ∈ range k, ((2 * j + 1 : ℕ) : ℝ) = k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- With a uniform bound `M₀` on the second differences, `|e(c,s)| ≤ ‖s‖² M₀ / 2`. -/
theorem norm_evenPart_le_const [NeZero L] (f : ZMod L → ℂ) {M₀ : ℝ} (hM : ∀ u, ‖lap f u‖ ≤ M₀)
    (c s : ZMod L) : ‖evenPart f c s‖ ≤ (zdist L s : ℝ) ^ 2 * M₀ / 2 := by
  refine (norm_evenPart_le f (fun _ => M₀) hM c s).trans (le_of_eq ?_)
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [← sum_mul, show ∑ j ∈ range (zdist L s), ((2 * j + 1 : ℕ) : ℝ) = _ from
    sum_range_two_mul_add_one _]
  ring

/-- The number of the points `c - j + i` (`j < k`, `i < 2j+1`) that hit `a`; its sum over the
centre `c` is `k²`. -/
noncomputable def hitCount (a : ZMod L) (k : ℕ) (c : ZMod L) : ℝ :=
  ∑ j ∈ range k, ∑ i ∈ range (2 * j + 1), if c - j + i = a then (1 : ℝ) else 0

theorem sum_hitCount [NeZero L] (a : ZMod L) (k : ℕ) : ∑ c : ZMod L, hitCount a k c = k ^ 2 := by
  unfold hitCount
  rw [sum_comm]
  simp_rw [sum_comm (s := univ)]
  have h : ∀ j i : ℕ, ∑ c : ZMod L, (if c - j + i = a then (1 : ℝ) else 0) = 1 := by
    intro j i
    have e : ∀ c : ZMod L, (c - j + i = a) = (c = a + j - i) := fun c =>
      propext ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [h, sum_const, card_range, nsmul_eq_mul, mul_one]
  exact_mod_cast sum_range_two_mul_add_one k

/-- **The even remainder, diagonal split**: if the second differences are at most `M_off` except
at one point `a`, where they are at most `M_d`, then
`|e(c,s)| ≤ ‖s‖² M_off / 2 + (M_d / 2) · hitCount a ‖s‖ c`. -/
theorem norm_evenPart_le_split [NeZero L] (f : ZMod L → ℂ) (a : ZMod L) {Moff Md : ℝ}
    (hoff : ∀ u, u ≠ a → ‖lap f u‖ ≤ Moff) (hd : ‖lap f a‖ ≤ Md) (hMoff : 0 ≤ Moff)
    (c s : ZMod L) :
    ‖evenPart f c s‖ ≤ (zdist L s : ℝ) ^ 2 * Moff / 2 + Md / 2 * hitCount a (zdist L s) c := by
  have hM : ∀ u, ‖lap f u‖ ≤ Moff + Md * (if u = a then 1 else 0) := by
    intro u
    by_cases hu : u = a
    · subst hu; simp only [ite_true, mul_one]; linarith
    · simp only [hu, ite_false, mul_zero, add_zero]; exact hoff u hu
  refine (norm_evenPart_le f _ hM c s).trans (le_of_eq ?_)
  set K := zdist L s
  have h1 : ∑ j ∈ range K, ∑ i ∈ range (2 * j + 1), (Moff + Md * (if c - j + i = a then 1 else 0))
      = ∑ j ∈ range K, ∑ _i ∈ range (2 * j + 1), Moff + Md * hitCount a K c := by
    simp only [sum_add_distrib, hitCount, mul_sum]
  have h2 : ∑ j ∈ range K, ∑ _i ∈ range (2 * j + 1), Moff = (K : ℝ) ^ 2 * Moff := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [← sum_mul, sum_range_two_mul_add_one]
  rw [h1, h2]
  ring

end Taylor

section Center

/-! ### Centring at the first point, and the weighted self-energy

Write `d = c + s` with `c = d₀` and `s₀ = 0` (`sum_center`).  By translation invariance the
self-energy only sees `s`, and (3.43) makes it summable against any polynomial weight
(`sum_pinned_SigmaPi_le`). -/

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

variable (L n) in
/-- The configurations pinned at the first point: `s₀ = 0`. -/
def pinned : Finset (Fin n → ZMod L) := univ.filter fun s => s 0 = 0

/-- `∑_d F(d) = ∑_c ∑_{s₀ = 0} F(s + c)`. -/
theorem sum_center {M : Type*} [AddCommMonoid M] (F : (Fin n → ZMod L) → M) :
    ∑ d, F d = ∑ c : ZMod L, ∑ s ∈ pinned L n, F (fun v => s v + c) := by
  rw [← Finset.sum_fiberwise univ (fun d => d 0) F]
  refine sum_congr rfl fun c _ => ?_
  refine Finset.sum_nbij' (fun d v => d v - c) (fun s v => s v + c) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd
    simp [pinned, hd]
  · intro s hs
    simp only [pinned, mem_filter, mem_univ, true_and] at hs
    simp [hs]
  · intro d _; funext v; simp
  · intro s _; funext v; simp
  · intro d _; congr 1; funext v; simp

/-- `∑_x e^{-λ‖x‖} (1 + ‖x‖)^p`, bounded uniformly in `L`. -/
noncomputable def polyExpSum (lam : ℝ) (p : ℕ) : ℝ :=
  p.factorial * (2 / lam) ^ p * Real.exp (lam / 2) * (2 * ((1 + lam / 2) / (lam / 2)))

theorem sum_exp_mul_pow_le {lam : ℝ} (hlam : 0 < lam) (p : ℕ) :
    ∑ x : ZMod L, Real.exp (-(lam * zdist L x)) * ((1 : ℝ) + zdist L x) ^ p
      ≤ polyExpSum lam p := by
  set K := (p.factorial : ℝ) * (2 / lam) ^ p * Real.exp (lam / 2)
  have hpt : ∀ x : ZMod L, Real.exp (-(lam * zdist L x)) * ((1 : ℝ) + zdist L x) ^ p
      ≤ K * Real.exp (-(lam / 2 * zdist L x)) := by
    intro x
    set y : ℝ := (zdist L x : ℝ)
    have hy : 0 ≤ y := Nat.cast_nonneg _
    have h := Real.pow_div_factorial_le_exp (x := lam * (1 + y) / 2) (by positivity) p
    have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    rw [div_le_iff₀ hf] at h
    have h' : (1 + y) ^ p ≤ K * Real.exp (lam * y / 2) := by
      have e1 : (lam * (1 + y) / 2) ^ p = (lam / 2) ^ p * (1 + y) ^ p := by rw [← mul_pow]; ring_nf
      have e2 : Real.exp (lam * (1 + y) / 2) = Real.exp (lam / 2) * Real.exp (lam * y / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1, e2] at h
      have hl : 0 < (lam / 2) ^ p := by positivity
      have e3 : K = p.factorial * Real.exp (lam / 2) / (lam / 2) ^ p := by
        simp only [K]; rw [div_pow, div_pow]; field_simp
      rw [e3, div_mul_eq_mul_div, le_div_iff₀ hl]
      linarith
    calc Real.exp (-(lam * y)) * (1 + y) ^ p
        ≤ Real.exp (-(lam * y)) * (K * Real.exp (lam * y / 2)) := by gcongr
      _ = K * Real.exp (-(lam / 2 * y)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  calc ∑ x : ZMod L, Real.exp (-(lam * zdist L x)) * ((1 : ℝ) + zdist L x) ^ p
      ≤ ∑ x : ZMod L, K * Real.exp (-(lam / 2 * zdist L x)) := sum_le_sum fun x _ => hpt x
    _ = K * ∑ x : ZMod L, Real.exp (-(lam / 2 * zdist L x)) := by rw [mul_sum]
    _ ≤ K * (2 * ((1 + lam / 2) / (lam / 2))) := by
        gcongr
        exact sum_exp_neg_zdist_le L (by positivity)
    _ = polyExpSum lam p := by simp only [K, polyExpSum]

/-- A pairwise decay with the first point gives a product decay:
`min_i C e^{-c x_i} ≤ C ∏_i e^{-(c/n) x_i}`. -/
theorem le_mul_prod_of_forall {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (x : Fin n → ℝ) {B : ℝ}
    (hB : ∀ i, B ≤ C * Real.exp (-(c * x i))) :
    B ≤ C * ∏ i, Real.exp (-(c / n * x i)) := by
  obtain ⟨i₀, -, hmax⟩ := exists_max_image univ x univ_nonempty
  refine (hB i₀).trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [← Real.exp_sum, Real.exp_le_exp, sum_neg_distrib, neg_le_neg_iff]
  calc ∑ i, c / n * x i ≤ ∑ _i : Fin n, c / n * x i₀ :=
        sum_le_sum fun i _ => by gcongr; exact hmax i (mem_univ _)
    _ = c * x i₀ := by
        have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

variable (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
include hL hE

/-- The constant of the weighted bound on the self-energy. -/
noncomputable def sigWeightConst (n : ℕ) (k : ℝ) (p : ℕ) : ℝ :=
  cor35Const n (Real.sqrt k) * polyExpSum (cor35Rate (Real.sqrt k) / n) p ^ n

/-- **(3.43), summed against a polynomial weight**: pinning `s₀ = 0`,
`∑_s |Σ^(∅)(t,σ,s)| ∏_v (1 + ‖s_v‖)^p ≤ C(n,k,p)`, uniformly in `L` and `0 ≤ t < 1`. -/
theorem sum_pinned_SigmaPi_le {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Fin n → Bool) (hn : 2 ≤ n) (p : ℕ) :
    ∑ s ∈ pinned L n, ‖SigmaPi L (mSigma E) t σ ∅ s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ p
      ≤ sigWeightConst n k p := by
  set C₃ := cor35Const n (Real.sqrt k)
  set r := cor35Rate (Real.sqrt k)
  have hδ : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hC₃ : 0 ≤ C₃ := cor35Const_nonneg n hδ
  have hr : 0 < r / n := by
    have := cZero_pos
    have : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
    have := Real.sqrt_pos.2 hδ
    simp only [r, cor35Rate]
    positivity
  set h : ZMod L → ℝ := fun x => Real.exp (-(r / n * zdist L x)) * ((1 : ℝ) + zdist L x) ^ p
  have hh0 : ∀ x, 0 ≤ h x := fun x => by positivity
  have hpt : ∀ s ∈ pinned L n,
      ‖SigmaPi L (mSigma E) t σ ∅ s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ p ≤ C₃ * ∏ v, h (s v) := by
    intro s hs
    simp only [pinned, mem_filter, mem_univ, true_and] at hs
    have hg := le_mul_prod_of_forall (by simp only [r, cor35Rate]; have := cZero_pos; positivity) hC₃ (fun i => (zdist L (s i) : ℝ))
      (B := ‖SigmaPi L (mSigma E) t σ ∅ s‖) (c := r) fun i => by
        have := norm_SigmaPi_empty_le hL hE hk0 hk1 hEk ht0 ht1 σ hn s i 0
        rwa [hs, sub_zero] at this
    calc ‖SigmaPi L (mSigma E) t σ ∅ s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ p
        ≤ (C₃ * ∏ i, Real.exp (-(r / n * zdist L (s i)))) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ p := by
          gcongr
      _ = C₃ * ∏ v, h (s v) := by rw [mul_assoc, ← prod_mul_distrib]
  calc ∑ s ∈ pinned L n, ‖SigmaPi L (mSigma E) t σ ∅ s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ p
      ≤ ∑ s ∈ pinned L n, C₃ * ∏ v, h (s v) := sum_le_sum hpt
    _ ≤ ∑ s : Fin n → ZMod L, C₃ * ∏ v, h (s v) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun s _ _ =>
          mul_nonneg hC₃ (prod_nonneg fun v _ => hh0 _)
    _ = C₃ * ∏ _v : Fin n, ∑ x : ZMod L, h x := by
        rw [← mul_sum, Fintype.prod_sum]
    _ ≤ C₃ * ∏ _v : Fin n, polyExpSum (r / n) p := by
        gcongr with v
        exact sum_exp_mul_pow_le hr p
    _ = sigWeightConst n k p := by
        rw [prod_const, card_univ, Fintype.card_fin]; rfl

end Center

section Expand

/-! ### Expanding `K^(∅)` around the first point

`K^(∅)_a = ∑_c ∑_{s₀=0} Σ^(∅)(s) ∏_v f_v(c + s_v)` with `f_v = (Θ_v)_{a_v, ·}`, and each factor
splits as `f_v(c) + o_v(c, s_v) + e_v(c, s_v)`; multiplying out, `K^(∅)` is a sum over the
`3ⁿ` choices `τ : Fin n → Fin 3` (`Kpi_empty_expand`). -/

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The three Taylor pieces: `0 ↦ f(c)`, `1 ↦ o(c,x)`, `2 ↦ e(c,x)`. -/
noncomputable def taylorTerm (f : ZMod L → ℂ) (j : Fin 3) (c x : ZMod L) : ℂ :=
  ![f c, oddPart f c x, evenPart f c x] j

omit [NeZero L] [NeZero n] in
theorem sum_taylorTerm (f : ZMod L → ℂ) (c x : ZMod L) :
    ∑ j : Fin 3, taylorTerm f j c x = f (c + x) := by
  rw [Fin.sum_univ_three, apply_add_eq f c x]
  rfl

/-- A long edge: opposite charges give `ξ = t |m|² = t`. -/
theorem thetaEdge_of_ne {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) {s s' : Bool} (h : s ≠ s') :
    thetaEdge L (mSigma E) t s s' = Theta L (t : ℂ) := by
  rw [thetaEdge, mSigma_mul_of_ne hE h, mul_one]

variable (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
include hL hE

/-- **The expansion**: `K^(∅)_a = ∑_τ ∑_c ∑_{s₀ = 0} Σ^(∅)(s) ∏_v T_{τ_v}(f_v; c, s_v)`. -/
theorem Kpi_empty_expand {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Fin n → Bool)
    (a : Fin n → ZMod L) :
    Kpi L (mSigma E) t σ a ∅ =
      ∑ τ : Fin n → Fin 3, ∑ c : ZMod L, ∑ s ∈ pinned L n,
        SigmaPi L (mSigma E) t σ ∅ s *
          ∏ v, taylorTerm (fun y => thetaEdge L (mSigma E) t (σ v) (σ (v + 1)) (a v) y)
            (τ v) c (s v) := by
  have hm := norm_mul_mSigma_lt_one (le_of_lt hE) ht0 ht1
  rw [Kpi_eq_sum_SigmaPi L, sum_center (M := ℂ)]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← mul_sum, SigmaPi_add_const (mSigma E) hm hL σ ∅ s c,
    ← Fintype.prod_sum (fun v (j : Fin 3) =>
      taylorTerm (fun y => thetaEdge L (mSigma E) t (σ v) (σ (v + 1)) (a v) y) j c (s v))]
  congr 1
  refine prod_congr rfl fun v _ => ?_
  rw [sum_taylorTerm, add_comm c (s v)]

end Expand

section RTerms

/-! ### The remainder terms

Abstract kernels `f_v` with `|f_v| ≤ A`, `∑|f_v| ≤ Λ`, `|∇f_v| ≤ 3/2`, `|Δf_v| ≤ 3` and
`|Δf_v| ≤ M_off` away from one point `a_v`.  If `Λ M_off ≤ C₁ A` and `Λ ≤ C₂ A²`, then every
choice `τ` containing an even piece or two odd pieces costs at most `C A^{n-1} ∏_v (1+‖s_v‖)²`
after summing over the centre. -/

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The pointwise bound on any Taylor piece. -/
theorem norm_taylorTerm_le (f : ZMod L → ℂ) {A : ℝ} (hA : 3 / 2 ≤ A) (hsup : ∀ y, ‖f y‖ ≤ A)
    (hgrad : ∀ u, ‖f (u + 1) - f u‖ ≤ 3 / 2) (hlap : ∀ u, ‖lap f u‖ ≤ 3) (j : Fin 3)
    (c x : ZMod L) : ‖taylorTerm f j c x‖ ≤ A * ((1 : ℝ) + zdist L x) ^ 2 := by
  have hk : (0 : ℝ) ≤ zdist L x := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ (1 + zdist L x) ^ 2 := by nlinarith
  have h2 : (zdist L x : ℝ) ≤ (1 + zdist L x) ^ 2 := by nlinarith
  have h3 : (zdist L x : ℝ) ^ 2 ≤ (1 + zdist L x) ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  fin_cases j
  · calc ‖taylorTerm f 0 c x‖ = ‖f c‖ := rfl
      _ ≤ A := hsup c
      _ ≤ A * ((1 : ℝ) + zdist L x) ^ 2 := le_mul_of_one_le_right hA0 h1
  · calc ‖taylorTerm f 1 c x‖ = ‖oddPart f c x‖ := rfl
      _ ≤ zdist L x * (3 / 2) := norm_oddPart_le f hgrad c x
      _ ≤ ((1 : ℝ) + zdist L x) ^ 2 * A := by gcongr
      _ = _ := mul_comm _ _
  · calc ‖taylorTerm f 2 c x‖ = ‖evenPart f c x‖ := rfl
      _ ≤ (zdist L x : ℝ) ^ 2 * 3 / 2 := norm_evenPart_le_const f hlap c x
      _ = (zdist L x : ℝ) ^ 2 * (3 / 2) := by ring
      _ ≤ ((1 : ℝ) + zdist L x) ^ 2 * A := by gcongr
      _ = _ := mul_comm _ _

omit [NeZero L] [NeZero n] in
/-- At the pinned point the shift is `0`, so only the value survives. -/
theorem norm_taylorTerm_zero_le (f : ZMod L → ℂ) (j : Fin 3) (c : ZMod L) :
    ‖taylorTerm f j c 0‖ ≤ ‖f c‖ := by
  fin_cases j
  · exact le_rfl
  · show ‖oddPart f c 0‖ ≤ _; rw [oddPart_zero, norm_zero]; exact norm_nonneg _
  · show ‖evenPart f c 0‖ ≤ _; rw [evenPart_zero, norm_zero]; exact norm_nonneg _

omit [NeZero n] in
/-- Pulling out a sup bound: `∑_c F(c) ∏_{v∈T} G_v(c) ≤ (∑_c F) ∏_{v∈T} S_v`. -/
theorem sum_mul_prod_le (F : ZMod L → ℝ) (G : Fin n → ZMod L → ℝ) (T : Finset (Fin n))
    (S : Fin n → ℝ) (hF : ∀ c, 0 ≤ F c) (hG0 : ∀ v c, 0 ≤ G v c) (hGS : ∀ v ∈ T, ∀ c, G v c ≤ S v) :
    ∑ c, F c * ∏ v ∈ T, G v c ≤ (∑ c, F c) * ∏ v ∈ T, S v := by
  rw [Finset.sum_mul]
  refine sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (hF c)
  exact Finset.prod_le_prod₀ (fun v _ => hG0 v c) fun v hv => hGS v hv c

/-- **The remainder terms**: a choice `τ` with an even piece, or with two odd pieces, costs at
most `(C₁/2 + 3/2 + 9C₂/4) A^{n-1} ∏_v (1+‖s_v‖)²` after summing over the centre. -/
theorem sum_prod_taylor_le (f : Fin n → ZMod L → ℂ) (a : Fin n → ZMod L) {A Λ Moff C₁ C₂ : ℝ}
    (hA : 3 / 2 ≤ A) (hsup : ∀ v y, ‖f v y‖ ≤ A) (hl1 : ∀ v, ∑ y, ‖f v y‖ ≤ Λ)
    (hgrad : ∀ v u, ‖f v (u + 1) - f v u‖ ≤ 3 / 2) (hlap : ∀ v u, ‖lap (f v) u‖ ≤ 3)
    (hoff : ∀ v u, u ≠ a v → ‖lap (f v) u‖ ≤ Moff) (hMoff : 0 ≤ Moff)
    (h₁ : Λ * Moff ≤ C₁ * A) (h₂ : Λ ≤ C₂ * A ^ 2) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (τ : Fin n → Fin 3) (hτ : (∃ v, τ v = 2) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ τ v₁ = 1 ∧ τ v₂ = 1)
    (s : Fin n → ZMod L) (hs : s 0 = 0) :
    ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
      (C₁ / 2 + 3 / 2 + 9 / 4 * C₂) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
  set X : Fin n → ZMod L → ℝ := fun v c => ‖taylorTerm (f v) (τ v) c (s v)‖ with hXdef
  set w : Fin n → ℝ := fun v => ((1 : ℝ) + zdist L (s v)) ^ 2 with hwdef
  set k : Fin n → ℝ := fun v => (zdist L (s v) : ℝ) with hkdef
  have hk0 : ∀ v, 0 ≤ k v := fun v => Nat.cast_nonneg _
  have hw1 : ∀ v, 1 ≤ w v := fun v => by simp only [w]; nlinarith [hk0 v]
  have hwk : ∀ v, k v ≤ w v := fun v => by simp only [w, k]; nlinarith [hk0 v]
  have hwk2 : ∀ v, k v ^ 2 ≤ w v := fun v => by simp only [w, k]; nlinarith [hk0 v]
  have hw0 : ∀ v, 0 ≤ w v := fun v => by linarith [hw1 v]
  have hA0 : 0 ≤ A := by linarith
  have hX0 : ∀ v c, 0 ≤ X v c := fun v c => norm_nonneg _
  have hXA : ∀ v c, X v c ≤ A * w v := fun v c =>
    norm_taylorTerm_le (f v) hA (hsup v) (hgrad v) (hlap v) (τ v) c (s v)
  have hXz : ∀ c, X 0 c ≤ ‖f 0 c‖ := fun c => by
    show ‖taylorTerm (f 0) (τ 0) c (s 0)‖ ≤ _
    rw [hs]; exact norm_taylorTerm_zero_le (f 0) (τ 0) c
  have hl1' : ∑ c, ‖f 0 c‖ ≤ Λ := hl1 0
  have hRHS : 0 ≤ (C₁ / 2 + 3 / 2 + 9 / 4 * C₂) * A ^ (n - 1) * ∏ v, w v := by
    have := prod_nonneg fun v (_ : v ∈ univ) => hw0 v
    positivity
  have hW : ∀ v₁, v₁ ≠ 0 → ∏ v, w v = w 0 * (w v₁ * ∏ v ∈ (univ.erase 0).erase v₁, w v) := by
    intro v₁ h
    rw [mul_prod_erase _ _ (mem_erase.2 ⟨h, mem_univ _⟩), mul_prod_erase _ _ (mem_univ _)]
  have hP : ∀ c v₁, v₁ ≠ 0 →
      ∏ v, X v c = X 0 c * (X v₁ c * ∏ v ∈ (univ.erase 0).erase v₁, X v c) := by
    intro c v₁ h
    rw [mul_prod_erase _ (fun v => X v c) (mem_erase.2 ⟨h, mem_univ _⟩),
      mul_prod_erase _ (fun v => X v c) (mem_univ _)]
  rcases hτ with ⟨v₁, h2⟩ | ⟨v₁, v₂, h12, h1, h2⟩
  · -- an even piece at `v₁`
    by_cases h01 : v₁ = 0
    · subst h01
      have hz : ∀ c, X 0 c = 0 := fun c => by
        show ‖taylorTerm (f 0) (τ 0) c (s 0)‖ = 0
        rw [h2, hs]; show ‖evenPart (f 0) c 0‖ = 0; rw [evenPart_zero, norm_zero]
      calc ∑ c, ∏ v, X v c = ∑ c : ZMod L, (0 : ℝ) := by
            refine sum_congr rfl fun c _ => ?_
            exact prod_eq_zero (mem_univ 0) (hz c)
        _ ≤ _ := by rw [sum_const_zero]; exact hRHS
    set T := (univ.erase (0 : Fin n)).erase v₁
    have hT : T.card = n - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨h01, mem_univ _⟩), card_erase_of_mem (mem_univ _),
        card_univ, Fintype.card_fin]
      omega
    set F : ZMod L → ℝ := fun c =>
      ‖f 0 c‖ * ((k v₁) ^ 2 * Moff / 2 + 3 / 2 * hitCount (a v₁) (zdist L (s v₁)) c)
    have hF0 : ∀ c, 0 ≤ F c := fun c => by
      have : 0 ≤ hitCount (a v₁) (zdist L (s v₁)) c := by
        unfold hitCount; positivity
      have := hk0 v₁
      positivity
    have hev : ∀ c, X v₁ c ≤ (k v₁) ^ 2 * Moff / 2 + 3 / 2 * hitCount (a v₁) (zdist L (s v₁)) c := by
      intro c
      have := norm_evenPart_le_split (f v₁) (a v₁) (hoff v₁) (hlap v₁ (a v₁)) hMoff c (s v₁)
      show ‖taylorTerm (f v₁) (τ v₁) c (s v₁)‖ ≤ _
      rw [h2]
      show ‖evenPart (f v₁) c (s v₁)‖ ≤ _
      linarith
    have hstep : ∀ c, ∏ v, X v c ≤ F c * ∏ v ∈ T, X v c := by
      intro c
      rw [hP c v₁ h01, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hXz c) (hev c) (hX0 _ _) (norm_nonneg _))
        (prod_nonneg fun v _ => hX0 v c)
    have hsumF : ∑ c, F c ≤ (C₁ / 2 + 3 / 2) * A * (k v₁) ^ 2 := by
      have hh : ∑ c, ‖f 0 c‖ * hitCount (a v₁) (zdist L (s v₁)) c ≤ A * (k v₁) ^ 2 := by
        calc ∑ c, ‖f 0 c‖ * hitCount (a v₁) (zdist L (s v₁)) c
            ≤ ∑ c, A * hitCount (a v₁) (zdist L (s v₁)) c := by
              refine sum_le_sum fun c _ => ?_
              have : 0 ≤ hitCount (a v₁) (zdist L (s v₁)) c := by unfold hitCount; positivity
              exact mul_le_mul_of_nonneg_right (hsup 0 c) this
          _ = A * (k v₁) ^ 2 := by rw [← mul_sum, sum_hitCount]
      have e : ∑ c, F c = (k v₁) ^ 2 * Moff / 2 * ∑ c, ‖f 0 c‖
          + 3 / 2 * ∑ c, ‖f 0 c‖ * hitCount (a v₁) (zdist L (s v₁)) c := by
        simp only [F, mul_add, sum_add_distrib, mul_sum]
        congr 1 <;> refine sum_congr rfl fun c _ => by ring
      rw [e]
      have hk2 := sq_nonneg (k v₁)
      calc (k v₁) ^ 2 * Moff / 2 * ∑ c, ‖f 0 c‖
            + 3 / 2 * ∑ c, ‖f 0 c‖ * hitCount (a v₁) (zdist L (s v₁)) c
          ≤ (k v₁) ^ 2 / 2 * (Λ * Moff) + 3 / 2 * (A * (k v₁) ^ 2) := by
            have : (k v₁) ^ 2 * Moff / 2 * ∑ c, ‖f 0 c‖ ≤ (k v₁) ^ 2 * Moff / 2 * Λ := by
              gcongr
            nlinarith
        _ ≤ (k v₁) ^ 2 / 2 * (C₁ * A) + 3 / 2 * (A * (k v₁) ^ 2) := by gcongr
        _ = (C₁ / 2 + 3 / 2) * A * (k v₁) ^ 2 := by ring
    calc ∑ c, ∏ v, X v c ≤ ∑ c, F c * ∏ v ∈ T, X v c := sum_le_sum fun c _ => hstep c
      _ ≤ (∑ c, F c) * ∏ v ∈ T, (A * w v) :=
          sum_mul_prod_le F X T _ hF0 hX0 fun v _ c => hXA v c
      _ ≤ ((C₁ / 2 + 3 / 2) * A * (k v₁) ^ 2) * (A ^ (n - 2) * ∏ v ∈ T, w v) := by
          rw [prod_mul_distrib, prod_const, hT]
          gcongr
      _ = (C₁ / 2 + 3 / 2) * (A * A ^ (n - 2)) * ((k v₁) ^ 2 * ∏ v ∈ T, w v) := by ring
      _ ≤ (C₁ / 2 + 3 / 2) * A ^ (n - 1) * (w 0 * (w v₁ * ∏ v ∈ T, w v)) := by
          have hn2 : A * A ^ (n - 2) = A ^ (n - 1) := by
            rw [← pow_succ']; congr 1
            have : 2 ≤ n := by
              have := Fin.pos_iff_ne_zero.2 h01
              have := v₁.isLt
              omega
            omega
          rw [hn2]
          have hPT : 0 ≤ ∏ v ∈ T, w v := prod_nonneg fun v _ => hw0 v
          have hkey : (k v₁) ^ 2 * ∏ v ∈ T, w v ≤ w 0 * (w v₁ * ∏ v ∈ T, w v) :=
            calc (k v₁) ^ 2 * ∏ v ∈ T, w v ≤ w v₁ * ∏ v ∈ T, w v :=
                  mul_le_mul_of_nonneg_right (hwk2 v₁) hPT
              _ = 1 * (w v₁ * ∏ v ∈ T, w v) := by ring
              _ ≤ w 0 * (w v₁ * ∏ v ∈ T, w v) :=
                  mul_le_mul_of_nonneg_right (hw1 0) (mul_nonneg (hw0 _) hPT)
          have hc : 0 ≤ (C₁ / 2 + 3 / 2) * A ^ (n - 1) := by positivity
          exact mul_le_mul_of_nonneg_left hkey hc
      _ = (C₁ / 2 + 3 / 2) * A ^ (n - 1) * ∏ v, w v := by rw [hW v₁ h01]
      _ ≤ _ := by
          have := prod_nonneg fun v (_ : v ∈ univ) => hw0 v
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hA0 _)) this
          nlinarith
  · -- two odd pieces
    by_cases h0 : v₁ = 0 ∨ v₂ = 0
    · have hτ0 : τ 0 = 1 := by rcases h0 with h | h <;> [rw [← h]; rw [← h]] <;> assumption
      have hz : ∀ c, X 0 c = 0 := fun c => by
        show ‖taylorTerm (f 0) (τ 0) c (s 0)‖ = 0
        rw [hτ0, hs]; show ‖oddPart (f 0) c 0‖ = 0; rw [oddPart_zero, norm_zero]
      calc ∑ c, ∏ v, X v c = ∑ c : ZMod L, (0 : ℝ) := by
            refine sum_congr rfl fun c _ => ?_
            exact prod_eq_zero (mem_univ 0) (hz c)
        _ ≤ _ := by rw [sum_const_zero]; exact hRHS
    push Not at h0
    obtain ⟨h01, h02⟩ := h0
    have hn3 : 3 ≤ n := by
      have := v₁.isLt; have := v₂.isLt
      have : (v₁ : ℕ) ≠ 0 := fun h => h01 (Fin.ext h)
      have : (v₂ : ℕ) ≠ 0 := fun h => h02 (Fin.ext h)
      have : (v₁ : ℕ) ≠ v₂ := fun h => h12 (Fin.ext h)
      omega
    have hm2 : v₂ ∈ (univ.erase (0 : Fin n)).erase v₁ :=
      mem_erase.2 ⟨h12.symm, mem_erase.2 ⟨h02, mem_univ _⟩⟩
    set T := ((univ.erase (0 : Fin n)).erase v₁).erase v₂
    have hT : T.card = n - 3 := by
      rw [card_erase_of_mem hm2, card_erase_of_mem (mem_erase.2 ⟨h01, mem_univ _⟩),
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      omega
    have hodd : ∀ v, τ v = 1 → ∀ c, X v c ≤ k v * (3 / 2) := by
      intro v hv c
      show ‖taylorTerm (f v) (τ v) c (s v)‖ ≤ _
      rw [hv]
      exact norm_oddPart_le (f v) (hgrad v) c (s v)
    have hstep : ∀ c, ∏ v, X v c ≤
        (‖f 0 c‖ * ((k v₁ * (3 / 2)) * (k v₂ * (3 / 2)))) * ∏ v ∈ T, X v c := by
      intro c
      rw [hP c v₁ h01, ← mul_prod_erase _ (fun v => X v c) hm2]
      have hPT : 0 ≤ ∏ v ∈ T, X v c := prod_nonneg fun v _ => hX0 v c
      have h1' := hodd v₁ h1 c
      have h2' := hodd v₂ h2 c
      calc X 0 c * (X v₁ c * (X v₂ c * ∏ v ∈ T, X v c))
          = (X 0 c * (X v₁ c * X v₂ c)) * ∏ v ∈ T, X v c := by ring
        _ ≤ (‖f 0 c‖ * ((k v₁ * (3 / 2)) * (k v₂ * (3 / 2)))) * ∏ v ∈ T, X v c := by
            refine mul_le_mul_of_nonneg_right ?_ hPT
            refine mul_le_mul (hXz c) (mul_le_mul h1' h2' (hX0 _ _) ?_) ?_ (norm_nonneg _)
            · have := hk0 v₁; positivity
            · exact mul_nonneg (hX0 _ _) (hX0 _ _)
    have hK : 0 ≤ (k v₁ * (3 / 2)) * (k v₂ * (3 / 2)) := by
      have := hk0 v₁; have := hk0 v₂; positivity
    have hPTw : 0 ≤ ∏ v ∈ T, w v := prod_nonneg fun v _ => hw0 v
    calc ∑ c, ∏ v, X v c
        ≤ ∑ c, (‖f 0 c‖ * ((k v₁ * (3 / 2)) * (k v₂ * (3 / 2)))) * ∏ v ∈ T, X v c :=
          sum_le_sum fun c _ => hstep c
      _ ≤ (∑ c, ‖f 0 c‖ * ((k v₁ * (3 / 2)) * (k v₂ * (3 / 2)))) * ∏ v ∈ T, (A * w v) :=
          sum_mul_prod_le _ X T _ (fun c => mul_nonneg (norm_nonneg _) hK) hX0
            fun v _ c => hXA v c
      _ = (∑ c, ‖f 0 c‖) * ((k v₁ * (3 / 2)) * (k v₂ * (3 / 2))) * (A ^ (n - 3) * ∏ v ∈ T, w v) := by
          rw [← sum_mul, prod_mul_distrib, prod_const, hT]
      _ ≤ (C₂ * A ^ 2) * ((k v₁ * (3 / 2)) * (k v₂ * (3 / 2))) * (A ^ (n - 3) * ∏ v ∈ T, w v) := by
          gcongr
          exact hl1'.trans h₂
      _ = 9 / 4 * C₂ * (A ^ 2 * A ^ (n - 3)) * (k v₁ * (k v₂ * ∏ v ∈ T, w v)) := by ring
      _ ≤ 9 / 4 * C₂ * A ^ (n - 1) * (w 0 * (w v₁ * (w v₂ * ∏ v ∈ T, w v))) := by
          rw [← pow_add, show 2 + (n - 3) = n - 1 by omega]
          have hc : 0 ≤ 9 / 4 * C₂ * A ^ (n - 1) := by positivity
          refine mul_le_mul_of_nonneg_left ?_ hc
          calc k v₁ * (k v₂ * ∏ v ∈ T, w v) ≤ w v₁ * (w v₂ * ∏ v ∈ T, w v) := by
                have := hk0 v₂
                gcongr
                · exact hwk v₁
                · exact hwk v₂
            _ = 1 * (w v₁ * (w v₂ * ∏ v ∈ T, w v)) := by ring
            _ ≤ w 0 * (w v₁ * (w v₂ * ∏ v ∈ T, w v)) :=
                mul_le_mul_of_nonneg_right (hw1 0) (by have := hw0 v₁; have := hw0 v₂; positivity)
      _ = 9 / 4 * C₂ * A ^ (n - 1) * ∏ v, w v := by
          rw [hW v₁ h01, ← mul_prod_erase _ w hm2]
      _ ≤ _ := by
          have := prod_nonneg fun v (_ : v ∈ univ) => hw0 v
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hA0 _)) this
          nlinarith

end RTerms

section Cancel

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **The first-order terms cancel**: for a self-energy that is even, `g(-s) = g(s)`, the odd part
of any kernel averages to zero. -/
theorem sum_pinned_odd_eq_zero (g : (Fin n → ZMod L) → ℂ) (hg : ∀ s, g (fun v => -s v) = g s)
    (f : ZMod L → ℂ) (c : ZMod L) (v₁ : Fin n) :
    ∑ s ∈ pinned L n, g s * oddPart f c (s v₁) = 0 := by
  set S := ∑ s ∈ pinned L n, g s * oddPart f c (s v₁)
  have h : S = -S := by
    have e : S = ∑ s ∈ pinned L n, g (fun v => -s v) * oddPart f c ((fun v => -s v) v₁) := by
      refine Finset.sum_nbij' (fun s v => -s v) (fun s v => -s v) ?_ ?_ ?_ ?_ ?_
      · intro s hs; simp only [pinned, mem_filter, mem_univ, true_and] at hs ⊢; rw [hs, neg_zero]
      · intro s hs; simp only [pinned, mem_filter, mem_univ, true_and] at hs ⊢; rw [hs, neg_zero]
      · intro s _; funext v; simp
      · intro s _; funext v; simp
      · intro s _; simp
    calc S = _ := e
      _ = ∑ s ∈ pinned L n, -(g s * oddPart f c (s v₁)) := by
          refine sum_congr rfl fun s _ => ?_
          rw [hg, oddPart_neg]; ring
      _ = -S := by rw [sum_neg_distrib]
  have h2 : (2 : ℂ) * S = 0 := by linear_combination h
  simpa using h2

/-- Translation invariance: `∑_d g(d) = L ∑_{s₀=0} g(s)`. -/
theorem sum_eq_mul_sum_pinned (g : (Fin n → ZMod L) → ℂ)
    (hg : ∀ s c, g (fun v => s v + c) = g s) :
    ∑ d, g d = L * ∑ s ∈ pinned L n, g s := by
  rw [sum_center (M := ℂ)]
  simp only [hg, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- The choice with a single odd piece at `v₁` contributes nothing. -/
theorem sum_taylor_single_eq_zero (g : (Fin n → ZMod L) → ℂ) (hg : ∀ s, g (fun v => -s v) = g s)
    (f : Fin n → ZMod L → ℂ) (τ : Fin n → Fin 3) (v₁ : Fin n) (h1 : τ v₁ = 1)
    (h0 : ∀ v, v ≠ v₁ → τ v = 0) :
    ∑ c : ZMod L, ∑ s ∈ pinned L n, g s * ∏ v, taylorTerm (f v) (τ v) c (s v) = 0 := by
  refine sum_eq_zero fun c _ => ?_
  have e : ∀ s : Fin n → ZMod L, ∏ v, taylorTerm (f v) (τ v) c (s v)
      = oddPart (f v₁) c (s v₁) * ∏ v ∈ univ.erase v₁, f v c := by
    intro s
    rw [← mul_prod_erase _ _ (mem_univ v₁)]
    congr 1
    · show taylorTerm (f v₁) (τ v₁) c (s v₁) = _; rw [h1]; rfl
    · refine prod_congr rfl fun v hv => ?_
      rw [h0 v (ne_of_mem_erase hv)]; rfl
  simp_rw [e, ← mul_assoc]
  rw [← sum_mul, sum_pinned_odd_eq_zero g hg, zero_mul]

/-- The choice with no odd or even piece factorises: `(∑_c ∏_v f_v(c)) (∑_{s₀=0} g(s))`. -/
theorem sum_taylor_zero_eq (g : (Fin n → ZMod L) → ℂ) (f : Fin n → ZMod L → ℂ)
    (τ : Fin n → Fin 3) (h0 : ∀ v, τ v = 0) :
    ∑ c : ZMod L, ∑ s ∈ pinned L n, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)
      = (∑ c : ZMod L, ∏ v, f v c) * ∑ s ∈ pinned L n, g s := by
  rw [sum_mul]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have : ∏ v, taylorTerm (f v) (τ v) c (s v) = ∏ v, f v c :=
    prod_congr rfl fun v _ => by rw [h0 v]; rfl
  rw [this, mul_comm]

end Cancel

section LongFacts

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L)
include hL

omit [NeZero L] hL in
/-- `η_t ℓ̂(t)² ≤ 1`, hence also `η_t ℓ̂(t) ≤ 1`. -/
theorem etaT_mul_ellHat_sq_le {E : ℝ} (hE : |E| ≤ 2) {t : ℝ} (ht1 : t < 1) :
    etaT E t * ellHat L (t : ℂ) ^ 2 ≤ 1 := by
  have h1t : 0 < 1 - t := by linarith
  have hη : etaT E t ≤ 1 - t := by rw [etaT_eq_zt_im]; exact zt_im_le hE ht1.le
  have hℓ : ellHat L (t : ℂ) ≤ 1 / Real.sqrt (1 - t) := by
    rw [ellHat_ofReal L ht1]; exact min_le_left _ _
  have hℓ0 : 0 ≤ ellHat L (t : ℂ) := by
    rw [ellHat_ofReal L ht1]
    exact le_min (by positivity) (Nat.cast_nonneg _)
  have hs : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  calc etaT E t * ellHat L (t : ℂ) ^ 2 ≤ (1 - t) * (1 / Real.sqrt (1 - t)) ^ 2 := by gcongr
    _ = 1 := by rw [div_pow, hs]; field_simp

theorem etaT_mul_ellHat_le {E : ℝ} (hE : |E| ≤ 2) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    etaT E t * ellHat L (t : ℂ) ≤ 1 := by
  have h := etaT_mul_ellHat_sq_le (L := L) hE ht1
  have hℓ1 : 1 ≤ ellHat L (t : ℂ) := one_le_ellHat L hL ht0 ht1
  have hη0 : 0 ≤ etaT E t := mul_nonneg (by linarith) (by rw [mE_im]; positivity)
  nlinarith

end LongFacts

section Alternating

/-! ### Lemma 3.11 for `π = ∅` and alternating charges

All boundary edges are long, `Θ_t` with `t` real.  With `A = 8e/(η_t ℓ̂)`:
`|Θ_t| ≤ A`, `∑|Θ_t| ≤ 1/η_t`, `|∇Θ_t| ≤ 3/2`, `|ΔΘ_t| ≤ 3` and `|ΔΘ_t| ≤ 24/ℓ̂` off the
diagonal (`Propagator/LongDiff.lean`); `η_t ℓ̂² ≤ 1` gives `1/η_t ≤ A²` and `(1/η_t)(24/ℓ̂) ≤ 2A`.
The leading term is `O(η_t)` by the sum-zero property (Lemma 3.10), the first-order terms vanish by
symmetry, and the rest are bounded by `sum_prod_taylor_le`. -/

theorem sigWeightConst_nonneg {n : ℕ} [NeZero n] {k : ℝ} (hk0 : 0 < k) (p : ℕ) :
    0 ≤ sigWeightConst n k p := by
  have hδ : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have h1 := cor35Const_nonneg n hδ
  have hr : 0 < cor35Rate (Real.sqrt k) / n := by
    have := cZero_pos
    have : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
    have := Real.sqrt_pos.2 hδ
    simp only [cor35Rate]
    positivity
  have h2 : 0 ≤ polyExpSum (cor35Rate (Real.sqrt k) / n) p := by
    unfold polyExpSum; positivity
  unfold sigWeightConst
  positivity

/-- **Lemma 3.11, (3.45), for `π = ∅` and alternating `σ`**:
`|K^(∅)_{t,σ,a}| ≤ C (η_t ℓ̂(t))^{-(n-1)}` for `|E| ≤ 2 - k`, `0 < t < 1`, uniformly in `L` and `a`. -/
theorem norm_Kpi_empty_alt_le {E k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {n : ℕ}
    [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ : Fin n → Bool, (∀ v, σ v ≠ σ (v + 1)) → ∀ a : Fin n → ZMod L,
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨Csz, hCsz0, hCsz⟩ := sum_zero hk0 hk1 hEk hn
  set SW := sigWeightConst n k 2
  have hSW : 0 ≤ SW := sigWeightConst_nonneg hk0 2
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨3 ^ n * ((Csz + 19 / 4 * SW) * e8 ^ (n - 1)), by positivity, ?_⟩
  intro L _ hL t ht0 ht1 σ halt a
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0 ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0 ht1
  have hηℓ2 : η * ℓ ^ 2 ≤ 1 := etaT_mul_ellHat_sq_le hE2 ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hA : 3 / 2 ≤ A := by
    have : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
    simp only [A, e8]; nlinarith
  -- the kernels
  set f : Fin n → ZMod L → ℂ := fun v y => thetaEdge L (mSigma E) t (σ v) (σ (v + 1)) (a v) y
  have hf : ∀ v y, f v y = Theta L (t : ℂ) (a v) y := fun v y => by
    simp only [f, thetaEdge_of_ne hE2 t (halt v)]
  have hsup : ∀ v y, ‖f v y‖ ≤ A := fun v y => by
    rw [hf, hAdef, hηdef, etaT_eq_zt_im, ← div_eq_mul_inv]
    exact norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _ _
  have hl1 : ∀ v, ∑ y, ‖f v y‖ ≤ η⁻¹ := fun v => by
    simp only [hf]; rw [hηdef, etaT_eq_zt_im]
    exact sum_norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _
  have hgrad : ∀ v u, ‖f v (u + 1) - f v u‖ ≤ 3 / 2 := fun v u => by
    rw [hf, hf, norm_sub_rev]; exact norm_Theta_sub_shift_le_uniform L hL ht0 ht1 _ _
  have hlap_eq : ∀ v u, ‖lap (f v) u‖ =
      ‖2 * Theta L (t : ℂ) (a v) u - Theta L (t : ℂ) (a v) (u + 1) - Theta L (t : ℂ) (a v) (u - 1)‖ :=
    fun v u => by
      simp only [lap, hf]
      rw [← norm_neg]; congr 1; ring
  have hlap : ∀ v u, ‖lap (f v) u‖ ≤ 3 := fun v u => by
    rw [hlap_eq]; exact norm_Theta_second_diff_le_three L hL ht0 ht1 _ _
  have hoff : ∀ v u, u ≠ a v → ‖lap (f v) u‖ ≤ 24 / ℓ := fun v u hu => by
    rw [hlap_eq]; exact norm_Theta_second_diff_le L hL ht0 ht1 (Ne.symm hu)
  have hMoff : 0 ≤ 24 / ℓ := by positivity
  have h₁ : η⁻¹ * (24 / ℓ) ≤ 2 * A := by
    rw [hAdef, show η⁻¹ * (24 / ℓ) = 24 * (η * ℓ)⁻¹ by field_simp]
    have : 0 < (η * ℓ)⁻¹ := by positivity
    simp only [e8]; nlinarith
  have h₂ : η⁻¹ ≤ 1 * A ^ 2 := by
    rw [one_mul, hAdef, mul_pow, inv_pow]
    rw [show η⁻¹ = (η * ℓ ^ 2) * ((η * ℓ) ^ 2)⁻¹ by field_simp]
    have : 0 < ((η * ℓ) ^ 2)⁻¹ := by positivity
    have : 1 ≤ e8 ^ 2 := by simp only [e8]; nlinarith
    nlinarith
  -- the three kinds of terms
  set g : (Fin n → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ ∅ s
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  have hgneg : ∀ s, g (fun v => -s v) = g s := fun s => SigmaPi_neg (mSigma E) hm hL σ ∅ s
  have hgadd : ∀ s c, g (fun v => s v + c) = g s := fun s c =>
    SigmaPi_add_const (mSigma E) hm hL σ ∅ s c
  set B := (Csz + 19 / 4 * SW) * A ^ (n - 1)
  have hterm : ∀ τ : Fin n → Fin 3,
      ‖∑ c : ZMod L, ∑ s ∈ pinned L n, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖ ≤ B := by
    intro τ
    have hA0 : 0 ≤ A := by linarith
    have hB0 : 0 ≤ B := by positivity
    by_cases hR : (∃ v, τ v = 2) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ τ v₁ = 1 ∧ τ v₂ = 1
    · -- the remainder terms
      have hW : ∀ s ∈ pinned L n, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
          (2 / 2 + 3 / 2 + 9 / 4 * 1) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
        intro s hs
        simp only [pinned, mem_filter, mem_univ, true_and] at hs
        exact sum_prod_taylor_le f a hA hsup hl1 hgrad hlap hoff hMoff h₁ h₂ (by norm_num)
          (by norm_num) τ hR s hs
      have hS := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ (by omega) 2
      calc ‖∑ c : ZMod L, ∑ s ∈ pinned L n, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖
          ≤ ∑ c : ZMod L, ∑ s ∈ pinned L n, ‖g s‖ * ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
            refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
            rw [norm_mul, norm_prod]
        _ = ∑ s ∈ pinned L n, ‖g s‖ * ∑ c : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            rw [sum_comm]; simp only [mul_sum]
        _ ≤ ∑ s ∈ pinned L n, ‖g s‖ *
              ((2 / 2 + 3 / 2 + 9 / 4 * 1) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
            sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hW s hs) (norm_nonneg _)
        _ = 19 / 4 * A ^ (n - 1) *
              ∑ s ∈ pinned L n, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
            rw [mul_sum]; refine sum_congr rfl fun s _ => by ring
        _ ≤ 19 / 4 * A ^ (n - 1) * SW := by gcongr
        _ ≤ B := by
            simp only [B]
            have : 0 ≤ Csz * A ^ (n - 1) := by positivity
            nlinarith
    push Not at hR
    obtain ⟨hn2, hn11⟩ := hR
    have key : ∀ j : Fin 3, j ≠ 2 → j ≠ 1 → j = 0 := by decide
    by_cases h1 : ∃ v₁, τ v₁ = 1
    · -- a single odd piece
      obtain ⟨v₁, hv₁⟩ := h1
      have h0 : ∀ v, v ≠ v₁ → τ v = 0 := fun v hv =>
        key _ (hn2 v) (hn11 v₁ v (Ne.symm hv) hv₁)
      rw [sum_taylor_single_eq_zero g hgneg f τ v₁ hv₁ h0, norm_zero]
      exact hB0
    · -- the leading term
      push Not at h1
      have h0 : ∀ v, τ v = 0 := fun v => key _ (hn2 v) (h1 v)
      rw [sum_taylor_zero_eq g f τ h0, norm_mul]
      have hlead : ‖∑ c : ZMod L, ∏ v, f v c‖ ≤ η⁻¹ * A ^ (n - 1) := by
        have hT : (univ.erase (0 : Fin n)).card = n - 1 := by
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        calc ‖∑ c : ZMod L, ∏ v, f v c‖ ≤ ∑ c : ZMod L, ‖f 0 c‖ * ∏ v ∈ univ.erase 0, ‖f v c‖ := by
              refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun c _ => ?_))
              rw [norm_prod, mul_prod_erase _ (fun v => ‖f v c‖) (mem_univ 0)]
          _ ≤ (∑ c : ZMod L, ‖f 0 c‖) * ∏ _v ∈ univ.erase (0 : Fin n), A :=
              sum_mul_prod_le _ (fun v c => ‖f v c‖) _ _ (fun c => norm_nonneg _)
                (fun v c => norm_nonneg _) fun v _ c => hsup v c
          _ ≤ η⁻¹ * A ^ (n - 1) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 0
      have hzero : ‖∑ s ∈ pinned L n, g s‖ ≤ Csz * η := by
        have h := hCsz L hL t ht0.le ht1 σ halt
        have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
        rw [sum_eq_mul_sum_pinned g hgadd, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul] at h
        exact h
      calc ‖∑ c : ZMod L, ∏ v, f v c‖ * ‖∑ s ∈ pinned L n, g s‖
          ≤ (η⁻¹ * A ^ (n - 1)) * (Csz * η) := by gcongr
        _ = Csz * A ^ (n - 1) := by field_simp
        _ ≤ B := by
            simp only [B]
            have : 0 ≤ SW * A ^ (n - 1) := by positivity
            nlinarith
  rw [Kpi_empty_expand hL hE ht0.le ht1 σ a]
  calc ‖∑ τ : Fin n → Fin 3, ∑ c : ZMod L, ∑ s ∈ pinned L n,
          g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖
      ≤ ∑ τ : Fin n → Fin 3, B := (norm_sum_le _ _).trans (sum_le_sum fun τ _ => hterm τ)
    _ = 3 ^ n * B := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring
    _ = 3 ^ n * ((Csz + 19 / 4 * SW) * e8 ^ (n - 1)) * (η * ℓ)⁻¹ ^ (n - 1) := by
        simp only [B, A, mul_pow]; ring

end Alternating

section NonAlternating

/-! ### Lemma 3.11 for `π = ∅` with a short boundary edge

If `σ_{v*} = σ_{v*+1}` for some `v*`, the boundary edge at `v*` is short: `|Θ_{t m²}|` decays on
the scale of the bulk gap, so its `ℓ¹` norm is `O(1)`.  Summing the centre with that edge and
bounding every other edge by its sup (`≤ C A`) gives `C A^{n-1}` without any expansion. -/

/-- A short edge `Θ_{t m(s)²}` decays on the scale of the bulk gap. -/
theorem norm_thetaEdge_same_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E k : ℝ} (hE : |E| < 2)
    (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s : Bool) (x y : ZMod L) :
    ‖thetaEdge L (mSigma E) t s s x y‖ ≤
      (2 * cTwo52 / Real.sqrt k + 1) *
        Real.exp (-(cZero * Real.sqrt (Real.sqrt k) * zdist L (x - y))) := by
  have hm1 := norm_mSigma_le_one hE
  let m' : Bool → ℂ := fun b => mSigma E (if b then s else !s)
  have hm1' : ∀ b, ‖m' b‖ ≤ 1 := fun b => hm1 _
  have hgap' : Real.sqrt k ≤ ‖1 - (t : ℂ) * (m' true * m' true)‖ := by
    simp only [m', ite_true]
    exact gap_mSigma hk0 hk1 hEk ht0 ht1.le s
  have h := (norm_thetaEdge_le hL hm1' ht0 ht1 (Real.sqrt_pos.2 hk0) hgap' x y).1
  have e : thetaEdge L (mSigma E) t s s = thetaEdge L m' t true true := by
    simp only [thetaEdge, m', ite_true]
  rw [e]
  exact h

/-- **Lemma 3.11, (3.45), for `π = ∅` and `σ` with a short boundary edge**. -/
theorem norm_Kpi_empty_short_le {E k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ : Fin n → Bool, (∃ v, σ v = σ (v + 1)) → ∀ a : Fin n → ZMod L,
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  set Bk := 2 * cTwo52 / Real.sqrt k + 1
  set κ := cZero * Real.sqrt (Real.sqrt k)
  have hδ : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hκ : 0 < κ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hBk : 1 ≤ Bk := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / Real.sqrt k := by positivity
    simp only [Bk]; linarith
  set S1 := 2 / (1 - Real.exp (-κ))
  have hS1 : 0 ≤ S1 := (zero_le_one.trans (one_le_two_div hκ))
  set SW0 := sigWeightConst n k 0
  have hSW0 : 0 ≤ SW0 := sigWeightConst_nonneg hk0 0
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨SW0 * (Bk * S1) * (Bk * e8) ^ (n - 1), by positivity, ?_⟩
  intro L _ hL t ht0 ht1 σ ⟨v₀, hv₀⟩ a
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0 ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0 ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hA1 : 1 ≤ A := by
    have : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
    simp only [A, e8]; nlinarith
  set θ : Fin n → Matrix (ZMod L) (ZMod L) ℂ := fun v => thetaEdge L (mSigma E) t (σ v) (σ (v + 1))
  -- every edge is at most `Bk A`
  have hsup : ∀ v x y, ‖θ v x y‖ ≤ Bk * A := by
    intro v x y
    by_cases hv : σ v = σ (v + 1)
    · have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ v) x y
      simp only [θ]; rw [← hv]
      calc _ ≤ Bk * Real.exp (-(κ * zdist L (x - y))) := h
        _ ≤ Bk * 1 := by
            gcongr; rw [Real.exp_le_one_iff, neg_nonpos]; positivity
        _ ≤ Bk * A := by gcongr
    · simp only [θ]
      rw [thetaEdge_of_ne hE2 t hv]
      have h := norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 x y
      rw [← etaT_eq_zt_im, div_eq_mul_inv] at h
      calc _ ≤ A := h
        _ = 1 * A := (one_mul A).symm
        _ ≤ Bk * A := by gcongr
  -- the short edge is summable
  have hl1 : ∀ x (s : ZMod L), ∑ c : ZMod L, ‖θ v₀ x (s + c)‖ ≤ Bk * S1 := by
    intro x s
    calc ∑ c : ZMod L, ‖θ v₀ x (s + c)‖
        ≤ ∑ c : ZMod L, Bk * Real.exp (-(κ * zdist L (c - (x - s)))) := by
          refine sum_le_sum fun c _ => ?_
          have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ v₀) x (s + c)
          simp only [θ]; rw [← hv₀]
          rw [show x - (s + c) = -(c - (x - s)) by ring, zdist_neg] at h
          exact h
      _ = Bk * ∑ c : ZMod L, Real.exp (-(κ * zdist L (c - (x - s)))) := by rw [mul_sum]
      _ ≤ Bk * S1 := by gcongr; exact sum_exp_zdist_le L hκ _
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  set g : (Fin n → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ ∅ s
  have hgadd : ∀ s c, g (fun v => s v + c) = g s := fun s c =>
    SigmaPi_add_const (mSigma E) hm hL σ ∅ s c
  have hSg := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ hn 0
  simp only [pow_zero, prod_const_one, mul_one] at hSg
  have hT : (univ.erase v₀).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [Kpi_eq_sum_SigmaPi L, sum_center (M := ℂ)]
  calc ‖∑ c : ZMod L, ∑ s ∈ pinned L n,
          SigmaPi L (mSigma E) t σ ∅ (fun v => s v + c) * ∏ v, θ v (a v) (s v + c)‖
      ≤ ∑ c : ZMod L, ∑ s ∈ pinned L n, ‖g s‖ * ∏ v, ‖θ v (a v) (s v + c)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
        rw [norm_mul, norm_prod, show SigmaPi L (mSigma E) t σ ∅ (fun v => s v + c) = g s from
          hgadd s c]
    _ = ∑ s ∈ pinned L n, ‖g s‖ * ∑ c : ZMod L, ∏ v, ‖θ v (a v) (s v + c)‖ := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ s ∈ pinned L n, ‖g s‖ * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by
        refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ∑ c : ZMod L, ∏ v, ‖θ v (a v) (s v + c)‖
            = ∑ c : ZMod L, ‖θ v₀ (a v₀) (s v₀ + c)‖ * ∏ v ∈ univ.erase v₀, ‖θ v (a v) (s v + c)‖ := by
              refine sum_congr rfl fun c _ => ?_
              rw [mul_prod_erase _ (fun v => ‖θ v (a v) (s v + c)‖) (mem_univ v₀)]
          _ ≤ (∑ c : ZMod L, ‖θ v₀ (a v₀) (s v₀ + c)‖) * ∏ _v ∈ univ.erase v₀, (Bk * A) :=
              sum_mul_prod_le _ (fun v c => ‖θ v (a v) (s v + c)‖) _ _ (fun c => norm_nonneg _)
                (fun v c => norm_nonneg _) fun v _ c => hsup v _ _
          _ ≤ (Bk * S1) * (Bk * A) ^ (n - 1) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 _ _
    _ = (∑ s ∈ pinned L n, ‖g s‖) * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by rw [sum_mul]
    _ ≤ SW0 * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by gcongr
    _ = SW0 * (Bk * S1) * (Bk * e8) ^ (n - 1) * (η * ℓ)⁻¹ ^ (n - 1) := by
        simp only [A, mul_pow]; ring

/-- **Lemma 3.11, (3.45), for `π = ∅`**: for `|E| ≤ 2 - k` there is `C = C(n,k)` with
`|K^(∅)_{t,σ,a}| ≤ C (η_t ℓ̂(t))^{-(n-1)}` for every `σ`, `a`, `0 < t < 1` and `L ≥ 3`. -/
theorem norm_Kpi_empty_le {E k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ : Fin n → Bool) (a : Fin n → ZMod L),
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_Kpi_empty_alt_le hk0 hk1 hEk hn
  obtain ⟨C₂, hC₂, h₂⟩ := norm_Kpi_empty_short_le hk0 hk1 hEk (n := n) (by omega)
  refine ⟨C₁ + C₂, by positivity, fun L _ hL t ht0 ht1 σ a => ?_⟩
  have hE : |E| < 2 := by linarith
  have hX : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
    have := etaT_pos hE ht1
    have := one_le_ellHat L hL ht0 ht1
    positivity
  by_cases halt : ∀ v, σ v ≠ σ (v + 1)
  · exact (h₁ L hL t ht0 ht1 σ halt a).trans (by nlinarith)
  · push Not at halt
    exact (h₂ L hL t ht0 ht1 σ halt a).trans (by nlinarith)

end NonAlternating

section LongCut

/-! ### Cutting at a long internal edge (pointwise)

`Θ_ξ - 1 = (ξ • 1) S Θ_ξ`, so the general cut `treeValW_cut` splits a tree containing the
internal edge `J` into the inside polygon, whose root leaf is the identity (the molecule `A(c₁)`
of (3.75)), and the outside polygon, a genuine tree whose glue leaf is `Θ_J`. -/

/-- Linearity in one leaf weight. -/
theorem treeValW_leaf_smul {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (a : Fin n → ZMod L) (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (v : Fin n) (c : ℂ) (X : Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L F a (Function.update M v (c • X)) E = c * treeValW L F a (Function.update M v X) E := by
  simp only [treeValW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prod_update_eq (fun w => M w (a w) (b ⟨leafPar F w, leafPar_mem F w⟩)) _ v
      (fun w hw => by rw [Function.update_of_ne hw]),
    prod_update_eq (fun w => M w (a w) (b ⟨leafPar F w, leafPar_mem F w⟩)) _ v
      (fun w hw => by rw [Function.update_of_ne hw]),
    Function.update_self, Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
variable (hL : 3 ≤ L) {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
  {J : Fin n × Fin n} (hJ : J ∈ F)
  (m : Bool → ℂ) (t : ℝ) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hF hn hJ hm

/-- **The cut at an internal edge, pointwise** (the decomposition (3.75)). -/
theorem treeValW_long_cut (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (σi : Fin (wIn J + 1) → Bool) (ai : ZMod L → Fin (wIn J + 1) → ZMod L)
    (σo : Fin (n - wIn J + 1) → Bool) (ao : ZMod L → Fin (n - wIn J + 1) → ZMod L)
    (hσi : ∀ i : Fin (wIn J + 1), σi i = σ (unShift J (i, i)).1)
    (hσo : ∀ i : Fin (n - wIn J + 1), σo i = σ (unColP J (i, i)).1)
    (hai0 : ∀ u, ai u (Fin.last _) = u) (hai1 : ∀ u, ∀ v : LIn J, ai u (inV J v) = a v)
    (hao0 : ∀ w, ao w (glueV J) = w) (hao1 : ∀ w, ∀ v : LOut J, ao w (outV J v) = a v) :
    treeValG L m t σ a F
      = ∑ u : ZMod L, ∑ w : ZMod L,
          ((t : ℂ) * (m (σ J.1) * m (σ J.2)) *
            treeValW L (FIn F J) (ai u)
              (Function.update (fun v => thetaEdge L m t (σi v) (σi (v + 1))) (Fin.last _) 1)
              (fun d => thetaEdge L m t (σi d.1.1) (σi d.1.2) - 1))
            * SB L u w * treeValG L m t σo (ao w) (FOut F J) := by
  have hJd := hF.1 J hJ
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  have hw : wIn J = J.2.val - J.1.val := rfl
  -- vertex / region bookkeeping
  have si : ∀ i : Fin (wIn J + 1), (unShift J (i, i)).1.val = i.val + J.1.val := fun i =>
    (unShift_val (i, i)).1
  have so : ∀ i : Fin (n - wIn J + 1), (unColP J (i, i)).1.val = unCol J i.val := fun i =>
    (unColP_val (i, i) hJ2).1
  have hσi' : ∀ (i : Fin (wIn J + 1)) (v : Fin n), v.val = i.val + J.1.val → σi i = σ v := by
    intro i v hv; rw [hσi i]; congr 1; exact Fin.ext (by rw [si i, hv])
  have hσo' : ∀ (i : Fin (n - wIn J + 1)) (v : Fin n), v.val = unCol J i.val → σo i = σ v := by
    intro i v hv; rw [hσo i]; congr 1; exact Fin.ext (by rw [so i, hv])
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hsucc : ∀ v : Fin n, v.val < n - 1 → (v + 1 : Fin n).val = v.val + 1 := by
    intro v hv; rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
  -- inside side conditions
  have hM1i : ∀ v : LIn J, thetaEdge L m t (σi (inV J v)) (σi (inV J v + 1))
      = thetaEdge L m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hv := v.2
    simp only [InArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := inV_val v.2
    have hlt : (inV J v.1).val < wIn J := by rw [h1]; simp only [wIn]; omega
    have hvn : v.1.val < n - 1 := by omega
    rw [hσi' _ v.1 (by rw [h1]; omega), hσi' _ (v.1 + 1) (by
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      omega)]
  have hEi : ∀ d : EIn F J, thetaEdge L m t (σi (shiftIn J d.1.1).1) (σi (shiftIn J d.1.1).2) - 1
      = thetaEdge L m t (σ d.1.1.1) (σ d.1.1.2) - 1 := by
    intro d
    have hlt := (hF.1 d.1.1 d.1.2).1
    have hv := shiftIn_val d.2.1 (le_of_lt hlt)
    have hdJ := d.2.1
    simp only [ArcLe, Fin.le_def] at hdJ
    rw [hσi' _ d.1.1.1 (by rw [hv.1]; omega),
      hσi' _ d.1.1.2 (by rw [hv.2]; omega)]
  -- outside side conditions
  have hg : (glueV J).val = J.1.val := by simp only [glueV, wIn]; omega
  have hM0o : thetaEdge L m t (σo (glueV J)) (σo (glueV J + 1))
      = thetaEdge L m t (σ J.1) (σ J.2) := by
    have hg1 : (glueV J + 1).val = J.1.val + 1 := by
      rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last, hg]; simp only [wIn]; omega), hg]
    rw [hσo' _ J.1 (by rw [hg, unCol_of_le le_rfl]), hσo' _ J.2 (by
      rw [hg1, unCol_of_gt (by omega)]; simp only [wIn]; omega)]
  have hM1o : ∀ v : LOut J, thetaEdge L m t (σo (outV J v)) (σo (outV J v + 1))
      = thetaEdge L m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
      have := v.2; simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
    have h1 := outV_val v.1 hJ2
    rw [hσo' _ v.1 (by rw [h1, unCol_col (by omega) hJw])]
    congr 1
    by_cases hr : v.1.val = n - 1
    · have hlast : outV J v.1 = Fin.last _ := by
        refine Fin.ext ?_
        rw [h1, Fin.val_last, col_of_gt (by omega), hr]; simp only [wIn]; omega
      have hv1 : v.1 + 1 = 0 := by
        refine Fin.ext ?_
        rw [Fin.val_add, hone, hr, Nat.sub_add_cancel (by omega), Nat.mod_self]; rfl
      rw [hlast, Fin.last_add_one, hv1]
      exact hσo' 0 0 (by simp [unCol])
    · have hvn : v.1.val < n - 1 := by have := v.1.isLt; omega
      have hlt : (outV J v.1).val < n - wIn J := by
        rw [h1]; rcases hvs with h | h
        · rw [col_of_le (by omega)]; simp only [wIn]; omega
        · rw [col_of_gt (by omega)]; simp only [wIn]; omega
      refine hσo' _ _ ?_
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      rcases hvs with h | h
      · rw [col_of_le (by omega)]
        by_cases h' : v.1.val + 1 ≤ J.1.val
        · rw [unCol_of_le h']
        · have : v.1.val + 1 = J.1.val := by omega
          rw [this, unCol_of_le le_rfl]
      · rw [col_of_gt (by omega), unCol_of_gt (by simp only [wIn]; omega)]
        simp only [wIn]; omega
  have hEo : ∀ d : EOut F J, thetaEdge L m t (σo (shiftOut J d.1.1).1) (σo (shiftOut J d.1.1).2) - 1
      = thetaEdge L m t (σ d.1.1.1) (σ d.1.1.2) - 1 := by
    intro d
    have hE := outEnds_of hF hn hJ (mem_nodes_of_mem d.1.2) d.2
    have hv := shiftOut_val d.1.1 hJ2
    rw [hσo' _ d.1.1.1 (by rw [hv.1, unCol_col hE.1 hJw]),
      hσo' _ d.1.1.2 (by rw [hv.2, unCol_col hE.2.1 hJw])]
  set ξ : ℂ := (t : ℂ) * (m (σ J.1) * m (σ J.2)) with hξ
  set Mi : Fin (wIn J + 1) → Matrix (ZMod L) (ZMod L) ℂ :=
    fun v => thetaEdge L m t (σi v) (σi (v + 1))
  have hM0i : Function.update Mi (Fin.last _) (ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ)) (Fin.last _)
      = (ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ)).transpose := by
    rw [Function.update_self, Matrix.transpose_smul, Matrix.transpose_one]
  have hM1i' : ∀ v : LIn J,
      Function.update Mi (Fin.last _) (ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ)) (inV J v)
        = thetaEdge L m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hv := v.2
    simp only [InArc, Fin.le_def, Fin.lt_def] at hv
    have hne : inV J v.1 ≠ Fin.last _ := by
      intro h
      have h1 := inV_val v.2
      have := congrArg Fin.val h
      rw [h1, Fin.val_last] at this
      simp only [wIn] at this
      omega
    rw [Function.update_of_ne hne]
    exact hM1i v
  have hEJ : (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1)
      = Function.update (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) ⟨J, hJ⟩
          (ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ) * SB L * thetaEdge L m t (σ J.1) (σ J.2)) := by
    funext d
    by_cases hd : d = ⟨J, hJ⟩
    · subst hd
      rw [Function.update_self]
      have h := mul_Theta L hL (hm (σ J.1) (σ J.2))
      rw [sub_mul, Matrix.one_mul, Matrix.smul_mul] at h
      show Theta L ξ - 1 = ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ) * SB L * Theta L ξ
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← h]
      abel
    · rw [Function.update_of_ne hd]
  rw [treeValG, hEJ, treeValW_cut L hF hn hJ a _ _ (ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ)) (SB L)
    (thetaEdge L m t (σ J.1) (σ J.2))]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [gval_in_eq hF hn hJ L a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
      (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) u _ (ai u)
        (Function.update Mi (Fin.last _) (ξ • (1 : Matrix (ZMod L) (ZMod L) ℂ)))
      (fun d => thetaEdge L m t (σi d.1.1) (σi d.1.2) - 1) (hai0 u) (hai1 u) hM0i hM1i' hEi,
    gval_out_eq hF hn hJ L a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
      (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) w _ (ao w)
        (fun v => thetaEdge L m t (σo v) (σo (v + 1)))
      (fun d => thetaEdge L m t (σo d.1.1) (σo d.1.2) - 1) (hao0 w) (hao1 w) hM0o hM1o hEo,
    treeValW_leaf_smul]
  rfl

end LongCut

end RBM
