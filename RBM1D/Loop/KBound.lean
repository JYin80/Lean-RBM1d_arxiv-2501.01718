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

end RBM
