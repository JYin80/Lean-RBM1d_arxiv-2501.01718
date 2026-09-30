/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.GUEPhase
import RBM1D.Loop.KBound
import Mathlib.Analysis.ODE.ExistUnique

/-!
# GUE-phase primitive loops and the uniform (2.59)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (7.33)–(7.36) and (2.59)/(3.46): existence and uniqueness of the GUE-phase primitive
loops `K̃` on `[t₁,t₀]`, and Lemma 3.11's bound `|K_{t,σ,a}| ≤ C(Wη_tℓ̂(t))^{-(n-1)}` made uniform
in the bulk energy `|E| ≤ 2-k` (needed because the §7.2 random layer evaluates `K` at a moving
energy).

## Private helpers

`RBM.norm_Kgen_le` (`Loop/KBound.lean`) and its whole dependency chain are stated for a
*fixed* implicit energy `E`.  Tracing every witness by hand (not just the `∃`-typed statements)
shows that only two of them actually construct an `E`-dependent (through `(mE E).im`) witness:
`RBM.norm_Alayer_le` and `RBM.sum_zero` (`Loop/SumZero.lean`).  Every other lemma in the chain
only ever combines already-`k`-only pieces with the (opaque) output of those two, so the
re-quantification needed for `norm_Kgen_le_unif` is: redo those two through `mE_im_ge`
(`√(2κ)/2 ≤ Im m(E)`, `Flow/Scales.lean`), then move `∀ E` inside the `∃ C` of every
downstream lemma mechanically (the witness formula of each downstream lemma never needs to
change, only its quantifier order and the two calls it makes into the first two).

## Existence of `K̃` (`gueK_exists`)

Neither Mathlib nor this library has a global existence theorem for linear ODEs (Mathlib's
`IsPicardLindelof` is local: for an affine field of operator norm `K` its confining inequality
forces a time step `< 1/K`).  `gueKTilde_ode_global` supplies one for any vector field that is
uniformly globally Lipschitz in space on a compact time interval and continuous in time, by
chaining the local theorem in steps of length `h = 1/(2(K+1))`, re-centring the ball at each new
endpoint and gluing with `HasDerivWithinAt.union`.  The primitive loops are then built by
induction on the length (`gueKTilde_exists_upto`): length `1` is constant (`primRhsGUE` is the
empty sum there), length `2` is `kTwoGUELoop` (`kTwoGUE_self`, `Kgen_two`,
`hasDerivAt_kTwoGUELoop`), and for length `n + 1 ≥ 3` the unknown slice on the finite set of
well-formed loops of length `n + 1` solves an ODE that is affine in the unknown: the two cut
lengths add up to `n + 3`, so at most one of them equals `n + 1`, and the other factor is an
already-constructed shorter loop, continuous and hence bounded on `[t₁, t₀]`.  Consistency
across lengths holds by construction (each step keeps the shorter lengths unchanged), so no
uniqueness theorem is needed for the existence statement.
-/

namespace RBM

open Finset Cor35 Set

section GUEPhaseKTildeHelpers

/-- Uniform bound on `(Im m^{(E)})⁻¹` over the bulk `|E| ≤ 2 - k`, from `mE_im_ge`. -/
private theorem invMEIm_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {E : ℝ}
    (hEk : |E| ≤ 2 - k) : ((mE E).im)⁻¹ ≤ 2 / Real.sqrt (2 * k) := by
  rw [show (2 : ℝ) / Real.sqrt (2 * k) = (Real.sqrt (2 * k) / 2)⁻¹ by rw [inv_div]]
  exact inv_anti₀ (by positivity) (mE_im_ge hk0 (by linarith) hEk)

/-- **`norm_Alayer_le`, uniform in the bulk energy.**  Same recursion as `norm_Alayer_le`
(`Loop/SumZero.lean`), with the one bare factor `((mE E).im)⁻¹` in its witness replaced by
the uniform bound `2/√(2k)` (`invMEIm_le_unif`); every other step is untouched. -/
private theorem norm_Alayer_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (n : ℕ) [NeZero n], 3 ≤ n → n ≤ N →
      ∀ (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (t : ℝ), 0 ≤ t → t < 1 →
        ‖Alayer (mSigma E) t σ π‖ ≤ C * (etaT E t)⁻¹ ^ (n - 1) := by
  set bound : ℝ := 2 / Real.sqrt (2 * k) with hbounddef
  have hbound0 : 0 ≤ bound := by positivity
  induction N with
  | zero => exact ⟨0, le_rfl, fun E _ n _ h3 hN => by omega⟩
  | succ N ih =>
  obtain ⟨C, hC0, hC⟩ := ih
  have hcor0 : 0 ≤ cor37Const (N + 1) k := cor37Const_nonneg' hk0
  refine ⟨C + cor37Const (N + 1) k + (2 ^ ((N + 1) * (N + 1)) + 1) * (C * C * bound),
    by positivity, fun E hEk n _ h3 hN σ π t ht0 ht1 => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set ι := (mE E).im with hιdef
  have hι0 : 0 < ι := mE_im_pos hE
  have hιbound : ι⁻¹ ≤ bound := invMEIm_le_unif hk0 hk1 hEk
  have hη : 0 < etaT E t := etaT_pos hE ht1
  set η := etaT E t with hηdef
  have hη' : η = (1 - t) * ι := rfl
  have hpow0 : 0 ≤ η⁻¹ ^ (n - 1) := by positivity
  have hCC : 0 ≤ C * C * bound := by positivity
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · refine (hC E hEk n h3 (by omega) σ π t ht0 ht1).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) + 1) hCC
    linarith
  have hn : n = N + 1 := by omega
  have hne_bound : ∀ π : Finset (Fin n × Fin n), π.Nonempty →
      ‖Alayer (mSigma E) t σ π‖ ≤ C * C * bound * η⁻¹ ^ (n - 1) := by
    intro π hπne
    rcases (TSPlong n σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
    · rw [Alayer_eq_zero_of_empty _ _ hemp, norm_zero]; positivity
    obtain ⟨hF₀T, hπ⟩ := mem_TSPlong.1 hF₀
    have hF₀' := isTSP_of_mem_TSP hF₀T
    obtain ⟨J, hJ, hinner⟩ := exists_innermost hF₀' (σ := σ) (hπ ▸ hπne)
    rw [hπ] at hJ hinner
    have hm := norm_mul_mSigma_lt_one hE2 ht0 ht1
    have hJd : IsDiag n J.1 J.2 := hF₀'.1 J (Flong_subset F₀ σ (hπ ▸ hJ))
    have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJ)).2
    rw [Alayer_cut (by omega) (mSigma E) hm σ hF₀T hπ hJ hinner,
      mSigma_mul_of_ne hE2 hJlong, mul_one]
    have hw := width_of_isDiag hJd
    have hw' : wIn J + 1 < n := by
      obtain ⟨-, -, hnot⟩ := hJd
      have := J.2.isLt
      simp only [wIn]
      omega
    have hwv : wIn J = J.2.val - J.1.val := rfl
    have hin := hC E hEk (wIn J + 1) (by omega) (by omega) (sigmaIn σ J) ∅ t ht0 ht1
    have hout := hC E hEk (n - wIn J + 1) (by omega) (by omega) (sigmaOut σ J)
      ((π.erase J).image (shiftOut J)) t ht0 ht1
    simp only [Nat.add_sub_cancel] at hin hout
    have ht : ‖(t : ℂ)‖ = t := Complex.norm_of_nonneg ht0
    have h1t : ‖(1 : ℂ) - t‖ = 1 - t := by
      rw [show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_of_nonneg (by linarith)
    rw [norm_mul, norm_mul, norm_mul, ht, h1t]
    have hkey : (1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J)) ≤ bound * η⁻¹ ^ (n - 1) := by
      have h1t0 : 1 - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
      have hι0' : ι ≠ 0 := hι0.ne'
      have heq : (1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J)) = ι⁻¹ * η⁻¹ ^ (n - 1) := by
        rw [← pow_add, show wIn J + (n - wIn J) = n - 1 + 1 by omega, pow_succ, hη']
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right hιbound hpow0
    calc t * (1 - t) * ‖Alayer (mSigma E) t (sigmaIn σ J) ∅‖ *
          ‖Alayer (mSigma E) t (sigmaOut σ J) ((π.erase J).image (shiftOut J))‖
        ≤ (1 - t) * (C * η⁻¹ ^ wIn J) * (C * η⁻¹ ^ (n - wIn J)) := by
          gcongr
          all_goals nlinarith
        _ = C * C * ((1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J))) := by ring
        _ ≤ C * C * (bound * η⁻¹ ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left hkey (mul_nonneg hC0 hC0)
        _ = C * C * bound * η⁻¹ ^ (n - 1) := by ring
  rcases π.eq_empty_or_nonempty with rfl | hπne
  · have hsum := norm_sum_Alayer_le hk0 hk1 hEk ht0 ht1 h3 σ
    have hmem : (∅ : Finset (Fin n × Fin n)) ∈ (diagonals n).powerset := empty_mem_powerset _
    rw [← add_sum_erase _ _ hmem] at hsum
    have hrest : ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖
        ≤ 2 ^ ((N + 1) * (N + 1)) * (C * C * bound * η⁻¹ ^ (n - 1)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (sum_le_sum fun π hπ => hne_bound π
        (nonempty_iff_ne_empty.2 (mem_erase.1 hπ).1)).trans ?_
      rw [sum_const, nsmul_eq_mul]
      gcongr
      have hc : ((diagonals n).powerset.erase ∅).card ≤ 2 ^ (n * n) := by
        refine (card_erase_le).trans ?_
        rw [card_powerset]
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have := card_le_univ (diagonals n)
        simpa using this
      rw [← hn]
      exact_mod_cast hc
    have htri : ‖Alayer (mSigma E) t σ ∅‖ ≤
        ‖Alayer (mSigma E) t σ ∅ +
            ∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖ +
          ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖ := by
      have := norm_sub_le (Alayer (mSigma E) t σ ∅ +
        ∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π)
        (∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π)
      rwa [add_sub_cancel_right] at this
    have hcor : cor37Const n k = cor37Const (N + 1) k := by rw [hn]
    rw [hcor] at hsum
    calc ‖Alayer (mSigma E) t σ ∅‖
        ≤ cor37Const (N + 1) k * η⁻¹ ^ (n - 1) +
            2 ^ ((N + 1) * (N + 1)) * (C * C * bound * η⁻¹ ^ (n - 1)) := by
          linarith
      _ ≤ _ := by
          have h2 : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) := by positivity
          nlinarith [mul_nonneg hC0 hpow0, mul_nonneg hCC hpow0]
  · refine (hne_bound π hπne).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1))) hCC
    linarith

/-- **`sum_zero`, uniform in the bulk energy.** -/
private theorem sum_zero_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ σ : Fin n → Bool, (∀ v, σ v ≠ σ (v + 1)) →
        ‖(L : ℂ)⁻¹ * ∑ d : Fin n → ZMod L, SigmaPi L (mSigma E) t σ ∅ d‖ ≤ C * etaT E t := by
  obtain ⟨C, hC0, hC⟩ := norm_Alayer_le_unif hk0 hk1 n
  set bound : ℝ := 2 / Real.sqrt (2 * k) with hbounddef
  have hbound0 : 0 ≤ bound := by positivity
  refine ⟨C * bound ^ n, by positivity, fun E hEk L _ hL t ht0 ht1 σ halt => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set ι := (mE E).im with hιdef
  have hι0 : 0 < ι := mE_im_pos hE
  have hιbound : ι⁻¹ ≤ bound := invMEIm_le_unif hk0 hk1 hEk
  have hm := norm_mul_mSigma_lt_one hE2 ht0 ht1
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  rw [sum_SigmaPi (mSigma E) hm hL (by omega), ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
  have hξ : ∀ v, (1 : ℂ) - t * (mSigma E (σ v) * mSigma E (σ (v + 1))) = ((1 - t : ℝ) : ℂ) := by
    intro v; rw [mSigma_mul_of_ne hE2 (halt v)]; push_cast; ring
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hQ : Qlayer (mSigma E) t σ ∅ = ((1 - t : ℝ) : ℂ) ^ n * Alayer (mSigma E) t σ ∅ := by
    unfold Alayer
    simp_rw [hξ]
    rw [prod_const, card_univ, Fintype.card_fin, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (by exact_mod_cast h1t.ne'), one_pow, one_mul]
  have hA := hC E hEk n hn le_rfl σ ∅ t ht0 ht1
  have hη : etaT E t = (1 - t) * ι := rfl
  have hηnn : 0 ≤ etaT E t := (etaT_pos hE ht1).le
  rw [hQ, norm_mul, norm_pow, Complex.norm_of_nonneg h1t.le]
  calc (1 - t) ^ n * ‖Alayer (mSigma E) t σ ∅‖
      ≤ (1 - t) ^ n * (C * (etaT E t)⁻¹ ^ (n - 1)) := by gcongr
    _ = C * ι⁻¹ ^ n * etaT E t := by
        have key : ∀ p : ℕ, (1 - t) ^ (p + 1) * (C * ((1 - t) * ι)⁻¹ ^ p) =
            C * ι⁻¹ ^ (p + 1) * ((1 - t) * ι) := by
          intro p
          have h1 : (1 - t) ≠ 0 := h1t.ne'
          have h2 : ι ≠ 0 := hι0.ne'
          rw [mul_inv, mul_pow, pow_succ, pow_succ]
          field_simp
          rw [one_div, inv_pow]
          field_simp
        have := key (n - 1)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n), ← hη] at this
    _ ≤ C * bound ^ n * etaT E t := by
        gcongr

set_option maxHeartbeats 1000000 in
-- Same combinatorial expansion as `sum_norm_innerId_alt_le` (`Loop/KBound.lean`), which
-- carries the same `set_option`.
private theorem sum_norm_innerId_alt_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ' : Fin N → Bool, (∀ v, σ' v ≠ σ' (v + 1)) → ∀ (a' : Fin N → ZMod L) (p : Fin N),
        ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
          ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
  obtain ⟨Csz, hCsz0, hCsz⟩ := sum_zero_unif hk0 hk1 hN
  set SW := sigWeightConst N k 2
  have hSW : 0 ≤ SW := sigWeightConst_nonneg hk0 2
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  set K0 := Csz + 19 / 4 * SW + 3 * (3 / 2) ^ (N - 2) * SW
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨3 ^ N * (K0 * e8 ^ (N - 2)), by positivity, ?_⟩
  intro E hEk L _ hL t ht0 ht1 σ' halt a' p
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
  have hηℓ2 : η * ℓ ^ 2 ≤ 1 := etaT_mul_ellHat_sq_le hE2 ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hinv1 : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
  have hA : 3 / 2 ≤ A := by simp only [A, e8]; nlinarith
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  have hℓA : ℓ ≤ A := by
    have : ℓ ≤ (η * ℓ)⁻¹ := by
      have h1 : ℓ * (η * ℓ) ≤ 1 := by nlinarith
      calc ℓ = ℓ * (η * ℓ) * (η * ℓ)⁻¹ := by field_simp
        _ ≤ 1 * (η * ℓ)⁻¹ := by gcongr
        _ = (η * ℓ)⁻¹ := one_mul _
    simp only [A, e8]; nlinarith
  have hApow : A ≤ A ^ (N - 2) := le_self_pow₀ hA1 (by omega)
  -- kernels
  set f : Fin N → ZMod L → ℂ := innerKer (mSigma E) t σ' a' p
  have hfp : ∀ y, f p y = 1 := fun y => by simp only [f, innerKer, Function.update_self]
  have hfv : ∀ v, v ≠ p → ∀ y, f v y = Theta L (t : ℂ) (a' v) y := fun v hv y => by
    simp only [f, innerKer, Function.update_of_ne hv, thetaEdge_of_ne hE2 t (halt v)]
  have hgrad : ∀ v u, ‖f v (u + 1) - f v u‖ ≤ 3 / 2 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hfp, hfp, sub_self, norm_zero]; norm_num
    · rw [hfv v hv, hfv v hv, norm_sub_rev]; exact norm_Theta_sub_shift_le_uniform L hL ht0 ht1 _ _
  have hlap_eq : ∀ v, v ≠ p → ∀ u, ‖lap (f v) u‖ =
      ‖2 * Theta L (t : ℂ) (a' v) u - Theta L (t : ℂ) (a' v) (u + 1) -
        Theta L (t : ℂ) (a' v) (u - 1)‖ :=
    fun v hv u => by
      simp only [lap, hfv v hv]
      rw [← norm_neg]; congr 1; ring
  have hlapp : ∀ u, lap (f p) u = 0 := fun u => by simp only [lap, hfp]; ring
  have hlap : ∀ v u, ‖lap (f v) u‖ ≤ 3 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hlapp, norm_zero]; norm_num
    · rw [hlap_eq v hv]; exact norm_Theta_second_diff_le_three L hL ht0 ht1 _ _
  have hG1 : ∀ v, ∑ u, ‖f v (u + 1) - f v u‖ ≤ 3 * ℓ := fun v => by
    by_cases hv : v = p
    · subst hv; simp only [hfp, sub_self, norm_zero, sum_const_zero]; positivity
    · simp only [hfv v hv]
      calc ∑ u, ‖Theta L (t : ℂ) (a' v) (u + 1) - Theta L (t : ℂ) (a' v) u‖
          = ∑ u, ‖Theta L (t : ℂ) (a' v) u - Theta L (t : ℂ) (a' v) (u + 1)‖ :=
            sum_congr rfl fun u _ => norm_sub_rev _ _
        _ ≤ 3 * ℓ := sum_norm_Theta_sub_shift_le L hL ht0 ht1 _
  have hG2 : ∀ v, ∑ u, ‖lap (f v) u‖ ≤ 2 * (3 * ℓ) := fun v => by
    by_cases hv : v = p
    · subst hv; simp only [hlapp, norm_zero, sum_const_zero]; positivity
    · simp only [hlap_eq v hv]
      calc _ ≤ 6 := sum_norm_Theta_second_diff_le L hL ht0 ht1 _
        _ ≤ 2 * (3 * ℓ) := by linarith
  -- the rescaled kernels (root carries `A`)
  set f' : Fin N → ZMod L → ℂ := Function.update f p (fun _ => (A : ℂ))
  have hf'p : ∀ y, f' p y = A := fun y => by simp only [f', Function.update_self]
  have hf'v : ∀ v, v ≠ p → f' v = f v := fun v hv => by simp only [f', Function.update_of_ne hv]
  have hsup' : ∀ v y, ‖f' v y‖ ≤ A := fun v y => by
    by_cases hv : v = p
    · subst hv; rw [hf'p, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0]
    · rw [hf'v v hv, hfv v hv, hAdef, hηdef, etaT_eq_zt_im, ← div_eq_mul_inv]
      exact norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _ _
  have hgrad' : ∀ v u, ‖f' v (u + 1) - f' v u‖ ≤ 3 / 2 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hf'p, hf'p, sub_self, norm_zero]; norm_num
    · rw [hf'v v hv]; exact hgrad v u
  have hlap'p : ∀ u, lap (f' p) u = 0 := fun u => by simp only [lap, hf'p]; ring
  have hlap' : ∀ v u, ‖lap (f' v) u‖ ≤ 3 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hlap'p, norm_zero]; norm_num
    · rw [hf'v v hv]; exact hlap v u
  have hoff' : ∀ v u, u ≠ a' v → ‖lap (f' v) u‖ ≤ 24 / ℓ := fun v u hu => by
    by_cases hv : v = p
    · subst hv; rw [hlap'p, norm_zero]; positivity
    · rw [hf'v v hv, hlap_eq v hv]; exact norm_Theta_second_diff_le L hL ht0 ht1 (Ne.symm hu)
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
  have hl1q : ∀ q, q ≠ p → ∑ y, ‖f' q y‖ ≤ η⁻¹ := fun q hq => by
    simp only [hf'v q hq, hfv q hq]; rw [hηdef, etaT_eq_zt_im]
    exact sum_norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _
  -- the product with `f'` is `A` times the product with `f`
  have hscale : ∀ (τ : Fin N → Fin 3), τ p = 0 → ∀ (s : Fin N → ZMod L), ∀ c,
      A * ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ = ∏ v, ‖taylorTerm (f' v) (τ v) c (s v)‖ := by
    intro τ hτp s c
    rw [← mul_prod_erase _ (fun v => ‖taylorTerm (f v) (τ v) c (s v)‖) (mem_univ p),
      ← mul_prod_erase _ (fun v => ‖taylorTerm (f' v) (τ v) c (s v)‖) (mem_univ p), ← mul_assoc]
    congr 1
    · show A * ‖taylorTerm (f p) (τ p) c (s p)‖ = ‖taylorTerm (f' p) (τ p) c (s p)‖
      rw [hτp]
      show A * ‖f p c‖ = ‖f' p c‖
      rw [hfp, hf'p, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0]
    · refine Finset.prod_congr rfl fun v hv => ?_
      rw [hf'v v (ne_of_mem_erase hv)]
  -- the self-energy
  set g : (Fin N → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ' ∅ s
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  have hgneg : ∀ s, g (fun v => -s v) = g s := fun s => SigmaPi_neg (mSigma E) hm hL σ' ∅ s
  have hgadd : ∀ s c, g (fun v => s v + c) = g s := fun s c =>
    SigmaPi_add_const (mSigma E) hm hL σ' ∅ s c
  have hzero : ‖∑ s ∈ pinned L N p, g s‖ ≤ Csz * η := by
    have h := hCsz E hEk L hL t ht0.le ht1 σ' halt
    have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    rw [sum_eq_mul_sum_pinned g hgadd p, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul] at h
    exact h
  have hSW2 := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ' (by omega) 2 p
  set B := K0 * A ^ (N - 2)
  have hB0 : 0 ≤ B := by positivity
  set T : (Fin N → Fin 3) → ZMod L → ℂ := fun τ u =>
    ∑ s ∈ pinned L N p, g s * ∏ v, taylorTerm (f v) (τ v) u (s v)
  have hexp : ∀ u, innerId (mSigma E) t σ' a' p u = ∑ τ : Fin N → Fin 3, T τ u := by
    intro u
    rw [innerId_eq hL (mSigma E) hm σ' a' p u]
    simp only [T]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [← mul_sum, prod_taylor_expand]
  have hWnn : ∀ s : Fin N → ZMod L, 0 ≤ ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 :=
    fun s => prod_nonneg fun _ _ => by positivity
  -- `∑_u |T_τ(u)| ≤ ∑_s |g(s)| ∑_u ∏_v |pieces|`
  have habs : ∀ τ : Fin N → Fin 3, ∑ u, ‖T τ u‖ ≤
      ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ := by
    intro τ
    calc ∑ u, ‖T τ u‖
        ≤ ∑ u : ZMod L, ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ := by
          refine sum_le_sum fun u _ => ?_
          refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
          rw [norm_mul, norm_prod]
      _ = _ := by rw [sum_comm]; simp only [mul_sum]
  have hterm : ∀ τ : Fin N → Fin 3, ∑ u, ‖T τ u‖ ≤ B := by
    intro τ
    by_cases hτp : τ p = 0
    swap
    · -- the root carries an odd or even piece at shift `0`
      have hz : ∀ u, T τ u = 0 := fun u => by
        refine sum_eq_zero fun s hs => ?_
        simp only [pinned, mem_filter] at hs
        have h0 : taylorTerm (f p) (τ p) u (s p) = 0 := by
          rw [hs.2]
          have : τ p = 1 ∨ τ p = 2 := by revert hτp; generalize τ p = j; decide +revert
          rcases this with h | h <;> rw [h]
          · exact oddPart_zero _ _
          · exact evenPart_zero _ _
        rw [prod_eq_zero (mem_univ p) h0, mul_zero]
      simp only [hz, norm_zero, sum_const_zero]; exact hB0
    by_cases hval : ∃ q, q ≠ p ∧ τ q = 0
    · obtain ⟨q, hqp, hq⟩ := hval
      by_cases hR : (∃ v, τ v = 2) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ τ v₁ = 1 ∧ τ v₂ = 1
      · -- the remainder terms, with the value factor `q`
        have hW : ∀ s : Fin N → ZMod L, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
            19 / 4 * A ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
          intro s
          have h := sum_prod_taylor_le_at f' a' hA hsup' q (hl1q q hqp) hgrad' hlap' hoff'
            (by positivity) h₁ h₂ (by norm_num) (by norm_num) τ hR hq s
          have e : ∑ c, ∏ v, ‖taylorTerm (f' v) (τ v) c (s v)‖
              = A * ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            rw [mul_sum]; exact sum_congr rfl fun c _ => (hscale τ hτp s c).symm
          rw [e, show A ^ (N - 1) = A * A ^ (N - 2) by rw [← pow_succ']; congr 1; omega] at h
          have h' : A * ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
              A * (19 / 4 * A ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) := by
            refine h.trans (le_of_eq ?_); ring
          exact le_of_mul_le_mul_left h' hA0
        calc ∑ u, ‖T τ u‖
            ≤ ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ :=
              habs τ
          _ ≤ ∑ s ∈ pinned L N p, ‖g s‖ *
                (19 / 4 * A ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
              sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hW s) (norm_nonneg _)
          _ = 19 / 4 * A ^ (N - 2) *
                ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
              rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
          _ ≤ 19 / 4 * A ^ (N - 2) * SW := by gcongr
          _ ≤ B := by
              simp only [B, K0]
              have : 0 ≤ (Csz + 3 * (3 / 2) ^ (N - 2) * SW) * A ^ (N - 2) := by positivity
              nlinarith
      · push Not at hR
        obtain ⟨hn2, hn11⟩ := hR
        have key : ∀ j : Fin 3, j ≠ 2 → j ≠ 1 → j = 0 := by decide
        by_cases h1 : ∃ v₁, τ v₁ = 1
        · -- a single odd piece
          obtain ⟨v₁, hv₁⟩ := h1
          have h0 : ∀ v, v ≠ v₁ → τ v = 0 := fun v hv =>
            key _ (hn2 v) (hn11 v₁ v (Ne.symm hv) hv₁)
          have hz : ∀ u, T τ u = 0 := fun u =>
            sum_taylor_single_eq_zero_pt g hgneg f τ v₁ hv₁ h0 p u
          simp only [hz, norm_zero, sum_const_zero]; exact hB0
        · -- the leading term
          push Not at h1
          have h0 : ∀ v, τ v = 0 := fun v => key _ (hn2 v) (h1 v)
          have hT : ∀ u, T τ u = (∏ v, f v u) * ∑ s ∈ pinned L N p, g s := by
            intro u
            simp only [T]
            rw [mul_sum]
            refine sum_congr rfl fun s _ => ?_
            have : ∏ v, taylorTerm (f v) (τ v) u (s v) = ∏ v, f v u :=
              Finset.prod_congr rfl fun v _ => by rw [h0 v]; rfl
            rw [this, mul_comm]
          have hcard : ((univ.erase q).erase p).card = N - 2 := by
            rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hqp, mem_univ _⟩),
              card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
            omega
          have hlead : ∑ u : ZMod L, ‖∏ v, f v u‖ ≤ η⁻¹ * A ^ (N - 2) := by
            calc ∑ u : ZMod L, ‖∏ v, f v u‖
                = ∑ u : ZMod L, ‖f q u‖ * ∏ v ∈ (univ.erase q).erase p, ‖f v u‖ := by
                  refine sum_congr rfl fun u _ => ?_
                  rw [norm_prod, ← mul_prod_erase _ (fun v => ‖f v u‖) (mem_univ q),
                    ← mul_prod_erase _ (fun v => ‖f v u‖) (mem_erase.2 ⟨Ne.symm hqp, mem_univ _⟩),
                    hfp, norm_one, one_mul]
              _ ≤ (∑ u : ZMod L, ‖f q u‖) * ∏ _v ∈ (univ.erase q).erase p, A :=
                  sum_mul_prod_le _ (fun v u => ‖f v u‖) _ _ (fun u => norm_nonneg _)
                    (fun v u => norm_nonneg _) fun v hv u => by
                      have hvp := ne_of_mem_erase hv
                      have := hsup' v u; rwa [hf'v v hvp] at this
              _ ≤ η⁻¹ * A ^ (N - 2) := by
                  rw [prod_const, hcard]
                  gcongr
                  have := hl1q q hqp; rwa [hf'v q hqp] at this
          calc ∑ u, ‖T τ u‖ = (∑ u : ZMod L, ‖∏ v, f v u‖) * ‖∑ s ∈ pinned L N p, g s‖ := by
                simp only [hT, norm_mul, sum_mul]
            _ ≤ (η⁻¹ * A ^ (N - 2)) * (Csz * η) := by gcongr
            _ = Csz * A ^ (N - 2) := by field_simp
            _ ≤ B := by
                simp only [B, K0]
                have : 0 ≤ (19 / 4 * SW + 3 * (3 / 2) ^ (N - 2) * SW) * A ^ (N - 2) := by
                  positivity
                nlinarith
    · -- no value factor besides the root
      push Not at hval
      have hW : ∀ s : Fin N → ZMod L, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
          3 * ℓ * (3 / 2) ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := fun s =>
        sum_prod_taylor_le_noval f p hfp hgrad hlap hG1 hG2 τ hτp hval s (by omega)
      calc ∑ u, ‖T τ u‖
          ≤ ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ :=
            habs τ
        _ ≤ ∑ s ∈ pinned L N p, ‖g s‖ *
              (3 * ℓ * (3 / 2) ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
            sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hW s) (norm_nonneg _)
        _ = 3 * ℓ * (3 / 2) ^ (N - 2) *
              ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
        _ ≤ 3 * ℓ * (3 / 2) ^ (N - 2) * SW := by gcongr
        _ ≤ 3 * A ^ (N - 2) * (3 / 2) ^ (N - 2) * SW := by
            gcongr; exact hℓA.trans hApow
        _ ≤ B := by
            simp only [B, K0]
            have : 0 ≤ (Csz + 19 / 4 * SW) * A ^ (N - 2) := by positivity
            nlinarith
  calc ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
      ≤ ∑ u : ZMod L, ∑ τ : Fin N → Fin 3, ‖T τ u‖ := by
        refine sum_le_sum fun u _ => ?_
        rw [hexp u]; exact norm_sum_le _ _
    _ = ∑ τ : Fin N → Fin 3, ∑ u : ZMod L, ‖T τ u‖ := sum_comm
    _ ≤ ∑ τ : Fin N → Fin 3, B := sum_le_sum fun τ _ => hterm τ
    _ = 3 ^ N * B := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring
    _ = 3 ^ N * (K0 * e8 ^ (N - 2)) * (η * ℓ)⁻¹ ^ (N - 2) := by
        simp only [B, A, mul_pow]; ring
private theorem sum_norm_innerId_short_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ' : Fin N → Bool) (p : Fin N), (∃ v, v ≠ p ∧ σ' v = σ' (v + 1)) →
        ∀ a' : Fin N → ZMod L,
          ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
            ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
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
  set SW0 := sigWeightConst N k 0
  have hSW0 : 0 ≤ SW0 := sigWeightConst_nonneg hk0 0
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨SW0 * (Bk * S1) * (Bk * e8) ^ (N - 2), by positivity, ?_⟩
  intro E hEk L _ hL t ht0 ht1 σ' p ⟨v₀, hv₀p, hv₀⟩ a'
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hA1 : 1 ≤ A := by
    have : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
    simp only [A, e8]; nlinarith
  set f : Fin N → ZMod L → ℂ := innerKer (mSigma E) t σ' a' p
  have hfp : ∀ y, f p y = 1 := fun y => by simp only [f, innerKer, Function.update_self]
  have hfv : ∀ v, v ≠ p → ∀ y, f v y = thetaEdge L (mSigma E) t (σ' v) (σ' (v + 1)) (a' v) y :=
    fun v hv y => by simp only [f, innerKer, Function.update_of_ne hv]
  have hsup : ∀ v, v ≠ p → ∀ y, ‖f v y‖ ≤ Bk * A := by
    intro v hvp y
    rw [hfv v hvp]
    by_cases hv : σ' v = σ' (v + 1)
    · have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ' v) (a' v) y
      rw [← hv]
      calc _ ≤ Bk * Real.exp (-(κ * zdist L (a' v - y))) := h
        _ ≤ Bk * 1 := by
            gcongr; rw [Real.exp_le_one_iff, neg_nonpos]; positivity
        _ ≤ Bk * A := by gcongr
    · rw [thetaEdge_of_ne hE2 t hv]
      have h := norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 (a' v) y
      rw [← etaT_eq_zt_im, div_eq_mul_inv] at h
      calc _ ≤ A := h
        _ = 1 * A := (one_mul A).symm
        _ ≤ Bk * A := by gcongr
  have hl1 : ∀ x : ZMod L, ∑ u : ZMod L, ‖f v₀ (u + x)‖ ≤ Bk * S1 := by
    intro x
    calc ∑ u : ZMod L, ‖f v₀ (u + x)‖
        ≤ ∑ u : ZMod L, Bk * Real.exp (-(κ * zdist L (u - (a' v₀ - x)))) := by
          refine sum_le_sum fun u _ => ?_
          rw [hfv v₀ hv₀p]
          have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ' v₀) (a' v₀) (u + x)
          rw [← hv₀]
          rw [show a' v₀ - (u + x) = -(u - (a' v₀ - x)) by ring, zdist_neg] at h
          exact h
      _ = Bk * ∑ u : ZMod L, Real.exp (-(κ * zdist L (u - (a' v₀ - x)))) := by rw [mul_sum]
      _ ≤ Bk * S1 := by gcongr; exact sum_exp_zdist_le L hκ _
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  set g : (Fin N → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ' ∅ s
  have hSg := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ' (by omega) 0 p
  simp only [pow_zero, prod_const_one, mul_one] at hSg
  have hmem : p ∈ univ.erase v₀ := mem_erase.2 ⟨Ne.symm hv₀p, mem_univ _⟩
  have hT : ((univ.erase v₀).erase p).card = N - 2 := by
    rw [card_erase_of_mem hmem, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega
  calc ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
      ≤ ∑ u : ZMod L, ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ‖f v (u + s v)‖ := by
        refine sum_le_sum fun u _ => ?_
        rw [innerId_eq hL (mSigma E) hm σ' a' p u]
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
        rw [norm_mul, norm_prod]
    _ = ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖f v (u + s v)‖ := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ s ∈ pinned L N p, ‖g s‖ * ((Bk * S1) * (Bk * A) ^ (N - 2)) := by
        refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ∑ u : ZMod L, ∏ v, ‖f v (u + s v)‖
            = ∑ u : ZMod L, ‖f v₀ (u + s v₀)‖ *
                ∏ v ∈ (univ.erase v₀).erase p, ‖f v (u + s v)‖ := by
              refine sum_congr rfl fun u _ => ?_
              rw [← mul_prod_erase _ (fun v => ‖f v (u + s v)‖) (mem_univ v₀),
                ← mul_prod_erase _ (fun v => ‖f v (u + s v)‖) hmem, hfp, norm_one, one_mul]
          _ ≤ (∑ u : ZMod L, ‖f v₀ (u + s v₀)‖) * ∏ _v ∈ (univ.erase v₀).erase p, (Bk * A) :=
              sum_mul_prod_le _ (fun v u => ‖f v (u + s v)‖) _ _ (fun u => norm_nonneg _)
                (fun v u => norm_nonneg _) fun v hv u => hsup v (ne_of_mem_erase hv) _
          _ ≤ (Bk * S1) * (Bk * A) ^ (N - 2) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 _
    _ = (∑ s ∈ pinned L N p, ‖g s‖) * ((Bk * S1) * (Bk * A) ^ (N - 2)) := by rw [sum_mul]
    _ ≤ SW0 * ((Bk * S1) * (Bk * A) ^ (N - 2)) := by gcongr
    _ = SW0 * (Bk * S1) * (Bk * e8) ^ (N - 2) * (η * ℓ)⁻¹ ^ (N - 2) := by
        simp only [A, mul_pow]; ring
/-- **The inner molecule, uniform in the bulk energy.** -/
private theorem sum_norm_innerId_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ' : Fin N → Bool) (p : Fin N), σ' p ≠ σ' (p + 1) → ∀ a' : Fin N → ZMod L,
        ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
          ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := sum_norm_innerId_alt_le_unif hk0 hk1 hN
  obtain ⟨C₂, hC₂, h₂⟩ := sum_norm_innerId_short_le_unif hk0 hk1 hN
  refine ⟨C₁ + C₂, by positivity, fun E hEk L _ hL t ht0 ht1 σ' p hp a' => ?_⟩
  have hE : |E| < 2 := by linarith
  have hX : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
    have := etaT_pos hE ht1
    have := one_le_ellHat L hL ht0.le ht1
    positivity
  by_cases halt : ∀ v, σ' v ≠ σ' (v + 1)
  · exact (h₁ E hEk L hL t ht0 ht1 σ' halt a' p).trans (by nlinarith)
  · push Not at halt
    obtain ⟨v, hv⟩ := halt
    have hvp : v ≠ p := fun h => hp (h ▸ hv)
    exact (h₂ E hEk L hL t ht0 ht1 σ' p ⟨v, hvp, hv⟩ a').trans (by nlinarith)
set_option maxHeartbeats 1000000 in
-- Same combinatorial expansion as `sum_norm_innerId_alt_le_unif` above; needs the same budget.
private theorem norm_Kpi_empty_alt_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {n : ℕ}
    [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ : Fin n → Bool, (∀ v, σ v ≠ σ (v + 1)) → ∀ a : Fin n → ZMod L,
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨Csz, hCsz0, hCsz⟩ := sum_zero_unif hk0 hk1 hn
  set SW := sigWeightConst n k 2
  have hSW : 0 ≤ SW := sigWeightConst_nonneg hk0 2
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨3 ^ n * ((Csz + 19 / 4 * SW) * e8 ^ (n - 1)), by positivity, ?_⟩
  intro E hEk L _ hL t ht0 ht1 σ halt a
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
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
      ‖2 * Theta L (t : ℂ) (a v) u - Theta L (t : ℂ) (a v) (u + 1) -
        Theta L (t : ℂ) (a v) (u - 1)‖ :=
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
      ‖∑ c : ZMod L, ∑ s ∈ pinned L n 0, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖ ≤ B := by
    intro τ
    have hA0 : 0 ≤ A := by linarith
    have hB0 : 0 ≤ B := by positivity
    by_cases hR : (∃ v, τ v = 2) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ τ v₁ = 1 ∧ τ v₂ = 1
    · -- the remainder terms
      have hW : ∀ s ∈ pinned L n 0, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
          (2 / 2 + 3 / 2 + 9 / 4 * 1) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
        intro s hs
        simp only [pinned, mem_filter] at hs
        exact sum_prod_taylor_le f a hA hsup hl1 hgrad hlap hoff hMoff h₁ h₂ (by norm_num)
          (by norm_num) τ hR s hs.2
      have hS := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ (by omega) 2
      calc ‖∑ c : ZMod L, ∑ s ∈ pinned L n 0, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖
          ≤ ∑ c : ZMod L, ∑ s ∈ pinned L n 0, ‖g s‖ * ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
            refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
            rw [norm_mul, norm_prod]
        _ = ∑ s ∈ pinned L n 0, ‖g s‖ * ∑ c : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            rw [sum_comm]; simp only [mul_sum]
        _ ≤ ∑ s ∈ pinned L n 0, ‖g s‖ *
              ((2 / 2 + 3 / 2 + 9 / 4 * 1) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
            sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hW s hs) (norm_nonneg _)
        _ = 19 / 4 * A ^ (n - 1) *
              ∑ s ∈ pinned L n 0, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
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
      have hzero : ‖∑ s ∈ pinned L n 0, g s‖ ≤ Csz * η := by
        have h := hCsz E hEk L hL t ht0.le ht1 σ halt
        have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
        rw [sum_eq_mul_sum_pinned g hgadd, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul] at h
        exact h
      calc ‖∑ c : ZMod L, ∏ v, f v c‖ * ‖∑ s ∈ pinned L n 0, g s‖
          ≤ (η⁻¹ * A ^ (n - 1)) * (Csz * η) := by gcongr
        _ = Csz * A ^ (n - 1) := by field_simp
        _ ≤ B := by
            simp only [B]
            have : 0 ≤ SW * A ^ (n - 1) := by positivity
            nlinarith
  rw [Kpi_empty_expand hL hE ht0.le ht1 σ a]
  calc ‖∑ τ : Fin n → Fin 3, ∑ c : ZMod L, ∑ s ∈ pinned L n 0,
          g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖
      ≤ ∑ τ : Fin n → Fin 3, B := (norm_sum_le _ _).trans (sum_le_sum fun τ _ => hterm τ)
    _ = 3 ^ n * B := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring
    _ = 3 ^ n * ((Csz + 19 / 4 * SW) * e8 ^ (n - 1)) * (η * ℓ)⁻¹ ^ (n - 1) := by
        simp only [B, A, mul_pow]; ring
/-- **Lemma 3.11, (3.45), for `π = ∅` and `σ` with a short boundary edge**. -/
private theorem norm_Kpi_empty_short_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
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
  intro E hEk L _ hL t ht0 ht1 σ ⟨v₀, hv₀⟩ a
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
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
  calc ‖∑ c : ZMod L, ∑ s ∈ pinned L n 0,
          SigmaPi L (mSigma E) t σ ∅ (fun v => s v + c) * ∏ v, θ v (a v) (s v + c)‖
      ≤ ∑ c : ZMod L, ∑ s ∈ pinned L n 0, ‖g s‖ * ∏ v, ‖θ v (a v) (s v + c)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
        rw [norm_mul, norm_prod, show SigmaPi L (mSigma E) t σ ∅ (fun v => s v + c) = g s from
          hgadd s c]
    _ = ∑ s ∈ pinned L n 0, ‖g s‖ * ∑ c : ZMod L, ∏ v, ‖θ v (a v) (s v + c)‖ := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ s ∈ pinned L n 0, ‖g s‖ * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by
        refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ∑ c : ZMod L, ∏ v, ‖θ v (a v) (s v + c)‖
            = ∑ c : ZMod L, ‖θ v₀ (a v₀) (s v₀ + c)‖ *
                ∏ v ∈ univ.erase v₀, ‖θ v (a v) (s v + c)‖ := by
              refine sum_congr rfl fun c _ => ?_
              rw [mul_prod_erase _ (fun v => ‖θ v (a v) (s v + c)‖) (mem_univ v₀)]
          _ ≤ (∑ c : ZMod L, ‖θ v₀ (a v₀) (s v₀ + c)‖) * ∏ _v ∈ univ.erase v₀, (Bk * A) :=
              sum_mul_prod_le _ (fun v c => ‖θ v (a v) (s v + c)‖) _ _ (fun c => norm_nonneg _)
                (fun v c => norm_nonneg _) fun v _ c => hsup v _ _
          _ ≤ (Bk * S1) * (Bk * A) ^ (n - 1) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 _ _
    _ = (∑ s ∈ pinned L n 0, ‖g s‖) * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by rw [sum_mul]
    _ ≤ SW0 * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by gcongr
    _ = SW0 * (Bk * S1) * (Bk * e8) ^ (n - 1) * (η * ℓ)⁻¹ ^ (n - 1) := by
        simp only [A, mul_pow]; ring
/-- **Lemma 3.11, (3.45), for `π = ∅`, uniform in the bulk energy.** -/
private theorem norm_Kpi_empty_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ : Fin n → Bool) (a : Fin n → ZMod L),
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_Kpi_empty_alt_le_unif hk0 hk1 hn
  obtain ⟨C₂, hC₂, h₂⟩ := norm_Kpi_empty_short_le_unif hk0 hk1 (n := n) (by omega)
  refine ⟨C₁ + C₂, by positivity, fun E hEk L _ hL t ht0 ht1 σ a => ?_⟩
  have hE : |E| < 2 := by linarith
  have hX : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
    have := etaT_pos hE ht1
    have := one_le_ellHat L hL ht0.le ht1
    positivity
  by_cases halt : ∀ v, σ v ≠ σ (v + 1)
  · exact (h₁ E hEk L hL t ht0 ht1 σ halt a).trans (by nlinarith)
  · push Not at halt
    exact (h₂ E hEk L hL t ht0 ht1 σ halt a).trans (by nlinarith)
/-- **Lemma 3.11, (3.45)**: for `|E| ≤ 2 - k` there is `C = C(N_max, k)` with
`|K^(π)_{t,σ,a}| ≤ C (η_t ℓ̂(t))^{-(n-1)}` for every `3 ≤ n ≤ N_max`, every `σ`, `a`, every `π`,
every `0 < t < 1` and every `L ≥ 3`. -/
private theorem norm_Kpi_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n], 3 ≤ n → n ≤ Nmax → ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
        ∀ (σ : Fin n → Bool) (a : Fin n → ZMod L) (π : Finset (Fin n × Fin n)),
          ‖Kpi L (mSigma E) t σ a π‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  -- the inner molecules, uniformly in their size
  obtain ⟨Cin, hCin0, hCin⟩ := exists_uniform (P := fun N C =>
      ∀ [NeZero N], ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
        ∀ (σ' : Fin N → Bool) (p : Fin N), σ' p ≠ σ' (p + 1) → ∀ a' : Fin N → ZMod L,
          ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
            ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2))
    (fun N C C' hP hCC' => fun E hEk L _ hL t ht0 ht1 σ' p hp a' => by
      have hE : |E| < 2 := by linarith
      have hb := hP E hEk L hL t ht0 ht1 σ' p hp a'
      have : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
        have := etaT_pos hE ht1; have := one_le_ellHat L hL ht0.le ht1; positivity
      exact hb.trans (by nlinarith))
    (fun N hN => by
      have : NeZero N := ⟨by omega⟩
      obtain ⟨C, hC0, hC⟩ := sum_norm_innerId_le_unif hk0 hk1 (N := N) hN
      exact ⟨C, hC0,
        fun E hEk L _ hL t ht0 ht1 σ' p hp a' => hC E hEk L hL t ht0 ht1 σ' p hp a'⟩) Nmax
  induction Nmax with
  | zero => exact ⟨0, le_rfl, fun n _ h3 hN => by omega⟩
  | succ N ih =>
  obtain ⟨C, hC0, hC⟩ := ih (fun N' hN' hN'N => hCin N' hN' (by omega))
  by_cases h3 : 3 ≤ N + 1
  swap
  · exact ⟨C, hC0, fun n _ hn hnN => by omega⟩
  have : NeZero (N + 1) := ⟨by omega⟩
  obtain ⟨Ce, hCe0, hCe⟩ := norm_Kpi_empty_le_unif hk0 hk1 (n := N + 1) h3
  refine ⟨C + Ce + Cin * C, by positivity, fun n _ hn hnN E hEk L _ hL t ht0 ht1 σ a π => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set X := (etaT E t * ellHat L (t : ℂ))⁻¹ with hXdef
  have hX0 : 0 ≤ X := by
    have := etaT_pos hE ht1; have := one_le_ellHat L hL ht0.le ht1; positivity
  have hXn : 0 ≤ X ^ (n - 1) := pow_nonneg hX0 _
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · refine (hC n hn (by omega) E hEk L hL t ht0 ht1 σ a π).trans ?_
    have : 0 ≤ (Ce + Cin * C) * X ^ (n - 1) := by positivity
    nlinarith
  obtain rfl : n = N + 1 := by omega
  by_cases hπ0 : π = ∅
  · subst hπ0
    refine (hCe E hEk L hL t ht0 ht1 σ a).trans ?_
    have : 0 ≤ (C + Cin * C) * X ^ (N + 1 - 1) := by positivity
    nlinarith
  rcases (TSPlong (N + 1) σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · simp only [Kpi, hemp, sum_empty, norm_zero]; positivity
  obtain ⟨hF₀T, hπ⟩ := mem_TSPlong.1 hF₀
  have hF₀' := isTSP_of_mem_TSP hF₀T
  have hπne : π.Nonempty := nonempty_iff_ne_empty.2 hπ0
  obtain ⟨J, hJ, hinner⟩ := exists_innermost hF₀' (σ := σ) (hπ ▸ hπne)
  rw [hπ] at hJ hinner
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  have hJd : IsDiag (N + 1) J.1 J.2 := hF₀'.1 J (Flong_subset F₀ σ (hπ ▸ hJ))
  have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJ)).2
  have hw := width_of_isDiag hJd
  have hwv : wIn J = J.2.val - J.1.val := rfl
  have hw' : wIn J + 1 < N + 1 := by
    obtain ⟨-, -, hnot⟩ := hJd
    have := J.2.isLt
    simp only [wIn]
    omega
  have hw2 : 2 ≤ wIn J := by omega
  -- the two factors
  have hroot : sigmaIn σ J (Fin.last _) ≠ sigmaIn σ J (Fin.last _ + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last _) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last, wIn]; congr 1; ext; simp only; omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]; congr 1; ext; simp only; omega
    rw [e1, e2]; exact Ne.symm hJlong
  have hin := hCin (wIn J + 1) (by omega) (by omega) E hEk L hL t ht0 ht1 (sigmaIn σ J) (Fin.last _)
    hroot (aIn J a)
  have hout : ∀ w, ‖Kpi L (mSigma E) t (sigmaOut σ J) (aOut J a w)
      ((π.erase J).image (shiftOut J))‖ ≤ C * X ^ (N + 1 - wIn J + 1 - 1) := fun w =>
    hC (N + 1 - wIn J + 1) (by omega) (by omega) E hEk L hL t ht0 ht1 _ _ _
  have hξ : ‖(t : ℂ) * (mSigma E (σ J.1) * mSigma E (σ J.2))‖ ≤ 1 := by
    rw [mSigma_mul_of_ne hE2 hJlong, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]; exact ht1.le
  rw [Kpi_cut hL (by omega) (mSigma E) hm σ hF₀T hπ hJ hinner a]
  set ξ := (t : ℂ) * (mSigma E (σ J.1) * mSigma E (σ J.2))
  set A := fun u => innerId (mSigma E) t (sigmaIn σ J) (aIn J a) (Fin.last _) u
  set B := fun w => Kpi L (mSigma E) t (sigmaOut σ J) (aOut J a w) ((π.erase J).image (shiftOut J))
  have hpow : X ^ (wIn J - 1) * X ^ (N + 1 - wIn J) = X ^ (N + 1 - 1) := by
    rw [← pow_add]; congr 1; omega
  calc ‖∑ u : ZMod L, ∑ w : ZMod L, ξ * A u * SB L u w * B w‖
      ≤ ∑ u : ZMod L, ∑ w : ZMod L, ‖A u‖ * ‖SB L u w‖ * (C * X ^ (N + 1 - wIn J)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun u _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun w _ => ?_)
        rw [norm_mul, norm_mul, norm_mul]
        have hb := hout w
        rw [show N + 1 - wIn J + 1 - 1 = N + 1 - wIn J by omega] at hb
        calc ‖ξ‖ * ‖A u‖ * ‖SB L u w‖ * ‖B w‖
            ≤ 1 * ‖A u‖ * ‖SB L u w‖ * (C * X ^ (N + 1 - wIn J)) := by
              gcongr
          _ = _ := by ring
    _ = (∑ u : ZMod L, ‖A u‖) * (C * X ^ (N + 1 - wIn J)) := by
        rw [sum_mul]
        refine sum_congr rfl fun u _ => ?_
        rw [← sum_mul, ← mul_sum, sum_norm_SB_row hL u, mul_one]
    _ ≤ (Cin * X ^ (wIn J - 1)) * (C * X ^ (N + 1 - wIn J)) := by
        gcongr
        exact hin
    _ = Cin * C * X ^ (N + 1 - 1) := by rw [← hpow]; ring
    _ ≤ (C + Ce + Cin * C) * X ^ (N + 1 - 1) := by
        have : 0 ≤ (C + Ce) * X ^ (N + 1 - 1) := by positivity
        nlinarith

/-- **Lemma 3.11, (3.46)**: `|K_{t,σ,a}| ≤ C (W η_t ℓ̂(t))^{-(n-1)}` for the loops of length
`3 ≤ n ≤ N_max`, uniformly in `L ≥ 3`, `W` and `0 < t < 1`, in the bulk `|E| ≤ 2 - k`. -/
private theorem norm_Kgen_le_unif_ge3 {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L →
      ∀ (W : ℕ) [NeZero W], ∀ t : ℝ, 0 < t → t < 1 →
      ∀ I : LoopIdx (ZMod L), I.WF → 3 ≤ I.length → I.length ≤ Nmax →
        ‖Kgen L W (mSigma E) t I‖ ≤
          C * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ ^ (I.length - 1) := by
  obtain ⟨C, hC0, hC⟩ := norm_Kpi_le_unif hk0 hk1 Nmax
  refine ⟨2 ^ (Nmax * Nmax) * C, by positivity, ?_⟩
  intro E hEk L _ hL W _ t ht0 ht1 I hI h3 hN
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  have hm1 := norm_mSigma_le_one hE
  have : NeZero I.length := ⟨by omega⟩
  set n := I.length
  have hrep := K_eq_sum_Kpi hL W (mSigma E) hm1 ht1 (isPrimitive_Kgen hL W (mSigma E) hm1 ht1)
    subset_rfl (fun s hs J hJ hJ2 => norm_Kgen_two_le hL W (mSigma E) hm1 ht1 hs J hJ hJ2)
    ⟨ht0.le, le_rfl⟩ I hI h3
  set X := (etaT E t * ellHat L (t : ℂ))⁻¹
  have hX0 : 0 ≤ X := by
    have := etaT_pos hE ht1; have := one_le_ellHat L hL ht0.le ht1; positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hprod : ‖(I.σ.map (mSigma E)).prod‖ = 1 := by
    induction I.σ with
    | nil => simp
    | cons b l ih => rw [List.map_cons, List.prod_cons, norm_mul, ih, norm_mSigma hE2, mul_one]
  have hcard : ((diagonals n).powerset.card : ℝ) ≤ 2 ^ (Nmax * Nmax) := by
    rw [card_powerset]
    have h1 : (diagonals n).card ≤ n * n := by
      calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_card (subset_univ _)
        _ = n * n := by rw [card_univ, Fintype.card_prod, Fintype.card_fin]
    have h2 : n * n ≤ Nmax * Nmax := Nat.mul_le_mul hN hN
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (h1.trans h2)
  have hWinv : ‖(W : ℂ)⁻¹ ^ (n - 1)‖ = ((W : ℝ)⁻¹) ^ (n - 1) := by
    rw [norm_pow, norm_inv, Complex.norm_natCast]
  rw [hrep, norm_mul, norm_mul, hprod, one_mul, hWinv]
  have hsum : ‖∑ π ∈ (diagonals n).powerset,
      Kpi L (mSigma E) t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π‖
        ≤ 2 ^ (Nmax * Nmax) * (C * X ^ (n - 1)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ π ∈ (diagonals n).powerset,
          ‖Kpi L (mSigma E) t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π‖
        ≤ ∑ _π ∈ (diagonals n).powerset, C * X ^ (n - 1) :=
          sum_le_sum fun π _ => hC n h3 hN E hEk L hL t ht0 ht1 _ _ π
      _ = ((diagonals n).powerset.card : ℝ) * (C * X ^ (n - 1)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ (Nmax * Nmax) * (C * X ^ (n - 1)) := by
          have : 0 ≤ C * X ^ (n - 1) := by positivity
          gcongr
  calc ((W : ℝ)⁻¹) ^ (n - 1) * ‖∑ π ∈ (diagonals n).powerset,
          Kpi L (mSigma E) t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π‖
      ≤ ((W : ℝ)⁻¹) ^ (n - 1) * (2 ^ (Nmax * Nmax) * (C * X ^ (n - 1))) := by gcongr
    _ = 2 ^ (Nmax * Nmax) * C * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ ^ (n - 1) := by
        rw [mul_inv, mul_pow]; ring
/-- **The 2-loop, uniform in the bulk energy**: `|kTwo_{t,σ,a}| ≤ C(Wη_tℓ̂(t))⁻¹`, adapting
`Band.norm_Kval_two_le` (`Flow/Iteration.lean`) off the `Band` wrapper, directly on `L, W`. -/
private theorem norm_kTwo_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ) [NeZero W],
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ s₁ s₂ : Bool, ∀ x y : ZMod L,
        ‖kTwo L W (mSigma E) t s₁ s₂ x y‖ ≤
          C * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ := by
  set Bk := 2 * cTwo52 / Real.sqrt k + 1
  have hBk : 1 ≤ Bk := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / Real.sqrt k := by
      have := Real.sqrt_nonneg k; positivity
    simp only [Bk]; linarith
  have he : 0 ≤ 8 * Real.exp 1 := by positivity
  refine ⟨Bk + 8 * Real.exp 1, by linarith, fun E hEk L _ hL W _ t ht0 ht1 s₁ s₂ x y => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hη : 0 < etaT E t := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ellHat L (t : ℂ) := by
    rw [ellHat_ofReal _ ht1]
    refine le_min ?_ (by exact_mod_cast (show 1 ≤ L by omega))
    rw [le_div_iff₀ (Real.sqrt_pos.2 (by linarith)), one_mul]
    exact Real.sqrt_le_one.2 (by linarith)
  have hηℓ : etaT E t * ellHat L (t : ℂ) ≤ 1 := by
    rcases ht0.lt_or_eq with ht0' | rfl
    · exact etaT_mul_ellHat_le hL hE2 ht0'.le ht1
    · have h1 : ellHat L ((0 : ℝ) : ℂ) = 1 := by
        rw [ellHat_ofReal _ zero_lt_one, sub_zero, Real.sqrt_one, div_one]
        exact min_eq_left (by exact_mod_cast (show 1 ≤ L by omega))
      rw [h1, mul_one, etaT, sub_zero, one_mul]
      exact mE_im_le_one hE
  have hpos : 0 < (W : ℝ) * (etaT E t * ellHat L (t : ℂ)) := by positivity
  have hWinv : (W : ℝ)⁻¹ ≤ ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ := by
    refine inv_anti₀ hpos ?_
    nlinarith
  have hS0 : 0 ≤ ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ := inv_nonneg.2 hpos.le
  rw [kTwo]
  have hm : ‖mSigma E s₁ * mSigma E s₂‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, one_mul]
  rw [norm_mul, norm_mul, hm, mul_one, norm_inv, Complex.norm_natCast]
  by_cases hss : s₁ = s₂
  · subst hss
    have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0 ht1 s₁ x y
    have h' : ‖Theta L ((t : ℂ) * (mSigma E s₁ * mSigma E s₁)) x y‖ ≤ Bk :=
      h.trans (mul_le_of_le_one_right (by linarith) (by
        rw [Real.exp_le_one_iff, neg_nonpos]; have := cZero_pos; positivity))
    calc (W : ℝ)⁻¹ * ‖Theta L ((t : ℂ) * (mSigma E s₁ * mSigma E s₁)) x y‖
        ≤ ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ * Bk :=
          mul_le_mul hWinv h' (norm_nonneg _) hS0
      _ ≤ (Bk + 8 * Real.exp 1) * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ := by nlinarith
  · rw [mSigma_mul_of_ne hE2 hss, mul_one]
    rcases ht0.lt_or_eq with ht0' | rfl
    · have h := norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0' ht1 x y
      rw [← etaT_eq_zt_im] at h
      calc (W : ℝ)⁻¹ * ‖Theta L (t : ℂ) x y‖
          ≤ (W : ℝ)⁻¹ * (8 * Real.exp 1 / (etaT E t * ellHat L (t : ℂ))) := by gcongr
        _ = 8 * Real.exp 1 * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ := by field_simp
        _ ≤ (Bk + 8 * Real.exp 1) * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ := by nlinarith
    · have h1 : ‖Theta L ((0 : ℝ) : ℂ) x y‖ ≤ 1 := by
        rw [Complex.ofReal_zero, Theta_zero, Matrix.one_apply]
        split_ifs <;> simp
      have hpos0 : 0 < (W : ℝ) * (etaT E 0 * ellHat L ((0 : ℝ) : ℂ)) := by positivity
      have hWinv0 : (W : ℝ)⁻¹ ≤ ((W : ℝ) * (etaT E 0 * ellHat L ((0 : ℝ) : ℂ)))⁻¹ := by
        refine inv_anti₀ hpos0 ?_
        nlinarith [hηℓ]
      have hS00 : 0 ≤ ((W : ℝ) * (etaT E 0 * ellHat L ((0 : ℝ) : ℂ)))⁻¹ := inv_nonneg.2 hpos0.le
      calc (W : ℝ)⁻¹ * ‖Theta L ((0 : ℝ) : ℂ) x y‖
          ≤ ((W : ℝ) * (etaT E 0 * ellHat L ((0 : ℝ) : ℂ)))⁻¹ * 1 :=
            mul_le_mul hWinv0 h1 (norm_nonneg _) hS00
        _ ≤ (Bk + 8 * Real.exp 1) * ((W : ℝ) * (etaT E 0 * ellHat L ((0 : ℝ) : ℂ)))⁻¹ := by
            nlinarith

end GUEPhaseKTildeHelpers

section GUEPhaseKTildeODE

open Metric
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Local step** (Picard–Lindelöf on one short interval).  For a vector field that is
`K`-Lipschitz in space uniformly on `[t₁, t₀]`, with `‖f t 0‖ ≤ B`, and a step `h` with
`K h ≤ 1/2`, a solution exists on `[s, s']` from any initial value `x` whenever
`t₁ ≤ s ≤ s' ≤ min (s + h) t₀`: the ball radius `a = 2 (B + K‖x‖) h` satisfies the confining
inequality `(B + K(‖x‖ + a)) h ≤ a`. -/
private theorem gueKTilde_ode_step (f : ℝ → V → V) {t1 t0 : ℝ} (K : ℝ≥0) (B h : ℝ)
    (hB0 : 0 ≤ B) (hh : 0 ≤ h) (hKh : (K : ℝ) * h ≤ 1 / 2)
    (hlip : ∀ t ∈ Icc t1 t0, LipschitzWith K (f t))
    (hcont : ∀ x, ContinuousOn (f · x) (Icc t1 t0))
    (hB : ∀ t ∈ Icc t1 t0, ‖f t 0‖ ≤ B)
    {s s' : ℝ} (hs : t1 ≤ s) (hss' : s ≤ s') (hs' : s' ≤ t0) (hsh : s' ≤ s + h) (x : V) :
    ∃ β : ℝ → V, β s = x ∧ ∀ t ∈ Icc s s', HasDerivWithinAt β (f t (β t)) (Icc s s') t := by
  have hsub : Icc s s' ⊆ Icc t1 t0 := Icc_subset_Icc hs hs'
  set a : ℝ := 2 * (B + K * ‖x‖) * h with ha
  have ha0 : 0 ≤ a := by positivity
  set Lb : ℝ := B + K * (‖x‖ + a) with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  set aN : ℝ≥0 := ⟨a, ha0⟩ with haN
  set LN : ℝ≥0 := ⟨Lb, hLb0⟩ with hLN
  have haN' : (aN : ℝ) = a := rfl
  have hLN' : (LN : ℝ) = Lb := rfl
  have hP : IsPicardLindelof f (⟨s, ⟨le_rfl, hss'⟩⟩ : Icc s s') x aN 0 LN K := by
    refine ⟨fun t ht => (hlip t (hsub ht)).lipschitzOnWith, fun y _ => (hcont y).mono hsub,
      fun t ht y hy => ?_, ?_⟩
    · have hy' : ‖y‖ ≤ ‖x‖ + a := by
        have := mem_closedBall.1 hy
        rw [dist_eq_norm] at this
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ ‖x‖ + a := by rw [haN'] at this; linarith
      have hl := (hlip t (hsub ht)).dist_le_mul y 0
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at hl
      have h1 : ‖f t y‖ ≤ ‖f t 0‖ + K * ‖y‖ := by
        calc ‖f t y‖ = ‖(f t y - f t 0) + f t 0‖ := by rw [sub_add_cancel]
          _ ≤ ‖f t y - f t 0‖ + ‖f t 0‖ := norm_add_le _ _
          _ ≤ K * ‖y‖ + ‖f t 0‖ := by linarith
          _ = ‖f t 0‖ + K * ‖y‖ := by ring
      rw [hLN']
      have := hB t (hsub ht)
      have hK0 : (0 : ℝ) ≤ K := K.2
      nlinarith
    · simp only [haN', hLN', NNReal.coe_zero, sub_zero, sub_self]
      have hmax : max (s' - s) 0 ≤ h := max_le (by linarith) hh
      have hK0 : (0 : ℝ) ≤ K := K.2
      calc Lb * max (s' - s) 0 ≤ Lb * h := mul_le_mul_of_nonneg_left hmax hLb0
        _ = (B + K * ‖x‖) * h + a * (K * h) := by rw [hLb]; ring
        _ ≤ (B + K * ‖x‖) * h + a * (1 / 2) := by gcongr
        _ = a := by rw [ha]; ring
  obtain ⟨β, hβ0, hβ⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ0, hβ⟩

omit [CompleteSpace V] in
/-- **Gluing**: solutions on `[t₁, s]` and `[s, s']` agreeing at `s` give a solution on
`[t₁, s']` (`HasDerivWithinAt.union`). -/
private theorem gueKTilde_ode_glue (f : ℝ → V → V) {t1 s s' : ℝ} (h1 : t1 ≤ s) (h2 : s ≤ s')
    (α β : ℝ → V) (hα : ∀ t ∈ Icc t1 s, HasDerivWithinAt α (f t (α t)) (Icc t1 s) t)
    (hβ : ∀ t ∈ Icc s s', HasDerivWithinAt β (f t (β t)) (Icc s s') t) (hαβ : β s = α s) :
    ∀ t ∈ Icc t1 s', HasDerivWithinAt (fun u => if u ≤ s then α u else β u)
      (f t (if t ≤ s then α t else β t)) (Icc t1 s') t := by
  intro t ht
  rw [← Icc_union_Icc_eq_Icc h1 h2]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases hts : t ≤ s
    · rw [ite_eq_left hts]
      exact (hα t ⟨ht.1, hts⟩).congr_of_mem (fun u hu => ite_eq_left hu.2) ⟨ht.1, hts⟩
    · have : t ∉ closure (Icc t1 s) := by rw [closure_Icc]; exact fun h => hts h.2
      exact HasFDerivWithinAt.of_notMem_closure this
  · by_cases hts : s ≤ t
    · have hγ : (if t ≤ s then α t else β t) = β t := by
        split_ifs with h
        · have : t = s := le_antisymm h hts
          subst this; exact hαβ.symm
        · rfl
      rw [hγ]
      refine (hβ t ⟨hts, ht.2⟩).congr_of_mem (fun u hu => ?_) ⟨hts, ht.2⟩
      split_ifs with h
      · have : u = s := le_antisymm h hu.1
        subst this; exact hαβ.symm
      · rfl
    · have : t ∉ closure (Icc s s') := by rw [closure_Icc]; exact fun h => hts h.1
      exact HasFDerivWithinAt.of_notMem_closure this

/-- **Global existence for a globally Lipschitz ODE on a compact interval**: chaining the local
Picard–Lindelöf theorem in steps of fixed length `h` with `K h ≤ 1/2`. -/
private theorem gueKTilde_ode_global (f : ℝ → V → V) {t1 t0 : ℝ} (h10 : t1 ≤ t0) (K : ℝ≥0)
    (hlip : ∀ t ∈ Icc t1 t0, LipschitzWith K (f t))
    (hcont : ∀ x, ContinuousOn (f · x) (Icc t1 t0)) (x0 : V) :
    ∃ α : ℝ → V, α t1 = x0 ∧ ∀ t ∈ Icc t1 t0, HasDerivWithinAt α (f t (α t)) (Icc t1 t0) t := by
  obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont 0)
  set B := max B' 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ t ∈ Icc t1 t0, ‖f t 0‖ ≤ B := fun t ht => (hB' t ht).trans (le_max_left _ _)
  set h : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hhdef
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hh : 0 < h := by positivity
  have hKh : (K : ℝ) * h ≤ 1 / 2 := by
    rw [hhdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set sm : ℕ → ℝ := fun m => min (t1 + m * h) t0 with hsm
  have hsm_ge : ∀ m, t1 ≤ sm m := by
    intro m
    have : (0:ℝ) ≤ m * h := by positivity
    exact le_min (by linarith) h10
  have hsm_le : ∀ m, sm m ≤ t0 := fun m => min_le_right _ _
  have claim : ∀ m : ℕ, ∃ α : ℝ → V, α t1 = x0 ∧
      ∀ t ∈ Icc t1 (sm m), HasDerivWithinAt α (f t (α t)) (Icc t1 (sm m)) t := by
    intro m
    induction m with
    | zero =>
      have h0 : sm 0 = t1 := by simp [hsm, h10]
      rw [h0]
      exact gueKTilde_ode_step f K B h hB0 hh.le hKh hlip hcont hB le_rfl le_rfl h10
        (by linarith) x0
    | succ m ih =>
      obtain ⟨α, hα0, hα⟩ := ih
      have hmono : sm m ≤ sm (m + 1) := by
        simp only [hsm]; push_cast
        exact min_le_min_right _ (by nlinarith)
      have hstep : sm (m + 1) ≤ sm m + h := by
        simp only [hsm]; push_cast
        rcases le_total (t1 + m * h) t0 with hc | hc
        · rw [min_eq_left hc]
          exact (min_le_left _ _).trans (by linarith)
        · rw [min_eq_right hc]
          exact (min_le_right _ _).trans (by linarith)
      obtain ⟨β, hβ0, hβ⟩ := gueKTilde_ode_step f K B h hB0 hh.le hKh hlip hcont hB
        (hsm_ge m) hmono (hsm_le _) hstep (α (sm m))
      refine ⟨fun u => if u ≤ sm m then α u else β u, ?_, ?_⟩
      · simp only [ite_eq_left (hsm_ge m), hα0]
      · exact gueKTilde_ode_glue f (hsm_ge m) hmono α β hα hβ hβ0
  obtain ⟨m, hm⟩ := exists_nat_ge ((t0 - t1) / h)
  have hsmm : sm m = t0 := by
    simp only [hsm]
    apply min_eq_right
    have := (div_le_iff₀ hh).1 hm
    linarith
  obtain ⟨α, hα0, hα⟩ := claim m
  rw [hsmm] at hα
  exact ⟨α, hα0, hα⟩

end GUEPhaseKTildeODE

end RBM

namespace RBM.Gauss.GUEGrid

open RBM Set

/-- `primRhsGUE K I` only reads `K` on well-formed loops of length `2..|I|`. -/
private theorem gueKTilde_primRhsGUE_congr (L W : ℕ) [NeZero L] {K K' : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF)
    (h : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → K J = K' J) :
    GUEPhase.primRhsGUE L W K I = GUEPhase.primRhsGUE L W K' I := by
  unfold GUEPhase.primRhsGUE GUEPhase.primBilGUE
  congr 1
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [h _ (hI.cutGlueL a hk.1 hl.1 hl.2) (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
      (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2),
    h _ (hI.cutGlueR b hk.1 hl.1 hl.2) (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
      (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)]

/-- On a loop of length `1` the right side of (7.33) is the empty sum. -/
private theorem gueKTilde_primRhsGUE_len_one (L W : ℕ) [NeZero L] (K : LoopIdx (ZMod L) → ℂ)
    {I : LoopIdx (ZMod L)} (h : I.length = 1) : GUEPhase.primRhsGUE L W K I = 0 := by
  unfold GUEPhase.primRhsGUE GUEPhase.primBilGUE
  rw [h]
  simp

/-- A well-formed loop of length `2` is `⟨[σ₁, σ₂], [a, b]⟩`. -/
private theorem gueKTilde_eq_two {L : ℕ} {J : LoopIdx (ZMod L)} (hJ : J.WF) (h : J.length = 2) :
    ∃ (σ₁ σ₂ : Bool) (a b : ZMod L), J = ⟨[σ₁, σ₂], [a, b]⟩ := by
  obtain ⟨σ, a⟩ := J
  have ha : a.length = 2 := h
  have hσ : σ.length = 2 := hJ.trans ha
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  exact ⟨s₁, s₂, x, y, rfl⟩

/-- The two hypotheses of `hasDerivAt_kTwoGUELoop` on `[t₁, t₀] ⊂ [0, 1)`. -/
private theorem gueKTilde_norm_lt {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) : ‖(t : ℂ) * (mSigma E σ₁ * mSigma E σ₂)‖ < 1 := by
  rw [norm_mul, norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht0]
  linarith

/-- Existence of the GUE-phase primitive loops up to length `n ≥ 2`, by induction on `n`. -/
private theorem gueKTilde_exists_upto (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| < 2) {t1 t0 : ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n : ℕ)
    (hn : 2 ≤ n) :
    ∃ K : ℝ → LoopIdx (ZMod L) → ℂ,
      (∀ J : LoopIdx (ZMod L), J.WF → 1 ≤ J.length → J.length ≤ n →
        K t1 J = Kgen L W (mSigma E) t1 J) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ J : LoopIdx (ZMod L), J.WF → 1 ≤ J.length → J.length ≤ n →
        HasDerivWithinAt (fun s => K s J) (GUEPhase.primRhsGUE L W (K t) J)
          (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : ZMod L,
        K t ⟨[σ₁, σ₂], [a, b]⟩ = GUEPhase.kTwoGUE L W (mSigma E) t1 t σ₁ σ₂ a b) := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- lengths `1` (constant) and `2` (the closed form `kTwoGUELoop`)
    set K : ℝ → LoopIdx (ZMod L) → ℂ := fun t J =>
      if J.length = 1 then Kgen L W (mSigma E) t1 J
      else GUEPhase.kTwoGUELoop L W (mSigma E) t1 t J with hKdef
    have hK2 : ∀ t (J : LoopIdx (ZMod L)), 2 ≤ J.length →
        K t J = GUEPhase.kTwoGUELoop L W (mSigma E) t1 t J := by
      intro t J h
      exact ite_eq_right (by omega)
    refine ⟨K, fun J hJ h1 h2 => ?_, fun t ht J hJ h1 h2 => ?_, fun t ht σ₁ σ₂ a b => ?_⟩
    · rcases Nat.lt_or_ge J.length 2 with h | h
      · exact ite_eq_left (by omega)
      · obtain ⟨σ₁, σ₂, a, b, rfl⟩ := gueKTilde_eq_two hJ (by omega)
        rw [hK2 t1 _ h, Kgen_two, ← GUEPhase.kTwoGUE_self L W]
        rfl
    · rcases Nat.lt_or_ge J.length 2 with h | h
      · have hl : J.length = 1 := by omega
        have e : (fun s => K s J) = fun _ => Kgen L W (mSigma E) t1 J :=
          funext fun s => ite_eq_left hl
        rw [e, gueKTilde_primRhsGUE_len_one L W _ hl]
        exact hasDerivWithinAt_const _ _ _
      · obtain ⟨σ₁, σ₂, a, b, rfl⟩ := gueKTilde_eq_two hJ (by omega)
        have e : (fun s => K s ⟨[σ₁, σ₂], [a, b]⟩) =
            fun s => GUEPhase.kTwoGUELoop L W (mSigma E) t1 s ⟨[σ₁, σ₂], [a, b]⟩ :=
          funext fun s => hK2 s _ h
        rw [e, gueKTilde_primRhsGUE_congr L W hJ (K' := GUEPhase.kTwoGUELoop L W (mSigma E) t1 t)
          (fun J' _ hJ' _ => hK2 t J' hJ')]
        refine (GUEPhase.hasDerivAt_kTwoGUELoop L W hL (mSigma E) σ₁ σ₂
          (gueKTilde_norm_lt hE ht1 (by linarith) σ₁ σ₂) ?_ a b).hasDerivWithinAt
        intro h1
        have := gueKTilde_norm_lt hE (ht1.trans ht.1) (by linarith [ht.2]) σ₁ σ₂
        rw [h1, norm_one] at this
        exact lt_irrefl _ this
    · rw [hK2 t _ (le_refl 2)]
      rfl
  | succ n hn ih =>
    obtain ⟨Kp, hq1, hq2, hq3⟩ := ih
    -- the unknown slice: well-formed loops of length `n + 1`
    have hSfin : {J : LoopIdx (ZMod L) | J.WF ∧ J.length = n + 1}.Finite :=
      (GUEPhase.finite_loopIdx L (n + 1)).subset fun J hJ => by
        obtain ⟨h1, h2⟩ := hJ
        exact ⟨h1, by omega, h2.le⟩
    set S := hSfin.toFinset with hSdef
    have hmemS : ∀ J, J ∈ S ↔ J.WF ∧ J.length = n + 1 := fun J => hSfin.mem_toFinset
    -- the shorter lengths are continuous, hence bounded, on `[t₁, t₀]`
    have hcontK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ContinuousOn (fun t => Kp t J) (Set.Icc t1 t0) := fun J hJ h2 hn' t ht =>
      (hq2 t ht J hJ (by omega) hn').continuousWithinAt
    have hTfin := GUEPhase.finite_loopIdx L n
    set T := hTfin.toFinset
    obtain ⟨M', hM'⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun t (J : T) => Kp t J.1) (s := Set.Icc t1 t0) (continuousOn_pi.2 fun J => by
        have hJ := hTfin.mem_toFinset.1 J.2
        exact hcontK J.1 hJ.1 hJ.2.1 hJ.2.2)
    set M := max M' 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hM : ∀ t ∈ Set.Icc t1 t0, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
        J.length ≤ n → ‖Kp t J‖ ≤ M := by
      intro t ht J hJ h2 hn'
      have hJT : J ∈ T := hTfin.mem_toFinset.2 ⟨hJ, h2, hn'⟩
      exact (norm_le_pi_norm (fun J : T => Kp t J.1) ⟨J, hJT⟩).trans
        ((hM' t ht).trans (le_max_left _ _))
    -- the vector field of the linear ODE for the length-`(n+1)` slice
    let g : ℝ → (S → ℂ) → LoopIdx (ZMod L) → ℂ := fun t y J =>
      if h : J ∈ S then y ⟨J, h⟩ else Kp t J
    let f : ℝ → (S → ℂ) → (S → ℂ) := fun t y I => GUEPhase.primRhsGUE L W (g t y) I.1
    have hgS : ∀ t y (J : LoopIdx (ZMod L)) (h : J ∈ S), g t y J = y ⟨J, h⟩ :=
      fun t y J h => dite_eq_left h
    have hgN : ∀ t y (J : LoopIdx (ZMod L)), J ∉ S → g t y J = Kp t J :=
      fun t y J h => dite_eq_right h
    have hnotS : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ n + 1 → J ∉ S → J.length ≤ n := by
      intro J hJ hl hS
      by_contra hc
      exact hS ((hmemS J).2 ⟨hJ, by omega⟩)
    -- continuity in `t`
    have hcont : ∀ y, ContinuousOn (fun t => f t y) (Set.Icc t1 t0) := by
      intro y
      refine continuousOn_pi.2 fun I => ?_
      have hI := (hmemS I.1).1 I.2
      have hg : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n + 1 →
          ContinuousOn (fun t => g t y J) (Set.Icc t1 t0) := by
        intro J hJ h2 hl
        by_cases hS : J ∈ S
        · simp only [hgS _ _ _ hS]
          exact continuousOn_const
        · simp only [hgN _ _ _ hS]
          exact hcontK J hJ h2 (hnotS J hJ hl hS)
      change ContinuousOn (fun t => (W : ℂ) * ∑ k ∈ Finset.Icc 1 I.1.length,
        ∑ l ∈ Finset.Ioc k I.1.length, ∑ a : ZMod L, ∑ b : ZMod L,
          g t y (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b * g t y (I.1.cutGlueR k l b))
        (Set.Icc t1 t0)
      refine continuousOn_const.mul (continuousOn_finsetSum _ fun k hk =>
        continuousOn_finsetSum _ fun l hl => continuousOn_finsetSum _ fun a _ =>
          continuousOn_finsetSum _ fun b _ => ?_)
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc] at hl
      exact ((hg _ (hI.1.cutGlueL a hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueL I.1 a hk.1 hl.1 hl.2)
        ((LoopIdx.length_cutGlueL_le I.1 a hk.1 hl.1 hl.2).trans hI.2.le)).mul
          continuousOn_const).mul
        (hg _ (hI.1.cutGlueR b hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueR I.1 b hk.1 hl.1 hl.2)
        ((LoopIdx.length_cutGlueR_le I.1 b hk.1 hl.1 hl.2).trans hI.2.le))
    -- the uniform Lipschitz bound: at most one cut factor has length `n + 1`
    set c0 : ℝ := (L : ℝ)⁻¹ * M with hc0
    have hc00 : 0 ≤ c0 := by positivity
    set C : ℝ := (W : ℝ) * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
      ∑ a : ZMod L, ∑ b : ZMod L, c0 with hCdef
    have hC0 : 0 ≤ C := by positivity
    set CN : NNReal := ⟨C, hC0⟩ with hCNdef
    have hCN : (CN : ℝ) = C := rfl
    have hlip : ∀ t ∈ Set.Icc t1 t0, LipschitzWith CN (f t) := by
      intro t ht
      refine LipschitzWith.of_dist_le_mul fun y y' => ?_
      rw [dist_eq_norm, dist_eq_norm, hCN]
      set δ := ‖y - y'‖ with hδ
      have hδ0 : 0 ≤ δ := norm_nonneg _
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun I => ?_
      have hI := (hmemS I.1).1 I.2
      have hterm : ∀ k ∈ Finset.Icc 1 (n + 1), ∀ l ∈ Finset.Ioc k (n + 1), ∀ a b : ZMod L,
          ‖g t y (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b * g t y (I.1.cutGlueR k l b) -
            g t y' (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b * g t y' (I.1.cutGlueR k l b)‖
            ≤ c0 * δ := by
        intro k hk l hl a b
        rw [Finset.mem_Icc] at hk
        rw [Finset.mem_Ioc] at hl
        have hl2 : l ≤ I.1.length := hI.2 ▸ hl.2
        have hsum := LoopIdx.length_cutGlueL_add_length_cutGlueR I.1 a hk.1 hl.1 hl2
        have hLR : (I.1.cutGlueR k l b).length = (I.1.cutGlueR k l a).length := by
          rw [LoopIdx.length_cutGlueR I.1 b hk.1 hl.1 hl2,
            LoopIdx.length_cutGlueR I.1 a hk.1 hl.1 hl2]
        have hWL := hI.1.cutGlueL a hk.1 hl.1 hl2
        have hWR := hI.1.cutGlueR b hk.1 hl.1 hl2
        have h2L := LoopIdx.two_le_length_cutGlueL I.1 a hk.1 hl.1 hl2
        have h2R := LoopIdx.two_le_length_cutGlueR I.1 b hk.1 hl.1 hl2
        have hleL := (LoopIdx.length_cutGlueL_le I.1 a hk.1 hl.1 hl2).trans hI.2.le
        have hleR := (LoopIdx.length_cutGlueR_le I.1 b hk.1 hl.1 hl2).trans hI.2.le
        have hSB : ‖GUEPhase.SBgue L a b‖ = (L : ℝ)⁻¹ := by
          rw [GUEPhase.SBgue_apply, norm_inv, Complex.norm_natCast]
        have hcoord : ∀ (J : LoopIdx (ZMod L)) (h : J ∈ S), ‖y ⟨J, h⟩ - y' ⟨J, h⟩‖ ≤ δ :=
          fun J h => norm_le_pi_norm (y - y') ⟨J, h⟩
        have hL0 : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
        by_cases hSL : I.1.cutGlueL k l a ∈ S <;> by_cases hSR : I.1.cutGlueR k l b ∈ S
        · exfalso
          have h1 := ((hmemS _).1 hSL).2
          have h2 := ((hmemS _).1 hSR).2
          omega
        · rw [hgS _ _ _ hSL, hgS _ _ _ hSL, hgN _ _ _ hSR, hgN _ _ _ hSR,
            show ∀ u v s w : ℂ, u * s * w - v * s * w = (u - v) * s * w from
              fun u v s w => by ring, norm_mul, norm_mul, hSB]
          have hKb := hM t ht _ hWR h2R (hnotS _ hWR hleR hSR)
          calc ‖y ⟨_, hSL⟩ - y' ⟨_, hSL⟩‖ * (L : ℝ)⁻¹ * ‖Kp t (I.1.cutGlueR k l b)‖
              ≤ δ * (L : ℝ)⁻¹ * M := by gcongr; exact hcoord _ hSL
            _ = c0 * δ := by rw [hc0]; ring
        · rw [hgN _ _ _ hSL, hgN _ _ _ hSL, hgS _ _ _ hSR, hgS _ _ _ hSR,
            show ∀ u v s w : ℂ, w * s * u - w * s * v = w * s * (u - v) from
              fun u v s w => by ring, norm_mul, norm_mul, hSB]
          have hKb := hM t ht _ hWL h2L (hnotS _ hWL hleL hSL)
          calc ‖Kp t (I.1.cutGlueL k l a)‖ * (L : ℝ)⁻¹ * ‖y ⟨_, hSR⟩ - y' ⟨_, hSR⟩‖
              ≤ M * (L : ℝ)⁻¹ * δ := by gcongr; exact hcoord _ hSR
            _ = c0 * δ := by rw [hc0]; ring
        · rw [hgN _ _ _ hSL, hgN _ _ _ hSL, hgN _ _ _ hSR, hgN _ _ _ hSR, sub_self, norm_zero]
          positivity
      have hIlen : I.1.length = n + 1 := hI.2
      calc ‖(f t y - f t y') I‖
          = ‖(W : ℂ) * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : ZMod L, ∑ b : ZMod L,
              (g t y (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b * g t y (I.1.cutGlueR k l b) -
                g t y' (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b *
                  g t y' (I.1.cutGlueR k l b))‖ := by
            simp only [Pi.sub_apply, f, GUEPhase.primRhsGUE, GUEPhase.primBilGUE, hIlen,
              ← mul_sub, ← Finset.sum_sub_distrib]
        _ = (W : ℝ) * ‖∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : ZMod L, ∑ b : ZMod L,
              (g t y (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b * g t y (I.1.cutGlueR k l b) -
                g t y' (I.1.cutGlueL k l a) * GUEPhase.SBgue L a b *
                  g t y' (I.1.cutGlueR k l b))‖ := by
            rw [norm_mul, Complex.norm_natCast]
        _ ≤ (W : ℝ) * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : ZMod L, ∑ b : ZMod L, c0 * δ := by
            gcongr
            exact norm_sum_le_of_le _ fun k hk => norm_sum_le_of_le _ fun l hl =>
              norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ => hterm k hk l hl a b
        _ = C * δ := by
            simp only [hCdef, mul_assoc, Finset.sum_mul]
    -- global existence for the length-`(n+1)` slice
    obtain ⟨α, hα0, hα⟩ := gueKTilde_ode_global f ht10 CN hlip hcont
      (fun I : S => Kgen L W (mSigma E) t1 I.1)
    refine ⟨fun t J => g t (α t) J, fun J hJ h1 hl => ?_, fun t ht J hJ h1 hl => ?_,
      fun t ht σ₁ σ₂ a b => ?_⟩
    · by_cases hS : J ∈ S
      · simp only [hgS _ _ _ hS, hα0]
      · simp only [hgN _ _ _ hS]
        exact hq1 J hJ h1 (hnotS J hJ hl hS)
    · by_cases hS : J ∈ S
      · have e : (fun s => g s (α s) J) = fun s => α s ⟨J, hS⟩ := funext fun s => hgS _ _ _ hS
        rw [e]
        exact hasDerivWithinAt_pi.1 (hα t ht) ⟨J, hS⟩
      · have hJn := hnotS J hJ hl hS
        have e : (fun s => g s (α s) J) = fun s => Kp s J := funext fun s => hgN _ _ _ hS
        rw [e, gueKTilde_primRhsGUE_congr L W hJ (K' := Kp t) fun J' hJ' _ hl' =>
          hgN _ _ _ fun hS' => by have := ((hmemS J').1 hS').2; omega]
        exact hq2 t ht J hJ h1 hJn
    · have hS : (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (ZMod L)) ∉ S := fun hS' => by
        have := ((hmemS _).1 hS').2
        simp only [LoopIdx.length, List.length_cons, List.length_nil] at this
        omega
      simp only [hgN _ _ _ hS]
      exact hq3 t ht σ₁ σ₂ a b

/-- **(7.33)**: the GUE-phase primitive loops exist on `[t₁, t₀]` for every length `≤ n₀`,
start from `Kgen` at `t₁`, and their `2`-loops are `kTwoGUE`. -/
theorem gueK_exists (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
    {t1 t0 : ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n0 : ℕ) :
    ∃ Kt : ℝ → LoopIdx (ZMod L) → ℂ,
      (∀ I, Kt t1 I = Kgen L W (mSigma E) t1 I) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ I : LoopIdx (ZMod L), I.WF → 1 ≤ I.length → I.length ≤ n0 →
        HasDerivWithinAt (fun s => Kt s I) (GUEPhase.primRhsGUE L W (Kt t) I)
          (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : ZMod L,
        Kt t ⟨[σ₁, σ₂], [a, b]⟩ = GUEPhase.kTwoGUE L W (mSigma E) t1 t σ₁ σ₂ a b) := by
  classical
  obtain ⟨K, hK1, hK2, hK3⟩ :=
    gueKTilde_exists_upto L W hL hE ht1 ht10 ht0 (max n0 2) (le_max_right _ _)
  set N := max n0 2 with hN
  refine ⟨fun t I => if I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N then K t I
    else Kgen L W (mSigma E) t1 I, fun I => ?_, fun t ht I hI h1 hl => ?_,
    fun t ht σ₁ σ₂ a b => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hK1 I h.1 h.2.1 h.2.2
    · rfl
  · have hIN : I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N := ⟨hI, h1, hl.trans (le_max_left _ _)⟩
    have e : (fun s => (fun t I => if I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N then K t I
        else Kgen L W (mSigma E) t1 I) s I) = fun s => K s I :=
      funext fun s => ite_eq_left hIN
    rw [e, gueKTilde_primRhsGUE_congr L W hI (K' := K t) fun J hJ h2 hJl =>
      ite_eq_left ⟨hJ, by omega, hJl.trans hIN.2.2⟩]
    exact hK2 t ht I hI h1 hIN.2.2
  · have h2 : (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (ZMod L)).WF ∧
        1 ≤ (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (ZMod L)).length ∧
        (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (ZMod L)).length ≤ N :=
      ⟨rfl, by simp [LoopIdx.length], by simp [LoopIdx.length, hN]⟩
    dsimp only
    rw [ite_eq_left h2]
    exact hK3 t ht σ₁ σ₂ a b

/-- **(2.59)/(3.46) with the constant uniform in the bulk energy** (needed at moving energies). -/
theorem norm_Kgen_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k → ∀ (L : ℕ) [NeZero L], 3 ≤ L →
      ∀ (W : ℕ) [NeZero W], ∀ t : ℝ, 0 < t → t < 1 →
        ∀ I : LoopIdx (ZMod L), I.WF → I.length = n →
          ‖Kgen L W (mSigma E) t I‖ ≤
            C * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ ^ (n - 1) := by
  rcases hn.eq_or_lt with rfl | hn1
  · -- length 1: `Kgen = mSigma E s`, of norm `1`.
    refine ⟨1, zero_le_one, fun E hEk L _ hL W _ t ht0 ht1 I hI hlen => ?_⟩
    have hE2 : |E| ≤ 2 := by linarith
    obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := hlen
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    rw [Kgen_one, norm_mSigma hE2, pow_zero, mul_one]
  · rcases lt_or_ge n 3 with hn3 | hn3
    · -- length 2: the closed form `kTwo`, bounded by `norm_kTwo_le_unif`.
      obtain rfl : n = 2 := by omega
      obtain ⟨C, hC0, hC⟩ := norm_kTwo_le_unif hk0 hk1
      refine ⟨C, hC0, fun E hEk L _ hL W _ t ht0 ht1 I hI hlen => ?_⟩
      obtain ⟨σ, a⟩ := I
      have ha : a.length = 2 := hlen
      have hσ : σ.length = 2 := hI.trans ha
      obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 ha
      obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
      rw [Kgen_two, pow_one]
      exact hC E hEk L hL W t ht0.le ht1 s₁ s₂ x y
    · -- length `≥ 3`: `norm_Kgen_le_unif_ge3` at `Nmax := n`.
      obtain ⟨C, hC0, hC⟩ := norm_Kgen_le_unif_ge3 hk0 hk1 n
      refine ⟨C, hC0, fun E hEk L _ hL W _ t ht0 ht1 I hI hlen => ?_⟩
      rw [← hlen]
      exact hC E hEk L hL W t ht0 ht1 I hI (by omega) (by omega)

end RBM.Gauss.GUEGrid

