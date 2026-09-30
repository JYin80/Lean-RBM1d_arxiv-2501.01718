/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.SumZero
import RBM1D.Flow.Scales

/-!
# The `∃ C after E` reorder for the constant producers of `Loop/SumZero.lean`

In `norm_Alayer_le` and `sum_zero` the existential witness for `C` is not explicit in `k` and
`n` alone: the induction of `norm_Alayer_le` adds a term `(… ) * (C * C * (mE E).im⁻¹)` at every
step, and `sum_zero`'s witness is `C * ((mE E).im⁻¹) ^ n`. Both depend on `E` through
`(mE E).im⁻¹`, an energy-dependent constant. The κ-bound pattern bounds
`(mE E).im⁻¹ ≤ 2 / √(2k)` once, via `mE_im_ge` (`Real.sqrt (2 * κ) / 2 ≤ (mE E).im` for
`0 < κ ≤ 2` and `|E| ≤ 2 - κ`, Flow/Scales.lean), and uses this κ-only bound wherever
`(mE E).im⁻¹` is part of the constant (not as part of the `η`-power exponent, which
stays `E`-dependent as an argument, not part of the witness).
-/

namespace RBM

open Finset

section KappaBound

/-- **The κ-bound needed here**: `(mE E).im⁻¹ ≤ 2/√(2k)` for `0 < k ≤ 1` and `|E| ≤ 2-k`,
from `mE_im_ge`. `private`. -/
private theorem invMEIm_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {E : ℝ}
    (hEk : |E| ≤ 2 - k) : (mE E).im⁻¹ ≤ 2 / Real.sqrt (2 * k) := by
  have hk2 : k ≤ 2 := by linarith
  have hb := mE_im_ge hk0 hk2 hEk
  have hk2' : 0 < 2 * k := by linarith
  have hpos : (0 : ℝ) < Real.sqrt (2 * k) / 2 := by positivity
  have h := inv_anti₀ hpos hb
  rwa [inv_div] at h

end KappaBound

section Induction350Unif

/-- **`norm_Alayer_le`, reordered**: `∃ C, ∀ E, |E| ≤ 2 - k → …`. Same induction on `N`, with
the κ-bound of `invMEIm_le_unif` in place of `(mE E).im⁻¹` in the constant. -/
theorem norm_Alayer_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (n : ℕ) [NeZero n], 3 ≤ n → n ≤ N →
      ∀ (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (t : ℝ), 0 ≤ t → t < 1 →
        ‖Alayer (mSigma E) t σ π‖ ≤ C * (etaT E t)⁻¹ ^ (n - 1) := by
  set invBound := (2 : ℝ) / Real.sqrt (2 * k) with hinvdef
  have hinv0 : 0 < invBound := by
    have : 0 < 2 * k := by linarith
    positivity
  induction N with
  | zero => exact ⟨0, le_rfl, fun E _ n _ h3 hN => by omega⟩
  | succ N ih =>
  obtain ⟨C, hC0, hC⟩ := ih
  have hcor0 : 0 ≤ cor37Const (N + 1) k := cor37Const_nonneg' hk0
  refine ⟨C + cor37Const (N + 1) k + (2 ^ ((N + 1) * (N + 1)) + 1) * (C * C * invBound),
    by positivity, fun E hEk n _ h3 hN σ π t ht0 ht1 => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set ι := (mE E).im with hιdef
  have hι0 : 0 < ι := mE_im_pos hE
  have hιm : ι⁻¹ ≤ invBound := invMEIm_le_unif hk0 hk1 hEk
  have hη : 0 < etaT E t := etaT_pos hE ht1
  set η := etaT E t with hηdef
  have hη' : η = (1 - t) * ι := rfl
  have hpow0 : 0 ≤ η⁻¹ ^ (n - 1) := by positivity
  have hCC : 0 ≤ C * C * invBound := by positivity
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · refine (hC E hEk n h3 (by omega) σ π t ht0 ht1).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) + 1) hCC
    linarith
  have hn : n = N + 1 := by omega
  have hne_bound : ∀ π : Finset (Fin n × Fin n), π.Nonempty →
      ‖Alayer (mSigma E) t σ π‖ ≤ C * C * invBound * η⁻¹ ^ (n - 1) := by
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
    have hkey : (1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J)) = ι⁻¹ * η⁻¹ ^ (n - 1) := by
      have h1t0 : 1 - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
      have hι0' : ι ≠ 0 := hι0.ne'
      rw [← pow_add, show wIn J + (n - wIn J) = n - 1 + 1 by omega, pow_succ, hη']
      field_simp
    have hstep : t * (1 - t) * ‖Alayer (mSigma E) t (sigmaIn σ J) ∅‖ *
          ‖Alayer (mSigma E) t (sigmaOut σ J) ((π.erase J).image (shiftOut J))‖
        ≤ C * C * ι⁻¹ * η⁻¹ ^ (n - 1) :=
      calc t * (1 - t) * ‖Alayer (mSigma E) t (sigmaIn σ J) ∅‖ *
            ‖Alayer (mSigma E) t (sigmaOut σ J) ((π.erase J).image (shiftOut J))‖
          ≤ (1 - t) * (C * η⁻¹ ^ wIn J) * (C * η⁻¹ ^ (n - wIn J)) := by
            gcongr
            all_goals nlinarith
        _ = C * C * ((1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J))) := by ring
        _ = C * C * ι⁻¹ * η⁻¹ ^ (n - 1) := by rw [hkey]; ring
    refine hstep.trans ?_
    have h0 : (0:ℝ) ≤ C * C := by positivity
    gcongr
  rcases π.eq_empty_or_nonempty with rfl | hπne
  · have hsum := norm_sum_Alayer_le hk0 hk1 hEk ht0 ht1 h3 σ
    have hmem : (∅ : Finset (Fin n × Fin n)) ∈ (diagonals n).powerset := empty_mem_powerset _
    rw [← add_sum_erase _ _ hmem] at hsum
    have hrest : ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖
        ≤ 2 ^ ((N + 1) * (N + 1)) * (C * C * invBound * η⁻¹ ^ (n - 1)) := by
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
            2 ^ ((N + 1) * (N + 1)) * (C * C * invBound * η⁻¹ ^ (n - 1)) := by
          linarith
      _ ≤ _ := by
          have h2 : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) := by positivity
          nlinarith [mul_nonneg hC0 hpow0, mul_nonneg hCC hpow0]
  · refine (hne_bound π hπne).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1))) hCC
    linarith

end Induction350Unif

section Lemma310Unif

/-- **`sum_zero`, reordered**: `∃ C, ∀ E, |E| ≤ 2 - k → …`. Same computation, with the κ-bound in
place of `(mE E).im⁻¹` in the witness. -/
theorem sum_zero_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 ≤ t → t < 1 →
        ∀ σ : Fin n → Bool, (∀ v, σ v ≠ σ (v + 1)) →
          ‖(L : ℂ)⁻¹ * ∑ d : Fin n → ZMod L, SigmaPi L (mSigma E) t σ ∅ d‖ ≤ C * etaT E t := by
  obtain ⟨C, hC0, hC⟩ := norm_Alayer_le_unif hk0 hk1 n
  set invBound := (2 : ℝ) / Real.sqrt (2 * k) with hinvdef
  have hinv0 : 0 < invBound := by
    have : 0 < 2 * k := by linarith
    positivity
  refine ⟨C * invBound ^ n, by positivity, fun E hEk L _ hL t ht0 ht1 σ halt => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set ι := (mE E).im with hιdef
  have hι0 : 0 < ι := mE_im_pos hE
  have hιm : ι⁻¹ ≤ invBound := invMEIm_le_unif hk0 hk1 hEk
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
  have hη0 : 0 ≤ etaT E t := (etaT_pos hE ht1).le
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
    _ ≤ C * invBound ^ n * etaT E t := by
        have hb : ι⁻¹ ^ n ≤ invBound ^ n := pow_le_pow_left₀ (by positivity) hιm n
        have h0 : (0:ℝ) ≤ C := hC0
        gcongr

end Lemma310Unif

end RBM
