/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowFlowMargin
import RBM1D.Gauss.PermutationFourierSemicircleZeroMode

/-! Deterministic comparison of the accepted semicircle zero-mode error with
the literal closed-flow threshold for `Dims.exampleGrow`.

This is only a scalar comparison. It makes no statement about a matrix,
sample, Gaussian local law, or membership in a flow event. -/

set_option autoImplicit false

open RBM RBM.Gauss Filter

namespace RBM.Gauss.PermutationFourierExampleGrowZeroFlowMargin

/-- The literal zero-mode error scale is eventually strictly below the
repository's closed-flow threshold at energy zero and half time. -/
theorem eventual_zero_mode_lt_flowDelta :
    ∀ᶠ N : ℕ in atTop,
      8 * Real.sqrt 2 / (Dims.exampleGrow.W N : ℝ) <
        flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
  have hWnat : ∀ᶠ N : ℕ in atTop, 1 ≤ Dims.exampleGrow.W N := by
    filter_upwards [tendsto_atTop.1 Dims.tendsto_growW 1] with N hN
    simpa only [Dims.exampleGrow_W] using hN
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hWnat, hlog,
      PermutationFourierExampleGrowFlowMargin.eventual_margin] with N hWn hlog hmargin
  have hW : (1 : ℝ) ≤ (Dims.exampleGrow.W N : ℝ) := by exact_mod_cast hWn
  let W : ℝ := Dims.exampleGrow.W N
  let x : ℝ := Real.log N
  let A : ℝ := 8 * Real.sqrt 2 / W
  let B : ℝ := 76 * Real.sqrt (x / W)
  have hWpos : 0 < W := by dsimp [W]; exact_mod_cast Dims.exampleGrow.W_pos N
  have hx : 1 ≤ x := hlog
  have hprod : 128 < 5776 * x * W := by
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx
    have hmul : 1 * 1 ≤ x * W := mul_le_mul hx hW (by norm_num) hx0
    nlinarith
  have hratio : 128 / W ^ 2 < 5776 * x / W := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < W ^ 2) hWpos]
    have hmul := mul_lt_mul_of_pos_right hprod hWpos
    nlinarith [hmul]
  have hsA : A ^ 2 = 128 / W ^ 2 := by
    dsimp [A]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsB : B ^ 2 = 5776 * x / W := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (div_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ W))]
    norm_num
    ring
  have hsq : A ^ 2 < B ^ 2 := by rw [hsA, hsB]; exact hratio
  have hApos : 0 < A := by dsimp [A]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hAB : A < B := by nlinarith
  have hmargin' : B < flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
    simpa [B, x, W] using hmargin
  dsimp [A, W]
  exact lt_trans hAB hmargin'

/-- A concrete nondegenerate witness: the growing model has positive width,
and the closed half-time interval has distinct endpoints in it. -/
theorem nondegenerate_witness :
    ∃ N : ℕ,
      0 < (Dims.exampleGrow.W N : ℝ) ∧
      (0 : ℝ) ∈ Set.Icc 0 (1 / 2) ∧
      (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) ∧
      (1 / 2 : ℝ) < 1 := by
  refine ⟨1, ?_, ?_⟩
  · exact_mod_cast Dims.exampleGrow.W_pos 1
  · exact PermutationFourierExampleGrowFlowMargin.half_time_endpoint

end RBM.Gauss.PermutationFourierExampleGrowZeroFlowMargin

#print axioms RBM.Gauss.PermutationFourierExampleGrowZeroFlowMargin.eventual_zero_mode_lt_flowDelta
#print axioms RBM.Gauss.PermutationFourierExampleGrowZeroFlowMargin.nondegenerate_witness
