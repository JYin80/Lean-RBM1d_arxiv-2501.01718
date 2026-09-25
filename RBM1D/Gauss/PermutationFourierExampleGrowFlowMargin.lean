/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Deterministic half-time scale and strict numerical margin for `Dims.exampleGrow`.

This compares the Fourier auxiliary error scale with the literal closed-flow threshold;
it makes no claim about a sample or good-event membership. -/

set_option autoImplicit false

open RBM RBM.Gauss Filter

namespace RBM.Gauss.PermutationFourierExampleGrowFlowMargin

theorem scale_half (N : ℕ) :
    (band Dims.exampleGrow).scale 0 N (1 / 2) =
      (Dims.exampleGrow.W N : ℝ) * Real.sqrt (1 / 2) := by
  have hL : (3 : ℝ) ≤ (Dims.exampleGrow.L N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.three_le_L N
  have hsqrt : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  have hmin : min (Real.sqrt (1 / 2 : ℝ)) ((Dims.exampleGrow.L N : ℝ) / 2) =
      Real.sqrt (1 / 2 : ℝ) := by
    apply min_eq_left
    linarith
  change (Dims.exampleGrow.W N : ℝ) *
      ellHat (Dims.exampleGrow.L N) ((1 / 2 : ℝ) : ℂ) * etaT 0 (1 / 2) = _
  rw [ellHat_ofReal _ (by norm_num : (1 / 2 : ℝ) < 1)]
  rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
  rw [show etaT 0 (1 / 2) = 1 / 2 by
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [etaT, mE_im, hs4]]
  have hs : Real.sqrt (1 / 2 : ℝ) > 0 := Real.sqrt_pos.2 (by norm_num)
  have hrec : (1 / Real.sqrt (1 / 2 : ℝ)) * (1 / 2 : ℝ) =
      Real.sqrt (1 / 2) := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  calc
    (Dims.exampleGrow.W N : ℝ) *
        min (1 / Real.sqrt (1 / 2 : ℝ)) (Dims.exampleGrow.L N : ℝ) * (1 / 2) =
        (Dims.exampleGrow.W N : ℝ) *
          (min (1 / Real.sqrt (1 / 2 : ℝ)) (Dims.exampleGrow.L N : ℝ) * (1 / 2)) := by ring
    _ = (Dims.exampleGrow.W N : ℝ) *
          min ((1 / Real.sqrt (1 / 2 : ℝ)) * (1 / 2))
            ((Dims.exampleGrow.L N : ℝ) * (1 / 2)) := by
            rw [min_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = _ := by rw [hrec]; convert congrArg ((Dims.exampleGrow.W N : ℝ) * ·) hmin using 1 <;> ring

theorem half_time_endpoint :
    (0 : ℝ) ∈ Set.Icc 0 (1 / 2) ∧ (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) ∧
      (1 / 2 : ℝ) < 1 := by
  norm_num

theorem scale_half_pos (N : ℕ) :
    0 < (band Dims.exampleGrow).scale 0 N (1 / 2) := by
  rw [scale_half]
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  exact mul_pos hW (Real.sqrt_pos.2 (by norm_num))


theorem numeric_margin {W x : ℝ} (hW : 0 < W) (hx : 0 ≤ x)
    (h : 5776 * x < W ^ ((2 : ℝ) / 3)) :
    76 * Real.sqrt (x / W) < W ^ (-(1 : ℝ) / 6) := by
  have hq : 0 ≤ x / W := div_nonneg hx hW.le
  have hleft : 0 ≤ 76 * Real.sqrt (x / W) := by positivity
  have hright : 0 < W ^ (-(1 : ℝ) / 6) := Real.rpow_pos_of_pos hW _
  have hpow : W * W ^ (-(1 : ℝ) / 3) = W ^ ((2 : ℝ) / 3) := by
    calc
      W * W ^ (-(1 : ℝ) / 3) = W ^ (1 : ℝ) * W ^ (-(1 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = W ^ ((2 : ℝ) / 3) := by rw [← Real.rpow_add hW]; congr 1; ring
  have hdiv : 5776 * x / W < W ^ (-(1 : ℝ) / 3) := by
    apply (div_lt_iff₀ hW).2
    nlinarith [hpow]
  have hsqleft : (76 * Real.sqrt (x / W)) ^ 2 = 5776 * x / W := by
    rw [mul_pow, Real.sq_sqrt hq]
    ring
  have hsqright : (W ^ (-(1 : ℝ) / 6)) ^ 2 = W ^ (-(1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    congr 1
    ring
  nlinarith


theorem eventual_numeric_margin :
    ∀ᶠ N : ℕ in atTop,
      76 * Real.sqrt (Real.log N / (Dims.exampleGrow.W N : ℝ)) <
        (Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 6) := by
  have hlo : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ)‖ ≤ (1 / 6000 : ℝ) *
        ‖(N : ℝ) ^ ((5 : ℝ) / 12)‖ :=
    ((isLittleO_log_rpow_atTop
      (show (0 : ℝ) < 5 / 12 by norm_num)).def
      (show (0 : ℝ) < 1 / 6000 by norm_num)) |>
        tendsto_natCast_atTop_atTop.eventually
  have hlog : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [hlo, hlog, Dims.bandwidth_grow] with N hlo hlog hband
  have hN : (0 : ℝ) < N := by
    have : 1 ≤ N := by
      by_contra h
      have : N = 0 := by omega
      simp [this] at hlog
    exact_mod_cast this
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hpow : (0 : ℝ) < (N : ℝ) ^ ((5 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hN _
  have hlogle : Real.log N ≤ (1 / 6000 : ℝ) *
      (N : ℝ) ^ ((5 : ℝ) / 12) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog.le, abs_of_nonneg hpow.le] using hlo
  have hband' : (N : ℝ) ^ ((5 : ℝ) / 8) ≤
      (Dims.exampleGrow.W N : ℝ) := by
    simpa only [show (1 : ℝ) / 2 + 1 / 8 = 5 / 8 by norm_num,
      Dims.exampleGrow_W] using hband
  have hpowle : (N : ℝ) ^ ((5 : ℝ) / 12) ≤
      (Dims.exampleGrow.W N : ℝ) ^ ((2 : ℝ) / 3) := by
    calc
      (N : ℝ) ^ ((5 : ℝ) / 12) = ((N : ℝ) ^ ((5 : ℝ) / 8)) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_mul hN.le]
        congr 1
        ring
      _ ≤ (Dims.exampleGrow.W N : ℝ) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hband' (by norm_num)
  apply numeric_margin hW hlog.le
  nlinarith


theorem threshold_lower (N : ℕ) :
    (Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 6) ≤
      flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
  let B := band Dims.exampleGrow
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hsqrt : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  have hscale : 0 < B.scale 0 N (1 / 2) :=
    scale_half_pos N
  have hscalele : B.scale 0 N (1 / 2) ≤ (Dims.exampleGrow.W N : ℝ) := by
    rw [show B.scale 0 N (1 / 2) =
      (Dims.exampleGrow.W N : ℝ) * Real.sqrt (1 / 2) from scale_half N]
    nlinarith
  have hinv : (Dims.exampleGrow.W N : ℝ)⁻¹ ≤ (B.scale 0 N (1 / 2))⁻¹ :=
    inv_anti₀ hscale hscalele
  have hrpow := Real.rpow_le_rpow (inv_nonneg.mpr hW.le) hinv
    (show (0 : ℝ) ≤ 1 / 6 by norm_num)
  change (Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 6) ≤
    ((B.scale 0 N (1 / 2))⁻¹) ^ ((1 : ℝ) / 6)
  rw [show (-(1 : ℝ) / 6) = -((1 : ℝ) / 6) by ring,
    Real.rpow_neg hW.le, ← Real.inv_rpow hW.le]
  exact hrpow

theorem eventual_margin :
    ∀ᶠ N : ℕ in atTop,
      76 * Real.sqrt (Real.log N / (Dims.exampleGrow.W N : ℝ)) <
        flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
  filter_upwards [eventual_numeric_margin] with N h
  exact lt_of_lt_of_le h (threshold_lower N)

end RBM.Gauss.PermutationFourierExampleGrowFlowMargin

#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.scale_half
#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.half_time_endpoint
#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.scale_half_pos
#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.numeric_margin
#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.eventual_numeric_margin
#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.threshold_lower
#print axioms RBM.Gauss.PermutationFourierExampleGrowFlowMargin.eventual_margin
