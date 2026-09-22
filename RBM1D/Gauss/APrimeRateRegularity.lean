/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeTimeIntegrability
import RBM1D.Gauss.APrimeTimeInt
import RBM1D.Gauss.FlowContInt

/-!
# T291: rate regularity audit for the actual Gaussian A′ coordinate route

The cross-budget shape has an integrable first-cell instance.  The stochastic
drift and evolved QV rates still need concrete time-family producers before
the weighted Minkowski closure can be instantiated.
-/

#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.APrimeDuhamelModel.qvRateEvolvedOn
#check @RBM.APrimeDuhamelModel.rateNormW_qvRateEvolvedOn_le
#check @RBM.Gauss.continuousOn_driftELK_time
#check @RBM.Gauss.continuousOn_driftEG_time
#check @RBM.APrimeTimeInt.nearInt_continuousOn
#check @RBM.APrimeTimeInt.intervalIntegrable_sqrt_inv
#check @RBM.APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
#check @RBM.MomentDuhamel.weightedMinkowski_of_deriv_le

namespace RBM.APrimeRateRegularity

open MeasureTheory Set

/-- The deterministic near-field cross budget has genuine time integrability
on the first cell, including its integrable square-root singularity at zero.
This is a candidate upper budget, not an identification with the as-yet
unnamed stochastic cross rate of the A′ coordinate family. -/
theorem intervalIntegrable_crossInt_qHatNear {E t κ : ℝ}
    (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IntervalIntegrable
      (fun u => APrimeModel.crossInt κ (APrimeTimeInt.qHatNear E 0 t) u)
      volume 0 t := by
  have hq : ContinuousOn (fun u => APrimeTimeInt.qHatNear E 0 t u)
      (Icc (0 : ℝ) t) := by
    simpa only [APrimeTimeInt.qHatNear, Set.uIcc_of_le ht0] using
      (APrimeTimeInt.nearInt_continuousOn hE ht0 ht1).div_const
        ((etaT E 0 / etaT E t) ^ 8)
  have hsqrt : ContinuousOn
      (fun u => Real.sqrt (κ * APrimeTimeInt.qHatNear E 0 t u))
      (Icc (0 : ℝ) t) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hq)
  have hbase : IntervalIntegrable (fun u : ℝ => Real.sqrt u⁻¹) volume 0 t :=
    APrimeTimeInt.intervalIntegrable_sqrt_inv ht0
  simpa only [APrimeModel.crossInt] using hbase.mul_continuousOn (by
    simpa only [Set.uIcc_of_le ht0] using hsqrt)

/-- A first-cell instance with a positive time length and a positive cross
rate at an interior time. -/
theorem crossInt_qHatNear_first_cell_witness :
    IntervalIntegrable
      (fun u => APrimeModel.crossInt 1 (APrimeTimeInt.qHatNear 0 0 (1 / 2)) u)
      volume 0 (1 / 2) ∧
    0 < APrimeModel.crossInt 1 (APrimeTimeInt.qHatNear 0 0 (1 / 2)) (1 / 4) := by
  have hη0 : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hηu : 0 < etaT 0 (1 / 4) := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hηt : 0 < etaT 0 (1 / 2) := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hq : 0 < APrimeTimeInt.qHatNear 0 0 (1 / 2) (1 / 4) := by
    simp only [APrimeTimeInt.qHatNear, Step2MomentStep.nearInt]
    positivity
  constructor
  · exact intervalIntegrable_crossInt_qHatNear (by norm_num) (by norm_num) (by norm_num)
  · simp only [APrimeModel.crossInt]
    positivity

#print axioms RBM.APrimeRateRegularity.intervalIntegrable_crossInt_qHatNear
#print axioms RBM.APrimeRateRegularity.crossInt_qHatNear_first_cell_witness

end RBM.APrimeRateRegularity
