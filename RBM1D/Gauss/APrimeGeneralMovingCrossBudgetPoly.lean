/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossPositive
import RBM1D.Gauss.APrimeGeneralMovingJointGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingJointMeasurable
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.Lemma514Q716
import RBM1D.Gauss.MomentDuhamelRhs

/-!
# T1107: a polynomial pointwise cap for the positive-time cross budget

The actual general-moving joint rate is bounded for every Gaussian sample by
the T617 envelope.  Its fixed-order integrability uses the canonical
measurability producer.  On the Gaussian probability space, this gives the
requested crude polynomial bound for the existing T1089 budget.  This module
does not bound the time integral of the budget or establish a small N1 slot.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetPoly

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- Uniformly in the output, every active target-mesh cell and its closed
running-time interval, the T1089 positive-time cross budget is bounded by a
single polynomial envelope.  The loss parameter and all hypotheses are the
same as in T1089; the estimate is only a pointwise cap. -/
theorem eventually_positive_time_cross_budget_le_polynomial
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Set.Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      0 < r →
        0 ≤ APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a r ∧
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a r ≤
          APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √r) * (N : ℝ) ^ (2 * D + 17) := by
  haveI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  have hProduct :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hEnvelope :=
    APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow hD
  have hIntegrable :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hProduct, hEnvelope, hIntegrable, eventually_ge_atTop 1] with
      N hProductN hEnvelopeN hIntegrableN hN
  have hNpos : 0 < N := by omega
  intro k hk a r hr hr0
  let m := APrimeSmoothWeightActual.canonicalM d s t
    (APrimeGeneralMovingMesh.targetMesh D) N
  let Y : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k m Step2.sigPM a
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r ω
  have hYint : Integrable (fun ω => |Y ω| ^ (2 * p)) (Gauss.P d) := by
    simpa [Y, m] using
      hIntegrableN k hk Step2.sigPM a r hr
  have hProd : ∀ ω : Gauss.Ω d,
      APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k m ω *
        √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r ω) ≤
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
    intro ω
    simpa [m] using hProductN k hk Step2.sigPM a r hr ω
  have hEnv0 : 0 ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N :=
    APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hY0 : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k m Step2.sigPM a
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r hNpos ω
  have hYbound : ∀ ω, |Y ω| ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
    intro ω
    change |APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k m Step2.sigPM a
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r ω| ≤ _
    rw [abs_of_nonneg (hY0 ω)]
    by_cases htrans : ω ∈ APrimeCrossJointSplit.transition d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k m
    · simpa only [Y, APrimeCrossJointSplit.jointRate,
        Set.indicator_of_mem htrans] using hProd ω
    · simpa only [Y, APrimeCrossJointSplit.jointRate,
        Set.indicator_of_notMem htrans] using hEnv0
  have hConstInt : Integrable
      (fun _ : Gauss.Ω d => APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p))
      (Gauss.P d) := integrable_const _
  have hPowerBound : ∀ ω : Gauss.Ω d,
      |Y ω| ^ (2 * p) ≤
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p) := by
    intro ω
    exact pow_le_pow_left₀ (abs_nonneg _) (hYbound ω) (2 * p)
  have hIntegral := integral_mono hYint hConstInt hPowerBound
  have hConstIntegral :
      (∫ _ω : Gauss.Ω d,
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p) ∂(Gauss.P d)) =
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p) := by
    simp [integral_const]
  have hMoment :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Y ≤
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
    unfold MomentDuhamel.momNorm
    have hInt0 : 0 ≤ ∫ ω, |Y ω| ^ (2 * p) ∂(Gauss.P d) :=
      integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
    calc
      (∫ ω, |Y ω| ^ (2 * p) ∂(Gauss.P d)) ^
          ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) ≤
          (APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p)) ^
            ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) :=
        Real.rpow_le_rpow hInt0 (hIntegral.trans_eq hConstIntegral) (by positivity)
      _ = APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
        rw [one_div]
        have hq : 2 * p ≠ 0 := by omega
        exact Real.pow_rpow_inv_natCast hEnv0 hq
  have hMomentPoly :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Y ≤ (N : ℝ) ^ (2 * D + 17) :=
    hMoment.trans hEnvelopeN
  have hCoeffNonneg :
      0 ≤ APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r) := by
    unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
    have hpR : 0 < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hp)
    exact div_nonneg (by positivity) (by positivity)
  constructor
  · exact APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget_nonneg
      E D deltaWeight s t N k p a hp hr0
  · change
      APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r) *
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Y ≤ _
    exact mul_le_mul_of_nonneg_left hMomentPoly hCoeffNonneg

/-- The accepted T995 nondegeneracy witness remains available with the
positive-time cross-budget module.  It supplies a genuine active positive
cell and a same-sample common-event member at `p = 1`; it does not assert
membership in the strict transition event. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingCrossHcrossPositive.t995_positive_cell_witness

#print axioms eventually_positive_time_cross_budget_le_polynomial
#print axioms t995_positive_cell_witness

end RBM.APrimeGeneralMovingCrossBudgetPoly
