/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral

/-!
# T1133: integral bound for the actual positive-time cross budget

Combines the actual-budget integrability theorem with its pointwise cap and
the exact integral of the deterministic inverse-square-root envelope.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetIntegralBound

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.APrimeGeneralMovingCrossHcrossPositive

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual T1089 positive-time `Bc` has the exact integral cap furnished
by integrating the T1107 polynomial envelope, on every active closed target
cell.  All parameters, the actual smooth weight, and the `Step2.sigPM` charge
are those of the accepted producers. -/
theorem eventually_integral_positive_time_cross_budget_le
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
        (∫ r in (s N)..
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          positiveTimeCrossBudget E D deltaWeight s t N k p a r) ≤
          2 * APrimeGeneralMovingCrossEnvelopeIntegral.envelopeConstant p N D *
            (√(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) - √(s N)) := by
  have hInt :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hEnv :=
    APrimeGeneralMovingCrossEnvelopeIntegral.eventually_active_target_cross_envelope_integral
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hInt, hEnv, eventually_ge_atTop 1] with N hIntN hEnvN hN
  have hNpos : 0 < N := by omega
  intro k hk a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hBcInt := hIntN k hk a
  have hEnvData := hEnvN k hk a
  have hEnvInt := hEnvData.1
  have hPoint : ∀ r ∈ Icc (s N) v,
      positiveTimeCrossBudget E D deltaWeight s t N k p a r ≤
        APrimeGeneralMovingCrossEnvelopeIntegral.crossEnvelope p N D r := by
    intro r hr
    have hr0 : 0 ≤ r := (hs0 N).trans hr.1
    by_cases hrpos : 0 < r
    · exact hEnvData.2.2 r hr hrpos
    · have hrEq : r = 0 := by linarith
      subst r
      simp [positiveTimeCrossBudget,
        APrimeGeneralMovingCrossEnvelopeIntegral.crossEnvelope,
        APrimeGeneralMovingCrossEnvelopeIntegral.envelopeConstant]
  have hmono := intervalIntegral.integral_mono_on hv.1 hBcInt hEnvInt hPoint
  calc
    (∫ r in (s N)..v, positiveTimeCrossBudget E D deltaWeight s t N k p a r)
        ≤ ∫ r in (s N)..v,
          APrimeGeneralMovingCrossEnvelopeIntegral.crossEnvelope p N D r := hmono
    _ = 2 * APrimeGeneralMovingCrossEnvelopeIntegral.envelopeConstant p N D *
          (√v - √(s N)) := hEnvData.2.1

/-- The accepted T995 nondegenerate positive-cell witness is retained at the
same actual weight and fixed charge used by the bound. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingCrossBudgetTimeIntegrable.t995_positive_cell_witness

#print axioms eventually_integral_positive_time_cross_budget_le
#print axioms t995_positive_cell_witness

end RBM.APrimeGeneralMovingCrossBudgetIntegralBound
