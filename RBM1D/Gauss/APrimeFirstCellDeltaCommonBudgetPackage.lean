/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFullCrossBudget
import RBM1D.Gauss.APrimeFirstCellDeltaQVNormBudget
import RBM1D.Gauss.APrimeFirstCellDeltaDriftIntegralBudget
import RBM1D.Gauss.APrimeFirstCellDeltaInitialMomentBudget

/-!
# T555: one-event variable-delta first-cell budget package

One `tauPrime` is chosen by T546 before `delta` and the target order.  At
the high order `max p ceil(20/delta)`, the full-cross, QV, drift, and initial
budgets are then assembled on T546's identical literal sharp common event.

Event nonemptiness and positive `k = 2` geometry are recorded without
identifying their witnesses with any resident predicate inherited from an
upstream module.  In particular, no support weight at `m = N` is identified
with the canonical weight.
-/

namespace RBM.APrimeFirstCellDeltaCommonBudgetPackage

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The four active-prefix budget groups, all at the same high order. -/
def activeBudgets (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let beta := delta
  let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  APrimeFirstCellDeltaFullCrossBudget.fullCrossIntegralBudgets
      tauPrime delta alpha q ∧
    APrimeFirstCellDeltaQVNormBudget.actualQVNormBudget
      tauPrime delta alpha q beta ∧
    APrimeFirstCellDeltaQVNormBudget.actualQVIntegralBudget
      tauPrime delta alpha q beta ∧
    APrimeFirstCellDeltaQVNormBudget.actualQVSqrtBudget
      tauPrime delta alpha q beta ∧
    APrimeFirstCellDeltaQVNormBudget.actualQVSqrtExplicitBudget
      tauPrime delta alpha q beta ∧
    APrimeFirstCellDeltaDriftIntegralBudget.actualDriftIntegralBudget
      tauPrime delta alpha beta q ∧
    (∀ᶠ N : Nat in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      ∀ a : LoopArg (d.L N) 2,
        APrimeFirstCellDeltaInitialMomentBudget.initialBoundAt
          tauPrime delta q N k a)

/-- Every exact empty-prefix branch needed by the four groups. -/
def exactZeroBudgets (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  (∀ N,
      (∫ r in (0 : Real)..cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 0,
        APrimeFirstCellDeltaFullCrossBudget.literalBfull
          tauPrime delta alpha q N
            (cutNetPt (fun _ => 0)
              APrimeSmoothTransition.transitionMesh N 0) r) = 0 ∧
      (∫ r in (0 : Real)..cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 0,
        APrimeFirstCellDeltaFullCrossBudget.BcrossActual
          tauPrime delta alpha q N
            (cutNetPt (fun _ => 0)
              APrimeSmoothTransition.transitionMesh N 0) r) = 0) ∧
    (∀ N, ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellDeltaQVNormBudget.endpoint N 0 = 0 ∧
      (∫ r in (0 : Real)..APrimeFirstCellDeltaQVNormBudget.endpoint N 0,
        APrimeFirstCellDeltaQVNormBudget.g
          tauPrime delta q N 0 a r) = 0 ∧
      Real.sqrt (((2 : Real) * q - 1) *
        (∫ r in (0 : Real)..APrimeFirstCellDeltaQVNormBudget.endpoint N 0,
          APrimeFirstCellDeltaQVNormBudget.g
            tauPrime delta q N 0 a r)) = 0) ∧
    APrimeFirstCellDeltaDriftIntegralBudget.kZeroDriftIntegralBudget
      tauPrime delta q ∧
    (∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellDeltaInitialMomentBudget.endpoint N 0 = 0 ∧
      (etaT 0 0 /
          etaT 0 (APrimeFirstCellDeltaInitialMomentBudget.endpoint N 0)) ^
          (-(2 : Real)) = 1 ∧
      (∀ omega : Ω d,
        APrimeFirstCellDeltaInitialMomentBudget.canonicalWeight
          tauPrime delta q N 0 omega = 1) ∧
      momNormW (P d)
        (APrimeFirstCellDeltaInitialMomentBudget.canonicalWeight
          tauPrime delta q N 0) q
        (APrimeFirstCellDeltaInitialMomentBudget.initial N 0 a) ≤
          (N : Real) ^ (5 * delta / 32))

/-- Event nonemptiness and deterministic positive `k = 2` geometry.
No assertion is made that one event sample realizes any other resident
predicate. -/
def eventNonemptyPositiveTwoGeometry
    (tauPrime delta alpha : Real) : Prop :=
  ∀ᶠ N : Nat in atTop,
    (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
      tauPrime delta alpha N).Nonempty ∧
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ APrimeFirstCellScaleFloors.ScalePackage tauPrime N 2

/-- A `HighProb` proof of the literal event and the scale floor give the
nonvacuous event/geometry package, with no common-sample strengthening. -/
theorem eventNonemptyPositiveTwoGeometry_of_highProb
    {tauPrime delta alpha : Real} (hTau : 0 < tauPrime)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha)) :
    eventNonemptyPositiveTwoGeometry tauPrime delta alpha := by
  filter_upwards [HighProb.nonempty (by simp) hprob,
    APrimeFirstCellScaleFloors.eventually_positive_two_scalePackage hTau]
      with N hne htwo
  exact ⟨hne, htwo⟩

/-- T546 chooses one `tauPrime`.  Its literal event and the very same
`HighProb` proof feed both T544 and T545; T546 supplies the drift budget,
while T547 is instantiated at the same arbitrary positive `tauPrime`.
All budgets use `P = max p ceil(20/delta)`. -/
theorem exists_commonBudgetPackage :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta → delta ≤ 1 / 100 →
      ∀ p : Nat, 1 ≤ p →
        let alpha := delta / 16
        let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        1 ≤ q ∧
        activeBudgets tauPrime delta p ∧
        exactZeroBudgets tauPrime delta p ∧
        eventNonemptyPositiveTwoGeometry tauPrime delta alpha := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaDriftIntegralBudget.exists_actualDriftIntegralBudget_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  dsimp only
  let alpha : Real := delta / 16
  let beta : Real := delta
  let P0 : Nat := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  have hAlpha : 0 < alpha := by dsimp [alpha]; positivity
  have hBeta : 0 < beta := by simpa [beta] using hDelta
  have hP : 1 ≤ P0 := by
    exact (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  obtain ⟨hmeas, hprob, hdrift, hdriftZero, _hdriftResident⟩ :=
    hall delta hDelta hDelta100 alpha hAlpha P0 hP beta hBeta
  have hcross :=
    APrimeFirstCellDeltaFullCrossBudget.fullCrossIntegralBudgets_of_highProb
      hTau hDelta hDelta100 hAlpha hprob P0 hP
  have hqvNorm :=
    APrimeFirstCellDeltaQVNormBudget.eventually_actualQVNormBudget_of_highProb
      hTau hDelta hAlpha hP hBeta hprob
  have hqvIntegral :=
    APrimeFirstCellDeltaQVNormBudget.eventually_actualQVIntegralBudget
      hTau hDelta hDelta100 hBeta hP hqvNorm
  have hqvSqrt :=
    APrimeFirstCellDeltaQVNormBudget.eventually_actualQVSqrtBudget
      hP hqvIntegral
  have hqvExplicit :=
    APrimeFirstCellDeltaQVNormBudget.eventually_actualQVSqrtExplicitBudget
      hTau hP hqvIntegral
  have hinitial :=
    APrimeFirstCellDeltaInitialMomentBudget.eventually_initialBoundAt
      hTau hDelta P0 hP
  have hinitialZero :=
    APrimeFirstCellDeltaInitialMomentBudget.eventually_initial_k_zero
      hTau hDelta P0 hP
  have hzero : exactZeroBudgets tauPrime delta p := by
    dsimp only [exactZeroBudgets, alpha, P0]
    refine ⟨?_, ?_, hdriftZero, hinitialZero⟩
    · intro N
      exact ⟨
        APrimeFirstCellDeltaFullCrossBudget.integral_literalBfull_k0
          tauPrime delta (delta / 16) P0 N,
        APrimeFirstCellDeltaFullCrossBudget.integral_BcrossActual_k0
          tauPrime delta (delta / 16) P0 N⟩
    · intro N a
      exact ⟨
        APrimeFirstCellDeltaQVNormBudget.endpoint_zero N,
        APrimeFirstCellDeltaQVNormBudget.integral_g_k_zero
          tauPrime delta P0 N a,
        APrimeFirstCellDeltaQVNormBudget.sqrt_integral_g_k_zero
          tauPrime delta P0 N a⟩
  refine ⟨hmeas, hprob, hP, ?_, hzero, ?_⟩
  · exact ⟨hcross, hqvNorm, hqvIntegral, hqvSqrt, hqvExplicit,
      hdrift, hinitial⟩
  · exact eventNonemptyPositiveTwoGeometry_of_highProb hTau hprob

#print axioms activeBudgets
#print axioms exactZeroBudgets
#print axioms eventNonemptyPositiveTwoGeometry
#print axioms eventNonemptyPositiveTwoGeometry_of_highProb
#print axioms exists_commonBudgetPackage

end

end RBM.APrimeFirstCellDeltaCommonBudgetPackage
