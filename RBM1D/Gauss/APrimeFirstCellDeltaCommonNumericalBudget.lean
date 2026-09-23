/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCoordinateBudgetArithmetic
import RBM1D.Gauss.APrimeFirstCellDeltaCommonBudgetPackage

/-!
# T558: common-package numerical budget absorption

T554's exact four-term numerical budget is instantiated at every active
first-cell endpoint under the single parameter package supplied by T555.
-/

namespace RBM.APrimeFirstCellDeltaCommonNumericalBudget

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual first-cell mesh endpoint used in the numerical budget. -/
noncomputable def endpoint (N k : Nat) : Real :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

/-- T554's exact four-term numerical right-hand side at one actual endpoint,
bounded by the target coordinate scale. -/
def numericalBudgetAt (delta : Real) (p N k : Nat) : Prop :=
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  let v := endpoint N k
  let R := APrimeFirstCellLoopCap.xRate v
  APrimeFirstCellDeltaCoordinateBudgetArithmetic.totalBudget
      delta P0 N R v <=
    (N : Real) ^ (delta / 5) * R ^ (-(2 : Real))

/-- Fixed-size endpoint instantiation of T554's uniform geometric bound. -/
theorem numericalBudgetAt_of_scalePackage
    {tauPrime delta : Real} {p N k : Nat}
    (hpack : APrimeFirstCellScaleFloors.ScalePackage tauPrime N k)
    (huniform : forall R v : Real,
      1 <= R -> R <= 2 -> 0 <= v -> v <= 1 / 2 ->
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.totalBudget delta
          (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N R v <=
        (N : Real) ^ (delta / 5) * R ^ (-(2 : Real))) :
    numericalBudgetAt delta p N k := by
  dsimp only [numericalBudgetAt, endpoint]
  exact huniform _ _ hpack.one_le_ratio hpack.ratio_le_two
    hpack.time_nonneg hpack.time_le_half

/-- The exact numerical budget is eventually absorbed at every active
first-cell endpoint. -/
def actualNumericalBudgets
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k,
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    numericalBudgetAt delta p N k

theorem eventually_actualNumericalBudgets
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p) :
    actualNumericalBudgets tauPrime delta p := by
  have hP : 1 <= APrimeFirstCellDeltaTargetWeight.highOrder delta p :=
    (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  filter_upwards [
    APrimeFirstCellDeltaCoordinateBudgetArithmetic.eventually_totalBudget_le
      hDelta (APrimeFirstCellDeltaTargetWeight.highOrder delta p) hP,
    APrimeFirstCellScaleFloors.eventually_scalePackage hTau]
      with N hbudget hscale
  intro k hk
  exact numericalBudgetAt_of_scalePackage (hscale k hk) hbudget

/-- Exact empty-prefix endpoint together with the same numerical bound. -/
def kZeroNumericalBudget (delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ numericalBudgetAt delta p N 0

theorem eventually_kZeroNumericalBudget
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p) :
    kZeroNumericalBudget delta p := by
  filter_upwards [eventually_actualNumericalBudgets hTau hDelta hp]
      with N hbudget
  exact ⟨by simp [endpoint, cutNetPt_zero],
    hbudget 0 (Nat.zero_le _)⟩

/-- T555's complete common package, extended only by T554's numerical
absorption at all active endpoints and at the exact empty prefix. -/
theorem exists_commonBudgetPackage_with_numerical :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall delta : Real, 0 < delta -> delta <= 1 / 100 ->
      forall p : Nat, 1 <= p ->
        let alpha := delta / 16
        let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        1 <= P0 ∧
        APrimeFirstCellDeltaCommonBudgetPackage.activeBudgets
          tauPrime delta p ∧
        APrimeFirstCellDeltaCommonBudgetPackage.exactZeroBudgets
          tauPrime delta p ∧
        APrimeFirstCellDeltaCommonBudgetPackage.eventNonemptyPositiveTwoGeometry
          tauPrime delta alpha ∧
        actualNumericalBudgets tauPrime delta p ∧
        kZeroNumericalBudget delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCommonBudgetPackage.exists_commonBudgetPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  dsimp only
  obtain ⟨hmeas, hprob, hP, hactive, hzero, hpositive⟩ :=
    hall delta hDelta hDelta100 p hp
  exact ⟨hmeas, hprob, hP, hactive, hzero, hpositive,
    eventually_actualNumericalBudgets hTau hDelta hp,
    eventually_kZeroNumericalBudget hTau hDelta hp⟩

end

end RBM.APrimeFirstCellDeltaCommonNumericalBudget

namespace RBM.APrimeFirstCellDeltaCommonNumericalBudget

#print axioms numericalBudgetAt_of_scalePackage
#print axioms eventually_actualNumericalBudgets
#print axioms eventually_kZeroNumericalBudget
#print axioms exists_commonBudgetPackage_with_numerical

end RBM.APrimeFirstCellDeltaCommonNumericalBudget
