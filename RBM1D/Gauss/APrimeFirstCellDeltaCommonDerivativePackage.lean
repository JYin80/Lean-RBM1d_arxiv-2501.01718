/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCommonBudgetPackage
import RBM1D.Gauss.APrimeFirstCellDeltaMomFlowDerivExact

/-!
# T560: common-`tauPrime` derivative package

T555's single `tauPrime` and literal sharp common event are retained while
T549's arbitrary-`tauPrime` derivative producers are instantiated at
`alpha = delta / 16` and the high order `P = highOrder delta p`.

Only the deterministic eventual derivative statements are combined with
event nonemptiness and positive `k = 2` geometry.  No assertion identifies
T549's separately constructed resident sample with a sample supplied here.
-/

namespace RBM.APrimeFirstCellDeltaCommonDerivativePackage

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T549's three derivative producers, all at `alpha = delta / 16` and the
same high order selected by T555. -/
def activeDerivativeBounds (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  APrimeFirstCellDeltaMomFlowDerivExact.actualMomFlowDerivBound
      tauPrime delta alpha q ∧
    APrimeFirstCellDeltaMomFlowDerivExact.zeroRMomFlowDerivBound
      tauPrime delta alpha q ∧
    APrimeFirstCellDeltaMomFlowDerivExact.kZeroMomFlowDerivBound
      tauPrime delta alpha q

/-- At any already chosen positive `tauPrime`, T549 supplies the positive-r,
left-endpoint, and exact empty-cell derivative statements at the T555
parameter choice. -/
theorem activeDerivativeBounds_of_tauPrime
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) (hDelta100 : delta <= 1 / 100)
    (p : Nat) (hp : 1 <= p) :
    activeDerivativeBounds tauPrime delta p := by
  let alpha : Real := delta / 16
  let q : Nat := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  have hAlpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  have hq : 1 <= q := by
    exact (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  have hpositive :=
    APrimeFirstCellDeltaMomFlowDerivExact.eventually_momFlowDerivBoundAt
      hTau hDelta hDelta100 hAlpha q hq
  have hzero :=
    APrimeFirstCellDeltaMomFlowDerivExact.eventually_zeroRMomFlowDerivBound
      (delta := delta) (alpha := alpha) hTau q hq
  have hkzero :=
    APrimeFirstCellDeltaMomFlowDerivExact.eventually_kZeroMomFlowDerivBound
      (delta := delta) (alpha := alpha) hTau q hq
  exact ⟨hpositive, hzero, hkzero⟩

/-- Closed common-parameter package.  The measurable high-probability event
and its nonempty positive-`k = 2` geometry are exactly T555's outputs, while
the derivative bounds are T549's arbitrary-`tauPrime` producers instantiated
at that same parameter. -/
theorem exists_commonDerivativePackage :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ p : Nat, 1 <= p ->
        let alpha := delta / 16
        let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        1 <= q ∧
        activeDerivativeBounds tauPrime delta p ∧
        APrimeFirstCellDeltaCommonBudgetPackage.eventNonemptyPositiveTwoGeometry
          tauPrime delta alpha := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCommonBudgetPackage.exists_commonBudgetPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  dsimp only
  obtain ⟨hmeas, hprob, hq, _hbudgets, _hzeroBudgets, hgeometry⟩ :=
    hall delta hDelta hDelta100 p hp
  have hderivative := activeDerivativeBounds_of_tauPrime
    hTau hDelta hDelta100 p hp
  exact ⟨hmeas, hprob, hq, hderivative, hgeometry⟩

#print axioms activeDerivativeBounds
#print axioms activeDerivativeBounds_of_tauPrime
#print axioms exists_commonDerivativePackage

end

end RBM.APrimeFirstCellDeltaCommonDerivativePackage
