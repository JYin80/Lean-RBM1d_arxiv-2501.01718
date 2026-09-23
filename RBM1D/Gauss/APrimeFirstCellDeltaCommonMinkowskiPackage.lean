/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCommonDerivativePackage
import RBM1D.Gauss.APrimeFirstCellDeltaMinkowskiActual

/-!
# T564: one-tauPrime common-event exact Minkowski package

T560's one-parameter derivative package is passed to T561's exact
derivative-to-Minkowski connector at `alpha = delta / 16` and
`q = highOrder delta p`.  The event and its positive geometry remain the
literal T560 fields; no resident samples are identified.
-/

namespace RBM.APrimeFirstCellDeltaCommonMinkowskiPackage

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- Exact Minkowski conclusions at T560's common parameter choice. -/
def exactMinkowskiBounds (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound
      tauPrime delta alpha q ∧
    APrimeFirstCellDeltaMinkowskiActual.zeroRPointwiseDerivativePremise
      tauPrime delta alpha q ∧
    APrimeFirstCellDeltaMinkowskiActual.kZeroMinkowskiActual
      tauPrime delta alpha q

/-- T560's three derivative predicates imply the corresponding T561
all-active, `r = 0`, and exact `k = 0` Minkowski conclusions. -/
theorem exactMinkowskiBounds_of_activeDerivativeBounds
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) (p : Nat) (hp : 1 <= p)
    (hderiv :
      APrimeFirstCellDeltaCommonDerivativePackage.activeDerivativeBounds
        tauPrime delta p) :
    exactMinkowskiBounds tauPrime delta p := by
  let alpha : Real := delta / 16
  let q : Nat := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  have hAlpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  have hq : 1 <= q := by
    exact (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  change
    APrimeFirstCellDeltaMomFlowDerivExact.actualMomFlowDerivBound
        tauPrime delta alpha q ∧
      APrimeFirstCellDeltaMomFlowDerivExact.zeroRMomFlowDerivBound
        tauPrime delta alpha q ∧
      APrimeFirstCellDeltaMomFlowDerivExact.kZeroMomFlowDerivBound
        tauPrime delta alpha q at hderiv
  obtain ⟨hpositive, hzero, hkzero⟩ := hderiv
  have hopen :=
    APrimeFirstCellDeltaMinkowskiActual.actualDerivativePremise_of_actualMomFlowDerivBound
      hpositive
  have hmink :=
    APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound_of_deriv
      hTau hDelta hAlpha hq hopen
  have hzeroOpen :
      APrimeFirstCellDeltaMinkowskiActual.zeroRPointwiseDerivativePremise
        tauPrime delta alpha q := by
    filter_upwards [hzero] with N hzeroN
    intro k hk a
    exact APrimeFirstCellDeltaMinkowskiActual.pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
        (hzeroN k hk a)
  have hkzeroActual :
      APrimeFirstCellDeltaMinkowskiActual.kZeroMinkowskiActual
        tauPrime delta alpha q := by
    filter_upwards [hkzero,
      APrimeFirstCellDeltaMinkowskiConsumer.eventually_kZeroMinkowskiBound
        tauPrime delta alpha q] with N hkzeroN hminkZeroN
    intro a
    exact ⟨hminkZeroN a |>.1,
      APrimeFirstCellDeltaMinkowskiActual.pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
          (hkzeroN a |>.2),
      hminkZeroN a |>.2⟩
  change
    APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound
        tauPrime delta alpha q ∧
      APrimeFirstCellDeltaMinkowskiActual.zeroRPointwiseDerivativePremise
        tauPrime delta alpha q ∧
      APrimeFirstCellDeltaMinkowskiActual.kZeroMinkowskiActual
        tauPrime delta alpha q
  exact ⟨hmink, hzeroOpen, hkzeroActual⟩

/-- Closed one-`tauPrime` package.  Event measurability, high probability,
and event-nonempty positive `k = 2` geometry are exactly T560's fields. -/
theorem exists_commonMinkowskiPackage :
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
        APrimeFirstCellDeltaCommonDerivativePackage.activeDerivativeBounds
          tauPrime delta p ∧
        exactMinkowskiBounds tauPrime delta p ∧
        APrimeFirstCellDeltaCommonBudgetPackage.eventNonemptyPositiveTwoGeometry
          tauPrime delta alpha := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCommonDerivativePackage.exists_commonDerivativePackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  dsimp only
  obtain ⟨hmeas, hprob, hq, hderiv, hgeometry⟩ :=
    hall delta hDelta hDelta100 p hp
  have hmink := exactMinkowskiBounds_of_activeDerivativeBounds
    hTau hDelta p hp hderiv
  exact ⟨hmeas, hprob, hq, hderiv, hmink, hgeometry⟩

#print axioms exactMinkowskiBounds
#print axioms exactMinkowskiBounds_of_activeDerivativeBounds
#print axioms exists_commonMinkowskiPackage

end

end RBM.APrimeFirstCellDeltaCommonMinkowskiPackage
