/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaMomFlowDerivExact
import RBM1D.Gauss.APrimeFirstCellDeltaMinkowskiConsumer

/-!
# T561: actual explicit-delta derivative-to-Minkowski connector

T549's actual pointwise derivative bound is definitionally identified with
T556's open premise.  The resulting statements stop at the exact integrated
Minkowski bound.
-/

namespace RBM.APrimeFirstCellDeltaMinkowskiActual

open Filter Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T549's literal pointwise conclusion is exactly T556's open premise. -/
theorem pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
    {tauPrime delta alpha : Real} {p N k : Nat}
    {a : LoopArg (d.L N) 2} {r : Real}
    (h : APrimeFirstCellDeltaMomFlowDerivExact.momFlowDerivBoundAt
      tauPrime delta alpha p N k a r) :
    APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt
      tauPrime delta alpha p N k a r := by
  simpa [APrimeFirstCellDeltaMomFlowDerivExact.momFlowDerivBoundAt,
    APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt,
    APrimeFirstCellDeltaMomFlowDerivExact.canonicalM,
    APrimeFirstCellDeltaMinkowskiConsumer.canonicalM,
    APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
    APrimeFirstCellDeltaMinkowskiConsumer.weight,
    APrimeFirstCellDeltaMinkowskiConsumer.Y,
    APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint,
    APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellGeneratorHle.canonicalWeight,
    APrimeFirstCellGeneratorHle.actualWeight,
    APrimeFirstCellSampleRegularity.Y,
    APrimeFirstCellSampleRegularity.G,
    APrimeFirstCellSampleRegularity.Q, d] using h

/-- Fixed-size exact Minkowski assembly from T549's pointwise conclusion. -/
theorem minkowskiBoundAt_of_momFlowDerivBoundAt
    {tauPrime delta alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hderiv : ∀ r ∈ Ioc (0 : Real)
      (APrimeFirstCellDeltaMinkowskiConsumer.endpoint N k),
      APrimeFirstCellDeltaMomFlowDerivExact.momFlowDerivBoundAt
        tauPrime delta alpha p N k a r) :
    APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt
      tauPrime delta alpha p N k a := by
  exact APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt_of_deriv
    hTau hDelta hAlpha hp hN hk a
    (fun r hr =>
      pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
        (hderiv r hr))

/-- Eventual T549 pointwise bounds discharge T556's full open premise. -/
theorem actualDerivativePremise_of_actualMomFlowDerivBound
    {tauPrime delta alpha : Real} {p : Nat}
    (hderiv :
      APrimeFirstCellDeltaMomFlowDerivExact.actualMomFlowDerivBound
        tauPrime delta alpha p) :
    APrimeFirstCellDeltaMinkowskiConsumer.actualDerivativePremise
      tauPrime delta alpha p := by
  filter_upwards [hderiv] with N hderivN
  intro k hk1 hk a r hr
  apply pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
  exact hderivN k hk1 hk a r (by
    simpa [APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hr)

/-- Closed all-active exact Minkowski bound for fixed explicit parameters. -/
theorem eventually_actualMinkowskiBound
    {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (hDelta100 : delta <= 1 / 100) (hAlpha : 0 < alpha)
    (p : Nat) (hp : 1 <= p) :
    APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound tauPrime delta alpha p := by
  apply APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound_of_deriv hTau hDelta hAlpha hp
  exact actualDerivativePremise_of_actualMomFlowDerivBound
    (APrimeFirstCellDeltaMomFlowDerivExact.eventually_momFlowDerivBoundAt
      hTau hDelta hDelta100 hAlpha p hp)

/-- T549's totalized `r = 0` statement in T556's identical vocabulary. -/
def zeroRPointwiseDerivativePremise
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k,
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt
        tauPrime delta alpha p N k a 0

theorem eventually_zeroRPointwiseDerivativePremise
    {tauPrime delta alpha : Real} (hTau : 0 < tauPrime)
    (p : Nat) (hp : 1 <= p) :
    zeroRPointwiseDerivativePremise tauPrime delta alpha p := by
  filter_upwards [APrimeFirstCellDeltaMomFlowDerivExact.eventually_zeroRMomFlowDerivBound
    (delta := delta) (alpha := alpha) hTau p hp] with N hzeroN
  intro k hk a
  exact pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
    (hzeroN k hk a)

/-- Exact empty-cell package: zero endpoint, the totalized derivative bound,
and the exact zero-interval Minkowski conclusion. -/
def kZeroMinkowskiActual
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    APrimeFirstCellDeltaMinkowskiConsumer.endpoint N 0 = 0 ∧
      APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt
        tauPrime delta alpha p N 0 a 0 ∧
      APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt tauPrime delta alpha p N 0 a

theorem eventually_kZeroMinkowskiActual
    {tauPrime delta alpha : Real} (hTau : 0 < tauPrime)
    (p : Nat) (hp : 1 <= p) :
    kZeroMinkowskiActual tauPrime delta alpha p := by
  filter_upwards [APrimeFirstCellDeltaMomFlowDerivExact.eventually_kZeroMomFlowDerivBound
      (delta := delta) (alpha := alpha) hTau p hp,
    APrimeFirstCellDeltaMinkowskiConsumer.eventually_kZeroMinkowskiBound tauPrime delta alpha p]
      with N hderivN hminkN
  intro a
  exact ⟨hminkN a |>.1,
    pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt (hderivN a |>.2),
    hminkN a |>.2⟩

/-- A same-event positive `k = 2` resident carrying both the actual
pointwise derivative conclusion and the exact integrated Minkowski bound. -/
def positiveTwoMinkowskiResident
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    let v := APrimeFirstCellDeltaMinkowskiConsumer.endpoint N 2
    0 < v ∧ v <= firstCellT tauPrime N ∧
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : Real) v,
      APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt
        tauPrime delta alpha p N 2 a r) ∧
    ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt tauPrime delta alpha p N 2 a

theorem positiveTwoMinkowskiResident_of_inputs
    {tauPrime delta alpha : Real} {p : Nat}
    (hresident : APrimeFirstCellDeltaMomFlowDerivExact.positiveTwoMomFlowDerivResident
      tauPrime delta alpha p)
    (hmink : APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound tauPrime delta alpha p) :
    positiveTwoMinkowskiResident tauPrime delta alpha p := by
  filter_upwards [hresident, hmink] with N hresidentN hminkN
  obtain ⟨omega, homega, hvpos, hvle, hk,
    _hcross0, _hcross, hderiv⟩ := hresidentN
  refine ⟨omega, homega, ?_, ?_, hk, ?_, ?_⟩
  · simpa [APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hvpos
  · simpa [APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hvle
  · intro a r hr
    apply pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
    exact hderiv a r (by
      simpa [APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
        APrimeFirstCellSampleRegularity.endpoint,
        APrimeFirstCellGeneratorHle.endpoint] using hr)
  · intro a
    exact hminkN 2 (by norm_num) hk a

/-- Closed actual derivative-to-Minkowski package.  It retains the original
sharp-event witness but makes no numerical coordinate estimate. -/
theorem exists_actualMinkowski_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ alpha : Real, 0 < alpha -> ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound tauPrime delta alpha p ∧
        zeroRPointwiseDerivativePremise tauPrime delta alpha p ∧
        kZeroMinkowskiActual tauPrime delta alpha p ∧
        positiveTwoMinkowskiResident tauPrime delta alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaMomFlowDerivExact.exists_momFlowDeriv_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 alpha hAlpha p hp
  obtain ⟨hmeas, hprob, hderiv, hzero, hkzero, hresident⟩ :=
    hall delta hDelta hDelta100 alpha hAlpha p hp
  have hopen :=
    actualDerivativePremise_of_actualMomFlowDerivBound hderiv
  have hmink :=
    APrimeFirstCellDeltaMinkowskiConsumer.actualMinkowskiBound_of_deriv hTau hDelta hAlpha hp hopen
  have hzeroOpen : zeroRPointwiseDerivativePremise
      tauPrime delta alpha p := by
    filter_upwards [hzero] with N hzeroN
    intro k hk a
    exact pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
      (hzeroN k hk a)
  have hkzeroActual : kZeroMinkowskiActual
      tauPrime delta alpha p := by
    filter_upwards [hkzero,
      APrimeFirstCellDeltaMinkowskiConsumer.eventually_kZeroMinkowskiBound tauPrime delta alpha p]
        with N hkzeroN hminkZeroN
    intro a
    exact ⟨hminkZeroN a |>.1,
      pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt (hkzeroN a |>.2),
      hminkZeroN a |>.2⟩
  exact ⟨hmeas, hprob, hmink, hzeroOpen, hkzeroActual,
    positiveTwoMinkowskiResident_of_inputs hresident hmink⟩

end

end RBM.APrimeFirstCellDeltaMinkowskiActual

namespace RBM.APrimeFirstCellDeltaMinkowskiActual

#print axioms pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
#print axioms minkowskiBoundAt_of_momFlowDerivBoundAt
#print axioms actualDerivativePremise_of_actualMomFlowDerivBound
#print axioms eventually_actualMinkowskiBound
#print axioms eventually_zeroRPointwiseDerivativePremise
#print axioms eventually_kZeroMinkowskiActual
#print axioms positiveTwoMinkowskiResident_of_inputs
#print axioms exists_actualMinkowski_with_resident

end RBM.APrimeFirstCellDeltaMinkowskiActual
