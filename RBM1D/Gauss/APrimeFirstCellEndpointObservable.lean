/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMoment
import RBM1D.Gauss.APrimeFirstCellEndpointCoord

/-!
# T515: the actual first-cell endpoint observable

This file identifies T509's literal coordinate observable at every active
moving endpoint with the coordinate family in T425.  It then rewrites the
finite output maximum and the normalized endpoint bootstrap quantity.  The
last theorem retains T509's same sharp-event resident and canonical weight,
but makes no family-moment or general-window assertion.
-/

namespace RBM.APrimeFirstCellEndpointObservable

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real := APrimeFirstCellQuantMoment.delta
noncomputable abbrev alpha : Real := APrimeFirstCellQuantMoment.alpha

/-- At the actual moving endpoint, T509's observable is definitionally the
norm of the corresponding literal normalized coordinate. -/
theorem Y_endpoint_eq_coordAt_norm (N k : Nat)
    (a : LoopArg (d.L N) 2) (omega : Gauss.Ω d) :
    Y N k a (endpoint N k) omega =
      ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
        (endpoint N k) (endpoint N k) (Hflow d N (endpoint N k) omega)‖ := by
  rfl

/-- The finite maximum of T509's endpoint observables is exactly T425's
literal endpoint-coordinate maximum. -/
theorem endpointCoordMax_eq_sup_Y (N k : Nat) (omega : Gauss.Ω d) :
    APrimeFirstCellEndpointCoord.endpointCoordMax d N (endpoint N k) omega =
      Finset.univ.sup' Finset.univ_nonempty
        (fun a : LoopArg (d.L N) 2 => Y N k a (endpoint N k) omega) := by
  rfl

/-- On every active first-cell endpoint, including `k = 0`, the normalized
bootstrap observable is `R_v^{-4}` plus the finite maximum of T509's literal
coordinate observables. -/
theorem jSnorm_endpoint_eq_sup_Y {tauPrime : Real} (hTau : 0 < tauPrime)
    (N k : Nat)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (omega : Gauss.Ω d) :
    let v := endpoint N k
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N v omega =
      1 / Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 +
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : LoopArg (d.L N) 2 => Y N k a v omega) := by
  have hid := APrimeFirstCellEndpointCoord.firstCell_endpoint_identity
    hTau N k hk omega
  exact hid.2.1.trans (congrArg
    (fun x : Real => 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 + x)
    (endpointCoordMax_eq_sup_Y N k omega))

/-- All three endpoint identifications at an arbitrary active index.  The
quantifier includes the boundary index `k = 0`. -/
theorem active_endpoint_observable (tauPrime : Real) (hTau : 0 < tauPrime)
    (N k : Nat)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (omega : Gauss.Ω d) :
    (forall a : LoopArg (d.L N) 2,
      Y N k a (endpoint N k) omega =
        ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
          (endpoint N k) (endpoint N k)
          (Hflow d N (endpoint N k) omega)‖) ∧
    APrimeFirstCellEndpointCoord.endpointCoordMax d N (endpoint N k) omega =
      Finset.univ.sup' Finset.univ_nonempty
        (fun a : LoopArg (d.L N) 2 => Y N k a (endpoint N k) omega) ∧
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N (endpoint N k) omega =
      1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 +
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : LoopArg (d.L N) 2 => Y N k a (endpoint N k) omega) := by
  exact ⟨fun a => Y_endpoint_eq_coordAt_norm N k a omega,
    endpointCoordMax_eq_sup_Y N k omega,
    jSnorm_endpoint_eq_sup_Y hTau N k hk omega⟩

/-- T509's same positive `k = 2` resident, with its sharp-event membership
and weight-one plateau, now carrying only the pointwise endpoint identities. -/
def positiveTwoEndpointObservableResident (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 <= firstCellT tauPrime N ∧
    weight tauPrime p N 2 omega = 1 ∧
    (forall a : LoopArg (d.L N) 2,
      Y N 2 a (endpoint N 2) omega =
        ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
          (endpoint N 2) (endpoint N 2)
          (Hflow d N (endpoint N 2) omega)‖) ∧
    APrimeFirstCellEndpointCoord.endpointCoordMax d N (endpoint N 2) omega =
      Finset.univ.sup' Finset.univ_nonempty
        (fun a : LoopArg (d.L N) 2 => Y N 2 a (endpoint N 2) omega) ∧
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N (endpoint N 2) omega =
      1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 2) ^ 4 +
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : LoopArg (d.L N) 2 => Y N 2 a (endpoint N 2) omega)

/-- Attach the endpoint identities to the very same resident supplied by
T509; no new event, sample, or probabilistic assumption is introduced. -/
theorem positiveTwoEndpointObservableResident_of_quantResident
    {tauPrime : Real} {p : Nat} (hTau : 0 < tauPrime)
    (hresident :
      APrimeFirstCellQuantMoment.positiveTwoQuantMomentResident tauPrime p) :
    positiveTwoEndpointObservableResident tauPrime p := by
  filter_upwards [hresident] with N hN
  obtain ⟨omega, homega, hk, hvpos, hvle, hweight, _hquant⟩ := hN
  obtain ⟨hcoord, hmax, hJ⟩ :=
    active_endpoint_observable tauPrime hTau N 2 hk omega
  exact ⟨omega, homega, hk, hvpos, hvle, hweight, hcoord, hmax, hJ⟩

/-- A closed choice of the same `tauPrime` and literal sharp event as T509,
retaining measurability, high probability, eventual nonemptiness, and its
positive weight-one resident, while stating only endpoint identities. -/
theorem exists_endpointObservable_with_resident :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall p : Nat, 1 <= p ->
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        (∀ᶠ N : Nat in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N).Nonempty) ∧
        positiveTwoEndpointObservableResident tauPrime p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellQuantMoment.exists_quantMoment_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro p hp
  obtain ⟨hmeas, hprob, hnonempty, _hactual, _hzero, hresident⟩ := hall p hp
  exact ⟨hmeas, hprob, hnonempty,
    positiveTwoEndpointObservableResident_of_quantResident hTau hresident⟩

#print axioms Y_endpoint_eq_coordAt_norm
#print axioms endpointCoordMax_eq_sup_Y
#print axioms jSnorm_endpoint_eq_sup_Y
#print axioms active_endpoint_observable
#print axioms positiveTwoEndpointObservableResident_of_quantResident
#print axioms exists_endpointObservable_with_resident

end

end RBM.APrimeFirstCellEndpointObservable
