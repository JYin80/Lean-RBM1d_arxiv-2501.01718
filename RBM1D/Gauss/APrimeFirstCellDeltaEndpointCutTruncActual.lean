/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCoordinateMoment
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointFromCoords
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointCutTrunc

/-!
# T567: closed actual first-cell endpoint cutoff package

T562's closed canonical coordinate estimate is put into T565's literal open
coordinate interface.  T565 supplies the target-weight endpoint norm and T563
then gives the cutoff integral at `N^(2 * delta)`.  The same construction keeps
the exact empty prefix and T562's nonempty positive `k = 2` event resident.

Only the actual first grid cell is closed here.  No moving-window or A-prime
closure is asserted.
-/

namespace RBM.APrimeFirstCellDeltaEndpointCutTruncActual

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T562's coordinate bound is definitionally the open coordinate premise
consumed by T565. -/
theorem coordinateMomentAt_of_coordinateBounds
    {tauPrime delta : Real} {p N k : Nat}
    (hcoords : forall a : LoopArg (d.L N) 2,
      APrimeFirstCellDeltaCoordinateMoment.coordinateBoundAt
        tauPrime delta p N k a) :
    APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt
      tauPrime delta p N k := by
  intro a
  have h := hcoords a
  simpa [APrimeFirstCellDeltaCoordinateMoment.coordinateBoundAt,
    APrimeFirstCellDeltaCoordinateMoment.endpoint,
    APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
    APrimeFirstCellDeltaMinkowskiConsumer.Y,
    APrimeFirstCellMinkowskiExact.endpoint,
    APrimeFirstCellMinkowskiExact.Y] using h

/-- The closed T562 active-coordinate producer discharges T565's eventual
open active-coordinate premise. -/
theorem actualCoordinatePremise_of_actualCoordinates
    {tauPrime delta : Real} {p : Nat}
    (hcoords :
      APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
        tauPrime delta p) :
    APrimeFirstCellDeltaEndpointFromCoords.actualCoordinatePremise
      tauPrime delta p := by
  filter_upwards [hcoords] with N hcoordsN
  intro k hk1 hk
  exact coordinateMomentAt_of_coordinateBounds (hcoordsN k hk1 hk)

/-- The closed T562 empty-prefix producer discharges T565's open empty-prefix
coordinate premise. -/
theorem kZeroCoordinatePremise_of_kZeroCoordinates
    {tauPrime delta : Real} {p : Nat}
    (hcoords :
      APrimeFirstCellDeltaCoordinateMoment.kZeroCoordinateMoments
        tauPrime delta p) :
    APrimeFirstCellDeltaEndpointFromCoords.kZeroCoordinatePremise
      tauPrime delta p := by
  filter_upwards [hcoords] with N hcoordsN
  exact coordinateMomentAt_of_coordinateBounds hcoordsN.2

/-- T562 followed by T565 and T563 proves the requested cutoff bound uniformly
over all positive active first-cell prefixes. -/
theorem actualEndpointCutoffBound_of_actualCoordinates
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords :
      APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
        tauPrime delta p) :
    APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
      tauPrime delta p := by
  have hend :=
    APrimeFirstCellDeltaEndpointFromCoords.actualEndpointMoments_of_coords
      hTau hDelta hp
        (actualCoordinatePremise_of_actualCoordinates hcoords)
  have hnorm :
      APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointNormPremise
        tauPrime delta p := by
    filter_upwards [hend] with N hendN
    intro k hk1 hk
    have h := hendN k hk1 hk
    change APrimeFirstCellDeltaEndpointCutTrunc.endpointNormPremiseAt
      tauPrime delta p N k at h
    exact h
  exact APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound_of_norm
    hTau hp hnorm

/-- Exact empty-prefix geometry and both weight-one identities, together with
the requested cutoff conclusion. -/
def kZeroEndpointCutoffActual
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    APrimeFirstCellDeltaCoordinateMoment.endpoint N 0 = 0 ∧
    Step2Moment.ratR 0 (fun _ => 0) N
      (APrimeFirstCellDeltaCoordinateMoment.endpoint N 0) = 1 ∧
    APrimeFirstCellDeltaEndpointMinkowski.endpointBaseline N 0 = 1 ∧
    (forall omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 0 omega = 1) ∧
    (forall omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 0 omega = 1) ∧
    APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt
      tauPrime delta p N 0

/-- T562's exact empty-prefix coordinate estimate closes the positive-order
empty-prefix cutoff package. -/
theorem kZeroEndpointCutoffActual_of_kZeroCoordinates
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords :
      APrimeFirstCellDeltaCoordinateMoment.kZeroCoordinateMoments
        tauPrime delta p) :
    kZeroEndpointCutoffActual tauPrime delta p := by
  have hend :=
    APrimeFirstCellDeltaEndpointFromCoords.kZeroEndpointMoments_of_coords
      hTau hDelta hp
        (kZeroCoordinatePremise_of_kZeroCoordinates hcoords)
  have hnorm :
      APrimeFirstCellDeltaEndpointCutTrunc.kZeroEndpointNormPremise
        tauPrime delta p := by
    filter_upwards [hend] with N hendN
    exact hendN.2.2.2.2.2
  have hcut :=
    APrimeFirstCellDeltaEndpointCutTrunc.kZeroEndpointCutoffBound_of_norm
      hTau hp hnorm
  filter_upwards [hend, hcut] with N hendN hcutN
  exact ⟨hendN.1, hendN.2.1, hendN.2.2.1, hendN.2.2.2.1,
    hendN.2.2.2.2.1, hcutN.2⟩

/-- A nonempty sample of T562's literal sharp common event at the positive
prefix `k = 2`, retaining only geometry, the two weight-one identities, and
the uniform endpoint cutoff conclusion. -/
def positiveTwoEndpointCutoffPackage
    (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      let v := APrimeFirstCellDeltaCoordinateMoment.endpoint N 2
      0 < v ∧
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      v <= 1 / 2 ∧
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 2 omega = 1 ∧
      APrimeFirstCellDeltaTargetWeight.canonicalWeight
        tauPrime delta P0 N 2 omega = 1 ∧
      APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt
        tauPrime delta p N 2

/-- Attach the deterministic uniform cutoff bound to T562's same-event
positive `k = 2` resident. -/
theorem positiveTwoEndpointCutoffPackage_of_inputs
    {tauPrime delta : Real} {p : Nat}
    (hpositive :
      APrimeFirstCellDeltaCoordinateMoment.positiveTwoCoordinateMomentPackage
        tauPrime delta p)
    (hcut : APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
      tauPrime delta p) :
    positiveTwoEndpointCutoffPackage tauPrime delta p := by
  filter_upwards [hpositive, hcut] with N hpositiveN hcutN
  obtain ⟨omega, homega, hvpos, hk, hvhalf, htarget, hcanonical,
    _hcoords⟩ := hpositiveN
  exact ⟨omega, homega, hvpos, hk, hvhalf, htarget, hcanonical,
    hcutN 2 (by norm_num) hk⟩

/-- Closed one-`tauPrime` actual first-cell endpoint cutoff package for every
`0 < delta <= 1/100` and fixed positive target order. -/
theorem exists_endpointCutoffActualPackage :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall delta : Real, 0 < delta -> delta <= 1 / 100 ->
      forall p : Nat, 1 <= p ->
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (Gauss.P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
          tauPrime delta p ∧
        kZeroEndpointCutoffActual tauPrime delta p ∧
        positiveTwoEndpointCutoffPackage tauPrime delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCoordinateMoment.exists_coordinateMomentPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  obtain ⟨hmeas, hprob, hcoords, hkzero, hpositive⟩ :=
    hall delta hDelta hDelta100 p hp
  have hcut := actualEndpointCutoffBound_of_actualCoordinates
    hTau hDelta hp hcoords
  exact ⟨hmeas, hprob, hcut,
    kZeroEndpointCutoffActual_of_kZeroCoordinates
      hTau hDelta hp hkzero,
    positiveTwoEndpointCutoffPackage_of_inputs hpositive hcut⟩

/-- The order-zero active-prefix cutoff bound is unconditional and uses no
coordinate or endpoint norm premise. -/
theorem actualEndpointCutoffBound_zero (tauPrime delta : Real) :
    APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
      tauPrime delta 0 :=
  APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound_zero
    tauPrime delta

/-- The order-zero empty-prefix cutoff package is unconditional. -/
theorem kZeroEndpointCutoffActual_zero (tauPrime delta : Real) :
    kZeroEndpointCutoffActual tauPrime delta 0 := by
  have hcut :=
    APrimeFirstCellDeltaEndpointCutTrunc.kZeroEndpointCutoffBound_zero
      tauPrime delta
  filter_upwards [hcut] with N hcutN
  have hz := APrimeFirstCellDeltaEndpointMinkowski.kZero_exact
    tauPrime delta 0 N
  refine ⟨?_, ?_, hz.2.2.1, hz.2.2.2, ?_, hcutN.2⟩
  · simpa [APrimeFirstCellDeltaCoordinateMoment.endpoint,
      APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellMinkowskiExact.endpoint] using hz.1
  · simpa [APrimeFirstCellDeltaCoordinateMoment.endpoint,
      APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellMinkowskiExact.endpoint] using hz.2.1
  · exact APrimeFirstCellDeltaTargetWeight.canonicalWeight_k_zero
      tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta 0) N

#print axioms coordinateMomentAt_of_coordinateBounds
#print axioms actualCoordinatePremise_of_actualCoordinates
#print axioms kZeroCoordinatePremise_of_kZeroCoordinates
#print axioms actualEndpointCutoffBound_of_actualCoordinates
#print axioms kZeroEndpointCutoffActual
#print axioms kZeroEndpointCutoffActual_of_kZeroCoordinates
#print axioms positiveTwoEndpointCutoffPackage
#print axioms positiveTwoEndpointCutoffPackage_of_inputs
#print axioms exists_endpointCutoffActualPackage
#print axioms actualEndpointCutoffBound_zero
#print axioms kZeroEndpointCutoffActual_zero

end

end RBM.APrimeFirstCellDeltaEndpointCutTruncActual
