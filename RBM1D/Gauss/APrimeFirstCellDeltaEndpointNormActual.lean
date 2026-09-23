/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCoordinateMoment
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointFromCoords

/-!
# T569: actual variable-delta first-cell endpoint norm

T562's closed canonical high-order coordinate estimate discharges exactly
the open coordinate premise of T565.  The output is the actual target-weight
endpoint `jSnorm` estimate on the first cell only.
-/

namespace RBM.APrimeFirstCellDeltaEndpointNormActual

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual target-weight endpoint conclusion. -/
def endpointNormAt (tauPrime delta : Real) (p N k : Nat) : Prop :=
  APrimeFirstCellDeltaEndpointFromCoords.endpointMomentAt
    tauPrime delta p N k

/-- Uniform endpoint bounds for every positive active first-cell prefix. -/
def actualEndpointNorms (tauPrime delta : Real) (p : Nat) : Prop :=
  APrimeFirstCellDeltaEndpointFromCoords.actualEndpointMoments
    tauPrime delta p

/-- Exact empty-prefix identities and endpoint bound. -/
def kZeroEndpointNorms (tauPrime delta : Real) (p : Nat) : Prop :=
  APrimeFirstCellDeltaEndpointFromCoords.kZeroEndpointMoments
    tauPrime delta p

/-- The same-event positive `k = 2` sample from T562, retaining both
weight-one plateaux and adding the actual target-weight endpoint norm. -/
def positiveTwoEndpointNormPackage
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
      endpointNormAt tauPrime delta p N 2

/-- T562's fixed-size coordinate conclusion is definitionally the open
coordinate premise consumed by T565, with the same order, measure, endpoint,
weight, and coordinate family. -/
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
    APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt,
    APrimeFirstCellMinkowskiExact.endpoint,
    APrimeFirstCellMinkowskiExact.Y,
    APrimeFirstCellDeltaTargetWeight.canonicalWeight,
    APrimeFirstCellCanonicalPlateau.canonicalWeight,
    APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellGeneratorHle.canonicalWeight,
    APrimeFirstCellGeneratorHle.actualWeight,
    APrimeFirstCellDeltaMinkowskiConsumer.weight,
    APrimeFirstCellDeltaMinkowskiConsumer.canonicalM, d] using h

/-- T562 closes T565's positive-active open coordinate premise. -/
theorem actualCoordinatePremise_of_coordinateMoments
    {tauPrime delta : Real} {p : Nat}
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
      tauPrime delta p) :
    APrimeFirstCellDeltaEndpointFromCoords.actualCoordinatePremise
      tauPrime delta p := by
  filter_upwards [hcoords] with N hcoordsN
  intro k hk1 hk
  exact coordinateMomentAt_of_coordinateBounds
    (hcoordsN k hk1 hk)

/-- T562 closes T565's exact empty-prefix coordinate premise. -/
theorem kZeroCoordinatePremise_of_coordinateMoments
    {tauPrime delta : Real} {p : Nat}
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.kZeroCoordinateMoments
      tauPrime delta p) :
    APrimeFirstCellDeltaEndpointFromCoords.kZeroCoordinatePremise
      tauPrime delta p := by
  filter_upwards [hcoords] with N hcoordsN
  exact coordinateMomentAt_of_coordinateBounds hcoordsN.2

/-- The actual positive-active endpoint norm obtained by substituting T562
into T565's open premise. -/
theorem actualEndpointNorms_of_coordinateMoments
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
      tauPrime delta p) :
    actualEndpointNorms tauPrime delta p := by
  exact APrimeFirstCellDeltaEndpointFromCoords.actualEndpointMoments_of_coords
    hTau hDelta hp
      (actualCoordinatePremise_of_coordinateMoments hcoords)

/-- The actual exact-`k = 0` endpoint package obtained by substituting T562
into T565's open empty-prefix premise. -/
theorem kZeroEndpointNorms_of_coordinateMoments
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.kZeroCoordinateMoments
      tauPrime delta p) :
    kZeroEndpointNorms tauPrime delta p := by
  exact APrimeFirstCellDeltaEndpointFromCoords.kZeroEndpointMoments_of_coords
    hTau hDelta hp
      (kZeroCoordinatePremise_of_coordinateMoments hcoords)

/-- T562's selected event sample and both weight-one facts are retained
unchanged.  The endpoint norm is a separate deterministic consequence of
its uniform coordinate bound. -/
theorem positiveTwoEndpointNormPackage_of_coordinatePackage
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hpositive :
      APrimeFirstCellDeltaCoordinateMoment.positiveTwoCoordinateMomentPackage
        tauPrime delta p) :
    positiveTwoEndpointNormPackage tauPrime delta p := by
  filter_upwards [hpositive, eventually_ge_atTop 81]
      with N hpositiveN hN
  obtain ⟨omega, homega, hvpos, hk, hvhalf, htarget,
    hcanonical, hcoords⟩ := hpositiveN
  refine ⟨omega, homega, hvpos, hk, hvhalf, htarget, hcanonical, ?_⟩
  unfold endpointNormAt
  exact APrimeFirstCellDeltaEndpointFromCoords.endpointMomentAt_of_coords
    hTau hDelta hp hN hk
      (coordinateMomentAt_of_coordinateBounds hcoords)

/-- Closed actual first-cell endpoint-norm package, using exactly T562's
single `tauPrime`, literal event, active and zero coordinate conclusions, and
positive same-event weight-one sample. -/
theorem exists_endpointNormPackage :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall delta : Real, 0 < delta -> delta <= 1 / 100 ->
      forall p : Nat, 1 <= p ->
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        actualEndpointNorms tauPrime delta p ∧
        kZeroEndpointNorms tauPrime delta p ∧
        positiveTwoEndpointNormPackage tauPrime delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCoordinateMoment.exists_coordinateMomentPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  obtain ⟨hmeas, hprob, hcoords, hkzero, hpositive⟩ :=
    hall delta hDelta hDelta100 p hp
  exact ⟨hmeas, hprob,
    actualEndpointNorms_of_coordinateMoments hTau hDelta hp hcoords,
    kZeroEndpointNorms_of_coordinateMoments hTau hDelta hp hkzero,
    positiveTwoEndpointNormPackage_of_coordinatePackage
      hTau hDelta hp hpositive⟩

#print axioms coordinateMomentAt_of_coordinateBounds
#print axioms actualCoordinatePremise_of_coordinateMoments
#print axioms kZeroCoordinatePremise_of_coordinateMoments
#print axioms actualEndpointNorms_of_coordinateMoments
#print axioms kZeroEndpointNorms_of_coordinateMoments
#print axioms positiveTwoEndpointNormPackage_of_coordinatePackage
#print axioms exists_endpointNormPackage

end

end RBM.APrimeFirstCellDeltaEndpointNormActual
