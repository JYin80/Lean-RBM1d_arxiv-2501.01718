/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCoordinateMoment
import RBM1D.Gauss.APrimeFirstCellDeltaTargetFamilyAssembly

/-!
# T568: actual variable-delta first-cell target-family package

T562's closed canonical high-order coordinate estimates discharge T557's
open coordinate premise.  T557 then supplies the coefficient-one transfer to
the target-weight family norm.
-/

namespace RBM.APrimeFirstCellDeltaTargetFamilyActual

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T562's fixed-size coordinate conclusions are definitionally T551/T557's
open coordinate premise. -/
theorem coordinateMomentAt_of_coordinateBounds
    {tauPrime delta : Real} {p N k : Nat}
    (hcoords : ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellDeltaCoordinateMoment.coordinateBoundAt
        tauPrime delta p N k a) :
    APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt
      tauPrime delta p N k := by
  intro a
  have h := hcoords a
  simpa [APrimeFirstCellDeltaCoordinateMoment.coordinateBoundAt,
    APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt,
    APrimeFirstCellDeltaCoordinateMoment.endpoint,
    APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
    APrimeFirstCellMinkowskiExact.endpoint,
    APrimeFirstCellDeltaMinkowskiConsumer.Y,
    APrimeFirstCellMinkowskiExact.Y, d] using h

/-- T562's all-active coordinate producer supplies T557's eventual premise
without changing the order, measure, weight, endpoint, or coordinate. -/
theorem familyCoordinateMoments_of_actualCoordinateMoments
    {tauPrime delta : Real} {p : Nat}
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
      tauPrime delta p) :
    APrimeFirstCellDeltaFamilyAssembly.actualCoordinateMoments
      tauPrime delta p := by
  filter_upwards [hcoords] with N hcoordsN
  intro k hk1 hk
  exact coordinateMomentAt_of_coordinateBounds (hcoordsN k hk1 hk)

/-- The closed actual target-family conclusion for every positive active
first-cell index. -/
theorem actualTargetFamilyMoments_of_actualCoordinateMoments
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
      tauPrime delta p) :
    APrimeFirstCellDeltaTargetFamilyAssembly.actualTargetFamilyMoments
      tauPrime delta p := by
  exact APrimeFirstCellDeltaTargetFamilyAssembly.actualTargetFamilyMoments_of_coords
    hTau hDelta hp
      (familyCoordinateMoments_of_actualCoordinateMoments hcoords)

/-- T562's exact zero-coordinate package supplies T557's exact zero
coordinate premise. -/
theorem familyKZeroCoordinateMoments_of_actual
    {tauPrime delta : Real} {p : Nat}
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.kZeroCoordinateMoments
      tauPrime delta p) :
    APrimeFirstCellDeltaTargetFamilyAssembly.kZeroCoordinateMoments
      tauPrime delta p := by
  filter_upwards [hcoords] with N hcoordsN
  exact coordinateMomentAt_of_coordinateBounds hcoordsN.2

/-- Exact `k = 0` target/canonical weight identities and target-family
bound from T562's exact zero-coordinate package. -/
theorem kZeroTargetFamilyMoments_of_actualCoordinates
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords : APrimeFirstCellDeltaCoordinateMoment.kZeroCoordinateMoments
      tauPrime delta p) :
    APrimeFirstCellDeltaTargetFamilyAssembly.kZeroTargetFamilyMoments
      tauPrime delta p := by
  exact APrimeFirstCellDeltaTargetFamilyAssembly.kZeroTargetFamilyMoments_of_coords
    hTau hDelta hp
      (familyKZeroCoordinateMoments_of_actual hcoords)

/-- Same-event positive `k = 2` package with both weights equal to one and
the proved numerical target-family conclusion. -/
def positiveTwoTargetFamilyPackage
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
      APrimeFirstCellDeltaTargetFamilyAssembly.targetFamilyMomentAt
        tauPrime delta p N 2

/-- T562's same-event plateau resident and T557's uniform deterministic
family conclusion combine without changing the resident sample. -/
theorem positiveTwoTargetFamilyPackage_of_inputs
    {tauPrime delta : Real} {p : Nat}
    (hpositive :
      APrimeFirstCellDeltaCoordinateMoment.positiveTwoCoordinateMomentPackage
        tauPrime delta p)
    (hfamily :
      APrimeFirstCellDeltaTargetFamilyAssembly.actualTargetFamilyMoments
        tauPrime delta p) :
    positiveTwoTargetFamilyPackage tauPrime delta p := by
  filter_upwards [hpositive, hfamily] with N hpositiveN hfamilyN
  obtain ⟨omega, homega, hvpos, hk, hvhalf,
    htarget, hcanonical, _hcoords⟩ := hpositiveN
  exact ⟨omega, homega, hvpos, hk, hvhalf, htarget, hcanonical,
    hfamilyN 2 (by norm_num) hk⟩

/-- Closed actual target-family package on T562's single `tauPrime` and
literal sharp common event. -/
theorem exists_actualTargetFamilyPackage :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        APrimeFirstCellDeltaCoordinateMoment.actualCoordinateMoments
          tauPrime delta p ∧
        APrimeFirstCellDeltaTargetFamilyAssembly.actualTargetFamilyMoments
          tauPrime delta p ∧
        APrimeFirstCellDeltaTargetFamilyAssembly.kZeroTargetFamilyMoments
          tauPrime delta p ∧
        positiveTwoTargetFamilyPackage tauPrime delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCoordinateMoment.exists_coordinateMomentPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  obtain ⟨hmeas, hprob, hcoords, hkzero, hpositive⟩ :=
    hall delta hDelta hDelta100 p hp
  have hfamily :=
    actualTargetFamilyMoments_of_actualCoordinateMoments
      hTau hDelta hp hcoords
  have hkfamily :=
    kZeroTargetFamilyMoments_of_actualCoordinates
      hTau hDelta hp hkzero
  exact ⟨hmeas, hprob, hcoords, hfamily, hkfamily,
    positiveTwoTargetFamilyPackage_of_inputs hpositive hfamily⟩

end

end RBM.APrimeFirstCellDeltaTargetFamilyActual

namespace RBM.APrimeFirstCellDeltaTargetFamilyActual

#print axioms coordinateMomentAt_of_coordinateBounds
#print axioms familyCoordinateMoments_of_actualCoordinateMoments
#print axioms actualTargetFamilyMoments_of_actualCoordinateMoments
#print axioms familyKZeroCoordinateMoments_of_actual
#print axioms kZeroTargetFamilyMoments_of_actualCoordinates
#print axioms positiveTwoTargetFamilyPackage_of_inputs
#print axioms exists_actualTargetFamilyPackage

end RBM.APrimeFirstCellDeltaTargetFamilyActual
