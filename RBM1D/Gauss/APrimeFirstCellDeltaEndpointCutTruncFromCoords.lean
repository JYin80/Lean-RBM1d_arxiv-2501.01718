/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointFromCoords
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointCutTrunc

/-!
# T566: endpoint cutoff integral from the open coordinate premise

T565 turns the explicit canonical high-order coordinate premise into the
actual target endpoint norm.  T563 consumes exactly that norm, with the same
measure, target weight, order, endpoint observable, and cutoff.  Their
composition gives the exact cutoff integral bound while keeping the
coordinate premise visibly open.

The zero-order branch remains unconditional.  This module asserts no
first-cell or general `hfamily`, `APrimeSlot'`, A-prime, or paper closure.
-/

namespace RBM.APrimeFirstCellDeltaEndpointCutTruncFromCoords

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The two delivered endpoint interfaces have literally identical
observables, measures, target weights, and moment orders. -/
theorem endpoint_interfaces_identical
    (tauPrime delta : Real) (p N k : Nat) :
    APrimeFirstCellDeltaEndpointFromCoords.endpointJ N k =
        APrimeFirstCellDeltaEndpointCutTrunc.endpointJ N k ∧
      (APrimeFirstCellDeltaEndpointFromCoords.endpointMomentAt
          tauPrime delta p N k ↔
        APrimeFirstCellDeltaEndpointCutTrunc.endpointNormPremiseAt
          tauPrime delta p N k) := by
  exact ⟨rfl, Iff.rfl⟩

/-- At one active endpoint, the open canonical order-`highOrder delta p`
coordinate premise gives T563's exact cutoff conclusion. -/
theorem endpointCutoffBoundAt_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p N k : Nat} (hp : 1 <= p)
    (hN : 81 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt
      tauPrime delta p N k) :
    APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt
      tauPrime delta p N k := by
  have hnorm :=
    APrimeFirstCellDeltaEndpointFromCoords.endpointMomentAt_of_coords
      hTau hDelta hp hN hk hcoords
  change APrimeFirstCellDeltaEndpointCutTrunc.endpointNormPremiseAt
    tauPrime delta p N k at hnorm
  exact APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt_of_norm
    hTau hp (by omega) hk hnorm

/-- The same open eventual coordinate premise supplies exactly T563's
eventual endpoint-norm premise. -/
theorem actualEndpointNormPremise_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords :
      APrimeFirstCellDeltaEndpointFromCoords.actualCoordinatePremise
        tauPrime delta p) :
    APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointNormPremise
      tauPrime delta p := by
  have hnorm :=
    APrimeFirstCellDeltaEndpointFromCoords.actualEndpointMoments_of_coords
      hTau hDelta hp hcoords
  filter_upwards [hnorm] with N hnormN
  intro k hk1 hk
  have h := hnormN k hk1 hk
  change APrimeFirstCellDeltaEndpointCutTrunc.endpointNormPremiseAt
    tauPrime delta p N k at h
  exact h

/-- For every positive active prefix, T565 followed by T563 yields the exact
cutoff integral `2^(2p) * N^((delta/2)*p)`. -/
theorem actualEndpointCutoffBound_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords :
      APrimeFirstCellDeltaEndpointFromCoords.actualCoordinatePremise
        tauPrime delta p) :
    APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
      tauPrime delta p := by
  exact APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound_of_norm
    hTau hp
      (actualEndpointNormPremise_of_coords hTau hDelta hp hcoords)

/-- T565's exact zero-prefix output is, in particular, T563's open
zero-prefix endpoint-norm premise. -/
theorem kZeroEndpointNormPremise_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords :
      APrimeFirstCellDeltaEndpointFromCoords.kZeroCoordinatePremise
        tauPrime delta p) :
    APrimeFirstCellDeltaEndpointCutTrunc.kZeroEndpointNormPremise
      tauPrime delta p := by
  have hnorm :=
    APrimeFirstCellDeltaEndpointFromCoords.kZeroEndpointMoments_of_coords
      hTau hDelta hp hcoords
  filter_upwards [hnorm] with N hnormN
  obtain ⟨_hv, _hR, _hb, _htarget, _hcanonical, h⟩ := hnormN
  change APrimeFirstCellDeltaEndpointCutTrunc.endpointNormPremiseAt
    tauPrime delta p N 0 at h
  exact h

/-- The exact zero-prefix identities retained from T565, together with
T563's exact cutoff conclusion. -/
def kZeroEndpointCutoffFromCoords
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧
    Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 0) = 1 ∧
    APrimeFirstCellDeltaEndpointMinkowski.endpointBaseline N 0 = 1 ∧
    (∀ omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 0 omega = 1) ∧
    (∀ omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 0 omega = 1) ∧
    APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt
      tauPrime delta p N 0

/-- Positive-order exact zero-prefix cutoff conclusion from the open
canonical coordinate premise. -/
theorem kZeroEndpointCutoffFromCoords_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hcoords :
      APrimeFirstCellDeltaEndpointFromCoords.kZeroCoordinatePremise
        tauPrime delta p) :
    kZeroEndpointCutoffFromCoords tauPrime delta p := by
  have hnorm :=
    APrimeFirstCellDeltaEndpointFromCoords.kZeroEndpointMoments_of_coords
      hTau hDelta hp hcoords
  have hcut :=
    APrimeFirstCellDeltaEndpointCutTrunc.kZeroEndpointCutoffBound_of_norm
      hTau hp (kZeroEndpointNormPremise_of_coords hTau hDelta hp hcoords)
  filter_upwards [hnorm, hcut] with N hnormN hcutN
  obtain ⟨hv, hR, hb, htarget, hcanonical, _hendpoint⟩ := hnormN
  exact ⟨hv, hR, hb, htarget, hcanonical, hcutN.2⟩

/-- The zero-order active-prefix cutoff bound is unconditional; no
coordinate or endpoint norm premise is used. -/
theorem actualEndpointCutoffBound_zero (tauPrime delta : Real) :
    APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
      tauPrime delta 0 :=
  APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound_zero
    tauPrime delta

/-- The zero-order empty prefix is unconditional and retains the same exact
endpoint, ratio, baseline, and two weight-one identities. -/
theorem kZeroEndpointCutoffFromCoords_zero (tauPrime delta : Real) :
    kZeroEndpointCutoffFromCoords tauPrime delta 0 := by
  have hcut :=
    APrimeFirstCellDeltaEndpointCutTrunc.kZeroEndpointCutoffBound_zero
      tauPrime delta
  filter_upwards [hcut] with N hcutN
  have hz := APrimeFirstCellDeltaEndpointMinkowski.kZero_exact
    tauPrime delta 0 N
  refine ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, ?_, hcutN.2⟩
  exact APrimeFirstCellDeltaTargetWeight.canonicalWeight_k_zero
    tauPrime delta (APrimeFirstCellDeltaTargetWeight.highOrder delta 0) N

#print axioms endpoint_interfaces_identical
#print axioms endpointCutoffBoundAt_of_coords
#print axioms actualEndpointNormPremise_of_coords
#print axioms actualEndpointCutoffBound_of_coords
#print axioms kZeroEndpointNormPremise_of_coords
#print axioms kZeroEndpointCutoffFromCoords
#print axioms kZeroEndpointCutoffFromCoords_of_coords
#print axioms actualEndpointCutoffBound_zero
#print axioms kZeroEndpointCutoffFromCoords_zero

end

end RBM.APrimeFirstCellDeltaEndpointCutTruncFromCoords
