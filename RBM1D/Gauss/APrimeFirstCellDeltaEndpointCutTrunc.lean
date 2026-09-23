/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCutTruncIntegral
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointMinkowski

/-!
# T563: variable-delta actual endpoint cutoff adapter

T553's analytic cutoff conversion is specialized to the actual first-cell
target weight and endpoint `jSnorm`.  The endpoint moment-norm estimate is an
explicit premise throughout; this module does not produce it.
-/

namespace RBM.APrimeFirstCellDeltaEndpointCutTrunc

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel MomentDuhamelCut

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual first-cell endpoint observable. -/
noncomputable abbrev endpointJ (N k : Nat) : Ω d -> Real :=
  fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N
    (APrimeFirstCellMinkowskiExact.endpoint N k) omega

/-- The exact target-weight cutoff integral at cutoff `N^(2*delta)`. -/
noncomputable def endpointCutoffIntegral
    (tauPrime delta : Real) (p N k : Nat) : Real :=
  ∫ omega,
    APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k omega *
      |cutTrunc ((N : Real) ^ (2 * delta)) (endpointJ N k omega)| ^
        (2 * p) ∂(Gauss.P d)

/-- The deliberately open actual endpoint norm premise. -/
def endpointNormPremiseAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k) p (endpointJ N k) ≤
    2 * (N : Real) ^ (delta / 4)

/-- The exact desired cutoff conclusion at one endpoint. -/
def endpointCutoffBoundAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  endpointCutoffIntegral tauPrime delta p N k ≤
    2 ^ (2 * p) * (N : Real) ^ ((delta / 2) * (p : Real))

/-- Honest weighted endpoint-power integrability for the same measure,
weight, order, and endpoint observable used by the cutoff integral. -/
theorem integrable_targetWeight_endpoint_pow
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    {p N k : Nat}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega =>
      APrimeFirstCellDeltaTargetWeight.targetWeight
          tauPrime delta p N k omega *
        |endpointJ N k omega| ^ (2 * p)) (Gauss.P d) := by
  exact APrimeFirstCellDeltaEndpointMinkowski.integrable_targetWeight_endpoint_pow
    (delta := delta) hTau hk

/-- Positive orders: T553 gives the exact constant and exponent from the
explicit endpoint norm premise. -/
theorem endpointCutoffBoundAt_of_norm
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    {p N k : Nat} (hp : 1 ≤ p) (hN : 1 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hnorm : endpointNormPremiseAt tauPrime delta p N k) :
    endpointCutoffBoundAt tauPrime delta p N k := by
  unfold endpointCutoffBoundAt endpointCutoffIntegral
  exact APrimeFirstCellDeltaCutTruncIntegral.integral_cutTrunc_le_of_momNormW
    hp hN
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_nonneg
      tauPrime delta p N k)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_le_one
      tauPrime delta p N k)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_aestronglyMeasurable
      tauPrime delta p N k)
    (fun omega => APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
      d 0 60 (fun _ => 0) N
        (APrimeFirstCellMinkowskiExact.endpoint N k) omega)
    (integrable_targetWeight_endpoint_pow hTau hk) hnorm

/-- At order zero, the integral is bounded directly by the probability-one
weight bound; no endpoint norm premise is used. -/
theorem endpointCutoffBoundAt_zero
    (tauPrime delta : Real) (N k : Nat) :
    endpointCutoffBoundAt tauPrime delta 0 N k := by
  unfold endpointCutoffBoundAt endpointCutoffIntegral
  simpa using
    (APrimeFirstCellDeltaCutTruncIntegral.integral_cutTrunc_zero_le
    (P := Gauss.P d)
    (W := APrimeFirstCellDeltaTargetWeight.targetWeight
      tauPrime delta 0 N k)
    (J := endpointJ N k) (delta := delta) (N := N)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_nonneg
      tauPrime delta 0 N k)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_le_one
      tauPrime delta 0 N k)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_aestronglyMeasurable
      tauPrime delta 0 N k))

/-- Eventual open premise over every positive active prefix. -/
def actualEndpointNormPremise
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N →
    endpointNormPremiseAt tauPrime delta p N k

/-- Eventual cutoff conclusion over every positive active prefix. -/
def actualEndpointCutoffBound
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N →
    endpointCutoffBoundAt tauPrime delta p N k

/-- Conditional eventual active-prefix adapter. -/
theorem actualEndpointCutoffBound_of_norm
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    {p : Nat} (hp : 1 ≤ p)
    (hnorm : actualEndpointNormPremise tauPrime delta p) :
    actualEndpointCutoffBound tauPrime delta p := by
  filter_upwards [hnorm, eventually_ge_atTop 1] with N hnormN hN
  intro k hk1 hk
  exact endpointCutoffBoundAt_of_norm hTau hp hN hk (hnormN k hk1 hk)

/-- The zero-order active-prefix wrapper is unconditional. -/
theorem actualEndpointCutoffBound_zero (tauPrime delta : Real) :
    actualEndpointCutoffBound tauPrime delta 0 := by
  filter_upwards [] with N
  intro k _hk1 _hk
  exact endpointCutoffBoundAt_zero tauPrime delta N k

/-- The deliberately open endpoint norm premise at the empty prefix. -/
def kZeroEndpointNormPremise
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpointNormPremiseAt tauPrime delta p N 0

/-- Exact empty-prefix geometry together with the cutoff conclusion. -/
def kZeroEndpointCutoffBound
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 ∧
      endpointCutoffBoundAt tauPrime delta p N 0

/-- Conditional positive-order empty-prefix adapter. -/
theorem kZeroEndpointCutoffBound_of_norm
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    {p : Nat} (hp : 1 ≤ p)
    (hnorm : kZeroEndpointNormPremise tauPrime delta p) :
    kZeroEndpointCutoffBound tauPrime delta p := by
  filter_upwards [hnorm, eventually_ge_atTop 1] with N hnormN hN
  exact ⟨by
      simp [APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero],
    endpointCutoffBoundAt_of_norm hTau hp hN (Nat.zero_le _) hnormN⟩

/-- The order-zero empty-prefix wrapper is unconditional and retains the
exact endpoint identity. -/
theorem kZeroEndpointCutoffBound_zero (tauPrime delta : Real) :
    kZeroEndpointCutoffBound tauPrime delta 0 := by
  filter_upwards [] with N
  exact ⟨by
      simp [APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero],
    endpointCutoffBoundAt_zero tauPrime delta N 0⟩

/-- T553's nonzero one-point probability-space witness is retained verbatim
to certify that the conditional analytic interface is satisfiable. -/
theorem conditional_interface_satisfiable :
    let P0 : Measure Unit := Measure.dirac ()
    let W : Unit -> Real := fun _ => 1
    let J : Unit -> Real := fun _ => 0
    P0 Set.univ = 1 ∧
      (forall omega, 0 <= W omega) ∧
      (forall omega, W omega <= 1) ∧
      AEStronglyMeasurable W P0 ∧
      (forall omega, 0 <= J omega) ∧
      Integrable (fun omega => W omega * |J omega| ^ (2 * 1)) P0 ∧
      momNormW P0 W 1 J <=
        2 * (1 : Real) ^ ((1 / 100 : Real) / 4) ∧
      (∫ omega, W omega *
        |cutTrunc ((1 : Real) ^ (2 * (1 / 100 : Real))) (J omega)| ^ (2 * 1)
          ∂P0) <=
        2 ^ (2 * 1) *
          (1 : Real) ^ (((1 / 100 : Real) / 2) * (1 : Real)) :=
  APrimeFirstCellDeltaCutTruncIntegral.conditional_interface_satisfiable

#print axioms endpointJ
#print axioms endpointCutoffIntegral
#print axioms endpointNormPremiseAt
#print axioms endpointCutoffBoundAt
#print axioms integrable_targetWeight_endpoint_pow
#print axioms endpointCutoffBoundAt_of_norm
#print axioms endpointCutoffBoundAt_zero
#print axioms actualEndpointNormPremise
#print axioms actualEndpointCutoffBound
#print axioms actualEndpointCutoffBound_of_norm
#print axioms actualEndpointCutoffBound_zero
#print axioms kZeroEndpointNormPremise
#print axioms kZeroEndpointCutoffBound
#print axioms kZeroEndpointCutoffBound_of_norm
#print axioms kZeroEndpointCutoffBound_zero
#print axioms conditional_interface_satisfiable

end

end RBM.APrimeFirstCellDeltaEndpointCutTrunc
