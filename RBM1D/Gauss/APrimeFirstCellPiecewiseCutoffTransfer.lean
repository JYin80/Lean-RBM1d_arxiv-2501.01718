/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointCutTruncActual
import RBM1D.Gauss.APrimeFirstCellPiecewiseWeightFields

/-!
# T574: coefficient-one first-cell piecewise cutoff transfer

The moment-order-independent first-cell weight is the literal `piecewiseW`
underlying T567's widened target weight.  Its endpoint cutoff integral uses
the same actual `jSnorm`, cutoff, order, Gaussian measure, mesh, and endpoint
as T567.  Pointwise weight domination transfers T567's bound with coefficient
one.

This is only a one-endpoint first-cell adapter.  It does not assert a
`WeightedMoment`, a moving-window family estimate, or an A-prime slot.
-/

namespace RBM.APrimeFirstCellPiecewiseCutoffTransfer

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel MomentDuhamelCut

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The exact moment-order-independent first-cell piecewise weight. -/
noncomputable def piecewiseWeight
    (tauPrime delta : Real) (N k : Nat) : Ω d -> Real :=
  APrimeWeight.piecewiseW
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh delta N k

/-- The piecewise-weight endpoint cutoff integral.  Only the exponent depends
on `p`; the weight itself does not. -/
noncomputable def endpointCutoffIntegral
    (tauPrime delta : Real) (p N k : Nat) : Real :=
  ∫ omega,
    piecewiseWeight tauPrime delta N k omega *
      abs (cutTrunc ((N : Real) ^ (2 * delta))
        (APrimeFirstCellDeltaEndpointCutTrunc.endpointJ N k omega)) ^
          (2 * p) ∂(P d)

/-- The exact coefficient and exponent inherited from T567. -/
def endpointCutoffBoundAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  endpointCutoffIntegral tauPrime delta p N k <=
    2 ^ (2 * p) * (N : Real) ^ ((delta / 2) * (p : Real))

/-- Uniform positive-active-prefix form of the piecewise cutoff bound. -/
def actualEndpointCutoffBound
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    endpointCutoffBoundAt tauPrime delta p N k

/-- Exact empty-prefix geometry, the order-independent weight-one identity,
and the corresponding cutoff conclusion. -/
def kZeroEndpointCutoffBound
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 ∧
    (∀ omega : Ω d,
      piecewiseWeight tauPrime delta N 0 omega = 1) ∧
    endpointCutoffBoundAt tauPrime delta p N 0

/-- The piecewise weight is pointwise below T567's literal target weight. -/
theorem piecewiseWeight_le_targetWeight
    (tauPrime delta : Real) (p N k : Nat) (omega : Ω d) :
    piecewiseWeight tauPrime delta N k omega <=
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k omega := by
  exact APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh)
    (N₀ := 1)
    (J := fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (s := fun _ => 0) (t := firstCellT tauPrime)
    (mesh := APrimeSmoothTransition.transitionMesh)
    (by norm_num) delta p N k omega

/-- Honest integrability of the dominating target-weight cutoff integrand. -/
theorem integrable_targetCutoffIntegrand
    (tauPrime delta : Real) (p N k : Nat) (hN : 1 <= N) :
    Integrable (fun omega =>
      APrimeFirstCellDeltaTargetWeight.targetWeight
          tauPrime delta p N k omega *
        abs (cutTrunc ((N : Real) ^ (2 * delta))
          (APrimeFirstCellDeltaEndpointCutTrunc.endpointJ N k omega)) ^
            (2 * p)) (P d) := by
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  exact Step2Bootstrap.integrable_weight_mul
    (Real.rpow_pos_of_pos hNpos (2 * delta))
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_nonneg
      tauPrime delta p N k)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_le_one
      tauPrime delta p N k)
    (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_aestronglyMeasurable
      tauPrime delta p N k)
    (fun omega => APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
      d 0 60 (fun _ => 0) N
        (APrimeFirstCellMinkowskiExact.endpoint N k) omega)
    (APrimeSlotFields.measurable_jSnorm
      (sample d) 0 60 (fun _ => 0) N
        (APrimeFirstCellMinkowskiExact.endpoint N k)).aestronglyMeasurable
    (2 * p)

/-- Coefficient-one integral domination.  The cutoff power is nonnegative,
so no coefficient, exponent, measure, endpoint, or cutoff changes. -/
theorem endpointCutoffIntegral_le_target
    (tauPrime delta : Real) (p N k : Nat) (hN : 1 <= N) :
    endpointCutoffIntegral tauPrime delta p N k <=
      APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffIntegral
        tauPrime delta p N k := by
  unfold endpointCutoffIntegral
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun omega =>
      mul_nonneg
        (APrimeWeight.piecewiseW_nonneg
          (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
            APrimeSmoothTransition.transitionMesh) 1
          (fun N u omega => Step2Moment.jSnorm
            (sample d) 0 60 (fun _ => 0) N u omega)
          (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh delta N k omega)
        (by positivity))
    (integrable_targetCutoffIntegrand tauPrime delta p N k hN)
    (Filter.Eventually.of_forall fun omega =>
      mul_le_mul_of_nonneg_right
        (piecewiseWeight_le_targetWeight tauPrime delta p N k omega)
        (by positivity))

/-- Transfer one target-weight endpoint cutoff bound with coefficient one. -/
theorem endpointCutoffBoundAt_of_target
    {tauPrime delta : Real} {p N k : Nat} (hN : 1 <= N)
    (htarget :
      APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt
        tauPrime delta p N k) :
    endpointCutoffBoundAt tauPrime delta p N k := by
  exact (endpointCutoffIntegral_le_target tauPrime delta p N k hN).trans
    htarget

/-- T567's positive-active-prefix conclusion transfers unchanged. -/
theorem actualEndpointCutoffBound_of_target
    {tauPrime delta : Real} {p : Nat}
    (htarget :
      APrimeFirstCellDeltaEndpointCutTrunc.actualEndpointCutoffBound
        tauPrime delta p) :
    actualEndpointCutoffBound tauPrime delta p := by
  filter_upwards [htarget, eventually_ge_atTop 1] with N htargetN hN
  intro k hk1 hk
  exact endpointCutoffBoundAt_of_target hN (htargetN k hk1 hk)

/-- The moment-order-independent piecewise weight equals one exactly at the
empty prefix, for every sample and every parameter value. -/
theorem piecewiseWeight_k_zero
    (tauPrime delta : Real) (N : Nat) (omega : Ω d) :
    piecewiseWeight tauPrime delta N 0 omega = 1 := by
  let J : Nat -> Real -> Ω d -> Real := fun N u omega =>
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega
  let s : Nat -> Real := fun _ => 0
  let t : Nat -> Real := firstCellT tauPrime
  let mesh : Nat -> Real := APrimeSmoothTransition.transitionMesh
  have hpref : omega ∈ Step2Bootstrap.prefNet J s mesh
      (fun N _ => (N : Real) ^ (2 * delta) * 1) N 0 := by
    intro j hj
    omega
  have hlo : 1 <= APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh
      delta N 0 omega :=
    APrimeWeight.piecewiseW_dom_canonical
      (fun N u omega =>
        APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
          d 0 60 (fun _ => 0) N u omega)
      delta N 0 omega hpref
  have hhi := APrimeWeight.piecewiseW_le_one
    (APrimeWeight.canonicalR s t mesh) 1 J s t mesh
    delta N 0 omega
  exact le_antisymm hhi hlo

/-- The first-cell endpoint itself is exactly zero at the empty prefix. -/
@[simp] theorem endpoint_k_zero (N : Nat) :
    APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 := by
  simp [APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero]

/-- T567's exact empty-prefix result transfers without retaining any of its
unrelated event or stochastic-resident fields. -/
theorem kZeroEndpointCutoffBound_of_target
    {tauPrime delta : Real} {p : Nat}
    (htarget :
      APrimeFirstCellDeltaEndpointCutTruncActual.kZeroEndpointCutoffActual
        tauPrime delta p) :
    kZeroEndpointCutoffBound tauPrime delta p := by
  filter_upwards [htarget, eventually_ge_atTop 1] with N htargetN hN
  refine ⟨endpoint_k_zero N, ?_, ?_⟩
  · exact piecewiseWeight_k_zero tauPrime delta N
  · exact endpointCutoffBoundAt_of_target hN htargetN.2.2.2.2.2

/-- Closed positive-order first-cell transfer, using exactly the `tauPrime`
selected by T567 and adding no hypotheses. -/
theorem exists_piecewiseEndpointCutoffPackage :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ p : Nat, 1 <= p ->
        actualEndpointCutoffBound tauPrime delta p ∧
        kZeroEndpointCutoffBound tauPrime delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaEndpointCutTruncActual.exists_endpointCutoffActualPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  obtain ⟨_hmeas, _hprob, hactive, hkzero, _hpositive⟩ :=
    hall delta hDelta hDelta100 p hp
  exact ⟨actualEndpointCutoffBound_of_target hactive,
    kZeroEndpointCutoffBound_of_target hkzero⟩

/-- The order-zero active-prefix bound transfers from T567 unconditionally. -/
theorem actualEndpointCutoffBound_zero (tauPrime delta : Real) :
    actualEndpointCutoffBound tauPrime delta 0 := by
  exact actualEndpointCutoffBound_of_target
    (APrimeFirstCellDeltaEndpointCutTruncActual.actualEndpointCutoffBound_zero
      tauPrime delta)

/-- The exact empty-prefix package also holds unconditionally at order zero. -/
theorem kZeroEndpointCutoffBound_zero (tauPrime delta : Real) :
    kZeroEndpointCutoffBound tauPrime delta 0 := by
  exact kZeroEndpointCutoffBound_of_target
    (APrimeFirstCellDeltaEndpointCutTruncActual.kZeroEndpointCutoffActual_zero
      tauPrime delta)

/-- Actual-model nontriviality: at the same positive first-cell prefix, the
exact p-independent weight is eventually one at the zero scalar sample and
zero at the explicit transition scalar sample.  No stochastic moment or
event fact is attached. -/
theorem piecewiseWeight_nonconstant_witness :
    ∀ᶠ N : Nat in atTop,
      piecewiseWeight 1 (1 / 8) N 2
          (APrimeSmoothTransition.scalarSample d 0) = 1 ∧
      piecewiseWeight 1 (1 / 8) N 2
          (APrimeSmoothTransition.scalarSample d
            (2 / Real.sqrt
              ((APrimeSmoothTransition.transitionMesh N)⁻¹))) = 0 := by
  simpa only [piecewiseWeight,
    APrimeFirstCellPiecewiseWeightFields.weight,
    APrimeFirstCellPiecewiseWeightFields.actualJ] using
      APrimeFirstCellPiecewiseWeightFields.eventually_weight_nonconstant_witness

#print axioms piecewiseWeight
#print axioms endpointCutoffIntegral
#print axioms endpointCutoffBoundAt
#print axioms actualEndpointCutoffBound
#print axioms kZeroEndpointCutoffBound
#print axioms piecewiseWeight_le_targetWeight
#print axioms integrable_targetCutoffIntegrand
#print axioms endpointCutoffIntegral_le_target
#print axioms endpointCutoffBoundAt_of_target
#print axioms actualEndpointCutoffBound_of_target
#print axioms piecewiseWeight_k_zero
#print axioms endpoint_k_zero
#print axioms kZeroEndpointCutoffBound_of_target
#print axioms exists_piecewiseEndpointCutoffPackage
#print axioms actualEndpointCutoffBound_zero
#print axioms kZeroEndpointCutoffBound_zero
#print axioms piecewiseWeight_nonconstant_witness

end

end RBM.APrimeFirstCellPiecewiseCutoffTransfer
