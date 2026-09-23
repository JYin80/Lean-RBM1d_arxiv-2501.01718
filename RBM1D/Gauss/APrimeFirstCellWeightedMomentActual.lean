/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointCutTruncActual

/-!
# T571: actual first-cell `WeightedMoment`

The p-independent narrow `piecewiseW` is transferred pointwise, with
coefficient one, to T567's order-dependent `widenedW`.  T567 then supplies
the exact cutoff integral for every positive moment order.  The empty prefix
and order-zero branches are kept separate.

This module is restricted to the first grid cell.  It does not construct a
general moving-window family, `APrimeSlot'`, or an A-prime closure.
-/

namespace RBM.APrimeFirstCellWeightedMomentActual

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel MomentDuhamelCut

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual normalized endpoint observable, with `E = 0`, `D = 60`, and
left endpoint zero. -/
noncomputable def firstCellJ (N : ℕ) (u : ℝ) (omega : Ω d) : ℝ :=
  Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega

/-- The p-independent first-cell prefix weight required by `WeightedMoment`. -/
noncomputable def firstCellWeight
    (tauPrime delta : ℝ) (N k : ℕ) (omega : Ω d) : ℝ :=
  APrimeWeight.piecewiseW
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1 firstCellJ
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh delta N k omega

/-- The exact restricted first-cell `WeightedMoment` target.  Both the level
and bootstrap scale are identically one, and `delta0 = 1/100`. -/
def firstCellWeightedMoment (tauPrime : ℝ) : Prop :=
  WeightedMoment (Gauss.P d) firstCellJ (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    (fun _ _ => 1) (fun _ => 1) (1 / 100) (firstCellWeight tauPrime)

/-- The narrow p-independent weight is pointwise below T567's literal target
weight, with coefficient one. -/
theorem firstCellWeight_le_targetWeight
    (tauPrime delta : ℝ) (p N k : ℕ) (omega : Ω d) :
    firstCellWeight tauPrime delta N k omega <=
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k omega := by
  exact APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh)
    (N₀ := 1) (J := firstCellJ) (s := fun _ => 0)
    (t := firstCellT tauPrime)
    (mesh := APrimeSmoothTransition.transitionMesh)
    (by norm_num) delta p N k omega

/-- Positive first-cell geometry and a value-one sample for the actual
p-independent weight.  No stochastic estimate is attached to this sample. -/
def positiveTwoPiecewiseWeightPackage
    (tauPrime delta : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta (delta / 16) N,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v /\
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N /\
      v <= 1 / 2 /\
      firstCellWeight tauPrime delta N 2 omega = 1

/-- T567's positive `k = 2` resident lies on the plateau of the narrow
p-independent weight as well. -/
theorem positiveTwoPiecewiseWeightPackage_of_endpoint
    {tauPrime delta : ℝ} (hDelta : 0 < delta)
    (hpositive :
      APrimeFirstCellDeltaEndpointCutTruncActual.positiveTwoEndpointCutoffPackage
        tauPrime delta 1) :
    positiveTwoPiecewiseWeightPackage tauPrime delta := by
  filter_upwards [hpositive,
    APrimeFirstCellCommon.eventually_norm_F₂
      (2 * delta) (by positivity)] with N hpositiveN hprefix
  obtain ⟨omega, homega, hvpos, hk, hvhalf, _htarget, _hcanonical,
    _hcut⟩ := hpositiveN
  have hcommon : omega ∈ APrimeFirstCellMovingSupport.commonEvent tauPrime
      (APrimeFirstCellEGAllOutputRunning.sourceLoss (delta / 16))
      (APrimeFirstCellEGAllOutputRunning.sourceLoss (delta / 16))
      (delta / 16) N := homega.2
  have hdyn :=
    APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hcommon
  have hraw := APrimeSupportRunning.good_subset tauPrime
    (delta / 16) N hdyn
  have hvalues := hprefix omega hraw.1.1.1
  change
    firstCellJ N 0 omega <= (N : ℝ) ^ (2 * delta) /\
      firstCellJ N (APrimeSmoothTransition.transitionMesh N)⁻¹ omega <=
        (N : ℝ) ^ (2 * delta) at hvalues
  have hpref : omega ∈ prefNet firstCellJ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh
      (fun N _ => (N : ℝ) ^ (2 * delta) * 1) N 2 := by
    intro j hj
    interval_cases j
    · simpa only [cutNetPt, Nat.cast_zero, zero_div, add_zero, mul_one] using
        hvalues.1
    · simpa only [cutNetPt, Nat.cast_one, zero_add, one_div, mul_one] using
        hvalues.2
  have hone : 1 <= firstCellWeight tauPrime delta N 2 omega := by
    exact APrimeWeight.piecewiseW_dom_canonical
      (t := firstCellT tauPrime)
      (fun N u omega =>
        APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
          d 0 60 (fun _ => 0) N u omega)
      delta N 2 omega hpref
  have hupp : firstCellWeight tauPrime delta N 2 omega <= 1 := by
    exact APrimeWeight.piecewiseW_le_one
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh) 1 firstCellJ
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh delta N 2 omega
  refine ⟨omega, homega, ?_, hk, ?_, le_antisymm hupp hone⟩
  · simpa [APrimeFirstCellDeltaCoordinateMoment.endpoint,
      APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellMinkowskiExact.endpoint] using hvpos
  · simpa [APrimeFirstCellDeltaCoordinateMoment.endpoint,
      APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      APrimeFirstCellMinkowskiExact.endpoint] using hvhalf

/-- T567's closed cutoff package gives the actual p-independent first-cell
`WeightedMoment`.  The same `tauPrime` also has a positive active sample on
which the narrow weight is one. -/
theorem exists_firstCellWeightedMomentActual :
    ∃ tauPrime : ℝ, 0 < tauPrime /\
      firstCellWeightedMoment tauPrime /\
      ∀ delta : ℝ, 0 < delta -> delta <= 1 / 100 ->
        positiveTwoPiecewiseWeightPackage tauPrime delta := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaEndpointCutTruncActual.exists_endpointCutoffActualPackage
  refine ⟨tauPrime, hTau, ?_, ?_⟩
  · intro delta hDelta hDelta100 p
    refine ⟨2 ^ (2 * p), by positivity, ?_⟩
    by_cases hp0 : p = 0
    · subst p
      have hactive :=
        APrimeFirstCellDeltaEndpointCutTruncActual.actualEndpointCutoffBound_zero
          tauPrime delta
      have hkzero :=
        APrimeFirstCellDeltaEndpointCutTruncActual.kZeroEndpointCutoffActual_zero
          tauPrime delta
      filter_upwards [hactive, hkzero, eventually_ge_atTop 1] with
        N hactiveN hkzeroN hN k hk
      by_cases hk0 : k = 0
      · subst k
        have hcut := hkzeroN.2.2.2.2.2
        exact firstCell_integral_le_target hTau hN (Nat.zero_le _) hcut
      · have hk1 : 1 <= k := Nat.one_le_iff_ne_zero.mpr hk0
        have hcut := hactiveN k hk1 hk
        exact firstCell_integral_le_target hTau hN hk hcut
    · have hp : 1 <= p := Nat.one_le_iff_ne_zero.mpr hp0
      obtain ⟨_hmeas, _hprob, hactive, hkzero, _hpositive⟩ :=
        hall delta hDelta hDelta100 p hp
      filter_upwards [hactive, hkzero, eventually_ge_atTop 1] with
        N hactiveN hkzeroN hN k hk
      by_cases hk0 : k = 0
      · subst k
        have hcut := hkzeroN.2.2.2.2.2
        exact firstCell_integral_le_target hTau hN (Nat.zero_le _) hcut
      · have hk1 : 1 <= k := Nat.one_le_iff_ne_zero.mpr hk0
        have hcut := hactiveN k hk1 hk
        exact firstCell_integral_le_target hTau hN hk hcut
  · intro delta hDelta hDelta100
    obtain ⟨_hmeas, _hprob, _hactive, _hkzero, hpositive⟩ :=
      hall delta hDelta hDelta100 1 (by norm_num)
    exact positiveTwoPiecewiseWeightPackage_of_endpoint hDelta hpositive
where
  firstCell_integral_le_target
      {tauPrime delta : ℝ} {p N k : ℕ}
      (hTau : 0 < tauPrime) (hN : 1 <= N)
      (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N)
      (hcut :
        APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffBoundAt
          tauPrime delta p N k) :
      (∫ omega,
        firstCellWeight tauPrime delta N k omega *
          |cutTrunc ((N : ℝ) ^ (2 * delta) * 1)
            (firstCellJ N
              (cutNetPt (fun _ => 0)
                APrimeSmoothTransition.transitionMesh N k) omega)| ^
            (2 * p) ∂(Gauss.P d)) <=
        2 ^ (2 * p) *
          ((N : ℝ) ^ (delta / 2 * (p : ℝ)) * 1 ^ (2 * p)) := by
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have htheta : 0 < (N : ℝ) ^ (2 * delta) :=
      Real.rpow_pos_of_pos hNr _
    have hright : Integrable (fun omega =>
        APrimeFirstCellDeltaTargetWeight.targetWeight
            tauPrime delta p N k omega *
          |cutTrunc ((N : ℝ) ^ (2 * delta))
            (APrimeFirstCellDeltaEndpointCutTrunc.endpointJ N k omega)| ^
            (2 * p)) (Gauss.P d) := by
      exact integrable_weight_mul htheta
        (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_nonneg
          tauPrime delta p N k)
        (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_le_one
          tauPrime delta p N k)
        (APrimeFirstCellDeltaEndpointMinkowski.targetWeight_aestronglyMeasurable
          tauPrime delta p N k)
        (fun omega =>
          APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
            d 0 60 (fun _ => 0) N
              (APrimeFirstCellMinkowskiExact.endpoint N k) omega)
        ((APrimeSlotFields.measurable_jSnorm
          (sample d) 0 60 (fun _ => 0) N
            (APrimeFirstCellMinkowskiExact.endpoint N k)).aestronglyMeasurable)
        (2 * p)
    have hmono :
        (∫ omega,
          firstCellWeight tauPrime delta N k omega *
            |cutTrunc ((N : ℝ) ^ (2 * delta))
              (APrimeFirstCellDeltaEndpointCutTrunc.endpointJ N k omega)| ^
              (2 * p) ∂(Gauss.P d)) <=
          APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffIntegral
            tauPrime delta p N k := by
      unfold APrimeFirstCellDeltaEndpointCutTrunc.endpointCutoffIntegral
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun omega =>
          mul_nonneg
            (APrimeWeight.piecewiseW_nonneg
              (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
                APrimeSmoothTransition.transitionMesh) 1 firstCellJ
              (fun _ => 0) (firstCellT tauPrime)
              APrimeSmoothTransition.transitionMesh delta N k omega)
            (by positivity))
        hright
        (Filter.Eventually.of_forall fun omega =>
          mul_le_mul_of_nonneg_right
            (firstCellWeight_le_targetWeight
              tauPrime delta p N k omega) (by positivity))
    have hfinal := hmono.trans hcut
    simpa [firstCellJ, APrimeFirstCellMinkowskiExact.endpoint,
      APrimeFirstCellDeltaEndpointCutTrunc.endpointJ] using hfinal

#print axioms firstCellJ
#print axioms firstCellWeight
#print axioms firstCellWeightedMoment
#print axioms firstCellWeight_le_targetWeight
#print axioms positiveTwoPiecewiseWeightPackage
#print axioms positiveTwoPiecewiseWeightPackage_of_endpoint
#print axioms exists_firstCellWeightedMomentActual

end

end RBM.APrimeFirstCellWeightedMomentActual
