/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyWidenedMoment
import RBM1D.Gauss.APrimeFirstCellEndpointHighMoment

/-!
# T528: first-cell endpoint moments under the widened target weight

For fixed `1 <= p <= P`, T524 supplies the order-`p` family maximum
bound under the literal widened target weight.  T522's exact endpoint
identity and coefficient-one weighted Minkowski then add the deterministic
endpoint term without changing the `delta / 2` family exponent.
-/

namespace RBM.APrimeFirstCellEndpointWidenedMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real :=
  APrimeFirstCellFamilyWidenedMoment.delta
noncomputable abbrev alpha : Real :=
  APrimeFirstCellFamilyWidenedMoment.alpha

/-- The endpoint moment under the literal order-`p` widened target weight. -/
def endpointWidenedMomentAt (tauPrime : Real) (p N k : Nat) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k) p
      (fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
        N (endpoint N k) omega) <=
    1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 +
      (N : Real) ^ (delta / 2) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))

/-- The target-weight family integrand is integrable at every active endpoint. -/
theorem integrable_targetWeight_familyMax_pow {tauPrime : Real}
    (hTau : 0 < tauPrime) {p N k : Nat}
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega =>
      APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega *
        |familyMax N k omega| ^ (2 * p)) (Gauss.P d) := by
  have hi := APrimeFirstCellFamilyLowMomentSameWeight.integrable_familyMax_pow
    hTau hk p
  have hwmeas : AEStronglyMeasurable
      (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k)
      (Gauss.P d) := by
    exact APrimeWeight.widenedW_meas
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u omega => Step2Moment.jSnorm
        (sample d) 0 60 (fun _ => 0) N u omega)
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh
      (fun N u => APrimeSlotFields.measurable_jSnorm
        (sample d) 0 60 (fun _ => 0) N u)
      p (1 / 2000) N k
  have hMmeas : AEStronglyMeasurable
      (fun omega => |familyMax N k omega| ^ (2 * p)) (Gauss.P d) :=
    (APrimeFirstCellFamilyLowMomentSameWeight.continuous_familyMax
      hTau hk).abs.pow (2 * p) |>.aestronglyMeasurable
  apply hi.mono' (hwmeas.mul hMmeas)
  exact Filter.Eventually.of_forall fun omega => by
    have hw0 : 0 <= APrimeFirstCellCrossOrderWeight.targetWeight
        tauPrime p N k omega := by
      exact APrimeWeight.widenedW_nonneg
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u omega => Step2Moment.jSnorm
          (sample d) 0 60 (fun _ => 0) N u omega)
        (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega
    have hw1 : APrimeFirstCellCrossOrderWeight.targetWeight
        tauPrime p N k omega <= 1 := by
      exact APrimeWeight.widenedW_le_one
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u omega => Step2Moment.jSnorm
          (sample d) 0 60 (fun _ => 0) N u omega)
        (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega
    change ‖APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega *
      |familyMax N k omega| ^ (2 * p)‖ <=
      |familyMax N k omega| ^ (2 * p)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (by positivity))]
    exact mul_le_of_le_one_left (by positivity) hw1

/-- Fixed-size coefficient-one assembly from T524 and T522. -/
theorem endpointWidenedMomentAt_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p N k : Nat}
    (hp : 1 <= p)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily : APrimeFirstCellFamilyWidenedMoment.familyWidenedMomentAt
      tauPrime p N k) : endpointWidenedMomentAt tauPrime p N k := by
  let w := APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k
  let M := familyMax N k
  let b := 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) :=
    Step2Moment.ratR_pos (by norm_num) (by norm_num) hv1
  have hb : 0 <= b := by dsimp [b]; positivity
  have hw0 : forall omega, 0 <= w omega := by
    intro omega
    exact APrimeWeight.widenedW_nonneg
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u omega => Step2Moment.jSnorm
        (sample d) 0 60 (fun _ => 0) N u omega)
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega
  have hw1 : forall omega, w omega <= 1 := by
    intro omega
    exact APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u omega => Step2Moment.jSnorm
        (sample d) 0 60 (fun _ => 0) N u omega)
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega
  have hM0 : forall omega, 0 <= M omega := by
    intro omega
    dsimp [M, familyMax]
    let a := Classical.choice
      (inferInstance : Nonempty (LoopArg (d.L N) 2))
    exact (abs_nonneg (Y N k a (endpoint N k) omega)).trans
      (Finset.le_sup' (fun a => |Y N k a (endpoint N k) omega|)
        (Finset.mem_univ a))
  have hMi : Integrable (fun omega => w omega * |M omega| ^ (2 * p))
      (Gauss.P d) := by
    exact integrable_targetWeight_familyMax_pow hTau hk
  have htriangle :=
    APrimeFirstCellEndpointHighMoment.momNormW_const_add_le
      hp hw0 hw1 hM0 hMi hb
  have hid : (fun omega => Step2Moment.jSnorm (sample d) 0 60
      (fun _ => 0) N (endpoint N k) omega) = fun omega => b + M omega := by
    funext omega
    exact APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
      hTau N k hk omega
  unfold endpointWidenedMomentAt
  rw [hid]
  exact htriangle.trans (by
    simpa only [add_comm] using add_le_add_left hfamily b)

/-- Positive active indices, uniformly after one eventual size threshold. -/
def actualEndpointWidenedMoment (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    endpointWidenedMomentAt tauPrime p N k

theorem actualEndpointWidenedMoment_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p : Nat} (hp : 1 <= p)
    (hfamily : APrimeFirstCellFamilyWidenedMoment.actualFamilyWidenedMoment
      tauPrime p) : actualEndpointWidenedMoment tauPrime p := by
  filter_upwards [hfamily] with N hfamilyN
  intro k hk1 hk
  exact endpointWidenedMomentAt_of_family hTau hp hk
    (hfamilyN k hk1 hk)

/-- The empty-prefix index is retained as a separate exact-ratio branch. -/
def kZeroEndpointWidenedMoment (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ endpointWidenedMomentAt tauPrime p N 0 ∧
      momNormW (Gauss.P d)
        (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 0) p
        (fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
          N (endpoint N 0) omega) <= 1 + (N : Real) ^ (delta / 2)

theorem kZeroEndpointWidenedMoment_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p : Nat} (hp : 1 <= p)
    (hzero : APrimeFirstCellFamilyWidenedMoment.kZeroFamilyWidenedMoment
      tauPrime p) : kZeroEndpointWidenedMoment tauPrime p := by
  filter_upwards [hzero] with N hz
  obtain ⟨hv, hfamily, _hsimple⟩ := hz
  have hendpoint := endpointWidenedMomentAt_of_family hTau hp
    (Nat.zero_le _) hfamily
  have hR : Step2Moment.ratR 0 (fun _ => 0) N 0 = 1 := by
    unfold Step2Moment.ratR
    exact div_self (Step2.etaT_pos' (E := 0) (by norm_num) (by norm_num)).ne'
  refine ⟨hv, hendpoint, ?_⟩
  simpa [endpointWidenedMomentAt, hv, hR, etaT, mE_zero] using hendpoint

/-- T524's positive `k = 2` resident, carrying the endpoint moment. -/
def positiveTwoEndpointWidenedMomentResident
    (tauPrime : Real) (p P : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 <= firstCellT tauPrime N ∧
    APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 2 omega = 1 ∧
    weight tauPrime P N 2 omega = 1 ∧
    endpointWidenedMomentAt tauPrime p N 2

theorem positiveTwoEndpointWidenedMomentResident_of_family
    {tauPrime : Real} {p P : Nat} (hTau : 0 < tauPrime)
    (hp : 1 <= p)
    (hresident :
      APrimeFirstCellFamilyWidenedMoment.positiveTwoFamilyWidenedMomentResident
        tauPrime p P) : positiveTwoEndpointWidenedMomentResident tauPrime p P := by
  filter_upwards [hresident] with N hr
  obtain ⟨omega, homega, hk, hvpos, hvle, htarget, hweight, hfamily⟩ := hr
  exact ⟨omega, homega, hk, hvpos, hvle, htarget, hweight,
    endpointWidenedMomentAt_of_family hTau hp hk hfamily⟩

/-- One parameter and one sharp event supply every fixed `1 <= p <= P`,
including the zero branch and the same positive target-weight-one resident. -/
theorem exists_endpointWidenedMoment_with_resident :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall p P : Nat, 1 <= p -> p <= P -> 8000 <= P ->
        (forall N k omega,
          APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega <=
            weight tauPrime P N k omega) ∧
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (Gauss.P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        (∀ᶠ N : Nat in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N).Nonempty) ∧
        actualEndpointWidenedMoment tauPrime p ∧
        kZeroEndpointWidenedMoment tauPrime p ∧
        positiveTwoEndpointWidenedMomentResident tauPrime p P := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellFamilyWidenedMoment.exists_familyWidenedMoment_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro p P hp hpP hP
  obtain ⟨hcompare, hmeas, hprob, hnonempty, hfamily, hzero, hresident⟩ :=
    hall p P hp hpP hP
  exact ⟨hcompare, hmeas, hprob, hnonempty,
    actualEndpointWidenedMoment_of_family hTau hp hfamily,
    kZeroEndpointWidenedMoment_of_family hTau hp hzero,
    positiveTwoEndpointWidenedMomentResident_of_family hTau hp hresident⟩

#print axioms integrable_targetWeight_familyMax_pow
#print axioms endpointWidenedMomentAt_of_family
#print axioms actualEndpointWidenedMoment_of_family
#print axioms kZeroEndpointWidenedMoment_of_family
#print axioms positiveTwoEndpointWidenedMomentResident_of_family
#print axioms exists_endpointWidenedMoment_with_resident

end

end RBM.APrimeFirstCellEndpointWidenedMoment
