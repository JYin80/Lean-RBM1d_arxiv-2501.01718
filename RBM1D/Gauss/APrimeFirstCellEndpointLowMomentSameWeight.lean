/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyLowMomentSameWeight
import RBM1D.Gauss.APrimeFirstCellEndpointHighMoment

/-!
# T525: lower endpoint moments under the same high-order canonical weight

For fixed `1 <= p <= P`, the weight remains the literal order-`P`
canonical weight throughout.  T521 supplies the order-`p` family maximum
bound and integrability under that weight; T522 supplies the pointwise
endpoint identity and coefficient-one weighted Minkowski.
-/

namespace RBM.APrimeFirstCellEndpointLowMomentSameWeight

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real :=
  APrimeFirstCellFamilyLowMomentSameWeight.delta
noncomputable abbrev alpha : Real :=
  APrimeFirstCellFamilyLowMomentSameWeight.alpha

/-- The requested lower-order endpoint moment under the unchanged
order-`P` canonical weight. -/
def endpointLowMomentAt (tauPrime : Real) (p P N k : Nat) : Prop :=
  momNormW (Gauss.P d) (weight tauPrime P N k) p
      (fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
        N (endpoint N k) omega) <=
    1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 +
      (N : Real) ^ (delta / 2) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))

/-- Fixed-size coefficient-one assembly from T521 and T522.  The moment
order is `p`, while the canonical weight keeps its original order `P`. -/
theorem endpointLowMomentAt_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P N k : Nat}
    (hp : 1 <= p) (hpP : p <= P) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily :
      APrimeFirstCellFamilyLowMomentSameWeight.familyLowMomentAt
        tauPrime p P N k) :
    endpointLowMomentAt tauPrime p P N k := by
  let w := weight tauPrime P N k
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
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega
  have hw1 : forall omega, w omega <= 1 := by
    intro omega
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega
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
    exact (APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_integrability
      hTau (hp.trans hpP) hN hk (p := p)).1
  have htriangle :=
    APrimeFirstCellEndpointHighMoment.momNormW_const_add_le
      hp hw0 hw1 hM0 hMi hb
  have hid : (fun omega => Step2Moment.jSnorm (sample d) 0 60
      (fun _ => 0) N (endpoint N k) omega) = fun omega => b + M omega := by
    funext omega
    exact APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
      hTau N k hk omega
  unfold endpointLowMomentAt
  rw [hid]
  exact htriangle.trans (by
    simpa only [add_comm] using add_le_add_left hfamily b)

/-- Positive active indices, with both orders fixed before the uniform
eventual size threshold. -/
def actualEndpointLowMoment (tauPrime : Real) (p P : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    endpointLowMomentAt tauPrime p P N k

theorem actualEndpointLowMoment_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P : Nat}
    (hp : 1 <= p) (hpP : p <= P)
    (hfamily :
      APrimeFirstCellFamilyLowMomentSameWeight.actualFamilyLowMoment
        tauPrime p P) :
    actualEndpointLowMoment tauPrime p P := by
  filter_upwards [hfamily, eventually_gt_atTop 0] with N hfamilyN hN
  intro k hk1 hk
  exact endpointLowMomentAt_of_family hTau hp hpP hN hk
    (hfamilyN k hk1 hk)

/-- The zero index is retained separately, including its exact `R_0 = 1`
simplification. -/
def kZeroEndpointLowMoment (tauPrime : Real) (p P : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ endpointLowMomentAt tauPrime p P N 0 ∧
      momNormW (Gauss.P d) (weight tauPrime P N 0) p
        (fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
          N (endpoint N 0) omega) <= 1 + (N : Real) ^ (delta / 2)

theorem kZeroEndpointLowMoment_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P : Nat}
    (hp : 1 <= p) (hpP : p <= P)
    (hzero :
      APrimeFirstCellFamilyLowMomentSameWeight.kZeroFamilyLowMoment
        tauPrime p P) :
    kZeroEndpointLowMoment tauPrime p P := by
  filter_upwards [hzero, eventually_gt_atTop 0] with N hz hN
  obtain ⟨hv, hfamily, _hsimple⟩ := hz
  have hendpoint := endpointLowMomentAt_of_family hTau hp hpP hN
    (Nat.zero_le _) hfamily
  have hR : Step2Moment.ratR 0 (fun _ => 0) N 0 = 1 := by
    unfold Step2Moment.ratR
    exact div_self (Step2.etaT_pos' (E := 0) (by norm_num) (by norm_num)).ne'
  refine ⟨hv, hendpoint, ?_⟩
  simpa [endpointLowMomentAt, hv, hR, etaT, mE_zero] using hendpoint

/-- T521's same positive `k = 2` resident with its unchanged order-`P`
canonical weight, now carrying the lower endpoint moment. -/
def positiveTwoEndpointLowMomentResident
    (tauPrime : Real) (p P : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 <= firstCellT tauPrime N ∧
    weight tauPrime P N 2 omega = 1 ∧
    endpointLowMomentAt tauPrime p P N 2

theorem positiveTwoEndpointLowMomentResident_of_family
    {tauPrime : Real} {p P : Nat} (hTau : 0 < tauPrime)
    (hp : 1 <= p) (hpP : p <= P)
    (hresident :
      APrimeFirstCellFamilyLowMomentSameWeight.positiveTwoFamilyLowMomentResident
        tauPrime p P) :
    positiveTwoEndpointLowMomentResident tauPrime p P := by
  filter_upwards [hresident, eventually_gt_atTop 0] with N hr hN
  obtain ⟨omega, homega, hk, hvpos, hvle, hweight, hfamily⟩ := hr
  exact ⟨omega, homega, hk, hvpos, hvle, hweight,
    endpointLowMomentAt_of_family hTau hp hpP hN hk hfamily⟩

/-- One T521 parameter and literal sharp event supply every fixed pair
`1 <= p <= P`, `P >= 8000`, including the zero branch and the same
positive canonical-weight-one resident. -/
theorem exists_endpointLowMoment_sameWeight_with_resident :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall p P : Nat, 1 <= p -> p <= P -> 8000 <= P ->
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (Gauss.P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        (∀ᶠ N : Nat in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N).Nonempty) ∧
        actualEndpointLowMoment tauPrime p P ∧
        kZeroEndpointLowMoment tauPrime p P ∧
        positiveTwoEndpointLowMomentResident tauPrime p P := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellFamilyLowMomentSameWeight.exists_familyLowMoment_sameWeight_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro p P hp hpP hP
  obtain ⟨hmeas, hprob, hnonempty, hfamily, hzero, hresident⟩ :=
    hall p P hp hpP hP
  exact ⟨hmeas, hprob, hnonempty,
    actualEndpointLowMoment_of_family hTau hp hpP hfamily,
    kZeroEndpointLowMoment_of_family hTau hp hpP hzero,
    positiveTwoEndpointLowMomentResident_of_family hTau hp hpP hresident⟩

#print axioms endpointLowMomentAt_of_family
#print axioms actualEndpointLowMoment_of_family
#print axioms kZeroEndpointLowMoment_of_family
#print axioms positiveTwoEndpointLowMomentResident_of_family
#print axioms exists_endpointLowMoment_sameWeight_with_resident

end

end RBM.APrimeFirstCellEndpointLowMomentSameWeight
