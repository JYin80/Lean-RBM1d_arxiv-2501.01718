/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyHighMoment
import RBM1D.Gauss.APrimeFirstCellEndpointObservable

/-!
# T522: the actual first-cell endpoint bootstrap moment

T515 identifies the endpoint bootstrap observable with a deterministic
`R_v^{-4}` baseline plus T512's finite coordinate maximum.  Weighted
Minkowski under the same canonical weight then transfers T512's high-order
family estimate to the actual endpoint `jSnorm`.
-/

namespace RBM.APrimeFirstCellEndpointHighMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real := APrimeFirstCellFamilyHighMoment.delta
noncomputable abbrev alpha : Real := APrimeFirstCellFamilyHighMoment.alpha

/-- Coefficient-one weighted Minkowski against a nonnegative deterministic
baseline.  The assumptions `0 <= w <= 1` make the weighted root of the
baseline have ordinary `L^q` norm at most the baseline itself. -/
theorem momNormW_const_add_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {w Z : Omega -> Real} {p : Nat}
    (hp : 1 <= p) (hw0 : forall omega, 0 <= w omega)
    (hw1 : forall omega, w omega <= 1)
    (hZ0 : forall omega, 0 <= Z omega)
    (hZi : Integrable (fun omega => w omega * |Z omega| ^ (2 * p)) P)
    {b : Real} (hb : 0 <= b) :
    momNormW P w p (fun omega => b + Z omega) <= b + momNormW P w p Z := by
  let q : Nat := 2 * p
  let root : Omega -> Real := fun omega => w omega ^ ((1 : Real) / q)
  have hq : q ≠ 0 := by dsimp [q]; omega
  have hroot0 : forall omega, 0 <= root omega := fun omega =>
    Real.rpow_nonneg (hw0 omega) _
  have hroot1 : forall omega, root omega <= 1 := by
    intro omega
    dsimp [root]
    calc
      w omega ^ ((1 : Real) / q) <= (1 : Real) ^ ((1 : Real) / q) :=
        Real.rpow_le_rpow (hw0 omega) (hw1 omega) (by positivity)
      _ = 1 := by simp
  have hrootZi : Integrable (fun omega => (root omega * Z omega) ^ q) P := by
    apply hZi.congr
    filter_upwards [] with omega
    dsimp only [root]
    rw [mul_pow, abs_of_nonneg (hZ0 omega)]
    have hq0 : (q : Real) ≠ 0 := by exact_mod_cast hq
    have he : ((1 : Real) / (q : Real)) * (q : Real) = 1 := by
      field_simp
    have hrootPow : (w omega ^ ((1 : Real) / q)) ^ q = w omega := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul (hw0 omega), he, Real.rpow_one]
    change w omega * Z omega ^ (2 * p) =
      (w omega ^ ((1 : Real) / q)) ^ q * Z omega ^ q
    dsimp [q]
    rw [hrootPow]
  have hpoint : forall omega,
      |root omega * (b + Z omega)| <= 1 * (root omega * Z omega) + b := by
    intro omega
    rw [abs_mul, abs_of_nonneg (hroot0 omega),
      abs_of_nonneg (add_nonneg hb (hZ0 omega))]
    calc
      root omega * (b + Z omega) = root omega * Z omega + root omega * b := by ring
      _ <= root omega * Z omega + 1 * b :=
        add_le_add_right (mul_le_mul_of_nonneg_right (hroot1 omega) hb) _
      _ = 1 * (root omega * Z omega) + b := by ring
  have hbase := Gauss.momNorm_le_affine (P := P) hq
    (Y := fun omega => root omega * Z omega)
    (Z := fun omega => root omega * (b + Z omega))
    (fun omega => mul_nonneg (hroot0 omega) (hZ0 omega)) hrootZi
    (by norm_num : (0 : Real) <= 1) hb hpoint
  have hrootZ := APrimeBadSplit.momNorm_root_eq (P := P) hq
    (W := w) (Z := Z) hw0
  have hrootAdd := APrimeBadSplit.momNorm_root_eq (P := P) hq
    (W := w) (Z := fun omega => b + Z omega) hw0
  change momNorm P q (fun omega => root omega * (b + Z omega)) <=
    1 * momNorm P q (fun omega => root omega * Z omega) + b at hbase
  rw [hrootAdd, hrootZ] at hbase
  simpa [momNormW, q, Nat.cast_mul, add_comm] using hbase

/-- T512's absolute maximum is T515's endpoint coordinate maximum, because
every coordinate observable is a norm and hence nonnegative. -/
theorem familyMax_eq_endpointCoordMax (N k : Nat) (omega : Gauss.Ω d) :
    APrimeFirstCellFamilyHighMoment.familyMax N k omega =
      APrimeFirstCellEndpointCoord.endpointCoordMax d N (endpoint N k) omega := by
  simp [APrimeFirstCellFamilyHighMoment.familyMax,
    APrimeFirstCellEndpointCoord.endpointCoordMax, Y,
    APrimeDuhamelModel.flowY]

/-- T515's pointwise endpoint identity in T512's literal `familyMax`
vocabulary. -/
theorem jSnorm_endpoint_eq_familyMax {tauPrime : Real} (hTau : 0 < tauPrime)
    (N k : Nat)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (omega : Gauss.Ω d) :
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N (endpoint N k) omega =
      1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 +
        APrimeFirstCellFamilyHighMoment.familyMax N k omega := by
  have h := APrimeFirstCellEndpointObservable.jSnorm_endpoint_eq_sup_Y
    hTau N k hk omega
  simpa [APrimeFirstCellFamilyHighMoment.familyMax, Y,
    APrimeDuhamelModel.flowY] using h

/-- The requested actual endpoint high-order moment at one active endpoint. -/
def endpointMomentAt (tauPrime : Real) (p N k : Nat) : Prop :=
  momNormW (P d) (weight tauPrime p N k) p
      (fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
        N (endpoint N k) omega) <=
    1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 +
      (N : Real) ^ (delta / 2) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))

/-- Fixed-size coefficient-one assembly from T512 and T515 under precisely
the same canonical weight and moment order. -/
theorem endpointMomentAt_of_family {tauPrime : Real} (hTau : 0 < tauPrime)
    {p N k : Nat} (hp : 8000 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily : APrimeFirstCellFamilyHighMoment.familyMomentAt tauPrime p N k) :
    endpointMomentAt tauPrime p N k := by
  let w := weight tauPrime p N k
  let M := APrimeFirstCellFamilyHighMoment.familyMax N k
  let b := 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4
  have hp1 : 1 <= p := by omega
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
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 p N k
      (canonicalM tauPrime N) omega
  have hw1 : forall omega, w omega <= 1 := by
    intro omega
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 p N k
      (canonicalM tauPrime N) omega
  have hM0 : forall omega, 0 <= M omega := by
    intro omega
    dsimp [M, APrimeFirstCellFamilyHighMoment.familyMax]
    let a := Classical.choice
      (inferInstance : Nonempty (LoopArg (d.L N) 2))
    exact (abs_nonneg (Y N k a (endpoint N k) omega)).trans
      (Finset.le_sup' (fun a => |Y N k a (endpoint N k) omega|)
        (Finset.mem_univ a))
  have hintCoord : forall a : LoopArg (d.L N) 2,
      Integrable (fun omega => w omega *
        |Y N k a (endpoint N k) omega| ^ (2 * p)) (P d) := by
    intro a
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
      (δ := delta) hTau hp1 hN hk a).2.hYi
  have hMi : Integrable (fun omega => w omega * |M omega| ^ (2 * p)) (P d) := by
    exact APrimeFirstCellFamilyHighMoment.integrable_weighted_finsetMax_pow
      (P d) w (fun a => Y N k a (endpoint N k)) (2 * p) hw0 hintCoord
  have htriangle := momNormW_const_add_le hp1 hw0 hw1 hM0 hMi hb
  have hid : (fun omega => Step2Moment.jSnorm (sample d) 0 60
      (fun _ => 0) N (endpoint N k) omega) = fun omega => b + M omega := by
    funext omega
    exact jSnorm_endpoint_eq_familyMax hTau N k hk omega
  unfold endpointMomentAt
  rw [hid]
  exact htriangle.trans (by
    simpa only [add_comm] using add_le_add_left hfamily b)

/-- Positive active indices, with the high order fixed before the uniform
eventual size threshold. -/
def actualEndpointHighMoment (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N -> endpointMomentAt tauPrime p N k

theorem actualEndpointHighMoment_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) (p : Nat) (hp : 8000 <= p)
    (hfamily : APrimeFirstCellFamilyHighMoment.actualFamilyHighMoment tauPrime p) :
    actualEndpointHighMoment tauPrime p := by
  filter_upwards [hfamily, eventually_gt_atTop 0] with N hfamilyN hN
  intro k hk1 hk
  exact endpointMomentAt_of_family hTau hp hN hk (hfamilyN k hk1 hk)

/-- The boundary index is retained separately, including its literal
`R_0 = 1` simplification. -/
def kZeroEndpointHighMoment (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ endpointMomentAt tauPrime p N 0 ∧
      momNormW (P d) (weight tauPrime p N 0) p
        (fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
          N (endpoint N 0) omega) <= 1 + (N : Real) ^ (delta / 2)

theorem eventually_kZeroEndpointHighMoment {tauPrime : Real}
    (hTau : 0 < tauPrime) (p : Nat) (hp : 8000 <= p) :
    kZeroEndpointHighMoment tauPrime p := by
  filter_upwards [APrimeFirstCellFamilyHighMoment.eventually_kZeroFamilyHighMoment
    hTau p hp, eventually_gt_atTop 0] with N hzero hN
  obtain ⟨hv, hfamily, _hsimple⟩ := hzero
  have hendpoint := endpointMomentAt_of_family hTau hp hN (Nat.zero_le _) hfamily
  have hR : Step2Moment.ratR 0 (fun _ => 0) N 0 = 1 := by
    unfold Step2Moment.ratR
    exact div_self (Step2.etaT_pos' (E := 0) (by norm_num) (by norm_num)).ne'
  refine ⟨hv, hendpoint, ?_⟩
  simpa [endpointMomentAt, hv, hR, etaT, mE_zero] using hendpoint

/-- T512's same positive `k = 2` resident, now carrying the endpoint
bootstrap moment under its unchanged canonical weight. -/
def positiveTwoEndpointHighMomentResident (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 <= firstCellT tauPrime N ∧
    weight tauPrime p N 2 omega = 1 ∧ endpointMomentAt tauPrime p N 2

theorem positiveTwoEndpointHighMomentResident_of_family
    {tauPrime : Real} {p : Nat} (hTau : 0 < tauPrime) (hp : 8000 <= p)
    (hresident :
      APrimeFirstCellFamilyHighMoment.positiveTwoFamilyHighMomentResident
        tauPrime p) :
    positiveTwoEndpointHighMomentResident tauPrime p := by
  filter_upwards [hresident, eventually_gt_atTop 0] with N hr hN
  obtain ⟨omega, homega, hk, hvpos, hvle, hweight, hfamily⟩ := hr
  exact ⟨omega, homega, hk, hvpos, hvle, hweight,
    endpointMomentAt_of_family hTau hp hN hk hfamily⟩

/-- One T512 parameter and literal sharp event supply the actual endpoint
moment, its zero branch, and a nondegenerate positive weight-one resident. -/
theorem exists_endpointHighMoment_with_resident :
    exists tauPrime : Real, 0 < tauPrime ∧ forall p : Nat, 8000 <= p ->
      (forall N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N)) ∧
      HighProb (P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha) ∧
      (∀ᶠ N : Nat in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N).Nonempty) ∧
      actualEndpointHighMoment tauPrime p ∧
      kZeroEndpointHighMoment tauPrime p ∧
      positiveTwoEndpointHighMomentResident tauPrime p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellFamilyHighMoment.exists_familyHighMoment_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro p hp
  obtain ⟨hmeas, hprob, hnonempty, hfamily, _hzero, hresident⟩ := hall p hp
  exact ⟨hmeas, hprob, hnonempty,
    actualEndpointHighMoment_of_family hTau p hp hfamily,
    eventually_kZeroEndpointHighMoment hTau p hp,
    positiveTwoEndpointHighMomentResident_of_family hTau hp hresident⟩

#print axioms momNormW_const_add_le
#print axioms familyMax_eq_endpointCoordMax
#print axioms jSnorm_endpoint_eq_familyMax
#print axioms endpointMomentAt_of_family
#print axioms actualEndpointHighMoment_of_family
#print axioms eventually_kZeroEndpointHighMoment
#print axioms positiveTwoEndpointHighMomentResident_of_family
#print axioms exists_endpointHighMoment_with_resident

end

end RBM.APrimeFirstCellEndpointHighMoment
