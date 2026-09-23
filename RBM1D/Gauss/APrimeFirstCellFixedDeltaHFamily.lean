/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyWidenedSharpMoment
import RBM1D.Gauss.APrimeFirstCellEndpointHighMoment
import RBM1D.Gauss.APrimeFirstCellEndpointWidenedMoment

/-!
# T535: fixed-delta first-cell endpoint hfamily integral

At the literal `delta = 1 / 2000`, the sharp widened family norm from T533
and the exact endpoint identity give a coefficient-one endpoint norm bound.
The corresponding weighted integral has exactly the hfamily exponent
`(delta / 2) * p`.  The degenerate order `p = 0` is treated directly from
`0 <= targetWeight <= 1` on the probability space.
-/

namespace RBM.APrimeFirstCellFixedDeltaHFamily

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel MomentDuhamelCut APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real :=
  APrimeFirstCellFamilyWidenedSharpMoment.delta
noncomputable abbrev alpha : Real :=
  APrimeFirstCellFamilyWidenedSharpMoment.alpha

private noncomputable abbrev endpointJ (N k : Nat) : Gauss.Ω d -> Real :=
  fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
    N (endpoint N k) omega

/-- The literal target weight is measurable. -/
theorem targetWeight_aestronglyMeasurable (tauPrime : Real) (p N k : Nat) :
    AEStronglyMeasurable
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

theorem targetWeight_nonneg (tauPrime : Real) (p N k : Nat)
    (omega : Gauss.Ω d) :
    0 <= APrimeFirstCellCrossOrderWeight.targetWeight
      tauPrime p N k omega := by
  exact APrimeWeight.widenedW_nonneg
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega

theorem targetWeight_le_one (tauPrime : Real) (p N k : Nat)
    (omega : Gauss.Ω d) :
    APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega <= 1 := by
  exact APrimeWeight.widenedW_le_one
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega

/-- Every active first-cell endpoint has `1 <= R_v <= 2`. -/
theorem endpoint_ratR_bounds {tauPrime : Real} (hTau : 0 < tauPrime)
    (N k : Nat)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    1 <= Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ∧
      Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) <= 2 := by
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hvhalf : endpoint N k <= 1 / 2 := hv.2.trans ht.2
  have hv1 : endpoint N k < 1 := hvhalf.trans_lt (by norm_num)
  have hR1 := APrimeFirstCellEndpointCoord.one_le_endpoint_ratR
    N hv.1 hv1
  have heta : (1 / 2 : Real) <= etaT 0 (endpoint N k) := by
    norm_num [etaT, mE_zero]
    linarith
  have heta0 : 0 < etaT 0 (endpoint N k) :=
    (by norm_num : (0 : Real) < 1 / 2).trans_le heta
  refine ⟨hR1, ?_⟩
  unfold Step2Moment.ratR
  rw [show etaT 0 0 = 1 by norm_num [etaT, mE_zero]]
  exact (div_le_iff₀ heta0).2 (by linarith)

/-- Honest integrability of the untruncated endpoint weighted power.  It is
deduced from T528's target-weight family integrability and the exact endpoint
identity, rather than from the total-integral convention. -/
theorem integrable_targetWeight_endpoint_pow {tauPrime : Real}
    (hTau : 0 < tauPrime) {p N k : Nat}
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega =>
      APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega *
        |endpointJ N k omega| ^ (2 * p)) (Gauss.P d) := by
  let w := APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k
  let M := familyMax N k
  let b := 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4
  let q := 2 * p
  have hwmeas : AEStronglyMeasurable w (Gauss.P d) :=
    targetWeight_aestronglyMeasurable tauPrime p N k
  have hw0 : forall omega, 0 <= w omega :=
    targetWeight_nonneg tauPrime p N k
  have hw1 : forall omega, w omega <= 1 :=
    targetWeight_le_one tauPrime p N k
  have hwint : Integrable w (Gauss.P d) := by
    apply Integrable.of_bound hwmeas 1
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 omega)]
      exact hw1 omega
  have hMint : Integrable (fun omega => w omega * |M omega| ^ q)
      (Gauss.P d) := by
    exact APrimeFirstCellEndpointWidenedMoment.integrable_targetWeight_familyMax_pow
      hTau hk
  have hb0 : 0 <= b := by dsimp [b]; positivity
  have hconst : Integrable (fun omega => w omega * |b| ^ q)
      (Gauss.P d) := by
    simpa only [mul_comm] using hwint.const_mul (|b| ^ q)
  have hmajor : Integrable (fun omega =>
      2 ^ (q - 1) *
        (w omega * |b| ^ q + w omega * |M omega| ^ q)) (Gauss.P d) :=
    (hconst.add hMint).const_mul _
  have hJmeas : Measurable (endpointJ N k) :=
    APrimeSlotFields.measurable_jSnorm
      (sample d) 0 60 (fun _ => 0) N (endpoint N k)
  apply hmajor.mono' (hwmeas.mul
    ((continuous_abs.measurable.comp hJmeas).pow_const q).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun omega => by
    have hM0 : 0 <= M omega := by
      dsimp [M, familyMax]
      let a := Classical.choice
        (inferInstance : Nonempty (LoopArg (d.L N) 2))
      exact (abs_nonneg (Y N k a (endpoint N k) omega)).trans
        (Finset.le_sup' (fun a => |Y N k a (endpoint N k) omega|)
          (Finset.mem_univ a))
    have hid := APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
      hTau N k hk omega
    change ‖w omega * |endpointJ N k omega| ^ q‖ <=
      2 ^ (q - 1) *
        (w omega * |b| ^ q + w omega * |M omega| ^ q)
    rw [show endpointJ N k omega = b + M omega by exact hid]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hw0 omega) (by positivity)),
      abs_of_nonneg (add_nonneg hb0 hM0), abs_of_nonneg hb0,
      abs_of_nonneg hM0]
    have hadd := add_pow_le hb0 hM0 q
    calc
      w omega * (b + M omega) ^ q
          <= w omega *
            (2 ^ (q - 1) * (b ^ q + M omega ^ q)) :=
        mul_le_mul_of_nonneg_left hadd (hw0 omega)
      _ = 2 ^ (q - 1) *
          (w omega * b ^ q + w omega * M omega ^ q) := by ring

/-- The widened endpoint norm is at most `1 + N^(delta/4)`. -/
theorem endpointMomNorm_le_one_add {tauPrime : Real}
    (hTau : 0 < tauPrime) {p N k : Nat} (hp : 1 <= p)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily :
      APrimeFirstCellFamilyWidenedSharpMoment.familyWidenedSharpMomentAt
        tauPrime p N k) :
    momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k)
      p (endpointJ N k) <= 1 + (N : Real) ^ (delta / 4) := by
  let w := APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k
  let M := familyMax N k
  let b := 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4
  have hR1 := (endpoint_ratR_bounds hTau N k hk).1
  have hR4 : 1 <= Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 :=
    one_le_pow₀ hR1
  have hR4pos : 0 < Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 :=
    (by norm_num : (0 : Real) < 1).trans_le hR4
  have hb0 : 0 <= b := by dsimp [b]; positivity
  have hb1 : b <= 1 := by
    dsimp [b]
    exact (div_le_one hR4pos).2 hR4
  have hRneg :
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real)) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
  have hM0 : forall omega, 0 <= M omega := by
    intro omega
    dsimp [M, familyMax]
    let a := Classical.choice
      (inferInstance : Nonempty (LoopArg (d.L N) 2))
    exact (abs_nonneg (Y N k a (endpoint N k) omega)).trans
      (Finset.le_sup' (fun a => |Y N k a (endpoint N k) omega|)
        (Finset.mem_univ a))
  have hw0 : forall omega, 0 <= w omega :=
    targetWeight_nonneg tauPrime p N k
  have hw1 : forall omega, w omega <= 1 :=
    targetWeight_le_one tauPrime p N k
  have hMint : Integrable (fun omega => w omega * |M omega| ^ (2 * p))
      (Gauss.P d) := by
    exact APrimeFirstCellEndpointWidenedMoment.integrable_targetWeight_familyMax_pow
      hTau hk
  have htriangle :=
    APrimeFirstCellEndpointHighMoment.momNormW_const_add_le
      hp hw0 hw1 hM0 hMint hb0
  have hid : endpointJ N k = fun omega => b + M omega := by
    funext omega
    exact APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
      hTau N k hk omega
  have hfamily' : momNormW (Gauss.P d) w p M <=
      (N : Real) ^ (delta / 4) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real)) := hfamily
  rw [hid]
  calc
    momNormW (Gauss.P d) w p (fun omega => b + M omega)
        <= b + momNormW (Gauss.P d) w p M := htriangle
    _ <= 1 + (N : Real) ^ (delta / 4) := by
      apply add_le_add hb1
      exact hfamily'.trans
        (mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg N) _) hRneg)

/-- For `N >= 1`, the endpoint norm is at most `2 N^(delta/4)`. -/
theorem endpointMomNorm_le_two_mul {tauPrime : Real}
    (hTau : 0 < tauPrime) {p N k : Nat} (hp : 1 <= p) (hN : 1 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily :
      APrimeFirstCellFamilyWidenedSharpMoment.familyWidenedSharpMomentAt
        tauPrime p N k) :
    momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k)
      p (endpointJ N k) <= 2 * (N : Real) ^ (delta / 4) := by
  have hNreal : (1 : Real) <= N := by exact_mod_cast hN
  have hdelta : 0 <= delta / 4 := by
    norm_num [delta, APrimeFirstCellFamilyWidenedSharpMoment.delta,
      APrimeFirstCellQuantMomentSharp.delta, APrimeFirstCellQuantMoment.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have hone : 1 <= (N : Real) ^ (delta / 4) :=
    Real.one_le_rpow hNreal hdelta
  linarith [endpointMomNorm_le_one_add hTau hp hk hfamily]

/-- The literal fixed-delta hfamily-shaped endpoint integral. -/
def fixedDeltaIntegralAt
    (tauPrime : Real) (p N k : Nat) (C : Real) : Prop :=
  ∫ omega,
      APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega *
        |cutTrunc ((N : Real) ^ (2 * delta)) (endpointJ N k omega)| ^
          (2 * p) ∂(Gauss.P d) <=
    C * (N : Real) ^ (delta / 2 * (p : Real))

/-- Positive moment orders have constant `2^(2p)` and the exact exponent
`(delta/2) p`. -/
theorem fixedDeltaIntegralAt_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p N k : Nat} (hp : 1 <= p) (hN : 1 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily :
      APrimeFirstCellFamilyWidenedSharpMoment.familyWidenedSharpMomentAt
        tauPrime p N k) :
    fixedDeltaIntegralAt tauPrime p N k (2 ^ (2 * p)) := by
  have hJint := integrable_targetWeight_endpoint_pow hTau (p := p) hk
  have hnorm := endpointMomNorm_le_two_mul hTau hp hN hk hfamily
  have hraw := APrimeOneStep.integral_cutTrunc_le_of_momNormW_le
    (P := Gauss.P d)
    (W := APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k)
    (Y := endpointJ N k) (Jf := endpointJ N k)
    (θ := (N : Real) ^ (2 * delta))
    (targetWeight_nonneg tauPrime p N k) hp hJint (fun omega => by
      have hJ0 := APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
        d 0 60 (fun _ => 0) N (endpoint N k) omega
      rw [abs_of_nonneg (cutTrunc_nonneg hJ0), abs_of_nonneg hJ0]
      exact cutTrunc_le_self hJ0) hnorm
  unfold fixedDeltaIntegralAt
  refine hraw.trans (le_of_eq ?_)
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  rw [mul_pow, ← Real.rpow_natCast ((N : Real) ^ (delta / 4)) (2 * p),
    ← Real.rpow_mul hNpos.le]
  congr 1
  push_cast
  ring_nf

/-- At `p = 0`, the integral is bounded by one directly from the weight. -/
theorem fixedDeltaIntegralAt_zero (tauPrime : Real) {N k : Nat} :
    fixedDeltaIntegralAt tauPrime 0 N k 1 := by
  have hzero := Gauss.integral_weight_pow_zero_le
    (P := Gauss.P d)
    (W := APrimeFirstCellCrossOrderWeight.targetWeight tauPrime 0 N k)
    (J := endpointJ N k) (θ := (N : Real) ^ (2 * delta))
    (targetWeight_nonneg tauPrime 0 N k)
    (targetWeight_le_one tauPrime 0 N k)
    (targetWeight_aestronglyMeasurable tauPrime 0 N k)
  unfold fixedDeltaIntegralAt
  simpa using hzero

def actualFixedDeltaHFamily
    (tauPrime : Real) (p : Nat) (C : Real) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    fixedDeltaIntegralAt tauPrime p N k C

def kZeroFixedDeltaHFamily
    (tauPrime : Real) (p : Nat) (C : Real) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ fixedDeltaIntegralAt tauPrime p N 0 C

theorem actualFixedDeltaHFamily_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p : Nat} (hp : 1 <= p)
    (hfamily :
      APrimeFirstCellFamilyWidenedSharpMoment.actualFamilyWidenedSharpMoment
        tauPrime p) :
    actualFixedDeltaHFamily tauPrime p (2 ^ (2 * p)) := by
  filter_upwards [hfamily, eventually_ge_atTop 1] with N hfamilyN hN
  intro k hk1 hk
  exact fixedDeltaIntegralAt_of_family hTau hp hN hk
    (hfamilyN k hk1 hk)

theorem kZeroFixedDeltaHFamily_of_family {tauPrime : Real}
    (hTau : 0 < tauPrime) {p : Nat} (hp : 1 <= p)
    (hzero :
      APrimeFirstCellFamilyWidenedSharpMoment.kZeroFamilyWidenedSharpMoment
        tauPrime p) :
    kZeroFixedDeltaHFamily tauPrime p (2 ^ (2 * p)) := by
  filter_upwards [hzero, eventually_ge_atTop 1] with N hz hN
  exact ⟨hz.1, fixedDeltaIntegralAt_of_family hTau hp hN
    (Nat.zero_le _) hz.2.1⟩

theorem actualFixedDeltaHFamily_zero (tauPrime : Real) :
    actualFixedDeltaHFamily tauPrime 0 1 := by
  filter_upwards [] with N
  intro k _hk1 _hk
  exact fixedDeltaIntegralAt_zero tauPrime

theorem kZeroFixedDeltaHFamily_zero (tauPrime : Real) :
    kZeroFixedDeltaHFamily tauPrime 0 1 := by
  filter_upwards [] with N
  exact ⟨by simp [endpoint, cutNetPt_zero],
    fixedDeltaIntegralAt_zero tauPrime⟩

/-- A positive same-event target-weight-one resident carrying the integral. -/
def positiveTwoFixedDeltaHFamilyResident
    (tauPrime : Real) (p : Nat) (C : Real) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 <= firstCellT tauPrime N ∧
    APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 2 omega = 1 ∧
    fixedDeltaIntegralAt tauPrime p N 2 C

theorem positiveTwoFixedDeltaHFamilyResident_of_base
    {tauPrime : Real} {p : Nat} {C : Real}
    (hbase :
      APrimeFirstCellFamilyWidenedSharpMoment.positiveTwoFamilyWidenedSharpMomentResident
        tauPrime 1 40000)
    (hintegral : actualFixedDeltaHFamily tauPrime p C) :
    positiveTwoFixedDeltaHFamilyResident tauPrime p C := by
  filter_upwards [hbase, hintegral,
    APrimeFirstCellCrossOrderWeight.eventually_targetWeight_two_one_on_sharpCommonEvent
      tauPrime] with N hr hi htarget
  obtain ⟨omega, homega, hk, hvpos, hvle, _htargetOne, _hweight,
    _hfamily⟩ := hr
  have homega' : omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime APrimeFirstCellQuantMoment.delta
          APrimeFirstCellQuantMoment.alpha N := by
    simpa only [delta, alpha,
      APrimeFirstCellFamilyWidenedSharpMoment.delta,
      APrimeFirstCellFamilyWidenedSharpMoment.alpha,
      APrimeFirstCellQuantMomentSharp.delta,
      APrimeFirstCellQuantMomentSharp.alpha] using homega
  exact ⟨omega, homega, hk, hvpos, hvle,
    htarget omega homega' p, hi 2 (by norm_num) hk⟩

/-- One parameter and one literal sharp event supply the complete fixed-delta
first-cell hfamily integral for every fixed moment order. -/
theorem exists_fixedDeltaHFamily_with_resident :
    exists tauPrime : Real, 0 < tauPrime ∧
      (forall N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha) ∧
      (∀ᶠ N : Nat in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N).Nonempty) ∧
      forall p : Nat, exists C : Real, 0 < C ∧
        actualFixedDeltaHFamily tauPrime p C ∧
        kZeroFixedDeltaHFamily tauPrime p C ∧
        positiveTwoFixedDeltaHFamilyResident tauPrime p C := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellFamilyWidenedSharpMoment.exists_familyWidenedSharpMoment_with_resident
  obtain ⟨_hcompareBase, hmeas, hprob, hnonempty, _hfamilyBase,
      _hzeroBase, hresidentBase⟩ :=
    hall 1 40000 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨tauPrime, hTau, hmeas, hprob, hnonempty, ?_⟩
  intro p
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨1, by norm_num, actualFixedDeltaHFamily_zero tauPrime,
      kZeroFixedDeltaHFamily_zero tauPrime, ?_⟩
    exact positiveTwoFixedDeltaHFamilyResident_of_base
      hresidentBase (actualFixedDeltaHFamily_zero tauPrime)
  · let P := max p 40000
    have hpP : p <= P := by simp [P]
    have hP : 40000 <= P := by simp [P]
    obtain ⟨_hcompare, _hmeas, _hprob, _hnonempty, hfamily, hzero,
        _hresident⟩ := hall p P hp hpP hP
    have hactual := actualFixedDeltaHFamily_of_family hTau hp hfamily
    refine ⟨2 ^ (2 * p), by positivity, hactual,
      kZeroFixedDeltaHFamily_of_family hTau hp hzero, ?_⟩
    exact positiveTwoFixedDeltaHFamilyResident_of_base hresidentBase hactual

#print axioms targetWeight_aestronglyMeasurable
#print axioms targetWeight_nonneg
#print axioms targetWeight_le_one
#print axioms endpoint_ratR_bounds
#print axioms integrable_targetWeight_endpoint_pow
#print axioms endpointMomNorm_le_one_add
#print axioms endpointMomNorm_le_two_mul
#print axioms fixedDeltaIntegralAt_of_family
#print axioms fixedDeltaIntegralAt_zero
#print axioms actualFixedDeltaHFamily_of_family
#print axioms kZeroFixedDeltaHFamily_of_family
#print axioms actualFixedDeltaHFamily_zero
#print axioms kZeroFixedDeltaHFamily_zero
#print axioms positiveTwoFixedDeltaHFamilyResident_of_base
#print axioms exists_fixedDeltaHFamily_with_resident

end

end RBM.APrimeFirstCellFixedDeltaHFamily
