/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaDriftBadPayment
import RBM1D.Gauss.APrimeFirstCellScaleFloors

/-!
# T541: absorb the actual first-cell drift coefficient

T458's scale floor absorbs the literal T442 coefficient at every moving
first-cell endpoint.  The result is then composed with T538's variable-`delta`
paid norm estimate, without changing its event, weight, endpoint, or
quantifier order.
-/

namespace RBM.APrimeFirstCellDeltaDriftCoefficientAbsorbed

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The paper-scale constant after the near row and far row are absorbed. -/
noncomputable def absorbedRate (alpha : Real) (N : Nat) (v : Real) : Real :=
  APrimeFirstCellDriftCoefficient.coefficientConstant * (Real.sqrt 2 + 1) *
    (N : Real) ^ (2 * alpha) *
      APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real))

theorem absorbedRate_eq_paperRate (alpha : Real) (N : Nat) (v : Real) :
    absorbedRate alpha N v =
    APrimeFirstCellDriftCoefficient.coefficientConstant *
        (Real.sqrt 2 + 1) * (N : Real) ^ (2 * alpha) *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real)) := rfl

private theorem xRate_bounds_of_mem {tauPrime : Real} {N k : Nat} {r : Real}
    (hpack : APrimeFirstCellScaleFloors.ScalePackage tauPrime N k)
    (hr : r ∈ Icc (0 : Real)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    1 <= APrimeFirstCellLoopCap.xRate r ∧
      APrimeFirstCellLoopCap.xRate r <= 2 := by
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hr1 : r < 1 :=
    hr.2.trans hpack.time_le_half |>.trans_lt (by norm_num)
  have hetaR : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hetav : 0 < etaT 0 v := Step2.etaT_pos' (by norm_num)
    (hpack.time_le_half.trans_lt (by norm_num))
  have hrv : APrimeFirstCellLoopCap.xRate r <=
      APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    rw [APrimeFirstCellDriftAbsorbed.etaT_zero_eq_one, one_div, one_div]
    exact inv_anti₀ hetav (etaT_le_of_le (by norm_num) hr.2)
  have hrone : 1 <= APrimeFirstCellLoopCap.xRate r := by
    simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hr.1 hr1)
  exact ⟨hrone, hrv.trans hpack.ratio_le_two⟩

private theorem far_row_le_power {N : Nat} {A x e a b : Real}
    (hN : 1 <= N)
    (hA : (N : Real) ^ (1 / 2 : Real) <= A)
    (hx0 : 0 <= x) (hx2 : x <= 2) (ha : 0 <= a) (hb : 0 <= b) :
    (N : Real) ^ e * A ^ (-a) * x ^ b <=
      (2 : Real) ^ b * (N : Real) ^ (e - a / 2) := by
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNr
  have hhalfpos : 0 < (N : Real) ^ (1 / 2 : Real) :=
    Real.rpow_pos_of_pos hNpos _
  have hApow : A ^ (-a) <= ((N : Real) ^ (1 / 2 : Real)) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hhalfpos hA (neg_nonpos.mpr ha)
  have hxpow : x ^ b <= (2 : Real) ^ b :=
    Real.rpow_le_rpow hx0 hx2 hb
  calc
    (N : Real) ^ e * A ^ (-a) * x ^ b <=
        (N : Real) ^ e * ((N : Real) ^ (1 / 2 : Real)) ^ (-a) *
          (2 : Real) ^ b := by gcongr
    _ = (2 : Real) ^ b * (N : Real) ^ (e - a / 2) := by
      calc
        (N : Real) ^ e * ((N : Real) ^ (1 / 2 : Real)) ^ (-a) *
            (2 : Real) ^ b =
            (2 : Real) ^ b * ((N : Real) ^ e *
              ((N : Real) ^ (1 / 2 : Real)) ^ (-a)) := by ring
        _ = _ := by
          rw [← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
          congr 1
          ring_nf

/-- The entire permitted `delta` range leaves a strict exponent margin. -/
theorem far_decay_gap_pos (delta : Real) (_hdelta : 0 < delta)
    (hdelta100 : delta <= 1 / 100) :
    0 < (1 / 2 : Real) - 4 * delta := by
  linarith

theorem eventually_far_decay (delta : Real) (hdelta : 0 < delta)
    (hdelta100 : delta <= 1 / 100) :
    ∀ᶠ N : Nat in atTop,
      (2 : Real) ^ (7 : Real) *
        (N : Real) ^ (4 * delta - 1 / 2) <= 1 := by
  have hgap := far_decay_gap_pos delta hdelta hdelta100
  filter_upwards [eventually_le_rpow ((2 : Real) ^ (7 : Real)) hgap,
    eventually_ge_atTop 1] with N hlarge hN
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNr
  have hp : 0 < (N : Real) ^ ((1 / 2 : Real) -
      4 * delta) :=
    Real.rpow_pos_of_pos hNpos _
  have hexp : 4 * delta - 1 / 2 =
      -((1 / 2 : Real) - 4 * delta) := by ring
  rw [hexp, Real.rpow_neg hNpos.le]
  calc
    (2 : Real) ^ (7 : Real) *
        ((N : Real) ^ ((1 / 2 : Real) -
          4 * delta))⁻¹ <=
      (N : Real) ^ ((1 / 2 : Real) -
          4 * delta) *
        ((N : Real) ^ ((1 / 2 : Real) -
          4 * delta))⁻¹ :=
      mul_le_mul_of_nonneg_right hlarge (inv_nonneg.mpr hp.le)
    _ = 1 := mul_inv_cancel₀ hp.ne'

private theorem coefficient_rows {tauPrime delta alpha : Real}
    {N k : Nat} {r : Real}
    (hN : 1 <= N)
    (hpack : APrimeFirstCellScaleFloors.ScalePackage tauPrime N k)
    (hr : r ∈ Icc (0 : Real)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k))
    (hdecay : (2 : Real) ^ (7 : Real) *
      (N : Real) ^ (4 * delta - 1 / 2) <= 1) :
    APrimeFirstCellDriftCoefficient.endpointCoefficient
        delta (2 * alpha) N
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r <=
      absorbedRate alpha N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) := by
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  let x := APrimeFirstCellLoopCap.xRate r
  let A := APrimeFirstCellLoopCap.endpointScale N v
  obtain ⟨hx1, hx2⟩ := xRate_bounds_of_mem hpack hr
  have hx0 : 0 <= x := zero_le_one.trans hx1
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hnear : x ^ (1 / 2 : Real) <= Real.sqrt 2 := by
    simpa only [Real.sqrt_eq_rpow] using
      (Real.rpow_le_rpow hx0 hx2 (by norm_num : (0 : Real) <= 1 / 2))
  have hfarPower : (N : Real) ^
        (4 * delta) *
        A ^ (-(1 : Real)) * x ^ (7 : Real) <=
      (2 : Real) ^ (7 : Real) *
        (N : Real) ^
          (4 * delta - 1 / 2) :=
    far_row_le_power hN hpack.n_half_le_scale hx0 hx2 (by norm_num) (by norm_num)
  have hfar : (N : Real) ^
        (4 * delta) * A⁻¹ * x ^ 7 <= 1 := by
    rw [← Real.rpow_neg_one]
    rw [show x ^ 7 = x ^ (7 : Real) by norm_num [Real.rpow_natCast]]
    exact hfarPower.trans hdecay
  have hxnear : x * x ^ (-(1 : Real) / 2) = x ^ (1 / 2 : Real) := by
    calc
      x * x ^ (-(1 : Real) / 2) =
          x ^ (1 : Real) * x ^ (-(1 : Real) / 2) := by rw [Real.rpow_one]
      _ = x ^ ((1 : Real) + (-(1 : Real) / 2)) :=
        (Real.rpow_add hxpos _ _).symm
      _ = x ^ (1 / 2 : Real) := by congr 1; ring
  have hxseven : x * x ^ (6 : Nat) = x ^ (7 : Nat) := by ring
  have hrows : x *
        (x ^ (-(1 : Real) / 2) +
          (N : Real) ^ (4 * delta) *
            A⁻¹ * x ^ 6) <= Real.sqrt 2 + 1 := by
    calc
      x * (x ^ (-(1 : Real) / 2) +
          (N : Real) ^ (4 * delta) *
            A⁻¹ * x ^ 6) =
        x ^ (1 / 2 : Real) +
          (N : Real) ^ (4 * delta) *
            A⁻¹ * x ^ 7 := by rw [mul_add, hxnear]; rw [← hxseven]; ring
      _ <= Real.sqrt 2 + 1 := add_le_add hnear hfar
  have hfac : 0 <= APrimeFirstCellDriftCoefficient.coefficientConstant *
      (N : Real) ^ (2 * alpha) *
        APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real)) := by
    exact mul_nonneg
      (mul_nonneg APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
        (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (zero_le_one.trans hpack.one_le_ratio) _)
  unfold APrimeFirstCellDriftCoefficient.endpointCoefficient
  rw [← APrimeFirstCellDriftAbsorbed.xRate_eq_inv_etaT r]
  change APrimeFirstCellDriftCoefficient.coefficientConstant *
      (N : Real) ^ (2 * alpha) * x *
        APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real)) *
          (x ^ (-(1 : Real) / 2) +
            (N : Real) ^ (4 * delta) *
              A⁻¹ * x ^ 6) <= _
  calc
    _ = (APrimeFirstCellDriftCoefficient.coefficientConstant *
        (N : Real) ^ (2 * alpha) *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real))) *
        (x * (x ^ (-(1 : Real) / 2) +
          (N : Real) ^ (4 * delta) *
            A⁻¹ * x ^ 6)) := by ring
    _ <= (APrimeFirstCellDriftCoefficient.coefficientConstant *
        (N : Real) ^ (2 * alpha) *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real))) *
            (Real.sqrt 2 + 1) :=
      mul_le_mul_of_nonneg_left hrows hfac
    _ = absorbedRate alpha N v := by unfold absorbedRate; ring

/-- T458 absorbs the literal T442 coefficient uniformly over all actual
moving first-cell endpoints and all real times in their prefixes. -/
theorem eventually_endpointCoefficient_le_absorbedRate
    {tauPrime delta : Real} (htau : 0 < tauPrime)
    (hdelta : 0 < delta) (hdelta100 : delta <= 1 / 100) (alpha : Real) :
    ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      ∀ r ∈ Icc (0 : Real) v,
        APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N v r <=
          absorbedRate alpha N v := by
  filter_upwards [APrimeFirstCellScaleFloors.eventually_scalePackage htau,
    eventually_far_decay delta hdelta hdelta100,
    eventually_ge_atTop 1] with N hpack hdecay hN
  intro k hk
  dsimp only
  intro r hr
  have hp := coefficient_rows (alpha := alpha) hN (hpack k hk) hr (hdecay := hdecay)
  simpa only [APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint] using hp

/-- The deterministic T442 coefficient is continuous on a first-cell
interval.  This statement concerns only the scalar envelope, not the random
moment norm. -/
theorem continuousOn_endpointCoefficient {delta nu : Real} {N : Nat} {v : Real}
    (hvhalf : v <= 1 / 2) :
    ContinuousOn
      (fun r => APrimeFirstCellDriftCoefficient.endpointCoefficient
        delta nu N v r) (Icc (0 : Real) v) := by
  have hetaCont : Continuous fun r : Real => etaT 0 r := by
    unfold etaT
    fun_prop
  have hetaNe : ∀ r ∈ Icc (0 : Real) v, etaT 0 r ≠ 0 := by
    intro r hr
    exact (Step2.etaT_pos' (by norm_num)
      (hr.2.trans_lt (hvhalf.trans_lt (by norm_num)))).ne'
  have hxCont : ContinuousOn (fun r => APrimeFirstCellLoopCap.xRate r)
      (Icc (0 : Real) v) := by
    unfold APrimeFirstCellLoopCap.xRate
    exact continuousOn_const.div hetaCont.continuousOn hetaNe
  have hxPos : ∀ r ∈ Icc (0 : Real) v,
      0 < APrimeFirstCellLoopCap.xRate r := by
    intro r hr
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num)
        (hr.2.trans_lt (hvhalf.trans_lt (by norm_num))))
  have hxPow (q : Real) : ContinuousOn
      (fun r => APrimeFirstCellLoopCap.xRate r ^ q) (Icc (0 : Real) v) :=
    hxCont.rpow_const (fun r hr => Or.inl (hxPos r hr).ne')
  have hetaInv : ContinuousOn (fun r => (etaT 0 r)⁻¹)
      (Icc (0 : Real) v) := hetaCont.continuousOn.inv₀ hetaNe
  have hprefix : ContinuousOn
      (fun r => APrimeFirstCellDriftCoefficient.coefficientConstant *
        (N : Real) ^ nu * (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real)))
      (Icc (0 : Real) v) :=
    ((continuousOn_const.mul continuousOn_const).mul hetaInv).mul continuousOn_const
  have hfar : ContinuousOn
      (fun r =>
        ((N : Real) ^ (4 * delta) *
          (APrimeFirstCellLoopCap.endpointScale N v)⁻¹) *
            APrimeFirstCellLoopCap.xRate r ^ (6 : Nat))
      (Icc (0 : Real) v) := continuousOn_const.mul (hxCont.pow 6)
  unfold APrimeFirstCellDriftCoefficient.endpointCoefficient
  exact hprefix.mul ((hxPow (-(1 : Real) / 2)).add hfar)

/-- Pointwise T458 absorption integrated over the deterministic time
interval. -/
theorem integral_endpointCoefficient_le_of_scale
    {tauPrime delta alpha : Real} {N k : Nat}
    (hN : 1 <= N)
    (hpack : APrimeFirstCellScaleFloors.ScalePackage tauPrime N k)
    (hdecay : (2 : Real) ^ (7 : Real) *
      (N : Real) ^ (4 * delta - 1 / 2) <= 1) :
    let v := APrimeFirstCellSampleRegularity.endpoint N k
    (∫ r in (0 : Real)..v,
        APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N v r) <=
      v * absorbedRate alpha N v := by
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hpoint : ∀ r ∈ Icc (0 : Real) v,
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N v r <=
        absorbedRate alpha N v := fun r hr =>
    coefficient_rows hN hpack hr hdecay
  have hint : IntervalIntegrable
      (fun r => APrimeFirstCellDriftCoefficient.endpointCoefficient
        delta (2 * alpha) N v r)
      volume 0 v :=
    (continuousOn_endpointCoefficient hpack.time_le_half).intervalIntegrable_of_Icc
      hpack.time_nonneg
  have hmono := intervalIntegral.integral_mono_on hpack.time_nonneg hint
    intervalIntegrable_const hpoint
  dsimp only
  simpa only [APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint, v,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] using hmono

/-- Uniform deterministic interval integral at every moving endpoint. -/
theorem eventually_integral_endpointCoefficient_le_absorbedRate
    {tauPrime delta : Real} (htau : 0 < tauPrime)
    (hdelta : 0 < delta) (hdelta100 : delta <= 1 / 100) (alpha : Real) :
    ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      (∫ r in (0 : Real)..v,
          APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N v r) <=
        v * absorbedRate alpha N v := by
  filter_upwards [APrimeFirstCellScaleFloors.eventually_scalePackage htau,
    eventually_far_decay delta hdelta hdelta100,
    eventually_ge_atTop 1] with N hpack hdecay hN
  intro k hk
  exact integral_endpointCoefficient_le_of_scale hN (hpack k hk) hdecay

/-- T538's actual weighted norm with its literal coefficient
replaced by the uniform absorbed rate. -/
def actualDriftNormAbsorbed
    (tauPrime delta alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∀ k : Nat, 1 <= k ->
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
        momNormW (P d)
            (APrimeFirstCellSampleRegularity.weight
              tauPrime delta p N k) p
            (APrimeFirstCellSampleRegularity.G N k a r) <=
          absorbedRate alpha N v + (N : Real) ^ (-beta)

theorem actualDriftNormAbsorbed_of_inputs
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hpaid : APrimeFirstCellDeltaDriftBadPayment.actualDriftNormPaid
      tauPrime delta alpha beta p)
    (hcoefficient : ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      ∀ r ∈ Icc (0 : Real) v,
        APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N v r <=
          absorbedRate alpha N v) :
    actualDriftNormAbsorbed tauPrime delta alpha beta p := by
  filter_upwards [hpaid, hcoefficient] with N hpaidN hcoefficientN
  intro k hk1 hk
  dsimp only
  intro r hr a
  exact (hpaidN k hk1 hk r hr a).trans
    (add_le_add (hcoefficientN k hk r hr) le_rfl)

/-- The exact zero endpoint and weight-one branch, with the coefficient
absorbed by the same deterministic estimate. -/
theorem eventually_actualDriftNormAbsorbed_k_zero_of_inputs
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hzero : ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
      (∀ omega, APrimeFirstCellSampleRegularity.weight
        tauPrime delta p N 0 omega = 1) ∧
      momNormW (P d)
          (APrimeFirstCellSampleRegularity.weight
            tauPrime delta p N 0) p
          (APrimeFirstCellSampleRegularity.G N 0 a 0) <=
        APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N
              (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
          (N : Real) ^ (-beta))
    (hcoefficient : ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      ∀ r ∈ Icc (0 : Real) v,
        APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N v r <=
          absorbedRate alpha N v) :
    ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
      (∀ omega, APrimeFirstCellSampleRegularity.weight
        tauPrime delta p N 0 omega = 1) ∧
      momNormW (P d)
          (APrimeFirstCellSampleRegularity.weight
            tauPrime delta p N 0) p
          (APrimeFirstCellSampleRegularity.G N 0 a 0) <=
        absorbedRate alpha N (APrimeFirstCellSampleRegularity.endpoint N 0) +
          (N : Real) ^ (-beta) := by
  filter_upwards [hzero, hcoefficient] with N hzeroN hcoefficientN
  intro a
  obtain ⟨hend, hweight, hnorm⟩ := hzeroN a
  have hmem : (0 : Real) ∈ Icc 0 (APrimeFirstCellSampleRegularity.endpoint N 0) := by
    rw [hend]
    exact ⟨le_rfl, le_rfl⟩
  have hcoeff := hcoefficientN 0 (Nat.zero_le _) 0 hmem
  exact ⟨hend, hweight, hnorm.trans (add_le_add hcoeff le_rfl)⟩

/-- A positive `k = 2` resident on the same literal T538 event, now carrying
the absorbed norm estimate.  Its displayed weight-one field remains the
support weight at smoothing order `m = N`. -/
def positiveActualDriftAbsorbedResident
    (tauPrime delta alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      APrimeSupportRunning.weight delta
        (firstCellT tauPrime) 2 p N 2 N omega = 1 ∧
      let v := APrimeFirstCellSampleRegularity.endpoint N 2
      0 < v ∧ v <= firstCellT tauPrime N ∧ firstCellT tauPrime N <= 1 / 2 ∧
      ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
        momNormW (P d)
            (APrimeFirstCellSampleRegularity.weight
              tauPrime delta p N 2) p
            (APrimeFirstCellSampleRegularity.G N 2 a r) <=
          absorbedRate alpha N v + (N : Real) ^ (-beta)

theorem positiveActualDriftAbsorbedResident_of_inputs
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hresident : APrimeFirstCellDeltaDriftBadPayment.positiveActualDriftPaidResident
      tauPrime delta alpha beta p)
    (hcoefficient : ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      ∀ r ∈ Icc (0 : Real) v,
        APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N v r <=
          absorbedRate alpha N v) :
    positiveActualDriftAbsorbedResident tauPrime delta alpha beta p := by
  filter_upwards [hresident, hcoefficient] with N hresidentN hcoefficientN
  obtain ⟨omega, homega, hk, hweight, hvpos, hvle, hvhalf, hnorm⟩ := hresidentN
  refine ⟨omega, homega, hk, hweight, hvpos, hvle, hvhalf, ?_⟩
  intro r hr a
  exact (hnorm r hr a).trans
    (add_le_add (hcoefficientN 2 hk r hr) le_rfl)

/-- Closed T541 producer.  The event and its `HighProb` proof are exactly
those returned by T538; the coefficient absorption is deterministic. -/
theorem exists_actualDriftNormAbsorbed_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ alpha : Real, 0 < alpha ->
      ∀ p : Nat, 1 <= p ->
      ∀ beta : Real, 0 < beta ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime
            delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime
            delta alpha) ∧
        actualDriftNormAbsorbed tauPrime delta alpha beta p ∧
        (∀ᶠ N : Nat in atTop, ∀ k,
          k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
            APrimeSmoothTransition.transitionMesh N ->
          let v := APrimeFirstCellSampleRegularity.endpoint N k
          (∫ r in (0 : Real)..v,
              APrimeFirstCellDriftCoefficient.endpointCoefficient
                delta
                  (2 * alpha) N v r) <=
            v * absorbedRate alpha N v) ∧
        (∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
          APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
          (∀ omega, APrimeFirstCellSampleRegularity.weight tauPrime
            delta p N 0 omega = 1) ∧
          momNormW (P d)
              (APrimeFirstCellSampleRegularity.weight tauPrime
                delta p N 0) p
              (APrimeFirstCellSampleRegularity.G N 0 a 0) <=
            absorbedRate alpha N (APrimeFirstCellSampleRegularity.endpoint N 0) +
              (N : Real) ^ (-beta)) ∧
        positiveActualDriftAbsorbedResident tauPrime delta alpha beta p := by
  obtain ⟨tauPrime, htau, hall⟩ :=
    APrimeFirstCellDeltaDriftBadPayment.exists_actualDriftNormPaid_with_resident
  refine ⟨tauPrime, htau, ?_⟩
  intro delta hdelta hdelta100 alpha halpha p hp beta hbeta
  obtain ⟨hmeas, hprob, hpaid, hzero, hresident⟩ :=
    hall delta hdelta hdelta100 alpha halpha p hp beta hbeta
  have hcoefficient := eventually_endpointCoefficient_le_absorbedRate
    htau hdelta hdelta100 alpha
  exact ⟨hmeas, hprob,
    actualDriftNormAbsorbed_of_inputs hpaid hcoefficient,
    eventually_integral_endpointCoefficient_le_absorbedRate
      htau hdelta hdelta100 alpha,
    eventually_actualDriftNormAbsorbed_k_zero_of_inputs hzero hcoefficient,
    positiveActualDriftAbsorbedResident_of_inputs hresident hcoefficient⟩

end

end RBM.APrimeFirstCellDeltaDriftCoefficientAbsorbed

namespace RBM.APrimeFirstCellDeltaDriftCoefficientAbsorbed

#print axioms absorbedRate
#print axioms absorbedRate_eq_paperRate
#print axioms far_decay_gap_pos
#print axioms eventually_far_decay
#print axioms eventually_endpointCoefficient_le_absorbedRate
#print axioms continuousOn_endpointCoefficient
#print axioms integral_endpointCoefficient_le_of_scale
#print axioms eventually_integral_endpointCoefficient_le_absorbedRate
#print axioms actualDriftNormAbsorbed
#print axioms actualDriftNormAbsorbed_of_inputs
#print axioms eventually_actualDriftNormAbsorbed_k_zero_of_inputs
#print axioms positiveActualDriftAbsorbedResident
#print axioms positiveActualDriftAbsorbedResident_of_inputs
#print axioms exists_actualDriftNormAbsorbed_with_resident

end RBM.APrimeFirstCellDeltaDriftCoefficientAbsorbed
