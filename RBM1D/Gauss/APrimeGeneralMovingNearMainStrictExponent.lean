/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingDriftNearMainSlot
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeDriftIntegralBudget

/-!
# T1235: sharpen the first T615 near-source integral exponent

This module integrates only the literal first summand of T615's near source
coefficient. It retains the `xiK * ratR(u)^(-2) * ratR(v)^(-2)` transport
normalization and the exact terminal `ratR(v)^(-2)` factor. It makes no claim
about the near residual or any other drift, QV, or cross contribution.
-/

namespace RBM.APrimeGeneralMovingNearMainStrictExponent

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal first summand of T615's near source coefficient, with the
exact transport normalization used by the pointwise T615 profile. -/
noncomputable def normalizedNearMain (E : Real) (s : Nat → Real)
    (zetaSrc zetaCtr : Real) (N : Nat) (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    (Step2Moment.ratR E s N u) ^ (-2 : Real) *
    (Step2Moment.ratR E s N v) ^ (-2 : Real) *
    (4 * (N : Real) ^ (zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
      (B.ell N u / B.ell N (s N)) ^ 3 *
      Lemma57.cNear (d.W N : Real) (B.ell N u))

/-- This file estimates exactly T1001's normalized integrand. -/
theorem normalizedNearMain_eq_T1001 (E : Real) (s : Nat → Real)
    (zetaSrc zetaCtr : Real) (N : Nat) (v u : Real) :
    normalizedNearMain E s zetaSrc zetaCtr N v u =
      APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
        E s zetaSrc zetaCtr N v u := rfl

private theorem integral_ratR_eta_inv_neg_half
    {E s0 v : Real} (hE : |E| < 2) (hs0 : s0 ≤ v) (hv1 : v < 1) :
    (∫ u in s0..v,
        APrimeDriftIntegralBudget.ratio s0 u ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) ≤ 2 / (mE E).im := by
  have hs1 : s0 < 1 := hs0.trans_lt hv1
  have hm := mE_im_pos hE
  have hq : (-(1 / 2 : Real)) ≠ 0 := by norm_num
  have hi := APrimeDriftIntegralBudget.integral_ratio_power
    hs1 hs0 hv1 hm.ne' hq
  have hfun : (fun u => APrimeDriftIntegralBudget.ratio s0 u ^ (-(1 / 2 : Real)) *
      (etaT E u)⁻¹) =
      (fun u => APrimeDriftIntegralBudget.ratio s0 u ^ (-(1 / 2 : Real)) /
        ((mE E).im * (1 - u))) := by
    funext u
    rw [Step2.etaT_eq]
    field_simp [ne_of_gt hm]
    <;> ring
  rw [hfun, hi]
  have hR1 : 1 ≤ APrimeDriftIntegralBudget.ratio s0 v := by
    unfold APrimeDriftIntegralBudget.ratio
    rw [le_div_iff₀ (by linarith : 0 < 1 - v)]
    linarith
  have hR0 : 0 < APrimeDriftIntegralBudget.ratio s0 v := zero_lt_one.trans_le hR1
  have hpow0 : 0 ≤ APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) :=
    Real.rpow_nonneg hR0.le _
  have heq :
      (APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) - 1) /
          ((mE E).im * (-(1 / 2 : Real))) =
        2 / (mE E).im -
          2 * APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) /
            (mE E).im := by
    field_simp [hm.ne']
    ring
  rw [heq]
  have hsub : 0 ≤
      2 * APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) /
        (mE E).im := by positivity
  linarith

private theorem ratio_cube_normalized_le
    {r R : Real} (hr : 0 ≤ r) (hR : 0 < R) (hR1 : 1 ≤ R) (h : r ^ 2 ≤ R) :
    r ^ 3 * R ^ (-2 : Real) ≤ R ^ (-(1 / 2 : Real)) := by
  have hRnonneg : 0 ≤ R := hR.le
  have hsqrt : r ≤ R ^ (1 / 2 : Real) := by
    have hsq : r ≤ Real.sqrt R := by
      rw [Real.le_sqrt hr hRnonneg]
      simpa [pow_two] using h
    simpa [Real.sqrt_eq_rpow] using hsq
  have hcube : r ^ 3 ≤ R ^ (3 / 2 : Real) := by
    have hpow := pow_le_pow_left₀ hr hsqrt 3
    have hright : (R ^ (1 / 2 : Real)) ^ (3 : Nat) = R ^ (3 / 2 : Real) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hRnonneg]
      congr 1
      ring
    exact le_trans hpow (le_of_eq hright)
  calc
    r ^ 3 * R ^ (-2 : Real) ≤ R ^ (3 / 2 : Real) * R ^ (-2 : Real) :=
      mul_le_mul_of_nonneg_right hcube (Real.rpow_nonneg hR.le _)
    _ = R ^ (-(1 / 2 : Real)) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem eventually_cNear_le {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {theta : Real} (htheta : 0 < theta) :
    ∀ᶠ N : Nat in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      Lemma57.cNear (d.W N : Real) (B.ell N u) ≤ (N : Real) ^ theta := by
  have ha : 0 < theta / 4 := by positivity
  have hlogR : ∀ᶠ W : Real in atTop,
      4 * Real.log W ^ (3 : Real) ≤ W ^ (theta / 4) := by
    have hsmall := (Asymptotics.isLittleO_iff_nat_mul_le'.1
      (isLittleO_log_rpow_rpow_atTop (3 : Real) ha)) 4
    filter_upwards [hsmall, eventually_ge_atTop 1] with W hsmall hW1
    have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ W) _)] using hsmall
  have hlog := (Step2.tendsto_W B).eventually hlogR
  have hexp := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 1 ha)
  have hfour := ((tendsto_rpow_atTop ha).comp (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [hlog, hexp, hfour, B.dim, eventually_ge_atTop 1]
    with N hlogN hexpN hfourN hdim hN u hu
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  change 4 ≤ (B.W N : Real) ^ (theta / 4) at hfourN
  change 4 ≤ (B.W N : Real) ^ (theta / 4) at hfourN
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : Real) < B.W N := by linarith
  have hWN : (B.W N : Real) ≤ N := by
    have hL1 : (1 : Real) ≤ B.L N := by exact_mod_cast B.one_le_L N
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  have hell : (1 : Real) ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hcmono := Step2FarInputs.cNear_le_cNear_one hW1 hell
  have hlog0 : 0 ≤ Real.log (B.W N : Real) := Real.log_nonneg hW1
  have hpoly : 2 * Real.log (B.W N : Real) ^ (3 : Real) + 2 ≤
      (B.W N : Real) ^ (theta / 4) := by nlinarith
  have hexp' : Real.exp (Real.log (B.W N : Real) ^ (3 / 4 : Real)) ≤
      (B.W N : Real) ^ (theta / 4) := by simpa only [one_mul] using hexpN
  have hc : Lemma57.cNear (B.W N : Real) 1 ≤
      (B.W N : Real) ^ (theta / 4) * (B.W N : Real) ^ (theta / 4) := by
    unfold Lemma57.cNear
    have hpoly' : 2 * Real.log (B.W N : Real) ^ (3 : Real) + 2 / 1 ≤
        (B.W N : Real) ^ (theta / 4) := by simpa using hpoly
    exact mul_le_mul hpoly' hexp' (Real.exp_pos _).le
      (Real.rpow_nonneg hW0.le _)
  calc
    Lemma57.cNear (d.W N : Real) (B.ell N u) ≤ Lemma57.cNear (d.W N : Real) 1 := hcmono
    _ ≤ (B.W N : Real) ^ (theta / 4) * (B.W N : Real) ^ (theta / 4) := hc
    _ = (B.W N : Real) ^ (theta / 2) := by
      rw [← Real.rpow_add hW0]
      congr 1
      ring
    _ ≤ (N : Real) ^ (theta / 2) := Real.rpow_le_rpow hW0.le hWN (by positivity)
    _ ≤ (N : Real) ^ theta := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)

private theorem continuousOn_nearMain {E : Real} {s : Nat → Real} {N : Nat}
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaSrc zetaCtr : Real) :
    ContinuousOn (fun u => normalizedNearMain E s zetaSrc zetaCtr N v u)
      (Set.Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Set.Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hsEll : 0 < B.ell N (s N) :=
    zero_lt_one.trans_le (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1)
  have hratio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Set.Icc (s N) v) := hEll.div_const _
  have hEta : ContinuousOn (fun u => etaT E u) (Set.Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ Set.Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Set.Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Set.Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u ∈ Set.Icc (s N) v, 1 - u ≠ 0 := by
      intro u hu
      linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRpos : ∀ u, u ∈ Set.Icc (s N) v → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRpow : ContinuousOn (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real))
      (Set.Icc (s N) v) := hR.rpow_const (fun u hu => Or.inl (ne_of_gt (hRpos u hu)))
  have hc : ContinuousOn (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u))
      (Set.Icc (s N) v) := by
    have hEllpos : ∀ u, u ∈ Set.Icc (s N) v → B.ell N u ≠ 0 := by
      intro u hu
      exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
        (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1)))
    have hinv : ContinuousOn (fun u => (B.ell N u)⁻¹) (Set.Icc (s N) v) :=
      hEll.inv₀ hEllpos
    have hpoly : ContinuousOn (fun u =>
        2 * Real.log (d.W N : Real) ^ (3 : Real) + 2 * (B.ell N u)⁻¹)
        (Set.Icc (s N) v) := by fun_prop
    have hexp : ContinuousOn (fun _ : Real =>
        Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)))
        (Set.Icc (s N) v) := continuousOn_const
    have hEq : (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u)) =
        (fun u => (2 * Real.log (d.W N : Real) ^ (3 : Real) +
          2 * (B.ell N u)⁻¹) * Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real))) := by
      funext u
      simp [Lemma57.cNear, div_eq_mul_inv]
    exact hEq ▸ hpoly.mul hexp
  have hmain : ContinuousOn (fun u => normalizedNearMain E s zetaSrc zetaCtr N v u)
      (Set.Icc (s N) v) := by
    unfold normalizedNearMain
    have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Set.Icc (s N) v) :=
      hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
    have hratio3 : ContinuousOn (fun u => (B.ell N u / B.ell N (s N)) ^ 3)
        (Set.Icc (s N) v) := hratio.pow 3
    have hinner : ContinuousOn (fun u =>
        4 * (N : Real) ^ (zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
          (B.ell N u / B.ell N (s N)) ^ 3 *
          Lemma57.cNear (d.W N : Real) (B.ell N u)) (Set.Icc (s N) v) := by
      have hscalar : ContinuousOn (fun _ : Real =>
          4 * (N : Real) ^ (zetaCtr + zetaSrc)) (Set.Icc (s N) v) := continuousOn_const
      have hprod := (hscalar.mul hEtaInv).mul (hratio3.mul hc)
      convert hprod using 1 <;> ext u <;> simp only [Pi.mul_apply] <;> ring
    exact ((continuousOn_const.mul hRpow).mul continuousOn_const).mul hinner
  exact hmain

/-- Under the T995 δ-dependent schedule, the literal T615 first near summand
fits the sharper power `N^(δ/8)`. The estimate is uniform
in all active cells, includes the zero cell, and preserves the exact terminal
`ratR(v)^(-2)` factor. -/
theorem eventually_near_main_integral_le_delta_eighth
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) {δ : Real} (hδ : 0 < δ)
    (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        normalizedNearMain E s
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u
        ≤ (8 / (mE E).im) * (N : Real) ^ (δ / 8) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  have hm := mE_im_pos hE
  have htheta : 0 < δ / 100 := by positivity
  have hcn := eventually_cNear_le hs0 hst ht1 htheta
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im htheta
  filter_upwards [hcn, hxi, eventually_ge_atTop 1] with N hcnN hxiN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hNpos : 0 < (N : Real) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hv1 : v < 1 := hvIcc.2.trans_lt (ht1 N)
  have hRatV : 0 < Step2Moment.ratR E s N v := Step2Moment.ratR_pos hE hs1 hv1
  have hmainInt : IntervalIntegrable
      (fun u => normalizedNearMain E s
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) N v u)
      volume (s N) v :=
    (continuousOn_nearMain hE (hs0 N) hvIcc.1 hv1 _ _).intervalIntegrable_of_Icc hvIcc.1
  have hkernelInt : IntervalIntegrable
      (fun u => (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
        (etaT E u)⁻¹) volume (s N) v := by
    have hpowInt := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := -(1 / 2 : Real)) hvIcc.1 hv1 (ne_of_gt hm)
    have heq : (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im (s N)
        (-(1 / 2 : Real)) u) =
        (fun u => (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp [ne_of_gt hm]
      <;> ring
    rw [← heq]
    exact hpowInt
  have hboundPoint : ∀ u ∈ Set.Icc (s N) v,
      normalizedNearMain E s
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) N v u ≤
        (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
            APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
            (etaT E u)⁻¹) := by
    intro u hu
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hellU : 0 < B.ell N u := zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans hu.1) hu1)
    have hellS : 0 < B.ell N (s N) := zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1)
    have hratio0 : 0 ≤ B.ell N u / B.ell N (s N) := div_nonneg hellU.le hellS.le
    have hratio_sq : (B.ell N u / B.ell N (s N)) ^ 2 ≤
        Step2Moment.ratR E s N u := by
      have hh := Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hu.1 hu1
      rw [ratR_eq_ratio hE]
      simpa [APrimeDriftIntegralBudget.ratio, Step2.etaT_ratio hE] using hh
    have hratio : 0 < Step2Moment.ratR E s N u := Step2Moment.ratR_pos hE hs1 hu1
    have hratio1 : 1 ≤ Step2Moment.ratR E s N u := by
      rw [ratR_eq_ratio hE]
      unfold APrimeDriftIntegralBudget.ratio
      rw [le_div_iff₀ (by linarith : 0 < 1 - u)]
      linarith [hu.1]
    have hcube := ratio_cube_normalized_le hratio0 hratio
      hratio1
      hratio_sq
    rw [ratR_eq_ratio hE] at hcube
    unfold normalizedNearMain
    rw [ratR_eq_ratio hE]
    have hW1 : 1 ≤ (d.W N : Real) := by exact_mod_cast B.one_le_W N
    have hcnear0 : 0 ≤ Lemma57.cNear (d.W N : Real) (B.ell N u) :=
      Lemma57.cNear_nonneg hW1 hellU
    have hcoef0 : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
          APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
        Lemma57.cNear (d.W N : Real) (B.ell N u) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      have hWxi := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hWxi)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hcnear0)
        (Real.rpow_nonneg (Step2Moment.ratR_pos hE hs1 hv1).le _)
    have heta0 : 0 ≤ (etaT E u)⁻¹ :=
      inv_nonneg.mpr (Step2.etaT_pos' hE hu1).le
    have hnonneg : 0 ≤ (B.ell N u / B.ell N (s N)) ^ 3 := by positivity
    have hcancel := mul_le_mul_of_nonneg_right hcube heta0
    have hfac : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
          APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
        Lemma57.cNear (d.W N : Real) (B.ell N u) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := hcoef0
    calc
      _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
            APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((B.ell N u / B.ell N (s N)) ^ 3 *
            (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-2 : Real) * (etaT E u)⁻¹) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
            APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
            (etaT E u)⁻¹) := by
          gcongr
  let C : Real := 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
        APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
      (N : Real) ^ (δ / 100) * (Step2Moment.ratR E s N v) ^ (-2 : Real)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hXi := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    have hNpow : 0 ≤ (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
        APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hRpow : 0 ≤ (Step2Moment.ratR E s N v) ^ (-2 : Real) :=
      Real.rpow_nonneg hRatV.le _
    positivity
  have hpoint' : ∀ u ∈ Set.Icc (s N) v,
      normalizedNearMain E s
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) N v u ≤
        C * ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := by
    intro u hu
    have hcu := hcnN u ⟨hu.1, hu.2.trans hvIcc.2⟩
    have hnonneg : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
          APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      have hxi0 := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
      have hNpow : 0 ≤ (N : Real) ^
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
            APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) :=
        Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hRvpow : 0 ≤ (Step2Moment.ratR E s N v) ^ (-2 : Real) :=
        Real.rpow_nonneg hRatV.le _
      positivity
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hratioPos : 0 < APrimeDriftIntegralBudget.ratio (s N) u := by
      unfold APrimeDriftIntegralBudget.ratio
      exact div_pos (by linarith [hu.1]) (by linarith [hu.2, hv1])
    have hkernel0 : 0 ≤ (APrimeDriftIntegralBudget.ratio (s N) u) ^
        (-(1 / 2 : Real)) * (etaT E u)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg hratioPos.le _)
        (inv_nonneg.mpr (Step2.etaT_pos' hE hu1).le)
    calc
      _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
              (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
                APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
            (etaT E u)⁻¹) := hboundPoint u hu
      _ ≤ C * ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := by
          dsimp [C]
          apply mul_le_mul_of_nonneg_right _ hkernel0
          have hfactor : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
              (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
                APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
              (Step2Moment.ratR E s N v) ^ (-2 : Real) := hnonneg
          calc
            _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
                (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
                  APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
                (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
                Lemma57.cNear (d.W N : Real) (B.ell N u) := by
              dsimp [d, B]
              ac_rfl
            _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
                (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
                  APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) *
                (Step2Moment.ratR E s N v) ^ (-2 : Real)) * (N : Real) ^ (δ / 100) :=
              mul_le_mul_of_nonneg_left hcu hfactor
            _ = C := by dsimp [C]; ring
  have hmono := intervalIntegral.integral_mono_on hvIcc.1 hmainInt
    (hkernelInt.const_mul C) hpoint'
  have hkernelBound :
      (∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) ≤ 2 / (mE E).im := by
    have hInt := integral_ratR_eta_inv_neg_half hE hvIcc.1 hv1
    exact hInt
  have hCbound : C ≤ 4 * (N : Real) ^ (δ / 8) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
    have hxiN' : Step2.xiK (d.L N) (d.W N) (mE E).im ≤ (N : Real) ^ (δ / 100) := hxiN
    have hzeta : APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
        APrimeGeneralMovingSlotLossSchedule.zetaSrc δ = δ / 1600 := by
      simp [APrimeGeneralMovingSlotLossSchedule.zetaCtr,
        APrimeGeneralMovingSlotLossSchedule.zetaSrc]
      ring
    have hpow : (N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100) *
        (N : Real) ^ (δ / 100) ≤ (N : Real) ^ (δ / 8) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      have hNge : (1 : Real) ≤ (N : Real) := by exact_mod_cast hN
      have hExponent : δ / 1600 + δ / 100 + δ / 100 < δ / 8 := by
        nlinarith [hδ]
      exact Real.rpow_le_rpow_of_exponent_le hNge (le_of_lt hExponent)
    change 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
        APrimeGeneralMovingSlotLossSchedule.zetaSrc δ) * (N : Real) ^ (δ / 100) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) ≤ _
    rw [hzeta]
    calc
      _ = 4 * (Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100)) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by ring
      _ ≤ 4 * ((N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100) *
          (N : Real) ^ (δ / 100)) * (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
          have hstep : Step2.xiK (d.L N) (d.W N) (mE E).im *
              (N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100) ≤
            (N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100) *
              (N : Real) ^ (δ / 100) := by
            calc
              _ = Step2.xiK (d.L N) (d.W N) (mE E).im *
                  ((N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100)) := by ring
              _ ≤ (N : Real) ^ (δ / 100) *
                  ((N : Real) ^ (δ / 1600) * (N : Real) ^ (δ / 100)) :=
                mul_le_mul_of_nonneg_right hxiN' (by positivity)
              _ = _ := by ring
          gcongr
      _ ≤ 4 * (N : Real) ^ (δ / 8) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by gcongr
  calc
    _ ≤ ∫ u in (s N)..v,
        C * ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := hmono
    _ = C * ∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹ := by rw [intervalIntegral.integral_const_mul]
    _ ≤ C * (2 / (mE E).im) := mul_le_mul_of_nonneg_left hkernelBound hC0
    _ ≤ (8 / (mE E).im) * (N : Real) ^ (δ / 8) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      have hm0 : 0 ≤ 2 / (mE E).im := by positivity
      calc
        _ = C * (2 / (mE E).im) := rfl
        _ ≤ (4 * (N : Real) ^ (δ / 8) *
            (Step2Moment.ratR E s N v) ^ (-2 : Real)) * (2 / (mE E).im) :=
          mul_le_mul_of_nonneg_right hCbound hm0
        _ = _ := by ring

/-- T995's nondegenerate `E=0`, `D=60`, positive-cell same-resident witness
also realizes the exact schedule used by this near-main slot theorem. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms normalizedNearMain_eq_T1001
#print axioms eventually_near_main_integral_le_delta_eighth
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingNearMainStrictExponent
