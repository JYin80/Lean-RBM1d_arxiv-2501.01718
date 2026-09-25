/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingTransitionPrefixGradient

/-!
# T1303: corrected free-loss scalar transition prefix-gradient bound

This file records the same-loss schedule and bounds the deterministic rate
used by the accepted same-time raw-QV prefix producer.  The actual
prefix-gradient conclusion remains conditional on the identical
common-event/transition intersection.
-/

namespace RBM.APrimeFreeLossPrefixGradient

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

noncomputable def deltaWeight (lambda : Real) : Real := lambda
noncomputable def xi (lambda : Real) : Real := lambda
noncomputable def deltaCap (lambda : Real) : Real := 2 * lambda
noncomputable def sourceLoss (lambda : Real) : Real := lambda / 1000
noncomputable def tauG (lambda : Real) : Real := sourceLoss lambda
noncomputable def zetaSrc (lambda : Real) : Real := sourceLoss lambda
noncomputable def zetaCtr (lambda : Real) : Real := sourceLoss lambda

private noncomputable def rateCapConst : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)

private noncomputable def rateRawConst : Real :=
  6 + 1200 * rateCapConst^3

/-- The scalar constant in the free-loss rate bound. -/
noncomputable def freeLossRateConst : Real :=
  Real.exp 1 * Real.sqrt rateRawConst

theorem freeLossRateConst_pos : 0 < freeLossRateConst := by
  unfold freeLossRateConst rateRawConst rateCapConst
  positivity

/-- The corrected source-loss schedule has all raw-producer and cap rooms.
The actual weight and buffer losses agree, and their sum is the cap. -/
theorem freeLoss_schedule_room {c lambda : Real}
    (hc : 0 < c) (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    0 < deltaWeight lambda ∧
    0 < xi lambda ∧
    0 < deltaCap lambda ∧
    0 < zetaSrc lambda ∧
    0 < zetaCtr lambda ∧
    0 < tauG lambda ∧
    deltaWeight lambda + xi lambda = deltaCap lambda ∧
    zetaSrc lambda ≤ tauG lambda ∧
    tauG lambda ≤ deltaWeight lambda / 16 ∧
    tauG lambda ≤ deltaCap lambda / 16 ∧
    deltaWeight lambda ≤ c / 20 ∧
    deltaCap lambda ≤ c / 20 ∧
    tauG lambda + 2 * deltaCap lambda + (2 : Real) / 15 < 1 ∧
    3 * (tauG lambda + 2 * deltaWeight lambda) - c / 30
      ≤ sourceLoss lambda + sourceLoss lambda := by
  have hlambda1 : lambda ≤ (1 : Real) / 10000 :=
    hsmall.trans (min_le_left _ _)
  have hlambdac : lambda ≤ c / 10000 :=
    hsmall.trans (min_le_right _ _)
  have hsource : 0 < sourceLoss lambda := by
    dsimp [sourceLoss]
    positivity
  have hcapweight : deltaWeight lambda + xi lambda = deltaCap lambda := by
    dsimp [deltaWeight, xi, deltaCap]
    ring
  refine ⟨?_, ?_, ?_, hsource, hsource, hsource, hcapweight, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · dsimp [deltaWeight]
    exact hlambda
  · dsimp [xi]
    exact hlambda
  · dsimp [deltaCap]
    positivity
  · rfl
  · dsimp [tauG, sourceLoss, deltaWeight]
    nlinarith
  · dsimp [tauG, sourceLoss, deltaCap]
    nlinarith
  · dsimp [deltaWeight]
    nlinarith [hc]
  · dsimp [deltaCap]
    nlinarith [hc]
  · dsimp [tauG, sourceLoss, deltaCap]
    nlinarith [hlambda1]
  · dsimp [tauG, sourceLoss, deltaWeight]
    nlinarith [hc, hlambdac]

private theorem ratio_fifth_le_cube {x r : Real}
    (hx : 0 ≤ x) (hr : 1 ≤ r) (hxr : x^2 ≤ r) : x^5 ≤ r^3 := by
  have hxle : x ≤ r := by
    have hr2 : r ≤ r^2 := by nlinarith
    nlinarith [sq_nonneg (x + r)]
  calc
    x^5 = x * (x^2)^2 := by ring
    _ ≤ r * r^2 := by gcongr
    _ = r^3 := by ring

private theorem near_source_scalar_le {N zeta eps eta c ellRatio r : Real}
    (hN : 0 < N) (heta : 0 < eta) (hc0 : 0 ≤ c) (hcn : c ≤ N^eps)
    (hell : 0 ≤ ellRatio) (hr : 1 ≤ r) (hratio : ellRatio^2 ≤ r) :
    4 * N^zeta * eta⁻¹ * c * ellRatio^5 ≤
      4 * N^(zeta + eps) * eta⁻¹ * r^3 := by
  have h5 := ratio_fifth_le_cube hell hr hratio
  have hm := mul_le_mul hcn h5 (pow_nonneg hell _) (by positivity)
  have hf : 0 ≤ 4 * N^zeta * eta⁻¹ := by positivity
  calc
    _ = (4 * N^zeta * eta⁻¹) * (c * ellRatio^5) := by ring
    _ ≤ (4 * N^zeta * eta⁻¹) * (N^eps * r^3) :=
      mul_le_mul_of_nonneg_left hm hf
    _ = 4 * N^(zeta + eps) * eta⁻¹ * r^3 := by
      rw [Real.rpow_add hN]
      ring

private theorem margin_to_inv_cubic {A N r e : Real}
    (hA : 0 < A) (hN : 0 < N) (hr : 0 < r)
    (hmargin : N^e * r^(27 : Real) ≤ A) :
    A^(-(1/3 : Real)) ≤ N^(-(e/3)) * r^(-(9 : Real)) := by
  have hp := Real.rpow_le_rpow
    (by positivity : 0 ≤ N^e * r^(27 : Real)) hmargin
    (by norm_num : (0 : Real) ≤ 1 / 3)
  have hleft : (N^e * r^(27 : Real))^(1/3 : Real) =
      N^(e/3) * r^9 := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hr.le _),
      ← Real.rpow_mul hN.le, ← Real.rpow_mul hr.le]
    congr 1
    · ring
    · norm_num
  rw [hleft] at hp
  have hinv := inv_anti₀
    (by positivity : 0 < N^(e/3) * r^9) hp
  rw [Real.rpow_neg hA.le, Real.rpow_neg hN.le, Real.rpow_neg hr.le]
  simpa [mul_inv, mul_comm] using hinv

private theorem transition_cap_le_const_mul
    {E tau delta : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hr : 1 ≤ Step2Moment.ratR E s N u) :
    APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
        E s tau delta N u ≤
      rateCapConst * (N : Real)^(tau + 2*delta) *
        Step2Moment.ratR E s N u^4 := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
  have hR4 : 1 ≤ Step2Moment.ratR E s N u^4 := one_le_pow₀ hr
  have ht : 1 ≤ (N : Real)^tau := Real.one_le_rpow hn htau
  have hd : 1 ≤ (N : Real)^(2*delta) := Real.one_le_rpow hn (by positivity)
  have hX : 1 ≤ (N : Real)^tau * (N : Real)^(2*delta) *
      Step2Moment.ratR E s N u^4 := by
    nlinarith [mul_le_mul ht hd (by positivity) (by positivity),
      mul_le_mul (mul_le_mul ht hd (by positivity) (by positivity)) hR4
        (by positivity) (by positivity)]
  have htX : (N : Real)^tau ≤ (N : Real)^tau * (N : Real)^(2*delta) *
      Step2Moment.ratR E s N u^4 := by
    have hm : 1 ≤ (N : Real)^(2*delta) *
        Step2Moment.ratR E s N u^4 :=
      by nlinarith [mul_le_mul hd hR4 (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real)^tau * (N : Real)^(2*delta) =
      (N : Real)^(tau + 2*delta) := by rw [Real.rpow_add hn0]
  unfold APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
    rateCapConst
  calc
    1 + (N : Real)^tau *
        (9 * Real.exp (Real.sqrt 3) *
          (((16 * (Real.exp 1)^2 + 1) * (N : Real)^(2*delta)) *
            Step2Moment.ratR E s N u^4) + 2) ≤
      (3 + 9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)) *
        ((N : Real)^tau * (N : Real)^(2*delta) *
          Step2Moment.ratR E s N u^4) := by
      have hmain : (N : Real)^tau *
          (9 * Real.exp (Real.sqrt 3) *
            (((16 * (Real.exp 1)^2 + 1) * (N : Real)^(2*delta)) *
              Step2Moment.ratR E s N u^4)) =
          (9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)) *
            ((N : Real)^tau * (N : Real)^(2*delta) *
              Step2Moment.ratR E s N u^4) := by ring
      rw [mul_add, hmain]
      nlinarith
    _ = _ := by rw [hpow]; ring

private theorem eventually_cNear2_le {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {eps : Real} (heps : 0 < eps) :
    ∀ᶠ N : Nat in atTop, ∀ u : TimeIcc s t N,
      Lemma57.cNear2 (B.W N : Real) (B.ell N (u : Real)) ≤ (N : Real)^eps := by
  have ha : 0 < eps / 2 := by positivity
  have hlog := (Asymptotics.isLittleO_iff_nat_mul_le'.1
    (isLittleO_log_rpow_rpow_atTop (3 : Real) ha)) 4
  have hlogW := (Step2.tendsto_W B).eventually hlog
  have hexpW := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 4 ha)
  have hfour := ((tendsto_rpow_atTop ha).comp
    (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [hlogW, hexpW, hfour, B.dim, eventually_ge_atTop 1]
    with N hlogN hexpN hfourN hdim hN u
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : Real) < B.W N := by linarith
  have hWN : (B.W N : Real) ≤ N := by
    have hL : (1 : Real) ≤ B.L N := by exact_mod_cast B.one_le_L N
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by
      exact_mod_cast hdim.1
    nlinarith
  have hell : (1 : Real) ≤ B.ell N (u : Real) := by
    simpa only [Band.ell] using one_le_ellHat_of_nonneg (B.one_le_L N)
      ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hlog0 : 0 ≤ Real.log (B.W N : Real) := Real.log_nonneg hW1
  have hfourN' : (4 : Real) ≤ (B.W N : Real)^(eps/2) := by
    simpa only [Function.comp_apply] using hfourN
  have hlogN' : 4 * Real.log (B.W N : Real)^(3 : Real) ≤
      (B.W N : Real)^(eps/2) := by
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ (B.W N : Real)) _)]
      using hlogN
  have hpoly : 2 * Real.log (B.W N : Real)^(3 : Real) +
      2 / B.ell N (u : Real) ≤
      (B.W N : Real)^(eps/2) := by
    have hdiv : 2 / B.ell N (u : Real) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : (0 : Real) < B.ell N (u : Real))).2
      nlinarith
    nlinarith [hlogN', hdiv, hfourN']
  have hexp' : Real.exp (4 * Real.log (B.W N : Real)^(3/4 : Real)) ≤
      (B.W N : Real)^(eps/2) := by simpa only [one_mul] using hexpN
  calc
    _ ≤ (B.W N : Real)^(eps/2) * (B.W N : Real)^(eps/2) := by
      unfold Lemma57.cNear2
      exact mul_le_mul hpoly hexp' (Real.exp_pos _).le
        (Real.rpow_nonneg hW0.le _)
    _ = (B.W N : Real)^eps := by rw [← Real.rpow_add hW0]; congr 1; ring
    _ ≤ (N : Real)^eps := Real.rpow_le_rpow hW0.le hWN heps.le

private theorem far_scalar_le {A N r J C e t : Real}
    (hA : 0 < A) (hN : 0 < N) (hr : 0 < r)
    (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hmargin : N^e * r^(27 : Real) ≤ A)
    (hcap : J ≤ C * N^t * r^4) :
    A^(-(1/3 : Real)) * J^3 ≤ C^3 * N^(3*t-e/3) * r^3 := by
  have hinv := margin_to_inv_cubic hA hN hr hmargin
  have hJ3 := pow_le_pow_left₀ hJ hcap 3
  have hprod := mul_le_mul hinv hJ3 (pow_nonneg hJ 3)
    (by positivity : 0 ≤ N^(-(e/3 : Real)) * r^(-(9 : Real)))
  have hNpow : N^(-(e/3 : Real)) * (N^t)^3 = N^(3*t-e/3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1 <;> ring
  have hrpow : r^(-(9 : Real)) * (r^4)^3 = r^3 := by
    rw [show (r^4 : Real) = r^(4 : Real) by norm_num [Real.rpow_natCast]]
    rw [← Real.rpow_natCast (r^4 : Real)]
    rw [← Real.rpow_mul hr.le]
    norm_num
    field_simp [ne_of_gt (pow_pos hr 9)]
  calc
    _ ≤ (N^(-(e/3 : Real)) * r^(-(9 : Real))) *
        (C * N^t * r^4)^3 := hprod
    _ = _ := by rw [mul_pow, mul_pow, ← hNpow, ← hrpow]; ring

private theorem root_transport_cancel {a b r C N q : Real}
    (ha : 0 < a) (hb : 0 < b) (hr : r = a / b)
    (hC : 0 < C) (hN : 0 < N) :
    r^(-(2 : Real)) * Real.sqrt (C * N^q * b⁻¹ * r^3) =
      Real.sqrt C * N^(q/2) * a^(-(1/2 : Real)) := by
  have hrpos : 0 < r := by rw [hr]; exact div_pos ha hb
  have hNpow : (N^(q/2))^2 = N^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hapow : (a^(-(1/2 : Real)))^2 = a^(-1 : Real) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    norm_num
  have hLpow : (r^(-(2 : Real)))^2 = r^(-(4 : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le]
    congr 1
    norm_num
  have hrpow : r^(-(4 : Real)) * r^3 = r^(-(1 : Real)) := by
    rw [Real.rpow_neg hrpos.le, Real.rpow_neg hrpos.le]
    norm_num [Real.rpow_natCast]
    field_simp [ne_of_gt hrpos]
  have hcancel : r^(-(4 : Real)) * b⁻¹ * r^3 = a^(-(1 : Real)) := by
    calc
      _ = (r^(-(4 : Real)) * r^3) * b⁻¹ := by ring
      _ = r^(-(1 : Real)) * b⁻¹ := by rw [hrpow]
      _ = a^(-(1 : Real)) := by
        rw [Real.rpow_neg hrpos.le, hr]
        rw [Real.rpow_one]
        rw [Real.rpow_neg ha.le]
        field_simp [ne_of_gt ha]
        norm_num
  have hleftsq :
      (r^(-(2 : Real)) * Real.sqrt (C * N^q * b⁻¹ * r^3))^2 =
        C * N^q * a^(-(1 : Real)) := by
    calc
      _ = C * N^q * (r^(-(4 : Real)) * b⁻¹ * r^3) := by
        rw [mul_pow, hLpow, Real.sq_sqrt (by positivity)]
        ring
      _ = C * N^q * a^(-(1 : Real)) := by rw [hcancel]
  have hrightsq :
      (Real.sqrt C * N^(q/2) * a^(-(1/2 : Real)))^2 =
        C * N^q * a^(-(1 : Real)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, hNpow, hapow]
  have hleft0 : 0 ≤ r^(-(2 : Real)) *
      Real.sqrt (C * N^q * b⁻¹ * r^3) := by positivity
  have hright0 : 0 ≤ Real.sqrt C * N^(q/2) * a^(-(1/2 : Real)) := by
    positivity
  nlinarith [hleftsq, hrightsq]

private theorem eventually_raw_rate_le
    {E c lambda : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ u : TimeIcc s t N,
      APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
          E s (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N (u : Real) ≤
        rateRawConst * (N : Real)^(sourceLoss lambda + sourceLoss lambda) *
          (etaT E (u : Real))⁻¹ *
          Step2Moment.ratR E s N (u : Real)^3 := by
  have hroom := freeLoss_schedule_room hc hlambda hsmall
  rcases hroom with ⟨hdw, hxi, hcap, hzsrc, hzctr, htau, hsum,
    hzt, htDw, htCap, hdwC, hcapC, hroom, hfarExp⟩
  have hNear := eventually_cNear2_le hs0 ht1
    (eps := sourceLoss lambda) (by positivity)
  have hMargin := hreg.margin hE hst ht1 hc
    (e := c/10) (b := 27) (a := 1) (by positivity) (by norm_num)
    (by field_simp [hc.ne']; norm_num)
  have hScale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  filter_upwards [hNear, hMargin, hScale, d.dim, eventually_ge_atTop 1]
    with N hNearN hMarginN hScaleN hdim hN u
  let r := Step2Moment.ratR E s N (u : Real)
  let eta := etaT E (u : Real)
  let A := B.scale E N (u : Real)
  let J := APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
    E s (tauG lambda) (deltaWeight lambda) N (u : Real)
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : Real) := by linarith
  have hu0 : 0 ≤ (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hr : 1 ≤ r := Step2Moment.one_le_ratR hE u.2.1 hu1
  have hrpos : 0 < r := by linarith
  have heta : 0 < eta := Step2.etaT_pos' hE hu1
  have heta1 : eta ≤ 1 := etaT_le_one hE hu0
  have hApos : 0 < A := by
    dsimp [A]
    rw [B.scale_eq_flowScale]
    exact flowScale_pos (by exact_mod_cast B.W_pos N) (B.one_le_L N) hE hu1
  have hA1 : 1 ≤ A := (Real.one_le_rpow hNreal hc.le).trans (hScaleN u).1
  have hMarginU : (N : Real)^(c/10) * r^(27 : Real) ≤ A := by
    have hm := hMarginN u
    change (N : Real)^(c/10) *
      (etaT E (s N) / etaT E (u : Real))^(27 : Real) ≤
        B.scale E N (u : Real)^(1 : Real) at hm
    have hrEq : r = etaT E (s N) / etaT E (u : Real) := by rfl
    rw [← hrEq, Real.rpow_one] at hm
    simpa [A] using hm
  have hEllS : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have hEllU : 0 < B.ell N (u : Real) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) ((u : Real) : Complex) by linarith)
  have hEllRatio : 0 ≤ B.ell N (u : Real) / B.ell N (s N) := by positivity
  have hEllRatio2 : (B.ell N (u : Real) / B.ell N (s N))^2 ≤ r := by
    dsimp [r]
    exact Step2MomentStep.ratio_sq_le (B := B) (s := s) hE u.2.1 hu1
  have hCnear : Lemma57.cNear2 (B.W N : Real) (B.ell N (u : Real)) ≤
      (N : Real)^(sourceLoss lambda) := by
    simpa using hNearN u
  have hNearRate :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s (zetaSrc lambda)
          N (u : Real) ≤
        4 * (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    have hnear := near_source_scalar_le
      (N := (N : Real)) (zeta := sourceLoss lambda)
      (eps := sourceLoss lambda) (eta := eta)
      hNpos heta
      (Lemma57.cNear2_nonneg (by exact_mod_cast B.W_pos N) hEllU)
      hCnear hEllRatio hr hEllRatio2
    simpa [Band.ell, zetaSrc, sourceLoss, r, eta] using hnear
  have hWinv : (B.W N : Real)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast B.W_pos N)
  have hbase1 : 1 ≤
      (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 := by
    have hpow : 1 ≤ (N : Real)^(sourceLoss lambda + sourceLoss lambda) :=
      Real.one_le_rpow hNreal (by positivity)
    have hetaInv : 1 ≤ eta⁻¹ := (one_le_inv₀ heta).2 heta1
    have hr3 : 1 ≤ r^3 := one_le_pow₀ hr
    have hprod : 1 ≤
        (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ := by
      nlinarith [mul_le_mul hpow hetaInv (by positivity) (by positivity)]
    nlinarith [mul_le_mul hprod hr3 (by positivity) (by positivity)]
  have hnear :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s (zetaSrc lambda)
          N (u : Real) +
        2 * (B.W N : Real)⁻¹ ≤
        6 * (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 := by
    have hbase0 : 0 ≤
        (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 := by
      positivity
    nlinarith [hNearRate, hWinv, hbase1]
  have hcapJ : J ≤ rateCapConst * (N : Real)^
      (tauG lambda + 2 * deltaWeight lambda) * r^4 := by
    dsimp [J, r]
    exact transition_cap_le_const_mul hN htau.le hdw.le hr
  have hJ0 : 0 ≤ J := by
    dsimp [J, APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap]
    positivity
  have hFarRaw := far_scalar_le hApos hNpos hrpos hJ0
    (show 0 ≤ rateCapConst by unfold rateCapConst; positivity)
    hMarginU hcapJ
  have hFarRaw' : A^(-(1/3 : Real)) * J^3 ≤
      rateCapConst^3 *
        (N : Real)^(3 * (tauG lambda + 2 * deltaWeight lambda) - c/30) *
        r^3 := by
    dsimp only [J] at hFarRaw
    rw [show c/10/3 = c/30 by ring] at hFarRaw
    exact hFarRaw
  have hExp : 3 * (tauG lambda + 2 * deltaWeight lambda) - c/30
      ≤ sourceLoss lambda + sourceLoss lambda := hfarExp
  have hFarPow := Real.rpow_le_rpow_of_exponent_le hNreal hExp
  have hCapConst0 : 0 ≤ rateCapConst := by
    unfold rateCapConst
    positivity
  have hFar :
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real) J ≤
        (1200 * rateCapConst^3) *
          (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    calc
      _ = 1200 * eta⁻¹ * (A^(-(1/3 : Real)) * J^3) := by ring
      _ ≤ 1200 * eta⁻¹ *
          (rateCapConst^3 *
            (N : Real)^(3 * (tauG lambda + 2 * deltaWeight lambda) - c/30) *
            r^3) :=
        mul_le_mul_of_nonneg_left hFarRaw' (by positivity)
      _ ≤ 1200 * eta⁻¹ *
          (rateCapConst^3 *
            (N : Real)^(sourceLoss lambda + sourceLoss lambda) * r^3) := by
        have hpowTerm :
            rateCapConst^3 *
                (N : Real)^(3 * (tauG lambda + 2 * deltaWeight lambda) - c/30) *
                r^3 ≤
              rateCapConst^3 *
                (N : Real)^(sourceLoss lambda + sourceLoss lambda) * r^3 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hFarPow (pow_nonneg hCapConst0 3))
            (by positivity)
        exact mul_le_mul_of_nonneg_left hpowTerm (by positivity)
      _ = _ := by ring
  change APrimeGeneralMovingQVAbsorption.nearSourceRate E s (zetaSrc lambda)
      N (u : Real) + 2 * (B.W N : Real)⁻¹ +
        APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real) J ≤
    rateRawConst * (N : Real)^(sourceLoss lambda + sourceLoss lambda) *
      eta⁻¹ * r^3
  calc
    _ ≤ 6 * (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 +
        (1200 * rateCapConst^3) *
          (N : Real)^(sourceLoss lambda + sourceLoss lambda) * eta⁻¹ * r^3 :=
      add_le_add hnear hFar
    _ = _ := by unfold rateRawConst; ring

/-- The actual transition rate has the free-loss size uniformly over positive
active target-mesh cells.  The loss parameter and model parameters are fixed
before the eventual cutoff in N. -/
theorem eventually_transitionPrefixGradientRate_le_free_loss
    {E D c lambda : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      1 ≤ k →
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N k ≤
        freeLossRateConst * (N : Real)^(sourceLoss lambda) *
          (etaT E (s N))^(-(1/2 : Real)) := by
  have hraw := eventually_raw_rate_le hE hc hreg hs0 hst ht1 hlambda hsmall
  filter_upwards [hraw, eventually_ge_atTop 1] with N hrawN hN
  intro k hk hkTop
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let S := etaT E (s N)
  let bound := Real.sqrt rateRawConst * (N : Real)^(sourceLoss lambda) *
    S^(-(1/2 : Real))
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hv : cutNetPt s mesh N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have hv1 : cutNetPt s mesh N k < 1 := hv.2.trans_lt (ht1 N)
  have hS : 0 < S := by
    dsimp [S]
    exact Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hbound0 : 0 ≤ bound := by positivity
  have htheta : 1 ≤ APrimeSmoothWeightActual.threshold
      (deltaWeight lambda) N := by
    unfold APrimeSmoothWeightActual.threshold
    have hpow : 1 ≤ (N : Real)^(2 * deltaWeight lambda) :=
      Real.one_le_rpow hNreal (by positivity)
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith [mul_le_mul hpow (sq_nonneg (Real.exp 1))
      (by positivity) (by positivity)]
  have hthetaPos : 0 < APrimeSmoothWeightActual.threshold
      (deltaWeight lambda) N :=
    lt_of_lt_of_le zero_lt_one htheta
  have hStoredUniform : ∀ j < k,
      APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s
        (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N
        (cutNetPt s mesh N j) ≤ bound := by
    intro j hj
    let u := cutNetPt s mesh N j
    have huWindow : u ∈ Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset (hj.le.trans hkTop))
    have hu0 : 0 ≤ u := (hs0 N).trans huWindow.1
    have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
    have hR1 : 1 ≤ Step2Moment.ratR E s N u :=
      Step2Moment.one_le_ratR hE huWindow.1 hu1
    have hRpos : 0 < Step2Moment.ratR E s N u := by linarith
    have hU : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hRatio : Step2Moment.ratR E s N u = S / etaT E u := by
      dsimp [S, Step2Moment.ratR]
    have hrawU := hrawN ⟨u, huWindow⟩
    have hsqrt := Real.sqrt_le_sqrt hrawU
    have hroot :
        Step2Moment.ratR E s N u^(-(2 : Real)) *
          Real.sqrt
            (APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
              E s (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N u) ≤ bound := by
      calc
        _ ≤ Step2Moment.ratR E s N u^(-(2 : Real)) *
            Real.sqrt (rateRawConst *
              (N : Real)^(sourceLoss lambda + sourceLoss lambda) *
              (etaT E u)⁻¹ * Step2Moment.ratR E s N u^3) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = bound := by
          dsimp [bound, S]
          conv_rhs =>
            rw [← (show (sourceLoss lambda + sourceLoss lambda) / 2 =
              sourceLoss lambda by ring)]
          exact root_transport_cancel (a := etaT E (s N)) (b := etaT E u)
            (r := Step2Moment.ratR E s N u) (C := rateRawConst)
            (N := (N : Real)) (q := sourceLoss lambda + sourceLoss lambda)
            hS hU hRatio (by unfold rateRawConst rateCapConst; positivity) hNpos
    have hRinv : Step2Moment.ratR E s N u^(-(2 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
    have hRinv4 :
        (Step2Moment.ratR E s N u^4)⁻¹ =
          Step2Moment.ratR E s N u^(-(4 : Real)) := by
      calc
        _ = (Real.rpow (Step2Moment.ratR E s N u) (4 : Real))⁻¹ := by
          rw [← Real.rpow_natCast]
          norm_num
        _ = _ := by
          exact (Real.rpow_neg hRpos.le (4 : Real)).symm
    have hRpow :
        Step2Moment.ratR E s N u^(-(4 : Real)) =
          Step2Moment.ratR E s N u^(-(2 : Real)) *
            Step2Moment.ratR E s N u^(-(2 : Real)) := by
      rw [← Real.rpow_add hRpos]
      congr 1
      ring
    have hinner :
        (Step2Moment.ratR E s N u^4)⁻¹ *
          Real.sqrt
            (APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
              E s (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N u) ≤ bound := by
      rw [hRinv4, hRpow]
      calc
        _ = Step2Moment.ratR E s N u^(-(2 : Real)) *
            (Step2Moment.ratR E s N u^(-(2 : Real)) *
              Real.sqrt
                (APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
                  E s (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N u)) := by ring
        _ ≤ Step2Moment.ratR E s N u^(-(2 : Real)) * bound :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
        _ ≤ 1 * bound :=
          mul_le_mul_of_nonneg_right hRinv hbound0
        _ = bound := by ring
    have hstored :
        APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s
          (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N u ≤ bound := by
      unfold APrimeGeneralMovingTransitionPrefixGradient.storedRootRate
      apply (div_le_iff₀ hthetaPos).2
      calc
        _ ≤ bound := hinner
        _ ≤ bound * APrimeSmoothWeightActual.threshold
            (deltaWeight lambda) N :=
          le_mul_of_one_le_right hbound0 htheta
    simpa [u] using hstored
  have htermUniform : ∀ j < k,
      Real.sqrt (cutNetPt s mesh N j) *
        APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s
          (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N
          (cutNetPt s mesh N j) ≤ bound := by
    intro j hj
    have huWindow : cutNetPt s mesh N j ∈ Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset (hj.le.trans hkTop))
    have hu0 : 0 ≤ cutNetPt s mesh N j := (hs0 N).trans huWindow.1
    have hu1 : cutNetPt s mesh N j ≤ 1 :=
      huWindow.2.trans (ht1 N).le
    have hsqrt : Real.sqrt (cutNetPt s mesh N j) ≤ 1 :=
      Real.sqrt_le_one.2 hu1
    have hstored0 : 0 ≤
        APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s
          (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N
          (cutNetPt s mesh N j) := by
      unfold APrimeGeneralMovingTransitionPrefixGradient.storedRootRate
      positivity
    calc
      _ ≤ 1 * bound := mul_le_mul hsqrt (hStoredUniform j hj)
        hstored0 (by norm_num)
      _ = bound := by ring
  have hsup :
      (Finset.range k).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun j => Real.sqrt (cutNetPt s mesh N j) *
          APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s
            (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N
            (cutNetPt s mesh N j)) ≤ bound := by
    apply Finset.sup'_le
    intro j hj
    exact htermUniform j (Finset.mem_range.mp hj)
  unfold APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
  rw [dif_pos (by omega)]
  calc
    _ ≤ Real.exp 1 * bound :=
      mul_le_mul_of_nonneg_left hsup (Real.exp_pos 1).le
    _ = freeLossRateConst * (N : Real)^(sourceLoss lambda) *
        (etaT E (s N))^(-(1/2 : Real)) := by
      dsimp [bound, freeLossRateConst, rateRawConst, S]
      ring

/-- The inactive-prefix scalar rate vanishes definitionally. -/
theorem transitionPrefixGradientRate_zero
    (E D lambda : Real) (s t : Nat → Real) (N : Nat) :
    APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
      E D s t (zetaSrc lambda) (tauG lambda) (deltaWeight lambda) N 0 = 0 := by
  simp [APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate]

/-- At k=0 the actual smooth-prefix gradient is zero for every model sample. -/
theorem prefixGradient_zero
    (E D delta : Real) (s mesh : Nat → Real) (N m : Nat)
    (hm : 1 ≤ m) (omega : Gauss.Ω d) :
    APrimeCrossJointSplit.prefixGradient d E D delta s mesh N 0 m omega = 0 := by
  have hmatrix : ∀ M : Matrix (d.Idx N) (d.Idx N) Complex,
      APrimeSmoothWeightActual.prefixMatrix d E D s mesh N 0 m M = 0 := by
    intro M
    simp only [APrimeSmoothWeightActual.prefixMatrix,
      Step2Bootstrap.softMax, Finset.range_zero, Finset.sum_empty]
    have hm0 : (0 : Real) < (m : Real) := by exact_mod_cast (by omega : 0 < m)
    exact Real.zero_rpow (ne_of_gt (by positivity : (0 : Real) <
      1 / (2 * (m : Real))))
  unfold APrimeCrossJointSplit.prefixGradient
  simp_rw [hmatrix]
  simp [Gauss.quadVar, Gauss.coordD1]

/-- The accepted raw-QV producer gives the same free-loss bound for the
literal actual prefix gradient on its unchanged common-event/transition
intersection, uniformly for every positive active cell. -/
theorem eventually_actual_prefixGradient_le_free_loss
    {E D c lambda : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      1 ≤ k →
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ omega,
        omega ∈
          (APrimeGeneralMovingCommonSources.commonEvent E D s t
              (zetaSrc lambda) (zetaCtr lambda) (tauG lambda) N ∩
            APrimeCrossJointSplit.transition d E D (deltaWeight lambda) s
              (APrimeGeneralMovingMesh.targetMesh D) N k
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh D) N)) →
        APrimeCrossJointSplit.prefixGradient d E D (deltaWeight lambda) s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N) omega ≤
        freeLossRateConst * (N : Real)^(sourceLoss lambda) *
          (etaT E (s N))^(-(1/2 : Real)) := by
  have hroom := freeLoss_schedule_room hc hlambda hsmall
  rcases hroom with ⟨_, _, _, hzsrc, hzctr, htau, _, hzt, htDw,
    _, hdwC, _, hroom, _⟩
  have hraw :=
    APrimeGeneralMovingTransitionPrefixGradient.eventually_prefixGradient_le_on_smooth_transition
      hE hD hs0 hst ht1 hc hreg hB hzsrc hzctr htau hlambda hzt htDw
      hdwC (by
        dsimp [tauG, sourceLoss, deltaWeight, deltaCap] at hroom ⊢
        nlinarith [hlambda])
  have hrate := eventually_transitionPrefixGradientRate_le_free_loss
    hE hD hs0 hst ht1 hc hreg hlambda hsmall
  filter_upwards [hraw, hrate] with N hrawN hrateN
  intro k hk hkTop omega homega
  exact (hrawN k hk hkTop omega homega).trans (hrateN k hk hkTop)

/-- A same-model witness for the new assumptions and source event: at E=0,
D=60, the admissible loss interval is nonempty and the first positive cell
has a resident of the literal common event eventually. -/
theorem freeLoss_assumptions_satisfiable :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (Gauss.sample d) 0 s ∧
      ∃ lambda : Real, 0 < lambda ∧
        lambda ≤ min (1 / 10000 : Real) (c / 10000) ∧
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
              (zetaSrc lambda) (zetaCtr lambda) (tauG lambda) N ∧
            1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N := by
  obtain ⟨_, _, c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      _hStep, hsource⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  let lambda := min (1 / 20000 : Real) (c / 20000)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min (by norm_num) (div_pos hc (by norm_num))
  have hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000) := by
    refine le_min ?_ ?_
    · dsimp [lambda]
      exact (min_le_left _ _).trans (by norm_num)
    · dsimp [lambda]
      exact (min_le_right _ _).trans (by nlinarith)
  have hsrcpos : 0 < zetaSrc lambda := by
    dsimp [zetaSrc, sourceLoss]
    positivity
  have hctrpos : 0 < zetaCtr lambda := by
    dsimp [zetaCtr, sourceLoss]
    positivity
  have htaupos : 0 < tauG lambda := by
    dsimp [tauG, sourceLoss]
    positivity
  have hdelpos : 0 < deltaWeight lambda := by
    dsimp [deltaWeight]
    exact hlambda
  have hN := hsource (zetaSrc lambda) (zetaCtr lambda) (tauG lambda)
    (deltaWeight lambda) hsrcpos hctrpos htaupos hdelpos
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, lambda, hlambda,
    hsmall, ?_⟩
  filter_upwards [hN] with N hN
  rcases hN with ⟨hwindow, omega, homega, hactive, _hweights⟩
  exact ⟨hwindow, omega, homega, hactive⟩

#print axioms freeLoss_schedule_room
#print axioms freeLossRateConst_pos
#print axioms eventually_transitionPrefixGradientRate_le_free_loss
#print axioms transitionPrefixGradientRate_zero
#print axioms prefixGradient_zero
#print axioms eventually_actual_prefixGradient_le_free_loss
#print axioms freeLoss_assumptions_satisfiable

end
end RBM.APrimeFreeLossPrefixGradient
