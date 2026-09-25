/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingTransitionPrefixGradient
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot

/-!
# T1237: strict exponent for the exact T1029 cross profile

The deterministic profile and its proof are kept at the same T613/T590 scale.
This file sharpens only the final exponent absorption under the T995 schedule.
-/

namespace RBM.APrimeGeneralMovingCrossProfileStrictExponent

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

set_option maxHeartbeats 1000000

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

private noncomputable def profileCap (E : Real) (s : Nat → Real)
    (tauG delta : Real) (N : Nat) (u : Real) : Real :=
  APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG delta N u

/-- An exact copy of the deterministic favorable cross integrand used in T1029. -/
noncomputable def crossProfile (E D : Real) (s t : Nat → Real)
    (zetaSrc tauG deltaWeight deltaCap : Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Real :=
  (2 * Real.sqrt u)⁻¹ *
    APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
      E D s t zetaSrc tauG deltaWeight N k *
    APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) D
      (profileCap E s tauG deltaCap N u) a

private noncomputable def capConst : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)

private noncomputable def transitionCapConst : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)

private noncomputable def absorbedRootConst : Real :=
  Real.sqrt 6 * (1 + 256 * Real.exp 3) +
    Real.sqrt (1200 * capConst^3)

private noncomputable def transitionRawConst : Real :=
  6 + 1200 * transitionCapConst^3

private noncomputable def transitionRootConst : Real :=
  Real.exp 1 * Real.sqrt transitionRawConst

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
    _ ≤ (4 * N^zeta * eta⁻¹) * (N^eps * r^3) := mul_le_mul_of_nonneg_left hm hf
    _ = 4 * N^(zeta + eps) * eta⁻¹ * r^3 := by rw [Real.rpow_add hN]; ring

private theorem margin_to_inv_cubic {A N r e : Real}
    (hA : 0 < A) (hN : 0 < N) (hr : 0 < r)
    (hmargin : N^e * r^(27 : Real) ≤ A) :
    A^(-(1/3 : Real)) ≤ N^(-(e/3)) * r^(-(9 : Real)) := by
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ N^e * r^(27 : Real))
    hmargin (by norm_num : (0 : Real) ≤ 1/3)
  have hleft : (N^e * r^(27 : Real))^(1/3 : Real) =
      N^(e/3) * r^9 := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hr.le _),
      ← Real.rpow_mul hN.le, ← Real.rpow_mul hr.le]
    congr 1
    · ring
    · norm_num
  rw [hleft] at hp
  have hinv := inv_anti₀ (by positivity : 0 < N^(e/3) * r^9) hp
  rw [Real.rpow_neg hA.le, Real.rpow_neg hN.le, Real.rpow_neg hr.le]
  simpa [mul_inv, mul_comm] using hinv

private theorem cap_le_const_mul
    {E zeta tau delta : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hr : 1 ≤ Step2Moment.ratR E s N u) :
    profileCap E s tau delta N u ≤
      capConst * (N : Real)^(tau + 2*delta) *
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
    have hm : 1 ≤ (N : Real)^(2*delta) * Step2Moment.ratR E s N u^4 :=
      by nlinarith [mul_le_mul hd hR4 (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real)^tau * (N : Real)^(2*delta) =
      (N : Real)^(tau + 2*delta) := by rw [Real.rpow_add hn0]
  unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap capConst
  calc
    1 + (N : Real)^tau *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
            Step2Moment.ratR E s N u^4) + 2) ≤
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        ((N : Real)^tau * (N : Real)^(2*delta) *
          Step2Moment.ratR E s N u^4) := by
      have hmain : (N : Real)^tau *
          (9 * Real.exp (Real.sqrt 3) *
            ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
              Step2Moment.ratR E s N u^4)) =
          (9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
            ((N : Real)^tau * (N : Real)^(2*delta) *
              Step2Moment.ratR E s N u^4) := by ring
      rw [mul_add, hmain]
      nlinarith
    _ = _ := by rw [hpow]; ring

private theorem transition_cap_le_const_mul
    {E tau delta : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hr : 1 ≤ Step2Moment.ratR E s N u) :
    APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
        E s tau delta N u ≤
      transitionCapConst * (N : Real)^(tau + 2*delta) *
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
    have hm : 1 ≤ (N : Real)^(2*delta) * Step2Moment.ratR E s N u^4 :=
      by nlinarith [mul_le_mul hd hR4 (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real)^tau * (N : Real)^(2*delta) =
      (N : Real)^(tau + 2*delta) := by rw [Real.rpow_add hn0]
  unfold APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
    transitionCapConst
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
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {eps : Real} (heps : 0 < eps) :
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
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by exact_mod_cast hdim.1
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
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ (B.W N : Real)) _)] using hlogN
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

private theorem power_rate_bound
    {E c zetaSrc tauG delta eps : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hδ : 0 < delta) (hsmall : delta ≤ min 1 (c/100))
    (hzeta : zetaSrc = APrimeGeneralMovingSlotLossSchedule.zetaSrc delta)
    (htau : tauG = APrimeGeneralMovingSlotLossSchedule.tauG delta)
    (heps : eps = delta/100) :
    ∀ᶠ N : Nat in atTop, ∀ u : TimeIcc s t N,
      let r := Step2Moment.ratR E s N (u : Real)
      let eta := etaT E (u : Real)
      let near := APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N (u : Real) +
        2 * (B.W N : Real)⁻¹
      let farW := APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real)
        (APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
          E s tauG (APrimeGeneralMovingSlotLossSchedule.deltaWeight delta) N (u : Real))
      let farCap := APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real)
        (profileCap E s tauG (APrimeGeneralMovingSlotLossSchedule.deltaCap delta) N (u : Real))
      near ≤ 6 * (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 ∧
      farW ≤ (1200 * transitionCapConst^3) *
        (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 ∧
      farCap ≤ (1200 * capConst^3) *
        (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
  have hδc : 100 * delta ≤ c := by
    have h := hsmall.trans (min_le_right 1 (c/100))
    linarith
  have hδ1 : delta ≤ 1 := hsmall.trans (min_le_left 1 (c/100))
  have hcapSchedule := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hsmall
  rcases hcapSchedule with ⟨hdwPos, _, hdcapPos, htauPos, hzetaPos, _, _, hzetaTau,
    htauCap, hcapC, hroom, _, _⟩
  have hepspos : 0 < eps := by rw [heps]; positivity
  have hNear := eventually_cNear2_le hs0 ht1 (eps := eps) hepspos
  have hMargin := hreg.margin hE hst ht1 hc
    (e := c/10) (b := 27) (a := 1) (by positivity) (by norm_num)
    (by field_simp [hc.ne']; norm_num)
  have hScale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  filter_upwards [hNear, hMargin, hScale, d.dim,
    eventually_ge_atTop 1] with N hNearN hMarginN hScaleN hdim hN u
  let r := Step2Moment.ratR E s N (u : Real)
  let eta := etaT E (u : Real)
  let A := B.scale E N (u : Real)
  let Jw := APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
    E s tauG (APrimeGeneralMovingSlotLossSchedule.deltaWeight delta) N (u : Real)
  let Jc := profileCap E s tauG
    (APrimeGeneralMovingSlotLossSchedule.deltaCap delta) N (u : Real)
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
  have hAupper : A ≤ (N : Real) := by
    obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast hdim.1
    change (B.W N : Real) * B.ell N (u : Real) * eta ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hEllS : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have hEllU : 0 < B.ell N (u : Real) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) ((u : Real) : Complex) by linarith)
  have hEllRatio : 0 ≤ B.ell N (u : Real) / B.ell N (s N) := by positivity
  have hEllRatio2 : (B.ell N (u : Real) / B.ell N (s N))^2 ≤ r := by
    dsimp [r]
    exact Step2MomentStep.ratio_sq_le (B := B) (s := s) hE u.2.1 hu1
  have hCnear : Lemma57.cNear2 (B.W N : Real) (B.ell N (u : Real)) ≤
      (N : Real)^eps := by
    have := hNearN u
    simpa [heps] using this
  have hNearRate :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N (u : Real) ≤
        4 * (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    exact near_source_scalar_le hNpos heta
      (Lemma57.cNear2_nonneg (by exact_mod_cast B.W_pos N) hEllU)
      hCnear hEllRatio hr hEllRatio2
  have hWinv : (B.W N : Real)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast B.W_pos N)
  have hbase1 : 1 ≤ (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
    have hpow : 1 ≤ (N : Real)^(zetaSrc+eps) :=
      Real.one_le_rpow hNreal (by rw [hzeta, APrimeGeneralMovingSlotLossSchedule.zetaSrc]; positivity)
    have hetaInv : 1 ≤ eta⁻¹ := (one_le_inv₀ heta).2 heta1
    have hr3 : 1 ≤ r^3 := one_le_pow₀ hr
    have hprod : 1 ≤ (N : Real)^(zetaSrc+eps) * eta⁻¹ := by
      nlinarith [mul_le_mul hpow hetaInv (by positivity) (by positivity)]
    nlinarith [mul_le_mul hprod hr3 (by positivity) (by positivity)]
  have hnear :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N (u : Real) +
        2 * (B.W N : Real)⁻¹ ≤
        6 * (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
    have hbase0 : 0 ≤ (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by positivity
    nlinarith [hNearRate, hWinv, hbase1]
  have hMarginU : (N : Real)^(c/10) * r^(27 : Real) ≤ A := by
    have hm := hMarginN u
    change (N : Real)^(c/10) *
      (etaT E (s N) / etaT E (u : Real))^(27 : Real) ≤
        B.scale E N (u : Real)^(1 : Real) at hm
    have hrEq : r = etaT E (s N) / etaT E (u : Real) := by rfl
    rw [← hrEq, Real.rpow_one] at hm
    simpa [A] using hm
  have htau0 : 0 ≤ tauG := by rw [htau]; exact htauPos.le
  have hdw0 : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight delta := hdwPos.le
  have hcap0 : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaCap delta := hdcapPos.le
  have hWcap : Jw ≤ transitionCapConst * (N : Real)^(
      tauG + 2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight delta) * r^4 := by
    dsimp [Jw, r]
    exact transition_cap_le_const_mul hN htau0 hdw0 hr
  have hCcap : Jc ≤ capConst * (N : Real)^(
      tauG + 2 * APrimeGeneralMovingSlotLossSchedule.deltaCap delta) * r^4 := by
    dsimp [Jc, r]
    exact cap_le_const_mul (zeta := 0) hN htau0 hcap0 hr
  have hWj0 : 0 ≤ Jw := by
    dsimp [Jw, APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap]
    positivity
  have hCj0 : 0 ≤ Jc := by
    dsimp [Jc, profileCap, APrimeGeneralMovingQVProfile.generalMovingBlockCap]
    positivity
  have hFarWRaw := far_scalar_le hApos hNpos hrpos hWj0
    (show 0 ≤ transitionCapConst by unfold transitionCapConst; positivity)
    hMarginU hWcap
  have hFarCRaw := far_scalar_le hApos hNpos hrpos hCj0
    (show 0 ≤ capConst by unfold capConst; positivity)
    hMarginU hCcap
  have hFarWRaw' : A^(-(1/3 : Real)) * Jw^3 ≤
      transitionCapConst^3 * (N : Real)^(
        3 * (tauG + 2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight delta) - c/30) *
        r^3 := by
    dsimp only [Jw] at hFarWRaw
    rw [show c/10/3 = c/30 by ring] at hFarWRaw
    exact hFarWRaw
  have hFarCRaw' : A^(-(1/3 : Real)) * Jc^3 ≤
      capConst^3 * (N : Real)^(
        3 * (tauG + 2 * APrimeGeneralMovingSlotLossSchedule.deltaCap delta) - c/30) *
        r^3 := by
    dsimp only [Jc] at hFarCRaw
    rw [show c/10/3 = c/30 by ring] at hFarCRaw
    exact hFarCRaw
  have hFarW :
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real) Jw ≤
        (1200 * transitionCapConst^3) *
          (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    have hExp : 3 * (tauG + 2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight delta)
        - c/30 ≤ zetaSrc + eps := by
      rw [htau, hzeta, heps,
        APrimeGeneralMovingSlotLossSchedule.tauG,
        APrimeGeneralMovingSlotLossSchedule.zetaSrc,
        APrimeGeneralMovingSlotLossSchedule.deltaWeight]
      nlinarith [hδc]
    have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hExp
    calc
      _ = 1200 * eta⁻¹ *
          (A^(-(1/3 : Real)) *
            (APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
              E s tauG (APrimeGeneralMovingSlotLossSchedule.deltaWeight delta)
              N (u : Real))^3) := by ring
      _ ≤ 1200 * eta⁻¹ *
          (transitionCapConst^3 *
            (N : Real)^(3*(tauG+2*APrimeGeneralMovingSlotLossSchedule.deltaWeight delta)-c/30) *
            r^3) := mul_le_mul_of_nonneg_left hFarWRaw'
              (mul_nonneg (by norm_num) (inv_nonneg.mpr heta.le))
      _ = (1200 * transitionCapConst^3) *
          (N : Real)^(3*(tauG+2*APrimeGeneralMovingSlotLossSchedule.deltaWeight delta)-c/30) *
          eta⁻¹ * r^3 := by ring
      _ = ((1200 * transitionCapConst^3) * eta⁻¹ * r^3) *
          (N : Real)^(3*(tauG+2*APrimeGeneralMovingSlotLossSchedule.deltaWeight delta)-c/30) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by unfold transitionCapConst; positivity)
      _ = _ := by ring
  have hFarC :
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real) Jc ≤
        (1200 * capConst^3) *
          (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    have hExp : 3 * (tauG + 2 * APrimeGeneralMovingSlotLossSchedule.deltaCap delta)
        - c/30 ≤ zetaSrc + eps := by
      rw [htau, hzeta, heps,
        APrimeGeneralMovingSlotLossSchedule.tauG,
        APrimeGeneralMovingSlotLossSchedule.zetaSrc,
        APrimeGeneralMovingSlotLossSchedule.deltaCap]
      nlinarith [hδc]
    have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hExp
    calc
      _ = 1200 * eta⁻¹ * (A^(-(1/3 : Real)) * Jc^3) := by ring
      _ ≤ 1200 * eta⁻¹ *
          (capConst^3 *
            (N : Real)^(3*(tauG+2*APrimeGeneralMovingSlotLossSchedule.deltaCap delta)-c/30) *
            r^3) := by
        exact mul_le_mul_of_nonneg_left hFarCRaw'
          (mul_nonneg (by norm_num) (inv_nonneg.mpr heta.le))
      _ = (1200 * capConst^3) *
          (N : Real)^(3*(tauG+2*APrimeGeneralMovingSlotLossSchedule.deltaCap delta)-c/30) *
          eta⁻¹ * r^3 := by ring
      _ = ((1200 * capConst^3) * eta⁻¹ * r^3) *
          (N : Real)^(3*(tauG+2*APrimeGeneralMovingSlotLossSchedule.deltaCap delta)-c/30) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by unfold capConst; positivity)
      _ = _ := by ring
  exact ⟨hnear, hFarW, hFarC⟩

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

private theorem integral_eta_sqrt_inv_le {E s v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    (etaT E s)⁻¹ * (∫ u in s..v, Real.sqrt u⁻¹) ≤
      2 / (mE E).im := by
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hm : 0 < (mE E).im := mE_im_pos hE
  have heta : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hIntS := APrimeTimeInt.integral_sqrt_inv hs0
  have hIntV := APrimeTimeInt.integral_sqrt_inv (hs0.trans hsv)
  have hbaseSV : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹) volume s v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv (hs0.trans hsv)).mono_set
    rw [Set.uIcc_of_le hsv, Set.uIcc_of_le (hs0.trans hsv)]
    intro u hu
    exact ⟨hs0.trans hu.1, hu.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (APrimeTimeInt.intervalIntegrable_sqrt_inv hs0) hbaseSV
  rw [hIntS, hIntV] at hadd
  have hIntEq : (∫ u in s..v, Real.sqrt u⁻¹) =
      2 * (Real.sqrt v - Real.sqrt s) := by linarith
  rw [hIntEq]
  have hsqrtv : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hsqrts : s ≤ Real.sqrt s := by
    have hsqrts1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1.le
    nlinarith [Real.sqrt_nonneg s, Real.sq_sqrt hs0]
  unfold etaT
  have hdiff : Real.sqrt v - Real.sqrt s ≤ 1 - s := by linarith
  have hbound : 2 * (Real.sqrt v - Real.sqrt s) ≤ 2 * (1 - s) := by nlinarith
  have hden : 0 < (1 - s) * (mE E).im := by positivity
  calc
    _ ≤ (etaT E s)⁻¹ * (2 * (1 - s)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr heta.le)
    _ = 2 / (mE E).im := by
      unfold etaT
      have h1s : 1 - s ≠ 0 := by linarith
      field_simp [h1s, ne_of_gt hm]

private theorem indicator_zero_one_bounds (p : Prop) [Decidable p] :
    0 ≤ (if p then (1 : Real) else 0) ∧ (if p then (1 : Real) else 0) ≤ 1 := by
  by_cases hp : p <;> simp [hp]

private theorem absorbed_root_profile_pointwise_le
    {E D : Real} {s t : Nat → Real} {zetaSrc tauG deltaCap eps : Real}
    {N : Nat} {u v : Real} (a : LoopArg (B.L N) 2)
    (hE : |E| < 2) (hD : 0 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 1 ≤ N) (hu : u ∈ Icc (s N) (t N)) (huv : u ≤ v)
    (hv1 : v < 1) (hzeta0 : 0 ≤ zetaSrc) (heps0 : 0 ≤ eps)
    (hnear : APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
        2 * (B.W N : Real)⁻¹ ≤
      6 * (N : Real)^(zetaSrc+eps) * (etaT E u)⁻¹ *
        Step2Moment.ratR E s N u^3)
    (hfar : APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
        (profileCap E s tauG deltaCap N u) ≤
      (1200 * capConst^3) * (N : Real)^(zetaSrc+eps) *
        (etaT E u)⁻¹ * Step2Moment.ratR E s N u^3)
    (hXi : Step2.xiK (B.L N) (B.W N : Real) (mE E).im ≤ (N : Real)^eps) :
    APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (profileCap E s tauG deltaCap N u) a ≤
      absorbedRootConst * (N : Real)^(zetaSrc/2 + 3*eps/2) *
        etaT E (s N)^(-(1/2 : Real)) *
        Step2Moment.ratR E s N v^(-(2 : Real)) := by
  classical
  let R := Step2Moment.ratR E s N u
  let V := Step2Moment.ratR E s N v
  let S := etaT E (s N)
  let U := etaT E u
  let q := zetaSrc + eps
  let near := APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
    2 * (B.W N : Real)⁻¹
  let far := APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
    (profileCap E s tauG deltaCap N u)
  let chi : Real := if (zdist (B.L N) (a 0 - a 1) : Real) <=
      6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0
  let leakage := (B.W N : Real)^(-D)
  let xi := Step2.xiK (B.L N) (B.W N : Real) (mE E).im
  let Kfar := 1200 * capConst^3
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : Real) := by linarith
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  have hS : 0 < S := by dsimp [S]; exact Step2.etaT_pos' hE hs1
  have hU : 0 < U := by dsimp [U]; exact Step2.etaT_pos' hE hu1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hu.1 hu1
  have hR : 0 < R := by linarith
  have hV : 0 < V := by
    dsimp [V]
    exact Step2Moment.ratR_pos hE ((hu.1.trans huv).trans_lt hv1) hv1
  have hRatio : R = S / U := by
    dsimp [R, S, U, Step2Moment.ratR]
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hNpow1 : 1 ≤ (N : Real)^eps := by
    exact Real.one_le_rpow hNreal heps0
  have hNearRoot : R^(-(2 : Real)) * Real.sqrt near ≤
      Real.sqrt 6 * (N : Real)^(q/2) * S^(-(1/2 : Real)) := by
    have hRoot := Real.sqrt_le_sqrt (by simpa [near, q] using hnear)
    calc
      _ ≤ R^(-(2 : Real)) *
          Real.sqrt (6 * (N : Real)^q * U⁻¹ * R^3) :=
        mul_le_mul_of_nonneg_left hRoot (by positivity)
      _ = _ := root_transport_cancel hS hU hRatio (by norm_num) hNpos
  have hFarRoot : R^(-(2 : Real)) * Real.sqrt far ≤
      Real.sqrt Kfar * (N : Real)^(q/2) * S^(-(1/2 : Real)) := by
    have hRoot := Real.sqrt_le_sqrt (by simpa [far, Kfar, q] using hfar)
    calc
      _ ≤ R^(-(2 : Real)) *
          Real.sqrt (Kfar * (N : Real)^q * U⁻¹ * R^3) :=
        mul_le_mul_of_nonneg_left hRoot (by positivity)
      _ = _ := root_transport_cancel hS hU hRatio
        (by unfold Kfar capConst; positivity) hNpos
  have hchi0 : 0 ≤ chi := by
    exact (indicator_zero_one_bounds _).1
  have hchi1 : chi ≤ 1 := by
    exact (indicator_zero_one_bounds _).2
  have hW1 : 1 ≤ (B.W N : Real) := by exact_mod_cast B.W_pos N
  have hleak0 : 0 ≤ leakage := by dsimp [leakage]; positivity
  have hleak1 : leakage ≤ 1 := by
    dsimp [leakage]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith [hD])
  have hXi0 : 0 ≤ xi := by dsimp [xi]; exact Step2.xiK_nonneg _ _ _
  have hXiCoef : xi * chi + 256 * Real.exp 3 * leakage ≤
      (1 + 256 * Real.exp 3) * (N : Real)^eps := by
    have hprod := mul_le_mul_of_nonneg_left hchi1 hXi0
    have hleak := mul_le_mul_of_nonneg_left hleak1
      (by positivity : 0 ≤ 256 * Real.exp 3)
    have hXi' : xi ≤ (N : Real)^eps := hXi
    have hprod' : xi * chi ≤ xi := by nlinarith [hprod]
    have hleak' : 256 * Real.exp 3 * leakage ≤ 256 * Real.exp 3 := by
      nlinarith [hleak]
    calc
      _ ≤ xi + 256 * Real.exp 3 := add_le_add hprod' hleak'
      _ ≤ (N : Real)^eps + 256 * Real.exp 3 * (N : Real)^eps :=
        add_le_add hXi' (by
          calc
            _ = 256 * Real.exp 3 * 1 := by ring
            _ ≤ 256 * Real.exp 3 * (N : Real)^eps :=
              mul_le_mul_of_nonneg_left hNpow1
                (by positivity : 0 ≤ 256 * Real.exp 3))
      _ = _ := by ring
  have hXiCoef0 : 0 ≤ xi * chi + 256 * Real.exp 3 * leakage := by positivity
  have hNearBound0 : 0 ≤ Real.sqrt 6 *
      (N : Real)^(q/2) * S^(-(1/2 : Real)) := by positivity
  have hFarBound0 : 0 ≤ Real.sqrt Kfar *
      (N : Real)^(q/2) * S^(-(1/2 : Real)) := by positivity
  have hNearTerm : R^(-(2 : Real)) *
      (Real.sqrt near * (xi * chi + 256 * Real.exp 3 * leakage)) ≤
      (Real.sqrt 6 * (1 + 256 * Real.exp 3)) *
        (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) := by
    have hprod := mul_le_mul hNearRoot hXiCoef hXiCoef0 hNearBound0
    have hpow : (N : Real)^(q/2) * (N : Real)^eps =
        (N : Real)^(q/2+eps) := by rw [← Real.rpow_add hNpos]
    calc
      _ = (R^(-(2 : Real)) * Real.sqrt near) *
          (xi * chi + 256 * Real.exp 3 * leakage) := by ring
      _ ≤ _ := by
        calc
          _ ≤ (Real.sqrt 6 * (N : Real)^(q/2) * S^(-(1/2 : Real))) *
              ((1 + 256 * Real.exp 3) * (N : Real)^eps) := hprod
          _ = _ := by
            calc
              _ = (Real.sqrt 6 * (1 + 256 * Real.exp 3)) *
                  ((N : Real)^(q/2) * (N : Real)^eps) * S^(-(1/2 : Real)) := by ring
              _ = _ := by rw [hpow]
  have hFarTerm : R^(-(2 : Real)) *
      (Real.sqrt far * xi) ≤ Real.sqrt Kfar *
        (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) := by
    have hprod := mul_le_mul hFarRoot hXi hXi0 hFarBound0
    have hpow : (N : Real)^(q/2) * (N : Real)^eps =
        (N : Real)^(q/2+eps) := by rw [← Real.rpow_add hNpos]
    calc
      _ = (R^(-(2 : Real)) * Real.sqrt far) * xi := by ring
      _ ≤ _ := by
        calc
          _ ≤ (Real.sqrt Kfar * (N : Real)^(q/2) * S^(-(1/2 : Real))) *
              (N : Real)^eps := hprod
          _ = _ := by
            calc
              _ = Real.sqrt Kfar *
                  ((N : Real)^(q/2) * (N : Real)^eps) * S^(-(1/2 : Real)) := by ring
              _ = _ := by rw [hpow]
  have hsum := add_le_add hNearTerm hFarTerm
  have hsumFactor :
      (Real.sqrt 6 * (1 + 256 * Real.exp 3)) *
          (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) +
        Real.sqrt Kfar * (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) =
      absorbedRootConst * (N : Real)^(zetaSrc/2+3*eps/2) *
        S^(-(1/2 : Real)) := by
    rw [show q/2+eps = zetaSrc/2+3*eps/2 by dsimp [q]; ring]
    unfold absorbedRootConst
    ring
  have hV0 : 0 ≤ V^(-(2 : Real)) := by positivity
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  change R^(-(2 : Real)) * V^(-(2 : Real)) *
      (Real.sqrt near * (xi * chi + 256 * Real.exp 3 * leakage) +
        Real.sqrt far * xi) ≤ _
  calc
    _ = V^(-(2 : Real)) *
        (R^(-(2 : Real)) *
            (Real.sqrt near * (xi * chi + 256 * Real.exp 3 * leakage)) +
          R^(-(2 : Real)) * (Real.sqrt far * xi)) := by ring
    _ ≤ V^(-(2 : Real)) *
        (Real.sqrt 6 * (1 + 256 * Real.exp 3) *
            (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) +
          Real.sqrt Kfar * (N : Real)^(q/2+eps) * S^(-(1/2 : Real))) :=
      mul_le_mul_of_nonneg_left hsum hV0
    _ = V^(-(2 : Real)) *
        ((Real.sqrt 6 * (1 + 256 * Real.exp 3) + Real.sqrt Kfar) *
          (N : Real)^(q/2+eps) * S^(-(1/2 : Real))) := by ring
    _ = V^(-(2 : Real)) *
        (absorbedRootConst * (N : Real)^(zetaSrc/2+3*eps/2) *
          S^(-(1/2 : Real))) := by
      rw [show q/2+eps = zetaSrc/2+3*eps/2 by dsimp [q]; ring]
      unfold absorbedRootConst
      ring
    _ = _ := by dsimp [V, S]; ring

private theorem transitionPrefixGradientRate_pointwise_bound
    {E D : Real} {s t : Nat → Real} {zetaSrc tauG deltaWeight deltaCap eps : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 1 ≤ N) (hk : k ≤ cutNetTop s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    (hdw0 : 0 ≤ deltaWeight) (heps0 : 0 ≤ eps)
    (hpower : ∀ u : TimeIcc s t N,
      let r := Step2Moment.ratR E s N (u : Real)
      let eta := etaT E (u : Real)
      let near := APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N (u : Real) +
        2 * (B.W N : Real)⁻¹
      let farW := APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real)
        (APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
          E s tauG deltaWeight N (u : Real))
      near ≤ 6 * (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 ∧
      farW ≤ (1200 * transitionCapConst^3) *
        (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3) :
    APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t zetaSrc tauG deltaWeight N k ≤
      transitionRootConst * (N : Real)^((zetaSrc+eps)/2) *
        etaT E (s N)^(-(1/2 : Real)) := by
  classical
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let S := etaT E (s N)
  let q := zetaSrc + eps
  let bound := Real.sqrt transitionRawConst * (N : Real)^(q/2) * S^(-(1/2 : Real))
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hv : cutNetPt s mesh N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : cutNetPt s mesh N k < 1 := hv.2.trans_lt (ht1 N)
  have hS : 0 < S := by dsimp [S]; exact Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hbound0 : 0 ≤ bound := by positivity
  have htheta : 1 ≤ APrimeSmoothWeightActual.threshold deltaWeight N := by
    unfold APrimeSmoothWeightActual.threshold
    have hpow : 1 ≤ (N : Real)^(2*deltaWeight) := Real.one_le_rpow hNreal (by positivity)
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith [mul_le_mul hpow he1 (by positivity) (by positivity)]
  have hthetaPos : 0 < APrimeSmoothWeightActual.threshold deltaWeight N := by
    exact APrimeSmoothWeightActual.threshold_pos (by omega)
  have hThetaInv : 0 < (APrimeSmoothWeightActual.threshold deltaWeight N)⁻¹ :=
    inv_pos.mpr hthetaPos
  have hStoredUniform : ∀ j < k,
      APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s zetaSrc tauG
        deltaWeight N (cutNetPt s mesh N j) ≤ bound := by
    intro j hj
    let uj := cutNetPt s mesh N j
    have huPrefix : uj ∈ Icc (s N) (cutNetPt s mesh N k) := by
      exact Step2Bootstrap.cutNetPt_mem_Icc
        (APrimeGeneralMovingMesh.targetMesh_pos D N) hj.le
    have huWindow : uj ∈ Icc (s N) (t N) :=
      ⟨huPrefix.1, huPrefix.2.trans hv.2⟩
    let uu : TimeIcc s t N := ⟨uj, huWindow⟩
    have hR1 : 1 ≤ Step2Moment.ratR E s N uj :=
      Step2Moment.one_le_ratR hE huWindow.1 (huWindow.2.trans_lt (ht1 N))
    have hRpos : 0 < Step2Moment.ratR E s N uj := by linarith
    have hU : 0 < etaT E uj :=
      Step2.etaT_pos' hE (huWindow.2.trans_lt (ht1 N))
    have hRatio : Step2Moment.ratR E s N uj = S / etaT E uj := by
      dsimp [S, Step2Moment.ratR]
    rcases hpower uu with ⟨hnear, hfar⟩
    have hraw :
        APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
            E s zetaSrc tauG deltaWeight N uj ≤
          transitionRawConst * (N : Real)^q * (etaT E uj)⁻¹ *
            Step2Moment.ratR E s N uj^3 := by
      unfold APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
      calc
        _ ≤ 6 * (N : Real)^q * (etaT E uj)⁻¹ *
              Step2Moment.ratR E s N uj^3 +
            (1200 * transitionCapConst^3) * (N : Real)^q *
              (etaT E uj)⁻¹ * Step2Moment.ratR E s N uj^3 :=
          add_le_add (by simpa [q] using hnear) (by simpa [q] using hfar)
        _ = _ := by unfold transitionRawConst; ring
    have hRoot : Step2Moment.ratR E s N uj^(-(2 : Real)) *
        Real.sqrt (APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
          E s zetaSrc tauG deltaWeight N uj) ≤ bound := by
      have hsqrt := Real.sqrt_le_sqrt (by simpa using hraw)
      have htransport := root_transport_cancel (a := S) (b := etaT E uj)
        (r := Step2Moment.ratR E s N uj) (C := transitionRawConst)
        (N := (N : Real)) (q := q) hS hU hRatio
        (show 0 < transitionRawConst by
          unfold transitionRawConst transitionCapConst
          positivity) hNpos
      have hRinv : Step2Moment.ratR E s N uj^(-(2 : Real)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
      calc
        _ ≤ Step2Moment.ratR E s N uj^(-(2 : Real)) *
          Real.sqrt (transitionRawConst * (N : Real)^q *
            (etaT E uj)⁻¹ * Step2Moment.ratR E s N uj^3) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = bound := htransport
    have hinner :
        (Step2Moment.ratR E s N uj^4)⁻¹ *
          Real.sqrt (APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
            E s zetaSrc tauG deltaWeight N uj) ≤ bound := by
      have hInv4 : (Step2Moment.ratR E s N uj^(4 : Nat))⁻¹ =
          Real.rpow (Step2Moment.ratR E s N uj) (-(4 : Real)) := by
        calc
          (Step2Moment.ratR E s N uj^(4 : Nat))⁻¹ =
              (Real.rpow (Step2Moment.ratR E s N uj) (4 : Real))⁻¹ := by
                rw [← Real.rpow_natCast]
                norm_num
          _ = Real.rpow (Step2Moment.ratR E s N uj) (-(4 : Real)) := by
                exact (Real.rpow_neg hRpos.le (4 : Real)).symm
      have hpow :
            Real.rpow (Step2Moment.ratR E s N uj) (-(4 : Real)) =
            Step2Moment.ratR E s N uj^(-(2 : Real)) *
              Step2Moment.ratR E s N uj^(-(2 : Real)) := by
        rw [← Real.rpow_add hRpos]
        congr 1
        ring
      have hRinv : Step2Moment.ratR E s N uj^(-(2 : Real)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
      calc
        _ = Step2Moment.ratR E s N uj^(-(2 : Real)) *
            (Step2Moment.ratR E s N uj^(-(2 : Real)) *
              Real.sqrt (APrimeGeneralMovingTransitionPrefixGradient.transitionRawCoordRate
                E s zetaSrc tauG deltaWeight N uj)) := by rw [hInv4, hpow]; ring
        _ ≤ Step2Moment.ratR E s N uj^(-(2 : Real)) * bound :=
          mul_le_mul_of_nonneg_left hRoot (by positivity)
        _ ≤ bound := by
          calc
            _ ≤ 1 * bound := mul_le_mul_of_nonneg_right hRinv hbound0
            _ = bound := by ring
    have hstored :
        APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s zetaSrc tauG
          deltaWeight N uj ≤ bound := by
      unfold APrimeGeneralMovingTransitionPrefixGradient.storedRootRate
      apply (div_le_iff₀ hthetaPos).2
      calc
        _ ≤ bound := hinner
        _ ≤ bound * APrimeSmoothWeightActual.threshold deltaWeight N :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left htheta hbound0
    simpa [uj] using hstored
  have htermUniform : ∀ j < k,
      Real.sqrt (cutNetPt s mesh N j) *
        APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s zetaSrc tauG
          deltaWeight N (cutNetPt s mesh N j) ≤ bound := by
    intro j hj
    have huPrefix : cutNetPt s mesh N j ∈ Icc (s N) (cutNetPt s mesh N k) :=
      Step2Bootstrap.cutNetPt_mem_Icc (APrimeGeneralMovingMesh.targetMesh_pos D N) hj.le
    have hu0 : 0 ≤ cutNetPt s mesh N j := (hs0 N).trans huPrefix.1
    have hu1 : cutNetPt s mesh N j ≤ 1 :=
      huPrefix.2.trans hv.2 |>.trans (ht1 N).le
    have hsqrt : Real.sqrt (cutNetPt s mesh N j) ≤ 1 := Real.sqrt_le_one.2 hu1
    have hstored0 : 0 ≤
        APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s zetaSrc tauG
          deltaWeight N (cutNetPt s mesh N j) := by
      unfold APrimeGeneralMovingTransitionPrefixGradient.storedRootRate
      positivity
    calc
      _ ≤ 1 * bound := mul_le_mul hsqrt (hStoredUniform j hj) hstored0 (by norm_num)
      _ = bound := by ring
  unfold APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
  split_ifs with hkpos
  · have hsup : (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hkpos⟩
        (fun j => Real.sqrt (cutNetPt s mesh N j) *
          APrimeGeneralMovingTransitionPrefixGradient.storedRootRate E s
            zetaSrc tauG deltaWeight N (cutNetPt s mesh N j)) ≤ bound := by
      apply Finset.sup'_le
      intro j hj
      exact htermUniform j (Finset.mem_range.mp hj)
    calc
      _ ≤ Real.exp 1 * bound := mul_le_mul_of_nonneg_left hsup (Real.exp_pos 1).le
      _ = transitionRootConst * (N : Real)^((zetaSrc+eps)/2) *
          etaT E (s N)^(-(1/2 : Real)) := by
        dsimp only [transitionRootConst, bound, S, q, transitionRawConst]
        ring
  · have hk0 : k = 0 := by omega
    simp
    unfold transitionRootConst transitionRawConst transitionCapConst
    positivity

private theorem continuousOn_absorbedRootProfile
    {E zetaSrc tauG deltaCap : Real} {s : Nat → Real} {N : Nat}
    {v D : Real} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (a : LoopArg (B.L N) 2) :
    ContinuousOn
      (fun u => APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
        zetaSrc N u v D (profileCap E s tauG deltaCap N u) a)
      (Icc (s N) v) := by
  let I : Set Real := Icc (s N) v
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    unfold etaT
    fun_prop
  have hEllPos : ∀ u ∈ I, 0 < B.ell N u := by
    intro u hu
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N)
        ((hs0 N).trans hu.1) (hu.2.trans_lt hv1))
  have hEtaPos : ∀ u ∈ I, 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hInvEll : ContinuousOn (fun u => (B.ell N u)⁻¹) I :=
    hEll.inv₀ (fun u hu => (hEllPos u hu).ne')
  have hInvEta : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    unfold Step2Moment.ratR
    exact ContinuousOn.div continuousOn_const hEta
      (fun u hu => (hEtaPos u hu).ne')
  have hRatPos : ∀ u ∈ I, 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE
      (hsv.trans_lt hv1) (hu.2.trans_lt hv1)
  have hRatNeg : ContinuousOn (fun u =>
      Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (hRatPos u hu).ne')
  have hJ : ContinuousOn (fun u => profileCap E s tauG deltaCap N u) I := by
    unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap
    exact continuousOn_const.add
      (continuousOn_const.mul
        ((continuousOn_const.mul
          (continuousOn_const.mul (hRat.pow 4))).add continuousOn_const))
  have hNear : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
        2 * (B.W N : Real)⁻¹) I := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate Lemma57.cNear2
    exact ((((continuousOn_const.mul hInvEta).mul
      ((continuousOn_const.add (continuousOn_const.mul hInvEll)).mul
        continuousOn_const)).mul ((hEll.div_const _).pow 5)).add
          continuousOn_const)
  have hScale : ContinuousOn (fun u => B.scale E N u) I := by
    unfold Band.scale
    exact (continuousOn_const.mul hEll).mul hEta
  have hScalePos : ∀ u ∈ I, 0 < B.scale E N u := by
    intro u hu
    have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
    change 0 < (B.W N : Real) * B.ell N u * etaT E u
    exact mul_pos (mul_pos hW (hEllPos u hu)) (hEtaPos u hu)
  have hScaleNeg : ContinuousOn (fun u =>
      B.scale E N u ^ (-(1 / 3 : Real))) I :=
    hScale.rpow_const (fun u hu => Or.inl (hScalePos u hu).ne')
  have hFar : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
        (profileCap E s tauG deltaCap N u)) I := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    exact ((continuousOn_const.mul hInvEta).mul hScaleNeg).mul (hJ.pow 3)
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  exact (hRatNeg.mul continuousOn_const).mul
    ((hNear.sqrt.mul continuousOn_const).add
      (hFar.sqrt.mul continuousOn_const))

private theorem intervalIntegrable_crossProfile
    {E D : Real} {s t : Nat → Real} {zetaSrc tauG deltaWeight deltaCap : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (B.L N) 2) :
    let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
    IntervalIntegrable (crossProfile E D s t zetaSrc tauG deltaWeight deltaCap
      N k a) volume (s N) v := by
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hBase : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹) volume
      (s N) v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
    rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
    intro u hu
    exact ⟨(hs0 N).trans hu.1, hu.2⟩
  have hFactor : ContinuousOn (fun u =>
      (1/2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a) (Icc (s N) v) := by
    exact continuousOn_const.mul
      (continuousOn_absorbedRootProfile (E := E) (zetaSrc := zetaSrc)
        (tauG := tauG) (deltaCap := deltaCap) (s := s) (N := N)
        (v := v) (D := D) hE hs0 hv.1 hv1 a)
  have hinv : ∀ u : Real,
      (2 * Real.sqrt u)⁻¹ = (Real.sqrt u)⁻¹ / 2 := by
    intro u
    rw [mul_inv_rev]
    norm_num
    ring
  change IntervalIntegrable (fun u =>
      (2 * Real.sqrt u)⁻¹ *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a) volume (s N) v
  have hfun : (fun u => (2 * Real.sqrt u)⁻¹ *
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t zetaSrc tauG deltaWeight N k *
      APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (profileCap E s tauG deltaCap N u) a) =
      (fun u => Real.sqrt u⁻¹ * ((1/2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a)) := by
    funext u
    rw [hinv u]
    rw [← Real.sqrt_inv u]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hfun]
  exact hBase.mul_continuousOn (by simpa only [Set.uIcc_of_le hv.1] using hFactor)

/-- The fixed `E` constant in the deterministic cross-profile budget. -/
noncomputable def crossProfileBudgetConst (E : Real) : Real :=
  transitionRootConst * absorbedRootConst / (mE E).im

/-- Integrate the literal T613 transition-prefix rate times the full T606
absorbed root profile on each active target-mesh cell.  The T995 loss schedule
leaves a strict exponent margin below `5δ/32`, while the endpoint transport
factor `ratR(v)⁻²` is retained. -/
theorem eventually_integral_crossProfile_le_delta_eighth
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 0 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (B.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        (∫ u in (s N)..v,
          crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) ≤
          crossProfileBudgetConst E * (N : Real)^(δ/8) *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
  let zetaSrc := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ
  let tauG := APrimeGeneralMovingSlotLossSchedule.tauG δ
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  let deltaCap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  let eps : Real := δ / 100
  let alpha : Real := zetaSrc + 2*eps
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps0 : 0 ≤ eps := heps.le
  have hdw0 : 0 ≤ deltaWeight := by
    dsimp [deltaWeight, APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hzeta0 : 0 ≤ zetaSrc := by
    dsimp [zetaSrc, APrimeGeneralMovingSlotLossSchedule.zetaSrc]
    positivity
  have hpowerEvent := power_rate_bound hE hc hreg hs0 hst ht1 hδ hδsmall
    (zetaSrc := zetaSrc) (tauG := tauG) (delta := δ) (eps := eps)
    rfl rfl rfl
  have htransitionPowerEvent : ∀ᶠ N : Nat in atTop, ∀ u : TimeIcc s t N,
      let r := Step2Moment.ratR E s N (u : Real)
      let eta := etaT E (u : Real)
      let near := APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N (u : Real) +
        2 * (B.W N : Real)⁻¹
      let farW := APrimeGeneralMovingQVAbsorption.absorbedFarRate E N (u : Real)
        (APrimeGeneralMovingTransitionPrefixGradient.transitionBlockCap
          E s tauG deltaWeight N (u : Real))
      near ≤ 6 * (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 ∧
      farW ≤ (1200 * transitionCapConst^3) *
        (N : Real)^(zetaSrc+eps) * eta⁻¹ * r^3 := by
    filter_upwards [hpowerEvent] with N hN u
    exact ⟨(hN u).1, (hN u).2.1⟩
  have hxiEvent := Step2FarInputs.eventually_xiK_le B (mE E).im heps
  have hExponent : alpha < δ/8 := by
    dsimp [alpha, eps, zetaSrc, APrimeGeneralMovingSlotLossSchedule.zetaSrc]
    nlinarith [hδ]
  have hConstPos : 0 < crossProfileBudgetConst E := by
    unfold crossProfileBudgetConst transitionRootConst transitionRawConst
      transitionCapConst absorbedRootConst capConst
    exact div_pos (mul_pos (by positivity) (by positivity)) (mE_im_pos hE)
  have hTransitionConstPos : 0 < transitionRootConst := by
    unfold transitionRootConst transitionRawConst transitionCapConst
    positivity
  have hAbsorbedConstPos : 0 < absorbedRootConst := by
    unfold absorbedRootConst capConst
    positivity
  filter_upwards [hpowerEvent, htransitionPowerEvent, hxiEvent,
      eventually_ge_atTop 1]
    with N hpower htransitionPower hxi hN
  intro k hk a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hN0 : (0 : Real) ≤ N := by linarith
  have hS : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hV : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hv1
  have hTbound :
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k ≤
        transitionRootConst * (N : Real)^((zetaSrc+eps)/2) *
          etaT E (s N)^(-(1/2 : Real)) := by
    exact transitionPrefixGradientRate_pointwise_bound
      (E := E) (D := D) (s := s) (t := t) (zetaSrc := zetaSrc)
      (tauG := tauG) (deltaWeight := deltaWeight) (deltaCap := deltaCap)
      (eps := eps) (N := N) (k := k) hE hs0 hst ht1 hN hk
      hdw0 heps0 htransitionPower
  have hT0 := APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
    E D s t zetaSrc tauG deltaWeight N k
  have hTbound0 : 0 ≤ transitionRootConst * (N : Real)^((zetaSrc+eps)/2) *
      etaT E (s N)^(-(1/2 : Real)) := by
    exact mul_nonneg (mul_nonneg hTransitionConstPos.le
      (Real.rpow_nonneg hN0 _)) (Real.rpow_nonneg hS.le _)
  have hXiN : Step2.xiK (B.L N) (B.W N : Real) (mE E).im ≤ (N : Real)^eps := hxi
  have hXi0 : 0 ≤ Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hCrossInt : IntervalIntegrable
      (crossProfile E D s t zetaSrc tauG deltaWeight deltaCap N k a)
      volume (s N) v := by
    simpa only [v] using intervalIntegrable_crossProfile
      hE hs0 hst ht1 hk a
  have hBaseInt : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹)
      volume (s N) v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
    rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
    intro u hu
    exact ⟨(hs0 N).trans hu.1, hu.2⟩
  let coeff := (transitionRootConst * absorbedRootConst / 2) *
    (N : Real)^alpha * (etaT E (s N))⁻¹ *
      Step2Moment.ratR E s N v^(-(2 : Real))
  have hcoeff0 : 0 ≤ coeff := by
    dsimp [coeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg hTransitionConstPos.le hAbsorbedConstPos.le)
            (by norm_num))
          (Real.rpow_nonneg hN0 _))
        (inv_nonneg.mpr hS.le))
      (Real.rpow_nonneg hV.le _)
  have hpoint : ∀ u ∈ Icc (s N) v,
      crossProfile E D s t zetaSrc tauG deltaWeight deltaCap N k a u ≤
        coeff * Real.sqrt u⁻¹ := by
    intro u hu
    have huWindow : u ∈ Icc (s N) (t N) :=
      ⟨hu.1, hu.2.trans hv.2⟩
    let uu : TimeIcc s t N := ⟨u, huWindow⟩
    rcases hpower uu with ⟨hnear, hfarW, hfarCap⟩
    have htransition := transitionPrefixGradientRate_pointwise_bound
      (E := E) (D := D) (s := s) (t := t) (zetaSrc := zetaSrc)
      (tauG := tauG) (deltaWeight := deltaWeight) (deltaCap := deltaCap)
      (eps := eps) (N := N) (k := k) hE hs0 hst ht1 hN hk
      hdw0 heps0 htransitionPower
    have hnear' : APrimeGeneralMovingQVAbsorption.nearSourceRate
          E s zetaSrc N u + 2 * (B.W N : Real)⁻¹ ≤
        6 * (N : Real)^(zetaSrc+eps) * (etaT E u)⁻¹ *
          Step2Moment.ratR E s N u^3 := by simpa using hnear
    have hfarCap' : APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
        (profileCap E s tauG deltaCap N u) ≤
        (1200 * capConst^3) * (N : Real)^(zetaSrc+eps) *
          (etaT E u)⁻¹ * Step2Moment.ratR E s N u^3 := by
      simpa [profileCap] using hfarCap
    have hprofile := absorbed_root_profile_pointwise_le (E := E) (D := D)
      (s := s) (t := t) (zetaSrc := zetaSrc) (tauG := tauG)
      (deltaCap := deltaCap) (eps := eps) (N := N) (u := u) (v := v) a
      hE hD hs0 hst ht1 hN huWindow hu.2 hv1 hzeta0 heps0 hnear' hfarCap' hXiN
    have hprofile0 : 0 ≤
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a := by
      have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
      have hU : 0 < etaT E u := Step2.etaT_pos' hE hu1
      have hRu : 0 < Step2Moment.ratR E s N u :=
        Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hu1
      have hscale : 0 < B.scale E N u := by
        change 0 < (B.W N : Real) * B.ell N u * etaT E u
        have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
        have hEll : 0 < B.ell N u := zero_lt_one.trans_le
          (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans huWindow.1) hu1)
        positivity
      have hnear0 : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
          2 * (B.W N : Real)⁻¹ := by
        unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
        have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
        have hEllU : 0 < B.ell N u := zero_lt_one.trans_le
          (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans huWindow.1) hu1)
        have hEllS : 0 < B.ell N (s N) := zero_lt_one.trans_le
          (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
            ((hst N).trans_lt (ht1 N)))
        have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
        have hCNear : 0 ≤ Lemma57.cNear2 (B.W N : Real) (B.ell N u) :=
          Lemma57.cNear2_nonneg hW1 hEllU
        have hEta : 0 < etaT E u := Step2.etaT_pos' hE hu1
        positivity
      have hfar0 : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
          (profileCap E s tauG deltaCap N u) := by
        unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
        have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
        have hEll : 0 < B.ell N u := zero_lt_one.trans_le
          (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans huWindow.1)
            (huWindow.2.trans_lt (ht1 N)))
        have hJ : 0 ≤ profileCap E s tauG deltaCap N u := by
          unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap
          positivity
        have hEta : 0 < etaT E u := Step2.etaT_pos' hE (huWindow.2.trans_lt (ht1 N))
        have hscale' : 0 < B.scale E N u := by
          change 0 < (B.W N : Real) * B.ell N u * etaT E u
          positivity
        have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : Real) ≤
            6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
          split_ifs <;> norm_num
        positivity
      unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
      positivity
    have hProduct :
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k *
          APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
            (profileCap E s tauG deltaCap N u) a ≤
          transitionRootConst * absorbedRootConst * (N : Real)^alpha *
            (etaT E (s N))⁻¹ * Step2Moment.ratR E s N v^(-(2 : Real)) := by
      have hNpow : (N : Real)^((zetaSrc+eps)/2) *
          (N : Real)^(zetaSrc/2+3*eps/2) = (N : Real)^alpha := by
        rw [← Real.rpow_add hNpos]
        congr 1
        dsimp [alpha]
        ring
      have hSpow : (etaT E (s N))^(-(1/2 : Real)) *
          (etaT E (s N))^(-(1/2 : Real)) = (etaT E (s N))⁻¹ := by
        rw [← Real.rpow_add hS]
        rw [show -(1/2 : Real) + -(1/2 : Real) = -1 by norm_num]
        rw [Real.rpow_neg hS.le, Real.rpow_one]
      calc
        _ ≤ (transitionRootConst * (N : Real)^((zetaSrc+eps)/2) *
              etaT E (s N)^(-(1/2 : Real))) *
            (absorbedRootConst * (N : Real)^(zetaSrc/2+3*eps/2) *
              etaT E (s N)^(-(1/2 : Real)) *
              Step2Moment.ratR E s N v^(-(2 : Real))) :=
          mul_le_mul htransition hprofile hprofile0 hTbound0
        _ = _ := by rw [← hNpow, ← hSpow]; ring
    have hinv : (2 * Real.sqrt u)⁻¹ = Real.sqrt u⁻¹ / 2 := by
      rw [mul_inv_rev]
      norm_num
      ring
    have hinv0 : 0 ≤ Real.sqrt u⁻¹ := by positivity
    calc
      _ = Real.sqrt u⁻¹ * ((1/2 : Real) *
          (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k *
          APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
            (profileCap E s tauG deltaCap N u) a)) := by
        unfold crossProfile
        rw [hinv]
        ring
      _ ≤ Real.sqrt u⁻¹ * ((1/2 : Real) *
          (transitionRootConst * absorbedRootConst * (N : Real)^alpha *
            (etaT E (s N))⁻¹ * Step2Moment.ratR E s N v^(-(2 : Real)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hProduct (by norm_num)) hinv0
      _ = coeff * Real.sqrt u⁻¹ := by dsimp [coeff]; ring
  have hDomInt : IntervalIntegrable (fun u : Real => coeff * Real.sqrt u⁻¹)
      volume (s N) v := hBaseInt.const_mul coeff
  have hmono := intervalIntegral.integral_mono_on hv.1 hCrossInt hDomInt hpoint
  have hIntEta := integral_eta_sqrt_inv_le hE (hs0 N) hv.1 hv1
  have hIntegralBound :
      (∫ u in (s N)..v,
        crossProfile E D s t zetaSrc tauG deltaWeight deltaCap N k a u) ≤
        (transitionRootConst * absorbedRootConst / (mE E).im) *
          (N : Real)^alpha * Step2Moment.ratR E s N v^(-(2 : Real)) := by
    have hcoefficient : 0 ≤
        (transitionRootConst * absorbedRootConst / 2) *
          (N : Real)^alpha * Step2Moment.ratR E s N v^(-(2 : Real)) := by
      positivity
    calc
      _ ≤ ∫ u in (s N)..v, coeff * Real.sqrt u⁻¹ := hmono
      _ = coeff * (∫ u in (s N)..v, Real.sqrt u⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (transitionRootConst * absorbedRootConst / 2) *
          (N : Real)^alpha * Step2Moment.ratR E s N v^(-(2 : Real)) *
            ((etaT E (s N))⁻¹ * (∫ u in (s N)..v, Real.sqrt u⁻¹)) := by
        dsimp [coeff]
        ring
      _ ≤ (transitionRootConst * absorbedRootConst / 2) *
          (N : Real)^alpha * Step2Moment.ratR E s N v^(-(2 : Real)) *
            (2 / (mE E).im) :=
        mul_le_mul_of_nonneg_left hIntEta hcoefficient
      _ = _ := by ring
  have hNpow : (N : Real)^alpha ≤ (N : Real)^(δ/8) :=
    Real.rpow_le_rpow_of_exponent_le hNreal hExponent.le
  have hFinal :
      (transitionRootConst * absorbedRootConst / (mE E).im) *
        (N : Real)^alpha * Step2Moment.ratR E s N v^(-(2 : Real)) ≤
      crossProfileBudgetConst E * (N : Real)^(δ/8) *
        Step2Moment.ratR E s N v^(-(2 : Real)) := by
    unfold crossProfileBudgetConst
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNpow (by positivity)) (by positivity)
  change (∫ u in (s N)..v,
      crossProfile E D s t zetaSrc tauG deltaWeight deltaCap N k a u) ≤
      crossProfileBudgetConst E * (N : Real)^(δ/8) *
        Step2Moment.ratR E s N v^(-(2 : Real))
  exact hIntegralBound.trans hFinal

#print axioms eventually_integral_crossProfile_le_delta_eighth

/-- The local profile copy is definitionally the public T1029 profile. -/
theorem crossProfile_eq_T1029
    (E D : Real) (s t : Nat → Real) (zetaSrc tauG deltaWeight deltaCap : Real)
    (N k : Nat) (a : LoopArg (B.L N) 2) (u : Real) :
    crossProfile E D s t zetaSrc tauG deltaWeight deltaCap N k a u =
      APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
        deltaWeight deltaCap N k a u := by
  rfl

/-- The fixed coefficient is exactly T1029's E-dependent coefficient. -/
theorem crossProfileBudgetConst_eq_T1029 (E : Real) :
    crossProfileBudgetConst E =
      APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E := by
  rfl

/-- The sharpened theorem stated directly for the imported T1029 integrand. -/
theorem eventually_integral_T1029_crossProfile_le_delta_eighth
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 0 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (B.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) ≤
          APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
            (N : Real)^(δ/8) *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
  simpa only [crossProfile_eq_T1029, crossProfileBudgetConst_eq_T1029] using
    (eventually_integral_crossProfile_le_delta_eighth
      hE hD hs0 hst ht1 hc hreg hδ hδsmall)

#print axioms eventually_integral_T1029_crossProfile_le_delta_eighth
#print axioms crossProfile_eq_T1029
#print axioms crossProfileBudgetConst_eq_T1029

end
end RBM.APrimeGeneralMovingCrossProfileStrictExponent
