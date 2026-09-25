/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget

/-!
# T1301: free-loss absorbed QV root and actual-weight integral budget

The actual smooth weight uses loss `lambda`; the QV source and scalar
epsilon use `h = lambda / 1000`, and the absorbed profile uses cap `2*lambda`.
The root estimate keeps the near `2*W⁻¹` residual and the complete absorbed
far coefficient before integrating T993's exact-profile estimate.
-/

namespace RBM.APrimeFreeLossQVRoot

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private noncomputable def capConst : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)

private noncomputable def rootConst : Real :=
  Real.sqrt 6 * (1 + 256 * Real.exp 3) +
    Real.sqrt (1200 * capConst^3)

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
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ N^e * r^(27 : Real)) hmargin
    (by norm_num : (0 : Real) ≤ 1/3)
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

private theorem cap_le_const_mul
    {E tau delta : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hr : 1 ≤ Step2Moment.ratR E s N u) :
    APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tau delta N u ≤
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
  unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap capConst
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

private theorem eventually_cNear2_le {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {eps : Real}
    (heps : 0 < eps) :
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
      2 / B.ell N (u : Real) ≤ (B.W N : Real)^(eps/2) := by
    have hdiv : 2 / B.ell N (u : Real) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : (0 : Real) < B.ell N (u : Real))).2
      nlinarith
    nlinarith [hlogN', hdiv, hfourN']
  have hexp' : Real.exp (4 * Real.log (B.W N : Real)^(3/4 : Real)) ≤
      (B.W N : Real)^(eps/2) := by simpa only [one_mul] using hexpN
  calc
    _ ≤ (B.W N : Real)^(eps/2) * (B.W N : Real)^(eps/2) := by
      unfold Lemma57.cNear2
      exact mul_le_mul hpoly hexp' (Real.exp_pos _).le (Real.rpow_nonneg hW0.le _)
    _ = (B.W N : Real)^eps := by rw [← Real.rpow_add hW0]; congr 1; ring
    _ ≤ (N : Real)^eps := Real.rpow_le_rpow hW0.le hWN heps.le

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
  have hright0 : 0 ≤ Real.sqrt C * N^(q/2) * a^(-(1/2 : Real)) := by positivity
  nlinarith [hleftsq, hrightsq]

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
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) ≤
      (1200 * capConst^3) * (N : Real)^(zetaSrc+eps) *
        (etaT E u)⁻¹ * Step2Moment.ratR E s N u^3)
    (hXi : Step2.xiK (B.L N) (B.W N : Real) (mE E).im ≤ (N : Real)^eps) :
    APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a ≤
      rootConst * (N : Real)^(zetaSrc/2 + 3*eps/2) *
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
    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u)
  let chi : Real := if (zdist (B.L N) (a 0 - a 1) : Real) ≤
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
  have hRatio : R = S / U := by dsimp [R, S, U, Step2Moment.ratR]
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hNpow1 : 1 ≤ (N : Real)^eps := Real.one_le_rpow hNreal heps0
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
  have hchi0 : 0 ≤ chi := (indicator_zero_one_bounds _).1
  have hchi1 : chi ≤ 1 := (indicator_zero_one_bounds _).2
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
    have hprod' : xi * chi ≤ xi := by nlinarith [hprod]
    have hleak' : 256 * Real.exp 3 * leakage ≤ 256 * Real.exp 3 := by
      nlinarith [hleak]
    have hXi' : xi ≤ (N : Real)^eps := hXi
    have hconst' : 256 * Real.exp 3 ≤
        256 * Real.exp 3 * (N : Real)^eps := by
      have hmul := mul_le_mul_of_nonneg_left hNpow1
        (show 0 ≤ 256 * Real.exp 3 by positivity)
      nlinarith [hmul]
    calc
      _ ≤ xi + 256 * Real.exp 3 := add_le_add hprod' hleak'
      _ ≤ (N : Real)^eps + 256 * Real.exp 3 * (N : Real)^eps := by
        exact add_le_add hXi' hconst'
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
  have hFarTerm : R^(-(2 : Real)) * (Real.sqrt far * xi) ≤
      Real.sqrt Kfar * (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) := by
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
              _ = Real.sqrt Kfar * ((N : Real)^(q/2) * (N : Real)^eps) *
                  S^(-(1/2 : Real)) := by ring
              _ = _ := by rw [hpow]
  have hsum := add_le_add hNearTerm hFarTerm
  have hsumFactor :
      (Real.sqrt 6 * (1 + 256 * Real.exp 3)) *
          (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) +
        Real.sqrt Kfar * (N : Real)^(q/2+eps) * S^(-(1/2 : Real)) =
      rootConst * (N : Real)^(zetaSrc/2+3*eps/2) * S^(-(1/2 : Real)) := by
    rw [show q/2+eps = zetaSrc/2+3*eps/2 by dsimp [q]; ring]
    unfold rootConst Kfar capConst
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
        (rootConst * (N : Real)^(zetaSrc/2+3*eps/2) *
          S^(-(1/2 : Real))) := by
      rw [show q/2+eps = zetaSrc/2+3*eps/2 by dsimp [q]; ring]
      unfold rootConst Kfar capConst
      ring
    _ = _ := by dsimp [V, S]; ring

/-- The complete T590 absorbed root, with the near `2/W` residual, endpoint
leakage, spatial indicator, and absorbed far row all retained, has the
free-loss pointwise scale. -/
theorem eventually_absorbed_root_le
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N)
          (APrimeGeneralMovingQVNormBudget.endpoint s t D N k),
      ∀ a : LoopArg (d.L N) 2,
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
          (lambda / 1000) N u
          (APrimeGeneralMovingQVNormBudget.endpoint s t D N k) D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s
            (lambda / 1000) (2 * lambda) N u) a ≤
        rootConst * (N : Real)^(2 * (lambda / 1000)) *
          etaT E (s N)^(-(1 / 2 : Real)) *
          Step2Moment.ratR E s N
            (APrimeGeneralMovingQVNormBudget.endpoint s t D N k)^(-(2 : Real)) := by
  let h : Real := lambda / 1000
  have hlambdaC : lambda ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  have hNear := eventually_cNear2_le hs0 ht1 (eps := h) (by dsimp [h]; positivity)
  have hMargin := hreg.margin hE hst ht1 hc
    (e := c / 10) (b := 27) (a := 1) (by positivity) (by norm_num)
    (by field_simp [hc.ne']; norm_num)
  have hScale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  have hXi := Step2FarInputs.eventually_xiK_le B (mE E).im
    (τ := h) (by dsimp [h]; positivity)
  filter_upwards [hNear, hMargin, hScale, hXi, B.dim,
      Step2.eventually_le_W_sq B, eventually_ge_atTop 1]
    with N hNearN hMarginN hScaleN hXiN hdimN hNW2N hN
  intro k hk u hu a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : Real) := by linarith
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans hv.2 |>.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hetaS : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have heta1 : etaT E u ≤ 1 := etaT_le_one hE hu0
  have hR : 1 ≤ Step2Moment.ratR E s N u :=
    Step2Moment.one_le_ratR hE hu.1 hu1
  have hRpos : 0 < Step2Moment.ratR E s N u := by linarith
  have hEllS : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
      ((hst N).trans_lt (ht1 N))
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have hEllU : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hEllRatio : 0 ≤ B.ell N u / B.ell N (s N) := by positivity
  have hEllRatio2 : (B.ell N u / B.ell N (s N))^2 ≤
      Step2Moment.ratR E s N u :=
    Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hu.1 hu1
  have hCnear : Lemma57.cNear2 (B.W N : Real) (B.ell N u) ≤ (N : Real)^h := by
    have hh := hNearN uu
    simpa only [Function.comp_apply] using hh
  have hNearRate :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u ≤
        4 * (N : Real)^(h+h) * (etaT E u)⁻¹ *
          Step2Moment.ratR E s N u^3 := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    exact near_source_scalar_le hNpos heta
      (Lemma57.cNear2_nonneg (by exact_mod_cast B.W_pos N) hEllU)
      hCnear hEllRatio hR hEllRatio2
  have hWinv : (B.W N : Real)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast B.W_pos N)
  have hBase1 : 1 ≤ (N : Real)^(h+h) * (etaT E u)⁻¹ *
      Step2Moment.ratR E s N u^3 := by
    have hNpow : 1 ≤ (N : Real)^(h+h) := Real.one_le_rpow hNreal (by positivity)
    have hEtainv : 1 ≤ (etaT E u)⁻¹ := (one_le_inv₀ heta).2 heta1
    have hR3 : 1 ≤ Step2Moment.ratR E s N u^3 := one_le_pow₀ hR
    have hprod : 1 ≤ (N : Real)^(h+h) * (etaT E u)⁻¹ := by
      nlinarith [mul_le_mul hNpow hEtainv (by positivity) (by positivity)]
    nlinarith [mul_le_mul hprod hR3 (by positivity) (by positivity)]
  have hNear :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u +
        2 * (B.W N : Real)⁻¹ ≤
      6 * (N : Real)^(h+h) * (etaT E u)⁻¹ *
        Step2Moment.ratR E s N u^3 := by
    have hBase0 : 0 ≤ (N : Real)^(h+h) * (etaT E u)⁻¹ *
        Step2Moment.ratR E s N u^3 := by positivity
    nlinarith [hNearRate, hWinv, hBase1]
  let A := B.scale E N u
  let J := APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h
    (2 * lambda) N u
  have hApos : 0 < A := by
    dsimp [A]
    rw [B.scale_eq_flowScale]
    exact flowScale_pos (by exact_mod_cast B.W_pos N) (B.one_le_L N) hE hu1
  have hA1 : 1 ≤ A := (Real.one_le_rpow hNreal hc.le).trans (hScaleN uu).1
  have hAupper : A ≤ (N : Real) := by
    obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N uu
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast hdimN.1
    change (B.W N : Real) * B.ell N u * etaT E u ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hMarginU : (N : Real)^(c/10) *
      Step2Moment.ratR E s N u^(27 : Real) ≤ A := by
    simpa [Step2Moment.ratR, A, Real.rpow_one] using hMarginN uu
  have hcap : J ≤ capConst * (N : Real)^(h+2*(2*lambda)) *
      Step2Moment.ratR E s N u^4 := by
    dsimp [J]
    exact cap_le_const_mul hN (by positivity) (by positivity) hR
  have hJ1 : 1 ≤ J := by
    dsimp [J, APrimeGeneralMovingQVProfile.generalMovingBlockCap]
    apply le_add_of_nonneg_right
    positivity
  have hJ0 : 0 ≤ J := by linarith
  have hFarRaw := far_scalar_le hApos hNpos hRpos hJ0
    (show 0 ≤ capConst by unfold capConst; positivity)
    hMarginU hcap
  have hFarExp : 3 * (h + 2 * (2 * lambda)) - c/30 ≤ h+h := by
    dsimp [h]
    nlinarith [hlambdaC]
  have hFarExpPow := Real.rpow_le_rpow_of_exponent_le hNreal hFarExp
  have hFar :
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u J ≤
        (1200 * capConst^3) * (N : Real)^(h+h) *
          (etaT E u)⁻¹ * Step2Moment.ratR E s N u^3 := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    have hFarRaw' : A^(-(1/3 : Real)) * J^3 ≤
        capConst^3 * (N : Real)^(3*(h+2*(2*lambda))-c/30) *
          Step2Moment.ratR E s N u^3 := by
      simpa only [A, J, show (c/10)/3 = c/30 by ring] using hFarRaw
    have hfactor : 0 ≤ 1200 * (etaT E u)⁻¹ := by positivity
    calc
      _ = (1200 * (etaT E u)⁻¹) * (A^(-(1/3 : Real)) * J^3) := by ring
      _ ≤ (1200 * (etaT E u)⁻¹) *
          (capConst^3 * (N : Real)^(3*(h+2*(2*lambda))-c/30) *
            Step2Moment.ratR E s N u^3) := mul_le_mul_of_nonneg_left hFarRaw' hfactor
      _ ≤ (1200 * (etaT E u)⁻¹) *
          (capConst^3 * (N : Real)^(h+h) *
            Step2Moment.ratR E s N u^3) := by
        have hcoef : 0 ≤ 1200 * (etaT E u)⁻¹ * capConst^3 *
            Step2Moment.ratR E s N u^3 := by
          have hc0 : 0 ≤ capConst := by unfold capConst; positivity
          positivity
        calc
          _ = (1200 * (etaT E u)⁻¹ * capConst^3 *
              Step2Moment.ratR E s N u^3) *
                (N : Real)^(3*(h+2*(2*lambda))-c/30) := by ring
          _ ≤ (1200 * (etaT E u)⁻¹ * capConst^3 *
              Step2Moment.ratR E s N u^3) * (N : Real)^(h+h) :=
            mul_le_mul_of_nonneg_left hFarExpPow hcoef
          _ = _ := by ring
      _ = _ := by ring
  have hXiPoint : Step2.xiK (B.L N) (B.W N : Real) (mE E).im ≤ (N : Real)^h := by
    exact hXiN
  have hPoint := absorbed_root_profile_pointwise_le (E := E) (D := D)
    (s := s) (t := t) (zetaSrc := h) (tauG := h) (deltaCap := 2*lambda)
    (eps := h) (N := N) (u := u) (v := v) a hE (by linarith [hD])
    hs0 hst ht1 hN huWindow hu.2
    (hv.2.trans_lt (ht1 N)) (by positivity) (by positivity)
    (by simpa [h] using hNear) (by simpa [J] using hFar) hXiPoint
  have hexp : h/2 + 3*h/2 = 2 * (lambda/1000) := by dsimp [h]; ring
  simpa only [h, J, v, show h/2 + 3*h/2 = 2 * (lambda/1000) from hexp] using hPoint

private theorem rootProfile_nonneg (E : Real) (N : Nat)
    (u v D ellSource J Smax epsilon : Real) (a : LoopArg (B.L N) 2) :
    0 ≤ APrimeFullQV.rootProfile B E N u v D ellSource J Smax epsilon a := by
  have hT : 0 ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg (show 0 ≤ (B.W N : Real) by positivity)
        (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 ≤ Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : Real) ≤
      6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
    split_ifs <;> norm_num
  unfold APrimeFullQV.rootProfile
  positivity

private theorem eventually_Qexact_le_absorbed_profile
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N)
          (APrimeGeneralMovingQVNormBudget.endpoint s t D N k),
      ∀ a : LoopArg (d.L N) 2,
        APrimeGeneralMovingQVNormBudget.Qexact E D s t
            (lambda / 1000) (lambda / 1000) (2 * lambda) N k a u ≤
          (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
            (lambda / 1000) N u
            (APrimeGeneralMovingQVNormBudget.endpoint s t D N k) D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s
              (lambda / 1000) (2 * lambda) N u) a)^2 := by
  let h : Real := lambda / 1000
  have hcapC : 2 * lambda ≤ c / 20 := by
    have hh := hsmall.trans (min_le_right _ _)
    nlinarith
  have htauCap : h ≤ (2 * lambda) / 16 := by dsimp [h]; nlinarith
  have hquad := APrimeGeneralMovingQVAbsorption.eventually_quadratic_source_comparison
    hE hs0 hst ht1 hc hreg
    (show 0 < h by dsimp [h]; positivity)
    (show 0 < h by dsimp [h]; positivity)
    (show 0 < 2 * lambda by positivity)
    (by dsimp [h]; rfl) htauCap hcapC
  have hscale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hquad, hscale, B.dim, hNW, eventually_ge_atTop 1]
    with N hquadN hscaleN hdimN hNW2N hN
  intro k hk u hu a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let Jbar := APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h
    (2 * lambda) N u
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : Real) := by linarith
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans hv.2 |>.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hellu : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hells : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hA : 1 ≤ B.scale E N u :=
    (Real.one_le_rpow hNr hc.le).trans (hscaleN uu).1
  have hAN : B.scale E N u ≤ (N : Real) := by
    obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N uu
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast hdimN.1
    have heta1 : etaT E u ≤ 1 := etaT_le_one hE hu0
    change (B.W N : Real) * B.ell N u * etaT E u ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hdimN.1
  have heta1 : etaT E u ≤ 1 := etaT_le_one hE hu0
  have hW1 : 1 ≤ (B.W N : Real) := by exact_mod_cast B.W_pos N
  have hleak : (B.W N : Real) * (B.L N : Real) *
      (B.W N : Real)^(-D) ≤ (etaT E u)⁻¹ * (B.scale E N u)⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hNr
      (lt_of_lt_of_le zero_lt_one hA) heta hWL hAN hNW2N heta1 (by linarith [hD])
  have hJ1 : 1 ≤ Jbar := by
    dsimp [Jbar, APrimeGeneralMovingQVProfile.generalMovingBlockCap]
    apply le_add_of_nonneg_right
    positivity
  have hfar := APrimeGeneralMovingQVAbsorption.diagFarRate_source_le_absorbed
    (E := E) (zetaSrc := h) (s := s) (N := N) (u := u)
    (D := D) (J := Jbar) hN hells hellu heta hA hJ1 (hquadN uu) hleak
  have hroot := APrimeGeneralMovingQVAbsorption.normalized_rootProfile_le_absorbed
    (E := E) (zetaSrc := h) (s := s) (N := N) (u := u)
    (v := v) (D := D) (J := Jbar) hE hu.1 hu.2
    (hv.2.trans_lt (ht1 N)) hN hells hfar a
  have hscaleInv : 0 ≤
      (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d hE hv.1
      (hv.2.trans_lt (ht1 N)) N a)).le
  have hroot0 : 0 ≤ APrimeFullQV.rootProfile B E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s h N) Jbar
      (APrimeGeneralMovingRawSources.sourceC4 E s h N u)
      ((B.W N : Real)⁻¹) a :=
    rootProfile_nonneg E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s h N) Jbar
      (APrimeGeneralMovingRawSources.sourceC4 E s h N u)
      ((B.W N : Real)⁻¹) a
  have hsq := pow_le_pow_left₀ (mul_nonneg hscaleInv hroot0) hroot 2
  simpa [APrimeGeneralMovingQVNormBudget.Qexact,
    APrimeGeneralMovingQVNormBudget.endpoint, v, Jbar, h] using hsq

private theorem scale_le_N (hE : |E| < 2) {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {N : Nat} (hdim : B.W N * B.L N ≤ N) (u : TimeIcc s t N) :
    B.scale E N (u : Real) ≤ (N : Real) := by
  obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hdim
  change (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) ≤ (N : Real)
  calc
    _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
    _ = (B.W N : Real) * (B.L N : Real) := by ring
    _ ≤ (N : Real) := hWL

private theorem eventually_R4_le_N_two_fifteenths
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      (Step2Moment.ratR E s N
        (APrimeGeneralMovingQVNormBudget.endpoint s t D N k))^4 ≤
        (N : Real)^(2/15 : Real) := by
  have hmargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hmargin, B.dim, eventually_ge_atTop 1]
    with N hmarginN hdimN hN
  intro k hk
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  let vv : TimeIcc s t N := ⟨v, hv⟩
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt (hv.2.trans_lt (ht1 N)))
      (hv.2.trans_lt (ht1 N))
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hv.1 (hv.2.trans_lt (ht1 N))
  have hR30 : Step2Moment.ratR E s N v^30 ≤ B.scale E N v := by
    have hh := hmarginN vv
    simpa only [Step2Moment.ratR] using hh
  have hscaleN : B.scale E N v ≤ (N : Real) :=
    scale_le_N hE hs0 ht1 (by exact_mod_cast hdimN.1) vv
  have hR30N : Step2Moment.ratR E s N v^30 ≤ (N : Real) :=
    hR30.trans hscaleN
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hRfour := rpow_mul_rpow_le_of_pow_thirty
    (A := (N : Real)) (R := Step2Moment.ratR E s N v) (Nr := (N : Real))
    (c := 1) (e := 0) (b := 4) (a := (2 : Real) / 15)
    hNr hR1 (by norm_num) (by norm_num) (by norm_num) hR30N
    (by simp) (by norm_num)
  have hRfourReal : (Step2Moment.ratR E s N v)^(4 : Real) ≤
      (N : Real)^(2/15 : Real) := by
    simpa only [Real.rpow_zero, one_mul] using hRfour
  have hRfourNat : (Step2Moment.ratR E s N v)^4 ≤
      (N : Real)^(2/15 : Real) := by
    rw [← Real.rpow_natCast]
    exact hRfourReal
  simpa only [v] using hRfourNat

noncomputable def actualQVIntegralConst (E : Real) : Real :=
  rootConst^2 / (mE E).im + 1

theorem actualQVIntegralConst_pos (E : Real) (hE : |E| < 2) :
    0 < actualQVIntegralConst E := by
  unfold actualQVIntegralConst
  have hm : 0 < (mE E).im := mE_im_pos hE
  positivity

/-- The actual smooth weight at loss `lambda` has the exact T993 QV
integral profile at buffer `xi=lambda`; its full absorbed root is integrated
at the same free-loss schedule. The conclusion is uniform over every active
net cell (including `k=0`) and every two-loop output. -/
theorem eventually_actual_weight_qv_integral_le_budget
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
        (∫ u in (s N)..v,
          APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u) ≤
          actualQVIntegralConst E * (N : Real)^(4 * (lambda / 1000)) *
            Step2Moment.ratR E s N v^(-(4 : Real)) := by
  let h : Real := lambda / 1000
  have hlambda1 : lambda ≤ (1 / 10000 : Real) := hsmall.trans (min_le_left _ _)
  have hroom : h + 2 * (lambda + lambda) + (2 : Real) / 15 < 1 := by
    dsimp [h]
    nlinarith [hlambda1]
  have hqv :=
    APrimeGeneralMovingActualSmoothQVNormBudget.eventually_actual_smooth_qv_integral_le_exact_profile
      hE hD hs0 hst ht1 hc hreg hB
      (zetaSrc := h) (zetaCtr := h) (tauG := h)
      (deltaWeight := lambda) (xi := lambda)
      (by dsimp [h]; positivity) (by dsimp [h]; positivity)
      (by dsimp [h]; positivity) (by positivity)
      (by positivity) hroom p hp 1 (by norm_num)
  have hroot := eventually_absorbed_root_le hE hD hs0 hst ht1 hc hreg
    hlambda hsmall
  have hprofile := eventually_Qexact_le_absorbed_profile
    hE hD hs0 hst ht1 hc hreg hlambda hsmall
  have hR4 := eventually_R4_le_N_two_fifteenths (D := D)
    hE hs0 hst ht1 hc hreg
  filter_upwards [hqv, hroot, hprofile, hR4, eventually_ge_atTop 1]
    with N hqvN hrootN hprofileN hR4N hN
  intro k hk a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let R := Step2Moment.ratR E s N v
  let S := etaT E (s N)
  let target := (N : Real)^(4*h) * R^(-(4 : Real))
  rcases hqvN k hk a with ⟨hgi, hrest⟩
  rcases hrest with ⟨hQi, hactualInt⟩
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hS : 0 < S := Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hRpos : 0 < R := Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hR1 : 1 ≤ R := Step2Moment.one_le_ratR hE hv.1 hv1
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : Real) := by linarith
  have hTarget0 : 0 ≤ target := by dsimp [target]; positivity
  have hpoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingQVNormBudget.Qexact E D s t h h (2*lambda) N k a u ≤
        rootConst^2 * (N : Real)^(4*h) * S^(-(1 : Real)) * R^(-(4 : Real)) := by
    intro u hu
    have hq := hprofileN k hk u hu a
    have hr := hrootN k hk u hu a
    have hAbs0 : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h (2*lambda) N u) a := by
      have hxi := Step2.xiK_nonneg (B.L N) (B.W N : Real) (mE E).im
      have hW0 : 0 < B.W N := by exact_mod_cast B.W_pos N
      have hWr : 0 < (B.W N : Real) := by exact_mod_cast B.W_pos N
      have hu1 : u < 1 := hu.2.trans_lt (hv.2.trans_lt (ht1 N))
      have hEtaU : 0 < etaT E u := Step2.etaT_pos' hE hu1
      have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : Real) ≤
          6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
        split_ifs <;> norm_num
      have hNear : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u := by
        unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
        have hEllS : 0 < B.ell N (s N) := by
          have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
            ((hst N).trans_lt (ht1 N))
          simpa only [Band.ell] using
            (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
        have hEllU : 0 < B.ell N u := by
          have hh := one_le_ellHat_of_nonneg (B.one_le_L N)
            ((hs0 N).trans hu.1)
            (hu.2.trans_lt (hv.2.trans_lt (ht1 N)))
          simpa only [Band.ell] using
            (show 0 < ellHat (B.L N) (u : Complex) by linarith)
        have hcNear : 0 ≤ Lemma57.cNear2 (B.W N : Real) (B.ell N u) :=
          Lemma57.cNear2_nonneg (by exact_mod_cast B.W_pos N) hEllU
        have hRatio : 0 ≤ B.ell N u / B.ell N (s N) := by positivity
        positivity
      have hFar : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h (2*lambda) N u) := by
        unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
        have hA : 0 < B.scale E N u := by
          rw [B.scale_eq_flowScale]
          exact flowScale_pos (by exact_mod_cast B.W_pos N) (B.one_le_L N) hE
            (hu.2.trans_lt (hv.2.trans_lt (ht1 N)))
        have hJ : 0 ≤ APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h
            (2*lambda) N u := by
          unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
          have hRu : 0 < Step2Moment.ratR E s N u :=
            Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hu1
          positivity
        have hAneg : 0 ≤ (B.scale E N u)^(-(1/3 : Real)) :=
          (Real.rpow_pos_of_pos hA _).le
        have hJ3 : 0 ≤ (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h
            (2*lambda) N u)^3 := by positivity
        have hEtaInv : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.mpr hEtaU.le
        positivity
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      have hRu : 0 < Step2Moment.ratR E s N u :=
        Step2Moment.ratR_pos hE hs1 hu1
      have hRuInv : 0 ≤ Step2Moment.ratR E s N u ^ (-(2 : Real)) :=
        Real.rpow_nonneg hRu.le _
      have hRvInv : 0 ≤ Step2Moment.ratR E s N v ^ (-(2 : Real)) :=
        Real.rpow_nonneg hRpos.le _
      have hWinv : 0 ≤ (B.W N : Real)⁻¹ := inv_nonneg.mpr hWr.le
      have hNearArg : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u +
          2 * (B.W N : Real)⁻¹ := by positivity
      have hNearSqrt : 0 ≤ Real.sqrt
          (APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u +
            2 * (B.W N : Real)⁻¹) := Real.sqrt_nonneg _
      have hWleak : 0 ≤ (B.W N : Real)^(-D) :=
        (Real.rpow_pos_of_pos hWr _).le
      have hkernel : 0 ≤ Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
          (if (zdist (B.L N) (a 0 - a 1) : Real) ≤
            6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0) +
          256 * Real.exp 3 * (B.W N : Real)^(-D) := by
        exact add_nonneg (mul_nonneg hxi (by split_ifs <;> norm_num)) (by positivity)
      have hfarSqrt : 0 ≤ Real.sqrt
          (APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h (2*lambda) N u)) :=
        Real.sqrt_nonneg _
      have hprofileTail : 0 ≤ Real.sqrt
          (APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u +
            2 * (B.W N : Real)⁻¹) *
            (Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
              (if (zdist (B.L N) (a 0 - a 1) : Real) ≤
                  6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0) +
              256 * Real.exp 3 * (B.W N : Real)^(-D)) +
          Real.sqrt (APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h (2*lambda) N u)) *
            Step2.xiK (B.L N) (B.W N : Real) (mE E).im := by
        exact add_nonneg (mul_nonneg hNearSqrt hkernel) (mul_nonneg hfarSqrt hxi)
      unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
      exact mul_nonneg (mul_nonneg hRuInv hRvInv) hprofileTail
    have hsq := pow_le_pow_left₀ hAbs0 hr 2
    have hsqeq :
        (rootConst * (N : Real)^(2*h) * S^(-(1/2 : Real)) * R^(-(2 : Real)))^2 =
          rootConst^2 * (N : Real)^(4*h) * S^(-(1 : Real)) * R^(-(4 : Real)) := by
      have hNpow : ((N : Real)^(2*h))^2 = (N : Real)^(4*h) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        congr 1
        ring
      have hSpow : (S^(-(1/2 : Real)))^2 = S^(-(1 : Real)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le]
        congr 1
        norm_num
      have hRpow : (R^(-(2 : Real)))^2 = R^(-(4 : Real)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
        congr 1
        norm_num
      rw [mul_pow, mul_pow, mul_pow, hNpow, hSpow, hRpow]
    calc
      _ ≤ APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h (2*lambda) N u) a ^ 2 := hq
      _ ≤ (rootConst * (N : Real)^(2*h) * S^(-(1/2 : Real)) *
          R^(-(2 : Real)))^2 := by
        exact hsq
      _ = _ := hsqeq
  have hQint :
      (∫ u in (s N)..v, APrimeGeneralMovingQVNormBudget.Qexact E D s t h h
        (2*lambda) N k a u) ≤
        rootConst^2 / (mE E).im * target := by
    have hm : 0 < (mE E).im := mE_im_pos hE
    have htime : v - s N ≤ S / (mE E).im := by
      have hgap : v - s N ≤ 1 - s N := by linarith [hv.2]
      calc
        _ ≤ 1 - s N := hgap
        _ = S / (mE E).im := by
          dsimp [S]
          rw [Step2.etaT_eq]
          field_simp [ne_of_gt hm]
    have hprofileBound0 : 0 ≤ rootConst^2 * (N : Real)^(4*h) *
        S^(-(1 : Real)) * R^(-(4 : Real)) := by positivity
    have hQi2 : IntervalIntegrable
        (APrimeGeneralMovingQVNormBudget.Qexact E D s t h h (2*lambda) N k a)
        volume (s N) v := by
      simpa only [two_mul, APrimeGeneralMovingActualSmoothQVNormBudget.endpoint] using hQi
    have hbound := intervalIntegral.integral_mono_on hv.1 hQi2
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : Real => rootConst^2 * (N : Real)^(4*h) *
          S^(-(1 : Real)) * R^(-(4 : Real))) volume (s N) v)
      (fun u hu => hpoint u hu)
    have hconstIntegral :
        (∫ u in (s N)..v,
          (fun _ : Real => rootConst^2 * (N : Real)^(4*h) *
            S^(-(1 : Real)) * R^(-(4 : Real))) u) =
          (v - s N) * (rootConst^2 * (N : Real)^(4*h) *
            S^(-(1 : Real)) * R^(-(4 : Real))) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    calc
      _ ≤ (v - s N) * (rootConst^2 * (N : Real)^(4*h) *
          S^(-(1 : Real)) * R^(-(4 : Real))) := by
        simpa only [hconstIntegral] using hbound
      _ ≤ (S / (mE E).im) *
          (rootConst^2 * (N : Real)^(4*h) * S^(-(1 : Real)) * R^(-(4 : Real))) :=
        mul_le_mul_of_nonneg_right htime hprofileBound0
      _ = rootConst^2 / (mE E).im * target := by
        have hSInv : (etaT E (s N))^(-(1 : Real)) = (etaT E (s N))⁻¹ := by
          rw [Real.rpow_neg hS.le, Real.rpow_one]
        dsimp [target, S]
        rw [hSInv]
        rw [Step2.etaT_eq]
        have hden : -(s N * (mE E).im) + (mE E).im ≠ 0 := by
          have hEtaEq : etaT E (s N) = (mE E).im * (1 - s N) := by
            rw [Step2.etaT_eq]
            ring
          have hpos : 0 < (mE E).im * (1 - s N) := by
            rw [← hEtaEq]
            exact hS
          have hpos' : 0 < -(s N * (mE E).im) + (mE E).im := by
            convert hpos using 1 <;> ring
          exact ne_of_gt hpos'
        field_simp [ne_of_gt hm, hden]
        have hsEta : 0 < 1 - s N := by linarith [hst N, ht1 N]
        field_simp [ne_of_gt hsEta]
  have hComplement : (v - s N) * (N : Real)^(-(1 : Real)) ≤ target := by
    have hlen : 0 ≤ v - s N ∧ v - s N ≤ 1 := by
      constructor <;> linarith [hv.1, hv.2, hs0 N, ht1 N]
    have hR4bd := hR4N k hk
    have hR4real : R^(4 : Real) ≤ (N : Real)^(2/15 : Real) := by
      change (Step2Moment.ratR E s N v)^(4 : Nat) ≤ (N : Real)^(2/15 : Real) at hR4bd
      rw [← Real.rpow_natCast] at hR4bd
      exact hR4bd
    have hinv := inv_anti₀ (Real.rpow_pos_of_pos hRpos 4) hR4real
    have hInvR : (N : Real)^(-(2/15 : Real)) ≤ R^(-(4 : Real)) := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_neg hRpos.le]
      simpa only [one_div] using hinv
    have hNexp : (N : Real)^(-(1 : Real)) ≤ (N : Real)^(-(2/15 : Real)) :=
      Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
    have hNpow : 1 ≤ (N : Real)^(4*h) := Real.one_le_rpow hNreal (by positivity)
    have hRinv0 : 0 ≤ R^(-(4 : Real)) := by positivity
    have hInvTarget : R^(-(4 : Real)) ≤ target := by
      dsimp [target]
      calc
        _ = 1 * R^(-(4 : Real)) := by ring
        _ ≤ (N : Real)^(4*h) * R^(-(4 : Real)) :=
          mul_le_mul_of_nonneg_right hNpow hRinv0
    calc
      _ ≤ 1 * (N : Real)^(-(1 : Real)) :=
        mul_le_mul_of_nonneg_right hlen.2 (by positivity)
      _ ≤ target := by
        have : (N : Real)^(-(1 : Real)) ≤ target :=
          hNexp.trans (hInvR.trans hInvTarget)
        simpa only [one_mul] using this
  have hInt :
      (∫ u in (s N)..v,
        APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u) ≤
        (∫ u in (s N)..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t h h (2*lambda) N k a u) +
          (v - s N) * (N : Real)^(-(1 : Real)) := by
    simpa only [two_mul, APrimeGeneralMovingActualSmoothQVNormBudget.endpoint] using hactualInt
  have hmain :
      (∫ u in (s N)..v,
        APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u) ≤
        actualQVIntegralConst E * target := by
    calc
      _ ≤ (∫ u in (s N)..v,
            APrimeGeneralMovingQVNormBudget.Qexact E D s t h h (2*lambda) N k a u) +
          (v - s N) * (N : Real)^(-(1 : Real)) := hInt
      _ ≤ rootConst^2 / (mE E).im * target + target :=
        add_le_add hQint hComplement
      _ = actualQVIntegralConst E * target := by
        unfold actualQVIntegralConst
        ring
  calc
    _ ≤ actualQVIntegralConst E * target := hmain
    _ = actualQVIntegralConst E * (N : Real)^(4 * (lambda / 1000)) *
        Step2Moment.ratR E s N v^(-(4 : Real)) := by
      dsimp [target, h, R]
      ring

/-- A positive-length first-cell model simultaneously realizes the free-loss
schedule, the regularity and bounds hypotheses, and a resident common-event
sample on the positive-cap plateau. -/
theorem free_loss_hypotheses_witness :
    ∃ c : Real, 0 < c ∧
    ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∃ lambda : Real,
        0 < lambda ∧
        lambda ≤ min (1/10000 : Real) (c/10000) ∧
        0 < lambda/1000 ∧
        0 < 2*lambda ∧
        lambda + lambda = 2*lambda ∧
        lambda/1000 ≤ (2*lambda)/16 ∧
        2*lambda ≤ c/20 ∧
        lambda/1000 + 2*(lambda+lambda) + (2 : Real)/15 < 1 ∧
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (lambda/1000) (lambda/1000) (lambda/1000) N ∧
            1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (APrimeGeneralMovingDetFields.J 0 60 s) s t
              (APrimeGeneralMovingMesh.targetMesh 60) (2*lambda) 1 N 1 omega = 1 := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hcommon⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  let lambda : Real := min (c/20000) (1/20000)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min (by positivity) (by norm_num)
  have hlambdaC : lambda ≤ c/10000 := by
    dsimp [lambda]
    have hmin : min (c/20000) (1/20000) ≤ c/20000 := min_le_left _ _
    nlinarith
  have hlambda1 : lambda ≤ 1/10000 := by
    dsimp [lambda]
    exact (min_le_right _ _).trans (by norm_num)
  have hsmall : lambda ≤ min (1/10000 : Real) (c/10000) := le_min hlambda1 hlambdaC
  have hh : 0 < lambda/1000 := by positivity
  have hcap : 0 < 2*lambda := by positivity
  have hcapTau : lambda/1000 ≤ (2*lambda)/16 := by nlinarith
  have hcapC : 2*lambda ≤ c/20 := by nlinarith [hlambdaC]
  have hroom : lambda/1000 + 2*(lambda+lambda) + (2 : Real)/15 < 1 := by
    nlinarith [hlambda1]
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    lambda, hlambda, hsmall, hh, hcap, by ring, hcapTau, hcapC, hroom, ?_⟩
  have hevent := hcommon (lambda/1000) (lambda/1000) (lambda/1000) (2*lambda)
    hh hh hh hcap
  filter_upwards [hevent] with N hN
  obtain ⟨hlen, omega, homega, hactive, hplateau⟩ := hN
  exact ⟨hlen, omega, homega, hactive, hplateau 1⟩

#print axioms eventually_absorbed_root_le
#print axioms actualQVIntegralConst
#print axioms actualQVIntegralConst_pos
#print axioms eventually_actual_weight_qv_integral_le_budget
#print axioms free_loss_hypotheses_witness

end
end RBM.APrimeFreeLossQVRoot
