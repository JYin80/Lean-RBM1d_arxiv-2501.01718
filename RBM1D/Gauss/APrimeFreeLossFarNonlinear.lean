/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingFarNonlinearStrictExponent
import RBM1D.Gauss.APrimeExponents

/-! # T1297: corrected-loss strict exponent for the T615 far nonlinear row

The observable is the exact sum of T615's inverse-scale and spatial-leakage
nonlinear far summands. The corrected schedule has actual weight loss
`lambda`, buffer `lambda`, cap `2*lambda`, and source losses `lambda/1000`.
-/

namespace RBM.APrimeFreeLossFarNonlinear

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

set_option maxHeartbeats 1000000

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def weightLoss (lambda : Real) : Real := lambda
noncomputable def bufferLoss (lambda : Real) : Real := lambda
noncomputable def capLoss (lambda : Real) : Real := 2 * lambda
noncomputable def sourceLoss (lambda : Real) : Real := lambda / 1000

noncomputable def normalizedFarInvScale (E : Real) (s : Nat → Real)
    (zeta tau delta : Real) (N : Nat) (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    Step2Moment.ratR E s N u ^ (-2 : Real) *
    Step2Moment.ratR E s N v ^ (-2 : Real) *
    ((etaT E u)⁻¹ * (4 * (N : Real) ^ zeta *
      (B.ell N u / B.ell N (s N))) *
      (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
        Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u) *
        (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹)))

noncomputable def normalizedFarLeakage (E D : Real) (s : Nat → Real)
    (zeta tau delta : Real) (N : Nat) (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    Step2Moment.ratR E s N u ^ (-2 : Real) *
    Step2Moment.ratR E s N v ^ (-2 : Real) *
    ((etaT E u)⁻¹ * (4 * (N : Real) ^ zeta *
      (B.ell N u / B.ell N (s N))) *
      (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
        Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u) *
        ((d.L N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) / B.ell N u)))

noncomputable abbrev normalizedFarNonlinear (E D : Real) (s : Nat → Real)
    (zeta tau delta : Real) (N : Nat) (v u : Real) : Real :=
  APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear
    E D s zeta tau delta N v u

private noncomputable def capC : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)

private theorem capC_pos : 0 < capC := by
  unfold capC
  positivity

/-- The corrected losses satisfy the same source/cap room used by the
T615 producers, with the explicitly requested strict smallness range. -/
theorem corrected_schedule_room {lambda c : Real} (hc : 0 < c)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    0 < weightLoss lambda ∧ 0 < bufferLoss lambda ∧
    0 < capLoss lambda ∧ 0 < sourceLoss lambda ∧
    weightLoss lambda + bufferLoss lambda = capLoss lambda ∧
    sourceLoss lambda ≤ weightLoss lambda / 16 ∧
    sourceLoss lambda ≤ capLoss lambda / 16 ∧
    capLoss lambda ≤ c / 20 ∧
    sourceLoss lambda + 4 * weightLoss lambda + (2 : Real) / 15 < 1 := by
  have hl1 : lambda ≤ (1 : Real) / 10000 := hsmall.trans (min_le_left _ _)
  have hlc : lambda ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  refine ⟨by simp [weightLoss]; exact hlambda,
    by simp [bufferLoss]; exact hlambda,
    by simp [capLoss]; positivity,
    by simp [sourceLoss]; positivity,
    by dsimp [weightLoss, bufferLoss, capLoss]; ring,
    ?_, ?_, ?_, ?_⟩
  · dsimp [sourceLoss, weightLoss]
    nlinarith [hlambda]
  · dsimp [sourceLoss, capLoss]
    nlinarith [hlambda]
  · dsimp [capLoss]
    nlinarith [hlc]
  · dsimp [sourceLoss, weightLoss]
    nlinarith [hl1]

/-- Exact arithmetic for the polynomial losses in the endpoint coefficient.
The `xiK` subpolynomial allowance is chosen to be `N^lambda`. -/
theorem corrected_far_coefficient_exponent (lambda : Real) :
    lambda + sourceLoss lambda +
      3 * (sourceLoss lambda + 2 * capLoss lambda) / 2 =
        (2801 / 400 : Real) * lambda := by
  dsimp [sourceLoss, capLoss]
  ring

private theorem blockCap_le_const
    {E : Real} {s : Nat → Real} {tau delta : Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hR : 1 ≤ Step2Moment.ratR E s N u) :
    APrimeGeneralMovingDriftSource.blockCap E s tau delta N u ≤
      capC * (N : Real) ^ (tau + 2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
  have hR4 : 1 ≤ Step2Moment.ratR E s N u ^ 4 := one_le_pow₀ hR
  have htauPow : 1 ≤ (N : Real) ^ tau := Real.one_le_rpow hn htau
  have hdeltaPow : 1 ≤ (N : Real) ^ (2 * delta) :=
    Real.one_le_rpow hn (by positivity)
  have hX1 : 1 ≤ (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
      Step2Moment.ratR E s N u ^ 4 := by
    nlinarith [mul_le_mul htauPow hdeltaPow (by positivity) (by positivity),
      mul_le_mul (mul_le_mul htauPow hdeltaPow (by positivity) (by positivity)) hR4
        (by positivity) (by positivity)]
  have htauX : (N : Real) ^ tau ≤
      (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
    have hmul : 1 ≤ (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
      nlinarith [mul_le_mul hdeltaPow hR4 (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hmul
      (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real) ^ tau * (N : Real) ^ (2 * delta) =
      (N : Real) ^ (tau + 2 * delta) := by rw [Real.rpow_add hn0]
  unfold APrimeGeneralMovingDriftSource.blockCap
  calc
    1 + (N : Real) ^ tau *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
            Step2Moment.ratR E s N u ^ 4) + 2) ≤
      capC * ((N : Real) ^ tau * (N : Real) ^ (2 * delta)) *
          Step2Moment.ratR E s N u ^ 4 := by
      let X := (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4
      have hmain : (N : Real) ^ tau *
          (9 * Real.exp (Real.sqrt 3) *
            ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
              Step2Moment.ratR E s N u ^ 4)) =
          (9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) * X := by
        dsimp [X]
        ring
      rw [mul_add, hmain]
      dsimp only [X] at hX1 htauX ⊢
      dsimp [capC]
      nlinarith
    _ = _ := by rw [hpow]

private theorem ratio_core_le {R rho J C n A Av : Real}
    (hR : 1 ≤ R) (hrho : 0 ≤ rho) (hrho2 : rho ^ 2 ≤ R)
    (hJ : 0 ≤ J) (hJcap : J ≤ C * n * R ^ 4)
    (hC : 0 ≤ C) (hn : 0 ≤ n) (hA : 0 < A) (hAv : 0 < Av)
    (hAvA : Av ≤ A) :
    R ^ (-2 : Real) * rho * (J * Real.sqrt J) * A⁻¹ ≤
      C ^ (3 / 2 : Real) * n ^ (3 / 2 : Real) *
        R ^ (11 / 2 : Real) * Av⁻¹ := by
  have hRpos : 0 < R := by linarith
  have hq : rho ≤ R ^ (1 / 2 : Real) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt hrho hRpos.le]
    exact hrho2
  have hJprod : J * Real.sqrt J ≤ (C * n * R ^ 4) ^ (3 / 2 : Real) := by
    have hpow := Real.rpow_le_rpow hJ hJcap
      (by norm_num : 0 ≤ (3 / 2 : Real))
    have hJid : J * Real.sqrt J = J ^ (3 / 2 : Real) := by
      rw [Real.sqrt_eq_rpow]
      calc
        J * J ^ (1 / 2 : Real) = J ^ (1 : Real) * J ^ (1 / 2 : Real) := by
          rw [Real.rpow_one]
        _ = J ^ (3 / 2 : Real) := by
          rw [← Real.rpow_add' hJ (by norm_num)]
          congr 1 <;> norm_num
    rw [hJid]
    exact hpow
  have hQid : (C * n * R ^ 4) ^ (3 / 2 : Real) =
      C ^ (3 / 2 : Real) * n ^ (3 / 2 : Real) * R ^ 6 := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC hn,
      ← Real.rpow_natCast R 4, ← Real.rpow_mul hRpos.le]
    norm_num
  have hRpow : R ^ (-2 : Real) * R ^ (1 / 2 : Real) * R ^ 6 ≤
      R ^ (11 / 2 : Real) := by
    rw [← Real.rpow_natCast R 6, ← Real.rpow_add hRpos,
      ← Real.rpow_add hRpos]
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hAinv : A⁻¹ ≤ Av⁻¹ := inv_anti₀ hAv hAvA
  calc
    R ^ (-2 : Real) * rho * (J * Real.sqrt J) * A⁻¹ ≤
      R ^ (-2 : Real) * R ^ (1 / 2 : Real) *
        ((C * n * R ^ 4) ^ (3 / 2 : Real)) * Av⁻¹ := by gcongr
    _ = (C ^ (3 / 2 : Real) * n ^ (3 / 2 : Real)) *
        (R ^ (-2 : Real) * R ^ (1 / 2 : Real) * R ^ 6) * Av⁻¹ := by
          rw [hQid]
          ring
    _ ≤ C ^ (3 / 2 : Real) * n ^ (3 / 2 : Real) *
        R ^ (11 / 2 : Real) * Av⁻¹ := by gcongr

private theorem pointwise_inv_scale_le
    {E : Real} {s : Nat → Real} {N : Nat} {v u : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hN : 1 ≤ N)
    {zeta tau delta : Real} (htau : 0 ≤ tau) (hdelta : 0 ≤ delta) :
    normalizedFarInvScale E s zeta tau delta N v u ≤
      (672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ zeta * capC ^ (3 / 2 : Real) *
        (N : Real) ^ (3 * (tau + 2 * delta) / 2) *
        Step2Moment.ratR E s N v ^ (-2 : Real) *
        (B.scale E N v)⁻¹) *
      (APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
        (etaT E u)⁻¹) := by
  let R := Step2Moment.ratR E s N u
  let rho := B.ell N u / B.ell N (s N)
  let J := APrimeGeneralMovingDriftSource.blockCap E s tau delta N u
  let A := B.scale E N u
  let Av := B.scale E N v
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hR : 1 ≤ R := Step2Moment.one_le_ratR hE hsu hu1
  have hRpos : 0 < R := by linarith
  have hEllS : 0 < B.ell N (s N) := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1)
  have hEllU : 0 < B.ell N u := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0.trans hsu) hu1)
  have hrho : 0 ≤ rho := div_nonneg hEllU.le hEllS.le
  have hrho2 : rho ^ 2 ≤ R := by
    dsimp [rho, R]
    exact Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hsu hu1
  have hJ : 0 ≤ J := by
    dsimp [J, APrimeGeneralMovingDriftSource.blockCap]
    positivity
  have hC : 0 ≤ capC := capC_pos.le
  have hn : 0 ≤ (N : Real) ^ (tau + 2 * delta) := by positivity
  have hJcap : J ≤ capC * (N : Real) ^ (tau + 2 * delta) * R ^ 4 := by
    dsimp [J, capC, R]
    exact blockCap_le_const hN htau hdelta hR
  have hW : 0 < (B.W N : Real) := by exact_mod_cast B.W_pos N
  have hA : 0 < A := B.scale_pos' hE N (hs0.trans hsu) hu1
  have hAv : 0 < Av := B.scale_pos' hE N (hs0.trans (hsu.trans huv)) hv1
  have hAvA : Av ≤ A := by
    have hh := flowScale_antitoneOn hW.le (B.L N) E
      (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 hv1.le) huv
    change B.scale E N v ≤ B.scale E N u
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact hh
  have hcore := ratio_core_le hR hrho hrho2 hJ hJcap hC hn hA hAv hAvA
  have hpow : ((N : Real) ^ (tau + 2 * delta)) ^ (3 / 2 : Real) =
      (N : Real) ^ (3 * (tau + 2 * delta) / 2) := by
    rw [← Real.rpow_mul (by positivity : (0 : Real) ≤ N)]
    congr 1 <;> ring
  have hxi : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have houter : 0 ≤ 672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ zeta * Step2Moment.ratR E s N v ^ (-2 : Real) *
        (etaT E u)⁻¹ := by positivity
  have hraw : normalizedFarInvScale E s zeta tau delta N v u =
      (672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ zeta * Step2Moment.ratR E s N v ^ (-2 : Real) *
        (etaT E u)⁻¹) *
      (R ^ (-2 : Real) * rho * (J * Real.sqrt J) * A⁻¹) := by
    dsimp [normalizedFarInvScale, R, rho, J, A, Band.scale]
    simp only [mul_inv_rev]
    ring
  rw [hraw]
  calc
    _ ≤ (672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ zeta * Step2Moment.ratR E s N v ^ (-2 : Real) *
        (etaT E u)⁻¹) *
      (capC ^ (3 / 2 : Real) *
        ((N : Real) ^ (tau + 2 * delta)) ^ (3 / 2 : Real) *
        R ^ (11 / 2 : Real) * Av⁻¹) :=
      mul_le_mul_of_nonneg_left hcore houter
    _ = _ := by
      rw [hpow]
      dsimp [Av, R]
      rw [show Step2Moment.ratR E s N u =
        APrimeDriftIntegralBudget.ratio (s N) u by
          unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
          rw [Step2.etaT_ratio hE]]
      ring

private theorem sqrt_W_floor_le_N_floor {N : Nat} {W D : Real}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : (N : Real) ≤ W ^ 2)
    (hD : 60 ≤ D) :
    Real.sqrt (W ^ (-D)) ≤ (N : Real) ^ (-(15 : Real)) := by
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hexp : -(D / 2) ≤ -(30 : Real) := by linarith
  have hroot : Real.sqrt (W ^ (-D)) = W ^ (-(D / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]
    congr 1 <;> ring
  have hWpow : W ^ (-(D / 2)) ≤ W ^ (-(30 : Real)) :=
    Real.rpow_le_rpow_of_exponent_le hW hexp
  have hpow : (N : Real) ^ 15 ≤ W ^ 30 := by
    calc
      (N : Real) ^ 15 ≤ (W ^ 2) ^ 15 := by gcongr
      _ = W ^ 30 := by ring
  have hNneg : (N : Real) ^ (-(15 : Real)) =
      ((N : Real) ^ 15)⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    norm_num [Real.rpow_natCast]
  have hWneg : W ^ (-(30 : Real)) = (W ^ 30)⁻¹ := by
    rw [Real.rpow_neg hW0.le]
    norm_num [Real.rpow_natCast]
  calc
    Real.sqrt (W ^ (-D)) = W ^ (-(D / 2)) := hroot
    _ ≤ W ^ (-(30 : Real)) := hWpow
    _ = (W ^ 30)⁻¹ := hWneg
    _ ≤ ((N : Real) ^ 15)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = (N : Real) ^ (-(15 : Real)) := hNneg.symm

private theorem spatial_factor_le_inverse_scale
    {E D : Real} {N : Nat} {u : Real}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hD : 60 ≤ D) (hN : 1 ≤ N)
    (hNW : (N : Real) ≤ (B.W N : Real) ^ 2)
    (hdim : B.W N * B.L N ≤ N) :
    (d.L N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) /
        B.ell N u ≤
      168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ := by
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.one_le_W N
  have hroot := sqrt_W_floor_le_N_floor hN hW1 hNW hD
  have hroot1 : Real.sqrt ((d.W N : Real) ^ (-D)) ≤ (N : Real)⁻¹ := by
    calc
      _ ≤ (N : Real) ^ (-(15 : Real)) := by simpa [B, d, band] using hroot
      _ ≤ (N : Real) ^ (-(1 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
      _ = (N : Real)⁻¹ := by rw [Real.rpow_neg hNpos.le]; norm_num
  have hWL : (d.W N : Real) * (d.L N : Real) ≤ N := by exact_mod_cast hdim
  have hηpos : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hη1 : etaT E u ≤ 1 := etaT_le_one hE hu0
  have hWL0 : 0 ≤ (d.W N : Real) * (d.L N : Real) := by positivity
  have hηmul : (d.W N : Real) * (d.L N : Real) * etaT E u ≤ N := by
    calc
      _ ≤ (d.W N : Real) * (d.L N : Real) := by
        nlinarith [mul_le_mul_of_nonneg_left hη1 hWL0]
      _ ≤ N := hWL
  have hprod : (d.W N : Real) * (d.L N : Real) * etaT E u *
      Real.sqrt ((d.W N : Real) ^ (-D)) ≤ 1 := by
    calc
      _ ≤ (N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) :=
        mul_le_mul_of_nonneg_right hηmul (Real.sqrt_nonneg _)
      _ ≤ (N : Real) * (N : Real)⁻¹ :=
        mul_le_mul_of_nonneg_left hroot1 hNpos.le
      _ = 1 := mul_inv_cancel₀ hNpos.ne'
  have hEll : 0 < B.ell N u := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1)
  have hScale : 0 < (d.W N : Real) * B.ell N u * etaT E u := by positivity
  have hOne : (d.L N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) /
      B.ell N u ≤ ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hScale).2
    calc
      ((d.L N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) /
          B.ell N u) * ((d.W N : Real) * B.ell N u * etaT E u) =
        (d.W N : Real) * (d.L N : Real) * etaT E u *
          Real.sqrt ((d.W N : Real) ^ (-D)) := by field_simp <;> ring
      _ ≤ 1 := hprod
  have hScaleInv : 0 ≤ ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ :=
    inv_nonneg.mpr hScale.le
  exact hOne.trans (by nlinarith)

private theorem leakage_le_inverse_scale
    {E D : Real} {s : Nat → Real} {N : Nat} {v u : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hD : 60 ≤ D)
    (hN : 1 ≤ N) (hNW : (N : Real) ≤ (B.W N : Real) ^ 2)
    (hdim : B.W N * B.L N ≤ N) (zeta tau delta : Real) :
    normalizedFarLeakage E D s zeta tau delta N v u ≤
      normalizedFarInvScale E s zeta tau delta N v u := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hfac := spatial_factor_le_inverse_scale hE (hs0.trans hsu)
    hu1 hD hN hNW hdim
  have hEllS : 0 < B.ell N (s N) := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1)
  have hEllU : 0 < B.ell N u := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0.trans hsu) hu1)
  let P : Real :=
    Step2.xiK (d.L N) (d.W N) (mE E).im *
      Step2Moment.ratR E s N u ^ (-2 : Real) *
      Step2Moment.ratR E s N v ^ (-2 : Real) *
      ((etaT E u)⁻¹ * (4 * (N : Real) ^ zeta *
        (B.ell N u / B.ell N (s N)))) *
      (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
        Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u))
  have hP : 0 ≤ P := by
    have hxi := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    have hru : 0 < Step2Moment.ratR E s N u :=
      Step2Moment.ratR_pos hE hs1 hu1
    have hrv : 0 < Step2Moment.ratR E s N v :=
      Step2Moment.ratR_pos hE hs1 hv1
    have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hJ : 0 ≤ APrimeGeneralMovingDriftSource.blockCap E s tau delta N u := by
      unfold APrimeGeneralMovingDriftSource.blockCap
      positivity
    dsimp [P]
    positivity
  calc
    normalizedFarLeakage E D s zeta tau delta N v u =
      P * ((d.L N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) /
        B.ell N u) := by
        dsimp [P, normalizedFarLeakage]
        field_simp [hEllS.ne', hEllU.ne']
        <;> ring
    _ ≤ P * (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) :=
      mul_le_mul_of_nonneg_left hfac hP
    _ = normalizedFarInvScale E s zeta tau delta N v u := by
      dsimp [P, normalizedFarInvScale]
      ring_nf

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem integral_ratio_eleven_halves {E a v : Real}
    (hE : |E| < 2) (hav : a ≤ v) (hv1 : v < 1) :
    (∫ u in a..v,
      APrimeDriftIntegralBudget.ratio a u ^ (11 / 2 : Real) *
        (etaT E u)⁻¹) =
      (APrimeDriftIntegralBudget.ratio a v ^ (11 / 2 : Real) - 1) /
        ((11 / 2 : Real) * (mE E).im) := by
  have hm := mE_im_pos hE
  have hfun : (fun u => APrimeDriftIntegralBudget.ratio a u ^ (11 / 2 : Real) *
      (etaT E u)⁻¹) =
      (fun u => APrimeDriftIntegralBudget.ratio a u ^ (11 / 2 : Real) /
        ((mE E).im * (1 - u))) := by
    funext u
    rw [Step2.etaT_eq]
    field_simp
    <;> ring
  rw [hfun, APrimeDriftIntegralBudget.integral_ratio_power
    (hav.trans_lt hv1) hav hv1 hm.ne' (by norm_num : (11 / 2 : Real) ≠ 0)]
  ring

private theorem endpoint_margin_product {N : Nat} {R A c : Real}
    (hN : 1 ≤ N) (hc : 0 < c) (hR1 : 1 ≤ R) (hA : 0 < A)
    (hmargin : (N : Real) ^ (c / 10) * R ^ (27 : Real) ≤ A) :
    (R ^ (11 / 2 : Real) - 1) * A⁻¹ ≤ (N : Real) ^ (-(c / 10)) := by
  have hN0 : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hR0 : 0 < R := by linarith
  have hNpow : 0 < (N : Real) ^ (c / 10) := Real.rpow_pos_of_pos hN0 _
  have hRpow : 0 < R ^ (27 : Real) := Real.rpow_pos_of_pos hR0 _
  have hRhalf : R ^ (11 / 2 : Real) ≤ R ^ (27 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hnum : R ^ (11 / 2 : Real) - 1 ≤ R ^ (27 : Real) := by linarith
  have hInv : A⁻¹ ≤ ((N : Real) ^ (c / 10) * R ^ (27 : Real))⁻¹ :=
    inv_anti₀ (mul_pos hNpow hRpow) hmargin
  have hprod : R ^ (27 : Real) * A⁻¹ ≤ ((N : Real) ^ (c / 10))⁻¹ := by
    calc
      _ ≤ R ^ (27 : Real) *
          ((N : Real) ^ (c / 10) * R ^ (27 : Real))⁻¹ :=
        mul_le_mul_of_nonneg_left hInv (Real.rpow_nonneg hR0.le _)
      _ = ((N : Real) ^ (c / 10))⁻¹ := by
        field_simp [hNpow.ne', hRpow.ne']
  calc
    (R ^ (11 / 2 : Real) - 1) * A⁻¹ ≤
        R ^ (27 : Real) * A⁻¹ :=
      mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hA.le)
    _ ≤ ((N : Real) ^ (c / 10))⁻¹ := hprod
    _ = (N : Real) ^ (-(c / 10)) := by
      rw [Real.rpow_neg hN0.le]

private theorem eventually_coefficient_le_margin
    {E c lambda : Real} (hc : 0 < c) (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop,
      672 * capC ^ (3 / 2 : Real) *
        Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (sourceLoss lambda) *
        (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2) ≤
          (N : Real) ^ (c / 20) := by
  let alpha : Real := lambda + sourceLoss lambda +
      3 * (sourceLoss lambda + 2 * capLoss lambda) / 2
  have hgap : 0 < c / 20 - alpha := by
    rw [show alpha = (2801 / 400 : Real) * lambda by
      dsimp [alpha]
      rw [corrected_far_coefficient_exponent]]
    have hlc := hsmall.trans (min_le_right _ _)
    nlinarith [hlc]
  have hconst := eventually_le_rpow (672 * capC ^ (3 / 2 : Real)) hgap
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im hlambda
  filter_upwards [hconst, hxi, eventually_ge_atTop 1] with N hconstN hxiN hN
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : Real) := by linarith
  have hxiN' : Step2.xiK (d.L N) (d.W N) (mE E).im ≤ (N : Real) ^ lambda := by
    simpa only [B, d, band] using hxiN
  have hpow : (N : Real) ^ lambda *
      (N : Real) ^ (sourceLoss lambda) *
      (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2) =
        (N : Real) ^ alpha := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
  have hgapPow : (N : Real) ^ (c / 20 - alpha) * (N : Real) ^ alpha =
      (N : Real) ^ (c / 20) := by
    rw [← Real.rpow_add hN0]
    congr 1 <;> ring
  have hconst0 : 0 ≤ 672 * capC ^ (3 / 2 : Real) := by
    have hcap : 0 ≤ capC := capC_pos.le
    positivity
  calc
    _ ≤ 672 * capC ^ (3 / 2 : Real) *
        (N : Real) ^ lambda * (N : Real) ^ (sourceLoss lambda) *
        (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2) := by
      have hRest0 : 0 ≤ (N : Real) ^ (sourceLoss lambda) *
          (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2) := by
        positivity
      calc
        _ = (672 * capC ^ (3 / 2 : Real)) *
            (Step2.xiK (d.L N) (d.W N) (mE E).im *
              ((N : Real) ^ (sourceLoss lambda) *
                (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2))) := by
          ring
        _ ≤ (672 * capC ^ (3 / 2 : Real)) *
            ((N : Real) ^ lambda *
              ((N : Real) ^ (sourceLoss lambda) *
                (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hxiN' hRest0) hconst0
        _ = _ := by ring
    _ = 672 * capC ^ (3 / 2 : Real) * (N : Real) ^ alpha := by
      calc
        _ = (672 * capC ^ (3 / 2 : Real)) *
            ((N : Real) ^ lambda * (N : Real) ^ (sourceLoss lambda) *
              (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2)) := by
          ring
        _ = _ := by rw [hpow]
    _ ≤ (N : Real) ^ (c / 20 - alpha) * (N : Real) ^ alpha :=
      mul_le_mul_of_nonneg_right hconstN (by positivity)
    _ = _ := hgapPow

/-- The inverse-scale summand has an eventual negative power after the exact
`A_u` interpolation is used at the endpoint. -/
private theorem eventually_inv_scale_integral_le_negative
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedFarInvScale E s (sourceLoss lambda) (sourceLoss lambda)
          (capLoss lambda) N v u) ≤
        (1 / (mE E).im) * (N : Real) ^ (-(c / 20)) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
  have hcoef := eventually_coefficient_le_margin (E := E) hc hlambda hsmall
  have hmargin := APrimeExponents.eventually_monomial_margin
    hE hst ht1 hc hreg
    (δ := 1) (a := c / 10) (b := 27)
    (by norm_num : 0 ≤ (27 : Real)) (by norm_num : (27 : Real) ≤ 30)
    (by nlinarith [hc])
  filter_upwards [hcoef, hmargin, Step2.eventually_le_W_sq B,
      B.dim, eventually_ge_atTop 1] with N hcoefN hmarginN hNW hdim hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNnat : 1 ≤ N := hN
  have hRv1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hv.1 hv1
  have hRv : 0 < Step2Moment.ratR E s N v := by linarith
  let Av := B.scale E N v
  have hAv : 0 < Av := B.scale_pos' hE N ((hs0 N).trans hv.1) hv1
  have hmarginV : (N : Real) ^ (c / 10) *
      Step2Moment.ratR E s N v ^ (27 : Real) ≤ Av := by
    have hh := hmarginN ⟨v, hv⟩
    change (N : Real) ^ (c / 10) *
      Step2Moment.ratR E s N v ^ (27 : Real) ≤ B.scale E N v
    simpa only [mul_one, Step2Moment.ratR] using hh
  have hend := endpoint_margin_product hNnat hc hRv1 hAv hmarginV
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hzeta : 0 ≤ sourceLoss lambda := by dsimp [sourceLoss]; positivity
  have htau : 0 ≤ sourceLoss lambda := by dsimp [sourceLoss]; positivity
  have hdelta : 0 ≤ capLoss lambda := by dsimp [capLoss]; positivity
  let K : Real := 672 * capC ^ (3 / 2 : Real) *
      Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (sourceLoss lambda) *
      (N : Real) ^ (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hxi := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    have hcap : 0 ≤ capC ^ (3 / 2 : Real) := Real.rpow_nonneg capC_pos.le _
    have hpow1 : 0 ≤ (N : Real) ^ (sourceLoss lambda) := by positivity
    have hpow2 : 0 ≤ (N : Real) ^
        (3 * (sourceLoss lambda + 2 * capLoss lambda) / 2) := by positivity
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcap) hxi) hpow1)
      hpow2
  have hKbd : K ≤ (N : Real) ^ (c / 20) := hcoefN
  have hsrcInt : IntervalIntegrable
      (fun u => normalizedFarInvScale E s (sourceLoss lambda)
        (sourceLoss lambda) (capLoss lambda) N v u) volume (s N) v :=
    APrimeGeneralMovingFarNonlinearStrictExponent.intervalIntegrable_normalizedFarInvScale
      hE (hs0 N) hv.1 hv1 (sourceLoss lambda) (sourceLoss lambda) (capLoss lambda)
  have hkernelInt : IntervalIntegrable
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
        (etaT E u)⁻¹) volume (s N) v := by
    have hh := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := (11 / 2 : Real)) hv.1 hv1 hm.ne'
    have heq : (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im
        (s N) (11 / 2 : Real) u) =
        (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
          (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp
      <;> ring
    rw [← heq]
    exact hh
  have hpoint : ∀ u ∈ Icc (s N) v,
      normalizedFarInvScale E s (sourceLoss lambda) (sourceLoss lambda)
        (capLoss lambda) N v u ≤
      (K * Step2Moment.ratR E s N v ^ (-2 : Real) * Av⁻¹) *
        (APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
          (etaT E u)⁻¹) := by
    intro u hu
    have hh := pointwise_inv_scale_le hE (hs0 N) hu.1 hu.2 hv1 hNnat
      htau hdelta (zeta := sourceLoss lambda)
    simpa only [K, Av, mul_assoc, mul_left_comm, mul_comm] using hh
  have hmono := intervalIntegral.integral_mono_on hv.1 hsrcInt
    (hkernelInt.const_mul (K * Step2Moment.ratR E s N v ^ (-2 : Real) * Av⁻¹))
    hpoint
  have hInt : (∫ u in (s N)..v,
      normalizedFarInvScale E s (sourceLoss lambda) (sourceLoss lambda)
        (capLoss lambda) N v u) ≤
      (K * Step2Moment.ratR E s N v ^ (-2 : Real) * Av⁻¹) *
        ((APrimeDriftIntegralBudget.ratio (s N) v ^ (11 / 2 : Real) - 1) /
          ((11 / 2 : Real) * (mE E).im)) := by
    calc
      _ ≤ ∫ u in (s N)..v,
          (K * Step2Moment.ratR E s N v ^ (-2 : Real) * Av⁻¹) *
            (APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
              (etaT E u)⁻¹) := hmono
      _ = (K * Step2Moment.ratR E s N v ^ (-2 : Real) * Av⁻¹) *
          ∫ u in (s N)..v,
            APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
              (etaT E u)⁻¹ := by rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_ratio_eleven_halves hE hv.1 hv1]
  have hRvRatio : APrimeDriftIntegralBudget.ratio (s N) v =
      Step2Moment.ratR E s N v := (ratR_eq_ratio hE).symm
  rw [hRvRatio] at hInt
  have hKprod : K * (N : Real) ^ (-(c / 10)) ≤
      (N : Real) ^ (-(c / 20)) := by
    have hN0 : 0 < (N : Real) := by linarith
    calc
      _ ≤ (N : Real) ^ (c / 20) * (N : Real) ^ (-(c / 10)) :=
        mul_le_mul_of_nonneg_right hKbd (Real.rpow_nonneg hN0.le _)
      _ = (N : Real) ^ (-(c / 20)) := by
        rw [← Real.rpow_add hN0]
        congr 1 <;> ring
  have hRvInv : 0 ≤ Step2Moment.ratR E s N v ^ (-2 : Real) := by positivity
  have hfac1_le : 1 / ((11 / 2 : Real) * (mE E).im) ≤
      1 / (mE E).im := by
    apply one_div_le_one_div_of_le hm
    nlinarith [hm]
  have hnum_nonneg : 0 ≤
      (Step2Moment.ratR E s N v ^ (11 / 2 : Real) - 1) * Av⁻¹ := by
    have hpow := Real.one_le_rpow hRv1 (by norm_num : 0 ≤ (11 / 2 : Real))
    exact mul_nonneg (by linarith) (by positivity)
  calc
    _ ≤ (K * Step2Moment.ratR E s N v ^ (-2 : Real) * Av⁻¹) *
        ((Step2Moment.ratR E s N v ^ (11 / 2 : Real) - 1) /
          ((11 / 2 : Real) * (mE E).im)) := by
      simpa only [mul_assoc] using hInt
    _ = (K * Step2Moment.ratR E s N v ^ (-2 : Real)) *
        ((Step2Moment.ratR E s N v ^ (11 / 2 : Real) - 1) * Av⁻¹) *
          (1 / ((11 / 2 : Real) * (mE E).im)) := by
      have hden : ((11 / 2 : Real) * (mE E).im) ≠ 0 := by positivity
      field_simp [hden, hm.ne']
      <;> ring
    _ ≤ (K * Step2Moment.ratR E s N v ^ (-2 : Real)) *
        ((Step2Moment.ratR E s N v ^ (11 / 2 : Real) - 1) * Av⁻¹) *
          (1 / (mE E).im) := by
      exact mul_le_mul_of_nonneg_left hfac1_le
        (mul_nonneg (mul_nonneg hK hRvInv) hnum_nonneg)
    _ ≤ (K * Step2Moment.ratR E s N v ^ (-2 : Real)) *
        (N : Real) ^ (-(c / 10)) * (1 / (mE E).im) := by
      have hleft0 : 0 ≤ K * Step2Moment.ratR E s N v ^ (-2 : Real) :=
        mul_nonneg hK hRvInv
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hend hleft0) (by positivity)
    _ = (1 / (mE E).im) * (K * (N : Real) ^ (-(c / 10))) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by ring
    _ ≤ (1 / (mE E).im) * (N : Real) ^ (-(c / 20)) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKprod (by positivity)) hRvInv

/-- T615's nonlinear far bracket, both spatial terms included, gains the
strict negative power `N^(-c/20)` and retains the endpoint `ratR(v)^(-2)`.
All structural parameters are fixed before `lambda`; there is no moment-order
parameter in this deterministic profile estimate. -/
theorem eventually_far_nonlinear_integral_le_negative
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedFarNonlinear E D s (sourceLoss lambda) (sourceLoss lambda)
          (capLoss lambda) N v u) ≤
        (2 / (mE E).im) * (N : Real) ^ (-(c / 20)) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
  have hinv := eventually_inv_scale_integral_le_negative
    hE hD hs0 hst ht1 hc hreg hlambda hsmall
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hinv, hNW, B.dim, eventually_ge_atTop 1]
    with N hinvN hNWN hdimN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hN1 : 1 ≤ (N : Real) := by exact_mod_cast hN
  have hNnat : 1 ≤ N := hN
  have hNWreal : (N : Real) ≤ (B.W N : Real) ^ 2 := hNWN
  have hdimreal : B.W N * B.L N ≤ N := by exact_mod_cast hdimN.1
  have hsrcInt : IntervalIntegrable
      (fun u => normalizedFarNonlinear E D s (sourceLoss lambda)
        (sourceLoss lambda) (capLoss lambda) N v u) volume (s N) v :=
    APrimeGeneralMovingDriftFarNonlinearSlot.intervalIntegrable_normalizedFarNonlinear
      hE (hs0 N) hv.1 hv1 (sourceLoss lambda) (sourceLoss lambda) (capLoss lambda)
  have hinvInt : IntervalIntegrable
      (fun u => normalizedFarInvScale E s (sourceLoss lambda)
        (sourceLoss lambda) (capLoss lambda) N v u) volume (s N) v :=
    APrimeGeneralMovingFarNonlinearStrictExponent.intervalIntegrable_normalizedFarInvScale
      hE (hs0 N) hv.1 hv1 (sourceLoss lambda) (sourceLoss lambda) (capLoss lambda)
  have hpoint : ∀ u ∈ Icc (s N) v,
      normalizedFarNonlinear E D s (sourceLoss lambda) (sourceLoss lambda)
        (capLoss lambda) N v u ≤
      2 * normalizedFarInvScale E s (sourceLoss lambda)
        (sourceLoss lambda) (capLoss lambda) N v u := by
    intro u hu
    have hleak := leakage_le_inverse_scale hE (hs0 N) hu.1 hu.2 hv1
      hD hNnat hNWreal hdimreal (sourceLoss lambda) (sourceLoss lambda)
        (capLoss lambda)
    change normalizedFarInvScale E s (sourceLoss lambda) (sourceLoss lambda)
        (capLoss lambda) N v u +
      normalizedFarLeakage E D s (sourceLoss lambda) (sourceLoss lambda)
        (capLoss lambda) N v u ≤ _
    nlinarith
  have hmono := intervalIntegral.integral_mono_on hv.1 hsrcInt
    (hinvInt.const_mul 2) hpoint
  calc
    _ ≤ ∫ u in (s N)..v,
        2 * normalizedFarInvScale E s (sourceLoss lambda)
          (sourceLoss lambda) (capLoss lambda) N v u := hmono
    _ = 2 * ∫ u in (s N)..v,
        normalizedFarInvScale E s (sourceLoss lambda)
          (sourceLoss lambda) (capLoss lambda) N v u :=
      by rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * ((1 / (mE E).im) * (N : Real) ^ (-(c / 20)) *
        Step2Moment.ratR E s N v ^ (-2 : Real)) := by
      exact mul_le_mul_of_nonneg_left (hinvN k hk) (by norm_num)
    _ = (2 / (mE E).im) * (N : Real) ^ (-(c / 20)) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by ring

/-- A same-resident witness for the corrected schedule: one positive-length
window, one active positive cell, one sample in the common event, and positive
actual smooth weight at the requested actual loss. -/
theorem corrected_schedule_nondegenerate_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧ Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ lambda : Real, 0 < lambda →
        lambda ≤ min (1 / 10000 : Real) (c / 10000) →
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧ ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (sourceLoss lambda) (sourceLoss lambda)
                (sourceLoss lambda) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 lambda s t
              (APrimeGeneralMovingMesh.targetMesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh 60) N) ω := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hw⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro lambda hlambda hsmall
  have hsrc : 0 < sourceLoss lambda := by dsimp [sourceLoss]; positivity
  have hctr : 0 < sourceLoss lambda := hsrc
  have htau : 0 < sourceLoss lambda := hsrc
  have hdw : 0 < weightLoss lambda := by dsimp [weightLoss]; exact hlambda
  have hresident := hw (sourceLoss lambda) (sourceLoss lambda)
    (sourceLoss lambda) (weightLoss lambda) hsrc hctr htau hdw
  filter_upwards [hresident] with N hN
  obtain ⟨hwindow, ω, hω, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (fun N u ω => Step2Moment.jSnorm
          (Gauss.sample d) 0 60 s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh 60)
        (weightLoss lambda) 1 N 1 ω = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := weightLoss lambda)
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) hdw.le N 1 1 ω (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos :
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (fun N u ω => Step2Moment.jSnorm
          (Gauss.sample d) 0 60 s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh 60)
        (weightLoss lambda) 1 N 1 ω := by
    rw [hwideOne]
    norm_num
  refine ⟨hwindow, ω, hω, hactive, ?_⟩
  simpa [weightLoss] using hwidePos.trans_le hcompare

theorem negative_constant_pos {E : Real} (hE : |E| < 2) :
    0 < 2 / (mE E).im := by
  positivity [mE_im_pos hE]

theorem exact_T615_nonlinear_identity
    (E D : Real) (s t : Nat → Real) (zeta tau delta : Real)
    (N : Nat) (v u : Real) :
    normalizedFarNonlinear E D s zeta tau delta N v u =
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N u ^ (-2 : Real) *
        Step2Moment.ratR E s N v ^ (-2 : Real) *
        ((etaT E u)⁻¹ * (4 * (N : Real) ^ zeta *
          (B.ell N u / B.ell N (s N))) *
          (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
            Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u) *
            (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ +
              (d.L N : Real) * Real.sqrt ((d.W N : Real) ^ (-D)) /
                B.ell N u))) := by
  exact APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear_eq_T615_bracket
    E D s t zeta tau delta N v u

#print axioms corrected_schedule_room
#print axioms corrected_far_coefficient_exponent
#print axioms exact_T615_nonlinear_identity
#print axioms negative_constant_pos
#print axioms eventually_far_nonlinear_integral_le_negative
#print axioms corrected_schedule_nondegenerate_witness

end

end RBM.APrimeFreeLossFarNonlinear
