/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftIntegralBudget
import RBM1D.Gauss.APrimeOneStep
import RBM1D.Hierarchy.Step2FarInputs
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingDriftSource

/-! # T1015: all-cell integral of the literal far inverse-scale row -/

namespace RBM.APrimeGeneralMovingDriftFarInvScaleSlotRepair

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private noncomputable def capC : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)

private theorem capC_pos : 0 < capC := by unfold capC; positivity

/-- The literal nonlinear inverse-scale summand from T615's accepted far
source coefficient, with both exact transport factors. -/
noncomputable def normalizedFarInvScale (E : Real) (s : Nat → Real)
    (zeta tau delta : Real) (N : Nat) (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    (Step2Moment.ratR E s N u) ^ (-2 : Real) *
    (Step2Moment.ratR E s N v) ^ (-2 : Real) *
    ((etaT E u)⁻¹ * (4 * (N : Real)^zeta *
      (B.ell N u / B.ell N (s N))) *
      (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
        Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u) *
        (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹)))

/-- This is the inverse-scale summand of T615's `farSourceCoeff` with the
actual source cap and endpoint normalization. -/
theorem normalizedFarInvScale_eq_source (E : Real) (s : Nat → Real)
    (zeta tau delta : Real) (N : Nat) (v u : Real) :
    normalizedFarInvScale E s zeta tau delta N v u =
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N u ^ (-2 : Real) *
        Step2Moment.ratR E s N v ^ (-2 : Real) *
        ((etaT E u)⁻¹ * (4 * (N : Real)^zeta *
          (B.ell N u / B.ell N (s N))) *
          (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
            Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u) *
            (168 * (B.scale E N u)⁻¹))) := by
  dsimp [normalizedFarInvScale, APrimeGeneralMovingDriftSource.blockCap, Band.scale]

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem integral_ratio_eleven_halves {E a v : Real}
    (hE : |E| < 2) (hav : a ≤ v) (hv1 : v < 1) :
    (∫ u in a..v, APrimeDriftIntegralBudget.ratio a u ^ (11 / 2 : Real) *
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

private theorem continuousOn_normalizedFarInvScale
    {E : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaCtr tauG delta : Real) :
    ContinuousOn (fun u => normalizedFarInvScale E s zetaCtr tauG delta N v u)
      (Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u, u ∈ Icc (s N) v → 1 - u ≠ 0 := by
      intro u hu; linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRatPos : ∀ u, u ∈ Icc (s N) v → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRatInv : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) (Icc (s N) v) :=
    hRat.rpow_const (fun u hu => Or.inl (ne_of_gt (hRatPos u hu)))
  have hEllPos : ∀ u, u ∈ Icc (s N) v → B.ell N u ≠ 0 := by
    intro u hu
    exact ne_of_gt (zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0.trans hu.1)
        (hu.2.trans_lt hv1)))
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Icc (s N) v) :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hEllRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  have hCap : ContinuousOn (fun u => APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u)
      (Icc (s N) v) := by
    unfold APrimeGeneralMovingDriftSource.blockCap
    have hRat4 : ContinuousOn (fun u => Step2Moment.ratR E s N u ^ (4 : Nat))
        (Icc (s N) v) := hRat.pow 4
    fun_prop
  have hSqrtCap : ContinuousOn
      (fun u => Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u)) (Icc (s N) v) := hCap.sqrt
  have hEtaU : ∀ u, u ∈ Icc (s N) v → etaT E u ≠ 0 :=
    fun u hu => (hEtaPos u hu).ne'
  have hEllConst : B.ell N (s N) ≠ 0 := by
    exact ne_of_gt (zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1))
  have hScale : ContinuousOn
      (fun u => (d.W N : Real) * B.ell N u * etaT E u) (Icc (s N) v) :=
    ((continuousOn_const.mul hEll).mul hEta)
  have hScaleNe : ∀ u, u ∈ Icc (s N) v →
      (d.W N : Real) * B.ell N u * etaT E u ≠ 0 := by
    intro u hu
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (B.W_pos N).ne')
      (hEllPos u hu)) (hEtaU u hu)
  have hScaleInv : ContinuousOn
      (fun u => ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) (Icc (s N) v) :=
    hScale.inv₀ hScaleNe
  unfold normalizedFarInvScale
  fun_prop


private theorem blockCap_le_const
    {E : Real} {s : Nat → Real} {tau delta : Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hR : 1 ≤ Step2Moment.ratR E s N u) :
    APrimeGeneralMovingDriftSource.blockCap E s tau delta N u ≤
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        (N : Real) ^ (tau + 2 * delta) * Step2Moment.ratR E s N u ^ 4 := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
  have hR4 : 1 ≤ Step2Moment.ratR E s N u ^ 4 := one_le_pow₀ hR
  have htauPow : 1 ≤ (N : Real) ^ tau := Real.one_le_rpow hn htau
  have hdeltaPow : 1 ≤ (N : Real) ^ (2 * delta) := Real.one_le_rpow hn (by positivity)
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
    nlinarith [mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real) ^ tau * (N : Real) ^ (2 * delta) =
      (N : Real) ^ (tau + 2 * delta) := by rw [Real.rpow_add hn0]
  unfold APrimeGeneralMovingDriftSource.blockCap
  calc
    1 + (N : Real) ^ tau *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
            Step2Moment.ratR E s N u ^ 4) + 2) <=
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        ((N : Real) ^ tau * (N : Real) ^ (2 * delta)) *
          Step2Moment.ratR E s N u ^ 4 := by
      let X := (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4
      have hmain : (N : Real) ^ tau *
          (9 * Real.exp (Real.sqrt 3) *
            ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
              Step2Moment.ratR E s N u ^ 4)) =
          (9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) * X := by
        dsimp [X]; ring
      rw [mul_add, hmain]
      dsimp only [X] at hX1 htauX ⊢
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
  have hQ : 0 ≤ C * n * R ^ 4 := by positivity
  have hJprod : J * Real.sqrt J ≤ (C * n * R ^ 4) ^ (3 / 2 : Real) := by
    have hpow := Real.rpow_le_rpow hJ hJcap (by norm_num : 0 ≤ (3 / 2 : Real))
    have hJid : J * Real.sqrt J = J ^ (3 / 2 : Real) := by
      rw [Real.sqrt_eq_rpow]
      calc
        J * J ^ (1 / 2 : Real) = J ^ (1 : Real) * J ^ (1 / 2 : Real) := by rw [Real.rpow_one]
        _ = J ^ (3 / 2 : Real) := by rw [← Real.rpow_add' hJ (by norm_num)]; congr 1 <;> norm_num
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
        (R ^ (-2 : Real) * R ^ (1 / 2 : Real) * R ^ 6) * Av⁻¹ := by rw [hQid]; ring
    _ ≤ C ^ (3 / 2 : Real) * n ^ (3 / 2 : Real) *
        R ^ (11 / 2 : Real) * Av⁻¹ := by gcongr


private theorem pointwise_le
    {E : Real} {s : Nat → Real} {N : Nat} {v u : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hN : 1 ≤ N)
    {zeta tau delta : Real} (htau : 0 ≤ tau) (hdelta : 0 ≤ delta) :
    normalizedFarInvScale E s zeta tau delta N v u ≤
      (672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real)^zeta * capC^(3 / 2 : Real) *
        (N : Real)^(3 * (tau + 2 * delta) / 2) *
        (Step2Moment.ratR E s N v)^(-2 : Real) *
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
  have hJ : 0 ≤ J := by dsimp [J, APrimeGeneralMovingDriftSource.blockCap]; positivity
  have hC : 0 ≤ capC := capC_pos.le
  have hn : 0 ≤ (N : Real)^(tau + 2 * delta) := by positivity
  have hJcap : J ≤ capC * (N : Real)^(tau + 2 * delta) * R^4 := by
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
  have hpow : ((N : Real)^(tau + 2 * delta))^(3 / 2 : Real) =
      (N : Real)^(3 * (tau + 2 * delta) / 2) := by
    rw [← Real.rpow_mul (by positivity : (0 : Real) ≤ N)]
    congr 1 <;> ring
  have hxi : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have houter : 0 ≤ 672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real)^zeta * (Step2Moment.ratR E s N v)^(-2 : Real) *
        (etaT E u)⁻¹ := by positivity
  have hraw : normalizedFarInvScale E s zeta tau delta N v u =
      (672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real)^zeta * (Step2Moment.ratR E s N v)^(-2 : Real) *
        (etaT E u)⁻¹) *
      (R^(-2 : Real) * rho * (J * Real.sqrt J) * A⁻¹) := by
    dsimp [normalizedFarInvScale, R, rho, J, A, Band.scale]
    simp only [mul_inv_rev]
    ring
  rw [hraw]
  calc
    _ ≤ (672 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real)^zeta * (Step2Moment.ratR E s N v)^(-2 : Real) *
        (etaT E u)⁻¹) *
        (capC^(3 / 2 : Real) *
          ((N : Real)^(tau + 2 * delta))^(3 / 2 : Real) *
          R^(11 / 2 : Real) * Av⁻¹) :=
      mul_le_mul_of_nonneg_left hcore houter
    _ = _ := by
      rw [hpow]
      dsimp [Av, R]
      rw [ratR_eq_ratio (u := u) hE]
      ring


/-- The literal running source is genuinely interval integrable on every
valid cell, including a degenerate zero cell. -/
theorem intervalIntegrable_normalizedFarInvScale
    {E : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zeta tau delta : Real) :
    IntervalIntegrable
      (fun u => normalizedFarInvScale E s zeta tau delta N v u)
      volume (s N) v :=
  (continuousOn_normalizedFarInvScale hE hs0 hsv hv1 zeta tau delta).intervalIntegrable_of_Icc hsv

/-- At `k=0` the cut endpoint is `s_N`, so the integral is exactly zero. -/
theorem zero_cell_integral_eq_zero
    (E D zeta tau delta : Real) (s : Nat → Real) (N : Nat) :
    (∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0),
      normalizedFarInvScale E s zeta tau delta N
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) u) = 0 := by
  simp only [cutNetPt_zero, intervalIntegral.integral_same]

private theorem endpoint_ratio_le_one {R A As : Real}
    (hR : 1 ≤ R) (hA : 0 < A) (hR30 : R ^ (30 : Nat) ≤ A)
    (_hAAs : A ≤ As) :
    (R ^ (11 / 2 : Real) - 1) * A⁻¹ ≤ 1 := by
  have hRpos : 0 < R := by linarith
  have hpow : R ^ (11 / 2 : Real) ≤ R ^ (30 : Nat) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hnum : R ^ (11 / 2 : Real) - 1 ≤ A := by linarith
  have hdiv : (R ^ (11 / 2 : Real) - 1) / A ≤ 1 := by
    exact (div_le_iff₀ hA).2 (by simpa using hnum)
  simpa only [div_eq_mul_inv] using hdiv

private theorem scheduled_gap {δ : Real} (hδ : 0 < δ) :
    0 < 5 * δ / 32 -
      (δ / 100 + APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
        3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
          2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2) := by
  dsimp [APrimeGeneralMovingSlotLossSchedule.zetaCtr,
    APrimeGeneralMovingSlotLossSchedule.tauG,
    APrimeGeneralMovingSlotLossSchedule.deltaCap]
  linarith

private theorem eventually_coefficient_le {E δ : Real}
    (hδ : 0 < δ) :
    ∀ᶠ N : Nat in atTop,
      672 * capC^(3 / 2 : Real) *
      Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
      (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
        2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2) ≤
      (N : Real)^(5 * δ / 32) := by
  let alpha : Real := δ / 100 + APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
    3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
      2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2
  have hgap : 0 < 5 * δ / 32 - alpha := scheduled_gap hδ
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im
    (by positivity : 0 < δ / 100)
  have hconst := eventually_le_rpow (672 * capC^(3 / 2 : Real)) hgap
  filter_upwards [hxi, hconst, eventually_ge_atTop 1] with N hxiN hconstN hN
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : Real) := by linarith
  have hpow : (N : Real)^(δ / 100) *
      (N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
      (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
        2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2) =
      (N : Real)^alpha := by
    dsimp [alpha]
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
  have hpow2 : (N : Real)^(5 * δ / 32 - alpha) * (N : Real)^alpha =
      (N : Real)^(5 * δ / 32) := by
    rw [← Real.rpow_add hN0]
    congr 1 <;> ring
  calc
    _ ≤ 672 * capC^(3 / 2 : Real) *
        (N : Real)^(δ / 100) *
        (N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
        (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
          2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2) := by
      have hK : 0 ≤ 672 * capC^(3 / 2 : Real) := by
        have := capC_pos
        positivity
      have hZG : 0 ≤ (N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
          (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
            2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2) := by positivity
      have hxiN' : Step2.xiK (d.L N) (d.W N) (mE E).im ≤
          (N : Real)^(δ / 100) := by simpa [B, d, band] using hxiN
      calc
        _ = (672 * capC^(3 / 2 : Real)) *
            (Step2.xiK (d.L N) (d.W N) (mE E).im *
              ((N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
                (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                  2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2))) := by ring
        _ ≤ (672 * capC^(3 / 2 : Real)) *
            ((N : Real)^(δ / 100) *
              ((N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
                (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                  2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hxiN' hZG) hK
        _ = _ := by ring
    _ = (672 * capC^(3 / 2 : Real)) * (N : Real)^alpha := by
      calc
        _ = (672 * capC^(3 / 2 : Real)) *
            ((N : Real)^(δ / 100) *
              (N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
              (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ (N : Real)^(5 * δ / 32 - alpha) * (N : Real)^alpha := by
      exact mul_le_mul_of_nonneg_right hconstN (by positivity)
    _ = _ := hpow2


/-- The literal T615 inverse-scale far summand fits the strict A-prime slot on
all active cells, including the zero cell.  The terminal `ratR(v)⁻²` remains
in the conclusion. -/
theorem eventually_far_inv_scale_integral_le_small_slot
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (_hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (_hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (_hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedFarInvScale E s
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        (1 / (mE E).im) * (N : Real)^(5 * δ / 32) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
  have hcoef := eventually_coefficient_le (E := E) hδ
  have htail := Cond272.pow_thirty_le hE hst ht1 hreg.1
  filter_upwards [hcoef, htail, eventually_ge_atTop 1] with N hcoefN htailN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hRv1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hv.1 hv1
  have hRv : 0 < Step2Moment.ratR E s N v := by linarith
  let Av := B.scale E N v
  let As := B.scale E N (s N)
  have hAv : 0 < Av := B.scale_pos' hE N ((hs0 N).trans hv.1) hv1
  have hAs : 0 < As := B.scale_pos' hE N (hs0 N) hs1
  have hAAs : Av ≤ As := by
    have hW : 0 ≤ (B.W N : Real) := by positivity
    have hh := flowScale_antitoneOn hW (B.L N) E
      (Set.mem_Iic.2 hs1.le) (Set.mem_Iic.2 hv1.le) hv.1
    change B.scale E N v ≤ B.scale E N (s N)
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact hh
  have hRv30 : (Step2Moment.ratR E s N v)^(30 : Nat) ≤ Av := by
    have hh := htailN (⟨v, hv⟩ : TimeIcc s t N)
    simpa only [Step2Moment.ratR] using hh
  have hend := endpoint_ratio_le_one hRv1 hAv hRv30 hAAs
  have hz : 0 ≤ APrimeGeneralMovingSlotLossSchedule.zetaCtr δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.zetaCtr]; positivity
  have htau : 0 ≤ APrimeGeneralMovingSlotLossSchedule.tauG δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.tauG]; positivity
  have hcap : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaCap δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaCap]; positivity
  let K : Real := 672 * capC^(3 / 2 : Real) *
      Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real)^APrimeGeneralMovingSlotLossSchedule.zetaCtr δ *
      (N : Real)^(3 * (APrimeGeneralMovingSlotLossSchedule.tauG δ +
        2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) / 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    have := capC_pos
    have := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    positivity
  have hKbd : K ≤ (N : Real)^(5 * δ / 32) := hcoefN
  let C : Real := K * (Step2Moment.ratR E s N v)^(-2 : Real) * Av⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsrcInt : IntervalIntegrable
      (fun u => normalizedFarInvScale E s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u)
      volume (s N) v :=
    intervalIntegrable_normalizedFarInvScale hE (hs0 N) hv.1 hv1 _ _ _
  have hkernelInt : IntervalIntegrable
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
        (etaT E u)⁻¹) volume (s N) v := by
    have hh := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := (11 / 2 : Real)) hv.1 hv1 hm.ne'
    have heq : (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im (s N)
        (11 / 2 : Real) u) =
        (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
          (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp
      <;> ring
    rw [← heq]
    exact hh
  have hpoint : ∀ u ∈ Icc (s N) v,
      normalizedFarInvScale E s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u ≤
      C * (APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
        (etaT E u)⁻¹) := by
    intro u hu
    have hh := pointwise_le hE (hs0 N) hu.1 hu.2 hv1 hN htau hcap
      (zeta := APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
    simpa only [C, K, Av, mul_assoc, mul_left_comm, mul_comm] using hh
  have hmono := intervalIntegral.integral_mono_on hv.1 hsrcInt
    (hkernelInt.const_mul C) hpoint
  have hInt : (∫ u in (s N)..v,
        normalizedFarInvScale E s
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
      C * ((APrimeDriftIntegralBudget.ratio (s N) v ^ (11 / 2 : Real) - 1) /
        ((11 / 2 : Real) * (mE E).im)) := by
    calc
      _ ≤ ∫ u in (s N)..v,
          C * (APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
            (etaT E u)⁻¹) := hmono
      _ = C * (∫ u in (s N)..v,
          APrimeDriftIntegralBudget.ratio (s N) u ^ (11 / 2 : Real) *
            (etaT E u)⁻¹) := by rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_ratio_eleven_halves hE hv.1 hv1]
  have hend0 : 0 ≤ (Step2Moment.ratR E s N v)^(11 / 2 : Real) - 1 := by
    have hh := Real.one_le_rpow hRv1 (by norm_num : 0 ≤ (11 / 2 : Real))
    linarith
  have hprod : K * ((Step2Moment.ratR E s N v ^ (11 / 2 : Real) - 1) * Av⁻¹) ≤
      (N : Real)^(5 * δ / 32) := by
    calc
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hend hK
      _ = K := by ring
      _ ≤ _ := hKbd
  have hq : (1 / ((11 / 2 : Real) * (mE E).im)) ≤ 1 / (mE E).im := by
    apply one_div_le_one_div_of_le hm
    nlinarith [hm]
  calc
    _ ≤ C * ((APrimeDriftIntegralBudget.ratio (s N) v ^ (11 / 2 : Real) - 1) /
        ((11 / 2 : Real) * (mE E).im)) := hInt
    _ = (1 / ((11 / 2 : Real) * (mE E).im)) *
        (Step2Moment.ratR E s N v)^(-2 : Real) *
        (K * ((Step2Moment.ratR E s N v ^ (11 / 2 : Real) - 1) * Av⁻¹)) := by
      rw [← ratR_eq_ratio (u := v) hE]
      dsimp [C]
      ring
    _ ≤ (1 / ((11 / 2 : Real) * (mE E).im)) *
        (Step2Moment.ratR E s N v)^(-2 : Real) *
        (N : Real)^(5 * δ / 32) := by gcongr
    _ ≤ (1 / (mE E).im) *
        (Step2Moment.ratR E s N v)^(-2 : Real) *
        (N : Real)^(5 * δ / 32) := by gcongr
    _ = _ := by ring

/-- The T995 same-event actual smooth-weight witness is nondegenerate at the
first positive cell of the same scheduled regime. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms intervalIntegrable_normalizedFarInvScale
#print axioms zero_cell_integral_eq_zero
#print axioms normalizedFarInvScale_eq_source
#print axioms eventually_far_inv_scale_integral_le_small_slot
#print axioms nondegenerate_positive_cell_witness

end RBM.APrimeGeneralMovingDriftFarInvScaleSlotRepair
