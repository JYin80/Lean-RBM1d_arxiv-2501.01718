/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVFixedTwo
import RBM1D.Gauss.APrimeFirstCellLoopCap
import RBM1D.Gauss.APrimeFirstCellQVRunningSmall
import RBM1D.Gauss.APrimeQVIntegralBudget

/-!
# T438: fixed-two current QV rows at the moving first-cell endpoint

This file keeps T437's literal moving endpoint and its full `rootProfile`
until the two `W⁻⁶⁰` corrections and the repaired `W⁻¹` near coefficient
have been paid.  The resulting three rows are the current rows of
(5.40)--(5.42).
-/

namespace RBM.APrimeFirstCellQVCurrentRows

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def currentConstant : ℝ := 9 * 2048 * 8

theorem currentConstant_pos : 0 < currentConstant := by
  norm_num [currentConstant]

/-- The three pointwise current rows, with the exact moving normalization. -/
noncomputable def currentRate (δ τ ν : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  currentConstant * (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
    APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) *
      (APrimeFirstCellLoopCap.xRate r ^ (-(3 / 2 : ℝ)) +
        (N : ℝ) ^ (4 * δ + 2 * τ) *
          (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
            APrimeFirstCellLoopCap.xRate r ^ (19 / 4 : ℝ) +
        (N : ℝ) ^ (6 * δ + 3 * τ) *
          (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
            APrimeFirstCellLoopCap.xRate r ^ (8 : ℝ))

noncomputable def preRows (δ τ : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  APrimeFirstCellLoopCap.xRate r ^ (5 / 2 : ℝ) +
    (N : ℝ) ^ (4 * δ + 2 * τ) *
      (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
        APrimeFirstCellLoopCap.xRate r ^ (35 / 4 : ℝ) +
    (N : ℝ) ^ (6 * δ + 3 * τ) *
      (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
        APrimeFirstCellLoopCap.xRate r ^ (12 : ℝ)

private theorem sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  have hxy : 0 ≤ √x * √y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt (add_nonneg hx hy), Real.sqrt_nonneg x,
    Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y)]

/-- A three-summand endpoint profile costs the factor nine after squaring.
The endpoint leakage remains a separate input up to this lemma. -/
theorem normalized_three_term_sq_le
    {An Af K T Xi leak χ R M X : ℝ}
    (hAn : 0 ≤ An) (hAf : 0 ≤ Af) (hK : 0 ≤ K) (hT : 0 < T)
    (hXi0 : 0 ≤ Xi) (hleak0 : 0 ≤ leak) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hR : 0 < R) (hM : An + Af ≤ M) (hXi : Xi ≤ X) (hleak : leak ≤ X) :
    ((T * R ^ 4)⁻¹ *
        (√An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T))) ^ 2 ≤
      9 * M * X ^ 2 * K ^ 2 * R ^ (-(8 : ℝ)) := by
  have hM0 : 0 ≤ M := (add_nonneg hAn hAf).trans hM
  have hX0 : 0 ≤ X := hXi0.trans hXi
  have hAnM : An ≤ M := by linarith
  have hAfM : Af ≤ M := by linarith
  have hsAn : √An ≤ √M := Real.sqrt_le_sqrt hAnM
  have hsAf : √Af ≤ √M := Real.sqrt_le_sqrt hAfM
  have hroot :
      √An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T) ≤
        3 * √M * K * T * X := by
    have hχXi : Xi * χ ≤ X := by
      calc
        Xi * χ ≤ Xi * 1 := mul_le_mul_of_nonneg_left hχ1 hXi0
        _ ≤ X := by simpa using hXi
    have hχXi0 : 0 ≤ Xi * χ := mul_nonneg hXi0 hχ0
    have hKT0 : 0 ≤ K * T := mul_nonneg hK hT.le
    have h1 : √An * (K * Xi * T * χ) ≤ √M * (K * X * T) := by
      calc
        _ = √An * ((K * T) * (Xi * χ)) := by ring
        _ ≤ √M * ((K * T) * X) := by
          exact mul_le_mul hsAn
            (mul_le_mul_of_nonneg_left hχXi hKT0)
            (mul_nonneg hKT0 hχXi0) (Real.sqrt_nonneg _)
        _ = _ := by ring
    have h2 : √An * (leak * K * T) ≤ √M * (X * K * T) := by
      have hright := mul_le_mul_of_nonneg_right hleak hKT0
      exact mul_le_mul hsAn (by simpa [mul_assoc, mul_left_comm, mul_comm] using hright)
        (by positivity) (Real.sqrt_nonneg _)
    have h3 : √Af * (K * Xi * T) ≤ √M * (K * X * T) := by
      have hright := mul_le_mul_of_nonneg_left hXi hKT0
      exact mul_le_mul hsAf
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hright)
        (by positivity) (Real.sqrt_nonneg _)
    calc
      _ = √An * (K * Xi * T * χ) + √An * (leak * K * T) +
          √Af * (K * Xi * T) := by ring
      _ ≤ √M * (K * X * T) + √M * (X * K * T) + √M * (K * X * T) :=
        add_le_add (add_le_add h1 h2) h3
      _ = 3 * √M * K * T * X := by ring
  have hroot0 : 0 ≤
      √An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T) := by
    positivity
  have hscale : 0 < T * R ^ 4 := mul_pos hT (pow_pos hR 4)
  have hnorm :
      (T * R ^ 4)⁻¹ *
          (√An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T)) ≤
        3 * √M * K * X * R ^ (-(4 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hroot (inv_pos.mpr hscale).le
    calc
      _ ≤ (T * R ^ 4)⁻¹ * (3 * √M * K * T * X) := hh
      _ = 3 * √M * K * X * R ^ (-(4 : ℝ)) := by
        have hRpow : R ^ (-(4 : ℝ)) = (R ^ (4 : ℕ))⁻¹ := by
          rw [Real.rpow_neg hR.le]
          norm_num only [Real.rpow_ofNat]
        rw [hRpow]
        field_simp [hT.ne', hR.ne']
  have hnorm0 : 0 ≤ (T * R ^ 4)⁻¹ *
      (√An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T)) :=
    mul_nonneg (inv_nonneg.mpr hscale.le) hroot0
  have hsq := pow_le_pow_left₀ hnorm0 hnorm 2
  calc
    _ ≤ (3 * √M * K * X * R ^ (-(4 : ℝ))) ^ 2 := hsq
    _ = 9 * M * X ^ 2 * K ^ 2 * R ^ (-(8 : ℝ)) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM0]
      have hR8 : (R ^ (-(4 : ℝ))) ^ 2 = R ^ (-(8 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
        norm_num
      rw [hR8]
      ring

/-- The exact endpoint-kernel algebra gives the `R⁻⁴ x⁻⁴` prefactor. -/
theorem endpoint_kernel_power {R x : ℝ} (hR : 0 < R) (hx : 0 < x) :
    ((R / x) ^ 2) ^ 2 * R ^ (-(8 : ℝ)) =
      R ^ (-(4 : ℝ)) * x ^ (-(4 : ℝ)) := by
  have hR8 : R ^ (-(8 : ℝ)) = (R ^ (8 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hR.le]
    norm_num only [Real.rpow_ofNat]
  have hR4 : R ^ (-(4 : ℝ)) = (R ^ (4 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hR.le]
    norm_num only [Real.rpow_ofNat]
  have hx4 : x ^ (-(4 : ℝ)) = (x ^ (4 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hx.le]
    norm_num only [Real.rpow_ofNat]
  rw [hR8, hR4, hx4]
  field_simp [hR.ne', hx.ne']

/-- The T418 source amplitude supplies the quadratic row with only its
literal `N^ζ` loss. -/
theorem source_four_sqrt_le {N ζ ell x Ar Av : ℝ}
    (hN : 1 ≤ N) (hζ : 0 ≤ ζ) (hx : 1 ≤ x)
    (hell0 : 0 ≤ ell) (hell : ell ≤ Real.sqrt x)
    (hAr : 0 < Ar) (hAv : 0 < Av) (hAvAr : Av ≤ Ar) :
    Ar * √(N ^ ζ * ell ^ (3 : ℕ) * Ar⁻¹ ^ (3 : ℕ)) ≤
      N ^ ζ * Av ^ (-(1 / 2 : ℝ)) * x ^ (3 / 4 : ℝ) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hS0 : 0 ≤ N ^ ζ * ell ^ (3 : ℕ) * Ar⁻¹ ^ (3 : ℕ) := by positivity
  have hleft0 : 0 ≤ Ar * √(N ^ ζ * ell ^ (3 : ℕ) * Ar⁻¹ ^ (3 : ℕ)) := by
    positivity
  have hright0 : 0 ≤ N ^ ζ * Av ^ (-(1 / 2 : ℝ)) * x ^ (3 / 4 : ℝ) := by
    positivity
  have hleftsq :
      (Ar * √(N ^ ζ * ell ^ (3 : ℕ) * Ar⁻¹ ^ (3 : ℕ))) ^ 2 =
        N ^ ζ * ell ^ (3 : ℕ) * Ar⁻¹ := by
    rw [mul_pow, Real.sq_sqrt hS0]
    field_simp [hAr.ne']
  have hell3 : ell ^ (3 : ℕ) ≤ x ^ (3 / 2 : ℝ) := by
    have hp := pow_le_pow_left₀ hell0 hell 3
    calc
      ell ^ (3 : ℕ) ≤ (Real.sqrt x) ^ (3 : ℕ) := hp
      _ = x ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        norm_num
  have hAinv : Ar⁻¹ ≤ Av⁻¹ := inv_anti₀ hAv hAvAr
  have hNz1 : 1 ≤ N ^ ζ := Real.one_le_rpow hN hζ
  have hraw : N ^ ζ * ell ^ (3 : ℕ) * Ar⁻¹ ≤
      (N ^ ζ * N ^ ζ) * Av⁻¹ * x ^ (3 / 2 : ℝ) := by
    have hNζ0 : 0 ≤ N ^ ζ := Real.rpow_nonneg hN0.le _
    have hxpow0 : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hAi0 : 0 ≤ Ar⁻¹ := inv_nonneg.mpr hAr.le
    have hAvi0 : 0 ≤ Av⁻¹ := inv_nonneg.mpr hAv.le
    calc
      _ ≤ N ^ ζ * x ^ (3 / 2 : ℝ) * Ar⁻¹ := by gcongr
      _ ≤ N ^ ζ * x ^ (3 / 2 : ℝ) * Av⁻¹ := by gcongr
      _ ≤ (N ^ ζ * N ^ ζ) * x ^ (3 / 2 : ℝ) * Av⁻¹ := by
        have hh : N ^ ζ ≤ N ^ ζ * N ^ ζ := by nlinarith
        gcongr
      _ = _ := by ring
  have hrightsq :
      (N ^ ζ * Av ^ (-(1 / 2 : ℝ)) * x ^ (3 / 4 : ℝ)) ^ 2 =
        (N ^ ζ * N ^ ζ) * Av⁻¹ * x ^ (3 / 2 : ℝ) := by
    have hAvpow : (Av ^ (-(1 / 2 : ℝ))) ^ 2 = Av⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hAv.le]
      norm_num [Real.rpow_neg_one]
    have hxpow : (x ^ (3 / 4 : ℝ)) ^ 2 = x ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [mul_pow, mul_pow, hAvpow, hxpow]
    ring
  nlinarith

/-- Exact fifth-power source loss, followed by the first-cell
`ell_r ≤ sqrt x_r` comparison. -/
theorem source_near_fifth_le {N : ℕ} {ζ ell x : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hx : 1 ≤ x)
    (hell0 : 0 ≤ ell) (hell : ell ≤ Real.sqrt x) :
    (ell / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) ≤
      2 * (N : ℝ) ^ ζ * x ^ (5 / 2 : ℝ) := by
  have hN0 : 0 < (N : ℝ) := zero_lt_one.trans_le hN
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hp := pow_le_pow_left₀ hell0 hell 5
  have hsqrt : (Real.sqrt x) ^ (5 : ℕ) = x ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  rw [show (ell / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) =
      2 * (N : ℝ) ^ ζ * ell ^ (5 : ℕ) by
    simpa [APrimeFirstCellSourceAllTime.ellSource,
      APrimeFirstCellJGCap.sourceEll] using
        APrimeFirstCellQVSmall.source_near_ratio_fifth N ζ ell hN0]
  gcongr
  simpa only [hsqrt] using hp

set_option maxHeartbeats 1000000 in
-- The expanded coefficient contains several nested real powers.
/-- T280g's coefficient bound specialized to the literal block value two.
The raw spatial floor and repaired near floor are consumed only through the
two displayed hypotheses. -/
theorem fixed_two_coefficient_le (N : ℕ) {ζ δ τ r v C : ℝ}
    (hr0 : 0 ≤ r) (hrv : r ≤ v) (hv1 : v < 1)
    (hN : 1 ≤ (N : ℝ)) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hC : 1 ≤ C)
    (hNear : Lemma57.cNear2 (d.W N : ℝ) (B.ell N r) ≤ C)
    (hFar : Lemma57.cFar2 (d.W N : ℝ) (B.ell N r) ≤ C)
    (hLeak : (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
      (etaT 0 r)⁻¹ * (B.scale 0 N r)⁻¹)
    (hFloor : (d.W N : ℝ)⁻¹ ≤ (etaT 0 r)⁻¹ *
      (B.ell N r / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ)) :
    APrimeQVEndpoint.diagNearRate B N (B.ell N r)
        (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 r) +
      2 * (d.W N : ℝ)⁻¹ +
      APrimeQVEndpoint.diagFarRate B N (B.ell N r) (etaT 0 r) 60 2
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) ≤
      16384 * C * (N : ℝ) ^ ζ * (etaT 0 r)⁻¹ * preRows δ τ N v r := by
  have hr1 : r < 1 := hrv.trans_lt hv1
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hη : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast B.one_le_W N
  have hell1 : 1 ≤ B.ell N r :=
    one_le_ellHat (d.L N) (d.three_le_L N) hr0 hr1
  have hell0 : 0 ≤ B.ell N r := zero_le_one.trans hell1
  have hx : 1 ≤ APrimeFirstCellLoopCap.xRate r := by
    simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hr0 hr1)
  have hell : B.ell N r ≤ Real.sqrt (APrimeFirstCellLoopCap.xRate r) := by
    have hh := Step3.ellHat_le_sqrt_mul
      (L := B.L N) (s := 0) (t := r) hr0 hr1
    have hz : ellHat (B.L N) ((0 : ℝ) : ℂ) = 1 :=
      ellHat_zero (B.L N) (B.three_le_L N)
    rw [hz, mul_one] at hh
    change ellHat (B.L N) (r : ℂ) ≤ _
    simpa only [APrimeFirstCellLoopCap.xRate, etaT, mE_zero,
      Complex.I_im, mul_one, sub_zero, one_mul] using hh
  have hAr : 0 < B.scale 0 N r := B.scale_pos' (by norm_num) N hr0 hr1
  have hAv : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
    B.scale_pos' (by norm_num) N hv0 hv1
  have hAvAr : APrimeFirstCellLoopCap.endpointScale N v ≤ B.scale 0 N r := by
    rw [APrimeFirstCellLoopCap.endpointScale, B.scale_eq_flowScale,
      B.scale_eq_flowScale]
    exact flowScale_antitoneOn (show (0 : ℝ) ≤ B.W N by positivity)
      (B.L N) 0 (Set.mem_Iic.2 hr1.le) (Set.mem_Iic.2 hv1.le) hrv
  have hsource := source_four_sqrt_le hN hζ hx hell0 hell hAr hAv hAvAr
  have hsource' : B.scale 0 N r *
      √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r) ≤
        (N : ℝ) ^ ζ *
          (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
            APrimeFirstCellLoopCap.xRate r ^ (3 / 4 : ℝ) := by
    simpa only [APrimeFirstCellSourceAllTime.sourceC4] using hsource
  have hnear := source_near_fifth_le (N := N) (ζ := ζ)
    (ell := B.ell N r) (x := APrimeFirstCellLoopCap.xRate r)
    hN hx hell0 hell
  have hcoeff := APrimeFullQV.ExponentRows.coefficient_bound
    (W := (d.W N : ℝ)) (L := (d.L N : ℝ))
    (ℓu := B.ell N r)
    (ℓs := APrimeFirstCellSourceAllTime.ellSource ζ N)
    (ηu := etaT 0 r) (D := 60) (J := 2)
    (S := APrimeFirstCellSourceAllTime.sourceC4 ζ N r) (C := C)
    hW (lt_of_lt_of_le zero_lt_one hell1)
    (by unfold APrimeFirstCellSourceAllTime.ellSource; positivity)
    hη (by norm_num) hC hNear hFar hLeak hFloor
  have hNδ : 1 ≤ (N : ℝ) ^ (4 * δ + 2 * τ) :=
    Real.one_le_rpow hN (by positivity)
  have hNδ3 : 1 ≤ (N : ℝ) ^ (6 * δ + 3 * τ) :=
    Real.one_le_rpow hN (by positivity)
  have hx35 : APrimeFirstCellLoopCap.xRate r ^ (3 / 4 : ℝ) ≤
      APrimeFirstCellLoopCap.xRate r ^ (35 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hx12 : 1 ≤ APrimeFirstCellLoopCap.xRate r ^ (12 : ℝ) :=
    Real.one_le_rpow hx (by norm_num)
  have hAinv : (B.scale 0 N r)⁻¹ ≤
      (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ := inv_anti₀ hAv hAvAr
  have hNζ1 : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN hζ
  let q2 := (N : ℝ) ^ (4 * δ + 2 * τ) *
    (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
      APrimeFirstCellLoopCap.xRate r ^ (35 / 4 : ℝ)
  let q3 := (N : ℝ) ^ (6 * δ + 3 * τ) *
    (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
      APrimeFirstCellLoopCap.xRate r ^ (12 : ℝ)
  have hq20 : 0 ≤ q2 := by dsimp [q2]; positivity
  have hq30 : 0 ≤ q3 := by dsimp [q3]; positivity
  have hrow2 : 4 * (B.scale 0 N r *
      √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r)) ≤
      4 * (N : ℝ) ^ ζ * q2 := by
    have hbase : B.scale 0 N r *
        √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r) ≤
        (N : ℝ) ^ ζ * q2 := by
      calc
        _ ≤ (N : ℝ) ^ ζ *
          (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
            APrimeFirstCellLoopCap.xRate r ^ (3 / 4 : ℝ) := hsource'
        _ ≤ (N : ℝ) ^ ζ *
            ((APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
              APrimeFirstCellLoopCap.xRate r ^ (35 / 4 : ℝ)) := by
          have hfac0 : 0 ≤ (N : ℝ) ^ ζ *
              (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) := by
            positivity
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx35 hfac0
        _ ≤ (N : ℝ) ^ ζ * q2 := by
          have hfac0 : 0 ≤
              (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
                APrimeFirstCellLoopCap.xRate r ^ (35 / 4 : ℝ) := by positivity
          dsimp [q2]
          have hh := mul_le_mul_of_nonneg_right hNδ hfac0
          nlinarith
    nlinarith
  have hrow3 : 8 * (B.scale 0 N r)⁻¹ ≤
      8 * (N : ℝ) ^ ζ * q3 := by
    have hbase : (B.scale 0 N r)⁻¹ ≤ (N : ℝ) ^ ζ * q3 := by
      calc
        _ ≤ (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ := hAinv
        _ ≤ q3 := by
          have hAvinv0 : 0 ≤ (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ :=
            inv_nonneg.mpr hAv.le
          have hfac : 1 ≤ (N : ℝ) ^ (6 * δ + 3 * τ) *
              APrimeFirstCellLoopCap.xRate r ^ (12 : ℝ) :=
            one_le_mul_of_one_le_of_one_le hNδ3 hx12
          dsimp [q3]
          have hh := mul_le_mul_of_nonneg_left hfac hAvinv0
          nlinarith
        _ ≤ (N : ℝ) ^ ζ * q3 := by
          have hq30' : 0 ≤ q3 := hq30
          nlinarith [mul_nonneg (sub_nonneg.mpr hNζ1) hq30']
    nlinarith
  have hbracket :
      (B.ell N r / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) +
        (2 : ℝ) ^ 2 * (B.scale 0 N r) *
          √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r) +
        (2 : ℝ) ^ 3 * (B.scale 0 N r)⁻¹ ≤
      8 * (N : ℝ) ^ ζ * preRows δ τ N v r := by
    change _ ≤ 8 * (N : ℝ) ^ ζ *
      (APrimeFirstCellLoopCap.xRate r ^ (5 / 2 : ℝ) + q2 + q3)
    have hnear' :
        (B.ell N r / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) ≤
          8 * (N : ℝ) ^ ζ * APrimeFirstCellLoopCap.xRate r ^ (5 / 2 : ℝ) :=
      hnear.trans (by gcongr <;> norm_num)
    have hNζ0 : 0 ≤ (N : ℝ) ^ ζ := Real.rpow_nonneg (by positivity) _
    have hx50 : 0 ≤ APrimeFirstCellLoopCap.xRate r ^ (5 / 2 : ℝ) := by positivity
    calc
      _ ≤ 8 * (N : ℝ) ^ ζ * APrimeFirstCellLoopCap.xRate r ^ (5 / 2 : ℝ) +
          4 * (N : ℝ) ^ ζ * q2 + 8 * (N : ℝ) ^ ζ * q3 :=
        add_le_add (add_le_add hnear' (by convert hrow2 using 1 <;> norm_num <;> ring))
          (by convert hrow3 using 1 <;> norm_num <;> ring)
      _ ≤ 8 * (N : ℝ) ^ ζ *
          (APrimeFirstCellLoopCap.xRate r ^ (5 / 2 : ℝ) + q2 + q3) := by
        have h4q : 4 * (N : ℝ) ^ ζ * q2 ≤ 8 * (N : ℝ) ^ ζ * q2 := by
          nlinarith [mul_nonneg hNζ0 hq20]
        linarith
  have hBW : B.W N = d.W N := rfl
  have hBL : B.L N = d.L N := rfl
  calc
    _ ≤ 2048 * C * (etaT 0 r)⁻¹ *
        ((B.ell N r / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) +
          (2 : ℝ) ^ 2 * (B.scale 0 N r) *
            √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r) +
          (2 : ℝ) ^ 3 * (B.scale 0 N r)⁻¹) := by
      simpa only [APrimeQVEndpoint.diagNearRate,
        APrimeQVEndpoint.diagFarRate, Band.scale, hBW, hBL] using hcoeff
    _ ≤ 2048 * C * (etaT 0 r)⁻¹ *
        (8 * (N : ℝ) ^ ζ * preRows δ τ N v r) := by gcongr
    _ = _ := by ring

/-- Multiplication by the endpoint kernel's `x⁻⁴` turns the pre-rows into
the three current exponents. -/
theorem x_neg_four_mul_preRows {x N Av δ τ : ℝ}
    (hx : 0 < x) :
    x ^ (-(4 : ℝ)) *
        (x ^ (5 / 2 : ℝ) +
          N ^ (4 * δ + 2 * τ) * Av ^ (-(1 / 2 : ℝ)) * x ^ (35 / 4 : ℝ) +
          N ^ (6 * δ + 3 * τ) * Av⁻¹ * x ^ (12 : ℝ)) =
      x ^ (-(3 / 2 : ℝ)) +
        N ^ (4 * δ + 2 * τ) * Av ^ (-(1 / 2 : ℝ)) * x ^ (19 / 4 : ℝ) +
        N ^ (6 * δ + 3 * τ) * Av⁻¹ * x ^ (8 : ℝ) := by
  have hnear : x ^ (-(4 : ℝ)) * x ^ (5 / 2 : ℝ) = x ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have htwo : x ^ (-(4 : ℝ)) * x ^ (35 / 4 : ℝ) = x ^ (19 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hthree : x ^ (-(4 : ℝ)) * x ^ (12 : ℝ) = x ^ (8 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [mul_add, mul_add]
  calc
    _ = x ^ (-(4 : ℝ)) * x ^ (5 / 2 : ℝ) +
        N ^ (4 * δ + 2 * τ) * Av ^ (-(1 / 2 : ℝ)) *
          (x ^ (-(4 : ℝ)) * x ^ (35 / 4 : ℝ)) +
        N ^ (6 * δ + 3 * τ) * Av⁻¹ *
          (x ^ (-(4 : ℝ)) * x ^ (12 : ℝ)) := by ring
    _ = _ := by rw [hnear, htwo, hthree]

/-- The literal first-cell kernel ratio equals `R_v/x_r`. -/
theorem time_ratio_eq_xRate_div {r v : ℝ} (hr1 : r < 1) (hv1 : v < 1) :
    (1 - r) / (1 - v) =
      APrimeFirstCellLoopCap.xRate v / APrimeFirstCellLoopCap.xRate r := by
  simp only [APrimeFirstCellLoopCap.xRate, etaT, mE_zero,
    Complex.I_im, mul_one, sub_zero]
  field_simp [show 1 - r ≠ 0 by linarith, show 1 - v ≠ 0 by linarith]

set_option maxHeartbeats 1000000 in
-- The proof unfolds the full endpoint profile once and then applies the scalar lemmas above.
/-- Pointwise conversion of T437's full fixed-two profile to the current
three-row rate.  Both `W⁻⁶⁰` terms are still explicit hypotheses here. -/
theorem fixedTwoMovingProfileAt_le_currentRate
    {δ ν : ℝ} (hδ : 0 ≤ δ) (hν : 0 < ν)
    {N : ℕ} {ω : Ω d} {v r : ℝ} {a : LoopArg (d.L N) 2}
    (hr0 : 0 ≤ r) (hrv : r ≤ v) (hv1 : v < 1)
    (hN : 1 ≤ (N : ℝ))
    (hNear : Lemma57.cNear2 (d.W N : ℝ) (B.ell N r) ≤ (N : ℝ) ^ (ν / 8))
    (hFar : Lemma57.cFar2 (d.W N : ℝ) (B.ell N r) ≤ (N : ℝ) ^ (ν / 8))
    (hLeak : (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
      (etaT 0 r)⁻¹ * (B.scale 0 N r)⁻¹)
    (hFloor : (d.W N : ℝ)⁻¹ ≤ (etaT 0 r)⁻¹ *
      (B.ell N r / APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) ^ (5 : ℕ))
    (hXi : Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im ≤
      (N : ℝ) ^ (ν / 8))
    (hEndpointLeak : 256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
      (N : ℝ) ^ (ν / 8))
    (hfixed : APrimeFirstCellQVFixedTwo.fixedTwoMovingProfileAt
      ν N ω v r a) :
    APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      currentRate δ (δ / 16) ν N v r := by
  let ζ := APrimeFirstCellEGAllOutputRunning.sourceLoss ν
  let x := APrimeFirstCellLoopCap.xRate r
  let R := APrimeFirstCellLoopCap.xRate v
  let Av := APrimeFirstCellLoopCap.endpointScale N v
  let ellS := APrimeFirstCellSourceAllTime.ellSource ζ N
  let S := APrimeFirstCellSourceAllTime.sourceC4 ζ N r
  let An := APrimeQVEndpoint.diagNearRate B N (B.ell N r) ellS (etaT 0 r) +
    2 * (d.W N : ℝ)⁻¹
  let Af := APrimeQVEndpoint.diagFarRate B N (B.ell N r) (etaT 0 r) 60 2 S
  let K := ((1 - r) / (1 - v)) ^ 2
  let T := Step2.tT B 0 N 60 v (zdist (B.L N) (a 0 - a 1))
  let Xi := Step2.xiK (B.L N) (B.W N : ℝ) (mE 0).im
  let leak := 256 * Real.exp 3 * (B.W N : ℝ) ^ (-(60 : ℝ))
  let χ : ℝ := if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
      6 * ellStar (B.W N : ℝ) (B.ell N v) then 1 else 0
  let X := (N : ℝ) ^ (ν / 8)
  let M := 16384 * X * (N : ℝ) ^ ζ * (etaT 0 r)⁻¹ *
    preRows δ (δ / 16) N v r
  have hr1 : r < 1 := hrv.trans_lt hv1
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hηr : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hx : 1 ≤ x := by
    dsimp [x]
    simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hr0 hr1)
  have hR : 1 ≤ R := by
    dsimp [R]
    simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hv0 hv1)
  have hζ0 : 0 ≤ ζ :=
    (APrimeFirstCellEGAllOutputRunning.sourceLoss_pos hν).le
  have hX1 : 1 ≤ X := Real.one_le_rpow hN (by positivity)
  have hcoeff : An + Af ≤ M := by
    dsimp [An, Af, M, X, ellS, S, ζ]
    exact fixed_two_coefficient_le N hr0 hrv hv1 hN hζ0 hδ
      (by positivity : 0 ≤ δ / 16) hX1 hNear hFar hLeak hFloor
  have hAn : 0 ≤ An := by
    dsimp [An, ellS]
    have hc := Lemma57.cNear2_nonneg
      (show 1 ≤ (d.W N : ℝ) by exact_mod_cast B.one_le_W N)
      (show 0 < B.ell N r by
        exact lt_of_lt_of_le zero_lt_one
          (one_le_ellHat (d.L N) (d.three_le_L N) hr0 hr1))
    have hmain : 0 ≤ APrimeQVEndpoint.diagNearRate B N (B.ell N r)
        (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 r) := by
      unfold APrimeQVEndpoint.diagNearRate
      have hellS : 0 < APrimeFirstCellSourceAllTime.ellSource ζ N := by
        unfold APrimeFirstCellSourceAllTime.ellSource
        positivity
      have hell0 : 0 ≤ B.ell N r := by
        exact zero_le_one.trans (one_le_ellHat
          (d.L N) (d.three_le_L N) hr0 hr1)
      have hratio : 0 ≤ B.ell N r /
          APrimeFirstCellSourceAllTime.ellSource ζ N :=
        div_nonneg hell0 hellS.le
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hηr.le)) hc)
        (pow_nonneg hratio _)
    exact add_nonneg hmain (by positivity)
  have hAf : 0 ≤ Af := by
    dsimp [Af, S]
    have hc := Lemma57.cFar2_nonneg
      (show 1 ≤ (d.W N : ℝ) by exact_mod_cast B.one_le_W N)
      (show 0 < B.ell N r by
        exact lt_of_lt_of_le zero_lt_one
          (one_le_ellHat (d.L N) (d.three_le_L N) hr0 hr1))
    have hS0 : 0 ≤ APrimeFirstCellSourceAllTime.sourceC4 ζ N r := by
      unfold APrimeFirstCellSourceAllTime.sourceC4
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _)
          (pow_nonneg (by
            exact zero_le_one.trans (one_le_ellHat
              (d.L N) (d.three_le_L N) hr0 hr1)) _))
        (pow_nonneg (inv_nonneg.mpr (B.scale_pos' (by norm_num) N hr0 hr1).le) _)
    have hW0 : 0 ≤ (B.W N : ℝ) := by positivity
    have hL0 : 0 ≤ (B.L N : ℝ) := by positivity
    have hell0 : 0 ≤ B.ell N r := by
      exact zero_le_one.trans (one_le_ellHat
        (d.L N) (d.three_le_L N) hr0 hr1)
    have hA0 : 0 ≤ (B.W N : ℝ) * B.ell N r * etaT 0 r :=
      mul_nonneg (mul_nonneg hW0 hell0) hηr.le
    unfold APrimeQVEndpoint.diagFarRate
    have hfirst : 0 ≤ Lemma57.cFar2 (↑(B.W N)) (B.ell N r) *
        ((2 * 2) ^ 2 *
          (↑(B.W N) * B.ell N r * etaT 0 r *
            (2 * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r)))) := by
      exact mul_nonneg hc
        (mul_nonneg (sq_nonneg (2 * 2))
          (mul_nonneg hA0
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))))
    have hsecond : 0 ≤ 72 * (2 * 2) ^ 3 *
        (↑(B.W N) * B.ell N r * etaT 0 r)⁻¹ := by
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr hA0)
    have hmain : 0 ≤ 2 * (etaT 0 r)⁻¹ *
        (Lemma57.cFar2 (↑(B.W N)) (B.ell N r) *
            ((2 * 2) ^ 2 *
              (↑(B.W N) * B.ell N r * etaT 0 r *
                (2 * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r)))) +
          72 * (2 * 2) ^ 3 *
            (↑(B.W N) * B.ell N r * etaT 0 r)⁻¹) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hηr.le))
        (add_nonneg hfirst hsecond)
    have hspace : 0 ≤ 4 * (B.W N : ℝ) * (B.L N : ℝ) *
        (B.W N : ℝ) ^ (-(60 : ℝ)) * (2 * 2) ^ 3 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hW0) hL0)
          (Real.rpow_nonneg hW0 _))
        (by norm_num)
    exact add_nonneg hmain hspace
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos (by exact_mod_cast d.W_pos N) _
  have hXi0 : 0 ≤ Xi := by dsimp [Xi]; exact Step2.xiK_nonneg _ _ _
  have hleak0 : 0 ≤ leak := by dsimp [leak]; positivity
  have hχ0 : 0 ≤ χ := by simp only [χ]; split <;> norm_num
  have hχ1 : χ ≤ 1 := by simp only [χ]; split <;> norm_num
  have hBW : B.W N = d.W N := rfl
  have hBL : B.L N = d.L N := rfl
  have hnorm := normalized_three_term_sq_le hAn hAf hK hT hXi0 hleak0
    hχ0 hχ1 (zero_lt_one.trans_le hR) hcoeff
    (by simpa only [Xi, X, hBW, hBL] using hXi)
    (by simpa only [leak, X, hBW] using hEndpointLeak)
  have hroot : APrimeFullQV.rootProfile B 0 N r v 60 ellS 2 S
      ((d.W N : ℝ)⁻¹) a =
      √An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T) := by
    dsimp only [APrimeFullQV.rootProfile, An, Af, K, T, Xi, leak, χ, ellS, S]
    ring_nf
    ac_rfl
  have hscale : APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v =
      T * R ^ 4 := by
    dsimp [APrimeDriftTimeFamily.driftScale, T, R,
      APrimeFirstCellLoopCap.xRate]
  have hraw : APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      ((T * R ^ 4)⁻¹ *
        (√An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T))) ^ 2 := by
    unfold APrimeFirstCellQVFixedTwo.fixedTwoMovingProfileAt at hfixed
    rw [hscale, hroot] at hfixed
    exact hfixed
  have hζle : ζ ≤ ν / 128 := by
    calc
      ζ ≤ (ν / 2) / 64 := by
        dsimp [ζ, APrimeFirstCellEGAllOutputRunning.sourceLoss,
          APrimeFirstCellEGFarSmallRunning.sourceLoss]
        exact min_le_left _ _
      _ = ν / 128 := by ring
  have hpow : X * (N : ℝ) ^ ζ * X ^ 2 ≤ (N : ℝ) ^ ν := by
    have hN0 : 0 < (N : ℝ) := zero_lt_one.trans_le hN
    have hexp : ν / 8 + ζ + ν / 4 ≤ ν := by linarith
    calc
      _ = (N : ℝ) ^ (ν / 8 + ζ + ν / 4) := by
        dsimp [X]
        rw [show ((N : ℝ) ^ (ν / 8)) ^ 2 = (N : ℝ) ^ (ν / 4) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          ring_nf]
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      _ ≤ (N : ℝ) ^ ν := Real.rpow_le_rpow_of_exponent_le hN hexp
  have hKrepr : K = (R / x) ^ 2 := by
    dsimp [K, R, x]
    rw [time_ratio_eq_xRate_div hr1 hv1]
  have hkernel : K ^ 2 * R ^ (-(8 : ℝ)) =
      R ^ (-(4 : ℝ)) * x ^ (-(4 : ℝ)) := by
    rw [hKrepr]
    exact endpoint_kernel_power (zero_lt_one.trans_le hR) (zero_lt_one.trans_le hx)
  have hrows : x ^ (-(4 : ℝ)) * preRows δ (δ / 16) N v r =
      x ^ (-(3 / 2 : ℝ)) +
        (N : ℝ) ^ (4 * δ + 2 * (δ / 16)) * Av ^ (-(1 / 2 : ℝ)) *
          x ^ (19 / 4 : ℝ) +
        (N : ℝ) ^ (6 * δ + 3 * (δ / 16)) * Av⁻¹ * x ^ (8 : ℝ) := by
    dsimp [preRows, Av]
    exact x_neg_four_mul_preRows (zero_lt_one.trans_le hx)
  calc
    _ ≤ ((T * R ^ 4)⁻¹ *
        (√An * (K * Xi * T * χ + leak * K * T) + √Af * (K * Xi * T))) ^ 2 := hraw
    _ ≤ 9 * M * X ^ 2 * K ^ 2 * R ^ (-(8 : ℝ)) := hnorm
    _ = currentConstant * (X * (N : ℝ) ^ ζ * X ^ 2) *
        (etaT 0 r)⁻¹ * R ^ (-(4 : ℝ)) *
          (x ^ (-(4 : ℝ)) * preRows δ (δ / 16) N v r) := by
      calc
        _ = 9 * M * X ^ 2 * (K ^ 2 * R ^ (-(8 : ℝ))) := by ring
        _ = 9 * M * X ^ 2 *
            (R ^ (-(4 : ℝ)) * x ^ (-(4 : ℝ))) := by rw [hkernel]
        _ = _ := by dsimp [M, currentConstant]; ring
    _ ≤ currentConstant * (N : ℝ) ^ ν *
        (etaT 0 r)⁻¹ * R ^ (-(4 : ℝ)) *
          (x ^ (-(4 : ℝ)) * preRows δ (δ / 16) N v r) := by
      have hpre0 : 0 ≤ preRows δ (δ / 16) N v r := by
        unfold preRows
        have hAv : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
          B.scale_pos' (by norm_num) N hv0 hv1
        positivity
      have hfac0 : 0 ≤ (etaT 0 r)⁻¹ * R ^ (-(4 : ℝ)) *
          (x ^ (-(4 : ℝ)) * preRows δ (δ / 16) N v r) := by
        exact mul_nonneg
          (mul_nonneg (inv_nonneg.mpr hηr.le)
            (Real.rpow_nonneg (zero_le_one.trans hR) _))
          (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) hpre0)
      have hh := mul_le_mul_of_nonneg_left hpow currentConstant_pos.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hfac0
    _ = currentRate δ (δ / 16) ν N v r := by
      rw [hrows]
      rfl

/-- All deterministic absorption premises for the current rows hold
uniformly on the first half-cell.  This is independent of the event and so
can be reused for the running family and for its positive resident. -/
theorem eventually_fixedTwoMovingProfileAt_le_currentRate
    {δ ν : ℝ} (hδ : 0 ≤ δ) (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 0 < v → v ≤ 1 / 2 →
      ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ ω : Ω d,
        ∀ a : LoopArg (d.L N) 2,
          APrimeFirstCellQVFixedTwo.fixedTwoMovingProfileAt ν N ω v r a →
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
            currentRate δ (δ / 16) ν N v r := by
  have hcoeff := APrimeFirstCellQVRunningSmall.eventually_coefficients_uniform
    (by positivity : 0 < ν / 8)
  have hscale := APrimeFirstCellQVRunningProfile.eventually_running_scales
  have hxi := Step2FarInputs.eventually_xiK_le B (mE 0).im
    (by positivity : 0 < ν / 8)
  have hconst := eventually_le_rpow (256 * Real.exp 3)
    (by positivity : 0 < ν / 8)
  filter_upwards [hcoeff, hscale, hxi, hconst] with
    N hcoeff hscale hxi hconst
  intro v hvpos hvhalf r hr ω a hfixed
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans hvhalf⟩
  obtain ⟨hNear, hFar⟩ := hcoeff r hrhalf
  obtain ⟨hWexp, _hlog4, _hlogD, hN, _hηN, _hA1, hAN,
    hWL, hNW⟩ := hscale r hrhalf
  have hr1 : r < 1 := hr.2.trans_lt hv1
  have hW1 : 1 ≤ (d.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hWexp
  have hAr : 0 < B.scale 0 N r :=
    B.scale_pos' (by norm_num) N hr.1 hr1
  have hη : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hη1 : etaT 0 r ≤ 1 := etaT_le_one (by norm_num) hr.1
  have hAN' : B.scale 0 N r ≤ (N : ℝ) := by
    change (d.W N : ℝ) * B.ell N r * etaT 0 r ≤ (N : ℝ)
    exact hAN
  have hLeak : (d.W N : ℝ) * (d.L N : ℝ) *
      (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
        (etaT 0 r)⁻¹ * (B.scale 0 N r)⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hN hAr hη
      hWL hAN' hNW hη1 (by norm_num)
  let ζ := APrimeFirstCellEGAllOutputRunning.sourceLoss ν
  have hζ : 0 < ζ := APrimeFirstCellEGAllOutputRunning.sourceLoss_pos hν
  have hellS : 0 < APrimeFirstCellSourceAllTime.ellSource ζ N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN hζ.le
  have hbase : 1 ≤ 2 * (N : ℝ) ^ ζ := by nlinarith
  have hellS1 : APrimeFirstCellSourceAllTime.ellSource ζ N ≤ 1 := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
  have hell1 : 1 ≤ B.ell N r :=
    one_le_ellHat (d.L N) (d.three_le_L N) hr.1 hr1
  have hratio : 1 ≤ B.ell N r /
      APrimeFirstCellSourceAllTime.ellSource ζ N := by
    apply (le_div_iff₀ hellS).2
    nlinarith
  have hFloor : (d.W N : ℝ)⁻¹ ≤ (etaT 0 r)⁻¹ *
      (B.ell N r / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) :=
    APrimeFullQV.ExponentRows.floor_paid hW1 hη hη1 hratio
  have hWneg : (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  have hEndpointLeak : 256 * Real.exp 3 *
      (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ (N : ℝ) ^ (ν / 8) := by
    calc
      _ ≤ 256 * Real.exp 3 * 1 := by gcongr
      _ ≤ (N : ℝ) ^ (ν / 8) := by simpa using hconst
  exact fixedTwoMovingProfileAt_le_currentRate hδ hν hr.1 hr.2 hv1 hN
    hNear hFar hLeak (by simpa only [ζ] using hFloor)
    (by simpa using hxi) hEndpointLeak hfixed

/-- The literal T437 event, with the fixed block value two, now carries the
three current rows at every active moving endpoint and every preceding time. -/
def currentRowsBound (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
        (∀ q ∈ Set.Icc (0 : ℝ) (1 / 2),
          APrimeSupportRunning.jG N q ω ≤ 2) ∧
        ∀ r ∈ Set.Icc (0 : ℝ) v,
          1 ≤ APrimeSupportRunning.jG N r ω ∧
          APrimeSupportRunning.jG N r ω ≤ 2 ∧
            ∀ a : LoopArg (d.L N) 2,
              APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
                currentRate δ (δ / 16) ν N v r

theorem eventually_currentRowsBound {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) (hν : 0 < ν) :
    currentRowsBound τ' δ ν := by
  filter_upwards [
    APrimeFirstCellQVFixedTwo.eventually_fixedTwo_running_moving_profile hτ',
    eventually_fixedTwoMovingProfileAt_le_currentRate hδ hν] with
    N hrun hconvert
  intro ω hω N0 p k m hN0 hp hm hk1 hk hw
  obtain ⟨hvpos, hvle, hvhalf, hJall, hprof⟩ :=
    hrun ω hω N0 p k m hN0 hp hm hk1 hk hw
  refine ⟨hvpos, hvle, hvhalf, hJall, ?_⟩
  intro r hr
  obtain ⟨hJ1, hJ2, hfixed⟩ := hprof r hr
  exact ⟨hJ1, hJ2, fun a =>
    hconvert _ hvpos hvhalf r hr ω a (hfixed a)⟩

/-- A positive `k = 2` resident of the same sharp event carrying all current
rows, including the two closed-interval endpoints. -/
def positiveCurrentRowsPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    APrimeFullQV.SourceEvent (sample d) 0 N v ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N v) ∧
    (∀ q ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N q ω ≤ 2) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) v,
      1 ≤ APrimeSupportRunning.jG N r ω ∧
      APrimeSupportRunning.jG N r ω ≤ 2 ∧
        ∀ a : LoopArg (d.L N) 2,
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
            currentRate δ (δ / 16) ν N v r) ∧
    (∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v 0 ω ≤
        currentRate δ (δ / 16) ν N v 0) ∧
    ∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v v ω ≤
        currentRate δ (δ / 16) ν N v v

theorem positiveCurrentRowsPlateau_of_fixed {τ' δ ν : ℝ}
    (hδ : 0 ≤ δ) (hν : 0 < ν)
    (hpositive :
      APrimeFirstCellQVFixedTwo.positiveFixedTwoMovingProfilePlateau τ' δ ν) :
    positiveCurrentRowsPlateau τ' δ ν := by
  filter_upwards [hpositive,
    eventually_fixedTwoMovingProfileAt_le_currentRate hδ hν] with
    N hpositive hconvert
  dsimp only [APrimeFirstCellQVFixedTwo.positiveFixedTwoMovingProfilePlateau]
    at hpositive
  obtain ⟨ω, hω, hvpos, hvle, hvhalf, hw, hsource, hJall, hprof,
    _hJ01, _hJ02, _hJv1, _hJv2, hzero, hend⟩ := hpositive
  refine ⟨ω, hω, hvpos, hvle, hvhalf, hw, hsource, hJall, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨hJ1, hJ2, hfixed⟩ := hprof r hr
    exact ⟨hJ1, hJ2, fun a =>
      hconvert _ hvpos hvhalf r hr ω a (hfixed a)⟩
  · intro a
    exact hconvert _ hvpos hvhalf 0 ⟨le_rfl, hvpos.le⟩ ω a (hzero a)
  · intro a
    exact hconvert _ hvpos hvhalf _ ⟨hvpos.le, le_rfl⟩ ω a (hend a)

/-- Closed same-event producer, with T437's parameter order and positive
resident unchanged. -/
theorem exists_currentRowsBound_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        currentRowsBound τ' δ ν ∧
        positiveCurrentRowsPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQVFixedTwo.exists_fixedTwo_running_moving_profile_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hfixed, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_currentRowsBound hτ' hδ.le hν,
    positiveCurrentRowsPlateau_of_fixed hδ.le hν hpositive⟩

/-- The exact positive Cond272Reg margins audited in T427 for the two far
current rows. -/
theorem current_far_exponent_margins {c δ τ ν : ℝ}
    (hc : 0 < c) (hδ : δ = c / 1000) (hτ : τ = δ / 16)
    (hν : 0 < ν) (hνsmall : ν ≤ δ / 100) :
    (4 * δ + 2 * τ + ν) / c + (19 / 4 : ℝ) / 30 < 1 / 2 ∧
    (6 * δ + 3 * τ + ν) / c + (8 : ℝ) / 30 < 1 :=
  APrimeQVIntegralBudget.far_exponent_margins hc hδ hτ hν hνsmall

end RBM.APrimeFirstCellQVCurrentRows

#print axioms RBM.APrimeFirstCellQVCurrentRows.normalized_three_term_sq_le
#print axioms RBM.APrimeFirstCellQVCurrentRows.endpoint_kernel_power
#print axioms RBM.APrimeFirstCellQVCurrentRows.fixedTwoMovingProfileAt_le_currentRate
#print axioms RBM.APrimeFirstCellQVCurrentRows.eventually_fixedTwoMovingProfileAt_le_currentRate
#print axioms RBM.APrimeFirstCellQVCurrentRows.eventually_currentRowsBound
#print axioms RBM.APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau_of_fixed
#print axioms RBM.APrimeFirstCellQVCurrentRows.exists_currentRowsBound_with_plateau
#print axioms RBM.APrimeFirstCellQVCurrentRows.current_far_exponent_margins
