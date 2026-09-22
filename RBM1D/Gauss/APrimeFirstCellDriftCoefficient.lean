/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellLoopCap

/-!
# T433: actual same-event drift coefficient absorption

The T422 coefficient is absorbed at the actual moving endpoint using T430's
running loop cap and retained spatial-floor estimate.
-/

namespace RBM.APrimeFirstCellDriftCoefficient
open Filter MeasureTheory Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def coefficientConstant : ℝ :=
  1 + 37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2

theorem coefficientConstant_pos : 0 < coefficientConstant := by
  unfold coefficientConstant
  positivity

/-- The exact scalar coefficient left by T422 before transport. -/
noncomputable def rawCoefficient (α : ℝ) (N : ℕ) (r : ℝ) (ω : Ω d) : ℝ :=
  (N : ℝ) ^ α * (etaT 0 r)⁻¹ * (B.ell N r / B.ell N 0) ^ 3 +
    Real.exp 1 * (Step2.jS (sample d) 0 60 N r ω) ^ 2 *
      (36 * ((etaT 0 r)⁻¹ * (B.scale 0 N r)⁻¹) +
        APrimeFirstCellLoopCap.spatialFloor N)

/-- The target coefficient in (5.42), at the actual moving endpoint. -/
noncomputable def endpointCoefficient (δ ν : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  coefficientConstant * (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
    APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) *
      (APrimeFirstCellLoopCap.xRate r ^ (-(1 : ℝ) / 2) +
        (N : ℝ) ^ (4 * δ) *
          (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
            APrimeFirstCellLoopCap.xRate r ^ 6)

noncomputable def scaledRawCoefficient (ν : ℝ) (N : ℕ)
    (v r : ℝ) (ω : Ω d) : ℝ :=
  Step2.xiK (d.L N) (d.W N) 1 *
    APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) *
    APrimeFirstCellLoopCap.xRate r ^ (-(2 : ℝ)) *
    rawCoefficient (ν / 2) N r ω

def coefficientInequality (δ ν : ℝ) (N : ℕ)
    (v r : ℝ) (ω : Ω d) : Prop :=
  scaledRawCoefficient ν N v r ω ≤ endpointCoefficient δ ν N v r

lemma coefficient_absorption {N ν δ η x R ellRatio Xi J Ar Av floor : ℝ}
    (hN : 1 ≤ N) (hν : 0 < ν) (hη : 0 < η) (hx : 1 ≤ x)
    (hR : 0 ≤ R)
    (hell0 : 0 ≤ ellRatio) (hell : ellRatio ≤ Real.sqrt x)
    (hXi : Xi ≤ N ^ (ν / 2))
    (hJ0 : 0 ≤ J)
    (hJ : J ≤ APrimeFirstCellLoopCap.loopConstant * N ^ (2 * δ) * x ^ 4)
    (hAr0 : 0 < Ar) (hAv0 : 0 < Av) (hAvAr : Av ≤ Ar)
    (hfloor0 : 0 ≤ floor) (hfloor : floor ≤ η⁻¹ * Av⁻¹) :
    Xi * R ^ (-(2 : ℝ)) * x ^ (-(2 : ℝ)) *
        (N ^ (ν / 2) * η⁻¹ * ellRatio ^ 3 +
          Real.exp 1 * J ^ 2 * (36 * (η⁻¹ * Ar⁻¹) + floor)) ≤
      coefficientConstant * N ^ ν * η⁻¹ * R ^ (-(2 : ℝ)) *
        (x ^ (-(1 : ℝ) / 2) + N ^ (4 * δ) * Av⁻¹ * x ^ 6) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hC0 : 0 ≤ APrimeFirstCellLoopCap.loopConstant := by
    unfold APrimeFirstCellLoopCap.loopConstant
    positivity
  have hell3 : ellRatio ^ 3 ≤ (Real.sqrt x) ^ 3 :=
    pow_le_pow_left₀ hell0 hell 3
  have hsqrt3 : (Real.sqrt x) ^ 3 = x ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hx32 : x ^ ((3 : ℝ) / 2) * x ^ (-(2 : ℝ)) =
      x ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hNsplit : N ^ (ν / 2) * N ^ (ν / 2) = N ^ ν := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hElead : Xi * x ^ (-(2 : ℝ)) *
        (N ^ (ν / 2) * η⁻¹ * ellRatio ^ 3) ≤
      N ^ ν * η⁻¹ * x ^ (-(1 : ℝ) / 2) := by
    calc
      _ ≤ N ^ (ν / 2) * x ^ (-(2 : ℝ)) *
          (N ^ (ν / 2) * η⁻¹ * (Real.sqrt x) ^ 3) := by gcongr
      _ = N ^ ν * η⁻¹ * x ^ (-(1 : ℝ) / 2) := by
        rw [hsqrt3]
        rw [← hNsplit, ← hx32]
        ring
  have hArInv : Ar⁻¹ ≤ Av⁻¹ := inv_anti₀ hAv0 hAvAr
  have hbracket : 36 * (η⁻¹ * Ar⁻¹) + floor ≤
      37 * (η⁻¹ * Av⁻¹) := by
    have hηi : 0 < η⁻¹ := inv_pos.mpr hη
    have hmain : η⁻¹ * Ar⁻¹ ≤ η⁻¹ * Av⁻¹ :=
      mul_le_mul_of_nonneg_left hArInv hηi.le
    linarith
  have hJsq : J ^ 2 ≤
      APrimeFirstCellLoopCap.loopConstant ^ 2 * N ^ (4 * δ) * x ^ 8 := by
    have hs := pow_le_pow_left₀ hJ0 hJ 2
    have hN4 : (N ^ (2 * δ)) ^ (2 : ℕ) = N ^ (4 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      ring
    calc
      J ^ 2 ≤ (APrimeFirstCellLoopCap.loopConstant * N ^ (2 * δ) * x ^ 4) ^ 2 := hs
      _ = APrimeFirstCellLoopCap.loopConstant ^ 2 *
          (N ^ (2 * δ)) ^ (2 : ℕ) * (x ^ 4) ^ (2 : ℕ) := by ring
      _ = APrimeFirstCellLoopCap.loopConstant ^ 2 * N ^ (4 * δ) * x ^ 8 := by
        rw [hN4]
        ring
  have hNhalf : N ^ (ν / 2) ≤ N ^ ν :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hQuad : Xi * x ^ (-(2 : ℝ)) *
        (Real.exp 1 * J ^ 2 * (36 * (η⁻¹ * Ar⁻¹) + floor)) ≤
      (37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2) *
        N ^ ν * η⁻¹ * (N ^ (4 * δ) * Av⁻¹ * x ^ 6) := by
    calc
      _ ≤ N ^ (ν / 2) * x ^ (-(2 : ℝ)) *
          (Real.exp 1 *
            (APrimeFirstCellLoopCap.loopConstant ^ 2 * N ^ (4 * δ) * x ^ 8) *
            (37 * (η⁻¹ * Av⁻¹))) := by gcongr
      _ ≤ N ^ ν * x ^ (-(2 : ℝ)) *
          (Real.exp 1 *
            (APrimeFirstCellLoopCap.loopConstant ^ 2 * N ^ (4 * δ) * x ^ 8) *
            (37 * (η⁻¹ * Av⁻¹))) := by gcongr
      _ = (37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2) *
          N ^ ν * η⁻¹ * (N ^ (4 * δ) * Av⁻¹ * x ^ 6) := by
        have hx86 : x ^ 8 * x ^ (-(2 : ℝ)) = x ^ 6 := by
          rw [show x ^ 8 = x ^ (8 : ℝ) by norm_cast,
            show x ^ 6 = x ^ (6 : ℝ) by norm_cast,
            ← Real.rpow_add hx0]
          norm_num
        calc
          _ = (37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2) *
              N ^ ν * η⁻¹ * (N ^ (4 * δ) * Av⁻¹ *
                (x ^ 8 * x ^ (-(2 : ℝ)))) := by ring
          _ = _ := by rw [hx86]
  have hR0 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hR _
  have hsum : Xi * x ^ (-(2 : ℝ)) *
        (N ^ (ν / 2) * η⁻¹ * ellRatio ^ 3 +
          Real.exp 1 * J ^ 2 * (36 * (η⁻¹ * Ar⁻¹) + floor)) ≤
      N ^ ν * η⁻¹ * x ^ (-(1 : ℝ) / 2) +
        (37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2) *
          N ^ ν * η⁻¹ * (N ^ (4 * δ) * Av⁻¹ * x ^ 6) := by
    rw [mul_add]
    exact add_le_add hElead hQuad
  have hC1 : 1 ≤ coefficientConstant := by
    unfold coefficientConstant
    have : 0 ≤ 37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2 := by positivity
    linarith
  have hCq : 37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2 ≤
      coefficientConstant := by
    unfold coefficientConstant
    linarith
  calc
    _ = R ^ (-(2 : ℝ)) * (Xi * x ^ (-(2 : ℝ)) *
        (N ^ (ν / 2) * η⁻¹ * ellRatio ^ 3 +
          Real.exp 1 * J ^ 2 * (36 * (η⁻¹ * Ar⁻¹) + floor))) := by ring
    _ ≤ R ^ (-(2 : ℝ)) *
        (N ^ ν * η⁻¹ * x ^ (-(1 : ℝ) / 2) +
          (37 * Real.exp 1 * APrimeFirstCellLoopCap.loopConstant ^ 2) *
            N ^ ν * η⁻¹ * (N ^ (4 * δ) * Av⁻¹ * x ^ 6)) :=
      mul_le_mul_of_nonneg_left hsum hR0
    _ ≤ R ^ (-(2 : ℝ)) *
        (coefficientConstant * N ^ ν * η⁻¹ * x ^ (-(1 : ℝ) / 2) +
          coefficientConstant * N ^ ν * η⁻¹ *
            (N ^ (4 * δ) * Av⁻¹ * x ^ 6)) := by
      have hNν0 : 0 ≤ N ^ ν := Real.rpow_nonneg (by linarith : 0 ≤ N) _
      have hηi0 : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
      have hxneg0 : 0 ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
      have hrow0 : 0 ≤ N ^ (4 * δ) * Av⁻¹ * x ^ 6 := by positivity
      gcongr
      · nlinarith [hC1, hNν0]
    _ = _ := by ring

def coefficientBound (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Set.Icc (0 : ℝ) v,
        coefficientInequality δ ν N v r ω

/-- Actual same-event scalar absorption at every real running time and the
actual moving endpoint. -/
theorem eventually_coefficient_bound {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hν : 0 < ν) :
    coefficientBound τ' δ ν := by
  filter_upwards [
    APrimeFirstCellLoopCap.eventually_running_loop_cap
      (hτ' := hτ') (hδ := hδ) (ν := ν / 2),
    APrimeFirstCellLoopCap.eventually_spatialFloor_le hτ',
    Step2FarInputs.eventually_xiK_le B 1 (by linarith : 0 < ν / 2),
    eventually_ge_atTop 1] with N hloop hfloor hXi hN
  intro ω hω N0 p k m hN0 hp hm hk hkT hw
  dsimp only
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hvTop : v ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc hwin
      (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hkT)
  have hvhalf : v ≤ 1 / 2 :=
    hvTop.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  intro r hr
  have hr1 : r < 1 := hr.2.trans_lt hv1
  have hη : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hx : 1 ≤ APrimeFirstCellLoopCap.xRate r := by
    simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hr.1 hr1)
  have hR : 0 ≤ APrimeFirstCellLoopCap.xRate v := by
    have hRv : 1 ≤ APrimeFirstCellLoopCap.xRate v := by
      simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
        (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
          (N := N) (by norm_num) hvTop.1 hv1)
    exact zero_le_one.trans hRv
  have hEll0 : B.ell N 0 = 1 :=
    ellHat_zero (B.L N) (B.three_le_L N)
  have hEllPos : 0 ≤ B.ell N r / B.ell N 0 := by
    rw [hEll0, div_one]
    exact (Step3.ellHat_pos_of_lt_one
      (show 1 ≤ B.L N by have := B.three_le_L N; omega) hr1).le
  have hEll : B.ell N r / B.ell N 0 ≤
      Real.sqrt (APrimeFirstCellLoopCap.xRate r) := by
    have hh := Step3.ellHat_le_sqrt_mul
      (L := B.L N) (s := 0) (t := r) hr.1 hr1
    rw [hEll0, div_one]
    have hz : ellHat (B.L N) ((0 : ℝ) : ℂ) = 1 :=
      ellHat_zero (B.L N) (B.three_le_L N)
    rw [hz, mul_one] at hh
    change ellHat (B.L N) (r : ℂ) ≤ _
    simpa only [APrimeFirstCellLoopCap.xRate, etaT, mE_zero,
      Complex.I_im, mul_one, sub_zero, one_mul] using hh
  have hJ0 : 0 ≤ Step2.jS (sample d) 0 60 N r ω := by
    exact (Step2Moment.one_le_jS (sample d) (E := 0) (D := 60) N r ω).trans' zero_le_one
  have hJ := hloop ω hω N0 p k m hN0 hp hm hk hkT hw r hr
  have hAr0 : 0 < B.scale 0 N r :=
    B.scale_pos' (by norm_num) N hr.1 hr1
  have hAv0 : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
    B.scale_pos' (by norm_num) N hvTop.1 hv1
  have hAvAr : APrimeFirstCellLoopCap.endpointScale N v ≤ B.scale 0 N r := by
    rw [APrimeFirstCellLoopCap.endpointScale, B.scale_eq_flowScale,
      B.scale_eq_flowScale]
    exact flowScale_antitoneOn (show (0 : ℝ) ≤ B.W N by positivity)
      (B.L N) 0 (Set.mem_Iic.2 hr1.le) (Set.mem_Iic.2 hv1.le) hr.2
  have hfloor' := hfloor r v hr hvTop.2
  have hfloor0 : 0 ≤ APrimeFirstCellLoopCap.spatialFloor N := by
    unfold APrimeFirstCellLoopCap.spatialFloor
    positivity
  unfold coefficientInequality scaledRawCoefficient rawCoefficient endpointCoefficient
  exact coefficient_absorption (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    hν hη hx hR hEllPos hEll hXi hJ0 hJ hAr0 hAv0 hAvAr
    hfloor0 hfloor'

/-- The closed running interval contains both `r=0` and `r=v`. -/
theorem coefficient_bound_endpoints_of_bound {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (h : coefficientBound τ' δ ν) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight δ (firstCellT τ')
          N0 p N k m ω →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        coefficientInequality δ ν N v 0 ω ∧
          coefficientInequality δ ν N v v ω := by
  filter_upwards [h] with N hN
  intro ω hω N0 p k m hN0 hp hm hk hkT hw
  dsimp only
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hv : 0 ≤ v :=
    (MomentDuhamelCut.netFinset_subset_Icc
      (APrimeSupportRunning.firstT_bounds hτ' N).1
      (APrimeSupportRunning.mesh_pos N) v
      (cutNetPt_mem_netFinset hkT)).1
  exact ⟨hN ω hω N0 p k m hN0 hp hm hk hkT hw 0 ⟨le_rfl, hv⟩,
    hN ω hω N0 p k m hN0 hp hm hk hkT hw v ⟨hv, le_rfl⟩⟩

def positiveCoefficientPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧ u2 ≤ firstCellT τ' N ∧
      ∀ r ∈ Set.Icc (0 : ℝ) u2,
        coefficientInequality δ ν N u2 r ω

/-- T422's positive `k=2` resident and the coefficient absorption use one
literal sample and one event. -/
theorem positiveCoefficientPlateau_of_raw {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hν : 0 < ν)
    (hraw : APrimeFirstCellDriftRaw.positiveRawDriftPlateau
      τ' δ (ν / 2)) :
    positiveCoefficientPlateau τ' δ ν := by
  filter_upwards [hraw, eventually_coefficient_bound hτ' hδ hν,
    eventually_ge_atTop 2] with N hraw hcoeff hN
  dsimp only [APrimeFirstCellDriftRaw.positiveRawDriftPlateau] at hraw
  obtain ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, _⟩ := hraw
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  refine ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, ?_⟩
  intro r hr
  exact hcoeff ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hwδ 1]; norm_num) r hr

/-- One literal high-probability event supplies the moving-endpoint
coefficient bound and a nondegenerate same-event resident. -/
theorem exists_good_with_coefficient_bound :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N)) ∧
        HighProb (P d)
          (APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2)) ∧
        coefficientBound τ' δ ν ∧
        positiveCoefficientPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hgood⟩ :=
    APrimeFirstCellDriftRaw.exists_good_with_raw_drift
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hraw, hplat⟩ :=
    hgood δ hδ hδ100 (ν / 2) (by linarith)
  exact ⟨hmeas, hp, eventually_coefficient_bound hτ' hδ hν,
    positiveCoefficientPlateau_of_raw hτ' hδ hν hplat⟩

#print axioms coefficient_absorption
#print axioms eventually_coefficient_bound
#print axioms coefficient_bound_endpoints_of_bound
#print axioms positiveCoefficientPlateau_of_raw
#print axioms exists_good_with_coefficient_bound

end RBM.APrimeFirstCellDriftCoefficient
