/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGFarRunning
import RBM1D.Gauss.APrimeFirstCellEGNearRunning
import RBM1D.Gauss.APrimeFirstCellQVSmall

/-!
# Active-support running far `eGpm` with an arbitrary positive power loss

The three literal rows from T410 are absorbed separately.  In particular,
the `D = 60` spatial floor is retained and no `A⁻¹/³` coarsening is used.
-/

namespace RBM.APrimeFirstCellEGFarSmallRunning

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- Source loss chosen after the requested final exponent. -/
noncomputable def sourceLoss (ν : ℝ) : ℝ := min (ν / 64) (1 / 64)

/-- Subpolynomial loss reserved for the running `cFar` coefficient. -/
noncomputable def subpolyLoss (ν : ℝ) : ℝ := min (ν / 64) (1 / 64)

/-- T410's same-parameter event at the two strict losses selected above. -/
def good (τ' ν : ℝ) (N : ℕ) : Set (Ω d) :=
  APrimeFirstCellEGFarRunning.good τ' (sourceLoss ν) (sourceLoss ν) N

theorem measurableSet_good {τ' : ℝ} (hτ' : 0 < τ')
    (ν : ℝ) (N : ℕ) : MeasurableSet (good τ' ν N) :=
  APrimeFirstCellEGFarRunning.measurableSet_good hτ'
    (sourceLoss ν) (sourceLoss ν) N

theorem highProb_good_of_inputs {τ' ν : ℝ} (hτ' : 0 < τ') (hν : 0 < ν)
    (h1 : Step1.Hyp (sample d) 0 (firstCellS τ') (firstCellT τ'))
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi)
    (h4 : firstCellRawLoopDom τ' 4) (h6 : firstCellRawLoopDom τ' 6) :
    HighProb (P d) (good τ' ν) := by
  have hζ : 0 < sourceLoss ν := lt_min (by positivity) (by norm_num)
  exact APrimeFirstCellEGFarRunning.highProb_good_of_inputs
    hτ' h1 hll h4 h6 hζ hζ

/-- `cFar` is subpolynomial uniformly over the complete first half-cell. -/
theorem eventually_cFar_le_running {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ r ∈ Set.Icc (0 : ℝ) (1 / 2),
      Lemma57.cFar (d.W N : ℝ) (B.ell N r) ≤ (N : ℝ) ^ θ := by
  filter_upwards [Step2FarInputs.eventually_cFar_one_le B hθ] with N hc r hr
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hℓ : 1 ≤ B.ell N r :=
    one_le_ellHat_of_nonneg (by
      change 1 ≤ d.L N
      exact (show 1 ≤ d.L N by have := d.three_le_L N; omega))
      hr.1 (hr.2.trans_lt (by norm_num))
  exact (Step2FarInputs.cFar_le_cFar_one hW hℓ).trans hc

/-- The literal T410 rows before the final constant absorption.  Their powers
are respectively `ζ + θ - 1/8`, `ζ - 7/16`, and `ζ - 281/16`. -/
theorem far_rows_le_powers (N : ℕ) (r ζ θ J : ℝ)
    (hN : 1 ≤ (N : ℝ))
    (hr : r ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hWgrow : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ))
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ))
    (hcFar : Lemma57.cFar (d.W N : ℝ) (B.ell N r) ≤ (N : ℝ) ^ θ)
    (hJ0 : 0 ≤ J) (hJ : J ≤ (N : ℝ) ^ ((1 : ℝ) / 8)) :
    let ℓ := B.ell N r
    let η := etaT 0 r
    let A := (d.W N : ℝ) * ℓ * η
    let κ₁ := 2 * (N : ℝ) ^ ζ * ℓ
    let κ₂ := firstCellDelta N + (d.W N : ℝ)⁻¹
    κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂) ≤
        6 * (N : ℝ) ^ (ζ + θ - 1 / 8) ∧
      κ₁ * (168 * J * Real.sqrt J * A⁻¹) ≤
        1344 * (N : ℝ) ^ (ζ - 7 / 16) ∧
      κ₁ * (J * Real.sqrt J * (d.L N : ℝ) *
        Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) ≤
        4 * (N : ℝ) ^ (ζ - 281 / 16) := by
  let W : ℝ := d.W N
  let L : ℝ := d.L N
  let ℓ : ℝ := B.ell N r
  let η : ℝ := etaT 0 r
  let A : ℝ := W * ℓ * η
  let κ₁ : ℝ := 2 * (N : ℝ) ^ ζ * ℓ
  let κ₂ : ℝ := firstCellDelta N + W⁻¹
  have hNpos : (0 : ℝ) < N := by linarith
  have hWpos : 0 < W := by
    change (0 : ℝ) < (d.W N : ℝ)
    exact_mod_cast d.W_pos N
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact_mod_cast (show 1 ≤ d.W N by have := d.W_pos N; omega)
  have hℓ1 : 1 ≤ ℓ := by
    dsimp [ℓ]
    exact one_le_ellHat_of_nonneg (by
      change 1 ≤ d.L N
      exact (show 1 ≤ d.L N by have := d.three_le_L N; omega))
      hr.1 (hr.2.trans_lt (by norm_num))
  have hℓ2 : ℓ ≤ 2 := by
    dsimp [ℓ]
    exact APrimeFirstCellQVSmall.ell_firstHalf_le_two N hr.1 hr.2
  have hηhalf : (1 / 2 : ℝ) ≤ η := by
    dsimp [η]
    rw [show etaT 0 r = 1 - r by norm_num [etaT, mE_zero]]
    linarith [hr.2]
  have hWhalf : W ^ (-(1 / 2 : ℝ)) ≤
      (N : ℝ) ^ (-(5 / 16 : ℝ)) := by
    calc
      W ^ (-(1 / 2 : ℝ)) ≤
          ((N : ℝ) ^ ((5 : ℝ) / 8)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos hNpos _) hWgrow (by norm_num)
      _ = (N : ℝ) ^ (-(5 / 16 : ℝ)) := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have hWinv : W⁻¹ ≤ (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
    rw [← Real.rpow_neg_one W]
    calc
      W ^ (-(1 : ℝ)) ≤ ((N : ℝ) ^ ((5 : ℝ) / 8)) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos hNpos _) hWgrow (by norm_num)
      _ = (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have hdelta : firstCellDelta N ≤
      (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hWhalf' : (d.W N : ℝ) ^ (-(1 : ℝ) / 2) ≤
        (N : ℝ) ^ (-(5 / 16 : ℝ)) := by
      simpa only [W] using (show W ^ (-(1 : ℝ) / 2) ≤
        (N : ℝ) ^ (-(5 / 16 : ℝ)) by convert hWhalf using 1 <;> ring)
    unfold firstCellDelta firstCellPsi
    calc
      (N : ℝ) ^ ((1 : ℝ) / 16) *
          ((d.W N : ℝ) ^ (-(1 : ℝ) / 2) / 2) ≤
          (N : ℝ) ^ ((1 : ℝ) / 16) *
            ((N : ℝ) ^ (-(5 / 16 : ℝ)) / 2) := by
              exact mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hWhalf' (by norm_num)) (by positivity)
      _ = (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
        calc
          (N : ℝ) ^ ((1 : ℝ) / 16) *
              ((N : ℝ) ^ (-(5 / 16 : ℝ)) / 2) =
              (1 / 2 : ℝ) * ((N : ℝ) ^ ((1 : ℝ) / 16) *
                (N : ℝ) ^ (-(5 / 16 : ℝ))) := by ring
          _ = _ := by
            rw [← Real.rpow_add hNpos]
            congr 1 <;> ring
  have hWinv_le : (N : ℝ) ^ (-(5 / 8 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hκ₂ : κ₂ ≤ (3 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    dsimp [κ₂]
    calc
      firstCellDelta N + W⁻¹ ≤
          (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) +
            (N : ℝ) ^ (-(5 / 8 : ℝ)) := add_le_add hdelta hWinv
      _ ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) +
            (N : ℝ) ^ (-(1 / 4 : ℝ)) := add_le_add_right hWinv_le _
      _ = _ := by ring
  have hκ₂0 : 0 ≤ κ₂ := by
    dsimp [κ₂]
    unfold firstCellDelta firstCellPsi
    positivity
  have hκ₁ : κ₁ ≤ 4 * (N : ℝ) ^ ζ := by
    dsimp [κ₁]
    have hp : 0 ≤ (N : ℝ) ^ ζ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hℓ2 hp]
  have hκ₁0 : 0 ≤ κ₁ := by dsimp [κ₁]; positivity
  have hcFar0 : 0 ≤ Lemma57.cFar (d.W N : ℝ) ℓ :=
    Lemma57.cFar_nonneg (by simpa only [W] using hW1)
      (lt_of_lt_of_le zero_lt_one hℓ1)
  have hJsqrt : Real.sqrt J ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := by
    calc
      Real.sqrt J ≤ Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 8)) :=
        Real.sqrt_le_sqrt hJ
      _ = (N : ℝ) ^ ((1 : ℝ) / 16) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have hJprod : J * Real.sqrt J ≤ (N : ℝ) ^ ((3 : ℝ) / 16) := by
    calc
      J * Real.sqrt J ≤ (N : ℝ) ^ ((1 : ℝ) / 8) *
          (N : ℝ) ^ ((1 : ℝ) / 16) :=
        mul_le_mul hJ hJsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = (N : ℝ) ^ ((3 : ℝ) / 16) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hAhalf : W / 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr hℓ1) hWpos.le,
      mul_nonneg (mul_nonneg hWpos.le (by linarith : 0 ≤ ℓ))
        (sub_nonneg.mpr hηhalf)]
  have hAinv : A⁻¹ ≤ 2 * (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have hi := inv_anti₀ (by positivity : 0 < W / 2) hAhalf
    calc
      A⁻¹ ≤ 2 * W⁻¹ := by simpa [div_eq_mul_inv] using hi
      _ ≤ 2 * (N : ℝ) ^ (-(5 / 8 : ℝ)) := by gcongr
  have hL : L ≤ (N : ℝ) := by
    have hL0 : 0 ≤ L := by dsimp [L]; positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hW1) hL0]
  have hW30 : Real.sqrt (W ^ (-(60 : ℝ))) ≤
      (N : ℝ) ^ (-(75 / 4 : ℝ)) := by
    have hp : W ^ (-(30 : ℝ)) ≤ (N : ℝ) ^ (-(75 / 4 : ℝ)) := by
      calc
        W ^ (-(30 : ℝ)) ≤
            ((N : ℝ) ^ ((5 : ℝ) / 8)) ^ (-(30 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos
            (Real.rpow_pos_of_pos hNpos _) hWgrow (by norm_num)
        _ = (N : ℝ) ^ (-(75 / 4 : ℝ)) := by
          rw [← Real.rpow_mul hNpos.le]
          congr 1
          ring
    calc
      Real.sqrt (W ^ (-(60 : ℝ))) = W ^ (-(30 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hWpos.le]
        congr 1
        ring
      _ ≤ _ := hp
  constructor
  · have hrow : Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ ≤
        (3 / 2 : ℝ) * (N : ℝ) ^ (θ - 1 / 8) := by
      calc
        _ ≤ (N : ℝ) ^ θ * (N : ℝ) ^ ((1 : ℝ) / 8) *
            ((3 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
              gcongr
        _ = (3 / 2 : ℝ) * (N : ℝ) ^ (θ - 1 / 8) := by
          calc
            (N : ℝ) ^ θ * (N : ℝ) ^ ((1 : ℝ) / 8) *
                ((3 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ))) =
                (3 / 2 : ℝ) * ((N : ℝ) ^ θ *
                  (N : ℝ) ^ ((1 : ℝ) / 8) *
                    (N : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
            _ = _ := by
              rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
              congr 1
              ring
    calc
      κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂) ≤
          (4 * (N : ℝ) ^ ζ) *
            ((3 / 2 : ℝ) * (N : ℝ) ^ (θ - 1 / 8)) :=
        mul_le_mul hκ₁ hrow
          (mul_nonneg (mul_nonneg hcFar0 hJ0) hκ₂0) (by positivity)
      _ = 6 * (N : ℝ) ^ (ζ + θ - 1 / 8) := by
        calc
          (4 * (N : ℝ) ^ ζ) *
              ((3 / 2 : ℝ) * (N : ℝ) ^ (θ - 1 / 8)) =
              6 * ((N : ℝ) ^ ζ * (N : ℝ) ^ (θ - 1 / 8)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hNpos]
            congr 1
            ring
  · constructor
    · have hrow : 168 * J * Real.sqrt J * A⁻¹ ≤
          336 * (N : ℝ) ^ (-(7 / 16 : ℝ)) := by
        calc
          _ = 168 * (J * Real.sqrt J) * A⁻¹ := by ring
          _ ≤ 168 * (N : ℝ) ^ ((3 : ℝ) / 16) *
              (2 * (N : ℝ) ^ (-(5 / 8 : ℝ))) := by gcongr
          _ = 336 * (N : ℝ) ^ (-(7 / 16 : ℝ)) := by
            calc
              168 * (N : ℝ) ^ ((3 : ℝ) / 16) *
                  (2 * (N : ℝ) ^ (-(5 / 8 : ℝ))) =
                  336 * ((N : ℝ) ^ ((3 : ℝ) / 16) *
                    (N : ℝ) ^ (-(5 / 8 : ℝ))) := by ring
              _ = _ := by
                rw [← Real.rpow_add hNpos]
                congr 1
                ring
      calc
        κ₁ * (168 * J * Real.sqrt J * A⁻¹) ≤
            (4 * (N : ℝ) ^ ζ) *
              (336 * (N : ℝ) ^ (-(7 / 16 : ℝ))) :=
          mul_le_mul hκ₁ hrow (by positivity) (by positivity)
        _ = 1344 * (N : ℝ) ^ (ζ - 7 / 16) := by
          calc
            (4 * (N : ℝ) ^ ζ) *
                (336 * (N : ℝ) ^ (-(7 / 16 : ℝ))) =
                1344 * ((N : ℝ) ^ ζ *
                  (N : ℝ) ^ (-(7 / 16 : ℝ))) := by ring
            _ = _ := by
              rw [← Real.rpow_add hNpos]
              congr 1
    · have hrow : J * Real.sqrt J * L *
          Real.sqrt (W ^ (-(60 : ℝ))) / ℓ ≤
          (N : ℝ) ^ (-(281 / 16 : ℝ)) := by
        have hnum0 : 0 ≤ J * Real.sqrt J * L *
            Real.sqrt (W ^ (-(60 : ℝ))) := by positivity
        calc
          J * Real.sqrt J * L * Real.sqrt (W ^ (-(60 : ℝ))) / ℓ ≤
              J * Real.sqrt J * L * Real.sqrt (W ^ (-(60 : ℝ))) :=
            div_le_self hnum0 hℓ1
          _ ≤ (N : ℝ) ^ ((3 : ℝ) / 16) * (N : ℝ) *
              (N : ℝ) ^ (-(75 / 4 : ℝ)) := by
            calc
              J * Real.sqrt J * L * Real.sqrt (W ^ (-(60 : ℝ))) =
                  (J * Real.sqrt J) * L *
                    Real.sqrt (W ^ (-(60 : ℝ))) := by ring
              _ ≤ _ := by gcongr
          _ = (N : ℝ) ^ (-(281 / 16 : ℝ)) := by
            calc
              (N : ℝ) ^ ((3 : ℝ) / 16) * (N : ℝ) *
                  (N : ℝ) ^ (-(75 / 4 : ℝ)) =
                  (N : ℝ) ^ ((3 : ℝ) / 16) * (N : ℝ) ^ (1 : ℝ) *
                    (N : ℝ) ^ (-(75 / 4 : ℝ)) := by rw [Real.rpow_one]
              _ = _ := by
                rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
                congr 1
                ring
      calc
        κ₁ * (J * Real.sqrt J * (d.L N : ℝ) *
            Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) ≤
            (4 * (N : ℝ) ^ ζ) *
              (N : ℝ) ^ (-(281 / 16 : ℝ)) := by
          dsimp [L, W] at hrow
          exact mul_le_mul hκ₁ hrow (by positivity) (by positivity)
        _ = 4 * (N : ℝ) ^ (ζ - 281 / 16) := by
          rw [mul_assoc, ← Real.rpow_add hNpos]
          congr 1

/-- After choosing both small losses from `ν`, the sum of the three literal
rows is bounded by `N^ν`, uniformly in the first half-cell. -/
theorem eventually_far_rows_absorbed {ν : ℝ} (hν : 0 < ν) :
    let ζ := sourceLoss ν
    ∀ᶠ N : ℕ in atTop, ∀ r ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ J : ℝ,
      0 ≤ J → J ≤ (N : ℝ) ^ ((1 : ℝ) / 8) →
      let ℓ := B.ell N r
      let η := etaT 0 r
      let A := (d.W N : ℝ) * ℓ * η
      let κ₁ := 2 * (N : ℝ) ^ ζ * ℓ
      let κ₂ := firstCellDelta N + (d.W N : ℝ)⁻¹
      κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
          168 * J * Real.sqrt J * A⁻¹ +
          J * Real.sqrt J * (d.L N : ℝ) *
            Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) ≤
        (N : ℝ) ^ ν := by
  dsimp only
  let ζ := sourceLoss ν
  let θ := subpolyLoss ν
  have hθ : 0 < θ := by
    dsimp [θ, subpolyLoss]
    exact lt_min (by positivity) (by norm_num)
  have hζcap : ζ ≤ 1 / 64 := by
    dsimp [ζ, sourceLoss]
    exact min_le_right _ _
  have hθcap : θ ≤ 1 / 64 := by
    dsimp [θ, subpolyLoss]
    exact min_le_right _ _
  have hlarge := eventually_le_rpow 1354 hν
  filter_upwards [eventually_cFar_le_running hθ, Dims.bandwidth_grow,
    Dims.dim_grow, hlarge, eventually_ge_atTop 1] with
    N hcFar hWgrow hdim hlarge hN r hr J hJ0 hJ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hWgrow' : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ) := by
    convert hWgrow using 1 <;> norm_num
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  obtain ⟨hrow1, hrow2, hrow3⟩ := far_rows_le_powers
    N r ζ θ J hNr hr hWgrow' hWL (hcFar r hr) hJ0 hJ
  let ℓ : ℝ := B.ell N r
  let η : ℝ := etaT 0 r
  let A : ℝ := (d.W N : ℝ) * ℓ * η
  let κ₁ : ℝ := 2 * (N : ℝ) ^ ζ * ℓ
  let κ₂ : ℝ := firstCellDelta N + (d.W N : ℝ)⁻¹
  have hp1 : (N : ℝ) ^ (ζ + θ - 1 / 8) ≤ 1 := by
    calc
      _ ≤ (N : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = 1 := Real.rpow_zero _
  have hp2 : (N : ℝ) ^ (ζ - 7 / 16) ≤ 1 := by
    calc
      _ ≤ (N : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = 1 := Real.rpow_zero _
  have hp3 : (N : ℝ) ^ (ζ - 281 / 16) ≤ 1 := by
    calc
      _ ≤ (N : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = 1 := Real.rpow_zero _
  have h1 : κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂) ≤ 6 :=
    hrow1.trans (by nlinarith)
  have h2 : κ₁ * (168 * J * Real.sqrt J * A⁻¹) ≤ 1344 :=
    hrow2.trans (by nlinarith)
  have h3 : κ₁ * (J * Real.sqrt J * (d.L N : ℝ) *
      Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) ≤ 4 :=
    hrow3.trans (by nlinarith)
  calc
    κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
        168 * J * Real.sqrt J * A⁻¹ +
        J * Real.sqrt J * (d.L N : ℝ) *
          Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) =
      κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂) +
        κ₁ * (168 * J * Real.sqrt J * A⁻¹) +
        κ₁ * (J * Real.sqrt J * (d.L N : ℝ) *
          Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) := by ring
    _ ≤ 1354 := by linarith
    _ ≤ (N : ℝ) ^ ν := hlarge

/-- On positive active-prefix support, every far output satisfies the desired
arbitrarily small power bound at every real running time.  The zero-time case
is discharged by the exact identity `eGpm = 0`. -/
theorem eventually_far_on_active_support {τ' ν : ℝ}
    (hτ' : 0 < τ') (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good τ' ν N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
          N0 p N k m ω →
        ∀ r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
        ∀ a₁ a₂ : ZMod (d.L N),
          ellStar (d.W N : ℝ) (B.ell N r) ≤
            (zdist (d.L N) (a₂ - a₁) : ℝ) →
          ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
              (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
            (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
              tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                (zdist (d.L N) (a₂ - a₁)) := by
  have hζ : 0 < sourceLoss ν := by
    unfold sourceLoss
    exact lt_min (by positivity) (by norm_num)
  filter_upwards [
    APrimeFirstCellEGFarRunning.eventually_running_far_exact
      (ζ₃ := sourceLoss ν) hτ' hζ,
    eventually_far_rows_absorbed hν] with N hbase hrows
  intro ω hω N0 p k m hN0 hp hm hk hkT hw r hr a₁ a₂ hfar
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans htop.2 |>.trans
      (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  by_cases hrzero : r = 0
  · subst r
    rw [APrimeFirstCellAllTimeNearSources.eGpm_zero N ω a₁ a₂, norm_zero]
    have hW0 : (0 : ℝ) ≤ d.W N := by exact_mod_cast (d.W_pos N).le
    have ht : 0 ≤ tailT (d.W N : ℝ) (B.ell N 0) (etaT 0 0) 60
        (zdist (d.L N) (a₂ - a₁)) := tailT_nonneg hW0 _
    have hp : 0 ≤ (N : ℝ) ^ ν := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hη : 0 ≤ (etaT 0 0)⁻¹ := by norm_num [etaT, mE_zero]
    exact mul_nonneg (mul_nonneg hp hη) ht
  · have hb := hbase N0 p k m hN0 hp hm hk hkT ω hω hw r hr a₁ a₂ hfar
    dsimp only at hb
    let ℓ : ℝ := B.ell N r
    let η : ℝ := etaT 0 r
    let A : ℝ := (d.W N : ℝ) * ℓ * η
    let J : ℝ := APrimeSupportRunning.jG N r ω
    let κ₁ : ℝ := 2 * (N : ℝ) ^ (sourceLoss ν) * ℓ
    let κ₂ : ℝ := firstCellDelta N + (d.W N : ℝ)⁻¹
    have hℓs : B.ell N (firstCellS τ' N) = 1 := by
      rw [firstCellS_eq_zero]
      exact ellHat_zero (B.L N) (B.three_le_L N)
    have hJ0 : 0 ≤ J := by
      have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
      exact (by norm_num : (0 : ℝ) ≤ 1).trans
        (APrimeJG.one_le_jG (sample d) 0 N r ω hWpos)
    have hcoef : κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
        168 * J * Real.sqrt J * A⁻¹ +
        J * Real.sqrt J * (d.L N : ℝ) *
          Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) ≤
        (N : ℝ) ^ ν := by
      simpa only [ℓ, η, A, J, κ₁, κ₂] using hrows r hrhalf J hJ0 hb.1
    have hηpos : 0 < η := by
      dsimp [η]
      exact etaT_pos_of_lt_one (by norm_num) (hrhalf.2.trans_lt (by norm_num))
    have htail : 0 ≤ tailT (d.W N : ℝ) ℓ η 60
        (zdist (d.L N) (a₂ - a₁)) := by
      apply tailT_nonneg
      exact_mod_cast (d.W_pos N).le
    have hb' : ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
        η⁻¹ * κ₁ *
          (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
            168 * J * Real.sqrt J * A⁻¹ +
            J * Real.sqrt J * (d.L N : ℝ) *
              Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) *
          tailT (d.W N : ℝ) ℓ η 60
            (zdist (d.L N) (a₂ - a₁)) := by
      simpa only [hℓs, div_one, ℓ, η, A, J, κ₁, κ₂] using hb.2
    calc
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
          η⁻¹ * κ₁ *
            (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
              168 * J * Real.sqrt J * A⁻¹ +
              J * Real.sqrt J * (d.L N : ℝ) *
                Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) *
            tailT (d.W N : ℝ) ℓ η 60
              (zdist (d.L N) (a₂ - a₁)) := hb'
      _ = η⁻¹ *
          (κ₁ * (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
            168 * J * Real.sqrt J * A⁻¹ +
            J * Real.sqrt J * (d.L N : ℝ) *
              Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ)) *
          tailT (d.W N : ℝ) ℓ η 60
            (zdist (d.L N) (a₂ - a₁)) := by ring
      _ ≤ η⁻¹ * (N : ℝ) ^ ν *
          tailT (d.W N : ℝ) ℓ η 60
            (zdist (d.L N) (a₂ - a₁)) := by gcongr
      _ = (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
          tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
            (zdist (d.L N) (a₂ - a₁)) := by
        dsimp [ℓ, η]
        ring

/-- A same-event nonvacuity witness at the first active prefix, augmented by
the absorbed far estimate at its antipodal pair. -/
def positiveFarSmallPlateau (τ' ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ good τ' ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
      (firstCellT τ') 2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    (bHalf B N).1 ≠ (bHalf B N).2 ∧
    ellStar (d.W N : ℝ) (B.ell N u2) ≤
      (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) ∧
    APrimeSupportRunning.jG N u2 ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
        (Hflow d N u2 ω) (zt 0 u2) (bHalf B N).2 (bHalf B N).1‖ ≤
      (N : ℝ) ^ ν * (etaT 0 u2)⁻¹ *
        tailT (d.W N : ℝ) (B.ell N u2) (etaT 0 u2) 60
          (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2))

theorem positiveFarSmallPlateau_of_good {τ' ν : ℝ}
    (hτ' : 0 < τ') (hν : 0 < ν)
    (hp : HighProb (P d) (good τ' ν)) :
    positiveFarSmallPlateau τ' ν := by
  have hp' : HighProb (P d)
      (APrimeFirstCellEGFarRunning.good τ' (sourceLoss ν) (sourceLoss ν)) := hp
  have hplat := APrimeFirstCellEGFarRunning.positiveFarPlateau_of_good hτ' hp'
  filter_upwards [hplat, eventually_far_on_active_support hτ' hν,
    eventually_ge_atTop 2] with N hplat hsmall hN
  dsimp only [APrimeFirstCellEGFarRunning.positiveFarPlateau] at hplat
  obtain ⟨ω, hω, hk, hw, hu2pos, hu2le, hne, hfar, hJ⟩ := hplat
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hbound := hsmall ω hω 2 1 2 N (by omega) (by norm_num)
    (by omega) (by norm_num) hk (by rw [hw 1]; norm_num) u2
    ⟨hu2pos.le, le_rfl⟩ (bHalf B N).2 (bHalf B N).1 hfar
  exact ⟨ω, hω, hk, hw, hu2pos, hu2le, hne, hfar, hJ, hbound⟩

/-- One T358 parameter is chosen before `ν`; for every positive requested loss
the same event is measurable, high probability, eventually inhabited, and
has the positive `k = 2` absorbed far witness above. -/
theorem exists_highProb_good_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet (good τ' ν N)) ∧
        HighProb (P d) (good τ' ν) ∧
        (∀ᶠ N : ℕ in atTop, (good τ' ν N).Nonempty) ∧
        positiveFarSmallPlateau τ' ν := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ν hν
  have hp := highProb_good_of_inputs hτ' hν h1 hll h4 h6
  exact ⟨measurableSet_good hτ' ν, hp, hp.nonempty (by simp),
    positiveFarSmallPlateau_of_good hτ' hν hp⟩

#print axioms eventually_cFar_le_running
#print axioms far_rows_le_powers
#print axioms eventually_far_rows_absorbed
#print axioms eventually_far_on_active_support
#print axioms positiveFarSmallPlateau_of_good
#print axioms exists_highProb_good_with_plateau

end RBM.APrimeFirstCellEGFarSmallRunning
