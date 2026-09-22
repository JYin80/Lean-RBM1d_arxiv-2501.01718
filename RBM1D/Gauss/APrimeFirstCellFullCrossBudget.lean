/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFullCrossIntegrability
import RBM1D.Gauss.APrimeFirstCellFarRowAbsorb
import RBM1D.Gauss.APrimeFirstCellCrossBadPayment
import RBM1D.Gauss.APrimeFirstCellPrefixAbsorbed

/-!
# T469: quantitative integral of the literal first-cell full cross rate

The exact favorable prefix rate, current three-row rate, all-sample
envelope, and complement probability are inserted into T457's `Bfull`.
-/

namespace RBM.APrimeFirstCellFullCrossBudget

open Filter MeasureTheory Set Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellFarRowAbsorb.delta

noncomputable abbrev tau : ℝ := APrimeFirstCellFarRowAbsorb.tau

/-- T464's absorbed favorable prefix coefficient. -/
noncomputable def prefixRate (α : ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  (16 * Real.sqrt 3 / Real.exp 1) * Real.sqrt v *
    (N : ℝ) ^ (α / 2 - 2 * delta)

/-- T461's absorbed square root of the current three-row rate. -/
noncomputable def currentRootRate (α : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
    (etaT 0 r) ^ (-(1 / 2 : ℝ)) *
      APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))

/-- Common scale in the final first-cell integral budget. -/
noncomputable def crossScale (α : ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  (N : ℝ) ^ (α - 2 * delta) *
    APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))

/-- Constant remaining inside the literal `Bfull` bracket. -/
noncomputable def bracketConstant : ℝ :=
  18432 * Real.sqrt 2 / Real.exp 1 + 1

/-- Explicit fixed-moment constant after integrating `r^{-1/2}`. -/
noncomputable def budgetConstant (p : ℕ) : ℝ :=
  (15 * (p : ℝ) / 4) * bracketConstant

/-- T457's literal rate with the T464 and T463 parameters inserted. -/
noncomputable def literalBfull (tauPrime α : ℝ) (p N : ℕ) (v r : ℝ) : ℝ :=
  APrimeFirstCellFullCrossIntegrability.Bfull p
    (prefixRate α N v)
    (APrimeFirstCellCrossBadPayment.jointEnvelope N)
    (APrimeFirstCellCrossBadPayment.rho tauPrime delta α N)
    delta α N v r

/-- Corrected literal envelope delivered by the T361 cross estimate. -/
noncomputable def BcrossActual (tauPrime α : ℝ) (p N : ℕ) (v r : ℝ) : ℝ :=
  (2 * (p : ℝ)) * literalBfull tauPrime α p N v r

/-- Explicit budget constant for the actual T361 envelope. -/
noncomputable def actualBudgetConstant (p : ℕ) : ℝ :=
  (2 * (p : ℝ)) * budgetConstant p

theorem bracketConstant_nonneg : 0 ≤ bracketConstant := by
  unfold bracketConstant
  positivity

theorem budgetConstant_nonneg (p : ℕ) : 0 ≤ budgetConstant p := by
  unfold budgetConstant
  exact mul_nonneg (by positivity) bracketConstant_nonneg

theorem prefixRate_nonneg {α : ℝ} {N : ℕ} {v : ℝ}
    (_hv0 : 0 ≤ v) : 0 ≤ prefixRate α N v := by
  unfold prefixRate
  positivity

theorem crossScale_nonneg {α : ℝ} {N : ℕ} {v : ℝ} :
    v ≤ 1 / 2 → 0 ≤ crossScale α N v := by
  intro hvhalf
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) (hvhalf.trans_lt (by norm_num)))
  unfold crossScale
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (Real.rpow_nonneg hxv.le _)

/-- The complete current bracket is retained until T461 bounds it by three. -/
theorem sqrt_currentRate_le {α : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (_hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hr : r ∈ Icc (0 : ℝ) v)
    (hbracket : APrimeFirstCellFarRowAbsorb.currentBracket N v r ≤ 3) :
    Real.sqrt (APrimeFirstCellQVCurrentRows.currentRate delta tau α N v r) ≤
      currentRootRate α N v r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : r < 1 := hr.2.trans hvhalf |>.trans_lt (by norm_num)
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hηr : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  have hfac0 : 0 ≤
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg APrimeFirstCellQVCurrentRows.currentConstant_pos.le
          (Real.rpow_nonneg hNr.le _))
        (inv_nonneg.mpr hηr.le))
      (Real.rpow_nonneg hxv.le _)
  have hrate :
      APrimeFirstCellQVCurrentRows.currentRate delta tau α N v r ≤
        APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
          (etaT 0 r)⁻¹ *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    rw [APrimeFirstCellFarRowAbsorb.currentRate_eq]
    exact mul_le_mul_of_nonneg_left hbracket hfac0
  have hNhalf : ((N : ℝ) ^ (α / 2)) ^ 2 = (N : ℝ) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  have hηhalf : ((etaT 0 r) ^ (-(1 / 2 : ℝ))) ^ 2 =
      (etaT 0 r)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hηr.le,
      ← Real.rpow_neg_one]
    congr 1
    ring
  have hxpow :
      (APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2 =
        APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxv.le]
    congr 1
    ring
  have htarget_sq : (currentRootRate α N v r) ^ 2 =
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    unfold currentRootRate APrimeFirstCellQVCurrentRows.currentConstant
    calc
      (384 * √3 * (N : ℝ) ^ (α / 2) *
          etaT 0 r ^ (-(1 / 2 : ℝ)) *
            APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2 =
          384 ^ 2 * (√3) ^ 2 * (((N : ℝ) ^ (α / 2)) ^ 2) *
            ((etaT 0 r ^ (-(1 / 2 : ℝ))) ^ 2) *
              ((APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2) := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by norm_num), hNhalf, hηhalf, hxpow]
        norm_num
        ring
  rw [Real.sqrt_le_iff]
  refine ⟨?_, hrate.trans_eq htarget_sq.symm⟩
  unfold currentRootRate
  positivity

private theorem eta_inv_half_le_sqrt_two {v r : ℝ}
    (hvhalf : v ≤ 1 / 2) (hr : r ∈ Icc (0 : ℝ) v) :
    (etaT 0 r) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 := by
  have hr1 : r < 1 := hr.2.trans hvhalf |>.trans_lt (by norm_num)
  have hη : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 r := by
    simp only [etaT, mE_zero]
    norm_num
    linarith [hr.2, hvhalf]
  have hinv : (etaT 0 r)⁻¹ ≤ (2 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hηhalf
    norm_num at this ⊢
    exact this
  have hsqrt := Real.sqrt_le_sqrt hinv
  rw [APrimeTimeInt.sqrt_inv_eq_rpow hη.le] at hsqrt
  simpa using hsqrt

private theorem sqrt_v_le_one {v : ℝ} (_hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2) :
    Real.sqrt v ≤ 1 := by
  have hv1 : v ≤ (1 : ℝ) := hvhalf.trans (by norm_num)
  simpa using (Real.sqrt_le_sqrt hv1)

/-- The sharp prefix coefficient and the retained current-root coefficient
multiply to the paper's explicit first-cell constant. -/
theorem prefix_mul_currentRoot_le {α : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hr : r ∈ Icc (0 : ℝ) v) :
    prefixRate α N v * currentRootRate α N v r ≤
      (18432 * Real.sqrt 2 / Real.exp 1) * crossScale α N v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNpow :
      (N : ℝ) ^ (α / 2 - 2 * delta) * (N : ℝ) ^ (α / 2) =
        (N : ℝ) ^ (α - 2 * delta) := by
    rw [← Real.rpow_add hNr]
    congr 1
    ring
  have hsqrt3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hηbound := eta_inv_half_le_sqrt_two hvhalf hr
  have hsv := sqrt_v_le_one hv0 hvhalf
  have hpow0 : 0 ≤ (N : ℝ) ^ (α - 2 * delta) :=
    Real.rpow_nonneg hNr.le _
  have hηpos : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num)
    (hr.2.trans hvhalf |>.trans_lt (by norm_num))
  have hη0 : 0 ≤ (etaT 0 r) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hηpos.le _
  have hx0 : 0 ≤ APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) := by
    exact Real.rpow_nonneg (by
      unfold APrimeFirstCellLoopCap.xRate
      exact (div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
        (Step2.etaT_pos' (by norm_num) (hvhalf.trans_lt (by norm_num)))).le) _
  calc
    prefixRate α N v * currentRootRate α N v r =
        (18432 / Real.exp 1) * Real.sqrt v *
          (N : ℝ) ^ (α - 2 * delta) *
            (etaT 0 r) ^ (-(1 / 2 : ℝ)) *
              APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) := by
      unfold prefixRate currentRootRate
      calc
        16 * Real.sqrt 3 / Real.exp 1 * Real.sqrt v *
              (N : ℝ) ^ (α / 2 - 2 * delta) *
            (384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
              etaT 0 r ^ (-(1 / 2 : ℝ)) *
                APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) =
            (16 * 384 / Real.exp 1) *
              (Real.sqrt 3 * Real.sqrt 3) * Real.sqrt v *
                ((N : ℝ) ^ (α / 2 - 2 * delta) *
                  (N : ℝ) ^ (α / 2)) *
                    etaT 0 r ^ (-(1 / 2 : ℝ)) *
                      APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) := by ring
        _ = _ := by
          rw [hNpow]
          have hsqrt3' : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
            nlinarith [hsqrt3]
          rw [hsqrt3']
          ring
    _ ≤ (18432 / Real.exp 1) * 1 *
          (N : ℝ) ^ (α - 2 * delta) * Real.sqrt 2 *
            APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) := by
      gcongr
    _ = (18432 * Real.sqrt 2 / Real.exp 1) * crossScale α N v := by
      unfold crossScale
      ring

/-- The two literal terms in T457's bracket fit the common moving scale. -/
theorem literal_bracket_le {tauPrime α : ℝ} {p N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hr : r ∈ Icc (0 : ℝ) v)
    (hbracket : APrimeFirstCellFarRowAbsorb.currentBracket N v r ≤ 3)
    (hpay : APrimeFirstCellCrossBadPayment.badPayment
      tauPrime delta α p N ≤ crossScale α N v) :
    prefixRate α N v *
          Real.sqrt (APrimeFirstCellQVCurrentRows.currentRate
            delta tau α N v r) +
        APrimeFirstCellCrossBadPayment.jointEnvelope N *
          APrimeFirstCellCrossBadPayment.rho tauPrime delta α N ^
            (1 / (2 * (p : ℝ))) ≤
      bracketConstant * crossScale α N v := by
  have hpref0 : 0 ≤ prefixRate α N v := prefixRate_nonneg hv0
  have hcurrent :
      prefixRate α N v *
          Real.sqrt (APrimeFirstCellQVCurrentRows.currentRate
            delta tau α N v r) ≤
        (18432 * Real.sqrt 2 / Real.exp 1) * crossScale α N v := by
    calc
      _ ≤ prefixRate α N v * currentRootRate α N v r :=
        mul_le_mul_of_nonneg_left
          (sqrt_currentRate_le hN hv0 hvhalf hr hbracket) hpref0
      _ ≤ _ := prefix_mul_currentRoot_le hN hv0 hvhalf hr
  have hpay' :
      APrimeFirstCellCrossBadPayment.jointEnvelope N *
          APrimeFirstCellCrossBadPayment.rho tauPrime delta α N ^
            (1 / (2 * (p : ℝ))) ≤ crossScale α N v := by
    have hden : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by norm_num
    simpa only [APrimeFirstCellCrossBadPayment.badPayment, hden] using hpay
  calc
    _ ≤ (18432 * Real.sqrt 2 / Real.exp 1) * crossScale α N v +
        crossScale α N v := add_le_add hcurrent hpay'
    _ = bracketConstant * crossScale α N v := by
      unfold bracketConstant
      ring

/-- Pointwise domination by the integrable square-root singularity.  The
totalized value at `r=0` is discharged separately. -/
theorem literalBfull_le {tauPrime α : ℝ} {p N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hr : r ∈ Icc (0 : ℝ) v)
    (hbracket : APrimeFirstCellFarRowAbsorb.currentBracket N v r ≤ 3)
    (hpay : APrimeFirstCellCrossBadPayment.badPayment
      tauPrime delta α p N ≤ crossScale α N v) :
    literalBfull tauPrime α p N v r ≤
      (15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v *
        (Real.sqrt r)⁻¹ := by
  by_cases hr0 : r = 0
  · subst r
    simp [literalBfull, APrimeFirstCellFullCrossIntegrability.Bfull]
  · have hsqrtinv0 : 0 ≤ (Real.sqrt r)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg r)
    have hp0 : 0 ≤ (15 * (p : ℝ) / 8) := by positivity
    have hmain := literal_bracket_le hN hv0 hvhalf hr hbracket hpay
    unfold literalBfull APrimeFirstCellFullCrossIntegrability.Bfull
    calc
      (15 * (p : ℝ) / 8) * (Real.sqrt r)⁻¹ *
          (prefixRate α N v *
              Real.sqrt (APrimeFirstCellQVCurrentRows.currentRate
                delta (delta / 16) α N v r) +
            APrimeFirstCellCrossBadPayment.jointEnvelope N *
              APrimeFirstCellCrossBadPayment.rho tauPrime delta α N ^
                (1 / (2 * (p : ℝ)))) ≤
          (15 * (p : ℝ) / 8) * (Real.sqrt r)⁻¹ *
            (bracketConstant * crossScale α N v) := by
        exact mul_le_mul_of_nonneg_left hmain (mul_nonneg hp0 hsqrtinv0)
      _ = _ := by ring

/-- Uniform quantitative integral budget for T457's literal `Bfull`, with
`p` fixed before the eventual bandwidth threshold. -/
theorem eventually_integral_literalBfull_le {tauPrime α : ℝ}
    (hTau : 0 < tauPrime) (hAlpha : 0 < α)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta α))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      (∫ r in (0 : ℝ)..v, literalBfull tauPrime α p N v r) ≤
        budgetConstant p * crossScale α N v := by
  filter_upwards [
    APrimeFirstCellScaleFloors.eventually_scalePackage hTau,
    APrimeFirstCellFarRowAbsorb.eventually_currentBracket_le_three hTau,
    APrimeFirstCellCrossBadPayment.eventually_badPayment_le_moving_rate
      hTau APrimeFirstCellFarRowAbsorb.delta_pos hAlpha hprob p hp,
    eventually_ge_atTop 1] with N hscale hbracket hpay hN
  intro k hk
  dsimp only
  by_cases hk0 : k = 0
  · subst k
    simp only [cutNetPt_zero, intervalIntegral.integral_same]
    exact mul_nonneg (budgetConstant_nonneg p) (crossScale_nonneg (by norm_num))
  · let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
    have hpack := hscale k hk
    have hv0 : 0 ≤ v := hpack.time_nonneg
    have hvhalf : v ≤ 1 / 2 := hpack.time_le_half
    have hrho : 0 ≤ APrimeFirstCellCrossBadPayment.rho
        tauPrime delta α N := ENNReal.toReal_nonneg
    have hint : IntervalIntegrable
        (literalBfull tauPrime α p N v) volume 0 v := by
      exact (APrimeFirstCellFullCrossIntegrability.intervalIntegrable_Bfull
        APrimeFirstCellFarRowAbsorb.delta_pos.le hAlpha hN hp hv0 hvhalf
        (prefixRate_nonneg hv0) (by
          unfold APrimeFirstCellCrossBadPayment.jointEnvelope
          positivity) hrho).1
    have hC0 : 0 ≤
        (15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v :=
      mul_nonneg (mul_nonneg (by positivity) bracketConstant_nonneg)
        (crossScale_nonneg hvhalf)
    have hdom : IntervalIntegrable
        (fun r : ℝ =>
          ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v) *
            (Real.sqrt r)⁻¹) volume 0 v :=
      by
        simpa using (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).const_mul
          ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v)
    have hmono :
        (∫ r in (0 : ℝ)..v, literalBfull tauPrime α p N v r) ≤
          ∫ r in (0 : ℝ)..v,
            ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v) *
              (Real.sqrt r)⁻¹ := by
      refine intervalIntegral.integral_mono_on hv0 hint hdom ?_
      intro r hr
      exact literalBfull_le hN hv0 hvhalf hr
        (hbracket k hk r hr) (hpay k hk)
    calc
      (∫ r in (0 : ℝ)..v, literalBfull tauPrime α p N v r) ≤
          ∫ r in (0 : ℝ)..v,
            ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v) *
              (Real.sqrt r)⁻¹ := hmono
      _ = ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v) *
            (2 * Real.sqrt v) := by
        rw [intervalIntegral.integral_const_mul]
        have hi := APrimeTimeInt.integral_sqrt_inv hv0
        simpa only [Real.sqrt_inv] using congrArg
          (fun z : ℝ =>
            ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v) * z) hi
      _ ≤ ((15 * (p : ℝ) / 8) * bracketConstant * crossScale α N v) * 2 := by
        exact mul_le_mul_of_nonneg_left (by
          have := sqrt_v_le_one hv0 hvhalf
          nlinarith) hC0
      _ = budgetConstant p * crossScale α N v := by
        unfold budgetConstant
        ring

/-- The `k=0` first-cell interval is exactly empty. -/
theorem integral_literalBfull_k0 (tauPrime α : ℝ) (p N : ℕ) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    (∫ r in (0 : ℝ)..v, literalBfull tauPrime α p N v r) = 0 := by
  simp only [cutNetPt_zero, intervalIntegral.integral_same]

theorem integral_BcrossActual_k0 (tauPrime α : ℝ) (p N : ℕ) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    (∫ r in (0 : ℝ)..v, BcrossActual tauPrime α p N v r) = 0 := by
  simp only [cutNetPt_zero, intervalIntegral.integral_same]

/-- The corrected T361 envelope has the same rate and the required extra
fixed factor `2p`. -/
theorem eventually_integral_BcrossActual_le {tauPrime α : ℝ}
    (hTau : 0 < tauPrime) (hAlpha : 0 < α)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta α))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      (∫ r in (0 : ℝ)..v, BcrossActual tauPrime α p N v r) ≤
        actualBudgetConstant p * crossScale α N v := by
  filter_upwards [eventually_integral_literalBfull_le
    hTau hAlpha hprob p hp] with N hN
  intro k hk
  dsimp only
  have h2p : 0 ≤ (2 * (p : ℝ)) := by positivity
  calc
    (∫ r in (0 : ℝ)..cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k,
        BcrossActual tauPrime α p N
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r) =
        (2 * (p : ℝ)) *
          ∫ r in (0 : ℝ)..cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k,
            literalBfull tauPrime α p N
              (cutNetPt (fun _ => 0)
                APrimeSmoothTransition.transitionMesh N k) r := by
      unfold BcrossActual
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 * (p : ℝ)) *
        (budgetConstant p * crossScale α N
          (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k)) :=
      mul_le_mul_of_nonneg_left (hN k hk) h2p
    _ = actualBudgetConstant p * crossScale α N
        (cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k) := by
      unfold actualBudgetConstant
      ring

/-- The positive `k=2` resident simultaneously carries both quantitative
budgets, so the bounds are not witnessed only by the empty `k=0` interval. -/
theorem eventually_positive_two_integral_budgets {tauPrime α : ℝ}
    (hTau : 0 < tauPrime) (hAlpha : 0 < α)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta α))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧
      2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      (∫ r in (0 : ℝ)..v, literalBfull tauPrime α p N v r) ≤
        budgetConstant p * crossScale α N v ∧
      (∫ r in (0 : ℝ)..v, BcrossActual tauPrime α p N v r) ≤
        actualBudgetConstant p * crossScale α N v := by
  filter_upwards [
    APrimeFirstCellScaleFloors.eventually_positive_two_scalePackage hTau,
    eventually_integral_literalBfull_le hTau hAlpha hprob p hp,
    eventually_integral_BcrossActual_le hTau hAlpha hprob p hp]
      with N htwo hliteral hactual
  dsimp only at htwo ⊢
  exact ⟨htwo.1, htwo.2.resident,
    hliteral 2 htwo.2.resident, hactual 2 htwo.2.resident⟩

#print axioms sqrt_currentRate_le
#print axioms prefix_mul_currentRoot_le
#print axioms literal_bracket_le
#print axioms literalBfull_le
#print axioms eventually_integral_literalBfull_le
#print axioms integral_literalBfull_k0
#print axioms integral_BcrossActual_k0
#print axioms eventually_integral_BcrossActual_le
#print axioms eventually_positive_two_integral_budgets

end RBM.APrimeFirstCellFullCrossBudget
