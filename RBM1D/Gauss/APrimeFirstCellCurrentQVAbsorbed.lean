/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFarRowAbsorb
import RBM1D.Gauss.APrimeFirstCellPrefixGoodRows

/-!
# T465: absorbed current quadratic-variation rate on the first cell

T438's literal current rate and T461's deterministic three-row absorption
are combined without changing the moving endpoint or the common event.
-/

namespace RBM.APrimeFirstCellCurrentQVAbsorbed

open Filter Set Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow

private noncomputable abbrev delta : ℝ :=
  APrimeFirstCellFarRowAbsorb.delta

private noncomputable abbrev tau : ℝ :=
  APrimeFirstCellFarRowAbsorb.tau

/-- The square-root rate after absorbing all three current rows. -/
noncomputable def absorbedCurrentRate (α : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
    (etaT 0 r) ^ (-(1 / 2 : ℝ)) *
      APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))

theorem absorbedCurrentRate_nonneg {α : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (_hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2) :
    0 ≤ absorbedCurrentRate α N v r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : r < 1 := hrv.trans hvhalf |>.trans_lt (by norm_num)
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hηr : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  unfold absorbedCurrentRate
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity)
        (Real.rpow_nonneg hNr.le _))
      (Real.rpow_nonneg hηr.le _))
    (Real.rpow_nonneg hxv.le _)

/-- Pointwise square-root conversion of the exact T438 rate after T461 has
bounded the complete current bracket. -/
theorem sqrt_qvAt_le_absorbed_of_rate {α : ℝ} {N : ℕ} {ω : Ω d}
    {v r : ℝ} {a : LoopArg (d.L N) 2}
    (hN : 1 ≤ N) (hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2)
    (hq : APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      APrimeFirstCellQVCurrentRows.currentRate delta tau α N v r)
    (hbracket : APrimeFirstCellFarRowAbsorb.currentBracket N v r ≤ 3) :
    Real.sqrt (APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω) ≤
      absorbedCurrentRate α N v r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : r < 1 := hrv.trans hvhalf |>.trans_lt (by norm_num)
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
  have hq3 : APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    calc
      _ ≤ APrimeFirstCellQVCurrentRows.currentRate delta tau α N v r := hq
      _ = APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
          (etaT 0 r)⁻¹ *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) *
              APrimeFirstCellFarRowAbsorb.currentBracket N v r :=
        APrimeFirstCellFarRowAbsorb.currentRate_eq α N v r
      _ ≤ _ := mul_le_mul_of_nonneg_left hbracket hfac0
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
  have htarget_sq : (absorbedCurrentRate α N v r) ^ 2 =
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    unfold absorbedCurrentRate APrimeFirstCellQVCurrentRows.currentConstant
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
  exact ⟨absorbedCurrentRate_nonneg hN hr0 hrv hvhalf,
    hq3.trans_eq htarget_sq.symm⟩

/-- Same-event absorbed current-QV estimate at every positive-support moving
endpoint.  The interval is closed, so both `r=0` and `r=v` are included. -/
def currentQVAbsorbed (τ' α : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight delta (firstCellT τ')
        N0 p N k m ω →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
        ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
          Real.sqrt (APrimeDriftTimeFamily.qvAt
            d 0 60 N Step2.sigPM a 0 v r ω) ≤
              absorbedCurrentRate α N v r

theorem eventually_currentQVAbsorbed {τ' α : ℝ}
    (hτ' : 0 < τ') (hα : 0 < α) : currentQVAbsorbed τ' α := by
  filter_upwards [
    APrimeFirstCellQVCurrentRows.eventually_currentRowsBound
      hτ' APrimeFirstCellFarRowAbsorb.delta_pos.le hα,
    APrimeFirstCellFarRowAbsorb.eventually_currentBracket_le_three hτ',
    eventually_ge_atTop 1] with N hrows hbracket hN
  intro ω hω N0 p k m hN0 hp hm hk1 hk hw
  obtain ⟨hvpos, hvle, hvhalf, _hJall, hpoint⟩ :=
    hrows ω hω N0 p k m hN0 hp hm hk1 hk hw
  refine ⟨hvpos, hvle, hvhalf, ?_⟩
  intro r hr a
  exact sqrt_qvAt_le_absorbed_of_rate hN hr.1 hr.2 hvhalf
    ((hpoint r hr).2.2 a) (hbracket k hk r hr)

/-- On the exact strict T455 transition, canonical smoothing gives the
positive-weight premise needed by the same-event theorem. -/
theorem eventually_transition_sqrt_qvAt_le_absorbed {τ' α : ℝ}
    (hτ' : 0 < τ') (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N,
      ∀ k : ℕ, 1 ≤ k →
        k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        ω ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT τ') APrimeSmoothTransition.transitionMesh N) →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
          Real.sqrt (APrimeDriftTimeFamily.qvAt
            d 0 60 N Step2.sigPM a 0 v r ω) ≤
              absorbedCurrentRate α N v r := by
  filter_upwards [eventually_currentQVAbsorbed hτ' hα,
    eventually_ge_atTop 2] with N hmain hN2
  intro ω hω k hk1 hk htrans
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have hm : 1 ≤ m := APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have hw : 0 < APrimeSupportRunning.weight delta (firstCellT τ')
      2 1 N k m ω :=
    APrimeFirstCellPrefixGoodRows.actualWeight_pos_of_transition hN2 hk htrans
  exact (hmain ω hω 2 1 k m hN2 (by norm_num) hm hk1 hk hw).2.2.2

/-- The `k=0` endpoint is kept as a separate geometric branch.  No
positive-support or transition inhabitance assertion is made here. -/
theorem zero_endpoint (N : ℕ) :
    cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0 = 0 := by
  simp only [cutNetPt_zero]

/-- Positive `k=2` resident carrying the absorbed current-QV bound on the
literal common event, including both current-time endpoints. -/
def positiveAbsorbedCurrentQVPlateau (τ' α : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N,
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
    (∀ p : ℕ, APrimeSupportRunning.weight delta (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v r ω) ≤
          absorbedCurrentRate α N v r) ∧
    (∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v 0 ω) ≤
          absorbedCurrentRate α N v 0) ∧
    ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v v ω) ≤
          absorbedCurrentRate α N v v

theorem positiveAbsorbedCurrentQVPlateau_of_current {τ' α : ℝ}
    (hτ' : 0 < τ')
    (hpositive : APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau
      τ' delta α) :
    positiveAbsorbedCurrentQVPlateau τ' α := by
  filter_upwards [hpositive,
    APrimeFirstCellFarRowAbsorb.eventually_currentBracket_le_three hτ',
    APrimeFirstCellScaleFloors.eventually_positive_two_scalePackage hτ',
    eventually_ge_atTop 1] with N hpositive hbracket htwo hN
  dsimp only [APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau]
    at hpositive
  obtain ⟨ω, hω, hvpos, hvle, hvhalf, hw, _hsource, _hJall,
    hpoint, hzero, hend⟩ := hpositive
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hk : 2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N := htwo.2.resident
  have habs : ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v r ω) ≤
          absorbedCurrentRate α N v r := by
    intro r hr a
    exact sqrt_qvAt_le_absorbed_of_rate hN hr.1 hr.2 hvhalf
      ((hpoint r hr).2.2 a) (hbracket 2 hk r hr)
  refine ⟨ω, hω, hvpos, hvle, hvhalf, hw, habs, ?_, ?_⟩
  · intro a
    exact habs 0 ⟨le_rfl, hvpos.le⟩ a
  · intro a
    exact habs v ⟨hvpos.le, le_rfl⟩ a

/-- Closed same-event producer with a positive actual `k=2` resident. -/
theorem exists_currentQVAbsorbed_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ α : ℝ, 0 < α →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α) ∧
        currentQVAbsorbed τ' α ∧
        positiveAbsorbedCurrentQVPlateau τ' α := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQVCurrentRows.exists_currentRowsBound_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro α hα
  obtain ⟨hmeas, hp, _hcurrent, hpositive⟩ := hall delta
    APrimeFirstCellFarRowAbsorb.delta_pos (by norm_num [delta,
      APrimeFirstCellFarRowAbsorb.delta]) α hα
  exact ⟨hmeas, hp, eventually_currentQVAbsorbed hτ' hα,
    positiveAbsorbedCurrentQVPlateau_of_current hτ' hpositive⟩

#print axioms sqrt_qvAt_le_absorbed_of_rate
#print axioms eventually_currentQVAbsorbed
#print axioms eventually_transition_sqrt_qvAt_le_absorbed
#print axioms zero_endpoint
#print axioms positiveAbsorbedCurrentQVPlateau_of_current
#print axioms exists_currentQVAbsorbed_with_plateau

end RBM.APrimeFirstCellCurrentQVAbsorbed
