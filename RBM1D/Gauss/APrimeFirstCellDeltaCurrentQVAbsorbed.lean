/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFarRowAbsorb
import RBM1D.Gauss.APrimeFirstCellPrefixGoodRows

/-!
# T540: variable-delta first-cell current-QV square-root absorption

The variable-delta current rate is combined with the deterministic three-row
absorption on the identical sharp common event.  The square root retains the
exact powers `N^(nu/2)`, `eta_r^(-1/2)`, and `xRate_v^(-2)`.
-/

namespace RBM.APrimeFirstCellDeltaCurrentQVAbsorbed

open Filter Set Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The square-root rate after absorbing all three current rows. -/
noncomputable def absorbedCurrentRate (nu : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  384 * Real.sqrt 3 * (N : ℝ) ^ (nu / 2) *
    (etaT 0 r) ^ (-(1 / 2 : ℝ)) *
      APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))

theorem absorbedCurrentRate_nonneg {nu : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (_hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2) :
    0 ≤ absorbedCurrentRate nu N v r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : r < 1 := hrv.trans hvhalf |>.trans_lt (by norm_num)
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have heta : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  unfold absorbedCurrentRate
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity)
        (Real.rpow_nonneg hNr.le _))
      (Real.rpow_nonneg heta.le _))
    (Real.rpow_nonneg hxv.le _)

/-- Pointwise square-root conversion of the variable-delta current rate. -/
theorem sqrt_qvAt_le_absorbed_of_rate {delta nu : ℝ} {N : ℕ} {omega : Ω d}
    {v r : ℝ} {a : LoopArg (d.L N) 2}
    (hN : 1 ≤ N) (hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2)
    (hq : APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r omega ≤
      APrimeFirstCellQVCurrentRows.currentRate delta
        (APrimeFirstCellDeltaFarRowAbsorb.tau delta) nu N v r)
    (hbracket : APrimeFirstCellDeltaFarRowAbsorb.currentBracket
      delta N v r ≤ 3) :
    Real.sqrt (APrimeDriftTimeFamily.qvAt
      d 0 60 N Step2.sigPM a 0 v r omega) ≤
        absorbedCurrentRate nu N v r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : r < 1 := hrv.trans hvhalf |>.trans_lt (by norm_num)
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have heta : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  have hfac0 : 0 ≤
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ nu *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg APrimeFirstCellQVCurrentRows.currentConstant_pos.le
          (Real.rpow_nonneg hNr.le _))
        (inv_nonneg.mpr heta.le))
      (Real.rpow_nonneg hxv.le _)
  have hq3 : APrimeDriftTimeFamily.qvAt
      d 0 60 N Step2.sigPM a 0 v r omega ≤
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ nu *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    calc
      _ ≤ APrimeFirstCellQVCurrentRows.currentRate delta
          (APrimeFirstCellDeltaFarRowAbsorb.tau delta) nu N v r := hq
      _ = APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ nu *
          (etaT 0 r)⁻¹ *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) *
              APrimeFirstCellDeltaFarRowAbsorb.currentBracket delta N v r :=
        APrimeFirstCellDeltaFarRowAbsorb.currentRate_eq delta nu N v r
      _ ≤ _ := mul_le_mul_of_nonneg_left hbracket hfac0
  have hNhalf : ((N : ℝ) ^ (nu / 2)) ^ 2 = (N : ℝ) ^ nu := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  have hetahalf : ((etaT 0 r) ^ (-(1 / 2 : ℝ))) ^ 2 =
      (etaT 0 r)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul heta.le,
      ← Real.rpow_neg_one]
    congr 1
    ring
  have hxpow :
      (APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2 =
        APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxv.le]
    congr 1
    ring
  have htarget_sq : (absorbedCurrentRate nu N v r) ^ 2 =
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ nu *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    unfold absorbedCurrentRate APrimeFirstCellQVCurrentRows.currentConstant
    calc
      (384 * √3 * (N : ℝ) ^ (nu / 2) *
          etaT 0 r ^ (-(1 / 2 : ℝ)) *
            APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2 =
          384 ^ 2 * (√3) ^ 2 * (((N : ℝ) ^ (nu / 2)) ^ 2) *
            ((etaT 0 r ^ (-(1 / 2 : ℝ))) ^ 2) *
              ((APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2) := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by norm_num), hNhalf, hetahalf, hxpow]
        norm_num
        ring
  rw [Real.sqrt_le_iff]
  exact ⟨absorbedCurrentRate_nonneg hN hr0 hrv hvhalf,
    hq3.trans_eq htarget_sq.symm⟩

/-- Same-event absorbed current-QV estimate at every positive-support moving
endpoint, including both endpoints of the closed current-time interval. -/
def currentQVAbsorbed (tauPrime delta nu : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
      tauPrime delta nu N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight delta (firstCellT tauPrime)
        N0 p N k m omega →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      0 < v ∧ v ≤ firstCellT tauPrime N ∧ v ≤ 1 / 2 ∧
        ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
          Real.sqrt (APrimeDriftTimeFamily.qvAt
            d 0 60 N Step2.sigPM a 0 v r omega) ≤
              absorbedCurrentRate nu N v r

theorem eventually_currentQVAbsorbed {tauPrime delta nu : ℝ}
    (htau : 0 < tauPrime) (hdelta : 0 < delta)
    (hdelta100 : delta ≤ 1 / 100) (hnu : 0 < nu) :
    currentQVAbsorbed tauPrime delta nu := by
  filter_upwards [
    APrimeFirstCellQVCurrentRows.eventually_currentRowsBound
      htau hdelta.le hnu,
    APrimeFirstCellDeltaFarRowAbsorb.eventually_currentBracket_le_three
      htau hdelta hdelta100,
    eventually_ge_atTop 1] with N hrows hbracket hN
  intro omega homega N0 p k m hN0 hp hm hk1 hk hw
  obtain ⟨hvpos, hvle, hvhalf, _hJall, hpoint⟩ :=
    hrows omega homega N0 p k m hN0 hp hm hk1 hk hw
  refine ⟨hvpos, hvle, hvhalf, ?_⟩
  intro r hr a
  exact sqrt_qvAt_le_absorbed_of_rate hN hr.1 hr.2 hvhalf
    ((hpoint r hr).2.2 a) (hbracket k hk r hr)

/-- On the exact strict transition, its actual support weight supplies the
positive-weight premise of the same-event theorem. -/
theorem eventually_transition_sqrt_qvAt_le_absorbed
    {tauPrime delta nu : ℝ} (htau : 0 < tauPrime)
    (hdelta : 0 < delta) (hdelta100 : delta ≤ 1 / 100)
    (hnu : 0 < nu) :
    ∀ᶠ N : ℕ in atTop,
      ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta nu N,
      ∀ k : ℕ, 1 ≤ k →
        k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh N →
        omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
          Real.sqrt (APrimeDriftTimeFamily.qvAt
            d 0 60 N Step2.sigPM a 0 v r omega) ≤
              absorbedCurrentRate nu N v r := by
  filter_upwards [eventually_currentQVAbsorbed htau hdelta hdelta100 hnu,
    eventually_ge_atTop 2] with N hmain hN2
  intro omega homega k hk1 hk htrans
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hm : 1 ≤ m := APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hw : 0 < APrimeSupportRunning.weight delta (firstCellT tauPrime)
      2 1 N k m omega :=
    APrimeFirstCellPrefixGoodRows.actualWeight_pos_of_transition hN2 hk htrans
  exact (hmain omega homega 2 1 k m hN2 (by norm_num) hm hk1 hk hw).2.2.2

/-- The exact `k = 0` endpoint geometry is a separate degenerate branch. -/
theorem zero_endpoint_geometry (N : ℕ) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    v = 0 ∧ ∀ r ∈ Icc (0 : ℝ) v, r = 0 := by
  dsimp only
  have hv : cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 = 0 := by
    simp only [cutNetPt_zero]
  refine ⟨hv, ?_⟩
  intro r hr
  rw [hv] at hr
  exact le_antisymm hr.2 hr.1

/-- Positive `k = 2` resident carrying the absorbed bound on the same event,
including the zero and moving current-time endpoints. -/
def positiveAbsorbedCurrentQVPlateau (tauPrime delta nu : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
      tauPrime delta nu N,
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT tauPrime N ∧ v ≤ 1 / 2 ∧
    (∀ p : ℕ, APrimeSupportRunning.weight delta (firstCellT tauPrime)
      2 p N 2 N omega = 1) ∧
    (∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v r omega) ≤
          absorbedCurrentRate nu N v r) ∧
    (∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v 0 omega) ≤
          absorbedCurrentRate nu N v 0) ∧
    ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v v omega) ≤
          absorbedCurrentRate nu N v v

theorem positiveAbsorbedCurrentQVPlateau_of_current
    {tauPrime delta nu : ℝ} (htau : 0 < tauPrime)
    (hdelta : 0 < delta) (hdelta100 : delta ≤ 1 / 100)
    (hpositive : APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau
      tauPrime delta nu) :
    positiveAbsorbedCurrentQVPlateau tauPrime delta nu := by
  filter_upwards [hpositive,
    APrimeFirstCellDeltaFarRowAbsorb.eventually_currentBracket_le_three
      htau hdelta hdelta100,
    APrimeFirstCellScaleFloors.eventually_positive_two_scalePackage htau,
    eventually_ge_atTop 1] with N hpositive hbracket htwo hN
  dsimp only [APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau]
    at hpositive
  obtain ⟨omega, homega, hvpos, hvle, hvhalf, hw, _hsource, _hJall,
    hpoint, _hzero, _hend⟩ := hpositive
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hk : 2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N := htwo.2.resident
  have habs : ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (APrimeDriftTimeFamily.qvAt
        d 0 60 N Step2.sigPM a 0 v r omega) ≤
          absorbedCurrentRate nu N v r := by
    intro r hr a
    exact sqrt_qvAt_le_absorbed_of_rate hN hr.1 hr.2 hvhalf
      ((hpoint r hr).2.2 a) (hbracket 2 hk r hr)
  refine ⟨omega, homega, hvpos, hvle, hvhalf, hw, habs, ?_, ?_⟩
  · intro a
    exact habs 0 ⟨le_rfl, hvpos.le⟩ a
  · intro a
    exact habs v ⟨hvpos.le, le_rfl⟩ a

/-- One mesh exponent is chosen before all admissible `delta` and `nu`; the
identical sharp event then carries the full estimate and a positive resident. -/
theorem exists_currentQVAbsorbed_with_plateau :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
      ∀ nu : ℝ, 0 < nu →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta nu N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta nu) ∧
        currentQVAbsorbed tauPrime delta nu ∧
        positiveAbsorbedCurrentQVPlateau tauPrime delta nu := by
  obtain ⟨tauPrime, htau, hall⟩ :=
    APrimeFirstCellQVCurrentRows.exists_currentRowsBound_with_plateau
  refine ⟨tauPrime, htau, ?_⟩
  intro delta hdelta hdelta100 nu hnu
  obtain ⟨hmeas, hp, _hcurrent, hpositive⟩ :=
    hall delta hdelta hdelta100 nu hnu
  exact ⟨hmeas, hp,
    eventually_currentQVAbsorbed htau hdelta hdelta100 hnu,
    positiveAbsorbedCurrentQVPlateau_of_current
      htau hdelta hdelta100 hpositive⟩

#print axioms absorbedCurrentRate_nonneg
#print axioms sqrt_qvAt_le_absorbed_of_rate
#print axioms eventually_currentQVAbsorbed
#print axioms eventually_transition_sqrt_qvAt_le_absorbed
#print axioms zero_endpoint_geometry
#print axioms positiveAbsorbedCurrentQVPlateau_of_current
#print axioms exists_currentQVAbsorbed_with_plateau

end RBM.APrimeFirstCellDeltaCurrentQVAbsorbed
