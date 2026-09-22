/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDriftTransportRaw
import RBM1D.Gauss.APrimeFirstCellDriftCoefficient

/-!
# T442: transported and absorbed actual first-cell drift

This file composes T431's moving-endpoint transport with T433's scalar
coefficient absorption on their identical T422 event.
-/

namespace RBM.APrimeFirstCellDriftAbsorbed

open Filter MeasureTheory Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

theorem etaT_zero_eq_one : etaT 0 0 = 1 := by
  norm_num [etaT, mE_zero]

theorem xRate_eq_inv_etaT (r : ℝ) :
    APrimeFirstCellLoopCap.xRate r = (etaT 0 r)⁻¹ := by
  rw [APrimeFirstCellLoopCap.xRate, etaT_zero_eq_one]
  exact one_div _

/-- T431 and T433 retain exactly the same actual T422 coefficient. -/
theorem rawDriftCoeff_eq_rawCoefficient
    (α : ℝ) (N : ℕ) (r : ℝ) (ω : Ω d) :
    APrimeFirstCellDriftTransportRaw.rawDriftCoeff α N r ω =
      APrimeFirstCellDriftCoefficient.rawCoefficient α N r ω := by
  rfl

/-- T431's reciprocal-square multiplier is T433's real-power multiplier. -/
theorem transportFactor_eq_scaledFactor (N : ℕ) {r v : ℝ}
    (hr1 : r < 1) (hv1 : v < 1) :
    APrimeFirstCellDriftTransportRaw.transportFactor N r v =
      Step2.xiK (d.L N) (d.W N) 1 *
        APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) *
        APrimeFirstCellLoopCap.xRate r ^ (-(2 : ℝ)) := by
  have hη0 : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hηr : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hηv : 0 < etaT 0 v := Step2.etaT_pos' (by norm_num) hv1
  have hxr : 0 < APrimeFirstCellLoopCap.xRate r := by
    exact div_pos hη0 hηr
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    exact div_pos hη0 hηv
  have hrpow : (APrimeFirstCellLoopCap.xRate r)⁻¹ ^ 2 =
      APrimeFirstCellLoopCap.xRate r ^ (-(2 : ℝ)) := by
    rw [inv_pow]
    rw [Real.rpow_neg hxr.le, ← Real.rpow_natCast]
    norm_num
  have hvpow : (APrimeFirstCellLoopCap.xRate v)⁻¹ ^ 2 =
      APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) := by
    rw [inv_pow]
    rw [Real.rpow_neg hxv.le, ← Real.rpow_natCast]
    norm_num
  unfold APrimeFirstCellDriftTransportRaw.transportFactor
  change Step2.xiK (d.L N) (d.W N) 1 *
      (APrimeFirstCellLoopCap.xRate v)⁻¹ ^ 2 *
      (APrimeFirstCellLoopCap.xRate r)⁻¹ ^ 2 = _
  rw [hvpow, hrpow]

/-- The literal transported T431 profile is definitionally the coefficient
absorbed by T433, including the actual scale and retained `W L W⁻⁶⁰` floor. -/
theorem transportedRawProfile_eq_scaledRawCoefficient
    (ν : ℝ) (N : ℕ) {r v : ℝ} (ω : Ω d)
    (hr1 : r < 1) (hv1 : v < 1) :
    APrimeFirstCellDriftTransportRaw.transportedRawProfile (ν / 2) N r v ω =
      APrimeFirstCellDriftCoefficient.scaledRawCoefficient ν N v r ω := by
  unfold APrimeFirstCellDriftTransportRaw.transportedRawProfile
  unfold APrimeFirstCellDriftCoefficient.scaledRawCoefficient
  rw [transportFactor_eq_scaledFactor N hr1 hv1,
    rawDriftCoeff_eq_rawCoefficient]

def absorbedDriftBound (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
        APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
          APrimeFirstCellDriftCoefficient.endpointCoefficient δ ν N v r

/-- T431 transport followed by T433 absorption on the identical T422 event. -/
theorem eventually_absorbed_drift_on_active_support {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν) : absorbedDriftBound τ' δ ν := by
  filter_upwards [
    APrimeFirstCellDriftTransportRaw.eventually_raw_transport_on_active_support
      hτ' hδ hδ100 (by linarith : 0 < ν / 2),
    APrimeFirstCellDriftCoefficient.eventually_coefficient_bound hτ' hδ hν]
      with N htrans hcoeff
  intro ω hω N0 p k m hN0 hp hm hk hkT hw
  dsimp only
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hvTop : v ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc hwin
      (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hkT)
  have hv1 : v < 1 :=
    (hvTop.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2).trans_lt
      (by norm_num)
  intro r hr a
  have hr1 : r < 1 := hr.2.trans_lt hv1
  have ht := htrans ω hω N0 p k m hN0 hp hm hk hkT hw r hr a
  have hc := hcoeff ω hω N0 p k m hN0 hp hm hk hkT hw r hr
  exact ht.trans ((transportedRawProfile_eq_scaledRawCoefficient
    ν N ω hr1 hv1).le.trans hc)

/-- The absorbed theorem retains both closed-interval boundary values. -/
theorem absorbed_drift_endpoints_of_bound {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (h : absorbedDriftBound τ' δ ν) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight δ (firstCellT τ')
          N0 p N k m ω →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        ∀ a : LoopArg (d.L N) 2,
          (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v 0 ω ≤
              APrimeFirstCellDriftCoefficient.endpointCoefficient δ ν N v 0) ∧
            (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v v ω ≤
              APrimeFirstCellDriftCoefficient.endpointCoefficient δ ν N v v) := by
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
  intro a
  exact ⟨hN ω hω N0 p k m hN0 hp hm hk hkT hw 0 ⟨le_rfl, hv⟩ a,
    hN ω hω N0 p k m hN0 hp hm hk hkT hw v ⟨hv, le_rfl⟩ a⟩

/-- The literal `k=0` branch is zero and hence satisfies the absorbed target. -/
theorem driftAt_cutNet_zero_le_endpointCoefficient
    (δ ν : ℝ) (N : ℕ) (ω : Ω d) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0) 0 ω ≤
      APrimeFirstCellDriftCoefficient.endpointCoefficient δ ν N 0 0 := by
  rw [APrimeFirstCellDriftTransportRaw.driftAt_cutNet_zero]
  have hη : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hηeq : etaT 0 0 = 1 := by norm_num [etaT, mE_zero]
  have hx : 0 < APrimeFirstCellLoopCap.xRate 0 := by
    exact div_pos hη hη
  have hxeq : APrimeFirstCellLoopCap.xRate 0 = 1 := by
    unfold APrimeFirstCellLoopCap.xRate
    rw [hηeq]
    norm_num
  have hA : 0 < APrimeFirstCellLoopCap.endpointScale N 0 := by
    exact B.scale_pos' (by norm_num) N (by norm_num) (by norm_num)
  have hNν : 0 ≤ (N : ℝ) ^ ν := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hNδ : 0 ≤ (N : ℝ) ^ (4 * δ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [APrimeFirstCellDriftCoefficient.endpointCoefficient, hηeq, hxeq]
  norm_num
  exact mul_nonneg
    (mul_nonneg APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le hNν)
    (add_nonneg zero_le_one (mul_nonneg hNδ (inv_nonneg.mpr hA.le)))

def positiveAbsorbedDriftPlateau (τ' δ ν : ℝ) : Prop :=
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
      ∀ r ∈ Set.Icc (0 : ℝ) u2, ∀ a : LoopArg (d.L N) 2,
        APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 u2 r ω ≤
          APrimeFirstCellDriftCoefficient.endpointCoefficient δ ν N u2 r

/-- T422's positive `k=2` resident remains on the same literal event after
both transport and coefficient absorption. -/
theorem positiveAbsorbedDriftPlateau_of_raw {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν)
    (hraw : APrimeFirstCellDriftRaw.positiveRawDriftPlateau
      τ' δ (ν / 2)) :
    positiveAbsorbedDriftPlateau τ' δ ν := by
  filter_upwards [hraw,
    eventually_absorbed_drift_on_active_support hτ' hδ hδ100 hν,
    eventually_ge_atTop 2] with N hraw habs hN
  dsimp only [APrimeFirstCellDriftRaw.positiveRawDriftPlateau] at hraw
  obtain ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, _⟩ := hraw
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  refine ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, ?_⟩
  intro r hr a
  exact habs ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hwδ 1]; norm_num) r hr a

/-- The quantifier order inherited from T422: one first-cell parameter,
then `delta,nu`, then eventual `N`. -/
theorem exists_good_with_absorbed_drift :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2) N)) ∧
        HighProb (P d)
          (APrimeFirstCellEGAllOutputRunning.good τ' δ (ν / 2)) ∧
        absorbedDriftBound τ' δ ν ∧
        positiveAbsorbedDriftPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hgood⟩ :=
    APrimeFirstCellDriftRaw.exists_good_with_raw_drift
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hraw, hplat⟩ :=
    hgood δ hδ hδ100 (ν / 2) (by linarith)
  exact ⟨hmeas, hp,
    eventually_absorbed_drift_on_active_support hτ' hδ hδ100 hν,
    positiveAbsorbedDriftPlateau_of_raw hτ' hδ hδ100 hν hplat⟩

#print axioms rawDriftCoeff_eq_rawCoefficient
#print axioms etaT_zero_eq_one
#print axioms xRate_eq_inv_etaT
#print axioms transportFactor_eq_scaledFactor
#print axioms transportedRawProfile_eq_scaledRawCoefficient
#print axioms eventually_absorbed_drift_on_active_support
#print axioms absorbed_drift_endpoints_of_bound
#print axioms driftAt_cutNet_zero_le_endpointCoefficient
#print axioms positiveAbsorbedDriftPlateau_of_raw
#print axioms exists_good_with_absorbed_drift

end RBM.APrimeFirstCellDriftAbsorbed
