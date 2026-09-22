/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDriftRaw

/-!
# T430: same-event loop cap and retained spatial floor

This file keeps the loop maximum `Step2.jS` distinct from the block maximum
`APrimeSupportRunning.jG`.  It also pays the literal `W⁻⁶⁰` floor using only
the deterministic first-cell scale inequalities.
-/

namespace RBM.APrimeFirstCellLoopCap

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The first-cell ratio `x_r = η_0 / η_r`. -/
noncomputable def xRate (r : ℝ) : ℝ := etaT 0 0 / etaT 0 r

/-- The explicit constant in the active-support loop cap. -/
noncomputable def loopConstant : ℝ := 16 * (Real.exp 1) ^ 2 + 1

/-- The literal `D=60` spatial floor from (5.34). -/
noncomputable def spatialFloor (N : ℕ) : ℝ :=
  (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-(60 : ℝ))

/-- The endpoint scale `A_v = W ℓ_v η_v`. -/
noncomputable def endpointScale (N : ℕ) (v : ℝ) : ℝ := B.scale 0 N v

def runningLoopCap (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
        Step2.jS (sample d) 0 60 N r ω ≤
          loopConstant * (N : ℝ) ^ (2 * δ) * xRate r ^ 4

/-- On T422's literal common event, positive actual support controls the
running loop maximum through the closed interval, including its endpoint. -/
theorem eventually_running_loop_cap {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) : runningLoopCap τ' δ ν := by
  filter_upwards [APrimeSupportRunning.eventually_running_support
      (δ := δ) (t := firstCellT τ')
      (fun N => (APrimeSupportRunning.firstT_bounds hτ' N).1)
      (fun N => (APrimeSupportRunning.firstT_bounds hτ' N).2),
    eventually_ge_atTop 1] with N hrun hN
  intro ω hω N0 p k m hN0 hp hm hk hkT hw r hr
  have hsupport : ω ∈ APrimeSupportRunning.good τ' (δ / 16) N :=
    APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hω
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) :=
    (APrimeSupportRunning.good_subset τ' (δ / 16) N hsupport).1.1.1
  have hJ := hrun N0 p k m hN0 hp hm hk hkT ω hX hw r hr
  have htop := MomentDuhamelCut.netFinset_subset_Icc
    (APrimeSupportRunning.firstT_bounds hτ' N).1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hrhalf : r ≤ 1 / 2 :=
    hr.2.trans htop.2 |>.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hr1 : r < 1 := hrhalf.trans_lt (by norm_num)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsmall : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (2 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hnorm : APrimeSupportRunning.J N r ω ≤
      loopConstant * (N : ℝ) ^ (2 * δ) := by
    exact hJ.trans (by
      unfold loopConstant
      nlinarith)
  have hraw := APrimeSupportRunning.raw_of_normalized hr1 ω hnorm
  simpa only [xRate, Step2Moment.ratR] using hraw

/-- At time zero the actual loop maximum is exactly one, independently of
the event or cutoff.  This is the separate `k=0` branch. -/
theorem loopJ_zero (N : ℕ) (ω : Ω d) :
    Step2.jS (sample d) 0 60 N 0 ω = 1 := by
  have h : Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N 0 ω = 1 := by
    exact APrimeFirstCellCommon.J_zero N ω
  simpa only [Step2Moment.jSnorm, Step2Moment.ratR, etaT, mE_zero,
    Complex.I_im, mul_one, sub_zero, div_one, one_pow] using h

/-- The running theorem contains both closed-interval boundary values
`r=0` and `r=v=u_k`. -/
theorem eventually_boundary_loop_caps {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight δ (firstCellT τ')
          N0 p N k m ω →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        Step2.jS (sample d) 0 60 N 0 ω ≤
            loopConstant * (N : ℝ) ^ (2 * δ) * xRate 0 ^ 4 ∧
          Step2.jS (sample d) 0 60 N v ω ≤
            loopConstant * (N : ℝ) ^ (2 * δ) * xRate v ^ 4 := by
  filter_upwards [eventually_running_loop_cap hτ' hδ] with N hcap
  intro ω hω N0 p k m hN0 hp hm hk hkT hw
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hv : v ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc hwin
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) v := ⟨le_rfl, hv.1⟩
  have hend : v ∈ Set.Icc (0 : ℝ) v := ⟨hv.1, le_rfl⟩
  exact ⟨hcap ω hω N0 p k m hN0 hp hm hk hkT hw 0 hzero,
    hcap ω hω N0 p k m hN0 hp hm hk hkT hw v hend⟩

def positiveLoopCapPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
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
      Step2.jS (sample d) 0 60 N r ω ≤
        loopConstant * (N : ℝ) ^ (2 * δ) * xRate r ^ 4

/-- T422's positive `k=2` resident carries the loop cap on the same literal
event and for the same sample. -/
theorem positiveLoopCapPlateau_of_raw {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ)
    (hplat : APrimeFirstCellDriftRaw.positiveRawDriftPlateau τ' δ ν) :
    positiveLoopCapPlateau τ' δ ν := by
  filter_upwards [hplat, eventually_running_loop_cap hτ' hδ,
    eventually_ge_atTop 2] with N hplat hcap hN
  dsimp only [APrimeFirstCellDriftRaw.positiveRawDriftPlateau] at hplat
  obtain ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, _hraw⟩ := hplat
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  refine ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, ?_⟩
  intro r hr
  exact hcap ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hwδ 1]; norm_num) r hr

/-- The T422 event, running loop cap, and nondegenerate `k=2` resident use one
literal first-cell parameter and one sample. -/
theorem exists_good_with_loop_cap :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellEGAllOutputRunning.good τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellEGAllOutputRunning.good τ' δ ν) ∧
        runningLoopCap τ' δ ν ∧
        positiveLoopCapPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hgood⟩ :=
    APrimeFirstCellDriftRaw.exists_good_with_raw_drift
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hraw, hplat⟩ := hgood δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_running_loop_cap hτ' hδ,
    positiveLoopCapPlateau_of_raw hτ' hδ hplat⟩

/-- The literal spatial floor is paid by the endpoint scale uniformly over
all real first-cell running times `0 ≤ r ≤ v`. -/
theorem eventually_spatialFloor_le {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ r v : ℝ,
      r ∈ Set.Icc (0 : ℝ) v → v ≤ firstCellT τ' N →
      spatialFloor N ≤ (etaT 0 r)⁻¹ * (endpointScale N v)⁻¹ := by
  filter_upwards [Dims.dim_grow, Step2.eventually_le_W_sq B,
    eventually_ge_atTop 1] with N hdim hNW hN
  intro r v hr hvT
  have hv0 : 0 ≤ v := hr.1.trans hr.2
  have hvhalf : v ≤ 1 / 2 :=
    hvT.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hr1 : r < 1 := hr.2.trans_lt hv1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) := B.one_le_W N
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have hA0 : 0 < endpointScale N v := by
    exact B.scale_pos' (by norm_num) N hv0 hv1
  have hη0 : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hη1 : etaT 0 r ≤ 1 := by
    rw [show etaT 0 r = 1 - r by simp [etaT, mE_zero]]
    linarith [hr.1]
  have hL1 : (1 : ℝ) ≤ d.L N := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hW0 : (0 : ℝ) ≤ d.W N := by positivity
  have hWleN : (d.W N : ℝ) ≤ N := by
    have := mul_le_mul_of_nonneg_left hL1 hW0
    nlinarith
  have hηell := etaT_mul_ellHat_le (L := d.L N) (d.three_le_L N)
    (E := 0) (by norm_num) hv0 hv1
  have hAleW : endpointScale N v ≤ (d.W N : ℝ) := by
    change (d.W N : ℝ) * B.ell N v * etaT 0 v ≤ (d.W N : ℝ)
    calc
      (d.W N : ℝ) * B.ell N v * etaT 0 v =
          (d.W N : ℝ) * (etaT 0 v * B.ell N v) := by ring
      _ ≤ (d.W N : ℝ) * 1 := mul_le_mul_of_nonneg_left hηell hW0
      _ = (d.W N : ℝ) := mul_one _
  have hAN : endpointScale N v ≤ (N : ℝ) := hAleW.trans hWleN
  exact RBM.APrimeFullQV.ExponentRows.leak_paid_by_dims
    hW1 hNr hA0 hη0 hWL hAN hNW hη1
    (by norm_num : (4 : ℝ) ≤ 60)

#print axioms eventually_running_loop_cap
#print axioms loopJ_zero
#print axioms eventually_boundary_loop_caps
#print axioms positiveLoopCapPlateau_of_raw
#print axioms exists_good_with_loop_cap
#print axioms eventually_spatialFloor_le

end RBM.APrimeFirstCellLoopCap
