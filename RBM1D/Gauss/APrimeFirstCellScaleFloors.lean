/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellLoopCap

/-!
# T458: deterministic moving first-cell scale floors

The polynomial and ratio floors are proved separately for every actual
moving first-cell endpoint.  They are inputs for later row absorption.
-/

namespace RBM.APrimeFirstCellScaleFloors

open Filter Set Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The complete deterministic scale package at one actual first-cell mesh
point.  The two lower bounds on `endpointScale` are separate fields. -/
structure ScalePackage (τ' : ℝ) (N k : ℕ) : Prop where
  resident : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
    APrimeSmoothTransition.transitionMesh N
  time_nonneg : 0 ≤ cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  time_le_half : cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k ≤ 1 / 2
  scale_pos : 0 < APrimeFirstCellLoopCap.endpointScale N
    (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
  n_half_le_scale : (N : ℝ) ^ (1 / 2 : ℝ) ≤
    APrimeFirstCellLoopCap.endpointScale N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
  one_le_ratio : 1 ≤ APrimeFirstCellLoopCap.xRate
    (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
  ratio_le_two : APrimeFirstCellLoopCap.xRate
    (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) ≤ 2
  ratio_pow_thirty_le_scale :
    APrimeFirstCellLoopCap.xRate
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) ^
        (30 : ℕ) ≤
      APrimeFirstCellLoopCap.endpointScale N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)

/-- The pointwise scale package from the bandwidth and the two numerical
power thresholds. -/
theorem scalePackage_of_bounds {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hN : 1 ≤ N)
    (hW : (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤ (d.W N : ℝ))
    (hN8 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
    (hN30 : (2 : ℝ) ^ (30 : ℕ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2))
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    ScalePackage τ' N k := by
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 := hv.2.trans ht.2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hηeq : etaT 0 v = 1 - v := by
    norm_num [etaT, mE_zero]
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 v := by
    rw [hηeq]
    linarith
  have hηone : etaT 0 v ≤ 1 := by
    rw [hηeq]
    linarith [hv.1]
  have hηpos : 0 < etaT 0 v := lt_of_lt_of_le (by norm_num) hηhalf
  have hell : (1 : ℝ) ≤ B.ell N v :=
    one_le_ellHat (d.L N) (d.three_le_L N) hv.1 hv1
  have hell0 : 0 ≤ B.ell N v := zero_le_one.trans hell
  have hW0 : (0 : ℝ) ≤ (d.W N : ℝ) := by positivity
  have hApos : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
    B.scale_pos' (by norm_num) N hv.1 hv1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have htwoN : 2 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (d.W N : ℝ) := by
    calc
      2 * (N : ℝ) ^ ((1 : ℝ) / 2) =
          (N : ℝ) ^ ((1 : ℝ) / 2) * 2 := by ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) *
          (N : ℝ) ^ ((1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left hN8 (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
        (Real.rpow_add hNpos _ _).symm
      _ ≤ (d.W N : ℝ) := hW
  have hNhalfW : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (d.W N : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    simpa only [mul_comm] using htwoN
  have hWell : (d.W N : ℝ) ≤ (d.W N : ℝ) * B.ell N v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hell hW0
  have hWhalfA : (d.W N : ℝ) / 2 ≤
      APrimeFirstCellLoopCap.endpointScale N v := by
    change (d.W N : ℝ) / 2 ≤ (d.W N : ℝ) * B.ell N v * etaT 0 v
    calc
      (d.W N : ℝ) / 2 ≤ ((d.W N : ℝ) * B.ell N v) / 2 :=
        div_le_div_of_nonneg_right hWell (by norm_num)
      _ = ((d.W N : ℝ) * B.ell N v) * (1 / 2 : ℝ) := by ring
      _ ≤ (d.W N : ℝ) * B.ell N v * etaT 0 v :=
        mul_le_mul_of_nonneg_left hηhalf (mul_nonneg hW0 hell0)
  have hNhalfA : (N : ℝ) ^ ((1 : ℝ) / 2) ≤
      APrimeFirstCellLoopCap.endpointScale N v := hNhalfW.trans hWhalfA
  have hηzero : etaT 0 0 = 1 := by
    norm_num [etaT, mE_zero]
  have hR1 : 1 ≤ APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    rw [hηzero]
    exact (le_div_iff₀ hηpos).2 (by simpa using hηone)
  have hR2 : APrimeFirstCellLoopCap.xRate v ≤ 2 := by
    unfold APrimeFirstCellLoopCap.xRate
    rw [hηzero]
    exact (div_le_iff₀ hηpos).2 (by nlinarith [hηhalf])
  have hR30 : APrimeFirstCellLoopCap.xRate v ^ (30 : ℕ) ≤
      APrimeFirstCellLoopCap.endpointScale N v := by
    calc
      APrimeFirstCellLoopCap.xRate v ^ (30 : ℕ) ≤ (2 : ℝ) ^ (30 : ℕ) :=
        pow_le_pow_left₀ (zero_le_one.trans hR1) hR2 30
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := hN30
      _ ≤ APrimeFirstCellLoopCap.endpointScale N v := hNhalfA
  exact {
    resident := hk
    time_nonneg := hv.1
    time_le_half := hvhalf
    scale_pos := hApos
    n_half_le_scale := hNhalfA
    one_le_ratio := hR1
    ratio_le_two := hR2
    ratio_pow_thirty_le_scale := hR30
  }

/-- Uniform deterministic scale package over every actual moving first-cell
mesh point. -/
theorem eventually_scalePackage {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ScalePackage τ' N k := by
  have hN8 : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
    eventually_le_rpow 2 (by norm_num)
  have hN30 : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ (30 : ℕ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop ((2 : ℝ) ^ (30 : ℕ))
  filter_upwards [Dims.bandwidth_grow, hN8, hN30,
    eventually_ge_atTop 1] with N hW h8 h30 hN
  intro k hk
  have hW' : (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤ (d.W N : ℝ) := by
    simpa [d, Dims.exampleGrow_W] using hW
  exact scalePackage_of_bounds hτ' hN hW' h8 h30 hk

/-- The zeroth mesh point is exactly time zero and carries the same package. -/
theorem eventually_zero_scalePackage {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      ScalePackage τ' N 0 ∧
        cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0 = 0 := by
  filter_upwards [eventually_scalePackage hτ'] with N hN
  exact ⟨hN 0 (Nat.zero_le _), by simp only [cutNetPt_zero]⟩

/-- A strictly positive actual `k=2` endpoint carries the deterministic scale
package. -/
theorem eventually_positive_two_scalePackage {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧ ScalePackage τ' N 2 := by
  filter_upwards [eventually_scalePackage hτ',
    APrimeSmoothTransition.eventually_exampleGrow_transition hτ'
      (by norm_num : (0 : ℝ) < 1 / 100)
      (by norm_num : (1 / 100 : ℝ) < 1 / 4)] with N hpack hgeometry
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hvpos : 0 < v := by
    dsimp only [v]
    simp only [cutNetPt, zero_add, Nat.cast_ofNat]
    exact div_pos (by norm_num) (APrimeSupportRunning.mesh_pos N)
  exact ⟨hvpos, hpack 2 hgeometry.2.1⟩

#print axioms scalePackage_of_bounds
#print axioms eventually_scalePackage
#print axioms eventually_zero_scalePackage
#print axioms eventually_positive_two_scalePackage

end RBM.APrimeFirstCellScaleFloors
