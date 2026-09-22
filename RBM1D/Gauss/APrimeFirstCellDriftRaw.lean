/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGAllOutputRunning

/-!
# T422: actual raw two-term first-cell drift bound

The literal `eGpm` output from T418 is combined with the deterministic
quadratic gluing estimate (5.34).  The running `Step2.jS` and the `W⁻⁶⁰`
floor are retained without absorption.
-/

namespace RBM.APrimeFirstCellDriftRaw

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The literal quadratic gluing summand in the length-two `(+,-)` drift. -/
noncomputable def quadGlue (N : ℕ) (r : ℝ) (ω : Ω d)
    (a₁ a₂ : ZMod ((band d).L N)) : ℂ :=
  Step2.eLL ((band d).L N) ((band d).W N)
    (Step2.lk (sample d) 0 N r ω) ![a₁, a₂]

/-- The unabsorbed pointwise right side of (5.34), with the actual running
`J_r = Step2.jS` and the literal `D=60` spatial floor. -/
noncomputable def quadProfile (N : ℕ) (r : ℝ) (ω : Ω d)
    (a₁ a₂ : ZMod ((band d).L N)) : ℝ :=
  Real.exp 1 * (Step2.jS (sample d) 0 60 N r ω) ^ 2 *
    (36 * ((etaT 0 r)⁻¹ *
      (((band d).W N : ℝ) * (band d).ell N r * etaT 0 r)⁻¹) +
      ((band d).W N : ℝ) * ((band d).L N : ℝ) *
        ((band d).W N : ℝ) ^ (-(60 : ℝ))) *
    tailT ((band d).W N : ℝ) ((band d).ell N r) (etaT 0 r) 60
      (zdist ((band d).L N) (a₂ - a₁))

noncomputable def eGpmProfile (ν : ℝ) (N : ℕ) (r : ℝ)
    (a₁ a₂ : ZMod ((band d).L N)) : ℝ :=
  (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
    ((band d).ell N r / (band d).ell N 0) ^ 3 *
      tailT ((band d).W N : ℝ) ((band d).ell N r) (etaT 0 r) 60
        (zdist ((band d).L N) (a₂ - a₁))

noncomputable def driftProfile (ν : ℝ) (N : ℕ) (r : ℝ) (ω : Ω d)
    (a₁ a₂ : ZMod ((band d).L N)) : ℝ :=
  eGpmProfile ν N r a₁ a₂ + quadProfile N r ω a₁ a₂

/-- The quadratic part is a deterministic all-sample estimate. -/
theorem norm_quadGlue_le (N : ℕ) (r : ℝ) (ω : Ω d)
    (a₁ a₂ : ZMod ((band d).L N)) (hr : r ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ‖quadGlue N r ω a₁ a₂‖ ≤ quadProfile N r ω a₁ a₂ := by
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hr1 : r < 1 := hr.2.trans_lt (by norm_num)
  have hEll : 1 ≤ (band d).ell N r :=
    one_le_ellHat_of_nonneg (by
      change 1 ≤ d.L N
      exact (show 1 ≤ d.L N by have := d.three_le_L N; omega))
      hr.1 hr1
  have hEta : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hbase := Step2.norm_eLL_le (L := (band d).L N) (d.three_le_L N)
    (W := ((band d).W N : ℝ)) (ℓu := (band d).ell N r) (ηu := etaT 0 r)
    hW hEll hEta 60 (Step2.lk (sample d) 0 N r ω) ![a₁, a₂]
  simpa only [quadProfile, Step2.jS, Matrix.cons_val_zero,
    Matrix.cons_val_one, Lemma57.zdist_sub_comm, quadGlue] using hbase

def rawDriftBound (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
      ∀ a₁ a₂ : ZMod ((band d).L N),
        ‖DriftDef.driftF (band d) 0 N r ((sample d).H N r ω)
            ![true, false] ![a₁, a₂]‖ ≤
          driftProfile ν N r ω a₁ a₂

/-- The actual full raw drift is bounded by the exact sum of T418's linear
profile and the unabsorbed quadratic (5.34) profile. -/
theorem eventually_raw_drift_on_active_support {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν) : rawDriftBound τ' δ ν := by
  filter_upwards [
    APrimeFirstCellEGAllOutputRunning.eventually_all_output_on_active_support
      hτ' hδ hδ100 hν] with N hall
  intro ω hω N0 p k m hN0 hp hm hk hkT hw r hr a₁ a₂
  have heg := hall ω hω N0 p k m hN0 hp hm hk hkT hw r hr a₁ a₂
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans htop.2 |>.trans
      (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  have hquad := norm_quadGlue_le N r ω a₁ a₂ hrhalf
  rw [DriftDef.driftF_zero_eq_eGpm_add_quadGlue,
    Step2FarInputs.quadGlue_pm_eq_eLL]
  change ‖EGDef.eGpm ((band d).L N) ((band d).W N) (mSigma 0)
      ((sample d).H N r ω) (zt 0 r) a₁ a₂ + quadGlue N r ω a₁ a₂‖ ≤
    driftProfile ν N r ω a₁ a₂
  unfold driftProfile
  exact (norm_add_le _ _).trans (add_le_add heg hquad)

/-- The same positive `k=2` resident from T418 also witnesses the complete
raw drift estimate at its positive time. -/
def positiveRawDriftPlateau (τ' δ ν : ℝ) : Prop :=
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
    ∀ a₁ a₂ : ZMod ((band d).L N),
      ‖DriftDef.driftF (band d) 0 N u2 ((sample d).H N u2 ω)
          ![true, false] ![a₁, a₂]‖ ≤
        driftProfile ν N u2 ω a₁ a₂

theorem positiveRawDriftPlateau_of_all_output {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν)
    (hplat : APrimeFirstCellEGAllOutputRunning.positiveAllOutputPlateau
      τ' δ ν) : positiveRawDriftPlateau τ' δ ν := by
  filter_upwards [hplat,
    eventually_raw_drift_on_active_support hτ' hδ hδ100 hν,
    eventually_ge_atTop 2] with N hplat hraw hN
  dsimp only [APrimeFirstCellEGAllOutputRunning.positiveAllOutputPlateau]
    at hplat
  obtain ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, _hall⟩ := hplat
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hbound : ∀ a₁ a₂ : ZMod ((band d).L N),
      ‖DriftDef.driftF (band d) 0 N u2 ((sample d).H N u2 ω)
          ![true, false] ![a₁, a₂]‖ ≤
        driftProfile ν N u2 ω a₁ a₂ := by
    intro a₁ a₂
    exact hraw ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hk (by rw [hwδ 1]; norm_num) u2
      ⟨hu2pos.le, le_rfl⟩ a₁ a₂
  exact ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, hbound⟩

theorem exists_good_with_raw_drift :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellEGAllOutputRunning.good τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellEGAllOutputRunning.good τ' δ ν) ∧
        rawDriftBound τ' δ ν ∧
        positiveRawDriftPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hgood⟩ :=
    APrimeFirstCellEGAllOutputRunning.exists_good_with_all_output
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hall, hplat⟩ := hgood δ hδ hδ100 ν hν
  exact ⟨hmeas, hp,
    eventually_raw_drift_on_active_support hτ' hδ hδ100 hν,
    positiveRawDriftPlateau_of_all_output hτ' hδ hδ100 hν hplat⟩

#print axioms norm_quadGlue_le
#print axioms eventually_raw_drift_on_active_support
#print axioms positiveRawDriftPlateau_of_all_output
#print axioms exists_good_with_raw_drift

end RBM.APrimeFirstCellDriftRaw
