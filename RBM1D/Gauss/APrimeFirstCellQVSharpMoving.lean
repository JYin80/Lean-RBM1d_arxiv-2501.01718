/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSharpCommonEvent
import RBM1D.Gauss.APrimeFirstCellQVMovingProfile

/-!
# T436: sharp same-event moving QV adapter

T434's literal sharp/common intersection supplies both the running source
event and the all-real-time block cap.  T415's deterministic scale ledger
then feeds the full uncut moving-endpoint QV theorem without changing any
row of its root profile.
-/

namespace RBM.APrimeFirstCellQVSharpMoving

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- T415's full uncut moving profile with T418's exact source loss. -/
def sharpMovingProfileAt (ν : ℝ) (N : ℕ) (ω : Ω d) (v r : ℝ)
    (a : LoopArg (d.L N) 2) : Prop :=
  APrimeFirstCellQVMovingProfile.movingProfileAt
    (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N ω v r a

private theorem running_mem_firstCell {τ' : ℝ} (hτ' : 0 < τ')
    {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    r ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  rw [APrimeSupportRunning.firstS_eq]
  exact ⟨hr.1, hr.2.trans htop.2⟩

private theorem endpoint_mem_firstCell {τ' : ℝ} (hτ' : 0 < τ')
    {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k ∈
      Set.Icc (0 : ℝ) (firstCellT τ' N) := by
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  exact MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)

private theorem endpoint_pos {N k : ℕ} (hk : 1 ≤ k) :
    0 < cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k := by
  simp only [cutNetPt, zero_add]
  exact div_pos (by exact_mod_cast hk) (APrimeSupportRunning.mesh_pos N)

/-- The deterministic full-QV call at the literal moving endpoint.  The
source and sharp block cap are projections of one T434 resident. -/
theorem qvAt_on_sharp_moving_of_scales {τ' δ ν : ℝ} (hτ' : 0 < τ')
    {N k : ℕ} {ω : Ω d}
    (hN2 : (2 : ℝ) ≤ N)
    (hω : ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k))
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log (d.W N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT 0 r)
    (hAu : 1 ≤ (d.W N : ℝ) * B.ell N r * etaT 0 r)
    (hAN : (d.W N : ℝ) * B.ell N r * etaT 0 r ≤ N)
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2)
    (hcap : APrimeSupportRunning.jG N r ω ≤ 2)
    (a : LoopArg (d.L N) 2) :
    sharpMovingProfileAt ν N ω
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r a := by
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
  have hrmem := running_mem_firstCell hτ' hk hr
  let u : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨r, hrmem⟩
  have hcommon : ω ∈ APrimeFirstCellMovingSupport.commonEvent τ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) (δ / 16) N := hω.2
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (show 0 < N by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hN2))
    u (APrimeFirstCellMovingSupport.commonEvent_to_source hcommon)
  have hell : 0 < APrimeFirstCellSourceAllTime.ellSource
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hvhalf : v ≤ (1 / 2 : ℝ) :=
    (endpoint_mem_firstCell hτ' hk).2.trans
      (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hN : (1 : ℝ) ≤ N := by linarith
  have hJcap : APrimeSupportRunning.jG N r ω ≤ (N : ℝ) :=
    hcap.trans hN2
  change APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤ _
  exact APrimeFullQV.qvAt_full_absorbed d (E := 0) (D := 60)
    (s := 0) (u := r) (v := v)
    (by norm_num) hr.1 hr.1 hr.2 hv1 N ω a hsource hell
    (by norm_num) hW hlog4 hlog hN heta hAu hAN hWL hNW hJcap

/-- Every actual positive-`δ` active prefix on the T434 event carries both
the all-real-time sharp block cap and T415's full uncut moving profile. -/
def sharpRunningMovingProfile (τ' δ ν : ℝ) : Prop :=
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
          APrimeSupportRunning.jG N r ω ≤ 2 ∧
            ∀ a : LoopArg (d.L N) 2,
              sharpMovingProfileAt ν N ω v r a

theorem eventually_sharp_running_moving_profile {τ' δ ν : ℝ}
    (hτ' : 0 < τ') : sharpRunningMovingProfile τ' δ ν := by
  filter_upwards [APrimeFirstCellQVRunningProfile.eventually_running_scales,
    APrimeFirstCellCTDecay.eventually_all_time_jG_le_two_on_good,
    eventually_ge_atTop 2] with N hsc hsharp hN2
  intro ω hω N0 p k m hN0 hp hm hk1 hk _hw
  dsimp only
  have hv := endpoint_mem_firstCell hτ' hk
  have hvhalf := hv.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hJall : ∀ q ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N q ω ≤ 2 := hsharp ω hω.1
  refine ⟨endpoint_pos hk1, hv.2, hvhalf, hJall, ?_⟩
  intro r hr
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans hvhalf⟩
  have hcap := hJall r hrhalf
  obtain ⟨hW, hlog4, hlog, _hN, heta, hAu, hAN, hWL, hNW⟩ :=
    hsc r hrhalf
  refine ⟨hcap, ?_⟩
  intro a
  exact qvAt_on_sharp_moving_of_scales hτ'
    (by exact_mod_cast hN2) hω hk hr hW hlog4 hlog heta hAu hAN hWL hNW hcap a

/-- The T434 positive `k = 2` resident also carries the sharp moving QV
profile at every preceding real time, including both endpoints explicitly. -/
def positiveSharpMovingProfilePlateau (τ' δ ν : ℝ) : Prop :=
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
      APrimeSupportRunning.jG N r ω ≤ 2 ∧
        ∀ a : LoopArg (d.L N) 2,
          sharpMovingProfileAt ν N ω v r a) ∧
    APrimeSupportRunning.jG N 0 ω ≤ 2 ∧
    APrimeSupportRunning.jG N v ω ≤ 2 ∧
    (∀ a : LoopArg (d.L N) 2,
      sharpMovingProfileAt ν N ω v 0 a) ∧
    ∀ a : LoopArg (d.L N) 2,
      sharpMovingProfileAt ν N ω v v a

theorem positiveSharpMovingProfilePlateau_of_sharp {τ' δ ν : ℝ}
    (hτ' : 0 < τ')
    (hpositive : APrimeFirstCellSharpCommonEvent.positiveSharpPlateau
      τ' δ ν) :
    positiveSharpMovingProfilePlateau τ' δ ν := by
  filter_upwards [hpositive, eventually_sharp_running_moving_profile hτ',
    eventually_ge_atTop 2] with N hpositive hrun hN
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hpositive
  obtain ⟨ω, hω, hk, hw, hvpos, hvle, hTle, hsource,
    _hJallOld, _hJ0Old, _hJvOld⟩ := hpositive
  have hh := hrun ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hw 1]; norm_num)
  obtain ⟨_hvpos, _hvle, _hvhalf, hJall, hprof⟩ := hh
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hvhalf : v ≤ (1 / 2 : ℝ) := hvle.trans hTle
  have hzero := hprof 0 ⟨le_rfl, hvpos.le⟩
  have hend := hprof v ⟨hvpos.le, le_rfl⟩
  exact ⟨ω, hω, hvpos, hvle, hvhalf, hw, hsource, hJall, hprof,
    hzero.1, hend.1, hzero.2, hend.2⟩

/-- Closed same-event producer with the T418/T434 parameter order. -/
theorem exists_sharp_running_moving_profile_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        sharpRunningMovingProfile τ' δ ν ∧
        positiveSharpMovingProfilePlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_sharp_running_moving_profile hτ',
    positiveSharpMovingProfilePlateau_of_sharp hτ' hpositive⟩

#print axioms sharpMovingProfileAt
#print axioms qvAt_on_sharp_moving_of_scales
#print axioms eventually_sharp_running_moving_profile
#print axioms positiveSharpMovingProfilePlateau_of_sharp
#print axioms exists_sharp_running_moving_profile_with_plateau

end RBM.APrimeFirstCellQVSharpMoving
