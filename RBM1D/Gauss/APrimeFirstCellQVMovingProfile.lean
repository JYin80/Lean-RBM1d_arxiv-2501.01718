/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVRunningProfile

/-!
# T415: actual uncut first-cell QV at the moving net endpoint

The right endpoint is the literal active net point.  The full T334 profile is
kept intact: the normalization is `driftScale ... 0 v`, and `rootProfile`
retains its near, quadratic, cubic, and `D = 60` leakage terms.
-/

namespace RBM.APrimeFirstCellQVMovingProfile

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The actual uncut QV profile with an explicit moving right endpoint. -/
def movingProfileAt (ζ : ℝ) (N : ℕ) (ω : Ω d) (v r : ℝ)
    (a : LoopArg (d.L N) 2) : Prop :=
  APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
    ((APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ *
      APrimeFullQV.rootProfile B 0 N r v 60
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeSupportRunning.jG N r ω)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N r)
        ((d.W N : ℝ)⁻¹) a) ^ 2

private theorem running_mem_firstCell {τ' : ℝ} (hτ' : 0 < τ')
    {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    r ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hmesh := APrimeSupportRunning.mesh_pos N
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin hmesh _
    (cutNetPt_mem_netFinset hk)
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

/-- T334 at the literal endpoint `v = u_k`.  All deterministic assumptions
are explicit at this local checkpoint. -/
theorem qvAt_on_joint_moving_of_scales {τ' ζ : ℝ} (hτ' : 0 < τ')
    {N k : ℕ} {ω : Ω d}
    (hN : 1 ≤ (N : ℝ))
    (hω : ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N)
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
    (hcap : APrimeSupportRunning.jG N r ω ≤
      (N : ℝ) ^ ((1 : ℝ) / 8))
    (a : LoopArg (d.L N) 2) :
    movingProfileAt ζ N ω
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r a := by
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
  have hrmem := running_mem_firstCell hτ' hk hr
  let u : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨r, hrmem⟩
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (by exact_mod_cast hN) u hω.1
  have hell : 0 < APrimeFirstCellSourceAllTime.ellSource ζ N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hvhalf : v ≤ (1 / 2 : ℝ) :=
    (endpoint_mem_firstCell hτ' hk).2.trans
      (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hJcap : APrimeSupportRunning.jG N r ω ≤ (N : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := hcap
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  change APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤ _
  exact APrimeFullQV.qvAt_full_absorbed d (E := 0) (D := 60)
    (s := 0) (u := r) (v := v)
    (by norm_num) hr.1 hr.1 hr.2 hv1 N ω a hsource hell
    (by norm_num) hW hlog4 hlog hN heta hAu hAN hWL hNW hJcap

/-- On the same T395 event, every positive active prefix has the full uncut
QV profile at its own moving endpoint and at every real preceding time. -/
theorem eventually_running_moving_profile {τ' ζ : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100)
          (firstCellT τ') N0 p N k m ω →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        0 < v ∧ v ≤ firstCellT τ' N ∧
          ∀ r ∈ Set.Icc (0 : ℝ) v,
            APrimeSupportRunning.jG N r ω ≤
                (N : ℝ) ^ ((1 : ℝ) / 8) ∧
              ∀ a : LoopArg (d.L N) 2, movingProfileAt ζ N ω v r a := by
  filter_upwards [APrimeFirstCellSourceSupport.eventually_source_and_support_at hτ',
    APrimeFirstCellQVRunningProfile.eventually_running_scales] with
    N hcons hsc ω hω N0 p k m hN0 hp hm hk1 hk hw
  dsimp only
  have hv := endpoint_mem_firstCell hτ' hk
  refine ⟨endpoint_pos hk1, hv.2, ?_⟩
  intro r hr
  have hcap := (hcons ω hω).2 N0 p k m hN0 hp hm hk1 hk hw r hr
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans (hv.2.trans
      (APrimeSupportRunning.firstT_bounds hτ' N).2)⟩
  obtain ⟨hW, hlog4, hlog, hN, heta, hAu, hAN, hWL, hNW⟩ :=
    hsc r hrhalf
  refine ⟨hcap, ?_⟩
  intro a
  exact qvAt_on_joint_moving_of_scales hτ' hN hω hk hr
    hW hlog4 hlog heta hAu hAN hWL hNW hcap a

private theorem grid_two_eq (N : ℕ) (hN : 1 ≤ N) :
    cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2 =
      2 * (N : ℝ) ^ (-(248 : ℝ)) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmesh : APrimeSmoothTransition.transitionMesh N =
      (N : ℝ) ^ (248 : ℕ) := by
    simp [APrimeSmoothTransition.transitionMesh, max_eq_right hn]
  simp only [cutNetPt, Nat.cast_ofNat, zero_add]
  rw [hmesh, Real.rpow_neg (Nat.cast_nonneg N)]
  norm_num [Real.rpow_natCast, div_eq_mul_inv]

/-- A same-sample nonvacuity witness at `k=2`, whose moving endpoint is
exactly `2*N^(-248)`. -/
def positiveMovingProfilePlateau (τ' ζ : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
    ∃ v : TimeIcc (firstCellS τ') (firstCellT τ') N,
      0 < (v : ℝ) ∧
      (v : ℝ) = 2 * (N : ℝ) ^ (-(248 : ℝ)) ∧
      (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
        (firstCellT τ') 2 p N 2 N ω = 1) ∧
      APrimeFullQV.SourceEvent (sample d) 0 N (v : ℝ) ω
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N v) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) (v : ℝ),
        APrimeSupportRunning.jG N r ω ≤
            (N : ℝ) ^ ((1 : ℝ) / 8) ∧
          ∀ a : LoopArg (d.L N) 2,
            movingProfileAt ζ N ω (v : ℝ) r a

theorem positiveMovingProfilePlateau_of_joint {τ' ζ : ℝ} (hτ' : 0 < τ')
    (hp : HighProb (P d) (APrimeFirstCellSourceSupport.jointEvent τ' ζ))
    (hpositive : APrimeFirstCellSourceSupport.positivePlateau τ' ζ) :
    positiveMovingProfilePlateau τ' ζ := by
  have hg : HighProb (P d) (APrimeSupportRunning.good τ' (1 / 100)) :=
    hp.mono (Eventually.of_forall fun N => Set.inter_subset_right)
  filter_upwards [hpositive, eventually_running_moving_profile hτ',
    APrimeSupportRunning.positive_plateau_on_good hτ'
      (by norm_num : (0 : ℝ) < 1 / 100) hg,
    eventually_ge_atTop 2] with N hpos hprof hplat hN
  obtain ⟨ω, hω, u1, u2, hu1pos, hu1eq, hu2eq, hw, hsource1,
    hsource2, hJ⟩ := hpos
  obtain ⟨_, _, _, _, hk, _⟩ := hplat
  have hgrid : cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2 = (u2 : ℝ) := by
    rw [grid_two_eq N (by omega), hu2eq]
  have hrun := hprof ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hw 1]; norm_num)
  obtain ⟨hvpos, hvtop, hrun⟩ := hrun
  refine ⟨ω, hω, u2, ?_, hu2eq, hw, hsource2, ?_⟩
  · simpa only [hgrid] using hvpos
  · intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2) := by
      simpa only [hgrid] using hr
    have hh := hrun r hr'
    simpa only [hgrid] using hh

/-- One first-cell parameter is chosen before the source loss; the same event
also contains a positive moving-endpoint profile witness. -/
theorem exists_running_moving_profile_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      (∀ N, MeasurableSet (APrimeFirstCellSourceSupport.jointEvent τ' ζ N)) ∧
      HighProb (P d) (APrimeFirstCellSourceSupport.jointEvent τ' ζ) ∧
      positiveMovingProfilePlateau τ' ζ := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSourceSupport.exists_jointEvent_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  obtain ⟨hmeas, hp, _, _, hpositive⟩ := hall ζ hζ
  exact ⟨hmeas, hp, positiveMovingProfilePlateau_of_joint hτ' hp hpositive⟩

#print axioms movingProfileAt
#print axioms qvAt_on_joint_moving_of_scales
#print axioms eventually_running_moving_profile
#print axioms positiveMovingProfilePlateau_of_joint
#print axioms exists_running_moving_profile_with_plateau

end RBM.APrimeFirstCellQVMovingProfile
