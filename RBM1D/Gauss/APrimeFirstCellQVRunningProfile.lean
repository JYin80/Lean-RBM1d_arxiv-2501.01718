/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSourceSupport
import RBM1D.Gauss.APrimeFirstCellJGCap
import RBM1D.Gauss.APrimeJGWidened

/-!
# T399: actual uncut QV profile on running first-cell active support

The source and the running block cap are taken from the same T395 event.
The endpoint is fixed at `v=1/2` and the normalization is the actual
`driftScale` of `qvAt_full_absorbed`.
-/

namespace RBM.APrimeFirstCellQVRunningProfile

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

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

/-- T334's deterministic scale and logarithmic premises hold uniformly over
the entire Gaussian first half-cell. -/
theorem eventually_running_scales :
    ∀ᶠ N : ℕ in atTop, ∀ r ∈ Set.Icc (0 : ℝ) (1 / 2),
      Real.exp 1 ≤ (d.W N : ℝ) ∧
      4 ≤ Real.log (d.W N : ℝ) ∧
      (4 * (60 : ℝ)) ^ 2 ≤ Real.log (d.W N : ℝ) ∧
      1 ≤ (N : ℝ) ∧
      (N : ℝ)⁻¹ ≤ etaT 0 r ∧
      1 ≤ (d.W N : ℝ) * B.ell N r * etaT 0 r ∧
      (d.W N : ℝ) * B.ell N r * etaT 0 r ≤ N ∧
      (d.W N : ℝ) * (d.L N : ℝ) ≤ N ∧
      (N : ℝ) ≤ (d.W N : ℝ) ^ 2 := by
  filter_upwards [APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    eventually_ge_atTop 2] with N hsc hN r hr
  obtain ⟨hW, hlog4, hlog, hN1, _, _, _, hWL, hNW⟩ := hsc
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hL3 : (3 : ℝ) ≤ d.L N := by exact_mod_cast d.three_le_L N
  have hWN : (d.W N : ℝ) ≤ N := by
    nlinarith [mul_nonneg (le_of_lt hWpos)
      (show (0 : ℝ) ≤ (d.L N : ℝ) - 1 by linarith)]
  have hW2 : (2 : ℝ) ≤ d.W N := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact he.trans hW
  have hη : etaT 0 r = 1 - r := by
    norm_num [etaT, Gauss.mE_zero]
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 r := by
    rw [hη]
    linarith [hr.2]
  have hηN : (N : ℝ)⁻¹ ≤ etaT 0 r := by
    have hi : (N : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [← one_div]
      exact (div_le_iff₀ (by linarith : (0 : ℝ) < N)).2 (by linarith)
    linarith
  have hℓ : 1 ≤ B.ell N r :=
    one_le_ellHat (d.L N) (d.three_le_L N) hr.1 (by linarith [hr.2])
  have hA1 : 1 ≤ (d.W N : ℝ) * B.ell N r * etaT 0 r := by
    calc
      (1 : ℝ) = 2 * 1 * (1 / 2) := by norm_num
      _ ≤ (d.W N : ℝ) * B.ell N r * etaT 0 r := by
        gcongr
  have hηℓ : etaT 0 r * B.ell N r ≤ 1 := by
    exact etaT_mul_ellHat_le (L := d.L N) (d.three_le_L N)
      (by norm_num : |(0 : ℝ)| ≤ 2)
      hr.1 (by linarith [hr.2])
  have hAN : (d.W N : ℝ) * B.ell N r * etaT 0 r ≤ N := by
    calc
      _ = (d.W N : ℝ) * (etaT 0 r * B.ell N r) := by ring
      _ ≤ (d.W N : ℝ) * 1 := mul_le_mul_of_nonneg_left hηℓ hWpos.le
      _ = (d.W N : ℝ) := by ring
      _ ≤ N := hWN
  exact ⟨hW, hlog4, hlog, hN1, hηN, hA1, hAN, hWL, hNW⟩

/-- T334's full uncut profile, with its near term, quadratic and cubic far
terms, spatial leakage, and fixed endpoint normalization left intact. -/
def profileAt (ζ : ℝ) (N : ℕ) (ω : Ω d) (r : ℝ)
    (a : LoopArg (d.L N) 2) : Prop :=
  APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2) r ω ≤
    ((APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2))⁻¹ *
      APrimeFullQV.rootProfile B 0 N r (1 / 2) 60
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeSupportRunning.jG N r ω)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N r)
        ((d.W N : ℝ)⁻¹) a) ^ 2

/-- Numerical inputs needed by the uncut T334 profile at one running time.
They are stated explicitly at this checkpoint, before uniform discharge. -/
theorem qvAt_on_joint_of_scales {τ' ζ : ℝ} (hτ' : 0 < τ')
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
    profileAt ζ N ω r a := by
  have hrmem := running_mem_firstCell hτ' hk hr
  let u : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨r, hrmem⟩
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (by exact_mod_cast hN) u hω.1
  have hell : 0 < APrimeFirstCellSourceAllTime.ellSource ζ N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hJcap : APrimeSupportRunning.jG N r ω ≤ (N : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := hcap
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have huv : r ≤ (1 / 2 : ℝ) :=
    hrmem.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  change APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2) r ω ≤ _
  exact APrimeFullQV.qvAt_full_absorbed d (E := 0) (D := 60)
    (s := 0) (u := r) (v := 1 / 2)
    (by norm_num) hr.1 hr.1 huv (by norm_num)
    N ω a hsource hell (by norm_num) hW hlog4 hlog hN heta hAu hAN
    hWL hNW hJcap

/-- The quadratic far row, cubic inverse-scale row, and cubic spatial
leakage remain separate after the support cap is inserted. -/
theorem diagFarRate_cap_rows (ζ : ℝ) (N : ℕ) (r : ℝ) :
    APrimeQVEndpoint.diagFarRate B N (B.ell N r) (etaT 0 r) 60
        ((N : ℝ) ^ ((1 : ℝ) / 8))
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) =
      2 * (etaT 0 r)⁻¹ *
        (Lemma57.cFar2 (B.W N : ℝ) (B.ell N r) *
          (4 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 *
            (((B.W N : ℝ) * B.ell N r * etaT 0 r) *
              (2 * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r)))) +
          576 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 *
            ((B.W N : ℝ) * B.ell N r * etaT 0 r)⁻¹) +
        32 * (B.W N : ℝ) * (B.L N : ℝ) *
          (B.W N : ℝ) ^ (-(60 : ℝ)) *
          ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 := by
  unfold APrimeQVEndpoint.diagFarRate
  ring

theorem diagFarRate_le_cap_rows {ζ : ℝ} {N : ℕ} {r : ℝ} {ω : Ω d}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcap : APrimeSupportRunning.jG N r ω ≤
      (N : ℝ) ^ ((1 : ℝ) / 8)) :
    APrimeQVEndpoint.diagFarRate B N (B.ell N r) (etaT 0 r) 60
        (APrimeSupportRunning.jG N r ω)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) ≤
      2 * (etaT 0 r)⁻¹ *
        (Lemma57.cFar2 (B.W N : ℝ) (B.ell N r) *
          (4 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 *
            (((B.W N : ℝ) * B.ell N r * etaT 0 r) *
              (2 * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r)))) +
          576 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 *
            ((B.W N : ℝ) * B.ell N r * etaT 0 r)⁻¹) +
        32 * (B.W N : ℝ) * (B.L N : ℝ) *
          (B.W N : ℝ) ^ (-(60 : ℝ)) *
          ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 := by
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast (B.one_le_W N)
  have hℓ : 0 < B.ell N r := by
    have hh := one_le_ellHat (d.L N) (d.three_le_L N) hr0 hr1
    change 1 ≤ B.ell N r at hh
    linarith
  have hη : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hJ0 : 0 ≤ APrimeSupportRunning.jG N r ω := by
    have hh : 1 ≤ APrimeSupportRunning.jG N r ω :=
      APrimeJG.one_le_jG (sample d) 0 N r ω
      (by exact_mod_cast d.W_pos N)
    exact hh.trans' (by norm_num)
  exact (APrimeJGWidened.diagFarRate_mono hW hℓ hη hJ0 hcap).trans_eq
    (diagFarRate_cap_rows ζ N r)

def farRowsBound (ζ : ℝ) (N : ℕ) (ω : Ω d) (r : ℝ) : Prop :=
  APrimeQVEndpoint.diagFarRate B N (B.ell N r) (etaT 0 r) 60
      (APrimeSupportRunning.jG N r ω)
      (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) ≤
    2 * (etaT 0 r)⁻¹ *
      (Lemma57.cFar2 (B.W N : ℝ) (B.ell N r) *
        (4 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 *
          (((B.W N : ℝ) * B.ell N r * etaT 0 r) *
            (2 * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N r)))) +
        576 * ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 *
          ((B.W N : ℝ) * B.ell N r * etaT 0 r)⁻¹) +
      32 * (B.W N : ℝ) * (B.L N : ℝ) *
        (B.W N : ℝ) ^ (-(60 : ℝ)) *
        ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 3

/-- On T395's event, every positive active prefix supports T334's actual
pointwise profile at every running time up to its net endpoint. -/
theorem eventually_running_profile {τ' ζ : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100)
          (firstCellT τ') N0 p N k m ω →
        ∀ r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
          APrimeSupportRunning.jG N r ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
          ∀ a : LoopArg (d.L N) 2, profileAt ζ N ω r a := by
  filter_upwards [APrimeFirstCellSourceSupport.eventually_source_and_support_at hτ',
    eventually_running_scales] with N hcons hsc ω hω N0 p k m hN0 hp hm hk1 hk hw r hr
  have hcap := (hcons ω hω).2 N0 p k m hN0 hp hm hk1 hk hw r hr
  have hrmem := running_mem_firstCell hτ' hk hr
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hrmem.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  obtain ⟨hW, hlog4, hlog, hN, heta, hAu, hAN, hWL, hNW⟩ := hsc r hrhalf
  refine ⟨hcap, ?_⟩
  intro a
  exact qvAt_on_joint_of_scales hτ' hN hω hk hr
    hW hlog4 hlog heta hAu hAN hWL hNW hcap a

theorem eventually_running_far_rows {τ' ζ : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100)
          (firstCellT τ') N0 p N k m ω →
        ∀ r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
          farRowsBound ζ N ω r := by
  filter_upwards [eventually_running_profile hτ'] with
    N hprof ω hω N0 p k m hN0 hp hm hk1 hk hw r hr
  have hcap := (hprof ω hω N0 p k m hN0 hp hm hk1 hk hw r hr).1
  have hrmem := running_mem_firstCell hτ' hk hr
  have hr1 : r < 1 :=
    (hrmem.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2).trans_lt
      (by norm_num)
  exact diagFarRate_le_cap_rows hr.1 hr1 hcap

private theorem grid_two_eq (N : ℕ) (hN : 1 ≤ N) :
    cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2 =
      2 * (N : ℝ) ^ (-(248 : ℝ)) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmesh : APrimeSmoothTransition.transitionMesh N = (N : ℝ) ^ (248 : ℕ) := by
    simp [APrimeSmoothTransition.transitionMesh, max_eq_right hn]
  simp only [cutNetPt, Nat.cast_ofNat, zero_add]
  rw [hmesh, Real.rpow_neg (Nat.cast_nonneg N)]
  norm_num [Real.rpow_natCast, div_eq_mul_inv]

/-- A nonvacuous joint-event witness at the first positive active prefix.
Both positive grid times carry the actual source; the full profile and sharp
block cap hold at every time through the second point. -/
def positiveProfilePlateau (τ' ζ : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
    ∃ u1 u2 : TimeIcc (firstCellS τ') (firstCellT τ') N,
      0 < (u1 : ℝ) ∧
      (u1 : ℝ) = (N : ℝ) ^ (-(248 : ℝ)) ∧
      (u2 : ℝ) = 2 * (N : ℝ) ^ (-(248 : ℝ)) ∧
      (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
        (firstCellT τ') 2 p N 2 N ω = 1) ∧
      APrimeFullQV.SourceEvent (sample d) 0 N (u1 : ℝ) ω
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N u1) ∧
      APrimeFullQV.SourceEvent (sample d) 0 N (u2 : ℝ) ω
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N u2) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) (u2 : ℝ),
        APrimeSupportRunning.jG N r ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
        ∀ a : LoopArg (d.L N) 2, profileAt ζ N ω r a

theorem positiveProfilePlateau_of_joint {τ' ζ : ℝ} (hτ' : 0 < τ')
    (hp : HighProb (P d) (APrimeFirstCellSourceSupport.jointEvent τ' ζ))
    (hpositive : APrimeFirstCellSourceSupport.positivePlateau τ' ζ) :
    positiveProfilePlateau τ' ζ := by
  have hg : HighProb (P d) (APrimeSupportRunning.good τ' (1 / 100)) :=
    hp.mono (Eventually.of_forall fun N => Set.inter_subset_right)
  filter_upwards [hpositive, eventually_running_profile hτ',
    APrimeSupportRunning.positive_plateau_on_good hτ'
      (by norm_num : (0 : ℝ) < 1 / 100) hg,
    eventually_ge_atTop 2] with N hpos hprof hplat hN
  obtain ⟨ω, hω, u1, u2, hu1pos, hu1eq, hu2eq, hw, hsource1,
    hsource2, _⟩ := hpos
  obtain ⟨_, _, _, _, hk, _⟩ := hplat
  have hgrid : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2 =
      (u2 : ℝ) := by
    rw [grid_two_eq N (by omega), hu2eq]
  refine ⟨ω, hω, u1, u2, hu1pos, hu1eq, hu2eq, hw,
    hsource1, hsource2, ?_⟩
  intro r hr
  have hr' : r ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2) := by
    simpa only [hgrid] using hr
  exact hprof ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hw 1]; norm_num) r hr'

/-- The T395 one-parameter HighProb event supports the full uncut profile
on an actual positive-time active prefix of the same sample. -/
theorem exists_running_profile_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      (∀ N, MeasurableSet (APrimeFirstCellSourceSupport.jointEvent τ' ζ N)) ∧
      HighProb (P d) (APrimeFirstCellSourceSupport.jointEvent τ' ζ) ∧
      positiveProfilePlateau τ' ζ := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSourceSupport.exists_jointEvent_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  obtain ⟨hmeas, hp, _, _, hpositive⟩ := hall ζ hζ
  exact ⟨hmeas, hp, positiveProfilePlateau_of_joint hτ' hp hpositive⟩

#print axioms eventually_running_scales
#print axioms qvAt_on_joint_of_scales
#print axioms diagFarRate_cap_rows
#print axioms diagFarRate_le_cap_rows
#print axioms eventually_running_profile
#print axioms eventually_running_far_rows
#print axioms positiveProfilePlateau_of_joint
#print axioms exists_running_profile_with_plateau

end RBM.APrimeFirstCellQVRunningProfile
