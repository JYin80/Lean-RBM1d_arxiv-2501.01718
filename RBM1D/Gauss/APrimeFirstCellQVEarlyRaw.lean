/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVFixedTwo

/-!
# T439: raw early QV on stored first-cell prefixes

At every stored time strictly before an active endpoint, the T434 event
supplies the actual all-time source event.  T334 is applied with its literal
normalization `x = eta(0)/eta(u)` and `Theta = N^(2*delta)`, after which the
actual block parameter is replaced by the sharp constant two.  All three raw
rate rows, including the `W^-60` leakage, remain present.
-/

namespace RBM.APrimeFirstCellQVEarlyRaw

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal normalized T334 bound with the far block slot fixed to two. -/
def fixedTwoEarlyRawAt (δ ν : ℝ) (N : ℕ) (ω : Ω d) (u : ℝ)
    (a : LoopArg (d.L N) 2) : Prop :=
  Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B 0 N u M' Step2.sigPM a)
      ((sample d).H N u ω) /
        (Step2.tT B 0 N 60 u (zdist (d.L N) (a 0 - a 1)) ^ 2 *
          (etaT 0 0 / etaT 0 u) ^ 8 * ((N : ℝ) ^ (2 * δ)) ^ 2) ≤
    (APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeFirstCellSourceAllTime.ellSource
            (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
          (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 2
          (APrimeFirstCellSourceAllTime.sourceC4
            (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u)) /
      ((etaT 0 0 / etaT 0 u) ^ 8 * ((N : ℝ) ^ (2 * δ)) ^ 2)

/-- The source-scale factor in the near row, with its factor two exposed. -/
theorem ell_div_ellSource_pow_five (ν : ℝ) (N : ℕ) (u : ℝ)
    (hN : 0 < (N : ℝ)) :
    (B.ell N u / APrimeFirstCellSourceAllTime.ellSource
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) ^ (5 : ℕ) =
      2 * (N : ℝ) ^ (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) *
        (B.ell N u) ^ (5 : ℕ) := by
  simpa [APrimeFirstCellJGCap.sourceEll,
    APrimeFirstCellSourceAllTime.ellSource] using
    APrimeFirstCellQVSmall.source_near_ratio_fifth N
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) (B.ell N u) hN

/-- At `J=2`, the cubic leakage row is literally `256 W L W^-60`. -/
theorem diagFarRate_two_eq (N : ℕ) (u Smax : ℝ) :
    APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 2 Smax =
      2 * (etaT 0 u)⁻¹ *
          (Lemma57.cFar2 (B.W N : ℝ) (B.ell N u) *
              (16 * (((B.W N : ℝ) * B.ell N u * etaT 0 u) * (2 * √Smax))) +
            72 * 64 * ((B.W N : ℝ) * B.ell N u * etaT 0 u)⁻¹) +
        256 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-60 : ℝ) := by
  unfold APrimeQVEndpoint.diagFarRate
  ring

/-- Deterministic T334 call at one stored time, followed only by monotonicity
of the literal far rate in the actual block parameter. -/
theorem fixedTwoEarlyRawAt_of_scales {τ' δ ν : ℝ} (hτ' : 0 < τ')
    {N k j : ℕ} {ω : Ω d}
    (hN2 : (2 : ℝ) ≤ N)
    (hω : ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hjk : j < k)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log (d.W N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT 0
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))
    (hAu : 1 ≤ (d.W N : ℝ) * B.ell N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
        etaT 0 (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))
    (hAN : (d.W N : ℝ) * B.ell N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
        etaT 0 (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ≤ N)
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2)
    (hcap : APrimeSupportRunning.jG N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ω ≤ 2)
    (a : LoopArg (d.L N) 2) :
    fixedTwoEarlyRawAt δ ν N ω
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) a := by
  let u := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j
  have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N := hjk.le.trans hk
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have huCell := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) u (cutNetPt_mem_netFinset hjtop)
  have huHalf : u ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨huCell.1, huCell.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  have hu1 : u < 1 := huHalf.2.trans_lt (by norm_num)
  let ut : TimeIcc (firstCellS τ') (firstCellT τ') N := by
    refine ⟨u, ?_⟩
    rw [APrimeSupportRunning.firstS_eq]
    exact huCell
  have hcommon : ω ∈ APrimeFirstCellMovingSupport.commonEvent τ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) (δ / 16) N := hω.2
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (show 0 < N by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hN2))
    ut (APrimeFirstCellMovingSupport.commonEvent_to_source hcommon)
  have hell : 0 < APrimeFirstCellSourceAllTime.ellSource
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hJcap : APrimeSupportRunning.jG N u ω ≤ (N : ℝ) := hcap.trans hN2
  have hx : 0 < etaT 0 0 / etaT 0 u := by
    have hηu : 0 < etaT 0 u := Step2.etaT_pos' (by norm_num) hu1
    have hη0 : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
    exact div_pos hη0 hηu
  have hTheta : 0 < (N : ℝ) ^ (2 * δ) := by
    have : (0 : ℝ) < N := by linarith
    exact Real.rpow_pos_of_pos this _
  have hraw := APrimeFullQV.early_normalized_full (sample d)
    (E := 0) (D := 60) (u := u) (by norm_num) huCell.1 hu1 N ω a
    (by simpa only [ut] using hsource) hell (by norm_num) hW hlog4 hlog
    hN1 heta hAu hAN hWL hNW hJcap hx hTheta
  have hℓ : 0 < B.ell N u := by
    have hh := one_le_ellHat (d.L N) (d.three_le_L N) huCell.1 hu1
    change 1 ≤ B.ell N u at hh
    linarith
  have hηu : 0 < etaT 0 u := Step2.etaT_pos' (by norm_num) hu1
  have hJ1 : 1 ≤ APrimeSupportRunning.jG N u ω :=
    APrimeJG.one_le_jG (sample d) 0 N u ω (by exact_mod_cast d.W_pos N)
  have hfar := APrimeJGWidened.diagFarRate_mono
    (B := B) (N := N) (ℓu := B.ell N u) (ηu := etaT 0 u)
    (D := 60) (Smax := APrimeFirstCellSourceAllTime.sourceC4
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u)
    (J := APrimeSupportRunning.jG N u ω) (J' := 2)
    (by exact_mod_cast B.one_le_W N) hℓ hηu (zero_le_one.trans hJ1) hcap
  have hnum :
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60
          (APrimeSupportRunning.jG N u ω)
          (APrimeFirstCellSourceAllTime.sourceC4
            (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u) ≤
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
        (APrimeFirstCellSourceAllTime.ellSource
          (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 2
          (APrimeFirstCellSourceAllTime.sourceC4
            (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u) := by
    exact add_le_add (le_refl _) hfar
  have hden : 0 ≤ (etaT 0 0 / etaT 0 u) ^ 8 *
      ((N : ℝ) ^ (2 * δ)) ^ 2 := by positivity
  unfold fixedTwoEarlyRawAt
  calc
    _ ≤ _ := hraw
    _ ≤ _ := div_le_div_of_nonneg_right hnum hden

/-- Every stored index below an actual positive active prefix carries the
literal early normalized bound, the source event, and the exact near ratio. -/
def earlyRawOnStoredPrefixes (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ j < k,
        let u := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N j
        u ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
        0 < etaT 0 0 / etaT 0 u ∧
        0 < (N : ℝ) ^ (2 * δ) ∧
        APrimeFullQV.SourceEvent (sample d) 0 N u ω
          (APrimeFirstCellSourceAllTime.ellSource
            (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
          (APrimeFirstCellSourceAllTime.sourceC4
            (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u) ∧
        APrimeSupportRunning.jG N u ω ≤ 2 ∧
        (B.ell N u / APrimeFirstCellSourceAllTime.ellSource
          (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) ^ (5 : ℕ) =
          2 * (N : ℝ) ^ (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) *
            (B.ell N u) ^ (5 : ℕ) ∧
        ∀ a : LoopArg (d.L N) 2, fixedTwoEarlyRawAt δ ν N ω u a

theorem eventually_earlyRaw_on_stored_prefixes {τ' δ ν : ℝ}
    (hτ' : 0 < τ') : earlyRawOnStoredPrefixes τ' δ ν := by
  filter_upwards [APrimeFirstCellQVRunningProfile.eventually_running_scales,
    APrimeFirstCellCTDecay.eventually_all_time_jG_le_two_on_good,
    eventually_ge_atTop 2] with N hsc hsharp hN2
  intro ω hω N0 p k m hN0 hp hm hk1 hk _hw j hjk
  dsimp only
  have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N := hjk.le.trans hk
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have huCell := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
  have huHalf : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j ∈
      Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨huCell.1, huCell.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  obtain ⟨hW, hlog4, hlog, _hN1, heta, hAu, hAN, hWL, hNW⟩ :=
    hsc _ huHalf
  have hcap := hsharp ω hω.1 _ huHalf
  have hu1 : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j < 1 :=
    huHalf.2.trans_lt (by norm_num)
  have hx : 0 < etaT 0 0 /
      etaT 0 (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) := by
    have := Step2.etaT_pos' (E := 0) (u := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j) (by norm_num) hu1
    have hη0 : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
    exact div_pos hη0 this
  have hTheta : 0 < (N : ℝ) ^ (2 * δ) := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact Real.rpow_pos_of_pos this _
  let ut : TimeIcc (firstCellS τ') (firstCellT τ') N := by
    refine ⟨cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j, ?_⟩
    rw [APrimeSupportRunning.firstS_eq]
    exact huCell
  have hcommon : ω ∈ APrimeFirstCellMovingSupport.commonEvent τ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) (δ / 16) N := hω.2
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (show 0 < N by omega) ut
      (APrimeFirstCellMovingSupport.commonEvent_to_source hcommon)
  refine ⟨huHalf, hx, hTheta, ?_, hcap,
    ell_div_ellSource_pow_five ν N _ (by positivity), ?_⟩
  · simpa only [ut] using hsource
  · intro a
    exact fixedTwoEarlyRawAt_of_scales hτ' (by exact_mod_cast hN2) hω hk hjk
      hW hlog4 hlog heta hAu hAN hWL hNW hcap a

/-- A same-event `k=2` resident with the positive stored point `j=1`; the
finite initial stored point `j=0` is retained explicitly. -/
def positiveEarlyRawPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    let u0 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0
    let u1 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
    let u2 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
    0 < u1 ∧ u1 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    u0 = 0 ∧
    APrimeFullQV.SourceEvent (sample d) 0 N u0 ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u0) ∧
    APrimeFullQV.SourceEvent (sample d) 0 N u1 ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u1) ∧
    APrimeSupportRunning.jG N u0 ω ≤ 2 ∧
    APrimeSupportRunning.jG N u1 ω ≤ 2 ∧
    (B.ell N u0 / APrimeFirstCellSourceAllTime.ellSource
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) ^ (5 : ℕ) =
      2 * (N : ℝ) ^ (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) *
        (B.ell N u0) ^ (5 : ℕ) ∧
    (B.ell N u1 / APrimeFirstCellSourceAllTime.ellSource
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N) ^ (5 : ℕ) =
      2 * (N : ℝ) ^ (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) *
        (B.ell N u1) ^ (5 : ℕ) ∧
    (∀ a : LoopArg (d.L N) 2, fixedTwoEarlyRawAt δ ν N ω u0 a) ∧
    ∀ a : LoopArg (d.L N) 2, fixedTwoEarlyRawAt δ ν N ω u1 a

theorem positiveEarlyRawPlateau_of_sharp {τ' δ ν : ℝ}
    (hτ' : 0 < τ')
    (hpositive : APrimeFirstCellSharpCommonEvent.positiveSharpPlateau
      τ' δ ν) : positiveEarlyRawPlateau τ' δ ν := by
  filter_upwards [hpositive, eventually_earlyRaw_on_stored_prefixes hτ',
    eventually_ge_atTop 2] with N hpositive hrun hN
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hpositive
  obtain ⟨ω, hω, hk, hw, _hu2pos, hu2le, _hTle, _hsource,
    _hJall, _hJ0, _hJ2⟩ := hpositive
  have hactive := hrun ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hw 1]; norm_num)
  have h0 := hactive 0 (by norm_num)
  have h1 := hactive 1 (by norm_num)
  have hmesh := APrimeSupportRunning.mesh_pos N
  have hu1pos : 0 < cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 1 := by
    simp only [cutNetPt, zero_add]
    positivity
  have hu12 : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1 <
      cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2 := by
    simp only [cutNetPt, zero_add]
    exact (div_lt_div_iff_of_pos_right hmesh).2 (by norm_num)
  have hu0 : cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 = 0 := by
    simp [cutNetPt]
  exact ⟨ω, hω, hu1pos, hu12, hu2le, hw, hu0,
    h0.2.2.2.1, h1.2.2.2.1, h0.2.2.2.2.1,
    h1.2.2.2.2.1, h0.2.2.2.2.2.1, h1.2.2.2.2.2.1,
    h0.2.2.2.2.2.2, h1.2.2.2.2.2.2⟩

/-- Closed T439 producer with the unchanged T434 parameter order. -/
theorem exists_earlyRaw_on_stored_prefixes_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        earlyRawOnStoredPrefixes τ' δ ν ∧
        positiveEarlyRawPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_earlyRaw_on_stored_prefixes hτ',
    positiveEarlyRawPlateau_of_sharp hτ' hpositive⟩

#print axioms ell_div_ellSource_pow_five
#print axioms diagFarRate_two_eq
#print axioms fixedTwoEarlyRawAt_of_scales
#print axioms eventually_earlyRaw_on_stored_prefixes
#print axioms positiveEarlyRawPlateau_of_sharp
#print axioms exists_earlyRaw_on_stored_prefixes_with_plateau

end RBM.APrimeFirstCellQVEarlyRaw
