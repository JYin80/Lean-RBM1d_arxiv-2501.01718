/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSourceAllTime
import RBM1D.Gauss.APrimeSupportRunning

/-!
# T395: one first-cell source/support event

The source and support events use the same first-cell grid parameter, while
their two Good thresholds remain distinct. The running `jG` bound is used only
on positive active-prefix support.
-/

namespace RBM.APrimeFirstCellSourceSupport

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

def jointEvent (τ' ζ : ℝ) (N : ℕ) : Set (Ω d) :=
  APrimeFirstCellSourceAllTime.commonEvent τ' ζ N ∩
    APrimeSupportRunning.good τ' (1 / 100) N

theorem measurableSet_jointEvent (τ' ζ : ℝ) (N : ℕ) :
    MeasurableSet (jointEvent τ' ζ N) :=
  (APrimeFirstCellSourceAllTime.commonEvent_measurable τ' ζ N).inter
    (APrimeSupportRunning.measurableSet_good τ' (1 / 100) N)

private theorem firstCellS_zero (τ' : ℝ) (N : ℕ) : firstCellS τ' N = 0 := by
  change gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0 = 0
  exact gridT_zero (by norm_num)

private theorem highProb_firstCell_good {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi) :
    HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta) := by
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, hmargin, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := first_cell_polynomial_regime d τ'
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    rw [firstCellS_zero]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N)
      hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  exact highProb_goodSetFlow_of_localLaw d
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hs0 ht1 hst
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)
    hKbig (fun N => (hΨpos N).le) hΨlowLL hll hmargin

/-- The two source laws and the local law are instantiated at the same `τ'`.
The source threshold `firstCellDelta` and the support threshold `flowDelta`
are kept as separate event components. -/
theorem highProb_jointEvent_at {τ' ζ : ℝ} (hτ' : 0 < τ') (hζ : 0 < ζ)
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi)
    (h4 : firstCellRawLoopDom τ' 4) (h6 : firstCellRawLoopDom τ' 6) :
    HighProb (P d) (jointEvent τ' ζ) := by
  have h4p := h4.highProb hζ
  have h6p := h6.highProb hζ
  have hsource : HighProb (P d)
      (APrimeFirstCellSourceAllTime.commonEvent τ' ζ) := by
    change HighProb (P d)
      (fun N => {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)} ∩
        {ω | ∀ p : TimeIcc (firstCellS τ') (firstCellT τ') N ×
          LoopData (d.L N) 4,
          ‖(sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ *
              Step1.aprioriRhs (band d) 0 (firstCellS τ') (firstCellT τ') 4 N p ω} ∩
        {ω | ∀ p : TimeIcc (firstCellS τ') (firstCellT τ') N ×
          LoopData (d.L N) 6,
          ‖(sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ *
              Step1.aprioriRhs (band d) 0 (firstCellS τ') (firstCellT τ') 6 N p ω} ∩
        goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta N)
    exact (((highProb_norm_Xmat_le d).inter h4p).inter h6p).inter
      (highProb_firstCell_good hτ' hll)
  exact hsource.inter (APrimeSupportRunning.highProb_good hτ'
    (by norm_num : (0 : ℝ) < 1 / 100) hll)

theorem eventually_nonempty_jointEvent_at {τ' ζ : ℝ} (hτ' : 0 < τ')
    (hζ : 0 < ζ)
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi)
    (h4 : firstCellRawLoopDom τ' 4) (h6 : firstCellRawLoopDom τ' 6) :
    ∀ᶠ N : ℕ in atTop, (jointEvent τ' ζ N).Nonempty :=
  (highProb_jointEvent_at hτ' hζ hll h4 h6).nonempty (by simp)

def jointConsequences (τ' ζ : ℝ) : Prop :=
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ jointEvent τ' ζ N,
      (∀ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
        APrimeFullQV.SourceEvent (sample d) 0 N (u : ℝ) ω
          (APrimeFirstCellSourceAllTime.ellSource ζ N)
          (APrimeFirstCellSourceAllTime.sourceC4 ζ N u)) ∧
      (∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
          N0 p N k m ω →
        ∀ r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
          APrimeSupportRunning.jG N r ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8))

/-- Both consequences hold for the same member of the joint event. -/
theorem eventually_source_and_support_at {τ' ζ : ℝ} (hτ' : 0 < τ') :
    jointConsequences τ' ζ := by
  filter_upwards [eventually_ge_atTop 1,
    APrimeSupportRunning.eventually_jG_le_eighth_on_support hτ'] with N hN hcap ω hω
  refine ⟨?_, ?_⟩
  · intro u
    exact APrimeFirstCellSourceAllTime.sourceEvent_of_common (by omega) u hω.1
  · intro N0 p k m hN0 hp hm hk hkT hw r hr
    exact hcap N0 p k m hN0 hp hm hk hkT ω hω.2 hw r hr

/-- The first-cell parameter is chosen once, before the source loss `ζ`. -/
theorem exists_jointEvent :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      (∀ N, MeasurableSet (jointEvent τ' ζ N)) ∧
      HighProb (P d) (jointEvent τ' ζ) ∧
      (∀ᶠ N : ℕ in atTop, (jointEvent τ' ζ N).Nonempty) ∧
      jointConsequences τ' ζ := by
  obtain ⟨τ', hτ', _, hll, h4, h6⟩ :=
    firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  have hp := highProb_jointEvent_at hτ' hζ hll h4 h6
  exact ⟨measurableSet_jointEvent τ' ζ, hp, hp.nonempty (by simp),
    eventually_source_and_support_at hτ'⟩

def positivePlateau (τ' ζ : ℝ) : Prop :=
    ∀ᶠ N : ℕ in atTop, ∃ ω ∈ jointEvent τ' ζ N,
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
          APrimeSupportRunning.jG N r ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8)

/-- An active first-cell prefix on one sample of the joint event. The cutoff
tests `u₀` and `u₁`; its positive weight supports the running bound through
`u₂=2u₁`. -/
theorem eventually_positive_plateau_at {τ' ζ : ℝ} (hτ' : 0 < τ') (hζ : 0 < ζ)
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi)
    (h4 : firstCellRawLoopDom τ' 4) (h6 : firstCellRawLoopDom τ' 6) :
    positivePlateau τ' ζ := by
  have hp := highProb_jointEvent_at hτ' hζ hll h4 h6
  have hg := APrimeSupportRunning.highProb_good hτ'
    (by norm_num : (0 : ℝ) < 1 / 100) hll
  filter_upwards [hp.nonempty (by simp),
    APrimeSupportRunning.positive_plateau_on_good hτ'
      (by norm_num : (0 : ℝ) < 1 / 100) hg,
    APrimeFirstCellCommon.eventually_active_weight_two_one hτ'
      (by norm_num : (0 : ℝ) < 1 / 100),
    APrimeSupportRunning.eventually_jG_le_eighth_on_support hτ',
    eventually_ge_atTop 2] with N hne hplat hweight hcap hN
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨_, _, _, _, hk, _⟩ := hplat
  have hnorm : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω.1.1.1.1
  have hmesh : APrimeSmoothTransition.transitionMesh N = (N : ℝ) ^ (248 : ℕ) := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    simp [APrimeSmoothTransition.transitionMesh, max_eq_right hn]
  have hmeshpos : 0 < APrimeSmoothTransition.transitionMesh N :=
    APrimeSupportRunning.mesh_pos N
  have hu1eq : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1 =
      (N : ℝ) ^ (-(248 : ℝ)) := by
    simp only [cutNetPt, Nat.cast_one, zero_add, one_div]
    rw [hmesh, Real.rpow_neg (Nat.cast_nonneg N)]
    norm_num [Real.rpow_natCast]
  have hu2eq : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2 =
      2 * (N : ℝ) ^ (-(248 : ℝ)) := by
    simp only [cutNetPt, Nat.cast_ofNat, zero_add]
    rw [hmesh, Real.rpow_neg (Nat.cast_nonneg N)]
    norm_num [Real.rpow_natCast, div_eq_mul_inv]
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hu1mem : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1 ∈
      Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
    rw [firstCellS_zero]
    exact MomentDuhamelCut.netFinset_subset_Icc hwin hmeshpos _
      (cutNetPt_mem_netFinset (s := fun _ => 0) (t := firstCellT τ')
        (mesh := APrimeSmoothTransition.transitionMesh) (by omega))
  have hu2mem : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2 ∈
      Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
    rw [firstCellS_zero]
    exact MomentDuhamelCut.netFinset_subset_Icc hwin hmeshpos _
      (cutNetPt_mem_netFinset hk)
  let u1 : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨_, hu1mem⟩
  let u2 : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨_, hu2mem⟩
  have hpos : 0 < (u1 : ℝ) := by
    change 0 < cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
    simp [cutNetPt, hmeshpos]
  have hw : ∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
      (firstCellT τ') 2 p N 2 N ω = 1 := by
    intro p
    have h := hweight ω hnorm p
    rw [APrimeSupportRunning.firstS_eq] at h
    exact h
  have hJ : ∀ r ∈ Set.Icc (0 : ℝ) (u2 : ℝ),
      APrimeSupportRunning.jG N r ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    intro r hr
    exact hcap 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hk ω hω.2 (by rw [hw 1]; norm_num) r hr
  exact ⟨ω, hω, u1, u2, hpos, hu1eq, hu2eq, hw,
    APrimeFirstCellSourceAllTime.sourceEvent_of_common (by omega) u1 hω.1,
    APrimeFirstCellSourceAllTime.sourceEvent_of_common (by omega) u2 hω.1, hJ⟩

/-- One `τ'` is selected before every `ζ`; the joint event and its positive
active-prefix witness use that same parameter and the same Gaussian sample. -/
theorem exists_jointEvent_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      (∀ N, MeasurableSet (jointEvent τ' ζ N)) ∧
      HighProb (P d) (jointEvent τ' ζ) ∧
      (∀ᶠ N : ℕ in atTop, (jointEvent τ' ζ N).Nonempty) ∧
      jointConsequences τ' ζ ∧ positivePlateau τ' ζ := by
  obtain ⟨τ', hτ', _, hll, h4, h6⟩ :=
    firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  have hp := highProb_jointEvent_at hτ' hζ hll h4 h6
  exact ⟨measurableSet_jointEvent τ' ζ, hp, hp.nonempty (by simp),
    eventually_source_and_support_at hτ',
    eventually_positive_plateau_at hτ' hζ hll h4 h6⟩

#print axioms highProb_jointEvent_at
#print axioms eventually_nonempty_jointEvent_at
#print axioms eventually_source_and_support_at
#print axioms exists_jointEvent
#print axioms eventually_positive_plateau_at
#print axioms exists_jointEvent_with_plateau

end RBM.APrimeFirstCellSourceSupport
