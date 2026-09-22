/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGNearRunning
import RBM1D.Gauss.APrimeFirstCellEGFarRunning

/-!
# T413: arbitrary-loss first-cell common support event

The support loss `ξ = δ/16` is kept distinct from all source losses.  The
event uses one literal first-cell parameter and the actual smooth weight.
-/

namespace RBM.APrimeFirstCellMovingSupport

open Filter MeasureTheory Gauss CutHypTheta Cutoff
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

private theorem prefixSample_nonneg (N k m : ℕ) (ω : Ω d) :
    0 ≤ APrimeSmoothWeightActual.prefixSample d 0 60 (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k m ω := by
  unfold APrimeSmoothWeightActual.prefixSample
    APrimeSmoothWeightActual.prefixMatrix
  exact Step2Bootstrap.softMax_nonneg _ _ _

theorem threshold_mono {δ : ℝ} {N : ℕ} (hN : 1 ≤ (N : ℝ))
    (hδ : δ ≤ 1 / 100) :
    APrimeSmoothWeightActual.threshold δ N ≤
      APrimeSmoothWeightActual.threshold (1 / 100) N := by
  unfold APrimeSmoothWeightActual.threshold
  gcongr

theorem cutoff_mono {δ : ℝ} {N k m : ℕ} (ω : Ω d)
    (hN : 1 ≤ (N : ℝ)) (hδ : δ ≤ 1 / 100) :
    APrimeSmoothWeightActual.cutoff d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m ω ≤
      APrimeSmoothWeightActual.cutoff d 0 60 (1 / 100) (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m ω := by
  have hNnat : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hpre := prefixSample_nonneg N k m ω
  have hδpos := APrimeSmoothWeightActual.threshold_pos (δ := δ) hNnat
  have hthr := threshold_mono hN hδ
  unfold APrimeSmoothWeightActual.cutoff
  apply Cutoff.cutChi_antitone
  exact div_le_div_of_nonneg_left hpre hδpos hthr

theorem weight_mono {τ' δ : ℝ} {N0 p N k m : ℕ} (ω : Ω d)
    (hN : 1 ≤ (N : ℝ)) (hδ : δ ≤ 1 / 100) :
    APrimeSupportRunning.weight δ (firstCellT τ') N0 p N k m ω ≤
      APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
        N0 p N k m ω := by
  unfold APrimeSupportRunning.weight APrimeSmoothWeightActual.weight
  split_ifs with hactive
  · exact pow_le_pow_left₀ (Cutoff.cutChi_nonneg _)
      (cutoff_mono ω hN hδ) (2 * p)
  · exact le_rfl

/-- Positivity of the actual `δ` cutoff implies positivity of the fixed
`1/100` cutoff used by the running source estimates. -/
theorem weight_pos_transfer {τ' δ : ℝ} {N0 p N k m : ℕ} {ω : Ω d}
    (hN : 1 ≤ (N : ℝ)) (_hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hw : 0 < APrimeSupportRunning.weight δ (firstCellT τ')
      N0 p N k m ω) :
    0 < APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
      N0 p N k m ω := by
  exact hw.trans_le (weight_mono (τ' := τ') ω hN hδ100)

theorem weight_one_transfer {τ' δ : ℝ} {N0 p N k m : ℕ} {ω : Ω d}
    (hN : 1 ≤ (N : ℝ)) (hδ100 : δ ≤ 1 / 100)
    (hw : APrimeSupportRunning.weight δ (firstCellT τ')
      N0 p N k m ω = 1) :
    APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
      N0 p N k m ω = 1 := by
  apply le_antisymm
  · exact APrimeSmoothWeightActual.weight_le_one d 0 60 (1 / 100)
      (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
      N0 p N k m ω
  · calc
      (1 : ℝ) = APrimeSupportRunning.weight δ (firstCellT τ')
          N0 p N k m ω := hw.symm
      _ ≤ APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
          N0 p N k m ω := weight_mono (τ' := τ') ω hN hδ100

/-- T410's running source event, T384's all-time length-four/six source,
the fixed support event used by T409/T410, and the dynamic `ξ` support event
all live at one literal first-cell parameter. -/
def commonEvent (τ' ζ₁ ζ₃ ξ : ℝ) (N : ℕ) : Set (Ω d) :=
  APrimeFirstCellEGFarRunning.good τ' ζ₁ ζ₃ N ∩
    APrimeSupportRunning.good τ' ξ N

theorem measurableSet_commonEvent {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ ξ : ℝ) (N : ℕ) : MeasurableSet (commonEvent τ' ζ₁ ζ₃ ξ N) :=
  (APrimeFirstCellEGFarRunning.measurableSet_good hτ' ζ₁ ζ₃ N).inter
    (APrimeSupportRunning.measurableSet_good τ' ξ N)

theorem highProb_commonEvent_of_inputs {τ' ζ₁ ζ₃ ξ : ℝ}
    (hτ' : 0 < τ') (hζ₁ : 0 < ζ₁) (hζ₃ : 0 < ζ₃) (hξ : 0 < ξ)
    (h1 : Step1.Hyp (sample d) 0 (firstCellS τ') (firstCellT τ'))
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi)
    (h4 : firstCellRawLoopDom τ' 4) (h6 : firstCellRawLoopDom τ' 6) :
    HighProb (P d) (commonEvent τ' ζ₁ ζ₃ ξ) :=
  (APrimeFirstCellEGFarRunning.highProb_good_of_inputs
    hτ' h1 hll h4 h6 hζ₁ hζ₃).inter
      (APrimeSupportRunning.highProb_good hτ' hξ hll)

theorem commonEvent_to_far {τ' ζ₁ ζ₃ ξ : ℝ} {N : ℕ} {ω : Ω d}
    (hω : ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N) :
    ω ∈ APrimeFirstCellEGFarRunning.good τ' ζ₁ ζ₃ N := hω.1

theorem commonEvent_to_near {τ' ν ξ : ℝ} {N : ℕ} {ω : Ω d}
    (hω : ω ∈ commonEvent τ'
      (APrimeFirstCellEGNearRunning.sourceLoss ν)
      (APrimeFirstCellEGNearRunning.sourceLoss ν) ξ N) :
    ω ∈ APrimeFirstCellEGNearRunning.good τ' ν N := hω.1

theorem commonEvent_to_source {τ' ζ₁ ζ₃ ξ : ℝ} {N : ℕ} {ω : Ω d}
    (hω : ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N) :
    ω ∈ APrimeFirstCellSourceAllTime.commonEvent τ' ζ₃ N := hω.1.2.1

theorem commonEvent_to_fixed_support {τ' ζ₁ ζ₃ ξ : ℝ}
    {N : ℕ} {ω : Ω d} (hω : ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N) :
    ω ∈ APrimeSupportRunning.good τ' (1 / 100) N := hω.1.2.2

theorem commonEvent_to_dynamic_support {τ' ζ₁ ζ₃ ξ : ℝ}
    {N : ℕ} {ω : Ω d} (hω : ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N) :
    ω ∈ APrimeSupportRunning.good τ' ξ N := hω.2

/-- The dynamic support cap is obtained directly from T388 at
`ξ=δ/16`; the fixed `N^(1/8)` cap is not used. -/
theorem eventually_dynamic_jG {τ' δ ζ₁ ζ₃ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) :
    let ξ := δ / 16
    ∀ᶠ N : ℕ in atTop, ∀ N0 p k m : ℕ,
      N0 ≤ N → 1 ≤ p → 1 ≤ m → 1 ≤ k →
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N,
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
        APrimeSupportRunning.jG N r ω ≤
          APrimeSupportRunning.supportConstant *
            (N : ℝ) ^ (2 * δ + δ / 16) := by
  dsimp only
  filter_upwards [APrimeSupportRunning.eventually_jG_le_constant_on_support
    hτ' hδ (by positivity : 0 < δ / 16)] with N hcap
  intro N0 p k m hN0 hp hm hk hkT ω hω hw r hr
  exact hcap N0 p k m hN0 hp hm hk hkT ω hω.2 hw r hr

def commonConsequences (τ' δ ζ₁ ζ₃ : ℝ) : Prop :=
  let ξ := δ / 16
  ∀ᶠ N : ℕ in atTop, ∀ ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N,
    (∀ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
      APrimeFullQV.SourceEvent (sample d) 0 N (u : ℝ) ω
        (APrimeFirstCellSourceAllTime.ellSource ζ₃ N)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ₃ N u)) ∧
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m → 1 ≤ k →
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      0 < APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
        N0 p N k m ω ∧
      ∀ r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
        APrimeSupportRunning.jG N r ω ≤
          APrimeSupportRunning.supportConstant *
            (N : ℝ) ^ (2 * δ + δ / 16)

theorem eventually_commonConsequences {τ' δ ζ₁ ζ₃ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100) :
    commonConsequences τ' δ ζ₁ ζ₃ := by
  have hcap := eventually_dynamic_jG (τ' := τ') (ζ₁ := ζ₁) (ζ₃ := ζ₃) hτ' hδ
  filter_upwards [hcap, eventually_ge_atTop 1] with N hcap hNnat ω hω
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast hNnat
  constructor
  · intro u
    exact APrimeFirstCellSourceAllTime.sourceEvent_of_common (by omega) u hω.1.2.1
  · intro N0 p k m hN0 hp hm hk hkT hw
    exact ⟨weight_pos_transfer hN hδ hδ100 hw,
      hcap N0 p k m hN0 hp hm hk hkT ω hω hw⟩

def positivePlateau (τ' δ ζ₁ ζ₃ : ℝ) : Prop :=
  let ξ := δ / 16
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ commonEvent τ' ζ₁ ζ₃ ξ N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    APrimeFullQV.SourceEvent (sample d) 0 N u2 ω
      (APrimeFirstCellSourceAllTime.ellSource ζ₃ N)
      (APrimeFirstCellSourceAllTime.sourceC4 ζ₃ N u2) ∧
    ∀ r ∈ Set.Icc (0 : ℝ) u2,
      APrimeSupportRunning.jG N r ω ≤
        APrimeSupportRunning.supportConstant *
          (N : ℝ) ^ (2 * δ + δ / 16)

theorem positivePlateau_of_common {τ' δ ζ₁ ζ₃ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hp : HighProb (P d) (commonEvent τ' ζ₁ ζ₃ (δ / 16))) :
    positivePlateau τ' δ ζ₁ ζ₃ := by
  have hdyn : HighProb (P d) (APrimeSupportRunning.good τ' (δ / 16)) :=
    hp.mono (Eventually.of_forall fun N => Set.inter_subset_right)
  have hcap := eventually_dynamic_jG (τ' := τ') (ζ₁ := ζ₁) (ζ₃ := ζ₃) hτ' hδ
  filter_upwards [hp.nonempty (by simp),
    APrimeSupportRunning.positive_plateau_on_good hτ' hδ hdyn,
    APrimeFirstCellCommon.eventually_active_weight_two_one hτ' hδ,
    hcap, eventually_ge_atTop 2] with N hne hplat hweight hcap hN
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨_, _, _, _, hk, _⟩ := hplat
  have hraw := APrimeSupportRunning.good_subset τ' (δ / 16) N hω.2
  have hnorm : ‖Xmat d N ω‖ ≤ (N : ℝ) := hraw.1.1.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwδ : ∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1 := by
    intro p
    have h := hweight ω hnorm p
    rw [APrimeSupportRunning.firstS_eq] at h
    exact h
  have hw100 : ∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
      (firstCellT τ') 2 p N 2 N ω = 1 := by
    intro p
    exact weight_one_transfer hNr hδ100 (hwδ p)
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hmesh : 0 < APrimeSmoothTransition.transitionMesh N :=
    APrimeSupportRunning.mesh_pos N
  have hu2pos : 0 < u2 := by
    dsimp [u2]
    simp only [cutNetPt, Nat.cast_ofNat, zero_add]
    positivity
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hu2mem : u2 ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc hwin hmesh _
      (cutNetPt_mem_netFinset hk)
  have hs0 : firstCellS τ' N = 0 := by
    exact Gauss.firstCellS_eq_zero τ' N
  let ut : TimeIcc (firstCellS τ') (firstCellT τ') N := by
    refine ⟨u2, ?_⟩
    rw [hs0]
    exact hu2mem
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (show 0 < N by omega) ut hω.1.2.1
  have hJ : ∀ r ∈ Set.Icc (0 : ℝ) u2,
      APrimeSupportRunning.jG N r ω ≤
        APrimeSupportRunning.supportConstant *
          (N : ℝ) ^ (2 * δ + δ / 16) := by
    exact hcap 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hk ω hω (by rw [hwδ 1]; norm_num)
  refine ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2mem.2, ?_, hJ⟩
  simpa only [ut] using hsource

/-- One T358 parameter is chosen before the cutoff loss, source losses, and
moment index.  Every component and the positive witness use that parameter. -/
theorem exists_commonEvent_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      let ξ := δ / 16
      ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
        (∀ N, MeasurableSet (commonEvent τ' ζ₁ ζ₃ ξ N)) ∧
        HighProb (P d) (commonEvent τ' ζ₁ ζ₃ ξ) ∧
        commonConsequences τ' δ ζ₁ ζ₃ ∧
        positivePlateau τ' δ ζ₁ ζ₃ := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100
  dsimp only
  intro ζ₁ ζ₃ hζ₁ hζ₃
  have hp := highProb_commonEvent_of_inputs hτ' hζ₁ hζ₃
    (by positivity : 0 < δ / 16) h1 hll h4 h6
  exact ⟨measurableSet_commonEvent hτ' ζ₁ ζ₃ (δ / 16), hp,
    eventually_commonConsequences hτ' hδ hδ100,
    positivePlateau_of_common hτ' hδ hδ100 hp⟩

#print axioms threshold_mono
#print axioms cutoff_mono
#print axioms weight_pos_transfer
#print axioms eventually_dynamic_jG
#print axioms eventually_commonConsequences
#print axioms positivePlateau_of_common
#print axioms exists_commonEvent_with_plateau

end RBM.APrimeFirstCellMovingSupport
