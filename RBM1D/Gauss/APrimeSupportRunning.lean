/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothTransition
import RBM1D.Gauss.APrimeFirstCellCommon
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.Eq45FlowBudget
import RBM1D.Gauss.LkGoodMeasurable

/-! # First-cell support bounds for the actual running observable -/
namespace RBM.APrimeSupportRunning
open Filter MeasureTheory Gauss Step2Bootstrap CutHypTheta Cutoff
open APrimeSmoothTransition
open scoped Matrix.Norms.L2Operator

noncomputable abbrev J (N : ℕ) (r : ℝ) (ω : Ω Dims.exampleGrow) : ℝ :=
  Step2Moment.jSnorm (sample Dims.exampleGrow) 0 60 (fun _ => 0) N r ω

noncomputable abbrev weight (δ : ℝ) (t : ℕ → ℝ) (N0 p N k m : ℕ)
    (ω : Ω Dims.exampleGrow) : ℝ :=
  APrimeSmoothWeightActual.weight Dims.exampleGrow 0 60 δ (fun _ => 0) t
    transitionMesh N0 p N k m ω

theorem mesh_pos (N : ℕ) : 0 < transitionMesh N := by
  unfold transitionMesh
  positivity

theorem net_support {δ : ℝ} {t : ℕ → ℝ} {N0 p N k m j : ℕ}
    (hN : 0 < N) (hN0 : N0 ≤ N) (hp : 1 ≤ p) (hm : 1 ≤ m)
    (hk : k ≤ cutNetTop (fun _ => 0) t transitionMesh N) (hj : j < k)
    (ht0 : 0 ≤ t N) (ht1 : t N < 1) (ω : Ω Dims.exampleGrow)
    (hw : 0 < weight δ t N0 p N k m ω) :
    J N (cutNetPt (fun _ => 0) transitionMesh N j) ω <
      16 * (Real.exp 1)^2 * (N : ℝ)^(2*δ) := by
  have hu := MomentDuhamelCut.netFinset_subset_Icc ht0 (mesh_pos N) _
    (cutNetPt_mem_netFinset (show j ≤ cutNetTop (fun _ => 0) t transitionMesh N by omega))
  have hlow := jSnorm_net_le_prefixSample Dims.exampleGrow (D := 60)
    hN hm hj (hu.2.trans_lt ht1) ω
  have hcap : APrimeSmoothWeightActual.prefixSample Dims.exampleGrow 0 60
      (fun _ => 0) transitionMesh N k m ω <
      2 * APrimeSmoothWeightActual.threshold δ N := by
    by_contra hn
    have hz : APrimeSmoothWeightActual.cutoff Dims.exampleGrow 0 60 δ
        (fun _ => 0) transitionMesh N k m ω = 0 := by
      apply cutChi_eq_zero
      exact (le_div_iff₀ (APrimeSmoothWeightActual.threshold_pos hN)).2 (le_of_not_gt hn)
    have hw0 : weight δ t N0 p N k m ω = 0 := by
      unfold weight APrimeSmoothWeightActual.weight
      rw [if_pos ⟨hk, hN0⟩, hz, zero_pow (by omega : 2*p ≠ 0)]
    linarith
  have he : 2 * APrimeSmoothWeightActual.threshold δ N =
      16 * (Real.exp 1)^2 * (N : ℝ)^(2*δ) := by
    unfold APrimeSmoothWeightActual.threshold
    ring
  exact hlow.trans_lt (he ▸ hcap)

theorem modulus :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω Dims.exampleGrow,
      ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ) →
      ∀ r ∈ Set.Icc (0 : ℝ) (1/2), ∀ v ∈ Set.Icc (0 : ℝ) (1/2),
      |J N r ω - J N v ω| ≤ (N : ℝ)^(122 : ℝ) * |r-v|^((1 : ℝ)/2) := by
  simpa only [J, Set.mem_setOf_eq, show (2 : ℝ)+2*60 = 122 by norm_num] using
    APrimeSlotFields.eventually_modulus_jSnorm_event Dims.exampleGrow
      (E := 0) (D := 60) (t₀ := 1/2) (s := fun _ => 0) (t := fun _ => 1/2)
      (Good := fun N => {ω | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)})
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => subset_rfl)

theorem mesh_error {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)^(122 : ℝ) * (1 / transitionMesh N)^((1 : ℝ)/2) = (N : ℝ)^(-(2 : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold transitionMesh
  rw [max_eq_right hn1, one_div, ← Real.rpow_natCast,
    ← Real.rpow_neg_one, ← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
  norm_num

/-- The strict prefix controls its whole running interval, including its right endpoint. -/
theorem eventually_running_support {δ : ℝ} {t : ℕ → ℝ}
    (ht0 : ∀ N, 0 ≤ t N) (ht : ∀ N, t N ≤ 1/2) :
    ∀ᶠ N : ℕ in atTop, ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) t transitionMesh N →
      ∀ ω : Ω Dims.exampleGrow, ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ) →
      0 < weight δ t N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ) (cutNetPt (fun _ => 0) transitionMesh N k),
        J N r ω ≤ 16 * (Real.exp 1)^2 * (N : ℝ)^(2*δ) + (N : ℝ)^(-(2 : ℝ)) := by
  filter_upwards [modulus, eventually_ge_atTop 1] with N hmod hN
  intro N0 p k m hN0 hp hm hk hkT ω hX hw
  apply prefix_of_modulus (s := fun _ => 0) (t := t)
    (mesh := transitionMesh) (Kmod := 122) (γ := (1 : ℝ)/2)
    (by norm_num) (ht0 N) (mesh_pos N) hk hkT
  · intro r hr v hv
    exact hmod ω hX r ⟨hr.1, hr.2.trans (ht N)⟩ v ⟨hv.1, hv.2.trans (ht N)⟩
  · exact (mesh_error hN).le
  · intro j hj
    exact (net_support (by omega) hN0 hp hm hkT hj (ht0 N)
      (by linarith [ht N]) ω hw).le

theorem raw_of_normalized {N : ℕ} {r C : ℝ} (hr : r < 1)
    (ω : Ω Dims.exampleGrow) (hJ : J N r ω ≤ C) :
    Step2.jS (sample Dims.exampleGrow) 0 60 N r ω ≤
      C * (Step2Moment.ratR 0 (fun _ => 0) N r)^4 := by
  have hp := Step2Moment.ratR_pos (E := 0) (s := fun _ => 0) (N := N)
    (by norm_num) (by norm_num) hr
  exact (div_le_iff₀ (pow_pos hp 4)).1 hJ

theorem ratR_four_le_sixteen {N : ℕ} {r : ℝ} (hr : r ≤ 1/2) :
    (Step2Moment.ratR 0 (fun _ => 0) N r)^4 ≤ 16 := by
  have he : Step2Moment.ratR 0 (fun _ => 0) N r = 1 / (1-r) := by
    simp [Step2Moment.ratR, etaT, mE_zero]
  rw [he]
  have hden : 0 < 1-r := by linarith
  have hp : 0 ≤ 1 / (1-r) := by positivity
  have hb : 1 / (1-r) ≤ (2 : ℝ) := (div_le_iff₀ (by linarith : 0 < 1-r)).2 (by linarith)
  exact (pow_le_pow_left₀ hp hb 4).trans_eq (by norm_num)

theorem firstS_eq (τ' : ℝ) : firstCellS τ' = fun _ => 0 := by
  funext N
  exact gridT_zero (by norm_num)

theorem firstT_bounds {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ) :
    0 ≤ firstCellT τ' N ∧ firstCellT τ' N ≤ 1/2 := by
  constructor
  · have hh := gridT_mono (W := ((band Dims.exampleGrow).W N : ℝ)) (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
      hτ'.le (1/2 : ℝ) (Nat.zero_le 1)
    simpa only [firstCellT, gridT_zero (by norm_num : (0 : ℝ) ≤ 1/2)] using hh
  · exact gridT_le _ _

private theorem first_scale_regime {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^((1 : ℝ)/2) ≤
      (band Dims.exampleGrow).scale 0 N (firstCellT τ' N) ∧
      (band Dims.exampleGrow).scale 0 N (firstCellT τ' N) ≤ N := by
  have hbig : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ)^((1 : ℝ)/8) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [Dims.bandwidth_grow, Dims.dim_grow, hbig, eventually_ge_atTop 1]
    with N hW hdim hbigN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hhalf := firstCell_scale_ge_half (τ' := τ') N
    (u := firstCellT τ' N) ⟨by rw [firstS_eq]; exact (firstT_bounds hτ' N).1, le_rfl⟩
  have hp := mul_le_mul_of_nonneg_left hbigN
    (Real.rpow_nonneg (Nat.cast_nonneg N) ((1 : ℝ)/2))
  have hsum : (N : ℝ)^((1 : ℝ)/2) * (N : ℝ)^((1 : ℝ)/8) =
      (N : ℝ)^((1 : ℝ)/2+1/8) := (Real.rpow_add hn _ _).symm
  rw [hsum] at hp
  have hWn : Dims.exampleGrow.W N ≤ N := by
    have hl : 1 ≤ Dims.growL N := le_trans (by norm_num) (Dims.three_le_growL N)
    change Dims.growW N ≤ N
    nlinarith [hdim.1]
  have hWN : (Dims.exampleGrow.W N : ℝ) ≤ N := by exact_mod_cast hWn
  have he := etaT_mul_ellHat_le (L := Dims.exampleGrow.L N)
    (Dims.exampleGrow.three_le_L N) (E := 0) (by norm_num)
    (firstT_bounds hτ' N).1 (by linarith [(firstT_bounds hτ' N).2])
  have hW0 : (0 : ℝ) ≤ Dims.exampleGrow.W N := by positivity
  change (N : ℝ)^((1 : ℝ)/2+1/8) ≤ (Dims.exampleGrow.W N : ℝ) at hW
  refine ⟨by change (N : ℝ)^((1 : ℝ)/2) ≤ _; linarith, ?_⟩
  change (Dims.exampleGrow.W N : ℝ) * ellHat (Dims.exampleGrow.L N) _ * _ ≤ N
  nlinarith [mul_le_mul_of_nonneg_left he hW0]

private theorem first_cond272 {τ' : ℝ} (hτ' : 0 < τ') :
    Cond272 (band Dims.exampleGrow) 0 (fun _ => 0) (firstCellT τ') := by
  have hbig : ∀ᶠ N : ℕ in atTop, (2 : ℝ)^30 ≤ (N : ℝ)^((1 : ℝ)/2) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [first_scale_regime hτ', hbig] with N hreg hbigN
  have hA : (2 : ℝ)^30 ≤ (band Dims.exampleGrow).scale 0 N (firstCellT τ' N) :=
    hbigN.trans hreg.1
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ)<2^30) hA
  have ht : (1/2 : ℝ) ≤ 1-firstCellT τ' N := by linarith [(firstT_bounds hτ' N).2]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/2) ht 30
  change ((band Dims.exampleGrow).scale 0 N (firstCellT τ' N))⁻¹ ≤
    ((1-firstCellT τ' N)/(1-0))^30
  norm_num only [sub_zero, div_one]
  exact hinv.trans (by convert hpow using 1 <;> norm_num)

private theorem first_eta_lower {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^(-(1 : ℝ)) ≤ etaT 0 (firstCellT τ' N) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.rpow_neg_one]
  have hi := inv_anti₀ (by norm_num : (0 : ℝ)<2) hn
  simp only [etaT, mE_zero, Complex.I_im, mul_one]
  norm_num at hi
  linarith [(firstT_bounds hτ' N).2]

private theorem first_flowDelta_margin {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^((1 : ℝ)/24) * firstCellPsi N ≤
      flowDelta Dims.exampleGrow 0 (firstCellT τ') N := by
  filter_upwards [first_scale_regime hτ', firstCellPsi_le_rpow_neg_quarter,
    eventually_ge_atTop 1] with N hreg hpsi hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have ha : 0 < (band Dims.exampleGrow).scale 0 N (firstCellT τ' N) :=
    (Real.rpow_pos_of_pos hn _).trans_le hreg.1
  have hi := inv_anti₀ ha hreg.2
  have hr := Real.rpow_le_rpow (inv_nonneg.2 hn.le) hi (by norm_num : (0 : ℝ) ≤ 1/6)
  have he : ((N : ℝ)⁻¹)^((1 : ℝ)/6) = (N : ℝ)^(-(1 : ℝ)/6) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hn.le]
    ring
  rw [he] at hr
  calc
    _ ≤ (N : ℝ)^((1 : ℝ)/24) * (N : ℝ)^(-(1 : ℝ)/4) :=
      mul_le_mul_of_nonneg_left hpsi (by positivity)
    _ = (N : ℝ)^(-(5 : ℝ)/24) := by rw [← Real.rpow_add hn]; congr 1 <;> ring
    _ ≤ (N : ℝ)^(-(1 : ℝ)/6) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    _ ≤ _ := hr

/-- Actual floored entry bounds and the matching along-flow good event. -/
theorem entry_sources {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi) :
    EntryBoundFlow' Dims.exampleGrow 0 (fun _ => 0) (firstCellT τ')
      (fun N => 2 * (N : ℝ)^(-(60 : ℝ))) ∧
    HighProb (P Dims.exampleGrow) (goodSetFlow Dims.exampleGrow 0 (fun _ => 0)
      (firstCellT τ') (flowDelta Dims.exampleGrow 0 (firstCellT τ'))) := by
  have ht1 : ∀ N, firstCellT τ' N < 1 := fun N => by linarith [(firstT_bounds hτ' N).2]
  have ht0 : ∀ N, 0 ≤ firstCellT τ' N := fun N => (firstT_bounds hτ' N).1
  have hd := flowDelta_le_rpow_neg Dims.exampleGrow
    ((first_scale_regime hτ').mono (fun N hN => hN.1))
  have hll' : LocalLawUnifIcc Dims.exampleGrow 0 (fun _ => 0) (firstCellT τ') firstCellPsi := by
    simpa only [firstS_eq] using hll
  obtain ⟨_, _, _, _, _, hlow, _, _, _, _, _, _, _, _, _⟩ := first_cell_joint_grid_scales hτ'
  obtain ⟨hK, _, _, _⟩ := first_cell_polynomial_regime Dims.exampleGrow τ'
  constructor
  · exact entryBoundFlow_floor Dims.exampleGrow (by norm_num) (fun _ => le_rfl) ht0 ht1
      (by norm_num : (0 : ℝ)≤1) (first_eta_lower hτ')
      (by norm_num : (0 : ℝ)<(1/2)/6) hd (by norm_num)
  · exact highProb_goodSetFlow_of_localLaw Dims.exampleGrow
      (by norm_num : (0 : ℝ)<1/24) (by norm_num) (fun _ => le_rfl) ht1 ht0
      (by norm_num : (0 : ℝ)≤3) (by norm_num : (0 : ℝ)≤2) hK
      (fun N => (firstCellPsi_pos N).le) hlow hll' (first_flowDelta_margin hτ')

noncomputable abbrev jG (N : ℕ) (r : ℝ) (ω : Ω Dims.exampleGrow) : ℝ :=
  APrimeJG.jG (sample Dims.exampleGrow) 0 N r ω
    ((band Dims.exampleGrow).ell N r) (etaT 0 r) 60

def comparisonEvent (τ' ξ : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω | ∀ r : TimeIcc (fun _ => 0) (firstCellT τ') N,
    jG N r ω ≤ 1 + (N : ℝ)^ξ *
      (9 * Real.exp (Real.sqrt 3) * Step2.jS (sample Dims.exampleGrow) 0 60 N r ω + 2)}

def entryEvent (τ' ξ : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω | ∀ q : TimeIcc (fun _ => 0) (firstCellT τ') N ×
      OffPair Dims.exampleGrow.L Dims.exampleGrow.W N,
    (goodSet (L := Dims.exampleGrow.L) (W := Dims.exampleGrow.W)
      (fun N ω => Hflow Dims.exampleGrow N q.1 ω) (zt 0 q.1) (mE 0)
      (flowDelta Dims.exampleGrow 0 (firstCellT τ')) N).indicator
      (fun ω => ‖green (Hflow Dims.exampleGrow N q.1 ω) (zt 0 q.1) q.2.1.1 q.2.1.2‖^2) ω ≤
      (N : ℝ)^ξ * ((∑ a ∈ sbSupport (Dims.exampleGrow.L N),
        ∑ b ∈ sbSupport (Dims.exampleGrow.L N),
        Lre (Hflow Dims.exampleGrow N q.1 ω) (zt 0 q.1)
          (q.2.1.2.1+b) (q.2.1.1.1+a)) +
        (if q.2.1.1.1-q.2.1.2.1 ∈ sbSupport (Dims.exampleGrow.L N)
          then (Dims.exampleGrow.W N : ℝ)⁻¹ else 0) + 2 * (N : ℝ)^(-(60 : ℝ)))}

def rawGood (τ' ξ : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)} ∩
    entryEvent τ' ξ N ∩
    goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (firstCellT τ')
      (flowDelta Dims.exampleGrow 0 (firstCellT τ')) N ∩ comparisonEvent τ' ξ N

noncomputable def good (τ' ξ : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  measCore (P Dims.exampleGrow) (rawGood τ' ξ N)

theorem measurableSet_good (τ' ξ : ℝ) (N : ℕ) : MeasurableSet (good τ' ξ N) :=
  measurableSet_measCore _ _

theorem good_subset (τ' ξ : ℝ) (N : ℕ) : good τ' ξ N ⊆ rawGood τ' ξ N :=
  measCore_subset _ _

theorem highProb_good {τ' ξ : ℝ} (hτ' : 0 < τ') (hξ : 0 < ξ)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi) :
    HighProb (P Dims.exampleGrow) (good τ' ξ) := by
  obtain ⟨he, hg⟩ := entry_sources hτ' hll
  have hj := APrimeJG.highProb_jG_le_of_entryBoundFlow Dims.exampleGrow
    (E := 0) (by norm_num) (fun _ => le_rfl)
    (fun N => (firstT_bounds hτ' N).1)
    (fun N => by linarith [(firstT_bounds hτ' N).2])
    (first_cond272 hτ') 60 (by norm_num) he hg hξ
  exact highProb_measCore ((((highProb_norm_Xmat_le Dims.exampleGrow).inter
    (he.highProb hξ)).inter hg).inter hj)

private theorem eventual_absorb {δ ξ : ℝ} (hslack : 2*δ+ξ<1) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ)^(2*δ+ξ) ≤ N := by
  have ht := ((tendsto_rpow_atTop (by linarith : 0 < 1-(2*δ+ξ))).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  filter_upwards [ht, eventually_ge_atTop 1] with N hN hn
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  change C ≤ (N : ℝ)^(1-(2*δ+ξ)) at hN
  have hmul := mul_le_mul_of_nonneg_right hN
    (Real.rpow_nonneg (Nat.cast_nonneg N) (2*δ+ξ))
  rw [← Real.rpow_add hn0, sub_add_cancel, Real.rpow_one] at hmul
  exact hmul

/-- Sharpness is only on positive active support inside the same source event. -/
theorem eventually_jG_le_on_support {τ' δ ξ : ℝ} (hτ' : 0 < τ')
    (hδ : 0 < δ) (hξ : 0 < ξ) (hslack : 2*δ+ξ<1) :
    ∀ᶠ N : ℕ in atTop, ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ') transitionMesh N →
      ∀ ω ∈ good τ' ξ N, 0 < weight δ (firstCellT τ') N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ) (cutNetPt (fun _ => 0) transitionMesh N k),
        jG N r ω ≤ (N : ℝ) := by
  let A : ℝ := 144 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2+1)
  filter_upwards [eventually_running_support
      (fun N => (firstT_bounds hτ' N).1) (fun N => (firstT_bounds hτ' N).2),
    eventual_absorb hslack (A+3), eventually_ge_atTop 1] with N hrun habs hN
  intro N0 p k m hN0 hp hm hk hkT ω hgood hw r hr
  have hg := good_subset τ' ξ N hgood
  have hX := hg.1.1.1
  have hcmp := hg.2
  have huk := MomentDuhamelCut.netFinset_subset_Icc (firstT_bounds hτ' N).1
    (mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hrt : r ≤ firstCellT τ' N := hr.2.trans huk.2
  have hrhalf : r ≤ 1/2 := hrt.trans (firstT_bounds hτ' N).2
  have hr1 : r < 1 := by linarith
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hJ := hrun N0 p k m hN0 hp hm hk hkT ω hX hw r hr
  have hlow : (N : ℝ)^(-(2 : ℝ)) ≤ (N : ℝ)^(2*δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hraw := raw_of_normalized hr1 ω (hJ.trans (show
      16 * (Real.exp 1)^2 * (N : ℝ)^(2*δ) + (N : ℝ)^(-(2 : ℝ)) ≤
      (16 * (Real.exp 1)^2+1) * (N : ℝ)^(2*δ) by nlinarith))
  have hraw' : Step2.jS (sample Dims.exampleGrow) 0 60 N r ω ≤
      16 * (16 * (Real.exp 1)^2+1) * (N : ℝ)^(2*δ) := by
    exact hraw.trans ((mul_le_mul_of_nonneg_left (ratR_four_le_sixteen hrhalf)
      (by positivity)).trans_eq (by ring))
  have hj := hcmp ⟨r, hr.1, hrt⟩
  have hδ1 : 1 ≤ (N : ℝ)^(2*δ) := Real.one_le_rpow hn1 (by positivity)
  have hξ1 : 1 ≤ (N : ℝ)^ξ := Real.one_le_rpow hn1 hξ.le
  have hprod : (N : ℝ)^(2*δ+ξ) = (N : ℝ)^(2*δ) * (N : ℝ)^ξ :=
    Real.rpow_add hn0 _ _
  have hcontrol : jG N r ω ≤ (A+3) * (N : ℝ)^(2*δ+ξ) := by
    rw [hprod]
    have he := mul_le_mul_of_nonneg_left hraw' (by positivity : 0 ≤ 9 * Real.exp (Real.sqrt 3))
    have he' := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (N : ℝ)^ξ)
    have h1 := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ (N : ℝ)^ξ)
    dsimp [A] at *
    nlinarith
  exact hcontrol.trans habs

private theorem firstT_eventually_half {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, firstCellT τ' N = 1/2 := by
  have ht : Tendsto (fun N : ℕ => (Dims.exampleGrow.W N : ℝ)^(-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W (band Dims.exampleGrow))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ)<1/2)] with N hN
  change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1/2) 1 = 1/2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Dims.growW N : ℝ)^(-τ') < 1/2 at hN
  linarith

/-- The strengthened source event still contains an actual positive-time active plateau. -/
theorem positive_plateau_on_good {τ' δ ξ : ℝ} (hτ' : 0 < τ') (hδ : 0 < δ)
    (hgood : HighProb (P Dims.exampleGrow) (good τ' ξ)) :
    ∀ᶠ N : ℕ in atTop, ∃ ω ∈ good τ' ξ N,
      0 < (transitionMesh N)⁻¹ ∧
      (transitionMesh N)⁻¹ ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) ∧
      2 ≤ cutNetTop (fun _ => 0) (firstCellT τ') transitionMesh N ∧
      ∀ p : ℕ, weight δ (firstCellT τ') 2 p N 2 N ω = 1 := by
  filter_upwards [FastDecayFlow.nonempty_of_highProb hgood,
    APrimeFirstCellCommon.eventually_active_weight_two_one hτ' hδ,
    firstT_eventually_half hτ', eventually_ge_atTop 4] with N hne hweight ht hN
  obtain ⟨ω, hω⟩ := hne
  have hX := (good_subset τ' ξ N hω).1.1.1
  have hn1 : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hn4 : (4 : ℝ)≤N := by exact_mod_cast hN
  have hm4 : (4 : ℝ)≤transitionMesh N := by
    unfold transitionMesh
    rw [max_eq_right hn1]
    have hn := pow_le_pow_right₀ hn1 (by norm_num : 1≤248)
    rw [pow_one] at hn
    exact hn4.trans hn
  have hhalf : (transitionMesh N)⁻¹ ≤ 1/2 := by
    have hi := inv_anti₀ (by norm_num : (0 : ℝ)<2) (by linarith : (2 : ℝ)≤transitionMesh N)
    simpa using hi
  have hk : 2 ≤ cutNetTop (fun _ => 0) (firstCellT τ') transitionMesh N := by
    unfold cutNetTop
    rw [ht]
    apply Nat.le_floor
    simp only [sub_zero]
    linarith
  refine ⟨ω, hω, inv_pos.mpr (mesh_pos N), ⟨(inv_pos.mpr (mesh_pos N)).le, by rwa [ht]⟩, hk, ?_⟩
  intro p
  have hw := hweight ω hX p
  rw [firstS_eq] at hw
  exact hw

/-- An actual source parameter supports both the whole-event comparison and every
positive active prefix implication. No A′ or global jG cap is assumed. -/
theorem exampleGrow_support_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ξ : ℝ, 0 < ξ →
      HighProb (P Dims.exampleGrow) (good τ' ξ) ∧
      ∀ δ : ℝ, 0 < δ → 2*δ+ξ<1 →
        ∀ᶠ N : ℕ in atTop, ∃ ω ∈ good τ' ξ N,
          0 < (transitionMesh N)⁻¹ ∧
          (transitionMesh N)⁻¹ ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) ∧
          2 ≤ cutNetTop (fun _ => 0) (firstCellT τ') transitionMesh N ∧
          (∀ p : ℕ, weight δ (firstCellT τ') 2 p N 2 N ω = 1) ∧
          ∀ r ∈ Set.Icc (0 : ℝ) (cutNetPt (fun _ => 0) transitionMesh N 2), jG N r ω ≤ N := by
  obtain ⟨τ', hτ', _, hll⟩ := firstCell_step1_and_localLaw_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ξ hξ
  have hg := highProb_good hτ' hξ hll
  refine ⟨hg, ?_⟩
  intro δ hδ hslack
  filter_upwards [positive_plateau_on_good hτ' hδ hg,
    eventually_jG_le_on_support hτ' hδ hξ hslack,
    eventually_ge_atTop 2] with N hw hcap hN
  obtain ⟨ω, hω, hp, ht, hk, hw⟩ := hw
  refine ⟨ω, hω, hp, ht, hk, hw, ?_⟩
  exact hcap 2 1 2 N hN (by norm_num) (by omega) (by norm_num) hk ω hω
    (by rw [hw 1]; norm_num)

#print axioms positive_plateau_on_good
#print axioms exampleGrow_support_witness
#print axioms highProb_good
#print axioms eventually_jG_le_on_support
#print axioms entry_sources
#print axioms eventually_running_support
#print axioms raw_of_normalized
#print axioms ratR_four_le_sixteen
end RBM.APrimeSupportRunning
