/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondExpMod
import RBM1D.Gauss.DetFlucAvgComplete
import RBM1D.Gauss.LkGoodMeasurable

/-! # Simultaneous first-cell fluctuation averaging -/
namespace RBM.Gauss.DetFlucAvgTimeNet
open Filter MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

/-- The conditional row is integrated before bounding its time increment. -/
theorem norm_flucDiag_sub_le_half (d : Dims) (N : ℕ) {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1/2)) (hv : v ∈ Set.Icc (0 : ℝ) (1/2))
    (k : d.Idx N) (ω : Ω d) :
    ‖flucDiag d N u (zt 0 u) (mE 0) k ω - flucDiag d N v (zt 0 v) (mE 0) k ω‖ ≤
      4 * (2 * ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖^2 + 9/2) *
        |u-v|^((1 : ℝ)/2) := by
  have hu1 : u < 1 := by linarith [hu.2]
  have hv1 : v < 1 := by linarith [hv.2]
  have hi (r : ℝ) (hr : r ≤ 1/2) : (etaT 0 r)⁻¹ ≤ 2 := by
    simp only [etaT, mE_zero, Complex.I_im, mul_one]
    apply (inv_le_comm₀ (by linarith : 0 < 1-r) (by norm_num : (0 : ℝ) < 2)).2
    norm_num
    linarith
  have hiu0 : 0 ≤ (etaT 0 u)⁻¹ := (inv_pos.mpr (etaT_pos_of_lt_one' (by norm_num) hu1)).le
  have hiv0 : 0 ≤ (etaT 0 v)⁻¹ := (inv_pos.mpr (etaT_pos_of_lt_one' (by norm_num) hv1)).le
  let R := |u-v|^((1 : ℝ)/2)
  have hR : 0 ≤ R := Real.rpow_nonneg (abs_nonneg _) _
  have hsqrt : |Real.sqrt u - Real.sqrt v| ≤ R := by
    simpa [R, Real.sqrt_eq_rpow] using RBM.abs_sqrt_sub_sqrt_le hu.1 hv.1
  have hlin : |u-v| ≤ R := self_le_rpow_half (abs_nonneg _) (by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2])
  have hG := norm_green_flow_sub_le d N (E := 0) (by norm_num) hu1 hv1 ω
  have hC := norm_condExpDiag_flow_sub_le d N (E := 0) (by norm_num) hu1 hv1 k ω
  have hG' : ‖green (Hflow d N u ω) (zt 0 u) - green (Hflow d N v ω) (zt 0 v)‖ ≤
      4 * (‖Xmat d N ω‖ + 1) * R := by
    calc
      _ ≤ 2 * (R * ‖Xmat d N ω‖ + R) * 2 := hG.trans (by gcongr; exact hi u hu.2; exact hi v hv.2)
      _ = _ := by ring
  have hC' : ‖condExpDiag d N u (zt 0 u) (mE 0) k ω -
      condExpDiag d N v (zt 0 v) (mE 0) k ω‖ ≤
      4 * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖^2 + 7/2) * R := by
    calc
      _ ≤ 2 * 2 * (R * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖^2 + 5/2) + R) :=
        hC.trans (by gcongr; exact hi u hu.2; exact hi v hv.2)
      _ = _ := by ring
  have heq : flucDiag d N u (zt 0 u) (mE 0) k ω - flucDiag d N v (zt 0 v) (mE 0) k ω =
      (green (Hflow d N u ω) (zt 0 u) - green (Hflow d N v ω) (zt 0 v)) k k -
      (condExpDiag d N u (zt 0 u) (mE 0) k ω - condExpDiag d N v (zt 0 v) (mE 0) k ω) := by
    simp only [flucDiag, greenDiagCentered, condExpDiag, Matrix.sub_apply]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add
    ((norm_apply_le_l2_opNorm _ _ _).trans hG') hC').trans_eq (by dsimp [R]; ring))

/-- Any time-independent weights of total absolute mass one have the same modulus. -/
theorem norm_flucAvg_sub_le_half (d : Dims) (N : ℕ) {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1/2)) (hv : v ∈ Set.Icc (0 : ℝ) (1/2))
    (w : d.Idx N → ℝ) (hw : ∑ k, |w k| = 1) (ω : Ω d) :
    ‖flucAvg d N u (zt 0 u) (mE 0) w ω - flucAvg d N v (zt 0 v) (mE 0) w ω‖ ≤
      4 * (2 * ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖^2 + 9/2) * |u-v|^((1 : ℝ)/2) := by
  rw [flucAvg, flucAvg, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k, |w k| * (4 * (2 * ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖^2 + 9/2) * |u-v|^((1 : ℝ)/2)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_flucDiag_sub_le_half d N hu hv k ω) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hw, one_mul]

private theorem firstCell_mem_half {τ' : ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N)) :
    u ∈ Set.Icc (0 : ℝ) (1/2) := by
  have hs : firstCellS τ' N = 0 := gridT_zero (by norm_num)
  exact ⟨by simpa [hs] using hu.1, hu.2.trans (gridT_le _ _)⟩

private theorem firstCell_psiSq_low :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^(-(2 : ℝ)) ≤ firstCellPsi N^2 := by
  filter_upwards [Dims.dim_grow, eventually_ge_atTop 4] with N hdim hN
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hW0 : (0 : ℝ) < Dims.exampleGrow.W N := by exact_mod_cast Dims.exampleGrow.W_pos N
  have hWn : Dims.exampleGrow.W N ≤ N := by
    have hl : 1 ≤ Dims.growL N := le_trans (by norm_num) (Dims.three_le_growL N)
    change Dims.growW N ≤ N
    nlinarith [hdim.1]
  have hW : (Dims.exampleGrow.W N : ℝ) ≤ N := by exact_mod_cast hWn
  have he : firstCellPsi N^2 = (Dims.exampleGrow.W N : ℝ)⁻¹ / 4 := by
    unfold firstCellPsi
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    norm_num only [mul_div_cancel_left₀, mul_one]
    rw [Real.rpow_neg_one]
  rw [he, Real.rpow_neg (by positivity : (0 : ℝ) ≤ N), Real.rpow_two]
  have hinv : (4 : ℝ) * Dims.exampleGrow.W N ≤ (N : ℝ)^2 := by nlinarith
  have hi := inv_anti₀ (by positivity : (0 : ℝ) < 4 * Dims.exampleGrow.W N) hinv
  convert hi using 1 <;> field_simp <;> ring

/-- The actual mass-one averages have Hölder constant N^5 on the norm event. -/
theorem firstCell_holder {τ' : ℝ} {V : ℕ → Type*}
    (w : ∀ N, V N → Dims.exampleGrow.Idx N → ℝ)
    (hw : ∀ N a, ∑ k, |w N a k| = 1) :
    ∀ᶠ N : ℕ in atTop, ∀ ω, ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ) →
      ∀ a, ∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      |‖flucAvg Dims.exampleGrow N u (zt 0 u) (mE 0) (w N a) ω‖ -
        ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0) (w N a) ω‖| ≤
        (N : ℝ)^(5 : ℝ) * |u-v|^((1 : ℝ)/2) := by
  filter_upwards [eventually_ge_atTop 8] with N hN ω hX a u hu v hv
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hX0 := norm_nonneg (Xmat Dims.exampleGrow N ω)
  have hc : 4 * (2 * ‖Xmat Dims.exampleGrow N ω‖ + 2 * ‖Xmat Dims.exampleGrow N ω‖^2 + 9/2)
      ≤ (N : ℝ)^(5 : ℝ) := by
    rw [Real.rpow_ofNat]
    have hp : (N : ℝ)^2 ≤ (N : ℝ)^3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h28 : (28 : ℝ) ≤ (N : ℝ)^3 := by nlinarith [sq_nonneg ((N : ℝ)-8)]
    have hcoef : 4 * (2 * ‖Xmat Dims.exampleGrow N ω‖ + 2 * ‖Xmat Dims.exampleGrow N ω‖^2 + 9/2)
        ≤ 28 * (N : ℝ)^2 := by nlinarith
    calc _ ≤ 28 * (N : ℝ)^2 := hcoef
         _ ≤ (N : ℝ)^3 * (N : ℝ)^2 := mul_le_mul_of_nonneg_right h28 (sq_nonneg _)
         _ = (N : ℝ)^5 := by ring
  exact (abs_norm_sub_norm_le _ _).trans
    ((norm_flucAvg_sub_le_half _ N (firstCell_mem_half hu) (firstCell_mem_half hv)
      (w N a) (hw N a) ω).trans (mul_le_mul_of_nonneg_right hc (by positivity)))

/-- First-cell time-net consumer: H=5, B=2, γ=1/2, hence mesh exponent 16. -/
theorem firstCell_stochDom_of_unif {τ' : ℝ} (hτ' : 0 < τ')
    {V : ℕ → Type*} [∀ N, Fintype (V N)]
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ)^(1 : ℝ))
    (w : ∀ N, V N → Dims.exampleGrow.Idx N → ℝ)
    (hw : ∀ N a, ∑ k, |w N a k| = 1)
    (hfix : UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u a ω => ‖flucAvg Dims.exampleGrow N u (zt 0 u) (mE 0) (w N a) ω‖)
      (fun N _ _ _ => firstCellPsi N^2)) :
    StochDom (P Dims.exampleGrow)
      (U := fun N => TimeIcc (firstCellS τ') (firstCellT τ') N × V N)
      (fun N q ω => ‖flucAvg Dims.exampleGrow N q.1 (zt 0 q.1) (mE 0) (w N q.2) ω‖)
      (fun N _ _ => firstCellPsi N^2) := by
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := fun N =>
    gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N) hτ'.le _ (Nat.zero_le 1)
  refine stochDom_timeIcc_of_unifDom hcard hst one_pos ?_
    (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 1/2) (fun N _ _ _ => sq_nonneg _)
    (δ := fun N => 1 / (N : ℝ)^(16 : ℝ))
    (Eventually.of_forall (fun N => by norm_num))
    (highProb_norm_Xmat_le Dims.exampleGrow) ?_ ?_ ?_ hfix
  · intro N
    have hs : firstCellS τ' N = 0 := gridT_zero (by norm_num)
    have ht : firstCellT τ' N ≤ 1/2 := gridT_le _ _
    linarith
  · exact firstCell_holder w hw
  · filter_upwards [firstCell_psiSq_low] with N hN _ _ _ _ _
    exact hN
  · intro ε hε
    filter_upwards [eventually_le_rpow 1 hε] with N hN _ _ _ _ _ _ _ _
    nlinarith [sq_nonneg (firstCellPsi N)]

noncomputable abbrev rowWeights (N : ℕ) (i : Dims.exampleGrow.Idx N) : Dims.exampleGrow.Idx N → ℝ :=
  fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j

noncomputable abbrev blockWeights (N : ℕ) (a : ZMod (Dims.exampleGrow.L N)) : Dims.exampleGrow.Idx N → ℝ :=
  blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) a

def RowDom (τ' : ℝ) : Prop :=
  StochDom (P Dims.exampleGrow)
    (U := fun N => TimeIcc (firstCellS τ') (firstCellT τ') N × Dims.exampleGrow.Idx N)
    (fun N q ω => ‖flucAvg Dims.exampleGrow N q.1 (zt 0 q.1) (mE 0) (rowWeights N q.2) ω‖)
    (fun N _ _ => firstCellPsi N^2)

def BlockDom (τ' : ℝ) : Prop :=
  StochDom (P Dims.exampleGrow)
    (U := fun N => TimeIcc (firstCellS τ') (firstCellT τ') N × ZMod (Dims.exampleGrow.L N))
    (fun N q ω => ‖flucAvg Dims.exampleGrow N q.1 (zt 0 q.1) (mE 0) (blockWeights N q.2) ω‖)
    (fun N _ _ => firstCellPsi N^2)

theorem simultaneous_of_localLaw {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi) :
    RowDom τ' ∧ BlockDom τ' := by
  obtain ⟨hr, hb⟩ := firstCellFlucAvg_psiSq_of_localLaw hτ' hll
  constructor
  · apply firstCell_stochDom_of_unif hτ' (card_Idx_le Dims.exampleGrow) rowWeights _ hr
    intro N i
    simp only [rowWeights, abs_of_nonneg (Sblk_nonneg _ _)]
    exact sum_Sblk_row (Dims.exampleGrow.three_le_L N) i
  · exact firstCell_stochDom_of_unif hτ' (card_ZMod_L_le Dims.exampleGrow)
      blockWeights (fun N a => sum_abs_blkCoef a) hb

/-- The common raw event asserts both families at every real time. -/
def jointGood (τ' ε : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω | ∀ q : TimeIcc (firstCellS τ') (firstCellT τ') N × Dims.exampleGrow.Idx N,
    ‖flucAvg Dims.exampleGrow N q.1 (zt 0 q.1) (mE 0) (rowWeights N q.2) ω‖ ≤
      (N : ℝ)^ε * firstCellPsi N^2} ∩
  {ω | ∀ q : TimeIcc (firstCellS τ') (firstCellT τ') N × ZMod (Dims.exampleGrow.L N),
    ‖flucAvg Dims.exampleGrow N q.1 (zt 0 q.1) (mE 0) (blockWeights N q.2) ω‖ ≤
      (N : ℝ)^ε * firstCellPsi N^2}

/-- A measurable subset preserving all simultaneous conclusions and the same failure measure. -/
noncomputable def good (τ' ε : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  measCore (P Dims.exampleGrow) (jointGood τ' ε N)

theorem measurableSet_good (τ' ε : ℝ) (N : ℕ) : MeasurableSet (good τ' ε N) :=
  measurableSet_measCore _ _

theorem good_subset (τ' ε : ℝ) (N : ℕ) : good τ' ε N ⊆ jointGood τ' ε N :=
  measCore_subset _ _

theorem highProb_good {τ' ε : ℝ} (hr : RowDom τ') (hb : BlockDom τ') (hε : 0 < ε) :
    HighProb (P Dims.exampleGrow) (good τ' ε) :=
  highProb_measCore ((hr.highProb hε).inter (hb.highProb hε))

/-- No local law or stochastic FA premise remains: Step 1 supplies the actual first cell. -/
theorem exampleGrow_simultaneous :
    ∃ τ' : ℝ, 0 < τ' ∧ RowDom τ' ∧ BlockDom τ' ∧
      ∀ ε : ℝ, 0 < ε → HighProb (P Dims.exampleGrow) (good τ' ε) ∧
        ∀ᶠ N : ℕ in atTop,
          firstCellS τ' N < firstCellT τ' N ∧ (good τ' ε N).Nonempty := by
  obtain ⟨τ', hτ', _, hll⟩ := firstCell_step1_and_localLaw_same_parameter
  obtain ⟨hr, hb⟩ := simultaneous_of_localLaw hτ' hll
  refine ⟨τ', hτ', hr, hb, ?_⟩
  intro ε hε
  have hg := highProb_good hr hb hε
  refine ⟨hg, ?_⟩
  filter_upwards [firstCell_localLaw_bridge_nondegenerate hτ',
    FastDecayFlow.nonempty_of_highProb hg] with N hN hne
  exact ⟨hN.1, hne⟩

#print axioms norm_flucDiag_sub_le_half
#print axioms norm_flucAvg_sub_le_half
#print axioms firstCell_holder
#print axioms firstCell_stochDom_of_unif
#print axioms simultaneous_of_localLaw
#print axioms highProb_good
#print axioms exampleGrow_simultaneous
end RBM.Gauss.DetFlucAvgTimeNet
