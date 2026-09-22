/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.Gauss.DetFlucAvgTimeNet

/-! # Simultaneous first-cell averaged one-loop law -/

namespace RBM.Gauss.DetAvgIBPTimeNet

open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def ibpResidual (N : ℕ) (u : ℝ) (i : d.Idx N) (ω : Ω d) : ℝ :=
  ‖condExpDiag d N u (zt 0 u) (mE 0) i ω
    - (u : ℂ) * mE 0 ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
      * (green (Hflow d N u ω) (zt 0 u) k k - mE 0)‖

def IBPDom (τ' : ℝ) : Prop :=
  StochDom (P d)
    (U := fun N => TimeIcc (firstCellS τ') (firstCellT τ') N × d.Idx N)
    (fun N q ω => ibpResidual N q.1 q.2 ω)
    (fun N _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N)

/-- The weighted IBP residual has one all-time first-cell domination event. -/
theorem ibpDom_of_unif {τ' : ℝ} (hτ' : 0 < τ')
    (hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta))
    (hfix : UnifDomIcc (P d) (firstCellS τ') (firstCellT τ')
      (fun N u (i : d.Idx N) ω => ibpResidual N u i ω)
      (fun N _ _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N)) :
    IBPDom τ' := by
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := fun N =>
    gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le _ (Nat.zero_le 1)
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := fun N => by
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := fun N =>
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  obtain ⟨_, hKc, hKtot, _⟩ := first_cell_polynomial_regime d τ'
  have hhol := holIBP_of_inputs (δ := firstCellDelta) d
    (by norm_num : |(0 : ℝ)| < 2) hs0 ht1 hKc hKtot
  obtain ⟨_, _, _, _, hpsilow, _, _, _, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  have hlow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(2 : ℝ)) ≤
        firstCellPsiWeighted N * firstCellPsiWeighted N := by
    filter_upwards [hpsilow] with N hN
    change (N : ℝ) ^ (-(2 : ℝ)) ≤ firstCellPsi N * firstCellPsi N at hN
    dsimp [firstCellPsiWeighted]
    nlinarith [sq_nonneg (firstCellPsi N)]
  have hζ0 : ∀ N (u : ℝ) (i : d.Idx N) (ω : Ω d),
      0 ≤ firstCellPsiWeighted N * firstCellPsiWeighted N := by
    intro N u i ω
    have hp : 0 ≤ firstCellPsiWeighted N :=
      mul_nonneg (by norm_num) (firstCellPsi_pos N).le
    exact mul_nonneg hp hp
  have hHol : ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ flowNetEvent d 0 (firstCellS τ') (firstCellT τ') firstCellDelta N,
      ∀ i : d.Idx N, ∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
        |ibpResidual N u i ω - ibpResidual N v i ω| ≤
          (N : ℝ) ^ (6 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
    simpa only [ibpResidual] using hhol
  refine stochDom_timeIcc_of_unifDom (card_Idx_le d) hst one_pos ?_
    (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 1 / 2) hζ0
    (δ := fun N => 1 / (N : ℝ) ^ (18 : ℝ))
    (Eventually.of_forall (fun N => by norm_num))
    (highProb_flowNetEvent d hΩ) hHol ?_ ?_ hfix
  · intro N
    have hs : firstCellS τ' N = 0 := gridT_zero (by norm_num)
    have ht : firstCellT τ' N ≤ 1 / 2 := gridT_le _ _
    linarith
  · filter_upwards [hlow] with N hN _ _ _ _ _
    exact hN
  · intro ε hε
    filter_upwards [eventually_le_rpow 1 hε] with N hN _ _ _ _ _ _ _ _
    have hp : 0 ≤ firstCellPsiWeighted N * firstCellPsiWeighted N :=
      mul_nonneg (mul_nonneg (by norm_num) (firstCellPsi_pos N).le)
        (mul_nonneg (by norm_num) (firstCellPsi_pos N).le)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hN hp

/-- The Step 1 local law supplies the weighted IBP time-net on its own cell. -/
theorem ibpDom_of_localLaw {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi) :
    IBPDom τ' := by
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := fun N => by
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := fun N =>
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := fun N =>
    gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le _ (Nat.zero_le 1)
  obtain ⟨hΨpos, h2Ψ1, hWinv, _, hΨlow, hΨlowLL, _,
    hmargin, hδ1, _, _, _, _, _, _⟩ := first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, hEnv⟩ := first_cell_polynomial_regime d τ'
  have hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta) :=
    highProb_goodSetFlow_of_localLaw d (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num) hs0 ht1 hst (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 2) hKbig (fun N => (hΨpos N).le)
      hΨlowLL hll hmargin
  have hΨ0 : ∀ N, 0 ≤ firstCellPsiWeighted N := fun N =>
    mul_nonneg (by norm_num) (hΨpos N).le
  have hΨ1 : ∀ᶠ N : ℕ in atTop,
      firstCellPsiWeighted N * firstCellPsiWeighted N ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with N _
    have hp : 0 ≤ firstCellPsi N := (hΨpos N).le
    have hle := h2Ψ1 N
    change 2 * firstCellPsi N ≤ 1 at hle
    dsimp [firstCellPsiWeighted]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle)
      (by linarith : 0 ≤ 1 + 2 * firstCellPsi N)]
  have hΨlow' : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(2 : ℝ)) ≤
        firstCellPsiWeighted N * firstCellPsiWeighted N := by
    filter_upwards [hΨlow] with N hN
    change (N : ℝ) ^ (-(2 : ℝ)) ≤ firstCellPsi N * firstCellPsi N at hN
    dsimp [firstCellPsiWeighted]
    nlinarith [sq_nonneg (firstCellPsi N)]
  have hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤
      firstCellPsiWeighted N * firstCellPsiWeighted N := by
    intro N
    have h := hWinv N
    change ((d.W N : ℝ))⁻¹ ≤ 4 * firstCellPsi N ^ 2 at h
    change ((Dims.growW N : ℝ))⁻¹ ≤ 4 * firstCellPsi N ^ 2 at h
    dsimp [firstCellPsiWeighted]
    nlinarith
  have hll' : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ')
      firstCellPsiWeighted := by
    apply hll.mono_control
    intro N u ij ω
    dsimp [firstCellPsiWeighted]
    have hp : 0 ≤ firstCellPsi N := (hΨpos N).le
    linarith
  have hfix := unifDomIcc_condExpDiag_weighted (d := d) (E := 0)
    (s := firstCellS τ') (t := firstCellT τ') (Ψ := firstCellPsiWeighted)
    (δ := firstCellDelta) (Kenv := 2) (B := 2)
    (by norm_num) hs0 ht1 hΨ0 (by norm_num) (by norm_num) hEnv
    hΨlow' hΨ1 hWΨ hδ1 hΩ hll'
  exact ibpDom_of_unif hτ' hΩ (by simpa only [ibpResidual] using hfix)

/-- The deterministic first-cell scale from (4.11)–(4.12). -/
noncomputable def Phi (N : ℕ) (u : ℝ) : ℝ :=
  1 / ((d.W N : ℝ) * (1 - u)) + ((d.W N : ℝ))⁻¹

theorem psiWeighted_sq_eq_invW (N : ℕ) :
    firstCellPsiWeighted N * firstCellPsiWeighted N = ((d.W N : ℝ))⁻¹ := by
  have hw : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  change (2 * (((d.W N : ℝ) ^ (-(1 : ℝ) / 2)) / 2)) *
    (2 * (((d.W N : ℝ) ^ (-(1 : ℝ) / 2)) / 2)) = ((d.W N : ℝ))⁻¹
  have hs : (((d.W N : ℝ) ^ (-(1 : ℝ) / 2))) ^ 2 = ((d.W N : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
    norm_num [Real.rpow_neg_one]
  nlinarith

theorem psiWeighted_sq_le_Phi (N : ℕ) {u : ℝ} (hu : u < 1) :
    firstCellPsiWeighted N * firstCellPsiWeighted N ≤ Phi N u := by
  rw [psiWeighted_sq_eq_invW, Phi]
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hden : 0 < (d.W N : ℝ) * (1 - u) := mul_pos hw (by linarith)
  have hnonneg : 0 ≤ 1 / ((d.W N : ℝ) * (1 - u)) := by positivity
  linarith

theorem psi_sq_le_Phi (N : ℕ) {u : ℝ} (hu : u < 1) :
    firstCellPsi N ^ 2 ≤ Phi N u := by
  have h := psiWeighted_sq_le_Phi N hu
  have hp : 0 ≤ firstCellPsi N := (firstCellPsi_pos N).le
  dsimp [firstCellPsiWeighted] at h
  nlinarith

def ibpGood (τ' ε : ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ∀ q : TimeIcc (firstCellS τ') (firstCellT τ') N × d.Idx N,
    ibpResidual N q.1 q.2 ω ≤
      (N : ℝ)^ε * (firstCellPsiWeighted N * firstCellPsiWeighted N)}

def jointGood (τ' ε : ℝ) (N : ℕ) : Set (Ω d) :=
  ibpGood τ' ε N ∩ DetFlucAvgTimeNet.good τ' ε N

noncomputable def good (τ' ε : ℝ) (N : ℕ) : Set (Ω d) :=
  measCore (P d) (jointGood τ' ε N)

theorem measurableSet_good (τ' ε : ℝ) (N : ℕ) : MeasurableSet (good τ' ε N) :=
  measurableSet_measCore _ _

theorem good_subset (τ' ε : ℝ) (N : ℕ) : good τ' ε N ⊆ jointGood τ' ε N :=
  measCore_subset _ _

theorem highProb_good {τ' ε : ℝ} (hI : IBPDom τ')
    (hR : DetFlucAvgTimeNet.RowDom τ')
    (hB : DetFlucAvgTimeNet.BlockDom τ') (hε : 0 < ε) :
    HighProb (P d) (good τ' ε) := by
  apply highProb_measCore
  exact (hI.highProb hε).inter (DetFlucAvgTimeNet.highProb_good hR hB hε)

/-- On the one common event, stability closes the actual block trace at the deterministic scale. -/
theorem trace_le_on_good {τ' ε : ℝ} (N : ℕ) (ω : Ω d)
    (hω : ω ∈ good τ' ε N)
    (u : ℝ) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (b : ZMod (d.L N)) :
    ‖Matrix.trace ((green (Hflow d N u ω) (zt 0 u)
      - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) b)‖ ≤
      (1 + 2 * Kstab 1) * (N : ℝ)^ε * Phi N u := by
  have hs : firstCellS τ' N = 0 := gridT_zero (by norm_num)
  have hv0 : 0 ≤ u := by simpa only [hs] using hu.1
  have hv1 : u < 1 := hu.2.trans_lt
    ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  obtain ⟨hI, hFA⟩ := good_subset τ' ε N hω
  obtain ⟨hR, hB⟩ := DetFlucAvgTimeNet.good_subset τ' ε N hFA
  have hA0 : 0 ≤ (N : ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hIBP : ∀ i : d.Idx N, ibpResidual N u i ω ≤ (N : ℝ)^ε * Phi N u := by
    intro i
    have hi := hI (⟨u, hu⟩, i)
    exact hi.trans (mul_le_mul_of_nonneg_left (psiWeighted_sq_le_Phi N hv1) hA0)
  have hRow : ∀ i : d.Idx N,
      ‖flucAvg d N u (zt 0 u) (mE 0)
        (fun j => Sblk (d.L N) (d.W N) i j) ω‖ ≤ (N : ℝ)^ε * Phi N u := by
    intro i
    have hi := hR (⟨u, hu⟩, i)
    change ‖flucAvg d N u (zt 0 u) (mE 0)
      (fun j => Sblk (d.L N) (d.W N) i j) ω‖ ≤
        (N : ℝ)^ε * firstCellPsi N ^ 2 at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (psi_sq_le_Phi N hv1) hA0)
  have hBlock :
      ‖flucAvg d N u (zt 0 u) (mE 0)
        (blkCoef (d.L N) (d.W N) b) ω‖ ≤ (N : ℝ)^ε * Phi N u := by
    have hb := hB (⟨u, hu⟩, b)
    change ‖flucAvg d N u (zt 0 u) (mE 0)
      (blkCoef (d.L N) (d.W N) b) ω‖ ≤
        (N : ℝ)^ε * firstCellPsi N ^ 2 at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (psi_sq_le_Phi N hv1) hA0)
  exact norm_detAvgIBP_le d (κ := 1) (E := 0) (v := u)
    (by norm_num) (by norm_num) (by norm_num) hv0 hv1 ω b
    (A := (N : ℝ)^ε) (Φ := Phi N u) hIBP hRow hBlock

/-- Absorb the fixed stability constant using half of the stochastic tolerance. -/
theorem eventually_trace_le_on_good {τ' ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good τ' (ε / 2) N,
      ∀ q : TimeIcc (firstCellS τ') (firstCellT τ') N × ZMod (d.L N),
        ‖Matrix.trace ((green (Hflow d N q.1 ω) (zt 0 q.1)
          - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) q.2)‖ ≤
          (N : ℝ)^ε * Phi N q.1 := by
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [eventually_le_rpow (1 + 2 * Kstab 1) hhalf,
    eventually_ge_atTop 1] with N hC hN ω hω q
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu1 : (q.1 : ℝ) < 1 := q.1.property.2.trans_lt
    ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hPhi : 0 ≤ Phi N q.1 := by
    unfold Phi
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    have hden : 0 < (d.W N : ℝ) * (1 - (q.1 : ℝ)) := mul_pos hw (by linarith)
    positivity
  have hpow : (N : ℝ)^(ε / 2) * (N : ℝ)^(ε / 2) = (N : ℝ)^ε := by
    rw [← Real.rpow_add hNr]
    congr 1
    ring
  have hconst : (1 + 2 * Kstab 1) * (N : ℝ)^(ε / 2) ≤ (N : ℝ)^ε := by
    calc
      _ ≤ (N : ℝ)^(ε / 2) * (N : ℝ)^(ε / 2) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hNr.le _)
      _ = _ := hpow
  exact (trace_le_on_good N ω hω q.1 q.1.property q.2).trans
    (mul_le_mul_of_nonneg_right hconst hPhi)

def TraceDom (τ' : ℝ) : Prop :=
  StochDom (P d)
    (U := fun N => TimeIcc (firstCellS τ') (firstCellT τ') N × ZMod (d.L N))
    (fun N q ω => ‖Matrix.trace ((green (Hflow d N q.1 ω) (zt 0 q.1)
      - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) q.2)‖)
    (fun N q _ => Phi N q.1)

theorem traceDom_of_inputs {τ' : ℝ} (hI : IBPDom τ')
    (hR : DetFlucAvgTimeNet.RowDom τ')
    (hB : DetFlucAvgTimeNet.BlockDom τ') : TraceDom τ' := by
  intro ε hε D hD
  have hhalf : 0 < ε / 2 := by linarith
  have hgood := highProb_good hI hR hB hhalf
  filter_upwards [hgood D hD, eventually_trace_le_on_good (τ' := τ') hε]
    with N hprob hbound
  change (P d) (badSet
    (fun N (q : TimeIcc (firstCellS τ') (firstCellT τ') N × ZMod (d.L N)) ω =>
      ‖Matrix.trace ((green (Hflow d N q.1 ω) (zt 0 q.1)
        - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) q.2)‖)
    (fun N q _ => Phi N q.1) ε N) ≤ _
  calc
    _ ≤ (P d) (good τ' (ε / 2) N)ᶜ := by
      apply measure_mono
      intro ω hω
      by_contra hmem
      obtain ⟨q, hq⟩ := hω
      have hmem' : ω ∈ good τ' (ε / 2) N := by simpa using hmem
      exact (not_lt.mpr (hbound ω hmem' q)) hq
    _ ≤ _ := hprob

/-- A single Step 1 cell carries the three errors and the deterministic one-loop law. -/
theorem exampleGrow_simultaneous :
    ∃ τ' : ℝ, 0 < τ' ∧ IBPDom τ' ∧
      DetFlucAvgTimeNet.RowDom τ' ∧ DetFlucAvgTimeNet.BlockDom τ' ∧
      TraceDom τ' ∧
      ∀ ε : ℝ, 0 < ε →
        HighProb (P d) (good τ' (ε / 2)) ∧
        ∀ᶠ N : ℕ in atTop,
          firstCellS τ' N < firstCellT τ' N ∧
          (good τ' (ε / 2) N).Nonempty ∧
          ∀ ω ∈ good τ' (ε / 2) N,
            ∀ q : TimeIcc (firstCellS τ') (firstCellT τ') N × ZMod (d.L N),
              ‖Matrix.trace ((green (Hflow d N q.1 ω) (zt 0 q.1)
                - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
                  Eblk (d.L N) (d.W N) q.2)‖ ≤
                (N : ℝ)^ε * Phi N q.1 := by
  obtain ⟨τ', hτ', _, hll⟩ := firstCell_step1_and_localLaw_same_parameter
  have hI := ibpDom_of_localLaw hτ' hll
  obtain ⟨hR, hB⟩ := DetFlucAvgTimeNet.simultaneous_of_localLaw hτ' hll
  refine ⟨τ', hτ', hI, hR, hB, traceDom_of_inputs hI hR hB, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hg := highProb_good hI hR hB hhalf
  refine ⟨hg, ?_⟩
  filter_upwards [firstCell_localLaw_bridge_nondegenerate hτ',
    FastDecayFlow.nonempty_of_highProb hg,
    eventually_trace_le_on_good (τ' := τ') hε] with N hlen hne hbound
  exact ⟨hlen.1, hne, hbound⟩

/-- The initial trace error is identically zero, independently of the good event. -/
theorem trace_at_zero (N : ℕ) (ω : Ω d) (b : ZMod (d.L N)) :
    Matrix.trace ((green (Hflow d N 0 ω) (zt 0 0)
      - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) b) = 0 :=
  detAvgIBP_at_zero d N (by norm_num : |(0 : ℝ)| ≤ 2) ω b

/-- The first auxiliary cut-net time, independently of the proof-net mesh. -/
noncomputable def cutTime (N : ℕ) : ℝ := ((N : ℝ) ^ (248 : ℕ))⁻¹

theorem eventually_firstCellT_half {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, firstCellT τ' N = 1 / 2 := by
  have hWt : Tendsto (fun N : ℕ => ((d.W N : ℝ)) ^ (-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W (band d))
  filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hW
  change gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Dims.growW N : ℝ) ^ (-τ') < 1 / 2 at hW
  linarith

theorem eventually_cutTime_mem {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      0 < cutTime N ∧
      cutTime N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
  filter_upwards [eventually_firstCellT_half hτ', eventually_ge_atTop 2]
    with N ht hN
  have hs : firstCellS τ' N = 0 := gridT_zero (by norm_num)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (2 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
    calc (2 : ℝ) ≤ (N : ℝ) := hNr
      _ ≤ (N : ℝ) ^ (248 : ℕ) := by
        calc (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := by simp
          _ ≤ (N : ℝ) ^ (248 : ℕ) :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
  have hcut : 0 < cutTime N := by unfold cutTime; positivity
  refine ⟨hcut, ?_⟩
  rw [hs, ht]
  constructor
  · exact hcut.le
  · unfold cutTime
    simpa [one_div] using
      (inv_le_inv₀ (show (0 : ℝ) < (N : ℝ) ^ 248 by linarith)
        (show (0 : ℝ) < 2 by norm_num)).2 hp

/-- The same continuum-time event controls the first auxiliary cut-net time. -/
theorem eventually_cutTime_trace_le_on_good {τ' ε : ℝ}
    (hτ' : 0 < τ') (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good τ' (ε / 2) N,
      ∀ b : ZMod (d.L N),
        ‖Matrix.trace ((green (Hflow d N (cutTime N) ω) (zt 0 (cutTime N))
          - mE 0 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖ ≤
          (N : ℝ)^ε * Phi N (cutTime N) := by
  filter_upwards [eventually_cutTime_mem hτ',
    eventually_trace_le_on_good (τ' := τ') hε] with N hmem hbound ω hω b
  exact hbound ω hω (⟨cutTime N, hmem.2⟩, b)

#print axioms ibpDom_of_unif
#print axioms ibpDom_of_localLaw
#print axioms highProb_good
#print axioms trace_le_on_good
#print axioms eventually_trace_le_on_good
#print axioms traceDom_of_inputs
#print axioms exampleGrow_simultaneous
#print axioms trace_at_zero
#print axioms eventually_cutTime_mem
#print axioms eventually_cutTime_trace_le_on_good

end RBM.Gauss.DetAvgIBPTimeNet
