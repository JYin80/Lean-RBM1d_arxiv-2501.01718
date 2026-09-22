/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowGrid
import RBM1D.Gauss.Eq45Small

/-!
# The budgeted fluctuation input on the first grid cell — T284

The direct supplier `flucGainUpTo'_goodSetFlow` uses the same threshold as its bad-event
base.  On T279's first cell that threshold is `N^(1/16) Ψ`, so its explicit budget cannot
be bounded by a constant multiple of `Ψ`.  The certificate below records this exact loss.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- The `B` produced by `flucGainUpTo'_goodSetFlow` after choosing the conditional
slice threshold so that its cost equals `2 δ`. -/
noncomputable def firstCellGoodSetBudget (p N : ℕ) : ℝ :=
  2 * (2 * minorDiffC (2 * p) * (2 * firstCellDelta N) + 2 * firstCellDelta N)

/-- The fixed threshold `δ=N^(1/16) Ψ` costs an unavoidable `N^(1/16)` in the
published good-set supplier's budget. -/
theorem no_fixed_budget_from_firstCellDelta (p : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ¬ ∀ᶠ N : ℕ in atTop,
      firstCellGoodSetBudget p N ≤ K * firstCellPsi N := by
  intro hbudget
  have hΨpos : ∀ N, 0 < firstCellPsi N := by
    intro N
    unfold firstCellPsi
    have hw : (0 : ℝ) < Dims.exampleGrow.W N := by
      exact_mod_cast Dims.exampleGrow.W_pos N
    positivity
  have hpow : ∀ᶠ N : ℕ in atTop,
      K + 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 16) :=
    eventually_le_rpow (K + 1) (by norm_num)
  obtain ⟨N, hBN, hPN⟩ := (hbudget.and hpow).exists
  have hC := minorDiffC_nonneg (2 * p)
  have hδ : firstCellDelta N = (N : ℝ) ^ ((1 : ℝ) / 16) * firstCellPsi N := rfl
  have hB : 4 * firstCellDelta N ≤ firstCellGoodSetBudget p N := by
    unfold firstCellGoodSetBudget
    nlinarith [mul_nonneg hC (le_of_lt (hΨpos N)),
      Real.rpow_nonneg (Nat.cast_nonneg N) ((1 : ℝ) / 16)]
  rw [hδ] at hB
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 3 * K + 4) (hΨpos N),
    mul_nonneg (sub_nonneg.mpr hPN) (hΨpos N).le]

#print axioms no_fixed_budget_from_firstCellDelta

/-! ### A threshold chosen after the stochastic-domination exponent -/

/-- This threshold is capped at `1/4`, as required by the minor expansion.  For each
positive exponent `θ`, it is eventually `(N+4)^θ Ψ_N`. -/
noncomputable def firstCellBudgetDelta (θ : ℝ) (N : ℕ) : ℝ :=
  min (1 / 4 : ℝ) (((N : ℝ) + 4) ^ θ * firstCellPsi N)

theorem firstCellPsi_pos (N : ℕ) : 0 < firstCellPsi N := by
  unfold firstCellPsi
  have hw : (0 : ℝ) < Dims.exampleGrow.W N := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  positivity

theorem firstCellBudgetDelta_pos {θ : ℝ} (_hθ : 0 ≤ θ) (N : ℕ) :
    0 < firstCellBudgetDelta θ N := by
  unfold firstCellBudgetDelta
  have hn : (0 : ℝ) < (N : ℝ) + 4 := by positivity
  have := firstCellPsi_pos N
  exact lt_min (by norm_num) (mul_pos (Real.rpow_pos_of_pos hn θ) this)

theorem firstCellBudgetDelta_le_quarter (θ : ℝ) (N : ℕ) :
    firstCellBudgetDelta θ N ≤ 1 / 4 := min_le_left _ _

/-- The cap retains the level scale needed by both row and block averaging. -/
theorem firstCellPsi_half_le_budgetDelta {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    firstCellPsi N / 2 ≤ firstCellBudgetDelta θ N := by
  have hhalf : 2 * firstCellPsi N ≤ 1 := by
    obtain ⟨_, h, _⟩ := first_cell_joint_grid_scales (by norm_num : (0 : ℝ) < 1 / 32)
    exact h N
  have hp : 1 ≤ ((N : ℝ) + 4) ^ θ :=
    Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hθ
  unfold firstCellBudgetDelta
  apply le_min
  · linarith
  · have hΨ := (firstCellPsi_pos N).le
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hΨ]

/-- On the growing-bandwidth example, the weak local-law scale is eventually at most
`N^(-1/4)`. -/
theorem firstCellPsi_le_rpow_neg_quarter :
    ∀ᶠ N : ℕ in atTop,
      firstCellPsi N ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := by
  filter_upwards [Dims.bandwidth_grow, eventually_ge_atTop 1] with N hW hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : (0 : ℝ) < Dims.exampleGrow.W N := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (Dims.exampleGrow.W N : ℝ) := by
    calc (N : ℝ) ^ ((1 : ℝ) / 2)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
          Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ ≤ (Dims.exampleGrow.W N : ℝ) := by
        simpa [Dims.exampleGrow_W] using hW
  have hroot : (N : ℝ) ^ ((1 : ℝ) / 4) ≤
      (Dims.exampleGrow.W N : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by positivity :
      (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) hpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1; rw [← Real.rpow_mul (by positivity)]; norm_num
  have hroot0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hi := inv_anti₀ hroot0 hroot
  unfold firstCellPsi
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hw.le,
    show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.rpow_neg (by positivity :
      (0 : ℝ) ≤ (N : ℝ))]
  linarith [inv_nonneg.mpr (by positivity :
    (0 : ℝ) ≤ (Dims.exampleGrow.W N : ℝ) ^ ((1 : ℝ) / 2))]

#print axioms firstCellPsi_le_rpow_neg_quarter

/-- Any exponent at most `1/32` leaves a fixed negative power after the bandwidth gain. -/
theorem firstCellBudgetRaw_le_rpow_neg_eighth {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 32) :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 4) ^ θ * firstCellPsi N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) := by
  filter_upwards [firstCellPsi_le_rpow_neg_quarter, eventually_ge_atTop 4]
    with N hΨ hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < N := by linarith
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hp : ((N : ℝ) + 4) ^ θ ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := by
    calc ((N : ℝ) + 4) ^ θ
        ≤ ((N : ℝ) ^ (2 : ℕ)) ^ θ :=
          Real.rpow_le_rpow (by positivity) hn2 hθ0
      _ = (N : ℝ) ^ (2 * θ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
          ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 16) :=
          Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hraw : ((N : ℝ) + 4) ^ θ * firstCellPsi N
      ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) := by
    calc ((N : ℝ) + 4) ^ θ * firstCellPsi N
        ≤ (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ (-(1 : ℝ) / 4) := by
          exact mul_le_mul hp hΨ (firstCellPsi_pos N).le
            (Real.rpow_nonneg hn0 _)
      _ = (N : ℝ) ^ (-(3 : ℝ) / 16) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
      _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) :=
          Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  exact hraw

#print axioms firstCellBudgetRaw_le_rpow_neg_eighth

theorem firstCellBudgetDelta_le_rpow_neg_eighth {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 32) :
    ∀ᶠ N : ℕ in atTop,
      firstCellBudgetDelta θ N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) := by
  filter_upwards [firstCellBudgetRaw_le_rpow_neg_eighth hθ0 hθ] with N hN
  exact (min_le_right _ _).trans hN

#print axioms firstCellBudgetDelta_le_rpow_neg_eighth

theorem firstCellBudgetDelta_eq_raw {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 32) :
    ∀ᶠ N : ℕ in atTop,
      firstCellBudgetDelta θ N = ((N : ℝ) + 4) ^ θ * firstCellPsi N := by
  filter_upwards [firstCellBudgetRaw_le_rpow_neg_eighth hθ0 hθ,
    eventually_le_rpow 4 (by norm_num : (0 : ℝ) < 1 / 8), eventually_ge_atTop 1]
    with N hraw hp hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) := by positivity
  have hsmall : (N : ℝ) ^ (-(1 : ℝ) / 8) ≤ 1 / 4 := by
    rw [show -(1 : ℝ) / 8 = -((1 : ℝ) / 8) by ring, Real.rpow_neg hn.le]
    rw [inv_le_iff_one_le_mul₀ hpow]
    nlinarith
  unfold firstCellBudgetDelta
  exact min_eq_right (hraw.trans hsmall)

theorem firstCellBudgetDelta_margin {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 32) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (θ / 2) * firstCellPsi N ≤ firstCellBudgetDelta θ N := by
  filter_upwards [firstCellBudgetDelta_eq_raw hθ0.le hθ, eventually_ge_atTop 1]
    with N hraw hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hp : (N : ℝ) ^ (θ / 2) ≤ ((N : ℝ) + 4) ^ θ := by
    calc (N : ℝ) ^ (θ / 2) ≤ (N : ℝ) ^ θ :=
          Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      _ ≤ ((N : ℝ) + 4) ^ θ :=
          Real.rpow_le_rpow hn0 (by linarith) hθ0.le
  rw [hraw]
  exact mul_le_mul_of_nonneg_right hp (firstCellPsi_pos N).le

theorem firstCellBudgetDelta_polyLo {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 32) : PolyLo (firstCellBudgetDelta θ) := by
  obtain ⟨_, _, _, _, _, hΨlow, _, _, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨1, one_pos, 2, ?_⟩
  filter_upwards [firstCellBudgetDelta_eq_raw hθ0.le hθ, hΨlow,
    eventually_ge_atTop 1] with N hraw hΨ hN
  have hp : 1 ≤ ((N : ℝ) + 4) ^ θ :=
    Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hθ0.le
  rw [one_mul, hraw]
  have hprod : firstCellPsi N ≤ ((N : ℝ) + 4) ^ θ * firstCellPsi N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (firstCellPsi_pos N).le]
  exact hΨ.trans hprod

#print axioms firstCellBudgetDelta_eq_raw
#print axioms firstCellBudgetDelta_margin
#print axioms firstCellBudgetDelta_polyLo

theorem firstCellBudgetDelta_highProb {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    HighProb (P Dims.exampleGrow)
      (goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
        (firstCellBudgetDelta θ)) := by
  let d := Dims.exampleGrow
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, _, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := first_cell_polynomial_regime d τ'
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  exact highProb_goodSetFlow_of_localLaw d (half_pos hθ0) (by norm_num)
    hs0 ht1 hst (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)
    hKbig (fun N => (hΨpos N).le) hΨlowLL hll
    (firstCellBudgetDelta_margin hθ0 hθ)

#print axioms firstCellBudgetDelta_highProb

/-- The first-cell spectral envelope needed to control the conditional tower. -/
theorem firstCellEta_polyHi (τ' : ℝ) :
    PolyHi (fun N => (etaT 0 (firstCellT τ' N))⁻¹ + 1) := by
  apply (polyHi_const (c := (3 : ℝ)) (by norm_num)).mono
  exact Filter.Eventually.of_forall fun N => by
    change (etaT 0 (gridT ((band Dims.exampleGrow).W N : ℝ)
      τ' (1 / 2 : ℝ) 1))⁻¹ + 1 ≤ 3
    linarith [first_cell_eta_inv_le_two Dims.exampleGrow τ' N]

/-- Both fixed-moment smallness conditions follow from the `N^{-1/8}` decay of the
movable good-event threshold. -/
theorem firstCellBudgetDelta_moment_small {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 32) (p : ℕ) :
    (∀ᶠ N : ℕ in atTop, 8 * (2 * p : ℝ) * firstCellBudgetDelta θ N ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      2 * minorDiffC (2 * p) * (2 * firstCellBudgetDelta θ N)
        + 2 * firstCellBudgetDelta θ N ≤ 1) := by
  have hδ := firstCellBudgetDelta_le_rpow_neg_eighth hθ0 hθ
  have hC : 0 ≤ 4 * minorDiffC (2 * p) + 2 := by
    have := minorDiffC_nonneg (2 * p)
    linarith
  have hsmall (C : ℝ) (hC : 0 ≤ C) :
      ∀ᶠ N : ℕ in atTop, C * firstCellBudgetDelta θ N ≤ 1 := by
    filter_upwards [hδ, eventually_le_rpow C (by norm_num : (0 : ℝ) < 1 / 8),
      eventually_ge_atTop 1] with N hδN hCN hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hpow : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) := by positivity
    have hbound : C * (N : ℝ) ^ (-(1 : ℝ) / 8) ≤ 1 := by
      rw [show -(1 : ℝ) / 8 = -((1 : ℝ) / 8) by ring, Real.rpow_neg hn.le,
        mul_inv_le_iff₀ hpow]
      simpa using hCN
    exact (mul_le_mul_of_nonneg_left hδN hC).trans hbound
  refine ⟨?_, ?_⟩
  · filter_upwards [hsmall (16 * (p : ℝ)) (by positivity)] with N hN
    nlinarith
  · filter_upwards [hsmall (4 * minorDiffC (2 * p) + 2) hC] with N hN
    nlinarith

#print axioms firstCellEta_polyHi
#print axioms firstCellBudgetDelta_moment_small

noncomputable def firstCellBudgetB (θ : ℝ) (p N : ℕ) : ℝ :=
  2 * (2 * minorDiffC (2 * p) * (2 * firstCellBudgetDelta θ N)
    + 2 * firstCellBudgetDelta θ N)

noncomputable def firstCellBudgetRho (θ : ℝ) (N : ℕ) : ℝ :=
  4 * firstCellBudgetDelta θ N

/-- The existing T177/T188 conditional tower construction produces the budgeted gain
from the local law when the good-event threshold is chosen after `θ`. -/
theorem firstCellFlucGain_from_localLaw {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
        FlucGainUpTo' Dims.exampleGrow N u (zt 0 u) (mE 0)
          (firstCellBudgetB θ p N) (firstCellBudgetRho θ N) (2 * p) (2 * p) := by
  let d := Dims.exampleGrow
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hδpos : ∀ N, 0 < firstCellBudgetDelta θ N :=
    firstCellBudgetDelta_pos hθ0.le
  have hδlo := firstCellBudgetDelta_polyLo hθ0 hθ
  have hΩ := firstCellBudgetDelta_highProb hτ' hθ0 hθ hll
  have hηhi := firstCellEta_polyHi τ'
  intro p
  obtain ⟨hMδ, hδC⟩ := firstCellBudgetDelta_moment_small hθ0.le hθ p
  have hsmall := hsmall_of_highProb d (E := 0) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellBudgetDelta θ)
    (by norm_num : |(0 : ℝ)| < 2) ht1 hδpos hδlo hηhi hΩ p
  filter_upwards [hMδ, hδC, hsmall] with N hMδN hδCN hsmallN u hu
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hΨ : (0 : ℝ) < 2 * firstCellBudgetDelta θ N := by
    linarith [hδpos N]
  have hcc : condCost 0 u (2 * p) (2 * firstCellBudgetDelta θ N)
      (condEps 0 u (2 * p) (2 * firstCellBudgetDelta θ N))
        = 2 * firstCellBudgetDelta θ N :=
    condCost_condEps (by norm_num) hu1 (2 * p) hΨ
  have h := flucGainUpTo'_goodSetFlow
    (E := 0) (s := firstCellS τ') (t := firstCellT τ')
    (δ := firstCellBudgetDelta θ) (M := 2 * p) (n := 2 * p)
    (by norm_num : |(0 : ℝ)| < 2) hu1 hu
    (condEps_nonneg (E := 0) (by norm_num) hu1 (2 * p) hΨ.le)
    (hδpos N) (firstCellBudgetDelta_le_quarter θ N)
    (by push_cast; linarith [hMδN])
    (by rw [hcc]; exact hδCN) (by rw [hcc]; exact hsmallN u hu)
  change FlucGainUpTo' d N u (zt 0 u) (mE 0)
    (firstCellBudgetB θ p N) (firstCellBudgetRho θ N) (2 * p) (2 * p)
  convert h using 1 <;> norm_num [firstCellBudgetB, firstCellBudgetRho, hcc]
  all_goals ring

#print axioms firstCellFlucGain_from_localLaw

theorem firstCellBudgetRho_le_one {θ : ℝ} (_hθ : 0 ≤ θ) (N : ℕ) :
    firstCellBudgetRho θ N ≤ 1 := by
  unfold firstCellBudgetRho
  linarith [firstCellBudgetDelta_le_quarter θ N]

theorem firstCellBudgetRho_sq_ge_W_inv {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    ((Dims.exampleGrow.W N : ℝ))⁻¹ ≤ firstCellBudgetRho θ N ^ 2 := by
  obtain ⟨_, _, hW, _⟩ :=
    first_cell_joint_grid_scales (by norm_num : (0 : ℝ) < 1 / 32)
  have hΨ := firstCellPsi_half_le_budgetDelta hθ N
  have hΨ0 := (firstCellPsi_pos N).le
  have hr : 2 * firstCellPsi N ≤ firstCellBudgetRho θ N := by
    unfold firstCellBudgetRho
    linarith
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * firstCellPsi N) hr 2
  calc
    ((Dims.exampleGrow.W N : ℝ))⁻¹ ≤ 4 * firstCellPsi N ^ 2 := hW N
    _ = (2 * firstCellPsi N) ^ 2 := by ring
    _ ≤ firstCellBudgetRho θ N ^ 2 := hsq

/-- For each small exponent the T177 moment engine gives row and block bounds at the
movable scale `4 δ_θ²`. -/
theorem firstCellFlucAvg_budget_family {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (i : Dims.exampleGrow.Idx N) ω =>
        ‖flucAvg Dims.exampleGrow N u (zt 0 u) (mE 0)
          (fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j) ω‖)
      (fun N _ _ _ => firstCellBudgetRho θ N * firstCellBudgetDelta θ N) ∧
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (a : ZMod (Dims.exampleGrow.L N)) ω =>
        ‖flucAvg Dims.exampleGrow N u (zt 0 u) (mE 0)
          (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) a) ω‖)
      (fun N _ _ _ => firstCellBudgetRho θ N * firstCellBudgetDelta θ N) := by
  let d := Dims.exampleGrow
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hg := firstCellFlucGain_from_localLaw hτ' hθ0 hθ hll
  have hKp : ∀ p : ℕ, 0 ≤ (8 * minorDiffC (2 * p) + 4 : ℝ) := by
    intro p
    have := minorDiffC_nonneg (2 * p)
    linarith
  have hBm : ∀ N, 0 ≤ firstCellBudgetDelta θ N :=
    fun N => (firstCellBudgetDelta_pos hθ0.le N).le
  have hBK : ∀ p N,
      firstCellBudgetB θ p N ≤
        (8 * minorDiffC (2 * p) + 4) * firstCellBudgetDelta θ N := by
    intro p N
    unfold firstCellBudgetB
    apply le_of_eq
    ring
  have hpos : ∀ N, 0 < firstCellBudgetRho θ N * firstCellBudgetDelta θ N := by
    intro N
    have hd : 0 < firstCellBudgetDelta θ N := firstCellBudgetDelta_pos hθ0.le N
    have hr : 0 < firstCellBudgetRho θ N := by
      unfold firstCellBudgetRho
      exact mul_pos (by norm_num) hd
    exact mul_pos hr hd
  have hρ1 : ∀ N, firstCellBudgetRho θ N ≤ 1 := firstCellBudgetRho_le_one hθ0.le
  have hcρB : ∀ N, ((d.W N : ℝ))⁻¹ ≤ firstCellBudgetRho θ N ^ 2 :=
    firstCellBudgetRho_sq_ge_W_inv hθ0.le
  have hcρR : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ firstCellBudgetRho θ N ^ 2 := by
    intro N
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    have h3 : ((3 * d.W N : ℝ))⁻¹ ≤ ((d.W N : ℝ))⁻¹ := by
      rw [inv_le_inv₀ (by linarith) hw]
      linarith
    exact h3.trans (hcρB N)
  constructor
  · exact unifDomIcc_flucAvg_Sblk_iter_budget
      (d := d) (E := 0) (s := firstCellS τ') (t := firstCellT τ')
      (Bp := firstCellBudgetB θ) (Bm := firstCellBudgetDelta θ)
      (Kp := fun p => 8 * minorDiffC (2 * p) + 4)
      (ep := firstCellBudgetRho θ) (by norm_num) ht1 hg hKp hBm hBK hpos hρ1 hcρR
  · exact unifDomIcc_flucAvg_blockAvg_iter_budget
      (d := d) (E := 0) (s := firstCellS τ') (t := firstCellT τ')
      (Bp := firstCellBudgetB θ) (Bm := firstCellBudgetDelta θ)
      (Kp := fun p => 8 * minorDiffC (2 * p) + 4)
      (ep := firstCellBudgetRho θ) (by norm_num) ht1 hg hKp hBm hBK hpos hρ1 hcρB

#print axioms firstCellFlucAvg_budget_family

/-- The movable threshold can be chosen after any requested domination exponent. -/
theorem firstCellBudgetScale_absorb {τ θ : ℝ} (hτ : 0 < τ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ τ / 16) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (τ / 2) *
          (firstCellBudgetRho θ N * firstCellBudgetDelta θ N)
        ≤ (N : ℝ) ^ τ * firstCellPsi N ^ 2 := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_le_rpow 4 (by linarith : 0 < τ / 4)] with N hN h4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) ≤ N := by positivity
  have hN4 : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by
    have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hraw : firstCellBudgetDelta θ N ≤ ((N : ℝ) + 4) ^ θ * firstCellPsi N :=
    min_le_right _ _
  have hpow : ((N : ℝ) + 4) ^ θ ≤ (N : ℝ) ^ (2 * θ) := by
    calc
      ((N : ℝ) + 4) ^ θ ≤ ((N : ℝ) ^ (2 : ℕ)) ^ θ :=
        Real.rpow_le_rpow (by positivity) hN4 hθ0
      _ = (N : ℝ) ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
        ring
  have hδ : firstCellBudgetDelta θ N ≤ (N : ℝ) ^ (2 * θ) * firstCellPsi N :=
    hraw.trans (mul_le_mul_of_nonneg_right hpow (firstCellPsi_pos N).le)
  have hδ0 : 0 ≤ firstCellBudgetDelta θ N :=
    (firstCellBudgetDelta_pos hθ0 N).le
  have hsq : firstCellBudgetDelta θ N ^ 2
      ≤ ((N : ℝ) ^ (2 * θ) * firstCellPsi N) ^ 2 :=
    pow_le_pow_left₀ hδ0 hδ 2
  have hExp : 4 * θ ≤ τ / 4 := by linarith
  have hPowExp : (N : ℝ) ^ (4 * θ) ≤ (N : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn hExp
  have hpow2 : ((N : ℝ) ^ (2 * θ)) ^ 2 = (N : ℝ) ^ (4 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    ring
  change (N : ℝ) ^ (τ / 2) * (4 * firstCellBudgetDelta θ N *
    firstCellBudgetDelta θ N) ≤ (N : ℝ) ^ τ * firstCellPsi N ^ 2
  have hΨsq : 0 ≤ firstCellPsi N ^ 2 := sq_nonneg _
  calc
    (N : ℝ) ^ (τ / 2) * (4 * firstCellBudgetDelta θ N *
        firstCellBudgetDelta θ N)
      = 4 * (N : ℝ) ^ (τ / 2) * firstCellBudgetDelta θ N ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ (τ / 2) *
        (((N : ℝ) ^ (2 * θ) * firstCellPsi N) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (4 * θ) *
        firstCellPsi N ^ 2 := by rw [mul_pow, hpow2]; ring
    _ ≤ 4 * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 4) *
        firstCellPsi N ^ 2 := by gcongr
    _ ≤ (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 2) *
        (N : ℝ) ^ (τ / 4) * firstCellPsi N ^ 2 := by
      gcongr
    _ = (N : ℝ) ^ τ * firstCellPsi N ^ 2 := by
      have hnpos : (0 : ℝ) < N := by linarith
      rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      congr 1; ring

#print axioms firstCellBudgetScale_absorb

/-- An arbitrarily small loss in the threshold disappears in stochastic domination. -/
theorem firstCellBudgetFamily_absorb {V : ℕ → Type*} {τ' : ℝ}
    {ξ : ∀ N, ℝ → V N → Ω Dims.exampleGrow → ℝ}
    (hfamily : ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 32 →
      UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ') ξ
        (fun N _ _ _ => firstCellBudgetRho θ N * firstCellBudgetDelta θ N)) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ') ξ
      (fun N _ _ _ => firstCellPsi N ^ 2) := by
  intro τ hτ D hD
  let θ : ℝ := min (τ / 16) (1 / 32)
  have hθ0 : 0 < θ := lt_min (by linarith) (by norm_num)
  have hθsmall : θ ≤ 1 / 32 := min_le_right _ _
  have hθτ : θ ≤ τ / 16 := min_le_left _ _
  have hsource := hfamily θ hθ0 hθsmall (τ / 2) (by linarith) D hD
  filter_upwards [hsource, firstCellBudgetScale_absorb hτ hθ0.le hθτ]
    with N hN hscale u hu a
  refine (measure_mono ?_).trans (hN u hu a)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt hscale hω

/-- The row and block fluctuation averages satisfy (4.12) at the `Ψ²` scale using
only the Step 2 local law. -/
theorem firstCellFlucAvg_psiSq_of_localLaw {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (i : Dims.exampleGrow.Idx N) ω =>
        ‖flucAvg Dims.exampleGrow N u (zt 0 u) (mE 0)
          (fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j) ω‖)
      (fun N _ _ _ => firstCellPsi N ^ 2) ∧
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (a : ZMod (Dims.exampleGrow.L N)) ω =>
        ‖flucAvg Dims.exampleGrow N u (zt 0 u) (mE 0)
          (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) a) ω‖)
      (fun N _ _ _ => firstCellPsi N ^ 2) := by
  constructor
  · exact firstCellBudgetFamily_absorb (fun θ hθ0 hθsmall =>
      (firstCellFlucAvg_budget_family hτ' hθ0 hθsmall hll).1)
  · exact firstCellBudgetFamily_absorb (fun θ hθ0 hθsmall =>
      (firstCellFlucAvg_budget_family hτ' hθ0 hθsmall hll).2)

#print axioms firstCellBudgetFamily_absorb
#print axioms firstCellFlucAvg_psiSq_of_localLaw

/-- The fixed-time row and block inputs for slot 5 follow from the local law. -/
theorem firstCellFlucFix_of_localLaw {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (i : Dims.exampleGrow.Idx N) ω =>
        ‖∑ k, (Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i k : ℂ) *
          ((green (Hflow Dims.exampleGrow N u ω) (zt 0 u) k k - mE 0) -
            condExpDiag Dims.exampleGrow N u (zt 0 u) (mE 0) k ω)‖)
      (fun N u _ ω => Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ∧
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (a : ZMod (Dims.exampleGrow.L N)) ω =>
        ‖∑ k, (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) a k : ℂ) *
          ((green (Hflow Dims.exampleGrow N u ω) (zt 0 u) k k - mE 0) -
            condExpDiag Dims.exampleGrow N u (zt 0 u) (mE 0) k ω)‖)
      (fun N u _ ω => Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
  let d := Dims.exampleGrow
  have hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ')
        (firstCellBudgetDelta (1 / 32))) :=
    firstCellBudgetDelta_highProb hτ' (by norm_num) (by norm_num) hll
  have hδ1 : ∀ᶠ N : ℕ in atTop, firstCellBudgetDelta (1 / 32) N ≤ 1 / 2 :=
    Filter.Eventually.of_forall (fun N =>
      (firstCellBudgetDelta_le_quarter (1 / 32) N).trans (by norm_num))
  obtain ⟨_, _, _, _, _, _, hΨW, _, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  have hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * firstCellPsi N ^ 2 ≤ (N : ℝ) ^ τ := by
    intro τ hτ
    simp only [pow_two]
    change ∀ᶠ N : ℕ in atTop,
      4 * ((Dims.exampleGrow.W N : ℕ) : ℝ) *
        (firstCellPsi N * firstCellPsi N) ≤ (N : ℝ) ^ τ
    exact hΨW τ hτ
  have havg := firstCellFlucAvg_psiSq_of_localLaw hτ' hll
  constructor
  · exact havg.1.trans
      (unifDomIcc_const_Lmax (V := fun N => d.Idx N) d (by norm_num) hδ1 hΩ hΦW)
  · exact havg.2.trans
      (unifDomIcc_const_Lmax (V := fun N => ZMod (d.L N)) d (by norm_num) hδ1 hΩ hΦW)

#print axioms firstCellFlucFix_of_localLaw

/-- Slot 5 on the first cell requires the Step 2 local law alone. -/
theorem first_cell_eq45FlowInputs_of_localLaw' {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    RBM.Eq45FlowInputs (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') := by
  let d := Dims.exampleGrow
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  obtain ⟨hΨpos, _, _, hΨ1, hΨlow, hΨlowLL, hΨW,
    hmargin, hδ1, hμ0, hμ1, hμnet, hfine, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, hKc, hKtot, hEnv⟩ := first_cell_polynomial_regime d τ'
  have hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta) :=
    highProb_goodSetFlow_of_localLaw d (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num) hs0 ht1 hst (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 2) hKbig (fun N => (hΨpos N).le)
      hΨlowLL hll hmargin
  let x : ∀ N, RBM.TimeIcc (firstCellS τ') (firstCellT τ') N → Ω d → d.Idx N → ℂ :=
    fun N u ω i => condExpDiag d N (u : ℝ) (zt 0 (u : ℝ)) (mE 0) i ω
  have hIBP : IBPFlow (sample d) 0 (firstCellS τ') (firstCellT τ') x := by
    exact ibpFlow_of_unifDom'
      (y := fun N u ω i => condExpDiag d N u (zt 0 u) (mE 0) i ω)
      d (by norm_num) hs0 ht1 hst (by norm_num) hμ0 hδ1 hμ1 hμnet hfine hΩ
      (holIBP_of_inputs (δ := firstCellDelta) d (by norm_num) hs0 ht1 hKc hKtot)
      (unifDomIcc_condExpDiag_flow (δ := firstCellDelta) d (by norm_num)
        hs0 ht1 (fun N => (hΨpos N).le) (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) ≤ 2) hEnv hΨlow hΨ1 hδ1 hΨW hΩ hll)
  have hfix := firstCellFlucFix_of_localLaw hτ' hll
  have hRow : FlucRowFlow (sample d) 0 (firstCellS τ') (firstCellT τ') x := by
    exact flucRowFlow_of_unifDom'
      (y := fun N u ω i => condExpDiag d N u (zt 0 u) (mE 0) i ω)
      d (by norm_num) hs0 ht1 hst (by norm_num) hμ0 hδ1 hμ1 hμnet hfine hΩ
      (holRow_of_inputs (δ := firstCellDelta) d (by norm_num) hs0 ht1 hKc hKtot)
      hfix.1
  have hBlk : FlucBlkFlow (sample d) 0 (firstCellS τ') (firstCellT τ') x := by
    exact flucBlkFlow_of_unifDom'
      (y := fun N u ω i => condExpDiag d N u (zt 0 u) (mE 0) i ω)
      d (by norm_num) hs0 ht1 hst (by norm_num) hμ0 hδ1 hμ1 hμnet hfine hΩ
      (holBlk_of_inputs (δ := firstCellDelta) d (by norm_num) hs0 ht1 hKc hKtot)
      hfix.2
  exact ⟨x, hIBP, hRow, hBlk⟩

/-- The fifth slot in the merged assembly, with no named gain or budget premise. -/
theorem first_cell_step5_of_localLaw' {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    RBM.StepGlue.Eq45Flow (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') := by
  apply RBM.eq45Flow_of_eq45FlowInputs (sample Dims.exampleGrow)
    (κ := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro N
    change 0 ≤ gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  · exact first_cell_eq45FlowInputs_of_localLaw' hτ' hll

#print axioms first_cell_eq45FlowInputs_of_localLaw'
#print axioms first_cell_step5_of_localLaw'

/-- The produced fifth slot and the inhabited, positive-length first-cell event coexist. -/
theorem first_cell_step5_nondegenerate_of_localLaw {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    RBM.StepGlue.Eq45Flow (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') ∧
    ∀ᶠ N : ℕ in atTop,
      firstCellS τ' N < firstCellT τ' N ∧
        (flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
          firstCellDelta N).Nonempty :=
  ⟨first_cell_step5_of_localLaw' hτ' hll,
    first_cell_flowNetEvent_nonempty_of_localLaw hτ' hll⟩

#print axioms first_cell_step5_nondegenerate_of_localLaw

end RBM.Gauss
