/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowGrid

/-!
# The first-cell local-law threshold bridge — T317

The same-window Step 2 `LocalLawFlow` is an explicit input.  The deterministic first-cell
scale comparison and a loss of half the stochastic-domination exponent convert it to the
selected threshold `firstCellPsi` used by the fifth-slot producer.
-/

namespace RBM.Gauss

open Filter MeasureTheory

#check RBM.LocalLawFlow
#check RBM.Gauss.LocalLawUnifIcc
#check RBM.Gauss.firstCellPsi
#check RBM.Gauss.first_cell_window_nondegenerate
#check RBM.Gauss.localLawUnifIcc_of_localLawFlow

/-- The actual first-cell scale stays at least half the initial bandwidth. -/
theorem firstCell_scale_ge_half {τ' : ℝ} (N : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N)) :
    (Dims.exampleGrow.W N : ℝ) / 2 ≤ (band Dims.exampleGrow).scale 0 N u := by
  let d := Dims.exampleGrow
  have hu0 : 0 ≤ u := by
    have hs : firstCellS τ' N = 0 := by
      unfold firstCellS
      exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith [hu.1]
  have hu2 : u ≤ 1 / 2 := by
    apply hu.2.trans
    change gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
    exact gridT_le (1 / 2 : ℝ) 1
  have hu1 : u < 1 := by linarith
  have hL : 1 ≤ d.L N := by have := d.three_le_L N; omega
  have hℓ : 1 ≤ ellHat (d.L N) (u : ℂ) :=
    one_le_ellHat_of_nonneg hL hu0 hu1
  have hη : etaT 0 u = 1 - u := by
    have hs : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp [etaT, mE_im, hs]
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hWℓ : (d.W N : ℝ) ≤ (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) := by
    nlinarith [mul_nonneg hW.le (sub_nonneg.mpr hℓ)]
  have hη2 : (1 / 2 : ℝ) ≤ 1 - u := by linarith
  change (d.W N : ℝ) / 2 ≤
    (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) * etaT 0 u
  rw [hη]
  calc
    (d.W N : ℝ) / 2 = (d.W N : ℝ) * (1 / 2 : ℝ) := by ring
    _ ≤ ((d.W N : ℝ) * ellHat (d.L N) (u : ℂ)) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hWℓ (by norm_num)
    _ ≤ ((d.W N : ℝ) * ellHat (d.L N) (u : ℂ)) * (1 - u) :=
      mul_le_mul_of_nonneg_left hη2 (mul_nonneg hW.le (by linarith [hℓ]))

/-- The source local-law scale is at most four times the selected first-cell threshold. -/
theorem firstCell_localLawScale_le_psi {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N)) :
    ((band Dims.exampleGrow).scale 0 N u)⁻¹ ^ ((1 : ℝ) / 2) ≤
      4 * firstCellPsi N := by
  let d := Dims.exampleGrow
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hA := firstCell_scale_ge_half N hu
  have hApos : 0 < (band d).scale 0 N u :=
    (half_pos hW).trans_le hA
  have hi : ((band d).scale 0 N u)⁻¹ ≤ ((d.W N : ℝ) / 2)⁻¹ :=
    inv_anti₀ (half_pos hW) hA
  have hhalf : ((d.W N : ℝ) / 2)⁻¹ = 2 * (d.W N : ℝ)⁻¹ := by
    field_simp
  have hΨW : (d.W N : ℝ)⁻¹ ≤ 4 * firstCellPsi N ^ 2 := by
    obtain ⟨_, _, h, _⟩ := first_cell_joint_grid_scales hτ'
    change (Dims.exampleGrow.W N : ℝ)⁻¹ ≤ 4 * firstCellPsi N ^ 2
    simpa [firstCellPsi] using h N
  have hΨ : 0 ≤ firstCellPsi N := by
    unfold firstCellPsi
    positivity
  have hr0 : 0 ≤ ((band d).scale 0 N u)⁻¹ ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (inv_nonneg.mpr hApos.le) _
  have hrsq : (((band d).scale 0 N u)⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 =
      ((band d).scale 0 N u)⁻¹ := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (inv_nonneg.mpr hApos.le)]
  rw [hhalf] at hi
  nlinarith [sq_nonneg (firstCellPsi N), hi, hΨW, hrsq]

/-- Step 2's same-window local law at its natural scale reaches the exact threshold
selected by the first-cell fifth-slot producer.  The fixed factor four is absorbed by
halving each requested stochastic-domination exponent. -/
theorem firstCell_localLawUnifIcc_of_localLawFlow {τ' : ℝ} (hτ' : 0 < τ')
    (hLL : RBM.LocalLawFlow (sample Dims.exampleGrow) 0
      (firstCellS τ') (firstCellT τ')) :
    LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi := by
  intro τ hτ D hD
  have hLL' := hLL (τ / 2) (half_pos hτ) D hD
  have hfour : ∀ᶠ N : ℕ in atTop, 4 ≤ (N : ℝ) ^ (τ / 2) :=
    eventually_le_rpow 4 (half_pos hτ)
  filter_upwards [hLL', hfour, eventually_ge_atTop 1] with N hN h4 hN1 u hu ij
  have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hΨ : 0 ≤ firstCellPsi N := by unfold firstCellPsi; positivity
  have hscale := firstCell_localLawScale_le_psi hτ' N hu
  have hp : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg hn.le _
  have hpower : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    calc
      (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2 + τ / 2) := by congr 1; ring
      _ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
        Real.rpow_add hn (τ / 2) (τ / 2)
  have hthreshold : (N : ℝ) ^ (τ / 2) *
      ((band Dims.exampleGrow).scale 0 N u)⁻¹ ^ ((1 : ℝ) / 2) ≤
      (N : ℝ) ^ τ * firstCellPsi N := by
    have hsq : 4 * (N : ℝ) ^ (τ / 2) ≤
        (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
      nlinarith [mul_nonneg hp (sub_nonneg.mpr h4)]
    calc
      (N : ℝ) ^ (τ / 2) *
          ((band Dims.exampleGrow).scale 0 N u)⁻¹ ^ ((1 : ℝ) / 2)
          ≤ (N : ℝ) ^ (τ / 2) * (4 * firstCellPsi N) :=
            mul_le_mul_of_nonneg_left hscale hp
      _ = (4 * (N : ℝ) ^ (τ / 2)) * firstCellPsi N := by ring
      _ ≤ ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) * firstCellPsi N :=
        mul_le_mul_of_nonneg_right hsq hΨ
      _ = (N : ℝ) ^ τ * firstCellPsi N := by rw [hpower]
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  refine ⟨(⟨u, hu⟩, ij), ?_⟩
  change (N : ℝ) ^ (τ / 2) *
    ((band Dims.exampleGrow).scale 0 N u)⁻¹ ^ ((1 : ℝ) / 2) <
    (sample Dims.exampleGrow).llErr 0 N u ω ij
  rw [(sample Dims.exampleGrow).llErr_eq N u ω ij]
  exact lt_of_le_of_lt hthreshold hω

/-- The conditional bridge runs on a positive first cell with a strictly positive
physical scale and a positive selected threshold. -/
theorem firstCell_localLaw_bridge_nondegenerate {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      firstCellS τ' N < firstCellT τ' N ∧
      0 < (band Dims.exampleGrow).scale 0 N (firstCellS τ' N) ∧
      0 < firstCellPsi N := by
  filter_upwards [first_cell_window_nondegenerate Dims.exampleGrow hτ'] with N hst
  have hmem : firstCellS τ' N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) :=
    ⟨le_rfl, hst.le⟩
  have hge := firstCell_scale_ge_half N hmem
  have hw : (0 : ℝ) < Dims.exampleGrow.W N := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  refine ⟨hst, (half_pos hw).trans_le hge, ?_⟩
  unfold firstCellPsi
  positivity

#print axioms firstCell_scale_ge_half
#print axioms firstCell_localLawScale_le_psi
#print axioms firstCell_localLawUnifIcc_of_localLawFlow
#print axioms firstCell_localLaw_bridge_nondegenerate

end RBM.Gauss
