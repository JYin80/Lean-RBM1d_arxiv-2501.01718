/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DimsExample
import RBM1D.Gauss.PermutationFourierClosedTimeGrid
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual size of the closed Fourier grid for `Dims.exampleGrow`

This deterministic specialization uses the mesh `log N / W_N` and the exact
clipped-grid count.  Its conservative constraint count includes `L_N` blocks,
`W_N - 1` nonzero modes, and every grid time.  The estimates hold eventually,
as do the nondegeneracy bounds.  No Gaussian local law is asserted here.
-/

namespace RBM.Gauss

open Filter

/-- The Fourier time mesh `h_N = log N / W_N` for the growing dimension witness. -/
noncomputable def permutationFourierExampleGrowMesh (N : ℕ) : ℝ :=
  Real.log N / (Dims.exampleGrow.W N : ℝ)

/-- The exact number of clipped time nodes for `h_N`. -/
noncomputable def permutationFourierExampleGrowGridCount (N : ℕ) : ℕ :=
  permutationFourierClosedTimeGridCount (permutationFourierExampleGrowMesh N)

/-- A conservative count of block, nonzero-mode, and time constraints. -/
noncomputable def permutationFourierExampleGrowConstraintCount (N : ℕ) : ℕ :=
  Dims.exampleGrow.L N * (Dims.exampleGrow.W N - 1) *
    permutationFourierExampleGrowGridCount N

private theorem eventually_mesh_bounds :
    ∀ᶠ N : ℕ in atTop,
      0 < permutationFourierExampleGrowMesh N ∧
        permutationFourierExampleGrowMesh N ≤ 1 / 2 := by
  have hlo : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ)‖ ≤ (1 / 2 : ℝ) *
        ‖(N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8)‖ :=
    ((isLittleO_log_rpow_atTop
      (show (0 : ℝ) < 1 / 2 + 1 / 8 by norm_num)).def
      (show (0 : ℝ) < 1 / 2 by norm_num)) |>
        tendsto_natCast_atTop_atTop.eventually
  have hlog : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [hlo, hlog, Dims.bandwidth_grow] with N hlo hlog hband
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hpow : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) := by positivity
  have hlog' : Real.log (N : ℝ) ≤
      (1 / 2 : ℝ) * ((N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog.le, abs_of_nonneg hpow] using hlo
  constructor
  · exact div_pos hlog hW
  · unfold permutationFourierExampleGrowMesh
    apply (div_le_iff₀ hW).2
    change (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤
      (Dims.exampleGrow.W N : ℝ) at hband
    nlinarith

private theorem eventually_log_one :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log N :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1

private theorem gridCount_le_two_width (N : ℕ) (ha : 1 ≤ Real.log N) :
    permutationFourierExampleGrowGridCount N ≤
      2 * Dims.exampleGrow.W N := by
  unfold permutationFourierExampleGrowGridCount permutationFourierExampleGrowMesh
  exact permutationFourierClosedTimeGridCount_div_le_two_width
    (Dims.exampleGrow.W N) (Real.log N)
    (Dims.exampleGrow.W_pos N) ha

private theorem constraintCount_le_two_N_sq (N : ℕ)
    (hdim : Dims.exampleGrow.W N * Dims.exampleGrow.L N ≤ N)
    (hT : permutationFourierExampleGrowGridCount N ≤
      2 * Dims.exampleGrow.W N) :
    permutationFourierExampleGrowConstraintCount N ≤ 2 * N ^ 2 := by
  have hL : 0 < Dims.exampleGrow.L N := by
    have := Dims.exampleGrow.three_le_L N
    omega
  have hW : 0 < Dims.exampleGrow.W N := Dims.exampleGrow.W_pos N
  have hWN : Dims.exampleGrow.W N ≤ N := by
    have hprod : Dims.exampleGrow.W N ≤
        Dims.exampleGrow.W N * Dims.exampleGrow.L N := by nlinarith
    omega
  have h1 : Dims.exampleGrow.L N * (Dims.exampleGrow.W N - 1) ≤
      Dims.exampleGrow.L N * Dims.exampleGrow.W N :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hdim' : Dims.exampleGrow.L N * Dims.exampleGrow.W N ≤ N := by
    simpa only [Nat.mul_comm] using hdim
  unfold permutationFourierExampleGrowConstraintCount
  calc
    Dims.exampleGrow.L N * (Dims.exampleGrow.W N - 1) *
        permutationFourierExampleGrowGridCount N
        ≤ (Dims.exampleGrow.L N * Dims.exampleGrow.W N) *
            (2 * Dims.exampleGrow.W N) := Nat.mul_le_mul h1 hT
    _ ≤ N * (2 * N) := Nat.mul_le_mul hdim' (Nat.mul_le_mul_left 2 hWN)
    _ = 2 * N ^ 2 := by ring

/-- Eventually the mesh is positive and at most `1/2`, the exact clipped grid
has at most `2W_N` nodes, and the conservative constraint count is at most `2N²`. -/
theorem permutationFourierExampleGrow_eventually_bounds :
    ∀ᶠ N : ℕ in atTop,
      0 < permutationFourierExampleGrowMesh N ∧
      permutationFourierExampleGrowMesh N ≤ 1 / 2 ∧
      permutationFourierExampleGrowGridCount N ≤ 2 * Dims.exampleGrow.W N ∧
      permutationFourierExampleGrowConstraintCount N ≤ 2 * N ^ 2 := by
  filter_upwards [eventually_mesh_bounds, eventually_log_one,
    Dims.exampleGrow.dim] with N hh ha hdim
  exact ⟨hh.1, hh.2, gridCount_le_two_width N ha,
    constraintCount_le_two_N_sq N hdim.1 (gridCount_le_two_width N ha)⟩

/-- Eventually there are at least three blocks, two coordinates per block,
one time node, and one actual block/mode/time constraint. -/
theorem permutationFourierExampleGrow_eventually_nondegenerate :
    ∀ᶠ N : ℕ in atTop,
      3 ≤ Dims.exampleGrow.L N ∧
      2 ≤ Dims.exampleGrow.W N ∧
      0 < permutationFourierExampleGrowGridCount N ∧
      0 < permutationFourierExampleGrowConstraintCount N := by
  have hw : ∀ᶠ N : ℕ in atTop, 2 ≤ Dims.exampleGrow.W N := by
    simpa only [Dims.exampleGrow_W] using
      Dims.tendsto_growW.eventually_ge_atTop 2
  filter_upwards [hw] with N hw
  have hl := Dims.exampleGrow.three_le_L N
  have ht : 0 < permutationFourierExampleGrowGridCount N := by
    unfold permutationFourierExampleGrowGridCount
      permutationFourierClosedTimeGridCount
    omega
  refine ⟨hl, hw, ht, ?_⟩
  unfold permutationFourierExampleGrowConstraintCount
  have : 0 < Dims.exampleGrow.W N - 1 := by omega
  positivity

#print axioms permutationFourierExampleGrow_eventually_bounds
#print axioms permutationFourierExampleGrow_eventually_nondegenerate

end RBM.Gauss
