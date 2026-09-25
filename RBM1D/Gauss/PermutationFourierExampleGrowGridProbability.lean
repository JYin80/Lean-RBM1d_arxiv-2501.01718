/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierFiniteGridProbability
import RBM1D.Gauss.PermutationFourierExampleGrowExponent
import RBM1D.Gauss.PermutationFourierClosedTimeGrid
import RBM1D.Defs.SemicircleQuantileCells
import RBM1D.Defs.SemicircleFlowKernelTimeModulus

/-!
# Growing-model finite-grid Fourier probability

For the actual midpoint-quantile flow-kernel table on the closed-time grid,
the same uniform permutation obeys every strict nonzero-mode bound with
probability at least `1 - 8 N^(-14)` eventually. This is a finite uniform-
permutation estimate, not an all-time or Gaussian event estimate and not the
paper's local laws (2.3)--(2.4).
-/

open Filter MeasureTheory

namespace RBM.Gauss

/-- On `[0,1/2]` the flow kernel has norm at most two; the lower bound on its
denominator is uniform in the midpoint quantile. -/
private theorem semicircleFlowKernel_norm_le_two (u x : ℝ) (hu : u ≤ 1 / 2) :
    ‖semicircleFlowKernel u x‖ ≤ 2 := by
  have hb : (0 : ℝ) < 1 - u := by linarith
  have hden := semicircleFlowResolvent_denominator_gap u x hu
  have hden' : (0 : ℝ) <
      ‖((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)‖ :=
    lt_of_lt_of_le hb hden
  have hinv : ‖semicircleFlowKernel u x‖ ≤ (1-u)⁻¹ := by
    rw [semicircleFlowKernel, norm_inv]
    exact (inv_le_inv₀ hden' hb).2 hden
  have hhalf : (1 / 2 : ℝ) ≤ 1-u := by linarith
  have hle : (1-u)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
    (inv_le_inv₀ hb (by norm_num)).2 hhalf
  calc
    ‖semicircleFlowKernel u x‖ ≤ (1-u)⁻¹ := hinv
    _ ≤ (1 / 2 : ℝ)⁻¹ := hle
    _ = 2 := by norm_num

/-- Eventually, for the actual growing dimensions, the midpoint-quantile
flow-kernel table at the closed-time grid nodes has one common permutation
satisfying every strict nonzero-mode Fourier bound at threshold
`64 * sqrt (log N / W_N)`, with probability at least `1 - 8 N^(-14)`.
The existential `hW` packages the eventual fact that the finite grid has a
nonzero canonical mode. -/
theorem permutationFourierExampleGrow_eventually_grid_good_probability :
    ∀ᶠ N : ℕ in atTop,
      ∃ hW : 2 ≤ Dims.exampleGrow.W N,
        1 ≤ permutationFourierExampleGrowGridCount N ∧
        0 < permutationFourierExampleGrowThreshold N ∧
        1 - 8 * (N : ℝ) ^ (-14 : ℝ) ≤
          (uniformPerm (Dims.exampleGrow.W N)).real
            (permutationFourierGridGoodSet
              (Dims.exampleGrow.W N)
              (permutationFourierExampleGrowGridCount N) hW
              (fun t j => semicircleFlowKernel
                (permutationFourierClosedTimeGrid
                  (permutationFourierExampleGrowMesh N) t)
                (semicircleLambda (Dims.exampleGrow.W N)
                  (by omega)
                  j.val j.isLt))
              (permutationFourierExampleGrowThreshold N)) := by
  filter_upwards [permutationFourierExampleGrow_eventually_bounds,
    permutationFourierExampleGrow_eventually_exponent_and_premise] with N hgrid hnum
  let W := Dims.exampleGrow.W N
  let T := permutationFourierExampleGrowGridCount N
  let h := permutationFourierExampleGrowMesh N
  let r := permutationFourierExampleGrowThreshold N
  rcases hnum with ⟨hLNat, hW, hTpos, hKpos, hr, hid, herr, hsmall, hprem⟩
  have hT : 1 ≤ T := by omega
  have hh : 0 < h := hgrid.1
  let lam : Fin W → ℝ := fun j =>
    semicircleLambda W (by omega) j.val j.isLt
  let x : Fin T → Fin W → ℂ := fun t j =>
    semicircleFlowKernel (permutationFourierClosedTimeGrid h t) (lam j)
  have hx : ∀ t j, ‖x t j‖ ≤ 2 := by
    intro t j
    exact semicircleFlowKernel_norm_le_two _ _
      (permutationFourierClosedTimeGrid_range h hh t).2
  have hprob := uniformPerm_permutationFourierGridGoodSet_prob_lower_bound
    W T hW hT x hx r hr
  have hL : 1 ≤ Dims.exampleGrow.L N := by omega
  have hcount : T * (W - 1) ≤ permutationFourierExampleGrowConstraintCount N := by
    unfold permutationFourierExampleGrowConstraintCount
    calc
      T * (W - 1) = 1 * ((W - 1) * T) := by ring
      _ ≤ Dims.exampleGrow.L N * ((W - 1) * T) := Nat.mul_le_mul_right _ hL
      _ = Dims.exampleGrow.L N * (W - 1) * T := by ring
  have hcountR : ((T * (W - 1) : ℕ) : ℝ) ≤
      (permutationFourierExampleGrowConstraintCount N : ℝ) := by
    exact_mod_cast hcount
  have htail :
      4 * ((T * (W - 1) : ℕ) : ℝ) * Real.exp (-(W : ℝ) * r ^ 2 / 256) ≤
        8 * (N : ℝ) ^ (-14 : ℝ) := by
    calc
      _ ≤ 4 * (permutationFourierExampleGrowConstraintCount N : ℝ) *
          Real.exp (-(W : ℝ) * r ^ 2 / 256) := by gcongr
      _ ≤ 8 * (N : ℝ) ^ (-14 : ℝ) := by
        simpa [W, r] using herr
  have hprob' :
      1 - 4 * ((T * (W - 1) : ℕ) : ℝ) * Real.exp (-(W : ℝ) * r ^ 2 / 256) ≤
        (uniformPerm W).real (permutationFourierGridGoodSet W T hW x r) := by
    simpa [W, T, x, r] using hprob
  refine ⟨hW, hT, hr, ?_⟩
  change 1 - 8 * (N : ℝ) ^ (-14 : ℝ) ≤
    (uniformPerm W).real (permutationFourierGridGoodSet W T hW x r)
  linarith

#print axioms permutationFourierExampleGrow_eventually_grid_good_probability

end RBM.Gauss
