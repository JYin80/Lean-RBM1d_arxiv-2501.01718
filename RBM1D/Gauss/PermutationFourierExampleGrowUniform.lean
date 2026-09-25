/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierFiniteExistence
import RBM1D.Gauss.PermutationFourierExampleGrowExponent
import RBM1D.Gauss.PermutationFourierClosedTimeInterpolation
import RBM1D.Defs.SemicircleQuantileCells

/-!
# One growing-model permutation for all positive-phase Fourier modes and times

This finite deterministic auxiliary uses the actual semicircle midpoint table.
It does not assert a matrix or Gaussian local law (2.3)--(2.4), nor event (4.1).
-/

set_option autoImplicit false

namespace RBM.Gauss

/-- The scalar flow kernel has norm at most two throughout the closed half-time
interval. The denominator bound remains valid at both endpoints. -/
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

/-- For every sufficiently large growing dimension, one permutation controls all
nonzero canonical positive-phase Fourier modes at every time in `[0, 1/2]`.
The permutation is chosen before the time and mode. -/
theorem permutationFourierExampleGrow_eventually_uniform :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∃ π : PermΩ (Dims.exampleGrow.W N),
        ∀ u : ℝ, 0 ≤ u → u ≤ 1/2 →
          ∀ q : Fin (Dims.exampleGrow.W N),
            q ≠ (⟨0, by have h := Dims.exampleGrow.W_pos N; omega⟩ :
              Fin (Dims.exampleGrow.W N)) →
            ‖permutationFourierSum (Dims.exampleGrow.W N)
              (fun j => semicircleFlowKernel u
                (semicircleLambda (Dims.exampleGrow.W N)
                  (by have h := Dims.exampleGrow.W_pos N; omega)
                  j.val j.isLt))
              (permutationFourierCharacter (Dims.exampleGrow.W N) q) π‖ <
                76 * Real.sqrt (Real.log N / (Dims.exampleGrow.W N : ℝ)) := by
  filter_upwards [permutationFourierExampleGrow_eventually_bounds,
    permutationFourierExampleGrow_eventually_exponent_and_premise] with N hmesh hnum
  let W := Dims.exampleGrow.W N
  let h := permutationFourierExampleGrowMesh N
  let T := permutationFourierExampleGrowGridCount N
  let r := permutationFourierExampleGrowThreshold N
  have hW : 2 ≤ W := hnum.2.1
  have hW1 : 1 ≤ W := by omega
  have hT : 1 ≤ T := by
    have ht : 0 < T := hnum.2.2.1
    omega
  have hh : 0 < h := hmesh.1
  let lam : Fin W → ℝ := fun j => semicircleLambda W hW1 j.val j.isLt
  have hlam : ∀ j : Fin W, |lam j| ≤ 2 := by
    intro j
    have hj := (semicircleMidpointQuantile W hW1 j.val j.isLt).property
    change -2 ≤ lam j ∧ lam j ≤ 2 at hj
    exact abs_le.mpr hj
  let x : Fin T → Fin W → ℂ :=
    fun t j => semicircleFlowKernel (permutationFourierClosedTimeGrid h t) (lam j)
  have hx : ∀ t j, ‖x t j‖ ≤ 2 := by
    intro t j
    exact semicircleFlowKernel_norm_le_two _ _ (permutationFourierClosedTimeGrid_range h hh t).2
  have hprem : 4 * ((T * (W - 1) : ℕ) : ℝ) *
      Real.exp (-(W : ℝ) * r ^ 2 / 256) < 1 := by
    simpa only [T, W, r] using hnum.2.2.2.2.2.2.2.2
  obtain ⟨π, hnode⟩ :=
    exists_permutationFourierSum_norm_lt_of_union_bound W T hW hT x hx r
      hnum.2.2.2.2.1 hprem
  refine ⟨π, ?_⟩
  intro u hu0 hu1 q hq
  have hχ : ∀ j : Fin W, ‖permutationFourierCharacter W q j‖ ≤ 1 := by
    intro j
    rw [permutationFourierCharacter_norm_eq_one]
  have hgrid : ∀ t : Fin (permutationFourierClosedTimeGridCount h),
      ‖permutationFourierSum W
        (fun k => semicircleFlowKernel (permutationFourierClosedTimeGrid h t) (lam k))
        (permutationFourierCharacter W q) π‖ < r := by
    intro t
    exact hnode t q hq
  have hi := permutationFourierClosedTimeInterpolation W h hW1 hh lam
    (permutationFourierCharacter W q) hlam hχ π r hgrid u hu0 hu1
  have hsum : r + 12 * Real.sqrt h =
      76 * Real.sqrt (Real.log N / (W : ℝ)) := by
    dsimp [r, h, permutationFourierExampleGrowThreshold,
      permutationFourierExampleGrowMesh, W]
    ring
  exact hi.trans_eq hsum

#print axioms permutationFourierExampleGrow_eventually_uniform

end RBM.Gauss
