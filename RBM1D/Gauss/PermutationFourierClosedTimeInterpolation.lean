/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierFlowTimeModulus
import RBM1D.Gauss.PermutationFourierClosedTimeGrid

/-! # Closed-time interpolation for a finite permutation Fourier sum

This deterministic lemma transfers strict bounds at every node of the actual
clipped grid to a uniform bound on the closed time interval. It supplies no
node bounds or probabilistic input and proves neither Gaussian local law
(2.3)--(2.4) of the prescribed paper.
-/

namespace RBM.Gauss

/-- Strict bounds at every actual node of the clipped time grid transfer to
the same fixed permutation at every time, with the square-root mesh loss. -/
theorem permutationFourierClosedTimeInterpolation
    (W : ℕ) (h : ℝ) (hW : 1 ≤ W) (hh : 0 < h)
    (lam : Fin W → ℝ) (χ : Fin W → ℂ)
    (hlam : ∀ j, |lam j| ≤ 2) (hχ : ∀ j, ‖χ j‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) (r : ℝ)
    (hgrid : ∀ j : Fin (permutationFourierClosedTimeGridCount h),
      ‖permutationFourierSum W
        (fun k => semicircleFlowKernel
          (permutationFourierClosedTimeGrid h j) (lam k)) χ π‖ < r)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ‖permutationFourierSum W (fun k => semicircleFlowKernel u (lam k)) χ π‖ <
      r + 12 * Real.sqrt h := by
  obtain ⟨j, hj⟩ := permutationFourierClosedTimeGrid_coverage h u hh hu0 hu1
  rcases permutationFourierClosedTimeGrid_range h hh j with ⟨hj0, hj1⟩
  have hmod := norm_permutationFourierSum_flow_time_modulus
    W hW lam χ hlam hχ π u (permutationFourierClosedTimeGrid h j)
    hu0 hj0 hu1 hj1
  have hsqrt : Real.sqrt |u - permutationFourierClosedTimeGrid h j| ≤
      Real.sqrt h := Real.sqrt_le_sqrt (le_of_lt hj)
  have hmod' :
      ‖permutationFourierSum W (fun k => semicircleFlowKernel u (lam k)) χ π -
        permutationFourierSum W
          (fun k => semicircleFlowKernel (permutationFourierClosedTimeGrid h j)
            (lam k)) χ π‖ ≤ 12 * Real.sqrt h := by
    exact hmod.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  calc
    ‖permutationFourierSum W (fun k => semicircleFlowKernel u (lam k)) χ π‖ =
        ‖(permutationFourierSum W
            (fun k => semicircleFlowKernel u (lam k)) χ π -
          permutationFourierSum W
            (fun k => semicircleFlowKernel (permutationFourierClosedTimeGrid h j)
              (lam k)) χ π) +
          permutationFourierSum W
            (fun k => semicircleFlowKernel (permutationFourierClosedTimeGrid h j)
              (lam k)) χ π‖ := by rw [sub_add_cancel]
    _ ≤ ‖permutationFourierSum W
          (fun k => semicircleFlowKernel u (lam k)) χ π -
        permutationFourierSum W
          (fun k => semicircleFlowKernel (permutationFourierClosedTimeGrid h j)
            (lam k)) χ π‖ +
        ‖permutationFourierSum W
          (fun k => semicircleFlowKernel (permutationFourierClosedTimeGrid h j)
            (lam k)) χ π‖ := norm_add_le _ _
    _ < 12 * Real.sqrt h + r := add_lt_add_of_le_of_lt hmod' (hgrid j)
    _ = r + 12 * Real.sqrt h := by ring

/-- A concrete all-node strict-bound witness at width one. The grid nodes are
`0` and `1/2`; their sum norms are `1` and `2`, below `r=3`. The endpoint
values are `i` and `2i`, so this example is nonconstant. -/
theorem permutationFourierClosedTimeInterpolation_W1_witness :
    (∀ j : Fin 1, |(fun _ : Fin 1 => (0 : ℝ)) j| ≤ 2) ∧
    (∀ j : Fin 1, ‖(fun _ : Fin 1 => (1 : ℂ)) j‖ ≤ 1) ∧
    (∀ j : Fin (permutationFourierClosedTimeGridCount (1 / 2 : ℝ)),
      ‖permutationFourierSum 1
        (fun k => semicircleFlowKernel
          (permutationFourierClosedTimeGrid (1 / 2 : ℝ) j)
          ((fun _ : Fin 1 => (0 : ℝ)) k))
        (fun _ => (1 : ℂ)) (Equiv.refl _)‖ < 3) ∧
    permutationFourierSum 1 (fun _ => semicircleFlowKernel 0 0)
      (fun _ => (1 : ℂ)) (Equiv.refl _) = Complex.I ∧
    permutationFourierSum 1 (fun _ => semicircleFlowKernel (1 / 2) 0)
      (fun _ => (1 : ℂ)) (Equiv.refl _) = 2 * Complex.I ∧
    Complex.I ≠ 2 * Complex.I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    have hbound : j.val < 2 := by
      simpa [permutationFourierClosedTimeGridCount] using j.isLt
    by_cases hj : j.val = 0
    · have hEq : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [hEq]
      norm_num [permutationFourierClosedTimeGrid,
        permutationFourierClosedTimeGridCount, permutationFourierSum,
        Fin.sum_univ_one, semicircleFlowKernel,
        semicircleFlowResolvent_half_at_zero]
    · have hj1 : j.val = 1 := by omega
      have hEq : j = ⟨1, by omega⟩ := Fin.ext hj1
      rw [hEq]
      norm_num [permutationFourierClosedTimeGrid,
        permutationFourierClosedTimeGridCount, permutationFourierSum,
        Fin.sum_univ_one, semicircleFlowKernel,
        semicircleFlowResolvent_half_at_zero]
  · norm_num [permutationFourierSum, Fin.sum_univ_one,
      semicircleFlowKernel, semicircleFlowResolvent_half_at_zero]
  · norm_num [permutationFourierSum, Fin.sum_univ_one,
      semicircleFlowKernel, semicircleFlowResolvent_half_at_zero]
  · norm_num

#print axioms permutationFourierClosedTimeInterpolation
#print axioms permutationFourierClosedTimeInterpolation_W1_witness

end RBM.Gauss
