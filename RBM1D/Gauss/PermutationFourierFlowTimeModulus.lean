/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleFlowKernelTimeModulus
import RBM1D.Gauss.PermutationFourierSwap

/-! # Closed-time modulus for a normalized finite Fourier sum

This deterministic adapter lifts the pointwise semicircle flow-kernel modulus
through the normalized finite permutation Fourier sum. -/

namespace RBM.Gauss

/-- The normalized finite Fourier sum inherits the closed-time modulus of the
semicircle flow kernel when its spectral inputs lie in `[-2,2]` and its
coefficients have norm at most one. -/
theorem norm_permutationFourierSum_flow_time_modulus
    (W : ℕ) (hW : 1 ≤ W) (lam : Fin W → ℝ) (χ : Fin W → ℂ)
    (hlam : ∀ j, |lam j| ≤ 2) (hχ : ∀ j, ‖χ j‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) (u v : ℝ)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ≤ 1 / 2) (hv : v ≤ 1 / 2) :
    ‖permutationFourierSum W (fun j => semicircleFlowKernel u (lam j)) χ π -
      permutationFourierSum W (fun j => semicircleFlowKernel v (lam j)) χ π‖
        ≤ 12 * Real.sqrt |u-v| := by
  rw [permutationFourierSum, permutationFourierSum, ← sub_div]
  rw [← Finset.sum_sub_distrib]
  rw [norm_div, Complex.norm_natCast]
  have hWreal : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  rw [div_le_iff₀ hWreal]
  calc
    ‖∑ i : Fin W,
        (χ i * semicircleFlowKernel u (lam (π i)) -
          χ i * semicircleFlowKernel v (lam (π i)))‖
        ≤ ∑ i : Fin W,
          ‖χ i * semicircleFlowKernel u (lam (π i)) -
            χ i * semicircleFlowKernel v (lam (π i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin W, (12 * Real.sqrt |u-v|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub]
      calc
        ‖χ i * (semicircleFlowKernel u (lam (π i)) -
            semicircleFlowKernel v (lam (π i)))‖
            ≤ ‖χ i‖ * ‖semicircleFlowKernel u (lam (π i)) -
              semicircleFlowKernel v (lam (π i))‖ := norm_mul_le _ _
        _ ≤ 1 * (12 * Real.sqrt |u-v|) := by
          apply mul_le_mul (hχ i) _ (norm_nonneg _) (by norm_num)
          exact semicircleFlowKernel_time_modulus u v (lam (π i))
            hu0 hv0 hu hv (hlam (π i))
        _ = 12 * Real.sqrt |u-v| := by norm_num
    _ = (12 * Real.sqrt |u-v|) * (W : ℝ) := by simp [mul_comm]

/-- Explicit nonconstant time behavior of the normalized sum at `W = 1`.
The constant spectral table `0` and coefficient table `1` give endpoint values
`i` and `2i` at times `0` and `1/2`. -/
theorem permutationFourierSum_W1_flow_endpoint_witness :
    (∀ j : Fin 1, |(fun _ : Fin 1 => (0 : ℝ)) j| ≤ 2) ∧
    (∀ j : Fin 1, ‖(fun _ : Fin 1 => (1 : ℂ)) j‖ ≤ 1) ∧
    permutationFourierSum 1 (fun _ => semicircleFlowKernel 0 0)
      (fun _ => (1:ℂ)) (Equiv.refl _) = Complex.I ∧
    permutationFourierSum 1 (fun _ => semicircleFlowKernel (1 / 2) 0)
      (fun _ => (1:ℂ)) (Equiv.refl _) = 2 * Complex.I ∧
    Complex.I ≠ 2 * Complex.I := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    norm_num
  · intro j
    norm_num
  · norm_num [permutationFourierSum, Fin.sum_univ_one,
      semicircleFlowKernel, semicircleFlowResolvent_half_at_zero]
  · norm_num [permutationFourierSum, Fin.sum_univ_one,
      semicircleFlowKernel, semicircleFlowResolvent_half_at_zero]
  · norm_num

#print axioms norm_permutationFourierSum_flow_time_modulus
#print axioms permutationFourierSum_W1_flow_endpoint_witness

end RBM.Gauss
