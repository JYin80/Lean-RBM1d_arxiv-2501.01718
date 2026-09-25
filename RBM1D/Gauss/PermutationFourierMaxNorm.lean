/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierSwap

/-!
# Uniform norm bound for a finite permutation Fourier sum

This deterministic estimate uses only the pointwise bounds on the two tables. The
local laws (2.3)–(2.4) are later probabilistic statements and are not claimed here.
-/

namespace RBM.Gauss

/-- The normalized Fourier sum is uniformly bounded by the product of the table bounds. -/
theorem norm_permutationFourierSum_le_two (W : ℕ) (hW : 1 ≤ W)
    (x χ : Fin W → ℂ) (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) :
    ‖permutationFourierSum W x χ π‖ ≤ 2 := by
  rw [permutationFourierSum, norm_div, Complex.norm_natCast]
  have hw : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  apply (div_le_iff₀ hw).2
  calc
    ‖∑ i : Fin W, χ i * x (π i)‖ ≤ ∑ i : Fin W, ‖χ i * x (π i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin W, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      calc
        ‖χ i‖ * ‖x (π i)‖ ≤ 1 * 2 := by
          exact mul_le_mul (hχ i) (hx (π i)) (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    _ = W * 2 := by simp [Finset.sum_const]
    _ = 2 * W := by ring

/-- The identity permutation attains the uniform bound with nonconstant two-point tables. -/
theorem permutationFourierSum_sharp_two :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      x 0 ≠ x 1 ∧ χ 0 ≠ χ 1 ∧
      ‖permutationFourierSum 2 x χ (Equiv.refl _)‖ = 2 := by
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 else -2
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  refine ⟨x, χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x]
  · intro i
    fin_cases i <;> norm_num [χ]
  · norm_num [x]
  · norm_num [χ]
  · norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ]

#print axioms norm_permutationFourierSum_le_two
#print axioms permutationFourierSum_sharp_two

end RBM.Gauss
