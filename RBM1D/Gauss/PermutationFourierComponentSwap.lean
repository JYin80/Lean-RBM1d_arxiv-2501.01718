/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierSwap

/-!
# Scalar components of the finite Fourier swap bound

The real and imaginary components of the normalized complex swap difference inherit
the same `8 / W` bound. These are deterministic consequences of the complex estimate.
-/

namespace RBM.Gauss

/-- The real component of the normalized Fourier swap difference is bounded by `8/W`. -/
theorem abs_re_permutationFourierSum_swap_le (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) (j k : Fin W) :
    |(permutationFourierSum W x χ ((Equiv.swap j k).trans π) -
      permutationFourierSum W x χ π).re| ≤ 8 / (W : ℝ) := by
  exact (Complex.abs_re_le_norm _).trans
    (norm_permutationFourierSum_swap_le W hW x χ hx hχ π j k)

/-- The imaginary component of the normalized Fourier swap difference is bounded by `8/W`. -/
theorem abs_im_permutationFourierSum_swap_le (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) (j k : Fin W) :
    |(permutationFourierSum W x χ ((Equiv.swap j k).trans π) -
      permutationFourierSum W x χ π).im| ≤ 8 / (W : ℝ) := by
  exact (Complex.abs_im_le_norm _).trans
    (norm_permutationFourierSum_swap_le W hW x χ hx hχ π j k)

/-- A nonconstant real-valued two-point witness attains the real-component bound at `W=2`. -/
theorem abs_re_permutationFourierSum_swap_sharp_two :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      x 0 ≠ x 1 ∧ χ 0 ≠ χ 1 ∧
      |(permutationFourierSum 2 x χ ((Equiv.swap 0 1).trans (Equiv.refl _)) -
        permutationFourierSum 2 x χ (Equiv.refl _)).re| = 8 / (2 : ℝ) := by
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 else -2
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  refine ⟨x, χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x]
  · intro i
    fin_cases i <;> norm_num [χ]
  · norm_num [x]
  · norm_num [χ]
  · norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ,
      Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- Multiplying the real witness table by `I` gives a nonconstant imaginary sharp witness. -/
theorem abs_im_permutationFourierSum_swap_sharp_two :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      x 0 ≠ x 1 ∧ χ 0 ≠ χ 1 ∧
      |(permutationFourierSum 2 x χ ((Equiv.swap 0 1).trans (Equiv.refl _)) -
        permutationFourierSum 2 x χ (Equiv.refl _)).im| = 8 / (2 : ℝ) := by
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 * Complex.I else -2 * Complex.I
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  refine ⟨x, χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x]
  · intro i
    fin_cases i <;> norm_num [χ]
  · intro h
    have hi := congrArg Complex.im h
    norm_num [x] at hi
  · norm_num [χ]
  · norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ,
      Equiv.swap_apply_left, Equiv.swap_apply_right]

#print axioms abs_re_permutationFourierSum_swap_le
#print axioms abs_im_permutationFourierSum_swap_le
#print axioms abs_re_permutationFourierSum_swap_sharp_two
#print axioms abs_im_permutationFourierSum_swap_sharp_two

end RBM.Gauss
