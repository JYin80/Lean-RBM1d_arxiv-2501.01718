/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierSwap

/-!
# Mean of a finite permutation Fourier sum

The uniform counting average of the normalized sum vanishes whenever the weights sum to zero.
-/

namespace RBM.Gauss

/-- Reindexing permutations by a domain transposition shows that the image of each
position has the same counting sum. -/
private theorem permutation_image_sum_eq_at (W : ℕ) (x : Fin W → ℂ)
    (i k : Fin W) :
    (∑ π : Equiv.Perm (Fin W), x (π i)) =
      ∑ π : Equiv.Perm (Fin W), x (π k) := by
  let τ : Equiv.Perm (Fin W) := Equiv.swap i k
  have h := (Equiv.sum_comp (Equiv.mulRight τ)
    (fun π : Equiv.Perm (Fin W) => x (π i)))
  simpa only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, τ,
    Equiv.swap_apply_left] using h.symm

/-- At any fixed position, uniform counting over all permutations gives the mean
of the entries of `x`. The reindexing above supplies uniformity; summing over
positions determines the common multiplicity. -/
theorem permutation_image_sum (W : ℕ) (hW : 2 ≤ W) (x : Fin W → ℂ)
    (i : Fin W) :
    (∑ π : Equiv.Perm (Fin W), x (π i)) =
      ((Fintype.card (Equiv.Perm (Fin W)) : ℂ) / (W : ℂ)) *
        ∑ j : Fin W, x j := by
  classical
  have hn : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have hcount : (W : ℂ) * (∑ π : Equiv.Perm (Fin W), x (π i)) =
      (Fintype.card (Equiv.Perm (Fin W)) : ℂ) * ∑ j : Fin W, x j := by
    calc
      (W : ℂ) * (∑ π : Equiv.Perm (Fin W), x (π i)) =
          ∑ j : Fin W, ∑ π : Equiv.Perm (Fin W), x (π j) := by
            simp_rw [← permutation_image_sum_eq_at W x i]
            simp
      _ = ∑ π : Equiv.Perm (Fin W), ∑ j : Fin W, x (π j) :=
            Finset.sum_comm
      _ = ∑ π : Equiv.Perm (Fin W), ∑ j : Fin W, x j := by
            apply Finset.sum_congr rfl
            intro π _
            exact Equiv.sum_comp π x
      _ = (Fintype.card (Equiv.Perm (Fin W)) : ℂ) * ∑ j : Fin W, x j := by
            simp
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).2
  calc
    (∑ π : Equiv.Perm (Fin W), x (π i)) * (W : ℂ) =
        (W : ℂ) * ∑ π : Equiv.Perm (Fin W), x (π i) := mul_comm _ _
    _ = _ := hcount

/-- The unnormalized counting sum of the existing `W⁻¹` Fourier quantity is zero
when the weights have zero sum. No bound on the table `x` is needed. -/
theorem permutationFourierSum_sum_zero (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hχ : (∑ i : Fin W, χ i) = 0) :
    (∑ π : Equiv.Perm (Fin W), permutationFourierSum W x χ π) = 0 := by
  have hnum :
      (∑ π : Equiv.Perm (Fin W), ∑ i : Fin W, χ i * x (π i)) = 0 := by
    calc
      (∑ π : Equiv.Perm (Fin W), ∑ i : Fin W, χ i * x (π i)) =
          ∑ i : Fin W, ∑ π : Equiv.Perm (Fin W), χ i * x (π i) :=
            Finset.sum_comm
      _ = ∑ i : Fin W, χ i * (∑ π : Equiv.Perm (Fin W), x (π i)) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ i : Fin W, χ i *
            (((Fintype.card (Equiv.Perm (Fin W)) : ℂ) / (W : ℂ)) *
              ∑ j : Fin W, x j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [permutation_image_sum W hW x i]
      _ = 0 := by rw [← Finset.sum_mul, hχ, zero_mul]
  change (∑ π : Equiv.Perm (Fin W),
    (∑ i : Fin W, χ i * x (π i)) / (W : ℂ)) = 0
  rw [← Finset.sum_div, hnum, zero_div]

/-- The uniform counting average over every permutation is zero. -/
theorem permutationFourierSum_mean_zero (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hχ : (∑ i : Fin W, χ i) = 0) :
    (∑ π : Equiv.Perm (Fin W), permutationFourierSum W x χ π) /
      (Fintype.card (Equiv.Perm (Fin W)) : ℂ) = 0 := by
  have hcard : (Fintype.card (Equiv.Perm (Fin W)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin W)) ≠ 0)
  rw [permutationFourierSum_sum_zero W hW x χ hχ, zero_div]

/-- A nonconstant two-point example has zero-sum weights and a nonzero Fourier
value at the identity, so its zero permutation mean is a genuine cancellation. -/
theorem permutationFourierSum_mean_zero_witness_two :
    ∃ x χ : Fin 2 → ℂ,
      x 0 ≠ x 1 ∧ χ 0 ≠ χ 1 ∧
      (∑ i : Fin 2, χ i) = 0 ∧
      permutationFourierSum 2 x χ (Equiv.refl _) ≠ 0 ∧
      (∑ π : Equiv.Perm (Fin 2), permutationFourierSum 2 x χ π) /
        (Fintype.card (Equiv.Perm (Fin 2)) : ℂ) = 0 := by
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 else -2
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  have hχ : (∑ i : Fin 2, χ i) = 0 := by
    norm_num [Fin.sum_univ_two, χ]
  refine ⟨x, χ, ?_, ?_, hχ, ?_, ?_⟩
  · norm_num [x]
  · norm_num [χ]
  · norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ]
  · exact permutationFourierSum_mean_zero 2 (by omega) x χ hχ

#print axioms permutation_image_sum
#print axioms permutationFourierSum_sum_zero
#print axioms permutationFourierSum_mean_zero
#print axioms permutationFourierSum_mean_zero_witness_two

end RBM.Gauss
