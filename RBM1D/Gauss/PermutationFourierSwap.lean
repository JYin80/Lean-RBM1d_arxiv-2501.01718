/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib

/-!
# A finite Fourier sum under a swap of domain positions

This is the deterministic bounded-difference step (P1). No character orthogonality or
probability is used: `χ` may be any bounded complex table.
-/

namespace RBM.Gauss

/-- The normalized weighted sum of a table arranged by a permutation. -/
noncomputable def permutationFourierSum (W : ℕ) (x χ : Fin W → ℂ)
    (π : Equiv.Perm (Fin W)) : ℂ :=
  (∑ i : Fin W, χ i * x (π i)) / (W : ℂ)

/-- Exchanging the domain positions `j,k` changes exactly two summands. -/
theorem permutationFourierSum_swap (W : ℕ) (x χ : Fin W → ℂ)
    (π : Equiv.Perm (Fin W)) (j k : Fin W) :
    permutationFourierSum W x χ ((Equiv.swap j k).trans π) -
      permutationFourierSum W x χ π =
      ((χ j - χ k) * (x (π k) - x (π j))) / (W : ℂ) := by
  classical
  by_cases hjk : j = k
  · subst k
    simp [permutationFourierSum]
  · let s : Finset (Fin W) := Finset.univ.erase j |>.erase k
    have hj : j ∈ (Finset.univ : Finset (Fin W)) := Finset.mem_univ _
    have hk : k ∈ (Finset.univ : Finset (Fin W)).erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ _⟩
    have hrest (i : Fin W) (hi : i ∈ s) : Equiv.swap j k i = i := by
      apply Equiv.swap_apply_of_ne_of_ne
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      · exact (Finset.mem_erase.mp hi).1
    have hsum (f : Fin W → ℂ) :
        (∑ i : Fin W, f i) = f j + f k + ∑ i ∈ s, f i := by
      rw [← Finset.sum_erase_add _ _ hj, ← Finset.sum_erase_add _ _ hk]
      simp only [s]
      ring
    rw [permutationFourierSum, permutationFourierSum, ← sub_div]
    simp only [Equiv.trans_apply]
    rw [hsum (fun i => χ i * x (π (Equiv.swap j k i))),
      hsum (fun i => χ i * x (π i))]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hr : (∑ i ∈ s, χ i * x (π (Equiv.swap j k i))) =
        ∑ i ∈ s, χ i * x (π i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrest i hi]
    rw [hr]
    congr 1
    ring

/-- The `8/W` bounded-difference estimate for `W ≥ 2`. -/
theorem norm_permutationFourierSum_swap_le (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) (j k : Fin W) :
    ‖permutationFourierSum W x χ ((Equiv.swap j k).trans π) -
      permutationFourierSum W x χ π‖ ≤ 8 / (W : ℝ) := by
  rw [permutationFourierSum_swap, norm_div, Complex.norm_natCast]
  have hχjk : ‖χ j - χ k‖ ≤ 2 := by
    calc
      ‖χ j - χ k‖ ≤ ‖χ j‖ + ‖χ k‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [hχ j, hχ k]
  have hxjk : ‖x (π k) - x (π j)‖ ≤ 4 := by
    calc
      ‖x (π k) - x (π j)‖ ≤ ‖x (π k)‖ + ‖x (π j)‖ := norm_sub_le _ _
      _ ≤ 4 := by linarith [hx (π k), hx (π j)]
  have hwpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  rw [norm_mul]
  apply (div_le_div_of_nonneg_right ?_ hwpos.le)
  calc
    ‖χ j - χ k‖ * ‖x (π k) - x (π j)‖ ≤ 2 * 4 :=
      mul_le_mul hχjk hxjk (norm_nonneg _) (by norm_num)
    _ = 8 := by norm_num

/-- A nonconstant two-point table and character saturate the bound. -/
theorem permutationFourierSum_swap_sharp_two :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      x 0 ≠ x 1 ∧ χ 0 ≠ χ 1 ∧
      ‖permutationFourierSum 2 x χ ((Equiv.swap 0 1).trans (Equiv.refl _)) -
        permutationFourierSum 2 x χ (Equiv.refl _)‖ = 8 / (2 : ℝ) := by
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

#print axioms permutationFourierSum
#print axioms permutationFourierSum_swap
#print axioms norm_permutationFourierSum_swap_le
#print axioms permutationFourierSum_swap_sharp_two

end RBM.Gauss
