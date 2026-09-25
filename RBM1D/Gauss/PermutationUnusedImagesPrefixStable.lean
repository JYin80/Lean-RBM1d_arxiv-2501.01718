/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationUnusedImageCount

/-!
# Stability of unused images on an actual permutation prefix cell

The values already revealed determine which images have appeared. This is a finite
combinatorial fact and does not assert a conditional distribution.
-/

namespace RBM.Gauss

/-- Permutations in one actual prefix cell have the same unused images. -/
theorem unusedImages_eq_of_mem_prefixCell
    (W : ℕ) (k : Fin W) (π ρ : PermΩ W)
    (hρ : ρ ∈ prefixCell W k.val π) :
    unusedImages W k ρ = unusedImages W k π := by
  classical
  have hprefix : ∀ i : Fin W, i.val < k.val → ρ i = π i := by
    simpa [prefixCell] using hρ
  ext v
  rw [mem_unusedImages_iff, mem_unusedImages_iff]
  constructor
  · intro h i hik
    have hi : i.val < k.val := Fin.lt_def.mp hik
    intro heq
    exact h i hik ((hprefix i hi).trans heq)
  · intro h i hik
    have hi : i.val < k.val := Fin.lt_def.mp hik
    intro heq
    exact h i hik ((hprefix i hi).symm.trans heq)

/-- Boundary checks: width zero has no next index, width one has one unused image,
and the final valid reveal has one unused image. -/
theorem unusedImages_prefix_boundary_checks :
    (¬ Nonempty (Fin 0)) ∧
      (∀ π : PermΩ 1, (unusedImages 1 0 π).card = 1) ∧
      (∀ (W : ℕ) (k : Fin W) (π : PermΩ W),
        k.val + 1 = W → (unusedImages W k π).card = 1) := by
  refine ⟨no_next_index_zero, ?_, ?_⟩
  · intro π
    exact unusedImages_card_one_zero π
  · intro W k π hk
    exact unusedImages_card_last W k π hk

/-- At width two and reveal index zero, identity and swap are distinct residents
of the same full prefix cell and have equal (two-element) unused-image sets. -/
theorem unusedImages_prefixCell_two_support_witness :
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    idPerm ≠ swapPerm ∧
      idPerm ∈ prefixCell 2 0 idPerm ∧
      swapPerm ∈ prefixCell 2 0 idPerm ∧
      unusedImages 2 0 idPerm = unusedImages 2 0 swapPerm ∧
      (unusedImages 2 0 idPerm).card = 2 ∧
      (unusedImages 2 0 swapPerm).card = 2 := by
  classical
  refine ⟨by decide, mem_prefixCell 2 0 _, ?_, ?_, ?_, ?_⟩
  · simp [prefixCell]
  · apply unusedImages_eq_of_mem_prefixCell 2 0 _ _
    simp [prefixCell]
  · exact unusedImages_card_two_zero _
  · exact unusedImages_card_two_zero _

#print axioms unusedImages_eq_of_mem_prefixCell
#print axioms unusedImages_prefix_boundary_checks
#print axioms unusedImages_prefixCell_two_support_witness

end RBM.Gauss
