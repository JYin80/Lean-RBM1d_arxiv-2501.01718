/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFiberCount

/-!
# Positive support of an actually realized next-image fiber

An existing permutation witnesses the fiber corresponding to its own next
image, whenever the prescribed prefix agrees with that permutation.
-/

namespace RBM.Gauss

/-- An agreeing permutation belongs to the fiber indexed by its actual next image. -/
theorem permutationPrefixFiber_actual_mem (W : ℕ) (k : Fin W)
    (p : Fin W → Fin W) (π : Equiv.Perm (Fin W))
    (hπ : ∀ i, i < k → π i = p i) :
    ∃ q : permutationPrefixFiber W k p (π k), q.1 = π := by
  exact ⟨⟨π, hπ, rfl⟩, rfl⟩

/-- Every actually realized next-image fiber has strictly positive finite size. -/
theorem permutationPrefixFiber_actual_card_pos (W : ℕ) (k : Fin W)
    (p : Fin W → Fin W) (π : Equiv.Perm (Fin W))
    (hπ : ∀ i, i < k → π i = p i) :
    0 < Fintype.card (permutationPrefixFiber W k p (π k)) := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨⟨π, hπ, rfl⟩⟩

/-- There is no next-image index at `W=0`. -/
theorem permutationPrefixFiber_no_index_zero : IsEmpty (Fin 0) :=
  ⟨fun k => Fin.elim0 k⟩

/-- At `W=1`, the sole fiber for the empty prefix has exactly one permutation. -/
theorem permutationPrefixFiber_one_card (p : Fin 1 → Fin 1) :
    Fintype.card (permutationPrefixFiber 1 0 p 0) = 1 := by
  classical
  let hunique : Unique (permutationPrefixFiber 1 0 p 0) := {
    default := ⟨Equiv.refl _, (by
      intro i hi
      exact (Fin.not_lt_zero i hi).elim), rfl⟩
    uniq := by
      intro a
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact Subsingleton.elim _ _
  }
  exact @Fintype.card_unique _ hunique _

/-- At `W=2`, identity and swap realize two distinct positive empty-prefix fibers. -/
theorem permutationPrefixFiber_two_distinct_positive :
    (∃ q : permutationPrefixFiber 2 0 (fun i => i) 0,
        q.1 = Equiv.refl (Fin 2)) ∧
      (∃ q : permutationPrefixFiber 2 0 (fun i => i) 1,
        q.1 = Equiv.swap 0 1) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 0) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 1) ∧
      (0 : Fin 2) ≠ 1 := by
  have hzero : ∃ q : permutationPrefixFiber 2 0 (fun i => i) 0,
      q.1 = Equiv.refl (Fin 2) := by
    exact ⟨⟨Equiv.refl _, (by
      intro i hi
      exact (Fin.not_lt_zero i hi).elim), rfl⟩, rfl⟩
  have hone : ∃ q : permutationPrefixFiber 2 0 (fun i => i) 1,
      q.1 = Equiv.swap 0 1 := by
    exact ⟨⟨Equiv.swap 0 1, (by
      intro i hi
      exact (Fin.not_lt_zero i hi).elim), (by simp)⟩, rfl⟩
  refine ⟨hzero, hone, ?_, ?_, by decide⟩
  · exact Fintype.card_pos_iff.mpr ⟨⟨Equiv.refl _, (by
      intro i hi
      exact (Fin.not_lt_zero i hi).elim), rfl⟩⟩
  · exact Fintype.card_pos_iff.mpr ⟨⟨Equiv.swap 0 1, (by
      intro i hi
      exact (Fin.not_lt_zero i hi).elim), (by simp)⟩⟩

#print axioms permutationPrefixFiber_actual_mem
#print axioms permutationPrefixFiber_actual_card_pos
#print axioms permutationPrefixFiber_no_index_zero
#print axioms permutationPrefixFiber_one_card
#print axioms permutationPrefixFiber_two_distinct_positive

end RBM.Gauss
