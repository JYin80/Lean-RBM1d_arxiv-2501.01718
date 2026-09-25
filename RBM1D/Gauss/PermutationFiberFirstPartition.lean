/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFiberCount

/-!
# Partition by the first image of a finite permutation

At prefix length zero the prescribed prefix is vacuous. Thus every permutation
lies in the unique fiber indexed by its image of zero. This is finite counting,
without a conditional distribution or a concentration assertion.
-/

namespace RBM.Gauss

/-- Membership in a first-image fiber is exactly the stated value of `π 0`. -/
theorem permutationFirstFiber_mem_iff (W : ℕ) (hW : 0 < W)
    (p : Fin W → Fin W) (v : Fin W) (π : Equiv.Perm (Fin W)) :
    (∃ q : permutationPrefixFiber W ⟨0, hW⟩ p v, q.1 = π) ↔
      π ⟨0, hW⟩ = v := by
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    exact q.2.2
  · intro hv
    exact ⟨⟨π, (by
      intro i hi
      have h : i.val < 0 := by
        change i.val < (⟨0, hW⟩ : Fin W).val at hi
        exact hi
      exact (Nat.not_lt_zero _ h).elim), hv⟩, rfl⟩

/-- Every permutation has exactly one first-image fiber, for arbitrary `p`. -/
theorem permutationFirstFiber_existsUnique (W : ℕ) (hW : 0 < W)
    (p : Fin W → Fin W) (π : Equiv.Perm (Fin W)) :
    ∃! v : Fin W, ∃ q : permutationPrefixFiber W ⟨0, hW⟩ p v, q.1 = π := by
  refine ⟨π ⟨0, hW⟩, (permutationFirstFiber_mem_iff W hW p _ π).2 rfl, ?_⟩
  intro v hv
  exact ((permutationFirstFiber_mem_iff W hW p v π).1 hv).symm

/-- Distinct first-image fibers contain no common permutation. -/
theorem permutationFirstFiber_disjoint (W : ℕ) (hW : 0 < W)
    (p : Fin W → Fin W) (v w : Fin W) (π : Equiv.Perm (Fin W))
    (hv : ∃ q : permutationPrefixFiber W ⟨0, hW⟩ p v, q.1 = π)
    (hw : ∃ q : permutationPrefixFiber W ⟨0, hW⟩ p w, q.1 = π) :
    v = w := by
  exact ((permutationFirstFiber_mem_iff W hW p v π).1 hv).symm.trans
    ((permutationFirstFiber_mem_iff W hW p w π).1 hw)

/-- The disjoint union of the first-image fibers is all permutations. -/
def permutationFirstFiberEquiv (W : ℕ) (hW : 0 < W)
    (p : Fin W → Fin W) :
    (Σ v : Fin W, permutationPrefixFiber W ⟨0, hW⟩ p v) ≃
      Equiv.Perm (Fin W) where
  toFun q := q.2.1
  invFun π := ⟨π ⟨0, hW⟩,
    ⟨π, (by
      intro i hi
      have h : i.val < 0 := by
        change i.val < (⟨0, hW⟩ : Fin W).val at hi
        exact hi
      exact (Nat.not_lt_zero _ h).elim), rfl⟩⟩
  left_inv := by
    rintro ⟨v, ⟨π, hp, hv⟩⟩
    dsimp
    cases hv
    rfl
  right_inv := by
    intro π
    rfl

/-- Exact cardinal partition by the first image, with no condition on `p`. -/
theorem permutationFirstFiber_card_sum (W : ℕ) (hW : 0 < W)
    (p : Fin W → Fin W) :
    (∑ v : Fin W, Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ p v)) =
      Fintype.card (Equiv.Perm (Fin W)) := by
  classical
  calc
    _ = Fintype.card (Σ v : Fin W, permutationPrefixFiber W ⟨0, hW⟩ p v) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card (Equiv.Perm (Fin W)) :=
      Fintype.card_congr (permutationFirstFiberEquiv W hW p)

/-- For `W=1`, the only first-image fiber has exactly one permutation. -/
theorem permutationFirstFiber_one_card (p : Fin 1 → Fin 1) :
    Fintype.card (permutationPrefixFiber 1 0 p 0) = 1 := by
  classical
  have hunique : Unique (permutationPrefixFiber 1 0 p 0) := {
    default := ⟨Equiv.refl _, (by intro i hi; exact (Fin.not_lt_zero i hi).elim), rfl⟩
    uniq := by
      intro a
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact Subsingleton.elim _ _
  }
  exact @Fintype.card_unique _ hunique _

/-- For `W=2`, both distinct first-image fibers have positive cardinality. -/
theorem permutationFirstFiber_two_card_pos :
    0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 0) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 1) :=
  permutationPrefixFiber_two_card_pos

#print axioms permutationFirstFiber_mem_iff
#print axioms permutationFirstFiber_existsUnique
#print axioms permutationFirstFiber_disjoint
#print axioms permutationFirstFiberEquiv
#print axioms permutationFirstFiber_card_sum
#print axioms permutationFirstFiber_one_card
#print axioms permutationFirstFiber_two_card_pos

end RBM.Gauss
