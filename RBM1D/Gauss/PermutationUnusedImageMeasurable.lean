/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationUnusedImageCount

/-!
# Measurability of unused-image events in the prefix filtration

Unused-image membership is determined by avoiding a value in each revealed
coordinate. Hence its event is a finite intersection of complements of the
generating coordinate cylinders.
-/

open MeasureTheory

namespace RBM.Gauss

/-- Membership of a value in the unused-image set is measurable with respect
to the information revealed before position `k`. -/
theorem measurableSet_unusedImage_prefixSigma (W : ℕ) (k : Fin W) (v : Fin W) :
    MeasurableSet[prefixSigma W k.val]
      {π : PermΩ W | v ∈ unusedImages W k π} := by
  classical
  have hevent :
      {π : PermΩ W | v ∈ unusedImages W k π} =
        ⋂ i : {i : Fin W // i.val < k.val}, {π : PermΩ W | π i.1 = v}ᶜ := by
    ext π
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff,
      Set.mem_ofPred_eq]
    rw [mem_unusedImages_iff]
    constructor
    · intro h i
      exact h i.1 (Fin.lt_def.mpr i.2)
    · intro h i hi
      exact h ⟨i, Fin.lt_def.mp hi⟩
  rw [hevent]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.compl
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨i.1, v, i.2, rfl⟩

/-- Boundary checks: there is no next index at width zero; before any reveal,
every value is unused at widths one and two; and the last valid reveal leaves
exactly one unused value. -/
theorem unusedImage_prefix_boundary_checks :
    (¬ Nonempty (Fin 0)) ∧
      (∀ π : PermΩ 1, ∀ v : Fin 1, v ∈ unusedImages 1 0 π) ∧
      (∀ π : PermΩ 2, ∀ v : Fin 2, v ∈ unusedImages 2 0 π) ∧
      (∀ (W : ℕ) (k : Fin W) (π : PermΩ W),
        k.val + 1 = W → (unusedImages W k π).card = 1) := by
  refine ⟨no_next_index_zero, ?_, ?_, ?_⟩
  · intro π v
    rw [mem_unusedImages_iff]
    intro i hi
    exact False.elim (Nat.not_lt_zero i.val (Fin.lt_def.mp hi))
  · intro π v
    rw [mem_unusedImages_iff]
    intro i hi
    exact False.elim (Nat.not_lt_zero i.val (Fin.lt_def.mp hi))
  · exact fun W k π hk => unusedImages_card_last W k π hk

/-- At `W=2`, after revealing position zero, the event that zero remains unused
contains the swap and excludes the identity, so it is nonempty and proper. -/
theorem unusedImage_prefix_two_nonempty_proper :
    (Equiv.swap (0 : Fin 2) 1 : PermΩ 2) ∈
        {π : PermΩ 2 | (0 : Fin 2) ∈ unusedImages 2 1 π} ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ∉
        {π : PermΩ 2 | (0 : Fin 2) ∈ unusedImages 2 1 π} := by
  constructor <;> simp [unusedImages]

#print axioms measurableSet_unusedImage_prefixSigma
#print axioms unusedImage_prefix_boundary_checks
#print axioms unusedImage_prefix_two_nonempty_proper

end RBM.Gauss
