/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
# Unused images of an actual permutation prefix

The images not attained before position `k` are in bijection with the positions
at or after `k`. This is finite counting only, with no conditional probability law.
-/

namespace RBM.Gauss

/-- Values not attained by `π` at a position strictly before `k`. -/
noncomputable def unusedImages (W : ℕ) (k : Fin W) (π : PermΩ W) :
    Finset (Fin W) := by
  classical
  exact Finset.univ.filter (fun v => ∀ i : Fin W, i < k → π i ≠ v)

theorem mem_unusedImages_iff (W : ℕ) (k : Fin W) (π : PermΩ W) (v : Fin W) :
    v ∈ unusedImages W k π ↔ ∀ i : Fin W, i < k → π i ≠ v := by
  classical
  simp [unusedImages]

private theorem unused_iff_inverse_ge (W : ℕ) (k : Fin W) (π : PermΩ W)
    (v : Fin W) :
    (∀ i : Fin W, i < k → π i ≠ v) ↔ k.val ≤ (π.symm v).val := by
  constructor
  · intro h
    by_contra hn
    have hlt : π.symm v < k := Fin.lt_def.mpr (Nat.lt_of_not_ge hn)
    exact h (π.symm v) hlt (π.apply_symm_apply v)
  · intro h i hi he
    have hidx : i = π.symm v := by
      simpa [he] using (π.symm_apply_apply i).symm
    have hval : i.val = (π.symm v).val := congrArg Fin.val hidx
    exact (Nat.not_lt_of_ge h) (hval ▸ hi)

/-- Exact number of unused images at a valid next-reveal position. -/
theorem unusedImages_card (W : ℕ) (k : Fin W) (π : PermΩ W) :
    (unusedImages W k π).card = W - k.val := by
  classical
  have hcard : (unusedImages W k π).card =
      ((Finset.univ : Finset (Fin W)).filter (fun j => k.val ≤ j.val)).card := by
    apply Finset.card_bij (fun v _ => π.symm v)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (unused_iff_inverse_ge W k π v).mp
        ((mem_unusedImages_iff W k π v).mp hv)
    · intro a ha b hb hab
      exact π.symm.injective hab
    · intro j hj
      refine ⟨π j, ?_, ?_⟩
      · apply (mem_unusedImages_iff W k π (π j)).mpr
        apply (unused_iff_inverse_ge W k π (π j)).mpr
        simpa using (Finset.mem_filter.mp hj).2
      · exact π.symm_apply_apply j
  rw [hcard]
  have hfree := Fintype.card_subtype_compl (fun j : Fin W => j.val < k.val)
  simpa only [not_lt, Fintype.card_fin, Fintype.card_subtype,
    Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt k.isLt)] using hfree

/-- A next position exists only below the width; its unused set is nonempty. -/
theorem unusedImages_card_pos (W : ℕ) (k : Fin W) (π : PermΩ W) :
    0 < (unusedImages W k π).card := by
  rw [unusedImages_card]
  exact Nat.sub_pos_of_lt k.isLt

/-- The final valid reveal has exactly one available image. -/
theorem unusedImages_card_last (W : ℕ) (k : Fin W) (π : PermΩ W)
    (hk : k.val + 1 = W) : (unusedImages W k π).card = 1 := by
  rw [unusedImages_card]
  omega

/-- There is no next-reveal index at width zero. -/
theorem no_next_index_zero : ¬ Nonempty (Fin 0) := by
  rintro ⟨k⟩
  exact k.elim0

theorem unusedImages_card_one_zero (π : PermΩ 1) :
    (unusedImages 1 0 π).card = 1 := by
  simpa using unusedImages_card 1 0 π

theorem unusedImages_card_two_zero (π : PermΩ 2) :
    (unusedImages 2 0 π).card = 2 := by
  simpa using unusedImages_card 2 0 π

theorem unusedImages_card_two_one (π : PermΩ 2) :
    (unusedImages 2 1 π).card = 1 := by
  simpa using unusedImages_card 2 1 π

/-- Identity and transposition are distinct realized samples with different
remaining images after one reveal. -/
theorem unusedImages_two_distinct_samples :
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    idPerm ≠ swapPerm ∧
      (1 : Fin 2) ∈ unusedImages 2 1 idPerm ∧
      (0 : Fin 2) ∈ unusedImages 2 1 swapPerm ∧
      (unusedImages 2 0 idPerm).card = 2 ∧
      (unusedImages 2 0 swapPerm).card = 2 ∧
      (unusedImages 2 1 idPerm).card = 1 ∧
      (unusedImages 2 1 swapPerm).card = 1 := by
  classical
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [unusedImages]
  · simp [unusedImages]
  · exact unusedImages_card_two_zero _
  · exact unusedImages_card_two_zero _
  · exact unusedImages_card_two_one _
  · exact unusedImages_card_two_one _

#print axioms unusedImages
#print axioms mem_unusedImages_iff
#print axioms unusedImages_card
#print axioms unusedImages_card_pos
#print axioms unusedImages_card_last
#print axioms no_next_index_zero
#print axioms unusedImages_card_one_zero
#print axioms unusedImages_card_two_zero
#print axioms unusedImages_card_two_one
#print axioms unusedImages_two_distinct_samples

end RBM.Gauss
