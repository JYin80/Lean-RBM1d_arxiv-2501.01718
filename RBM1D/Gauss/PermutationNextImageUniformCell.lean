/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageCellRatio
import RBM1D.Gauss.PermutationUnusedImageCount
import RBM1D.Gauss.PermutationFiberCount

/-!
# Uniform next image on an actual permutation prefix cell

This is a finite event quotient on a positive actual cell, not a conditional
distribution with respect to `prefixSigma`.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

/-- Partition an actual cell by its next image. -/
private def prefixCellNextImageSigmaEquiv (W : ℕ) (k : Fin W) (π : PermΩ W) :
    (Σ v : Fin W, prefixCellNextFiber W k π v) ≃
      {ρ : PermΩ W // ρ ∈ prefixCell W k.val π} where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun x := ⟨x.1 k, ⟨x.1, x.2, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨v, ⟨ρ, hcell, hnext⟩⟩
    dsimp
    subst v
    rfl
  right_inv x := by cases x; rfl

/-- The cell cardinal is the sum of all next-image fiber cardinals. -/
theorem prefixCell_card_eq_sum_nextFibers (W : ℕ) (k : Fin W) (π : PermΩ W) :
    (prefixCell W k.val π).card =
      ∑ v : Fin W, Fintype.card (prefixCellNextFiber W k π v) := by
  classical
  have h := Fintype.card_congr (prefixCellNextImageSigmaEquiv W k π)
  rw [Fintype.card_sigma] at h
  have hcell : Fintype.card {ρ : PermΩ W // ρ ∈ prefixCell W k.val π} =
      (prefixCell W k.val π).card := by
    rw [Fintype.card_subtype]
    simp
  exact (h.trans hcell).symm

/-- Every fiber at an image already used by the actual prefix is empty. -/
private theorem nextFiber_card_zero_not_unused (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) (hv : v ∉ unusedImages W k π) :
    Fintype.card (prefixCellNextFiber W k π v) = 0 := by
  have hnot : ¬ ∀ i : Fin W, i < k → π i ≠ v := by
    simpa [mem_unusedImages_iff] using hv
  push Not at hnot
  obtain ⟨i, hi, hiv⟩ := hnot
  exact prefixCellNextFiber_card_zero_of_used W k π v i hi hiv

/-- The cell is partitioned across exactly the unused images. -/
theorem prefixCell_card_eq_sum_unused_nextFibers (W : ℕ) (k : Fin W)
    (π : PermΩ W) :
    (prefixCell W k.val π).card =
      ∑ v ∈ unusedImages W k π,
        Fintype.card (prefixCellNextFiber W k π v) := by
  classical
  rw [prefixCell_card_eq_sum_nextFibers]
  unfold unusedImages
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with hcond
  · rfl
  · have huv : v ∉ unusedImages W k π := by
      intro hv'
      exact hcond ((mem_unusedImages_iff W k π v).mp hv')
    exact nextFiber_card_zero_not_unused W k π v huv

/-- All unused next-image fibers have the same cardinality. -/
theorem prefixCellNextFiber_card_eq_of_unused (W : ℕ) (k : Fin W)
    (π : PermΩ W) (a b : Fin W)
    (ha : a ∈ unusedImages W k π) (hb : b ∈ unusedImages W k π) :
    Fintype.card (prefixCellNextFiber W k π a) =
      Fintype.card (prefixCellNextFiber W k π b) := by
  classical
  by_cases hab : a = b
  · subst b; rfl
  have hW : 2 ≤ W := by
    have hne : a.val ≠ b.val := by exact fun he => hab (Fin.ext he)
    omega
  rw [prefixCellNextFiber_card_eq, prefixCellNextFiber_card_eq]
  exact permutationPrefixFiber_card_eq W hW k (fun i => π i) a b hab
    ((mem_unusedImages_iff W k π a).mp ha)
    ((mem_unusedImages_iff W k π b).mp hb)

/-- Each unused next-image fiber is positive: the actual continuation `π`
supplies one fiber, and equal-card transport supplies every other. -/
theorem prefixCellNextFiber_card_pos_of_unused (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) (hv : v ∈ unusedImages W k π) :
    0 < Fintype.card (prefixCellNextFiber W k π v) := by
  classical
  have hπ : π k ∈ unusedImages W k π := by
    apply (mem_unusedImages_iff W k π (π k)).mpr
    intro i hi he
    exact (ne_of_lt hi) (π.injective he)
  have hpos : 0 < Fintype.card (prefixCellNextFiber W k π (π k)) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨π, mem_prefixCell W k.val π, rfl⟩⟩
  rw [prefixCellNextFiber_card_eq_of_unused W k π v (π k) hv hπ]
  exact hpos

/-- The exact finite partition identity: the cell cardinal is the number of
unused images times one (positive) unused fiber cardinal. -/
theorem prefixCell_card_eq_unused_mul_fiber (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) (hv : v ∈ unusedImages W k π) :
    (prefixCell W k.val π).card =
      (W - k.val) * Fintype.card (prefixCellNextFiber W k π v) := by
  classical
  rw [prefixCell_card_eq_sum_unused_nextFibers]
  have heq : (∑ a ∈ unusedImages W k π,
      Fintype.card (prefixCellNextFiber W k π a)) =
      ∑ a ∈ unusedImages W k π,
        Fintype.card (prefixCellNextFiber W k π v) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact prefixCellNextFiber_card_eq_of_unused W k π a v ha hv
  rw [heq]
  simp [unusedImages_card]

/-- Exact next-image event law on a positive actual prefix cell. -/
theorem uniformPerm_nextImage_given_actualPrefix
    (W : ℕ) (k : Fin W) (π : PermΩ W) (v : Fin W)
    (hv : ∀ i : Fin W, i < k → π i ≠ v) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
        (1 : ENNReal) / ((W - k.val : ℕ) : ENNReal) := by
  have huv : v ∈ unusedImages W k π :=
    (mem_unusedImages_iff W k π v).mpr hv
  rw [uniformPerm_nextImage_cell_ratio,
    prefixCell_card_eq_unused_mul_fiber W k π v huv]
  have hpos := prefixCellNextFiber_card_pos_of_unused W k π v huv
  have hne : (Fintype.card (prefixCellNextFiber W k π v) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have htop : (Fintype.card (prefixCellNextFiber W k π v) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hcast : ((W - k.val) * Fintype.card (prefixCellNextFiber W k π v) : ℕ) =
      (W - k.val : ENNReal) *
        (Fintype.card (prefixCellNextFiber W k π v) : ENNReal) := by
    exact_mod_cast (Nat.cast_mul _ _)
  rw [hcast]
  calc
    (Fintype.card (prefixCellNextFiber W k π v) : ENNReal) /
        ((W - k.val : ENNReal) *
          (Fintype.card (prefixCellNextFiber W k π v) : ENNReal)) =
        ((1 : ENNReal) *
          (Fintype.card (prefixCellNextFiber W k π v) : ENNReal)) /
            ((W - k.val : ENNReal) *
              (Fintype.card (prefixCellNextFiber W k π v) : ENNReal)) := by rw [one_mul]
    _ = (1 : ENNReal) / (W - k.val : ENNReal) :=
      ENNReal.mul_div_mul_right 1 _ hne htop
    _ = (1 : ENNReal) / ((W - k.val : ℕ) : ENNReal) := by
      rw [ENNReal.natCast_sub]

/-- Both denominators in the finite event quotient are strictly positive,
and the unused next-image fiber has a real witness. -/
theorem uniformPerm_nextImage_actualPrefix_nonzero
    (W : ℕ) (k : Fin W) (π : PermΩ W) (v : Fin W)
    (hv : ∀ i : Fin W, i < k → π i ≠ v) :
    0 < uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} ∧
      0 < W - k.val ∧
      0 < Fintype.card (prefixCellNextFiber W k π v) := by
  refine ⟨(uniformPerm_actualPrefix_event_pos_ne_top W k π).1, ?_, ?_⟩
  · exact Nat.sub_pos_of_lt k.isLt
  · exact prefixCellNextFiber_card_pos_of_unused W k π v
      ((mem_unusedImages_iff W k π v).mpr hv)

/-- Width zero has no next-image coordinate. -/
theorem uniformPerm_nextImage_no_index_zero : ¬ Nonempty (Fin 0) :=
  no_next_index_zero

/-- The only width-one next-image event has relative mass one. -/
theorem uniformPerm_nextImage_given_actualPrefix_one :
    uniformPerm 1 {ρ | ρ ∈ prefixCell 1 0 (Equiv.refl _) ∧ ρ 0 = 0} /
      uniformPerm 1 {ρ | ρ ∈ prefixCell 1 0 (Equiv.refl _)} = 1 := by
  have hv : ∀ i : Fin 1, i < 0 → (Equiv.refl (Fin 1)) i ≠ 0 := by
    intro i hi
    exact (Fin.not_lt_zero i hi).elim
  simpa using uniformPerm_nextImage_given_actualPrefix 1 0 (Equiv.refl _) 0 hv

/-- Two distinct unused first images each have half the cell mass. -/
theorem uniformPerm_nextImage_given_actualPrefix_two :
    uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _) ∧ ρ 0 = 0} /
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _)} =
          (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _) ∧ ρ 0 = 1} /
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _)} =
          (1 : ENNReal) / 2 ∧
      (0 : Fin 2) ≠ 1 := by
  have hv (v : Fin 2) :
      ∀ i : Fin 2, i < 0 → (Equiv.refl (Fin 2)) i ≠ v := by
    intro i hi
    exact (Fin.not_lt_zero i hi).elim
  refine ⟨?_, ?_, by decide⟩
  · simpa using uniformPerm_nextImage_given_actualPrefix 2 0 (Equiv.refl _) 0 (hv 0)
  · simpa using uniformPerm_nextImage_given_actualPrefix 2 0 (Equiv.refl _) 1 (hv 1)

/-- At the final valid reveal, the sole unused image has relative mass one. -/
theorem uniformPerm_nextImage_given_actualPrefix_last
    (W : ℕ) (k : Fin W) (π : PermΩ W) (v : Fin W)
    (hv : ∀ i : Fin W, i < k → π i ≠ v) (hk : k.val + 1 = W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} = 1 := by
  rw [uniformPerm_nextImage_given_actualPrefix W k π v hv]
  have h : W - k.val = 1 := by omega
  simp [h]

#print axioms prefixCell_card_eq_sum_nextFibers
#print axioms prefixCell_card_eq_sum_unused_nextFibers
#print axioms prefixCellNextFiber_card_eq_of_unused
#print axioms prefixCellNextFiber_card_pos_of_unused
#print axioms prefixCell_card_eq_unused_mul_fiber
#print axioms uniformPerm_nextImage_given_actualPrefix
#print axioms uniformPerm_nextImage_actualPrefix_nonzero
#print axioms uniformPerm_nextImage_no_index_zero
#print axioms uniformPerm_nextImage_given_actualPrefix_one
#print axioms uniformPerm_nextImage_given_actualPrefix_two
#print axioms uniformPerm_nextImage_given_actualPrefix_last

end RBM.Gauss
