/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationPrefixCellFiberBridge
import RBM1D.Gauss.PermutationPrefixCellMass

/-!
# Relative mass of a next-image event inside an actual permutation prefix cell

This is an identity of finite event probabilities. It does not identify a
conditional distribution with respect to the prefix sigma algebra.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

/-- The event fixing the next image has the cardinality of its subtype fiber. -/
theorem prefixCell_nextImage_event_card (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) :
    (Finset.univ.filter (fun ρ : PermΩ W =>
      ρ ∈ prefixCell W k.val π ∧ ρ k = v)).card =
      Fintype.card (prefixCellNextFiber W k π v) := by
  classical
  have hcard : Fintype.card (prefixCellNextFiber W k π v) =
      Fintype.card {ρ : PermΩ W // ρ ∈ prefixCell W k.val π ∧ ρ k = v} :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcard, Fintype.card_subtype]

/-- Uniform mass of the next-image event is its finite fiber cardinality
divided by the total number of permutations. -/
theorem uniformPerm_nextImage_event (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v} =
      (Fintype.card (prefixCellNextFiber W k π v) : ENNReal) /
        Fintype.card (PermΩ W) := by
  classical
  rw [uniformPerm, ProbabilityTheory.uniformOn_univ]
  have hs : {ρ : PermΩ W | ρ ∈ prefixCell W k.val π ∧ ρ k = v} =
      (Finset.univ.filter (fun ρ : PermΩ W =>
        ρ ∈ prefixCell W k.val π ∧ ρ k = v) : Set (PermΩ W)) := by
    ext ρ
    simp
  rw [hs, Measure.count_apply_finset, prefixCell_nextImage_event_card]

private theorem finite_common_denominator_cancel (a b c : ENNReal)
    (hcZero : c ≠ 0) (hcTop : c ≠ ⊤) :
    (a / c) / (b / c) = a / b := by
  calc
    (a / c) / (b / c) = (a * c⁻¹) / (b * c⁻¹) := by
      simp only [div_eq_mul_inv]
    _ = a / b := ENNReal.mul_div_mul_right a b
      (ENNReal.inv_ne_zero.mpr hcTop) (ENNReal.inv_ne_top.mpr hcZero)

/-- The finite conditioning cell has positive, finite mass. -/
theorem uniformPerm_actualPrefix_event_pos_ne_top (W : ℕ) (k : Fin W)
    (π : PermΩ W) :
    0 < uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} ∧
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} ≠ ⊤ := by
  constructor
  · exact uniformPerm_prefixCell_event_pos W k.val π
  · rw [uniformPerm_prefixCell_event]
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (PermΩ W))))

/-- Exact conditional-on-cell event quotient, valid for every proposed next
image, including values already used by the prefix. -/
theorem uniformPerm_nextImage_cell_ratio (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
        (Fintype.card (prefixCellNextFiber W k π v) : ENNReal) /
          (prefixCell W k.val π).card := by
  rw [uniformPerm_nextImage_event, uniformPerm_prefixCell_event]
  apply finite_common_denominator_cancel
  · exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (PermΩ W)))
  · exact ENNReal.natCast_ne_top _

/-- A previously exposed image cannot occur at the next coordinate. -/
theorem prefixCellNextFiber_card_zero_of_used (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) (i : Fin W) (hi : i < k) (hiv : π i = v) :
    Fintype.card (prefixCellNextFiber W k π v) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  constructor
  rintro ⟨ρ, hcell, hnext⟩
  have hbefore : ρ i = π i := (Finset.mem_filter.mp hcell).2 i (by omega)
  have hik : i = k := ρ.injective ((hbefore.trans hiv).trans hnext.symm)
  exact (ne_of_lt hi) hik

/-- Hence the quotient is zero for an image already used by the prefix. -/
theorem uniformPerm_nextImage_cell_ratio_zero_of_used (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) (i : Fin W) (hi : i < k) (hiv : π i = v) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} = 0 := by
  rw [uniformPerm_nextImage_cell_ratio,
    prefixCellNextFiber_card_zero_of_used W k π v i hi hiv]
  simp

/-- The only width-one reveal has conditional-on-cell mass one. -/
theorem uniformPerm_nextImage_cell_ratio_one :
    uniformPerm 1 {ρ | ρ ∈ prefixCell 1 0 (Equiv.refl _) ∧ ρ 0 = 0} /
      uniformPerm 1 {ρ | ρ ∈ prefixCell 1 0 (Equiv.refl _)} = 1 := by
  have hcell : (prefixCell 1 0 (Equiv.refl _)).card = 1 := by
    rw [prefixCell_eq_univ_of_zero, Finset.card_univ, Fintype.card_perm]
    norm_num
  simpa [hcell, prefixCellNextFiber_one_card] using
    (uniformPerm_nextImage_cell_ratio 1 (0 : Fin 1) (Equiv.refl _) (0 : Fin 1))

/-- At width two, the two distinct next-image values each have half the
mass of the empty-prefix cell. -/
theorem uniformPerm_nextImage_cell_ratio_two :
    uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _) ∧ ρ 0 = 0} /
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _)} =
          (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _) ∧ ρ 0 = 1} /
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _)} =
          (1 : ENNReal) / 2 ∧
      (0 : Fin 2) ≠ 1 := by
  classical
  have hcell : (prefixCell 2 0 (Equiv.refl _)).card = 2 := by
    rw [prefixCell_eq_univ_of_zero, Finset.card_univ, Fintype.card_perm]
    norm_num
  have hf0 : Fintype.card (prefixCellNextFiber 2 0 (Equiv.refl _) 0) = 1 := by
    rw [← prefixCell_nextImage_event_card]
    decide
  have hf1 : Fintype.card (prefixCellNextFiber 2 0 (Equiv.refl _) 1) = 1 := by
    rw [← prefixCell_nextImage_event_card]
    decide
  refine ⟨?_, ?_, by decide⟩
  · simpa [hf0, hcell] using
      (uniformPerm_nextImage_cell_ratio 2 (0 : Fin 2) (Equiv.refl _) (0 : Fin 2))
  · simpa [hf1, hcell] using
      (uniformPerm_nextImage_cell_ratio 2 (0 : Fin 2) (Equiv.refl _) (1 : Fin 2))

#print axioms prefixCell_nextImage_event_card
#print axioms uniformPerm_nextImage_event
#print axioms uniformPerm_actualPrefix_event_pos_ne_top
#print axioms uniformPerm_nextImage_cell_ratio
#print axioms prefixCellNextFiber_card_zero_of_used
#print axioms uniformPerm_nextImage_cell_ratio_zero_of_used
#print axioms uniformPerm_nextImage_cell_ratio_one
#print axioms uniformPerm_nextImage_cell_ratio_two

end RBM.Gauss
