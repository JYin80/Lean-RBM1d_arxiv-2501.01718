/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageUniformCell

/-!
# Finite-set next-image quotient on an actual permutation prefix cell

This is a finite event quotient on a positive actual cell. It is not a
conditional distribution with respect to the prefix sigma algebra.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

private def prefixCellNextImageFinsetEquiv (W : ℕ) (k : Fin W)
    (π : PermΩ W) (A : Finset (Fin W)) :
    (Σ v : {v : Fin W // v ∈ A}, prefixCellNextFiber W k π v.1) ≃
      {ρ : PermΩ W // ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} where
  toFun x := ⟨x.2.1, ⟨x.2.2.1, by rw [x.2.2.2]; exact x.1.2⟩⟩
  invFun x := ⟨⟨x.1 k, x.2.2⟩, ⟨x.1, x.2.1, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨v, hv⟩, ⟨ρ, hcell, hnext⟩⟩
    change ρ k = v at hnext
    apply Sigma.ext
    · apply Subtype.ext
      exact hnext
    · cases hnext
      rfl
  right_inv x := by
    rcases x with ⟨ρ, hcell, hA⟩
    rfl

private theorem prefixCell_nextImage_finset_event_card (W : ℕ)
    (k : Fin W) (π : PermΩ W) (A : Finset (Fin W)) :
    (Finset.univ.filter (fun ρ : PermΩ W =>
      ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A)).card =
      ∑ v ∈ A, Fintype.card (prefixCellNextFiber W k π v) := by
  classical
  have hcard := Fintype.card_congr (prefixCellNextImageFinsetEquiv W k π A)
  rw [Fintype.card_sigma] at hcard
  have hleft : Fintype.card {ρ : PermΩ W //
      ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} =
    (Finset.univ.filter (fun ρ : PermΩ W =>
        ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A)).card := by
    rw [Fintype.card_subtype]
  calc
    (Finset.univ.filter (fun ρ : PermΩ W =>
        ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A)).card =
      Fintype.card {ρ : PermΩ W // ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} := hleft.symm
    _ = ∑ v ∈ A, Fintype.card (prefixCellNextFiber W k π v) := by
      calc
        Fintype.card {ρ : PermΩ W // ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} =
            ∑ i : {v : Fin W // v ∈ A},
              Fintype.card (prefixCellNextFiber W k π i.1) := hcard.symm
        _ = ∑ i ∈ A.attach,
              Fintype.card (prefixCellNextFiber W k π i.1) :=
          Finset.sum_coe_sort_eq_attach A
            (fun i => Fintype.card (prefixCellNextFiber W k π i.1))
        _ = ∑ v ∈ A, Fintype.card (prefixCellNextFiber W k π v) :=
          Finset.sum_attach A (fun v => Fintype.card (prefixCellNextFiber W k π v))

private theorem uniformPerm_nextImage_finset_event (W : ℕ)
    (k : Fin W) (π : PermΩ W) (A : Finset (Fin W)) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} =
      (∑ v ∈ A, (Fintype.card (prefixCellNextFiber W k π v) : ENNReal)) /
        (Fintype.card (PermΩ W) : ENNReal) := by
  classical
  rw [uniformPerm, ProbabilityTheory.uniformOn_univ]
  have hs : {ρ : PermΩ W | ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} =
      (Finset.univ.filter (fun ρ : PermΩ W =>
        ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A) : Set (PermΩ W)) := by
    ext ρ
    simp
  rw [hs, Measure.count_apply_finset, prefixCell_nextImage_finset_event_card,
    Nat.cast_sum]

private theorem finite_common_denominator_cancel_finset (a b c : ENNReal)
    (hcZero : c ≠ 0) (hcTop : c ≠ ⊤) :
    (a / c) / (b / c) = a / b := by
  calc
    (a / c) / (b / c) = (a * c⁻¹) / (b * c⁻¹) := by
      simp only [div_eq_mul_inv]
    _ = a / b := ENNReal.mul_div_mul_right a b
      (ENNReal.inv_ne_zero.mpr hcTop) (ENNReal.inv_ne_top.mpr hcZero)

/-- The quotient for an arbitrary finite set of next-image values is the
fraction of unused images belonging to that set. -/
theorem uniformPerm_nextImage_finset_given_actualPrefix
    (W : ℕ) (k : Fin W) (π : PermΩ W) (A : Finset (Fin W)) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
        ((A.filter (fun v => v ∈ unusedImages W k π)).card : ENNReal) /
          ((W - k.val : ℕ) : ENNReal) := by
  classical
  have hnext : π k ∈ unusedImages W k π := by
    apply (mem_unusedImages_iff W k π (π k)).mpr
    intro i hi he
    exact (ne_of_lt hi) (π.injective he)
  have hfiber_pos := prefixCellNextFiber_card_pos_of_unused W k π (π k) hnext
  have hfiber_ne :
      (Fintype.card (prefixCellNextFiber W k π (π k)) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hfiber_pos)
  have hfiber_top :
      (Fintype.card (prefixCellNextFiber W k π (π k)) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hAcard :
      (∑ v ∈ A, Fintype.card (prefixCellNextFiber W k π v)) =
        (A.filter (fun v => v ∈ unusedImages W k π)).card *
          Fintype.card (prefixCellNextFiber W k π (π k)) := by
    calc
      (∑ v ∈ A, Fintype.card (prefixCellNextFiber W k π v)) =
          ∑ v ∈ A, if v ∈ unusedImages W k π then
            Fintype.card (prefixCellNextFiber W k π (π k)) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases huv : v ∈ unusedImages W k π
        · simp [huv, prefixCellNextFiber_card_eq_of_unused W k π v (π k) huv hnext]
        · have hnot : ¬ ∀ i : Fin W, i < k → π i ≠ v := by
            simpa [mem_unusedImages_iff] using huv
          push Not at hnot
          obtain ⟨i, hi, hiv⟩ := hnot
          simp [huv, prefixCellNextFiber_card_zero_of_used W k π v i hi hiv]
      _ = ∑ v ∈ A.filter (fun v => v ∈ unusedImages W k π),
          Fintype.card (prefixCellNextFiber W k π (π k)) := by
        rw [Finset.sum_filter]
      _ = (A.filter (fun v => v ∈ unusedImages W k π)).card *
          Fintype.card (prefixCellNextFiber W k π (π k)) := by simp
  have hcell_card := prefixCell_card_eq_unused_mul_fiber W k π (π k) hnext
  rw [uniformPerm_nextImage_finset_event, uniformPerm_prefixCell_event]
  have hcastA :
      (((A.filter (fun v => v ∈ unusedImages W k π)).card *
        Fintype.card (prefixCellNextFiber W k π (π k)) : ℕ) : ENNReal) =
        ((A.filter (fun v => v ∈ unusedImages W k π)).card : ENNReal) *
          (Fintype.card (prefixCellNextFiber W k π (π k)) : ENNReal) := by
    exact_mod_cast Nat.cast_mul _ _
  have hcastCell :
      (((W - k.val) * Fintype.card (prefixCellNextFiber W k π (π k)) : ℕ) : ENNReal) =
        (W - k.val : ENNReal) *
          (Fintype.card (prefixCellNextFiber W k π (π k)) : ENNReal) := by
    exact_mod_cast Nat.cast_mul _ _
  have hperm_ne : (Fintype.card (PermΩ W) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (PermΩ W)))
  have hperm_top : (Fintype.card (PermΩ W) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    _ = (∑ v ∈ A, (Fintype.card (prefixCellNextFiber W k π v) : ENNReal)) /
        (prefixCell W k.val π).card :=
          finite_common_denominator_cancel_finset _ _ _ hperm_ne hperm_top
    _ = (((A.filter (fun v => v ∈ unusedImages W k π)).card : ENNReal) *
        (Fintype.card (prefixCellNextFiber W k π (π k)) : ENNReal)) /
        (((W - k.val : ℕ) : ENNReal) *
          (Fintype.card (prefixCellNextFiber W k π (π k)) : ENNReal)) := by
            rw [← Nat.cast_sum, hAcard, hcell_card, hcastA, hcastCell,
              ENNReal.natCast_sub]
    _ = ((A.filter (fun v => v ∈ unusedImages W k π)).card : ENNReal) /
        ((W - k.val : ℕ) : ENNReal) :=
          ENNReal.mul_div_mul_right _ _ hfiber_ne hfiber_top

/-- Every actual prefix cell has positive finite mass, and its number of
unused next images is positive. -/
theorem uniformPerm_nextImage_finset_actualPrefix_nonzero
    (W : ℕ) (k : Fin W) (π : PermΩ W) :
    0 < uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} ∧
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} ≠ ⊤ ∧
      0 < W - k.val := by
  refine ⟨(uniformPerm_actualPrefix_event_pos_ne_top W k π).1,
    (uniformPerm_actualPrefix_event_pos_ne_top W k π).2,
    Nat.sub_pos_of_lt k.isLt⟩

/-- At width zero there is no valid next-image index. -/
theorem uniformPerm_nextImage_finset_no_index_zero : ¬ Nonempty (Fin 0) :=
  no_next_index_zero

/-- At width one, the full next-image set has relative mass one. -/
theorem uniformPerm_nextImage_finset_one :
    uniformPerm 1 {ρ | ρ ∈ prefixCell 1 0 (Equiv.refl _) ∧ ρ 0 ∈ (Finset.univ : Finset (Fin 1))} /
      uniformPerm 1 {ρ | ρ ∈ prefixCell 1 0 (Equiv.refl _)} = 1 := by
  calc
    _ = ((Finset.univ.filter (fun v : Fin 1 => v ∈ unusedImages 1 0
        (Equiv.refl (Fin 1)))).card : ENNReal) / (1 : ENNReal) := by
      simpa using uniformPerm_nextImage_finset_given_actualPrefix
        1 (0 : Fin 1) (Equiv.refl _) (Finset.univ : Finset (Fin 1))
    _ = 1 := by
      change ((unusedImages 1 0 (Equiv.refl (Fin 1))).card : ENNReal) / 1 = 1
      rw [unusedImages_card_one_zero]
      norm_num

/-- At width two, a singleton next-image set has relative mass one half;
the identity and swap realize the two distinct positive fibers. -/
theorem uniformPerm_nextImage_finset_two :
    uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _) ∧ ρ 0 ∈ ({0} : Finset (Fin 2))} /
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _)} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _) ∧ ρ 0 ∈ ({1} : Finset (Fin 2))} /
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl _)} = (1 : ENNReal) / 2 ∧
      (0 : Fin 2) ≠ 1 ∧
      Nonempty (prefixCellNextFiber 2 0 (Equiv.refl _) 0) ∧
      Nonempty (prefixCellNextFiber 2 0 (Equiv.refl _) 1) ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ≠ Equiv.swap 0 1 ∧
      0 < Fintype.card (prefixCellNextFiber 2 0 (Equiv.refl _) 0) ∧
      0 < Fintype.card (prefixCellNextFiber 2 0 (Equiv.refl _) 1) := by
  have h0 : (0 : Fin 2) ∈ unusedImages 2 0 (Equiv.refl _) := by
    apply (mem_unusedImages_iff 2 0 (Equiv.refl _) 0).mpr
    intro i hi
    exact (Fin.not_lt_zero i hi).elim
  have h1 : (1 : Fin 2) ∈ unusedImages 2 0 (Equiv.refl _) := by
    apply (mem_unusedImages_iff 2 0 (Equiv.refl _) 1).mpr
    intro i hi
    exact (Fin.not_lt_zero i hi).elim
  refine ⟨?_, ?_, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · have hfilter : ({0} : Finset (Fin 2)).filter
        (fun v => v ∈ unusedImages 2 0 (Equiv.refl _)) = {0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro hv
        subst v
        exact ⟨rfl, h0⟩
    simpa [hfilter] using uniformPerm_nextImage_finset_given_actualPrefix
      2 (0 : Fin 2) (Equiv.refl _) ({0} : Finset (Fin 2))
  · have hfilter : ({1} : Finset (Fin 2)).filter
        (fun v => v ∈ unusedImages 2 0 (Equiv.refl _)) = {1} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro hv
        subst v
        exact ⟨rfl, h1⟩
    simpa [hfilter] using uniformPerm_nextImage_finset_given_actualPrefix
      2 (0 : Fin 2) (Equiv.refl _) ({1} : Finset (Fin 2))
  · exact prefixCellNextFiber_two_witness.1
  · exact prefixCellNextFiber_two_witness.2.1
  · exact prefixCellNextFiber_two_witness.2.2.1
  · exact prefixCellNextFiber_two_witness.2.2.2.1
  · exact prefixCellNextFiber_two_witness.2.2.2.2

/-- At the final valid reveal, a singleton set containing the unique unused
image has relative mass one. -/
theorem uniformPerm_nextImage_finset_last
    (W : ℕ) (k : Fin W) (π : PermΩ W) (A : Finset (Fin W))
    (hk : k.val + 1 = W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k ∈ A} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
        if π k ∈ A then 1 else 0 := by
  have hunused : unusedImages W k π = {π k} := by
    classical
    ext v
    simp only [Finset.mem_singleton]
    constructor
    · intro hv
      have hcard := unusedImages_card_last W k π hk
      have hmem : π k ∈ unusedImages W k π := by
        apply (mem_unusedImages_iff W k π (π k)).mpr
        intro i hi he
        exact (ne_of_lt hi) (π.injective he)
      have hsub : ({π k} : Finset (Fin W)) ⊆ unusedImages W k π :=
        Finset.singleton_subset_iff.mpr hmem
      have heq : ({π k} : Finset (Fin W)) = unusedImages W k π :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp)
      have hmem : v ∈ ({π k} : Finset (Fin W)) :=
        (Finset.ext_iff.mp heq v).mpr hv
      simpa using hmem
    · rintro rfl
      apply (mem_unusedImages_iff W k π (π k)).mpr
      intro i hi he
      exact (ne_of_lt hi) (π.injective he)
  rw [uniformPerm_nextImage_finset_given_actualPrefix, hunused]
  have hrem : W - k.val = 1 := by omega
  by_cases hA : π k ∈ A
  · have hfilter : A.filter (fun v => v = π k) = {π k} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro hv
        subst v
        exact ⟨hA, rfl⟩
    have hcardfilter : (A.filter (fun v => v = π k)).card = 1 := by
      rw [hfilter]
      simp
    simp [hA, hrem, hcardfilter]
  · simp [hA, hrem]

#print axioms prefixCell_nextImage_finset_event_card
#print axioms uniformPerm_nextImage_finset_event
#print axioms uniformPerm_nextImage_finset_given_actualPrefix
#print axioms uniformPerm_nextImage_finset_actualPrefix_nonzero
#print axioms uniformPerm_nextImage_finset_no_index_zero
#print axioms uniformPerm_nextImage_finset_one
#print axioms uniformPerm_nextImage_finset_two
#print axioms uniformPerm_nextImage_finset_last

end RBM.Gauss
