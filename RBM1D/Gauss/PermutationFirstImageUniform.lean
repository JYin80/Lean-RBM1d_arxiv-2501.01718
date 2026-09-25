/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationPrefixFiltrationCore
import RBM1D.Gauss.PermutationFiberFirstPartition

/-!
# Uniform law of the first image of a finite uniform permutation

The result is a finite counting identity for the first coordinate only. It does
not assert a conditional law after an arbitrary revealed prefix.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

private def firstImageEventEquiv (W : ℕ) (hW : 0 < W) (v : Fin W) :
    {π : PermΩ W // π ⟨0, hW⟩ = v} ≃
      permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v where
  toFun π := ⟨π.1, (by
    intro i hi
    change i.val < (⟨0, hW⟩ : Fin W).val at hi
    simp at hi), π.2⟩
  invFun π := ⟨π.1, π.2.2⟩
  left_inv := by intro π; rfl
  right_inv := by intro π; rfl

private theorem firstImageFiber_card_mul (W : ℕ) (hW : 2 ≤ W) (v : Fin W) :
    W * Fintype.card (permutationPrefixFiber W ⟨0, by omega⟩ (fun i => i) v) =
      Fintype.card (PermΩ W) := by
  classical
  let k : Fin W := ⟨0, by omega⟩
  have heq (x y : Fin W) :
      Fintype.card (permutationPrefixFiber W k (fun i => i) x) =
        Fintype.card (permutationPrefixFiber W k (fun i => i) y) := by
    by_cases hxy : x = y
    · subst y
      rfl
    · exact permutationPrefixFiber_card_eq W hW k (fun i => i) x y hxy
        (by intro i hi; change i.val < k.val at hi; simp [k] at hi)
        (by intro i hi; change i.val < k.val at hi; simp [k] at hi)
  have hsum := permutationFirstFiber_card_sum W (by omega) (fun i => i)
  have hsum' :
      (∑ x : Fin W, Fintype.card (permutationPrefixFiber W k (fun i => i) x)) =
        Fintype.card (PermΩ W) := by
    simpa [k] using hsum
  calc
    W * Fintype.card (permutationPrefixFiber W k (fun i => i) v) =
        Fintype.card (Fin W) * Fintype.card (permutationPrefixFiber W k (fun i => i) v) := by
          simp
    _ = ∑ x : Fin W, Fintype.card (permutationPrefixFiber W k (fun i => i) v) := by simp
    _ = ∑ x : Fin W, Fintype.card (permutationPrefixFiber W k (fun i => i) x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (heq x v).symm
    _ = Fintype.card (PermΩ W) := hsum'

private theorem uniformPerm_firstImage_event_card (W : ℕ) (hW : 0 < W)
    (v : Fin W) :
    uniformPerm W {π | π ⟨0, hW⟩ = v} =
      (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal) /
        Fintype.card (PermΩ W) := by
  classical
  let A : Finset (PermΩ W) := Finset.univ.filter (fun π => π ⟨0, hW⟩ = v)
  have hA : (A : Set (PermΩ W)) = {π | π ⟨0, hW⟩ = v} := by
    ext π
    simp [A]
  have hcard : A.card = Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) := by
    have hsub : A.card = Fintype.card {π : PermΩ W // π ⟨0, hW⟩ = v} := by
      rw [Fintype.card_subtype]
    rw [hsub]
    exact Fintype.card_congr (firstImageEventEquiv W hW v)
  rw [← hA, uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
  rw [hcard]

/-- Every first-image fiber has mass exactly `1/W` under the uniform
permutation measure, for every positive width. -/
theorem uniformPerm_firstImage (W : ℕ) (hW : 0 < W) (v : Fin W) :
    uniformPerm W {π | π ⟨0, hW⟩ = v} = (1 : ENNReal) / (W : ENNReal) := by
  classical
  by_cases hW1 : W = 1
  · subst W
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    rw [uniformPerm_firstImage_event_card 1 (by norm_num) 0]
    have hone : Fintype.card (permutationPrefixFiber 1 ⟨0, by norm_num⟩
        (fun i => i) (0 : Fin 1)) = 1 := by
      simpa using permutationFirstFiber_one_card (fun i : Fin 1 => i)
    rw [hone]
    norm_num [Fintype.card_perm]
  · have hW2 : 2 ≤ W := by omega
    rw [uniformPerm_firstImage_event_card W hW v]
    have hmul := firstImageFiber_card_mul W hW2 v
    have hcardpos : 0 < Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) := by
      exact Fintype.card_pos_iff.mpr ⟨⟨Equiv.swap (⟨0, hW⟩ : Fin W) v,
        (by intro i hi
            change i.val < (⟨0, hW⟩ : Fin W).val at hi
            simp at hi), by simp⟩⟩
    have hmulE : (W : ENNReal) *
        (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal) =
        (Fintype.card (PermΩ W) : ENNReal) := by exact_mod_cast hmul
    rw [← hmulE]
    have hWpos : (W : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
    have hCpos : (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal) ≠ 0 :=
      by exact_mod_cast (Nat.ne_of_gt hcardpos)
    have hden : (W : ENNReal) *
        (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal) ≠ 0 :=
      mul_ne_zero hWpos hCpos
    have hnumfin :
        (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    have hleftfin := ENNReal.div_ne_top hnumfin hden
    have hrightfin := ENNReal.div_ne_top ENNReal.one_ne_top hWpos
    apply (ENNReal.toReal_eq_toReal_iff'
      (x := (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal) /
        ((W : ENNReal) *
          (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ENNReal)))
      (y := (1 : ENNReal) / (W : ENNReal)) hleftfin hrightfin).mp
    simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_one]
    have hWreal : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
    have hCreal :
        (Fintype.card (permutationPrefixFiber W ⟨0, hW⟩ (fun i => i) v) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcardpos)
    field_simp [hWreal, hCreal]

/-- At width two, identity and transposition give distinct positive events,
each with mass one half. -/
theorem uniformPerm_firstImage_two_witness :
    uniformPerm 2 {π | π 0 = (0 : Fin 2)} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {π | π 0 = (1 : Fin 2)} = (1 : ENNReal) / 2 ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ≠ Equiv.swap 0 1 ∧
      (Equiv.refl (Fin 2) : PermΩ 2) 0 = 0 ∧
      (Equiv.swap (0 : Fin 2) 1 : PermΩ 2) 0 = 1 := by
  constructor
  · simpa using uniformPerm_firstImage 2 (by norm_num) (0 : Fin 2)
  constructor
  · simpa using uniformPerm_firstImage 2 (by norm_num) (1 : Fin 2)
  · constructor
    · decide
    · constructor <;> simp

#print axioms uniformPerm_firstImage
#print axioms uniformPerm_firstImage_two_witness

end RBM.Gauss
