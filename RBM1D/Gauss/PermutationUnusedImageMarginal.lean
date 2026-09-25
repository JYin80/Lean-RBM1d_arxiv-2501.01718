/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationUnusedImageCount
import RBM1D.Gauss.PermutationFirstImageUniform

/-!
# Global marginal law of an unused permutation image

This is a finite, unconditional marginal. It is not a conditional law given a
revealed prefix and makes no assertion about the random-matrix local laws.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

private theorem unused_iff_inverse_ge (W : ℕ) (k : Fin W) (π : PermΩ W)
    (v : Fin W) :
    v ∈ unusedImages W k π ↔ k.val ≤ (π.symm v).val := by
  rw [mem_unusedImages_iff]
  constructor
  · intro h
    by_contra hn
    have hi : π.symm v < k := Fin.lt_def.mpr (Nat.lt_of_not_ge hn)
    exact h (π.symm v) hi (π.apply_symm_apply v)
  · intro h i hi heq
    have hidx : i = π.symm v := by
      apply π.injective
      simpa [heq] using (π.apply_symm_apply v).symm
    have hval : i.val = (π.symm v).val := congrArg Fin.val hidx
    exact (Nat.not_lt_of_ge h) (hval ▸ hi)

private noncomputable def unusedEventEquiv (W : ℕ) (k v : Fin W) :
    {π : PermΩ W // v ∈ unusedImages W k π} ≃
      {j : Fin W // k.val ≤ j.val} ×
        {ρ : PermΩ W // ρ (⟨0, Nat.zero_lt_of_lt k.isLt⟩ : Fin W) = v} where
  toFun π := by
    let j : Fin W := π.1.symm v
    let z : Fin W := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    refine ⟨⟨j, (unused_iff_inverse_ge W k π.1 v).mp π.2⟩,
      ⟨(Equiv.swap z j).trans π.1, ?_⟩⟩
    change π.1 ((Equiv.swap z j) z) = v
    simp [j]
  invFun p := by
    let j : Fin W := p.1.1
    let z : Fin W := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    let ρ : PermΩ W := p.2.1
    let π : PermΩ W := (Equiv.swap z j).trans ρ
    refine ⟨π, (unused_iff_inverse_ge W k π v).mpr ?_⟩
    have hj : π j = v := by
      change ρ ((Equiv.swap z j) j) = v
      simpa using p.2.2
    have hinv : π.symm v = j := by
      simpa using congrArg π.symm hj.symm
    simpa [j, hinv] using p.1.2
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    let j : Fin W := π.1.symm v
    let z : Fin W := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    simp [Equiv.trans_apply, j, z, Equiv.swap_apply_self]
  right_inv p := by
    rcases p with ⟨⟨j, hj⟩, ⟨ρ, hρ⟩⟩
    let z : Fin W := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    let σ : PermΩ W := (Equiv.swap z j).trans ρ
    have hσ : σ j = v := by
      change ρ ((Equiv.swap z j) j) = v
      simpa using hρ
    have hinv : σ.symm v = j := by
      simpa using congrArg σ.symm hσ.symm
    apply Prod.ext
    · apply Subtype.ext
      exact hinv
    · apply Subtype.ext
      apply Equiv.ext
      intro i
      change (Equiv.swap z (σ.symm v)).trans σ i = ρ i
      rw [hinv]
      change ρ ((Equiv.swap z j) ((Equiv.swap z j) i)) = ρ i
      rw [Equiv.swap_apply_self]

private theorem unusedImages_event_card (W : ℕ) (k v : Fin W) :
    Fintype.card {π : PermΩ W // v ∈ unusedImages W k π} =
      (W - k.val) * Fintype.card {ρ : PermΩ W //
        ρ (⟨0, Nat.zero_lt_of_lt k.isLt⟩ : Fin W) = v} := by
  classical
  rw [Fintype.card_congr (unusedEventEquiv W k v), Fintype.card_prod]
  have htail : Fintype.card {j : Fin W // k.val ≤ j.val} = W - k.val := by
    simpa only [not_lt, Fintype.card_fin, Fintype.card_subtype,
      Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt k.isLt)] using
        (Fintype.card_subtype_compl (fun j : Fin W => j.val < k.val))
  rw [htail]

private theorem uniformPerm_unused_event_card_ratio (W : ℕ) (k v : Fin W) :
    uniformPerm W {π | v ∈ unusedImages W k π} =
      (Fintype.card {π : PermΩ W // v ∈ unusedImages W k π} : ENNReal) /
        (Fintype.card (PermΩ W) : ENNReal) := by
  classical
  let A : Finset (PermΩ W) := Finset.univ.filter (fun π => v ∈ unusedImages W k π)
  have hA : (A : Set (PermΩ W)) = {π | v ∈ unusedImages W k π} := by
    ext π
    simp [A]
  have hcard : A.card = Fintype.card {π : PermΩ W // v ∈ unusedImages W k π} := by
    rw [Fintype.card_subtype]
  rw [← hA, uniformPerm, ProbabilityTheory.uniformOn_univ,
    Measure.count_apply_finset, hcard]

/-- For a uniformly chosen permutation, a fixed value is still unused after
the first `k` positions with probability `(W-k)/W`. -/
theorem uniformPerm_unusedImages_marginal (W : ℕ) (k v : Fin W) :
    uniformPerm W {π : PermΩ W | v ∈ unusedImages W k π} =
      ((W - k.val : ℕ) : ENNReal) / (W : ENNReal) := by
  classical
  let hW : 0 < W := Nat.zero_lt_of_lt k.isLt
  let zero : Fin W := ⟨0, hW⟩
  have hfirst := uniformPerm_firstImage W hW v
  have hfirst' : uniformPerm W {ρ : PermΩ W | ρ (⟨0, hW⟩ : Fin W) = v} =
      (1 : ENNReal) / (W : ENNReal) := hfirst
  have hfirstCard :
      uniformPerm W {ρ : PermΩ W | ρ (⟨0, hW⟩ : Fin W) = v} =
        (Fintype.card {ρ : PermΩ W // ρ (⟨0, hW⟩ : Fin W) = v} : ENNReal) /
          (Fintype.card (PermΩ W) : ENNReal) := by
    classical
    let z : Fin W := ⟨0, hW⟩
    let A : Finset (PermΩ W) := Finset.univ.filter (fun ρ => ρ z = v)
    have hA : (A : Set (PermΩ W)) = {ρ | ρ z = v} := by
      ext ρ
      simp [A]
    have hcard : A.card = Fintype.card {ρ : PermΩ W // ρ z = v} := by
      rw [Fintype.card_subtype]
    simpa [z] using (show uniformPerm W {ρ | ρ z = v} =
      (Fintype.card {ρ : PermΩ W // ρ z = v} : ENNReal) /
        (Fintype.card (PermΩ W) : ENNReal) by
      rw [← hA, uniformPerm, ProbabilityTheory.uniformOn_univ,
        Measure.count_apply_finset, hcard])
  rw [uniformPerm_unused_event_card_ratio, unusedImages_event_card]
  rw [Nat.cast_mul]
  have hfirstFiber :
      (Fintype.card {ρ : PermΩ W // ρ (⟨0, hW⟩ : Fin W) = v} : ENNReal) /
          (Fintype.card (PermΩ W) : ENNReal) = (1 : ENNReal) / (W : ENNReal) := by
    rw [← hfirstCard]
    exact hfirst'
  calc
    ((W - k.val : ℕ) : ENNReal) *
        (Fintype.card {ρ : PermΩ W //
          ρ (⟨0, Nat.zero_lt_of_lt k.isLt⟩ : Fin W) = v} : ENNReal) /
        (Fintype.card (PermΩ W) : ENNReal) =
      ((W - k.val : ℕ) : ENNReal) *
        ((Fintype.card {ρ : PermΩ W //
          ρ (⟨0, hW⟩ : Fin W) = v} : ENNReal) /
            (Fintype.card (PermΩ W) : ENNReal)) := by
          rw [mul_div_assoc]
    _ = ((W - k.val : ℕ) : ENNReal) * ((1 : ENNReal) / (W : ENNReal)) := by
          rw [hfirstFiber]
    _ = ((W - k.val : ℕ) : ENNReal) / (W : ENNReal) := by
          rw [← mul_div_assoc, mul_one]

/-- The event has positive mass at every valid reveal index. -/
theorem uniformPerm_unusedImages_marginal_pos (W : ℕ) (k v : Fin W) :
    0 < uniformPerm W {π : PermΩ W | v ∈ unusedImages W k π} := by
  rw [uniformPerm_unusedImages_marginal]
  apply ENNReal.div_pos
  · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt k.isLt))
  · exact ENNReal.natCast_ne_top W

/-- The denominator `W` is positive and finite for every valid reveal index. -/
theorem unusedImages_marginal_denominator_pos_finite (W : ℕ) (k : Fin W) :
    0 < (W : ENNReal) ∧ (W : ENNReal) ≠ ⊤ := by
  have hW : 0 < W := Nat.zero_lt_of_lt k.isLt
  exact ⟨by exact_mod_cast hW, ENNReal.natCast_ne_top W⟩

/-- Width zero has no valid reveal index. -/
theorem unusedImages_marginal_no_index_zero : ¬ Nonempty (Fin 0) := by
  exact no_next_index_zero

/-- At width one and reveal index zero, the fixed value remains unused surely. -/
theorem uniformPerm_unusedImages_marginal_one :
    ∀ v : Fin 1,
      uniformPerm 1 {π : PermΩ 1 | v ∈ unusedImages 1 0 π} = 1 := by
  intro v
  simpa using uniformPerm_unusedImages_marginal 1 0 v

/-- At width two, the unused marginal is one at `k=0` and one half at `k=1`. -/
theorem uniformPerm_unusedImages_marginal_two :
    ∀ v : Fin 2,
      uniformPerm 2 {π : PermΩ 2 | v ∈ unusedImages 2 0 π} = 1 ∧
        uniformPerm 2 {π : PermΩ 2 | v ∈ unusedImages 2 1 π} =
          (1 : ENNReal) / 2 := by
  intro v
  constructor
  · rw [uniformPerm_unusedImages_marginal]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  · rw [uniformPerm_unusedImages_marginal]
    norm_num

/-- The last valid reveal leaves a specified value with probability `1/W`. -/
theorem uniformPerm_unusedImages_marginal_last (W : ℕ) (k v : Fin W)
    (hk : k.val + 1 = W) :
    uniformPerm W {π : PermΩ W | v ∈ unusedImages W k π} =
      (1 : ENNReal) / (W : ENNReal) := by
  rw [uniformPerm_unusedImages_marginal]
  have hsub : W - k.val = 1 := by omega
  rw [hsub]
  simp

/-- Identity and swap at width two witness a nonempty proper unused-value event. -/
theorem unusedImages_marginal_two_nontrivial :
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    idPerm ∈ {π : PermΩ 2 | (1 : Fin 2) ∈ unusedImages 2 1 π} ∧
      swapPerm ∉ {π : PermΩ 2 | (1 : Fin 2) ∈ unusedImages 2 1 π} ∧
      uniformPerm 2 {π : PermΩ 2 | (1 : Fin 2) ∈ unusedImages 2 1 π} =
        (1 : ENNReal) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [unusedImages]
  · simp [unusedImages]
  · simpa using uniformPerm_unusedImages_marginal 2 1 (1 : Fin 2)

#print axioms uniformPerm_unusedImages_marginal
#print axioms uniformPerm_unusedImages_marginal_pos
#print axioms unusedImages_marginal_denominator_pos_finite
#print axioms unusedImages_marginal_no_index_zero
#print axioms uniformPerm_unusedImages_marginal_one
#print axioms uniformPerm_unusedImages_marginal_two
#print axioms uniformPerm_unusedImages_marginal_last
#print axioms unusedImages_marginal_two_nontrivial

end RBM.Gauss
