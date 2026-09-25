/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationUnusedImageCount
import RBM1D.Gauss.PermutationNextImageWeightedCondExp
import RBM1D.Gauss.PermutationPrefixCellMass

/-!
# Deterministic bound for a next-image centered increment

The next-image value and its average over the images unused before that
position both lie in the same deterministic interval. Their difference is
therefore bounded by the interval's diameter.
-/

namespace RBM.Gauss

/-- The next-image value differs from its actual unused-image average by at
most twice a uniform bound on the function. -/
theorem permutation_nextImage_increment_le
    (W : ℕ) (k : Fin W) (π : PermΩ W) (f : Fin W → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hf : ∀ v, |f v| ≤ C) :
    |f (π k) -
      (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ)| ≤ 2 * C := by
  have hden : 0 < ((W - k.val : ℕ) : ℝ) :=
    uniformPerm_nextImage_weighted_condExp_denominator_pos W k
  have hcard : ((unusedImages W k π).card : ℝ) =
      ((W - k.val : ℕ) : ℝ) := by
    exact_mod_cast (unusedImages_card W k π)
  have hsum : |∑ v ∈ unusedImages W k π, f v| ≤
      C * ((W - k.val : ℕ) : ℝ) := by
    calc
      |∑ v ∈ unusedImages W k π, f v| ≤
          ∑ v ∈ unusedImages W k π, |f v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ unusedImages W k π, C := by
        apply Finset.sum_le_sum
        intro v hv
        exact hf v
      _ = C * ((unusedImages W k π).card : ℝ) := by simp [mul_comm]
      _ = C * ((W - k.val : ℕ) : ℝ) := by rw [hcard]
  have hmean : |(∑ v ∈ unusedImages W k π, f v) /
      ((W - k.val : ℕ) : ℝ)| ≤ C := by
    rw [abs_div, abs_of_pos hden]
    rw [div_le_iff₀ hden]
    exact hsum
  calc
    |f (π k) - (∑ v ∈ unusedImages W k π, f v) /
        ((W - k.val : ℕ) : ℝ)|
        ≤ |f (π k)| + |(∑ v ∈ unusedImages W k π, f v) /
          ((W - k.val : ℕ) : ℝ)| := abs_sub _ _
    _ ≤ C + C := add_le_add (hf _) hmean
    _ = 2 * C := by ring

/-- At the final reveal, the unused-image average is exactly the revealed
value, so the centered increment vanishes. -/
theorem permutation_nextImage_increment_last_eq_zero
    (W : ℕ) (k : Fin W) (π : PermΩ W) (f : Fin W → ℝ)
    (hk : k.val + 1 = W) :
    f (π k) -
        (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ) = 0 := by
  have hmem : π k ∈ unusedImages W k π := by
    rw [mem_unusedImages_iff]
    intro i hik hEq
    exact (Fin.ne_of_lt hik) (π.injective hEq)
  have huniq : ∀ v ∈ unusedImages W k π, v = π k := by
    intro v hv
    rw [mem_unusedImages_iff] at hv
    by_contra hne
    have hpre : π.symm v < k := by
      apply Fin.lt_def.mpr
      by_contra hnot
      have hge : k.val ≤ (π.symm v).val := Nat.le_of_not_gt hnot
      have hlt : (π.symm v).val < W := (π.symm v).isLt
      have heq : (π.symm v).val = k.val := by omega
      have hfin : π.symm v = k := Fin.ext heq
      exact hne (by simpa [hfin] using (π.apply_symm_apply v).symm)
    exact hv (π.symm v) hpre (π.apply_symm_apply v)
  have hset : unusedImages W k π = {π k} := by
    ext v
    simp only [Finset.mem_singleton]
    constructor
    · exact huniq v
    · intro h
      simpa [h] using hmem
  have hden : (W - k.val : ℕ) = 1 := by omega
  rw [hset, hden]
  simp

/-- Width one consists of a deterministic final reveal. -/
theorem permutation_nextImage_increment_one_eq_zero
    (π : PermΩ 1) (f : Fin 1 → ℝ) :
    f (π 0) - (∑ v ∈ unusedImages 1 0 π, f v) / (1 : ℝ) = 0 := by
  simpa using permutation_nextImage_increment_last_eq_zero 1 (0 : Fin 1) π f
    (by norm_num)

/-- At width two, the nonconstant function `f(0)=0`, `f(1)=1` has centered
next-image values `-1/2` and `1/2` on the identity and transposition samples.
Each sample is a positive-mass atom of the uniform permutation measure. -/
theorem permutation_nextImage_increment_two_witness :
    let f : Fin 2 → ℝ := fun v => if v = 0 then 0 else 1
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    f 0 = 0 ∧ f 1 = 1 ∧
      0 < uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 idPerm} ∧
      0 < uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 swapPerm} ∧
      f (idPerm 0) -
          (∑ v ∈ unusedImages 2 0 idPerm, f v) / (2 : ℝ) = -(1 / 2 : ℝ) ∧
      f (swapPerm 0) -
          (∑ v ∈ unusedImages 2 0 swapPerm, f v) / (2 : ℝ) = 1 / 2 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · simpa using uniformPerm_prefixCell_event_pos 2 1 (Equiv.refl (Fin 2))
  · simpa using uniformPerm_prefixCell_event_pos 2 1 (Equiv.swap 0 1)
  · norm_num [unusedImages]
  · norm_num [unusedImages]

#print axioms permutation_nextImage_increment_le
#print axioms permutation_nextImage_increment_last_eq_zero
#print axioms permutation_nextImage_increment_one_eq_zero
#print axioms permutation_nextImage_increment_two_witness

end RBM.Gauss
