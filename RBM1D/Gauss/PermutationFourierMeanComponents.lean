/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierMean

/-!
# Real and imaginary parts of the uniform permutation Fourier mean

The scalar counting means are the real and imaginary parts of the same complex
mean, with the permutation-card denominator interpreted in `ℝ`.
-/

namespace RBM.Gauss

/-- The real component has zero uniform counting mean, retaining the full
permutation-card denominator. -/
theorem permutationFourierSum_re_mean_zero (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hχ : (∑ i : Fin W, χ i) = 0) :
    (∑ π : Equiv.Perm (Fin W), (permutationFourierSum W x χ π).re) /
      (Fintype.card (Equiv.Perm (Fin W)) : ℝ) = 0 := by
  have hmean := permutationFourierSum_mean_zero W hW x χ hχ
  have hcard : (Fintype.card (Equiv.Perm (Fin W)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin W)) ≠ 0)
  have hsum : (∑ π : Equiv.Perm (Fin W), permutationFourierSum W x χ π) = 0 := by
    rcases (div_eq_zero_iff.mp hmean) with hsum | hzero
    · exact hsum
    · exact (hcard hzero).elim
  have hsumRe :
      (∑ π : Equiv.Perm (Fin W), (permutationFourierSum W x χ π).re) = 0 := by
    rw [← Complex.re_sum]
    rw [hsum]
    simp
  rw [hsumRe, zero_div]

/-- The imaginary component has zero uniform counting mean, retaining the full
permutation-card denominator. -/
theorem permutationFourierSum_im_mean_zero (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hχ : (∑ i : Fin W, χ i) = 0) :
    (∑ π : Equiv.Perm (Fin W), (permutationFourierSum W x χ π).im) /
      (Fintype.card (Equiv.Perm (Fin W)) : ℝ) = 0 := by
  have hmean := permutationFourierSum_mean_zero W hW x χ hχ
  have hcard : (Fintype.card (Equiv.Perm (Fin W)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin W)) ≠ 0)
  have hsum : (∑ π : Equiv.Perm (Fin W), permutationFourierSum W x χ π) = 0 := by
    rcases (div_eq_zero_iff.mp hmean) with hsum | hzero
    · exact hsum
    · exact (hcard hzero).elim
  have hsumIm :
      (∑ π : Equiv.Perm (Fin W), (permutationFourierSum W x χ π).im) = 0 := by
    rw [← Complex.im_sum]
    rw [hsum]
    simp
  rw [hsumIm, zero_div]

/-- The nonconstant `W = 2` cancellation example from T684 also witnesses both
scalar component means: the identity Fourier value is nonzero although each
uniform counting mean vanishes. -/
theorem permutationFourierSum_components_mean_zero_witness_two :
    ∃ x χ : Fin 2 → ℂ,
      x 0 ≠ x 1 ∧ χ 0 ≠ χ 1 ∧
      (∑ i : Fin 2, χ i) = 0 ∧
      permutationFourierSum 2 x χ (Equiv.refl _) ≠ 0 ∧
      (∑ π : Equiv.Perm (Fin 2), (permutationFourierSum 2 x χ π).re) /
        (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) = 0 ∧
      (∑ π : Equiv.Perm (Fin 2), (permutationFourierSum 2 x χ π).im) /
        (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) = 0 := by
  obtain ⟨x, χ, hx, hχnc, hχ, hidentity, _⟩ :=
    permutationFourierSum_mean_zero_witness_two
  exact ⟨x, χ, hx, hχnc, hχ, hidentity,
    permutationFourierSum_re_mean_zero 2 (by omega) x χ hχ,
    permutationFourierSum_im_mean_zero 2 (by omega) x χ hχ⟩

#print axioms permutationFourierSum_re_mean_zero
#print axioms permutationFourierSum_im_mean_zero
#print axioms permutationFourierSum_components_mean_zero_witness_two

end RBM.Gauss
