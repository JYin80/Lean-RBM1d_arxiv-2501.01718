/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierDoobAzumaScalar
import RBM1D.Gauss.PermutationFourierComplexTailUnion
import RBM1D.Gauss.PermutationFourierMeanComponents

/-!
# Centered complex Fourier concentration on finite permutation spaces

The scalar actual-prefix Azuma tails and the four-event complex norm bridge give
a centered complex Fourier tail for a uniform random permutation. This is a
finite-permutation statement and has no Gaussian local-law content.
-/

open MeasureTheory

namespace RBM.Gauss

private noncomputable def permutationFourierComplexMean (W : ℕ) (x χ : Fin W → ℂ) : ℂ :=
  (∑ ρ : PermΩ W, permutationFourierSum W x χ ρ) /
    (Fintype.card (PermΩ W) : ℂ)

private theorem permutationFourierComplexMean_re (W : ℕ) (x χ : Fin W → ℂ) :
    (permutationFourierComplexMean W x χ).re =
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
        (Fintype.card (PermΩ W) : ℝ) := by
  simp only [permutationFourierComplexMean, Complex.div_re, Complex.re_sum,
    Complex.normSq_natCast, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, add_zero]
  have hcard : (Fintype.card (PermΩ W) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PermΩ W) ≠ 0)
  field_simp [hcard]
  ring

private theorem permutationFourierComplexMean_im (W : ℕ) (x χ : Fin W → ℂ) :
    (permutationFourierComplexMean W x χ).im =
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
        (Fintype.card (PermΩ W) : ℝ) := by
  simp only [permutationFourierComplexMean, Complex.div_im, Complex.im_sum,
    Complex.normSq_natCast, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, sub_zero]
  have hcard : (Fintype.card (PermΩ W) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PermΩ W) ≠ 0)
  field_simp [hcard]
  ring

/-- The centered complex Fourier observable has the exact finite-uniform tail
`4 exp (-W r² / 256)` for every `W ≥ 2`. -/
theorem uniformPerm_permutationFourierSum_centered_complex_tail
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) :
    (uniformPerm W).real {π |
      r ≤ ‖permutationFourierSum W x χ π - permutationFourierComplexMean W x χ‖} ≤
      4 * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
  let Z : PermΩ W → ℂ := fun π =>
    permutationFourierSum W x χ π - permutationFourierComplexMean W x χ
  let s : ℝ := r / Real.sqrt 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hReMean : (permutationFourierComplexMean W x χ).re =
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
        Fintype.card (PermΩ W) := permutationFourierComplexMean_re W x χ
  have hImMean : (permutationFourierComplexMean W x χ).im =
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
        Fintype.card (PermΩ W) := permutationFourierComplexMean_im W x χ
  have hRe : (uniformPerm W).real {π | s ≤ (Z π).re} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
    have h := uniformPerm_prefixFourierReal_centered_upper_tail W hW x χ hx hχ s hs
    convert h using 1 <;> congr 1 <;> ext π <;>
      simp [Z, Complex.sub_re, hReMean]
  have hNegRe : (uniformPerm W).real {π | s ≤ -(Z π).re} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
    have h := uniformPerm_prefixFourierReal_centered_lower_tail W hW x χ hx hχ s hs
    convert h using 1 <;> congr 1 <;> ext π <;>
      simp [Z, Complex.sub_re, hReMean]
  have hIm : (uniformPerm W).real {π | s ≤ (Z π).im} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
    have h := uniformPerm_prefixFourierImag_centered_upper_tail W hW x χ hx hχ s hs
    convert h using 1 <;> congr 1 <;> ext π <;>
      simp [Z, Complex.sub_im, hImMean]
  have hNegIm : (uniformPerm W).real {π | s ≤ -(Z π).im} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
    have h := uniformPerm_prefixFourierImag_centered_lower_tail W hW x χ hx hχ s hs
    convert h using 1 <;> congr 1 <;> ext π <;>
      simp [Z, Complex.sub_im, hImMean]
  have htail := uniformPerm_complexNorm_tail_of_signedCoordinate_tails
    W Z r (Real.exp (-(W : ℝ) * s ^ 2 / 128)) hr hRe hNegRe hIm hNegIm
  have hscale : 2 * s ^ 2 = r ^ 2 := by
    dsimp [s]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, hsqrt]
    field_simp
  have hexp : -(W : ℝ) * s ^ 2 / 128 = -(W : ℝ) * r ^ 2 / 256 := by
    calc
      -(W : ℝ) * s ^ 2 / 128 = -(W : ℝ) * (2 * s ^ 2) / 256 := by ring
      _ = -(W : ℝ) * r ^ 2 / 256 := by rw [hscale]
  simpa only [Z, s, hexp] using htail

/-- For a zero-sum character, the centered theorem specializes to the
uncentered Fourier sum. -/
theorem uniformPerm_permutationFourierSum_zeroCharacter_complex_tail
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχbound : ∀ i, ‖χ i‖ ≤ 1)
    (hχ : (∑ i : Fin W, χ i) = 0) (r : ℝ) (hr : 0 ≤ r) :
    (uniformPerm W).real {π | r ≤ ‖permutationFourierSum W x χ π‖} ≤
      4 * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
  have hmean := permutationFourierSum_mean_zero W hW x χ hχ
  have hcard : (Fintype.card (PermΩ W) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PermΩ W) ≠ 0)
  have hsum : (∑ ρ : PermΩ W, permutationFourierSum W x χ ρ) = 0 := by
    rcases (div_eq_zero_iff.mp hmean) with hsum | hzero
    · exact hsum
    · exact (hcard hzero).elim
  have hmean0 : permutationFourierComplexMean W x χ = 0 := by
    simp [permutationFourierComplexMean, hsum]
  simpa [hmean0] using
    uniformPerm_permutationFourierSum_centered_complex_tail W hW x χ hx hχbound r hr

/-- At widths zero and one, the permutation space is a singleton, so the
centered complex Fourier observable vanishes pointwise. -/
theorem permutationFourierComplexMean_singleton_widths
    (W : ℕ) (hW : W = 0 ∨ W = 1) (x χ : Fin W → ℂ) (π : PermΩ W) :
    permutationFourierSum W x χ π = permutationFourierComplexMean W x χ := by
  classical
  have hsub : Subsingleton (PermΩ W) := by
    rcases hW with rfl | rfl <;> infer_instance
  have hsum : (∑ ρ : PermΩ W, permutationFourierSum W x χ ρ) =
      (Fintype.card (PermΩ W) : ℂ) * permutationFourierSum W x χ π := by
    calc
      _ = ∑ _ρ : PermΩ W, permutationFourierSum W x χ π := by
        apply Finset.sum_congr rfl
        intro ρ _
        rw [show ρ = π from hsub.elim _ _]
      _ = _ := by simp
  dsimp [permutationFourierComplexMean]
  rw [hsum]
  symm
  exact mul_div_cancel_left₀ _
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PermΩ W) ≠ 0))

/-- At `W=0,1`, positive thresholds have an empty centered norm event and
therefore zero uniform measure. -/
theorem uniformPerm_permutationFourierSum_centered_singleton_tail
    (W : ℕ) (hW : W = 0 ∨ W = 1) (x χ : Fin W → ℂ) (r : ℝ) (hr : 0 < r) :
    (uniformPerm W).real {π |
      r ≤ ‖permutationFourierSum W x χ π - permutationFourierComplexMean W x χ‖} = 0 := by
  have hzero (π : PermΩ W) :
      permutationFourierSum W x χ π - permutationFourierComplexMean W x χ = 0 := by
    rw [permutationFourierComplexMean_singleton_widths W hW x χ π]
    simp
  have hempty : {π : PermΩ W | r ≤
      ‖permutationFourierSum W x χ π - permutationFourierComplexMean W x χ‖} = ∅ := by
    ext π
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [hzero π]
    simp [hr]
  rw [hempty]
  simp

/-- A concrete, nonconstant zero-sum `W=2` Fourier table has positive mass on
both permutations and a nonzero value at the identity. -/
theorem permutationFourierComplexConcentration_two_witness :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      (∑ i : Fin 2, χ i) = 0 ∧
      permutationFourierSum 2 x χ (Equiv.refl _) = 2 ∧
      permutationFourierSum 2 x χ (Equiv.swap 0 1) = -2 ∧
      permutationFourierComplexMean 2 x χ = 0 ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} := by
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 else -2
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  have hχ : (∑ i : Fin 2, χ i) = 0 := by norm_num [Fin.sum_univ_two, χ]
  have hvalues : permutationFourierSum 2 x χ (Equiv.refl _) = 2 ∧
      permutationFourierSum 2 x χ (Equiv.swap 0 1) = -2 := by
    constructor <;> norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hmean : permutationFourierComplexMean 2 x χ = 0 := by
    have h := permutationFourierSum_mean_zero 2 (by omega) x χ hχ
    simpa [permutationFourierComplexMean] using h
  refine ⟨x, χ, ?_, ?_, hχ, hvalues.1, hvalues.2, hmean, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x]
  · intro i
    fin_cases i <;> norm_num [χ]
  · rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    norm_num [Fintype.card_perm]
  · rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    norm_num [Fintype.card_perm]

#print axioms uniformPerm_permutationFourierSum_centered_complex_tail
#print axioms uniformPerm_permutationFourierSum_zeroCharacter_complex_tail
#print axioms permutationFourierComplexMean_singleton_widths
#print axioms uniformPerm_permutationFourierSum_centered_singleton_tail
#print axioms permutationFourierComplexConcentration_two_witness

end RBM.Gauss
