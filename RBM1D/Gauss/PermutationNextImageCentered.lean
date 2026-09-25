/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageWeightedCondExp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Centered next-image martingale difference

The next image minus its unused-image average has conditional expectation zero
given the permutation prefix. This is a finite-permutation auxiliary result.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

/-- The average of `f` over the values not yet used before position `k`. -/
noncomputable def unusedImageAverage (W : ℕ) (k : Fin W) (f : Fin W → ℝ) :
    PermΩ W → ℝ := fun π =>
      (∑ v : Fin W, if v ∈ unusedImages W k π then f v else 0) /
        ((W - k.val : ℕ) : ℝ)

private theorem unusedImageAverage_eq (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) (π : PermΩ W) :
    unusedImageAverage W k f π =
      (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ) := by
  unfold unusedImageAverage
  rw [← Finset.sum_filter]
  congr 1
  simp [unusedImages]

private theorem unusedImageAverage_measurable (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) :
    Measurable[prefixSigma W k.val] (unusedImageAverage W k f) := by
  classical
  unfold unusedImageAverage
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro v hv
  exact Measurable.ite (measurableSet_unusedImage_prefixSigma W k v)
    measurable_const measurable_const

private theorem unusedImageAverage_integrable (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) : Integrable (unusedImageAverage W k f) (uniformPerm W) :=
  Integrable.of_finite

/-- For every finite width, valid reveal position, and real-valued function,
the next-image fluctuation about its remaining-image mean is a martingale
difference for the prefix filtration. -/
theorem uniformPerm_nextImage_centered_condExp
    (W : ℕ) (k : Fin W) (f : Fin W → ℝ) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      f (ρ k) - unusedImageAverage W k f ρ) | prefixSigma W k.val]
      =ᵐ[uniformPerm W] (fun _ => 0) := by
  have hnext := uniformPerm_nextImage_weighted_condExp W k f
  have hmean :
      (uniformPerm W)[unusedImageAverage W k f | prefixSigma W k.val]
        =ᵐ[uniformPerm W] unusedImageAverage W k f := by
    have hEq := condExp_of_stronglyMeasurable
      (show prefixSigma W k.val ≤ ⊤ from le_top)
      ((unusedImageAverage_measurable W k f).stronglyMeasurable)
      (unusedImageAverage_integrable W k f)
    filter_upwards [] with π
    exact congrFun hEq π
  have hsub := condExp_sub (μ := uniformPerm W)
    (m := prefixSigma W k.val)
    (Integrable.of_finite : Integrable (fun ρ : PermΩ W => f (ρ k)) (uniformPerm W))
    (unusedImageAverage_integrable W k f)
  filter_upwards [hsub, hnext, hmean] with π hπ hnextπ hmeanπ
  change (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k)) - unusedImageAverage W k f |
    prefixSigma W k.val] π = 0
  rw [hπ, Pi.sub_apply, hnextπ, hmeanπ, unusedImageAverage_eq W k f π]
  ring

/-- The denominator in the remaining-image average is strictly positive for
every valid `Fin W` reveal position. -/
theorem unusedImageAverage_denominator_pos
    (W : ℕ) (k : Fin W) : 0 < ((W - k.val : ℕ) : ℝ) := by
  exact uniformPerm_nextImage_weighted_condExp_denominator_pos W k

/-- With one value, the centered next-image fluctuation vanishes at every
permutation, not merely almost everywhere. -/
theorem uniformPerm_nextImage_centered_one_pointwise (f : Fin 1 → ℝ)
    (π : PermΩ 1) :
    f (π 0) - unusedImageAverage 1 0 f π = 0 := by
  have hπ : π 0 = (0 : Fin 1) := Fin.eq_zero (π 0)
  simp [unusedImageAverage, unusedImages, hπ]

private theorem unusedImages_eq_singleton_last (W : ℕ) (k : Fin W)
    (π : PermΩ W) (hk : k.val + 1 = W) :
    unusedImages W k π = {π k} := by
  classical
  ext v
  rw [Finset.mem_singleton]
  rw [mem_unusedImages_iff]
  constructor
  · intro hv
    have hnot : ¬ (π.symm v).val < k.val := by
      intro hlt
      have h := hv (π.symm v) (Fin.lt_def.mpr hlt)
      exact h (π.apply_symm_apply v)
    have hge : k.val ≤ (π.symm v).val := Nat.le_of_not_gt hnot
    have hle : (π.symm v).val ≤ k.val := by omega
    have heq : π.symm v = k := Fin.ext (by omega)
    simpa using congrArg π heq
  · intro hv i hi heq
    subst v
    have hidx : i = k := π.injective heq
    subst i
    exact (Fin.lt_irrefl k hi).elim

/-- At the final reveal, the unused-image average is the actual next value,
so centering vanishes pointwise. -/
theorem uniformPerm_nextImage_centered_last_pointwise
    (W : ℕ) (k : Fin W) (f : Fin W → ℝ) (π : PermΩ W)
    (hk : k.val + 1 = W) :
    f (π k) - unusedImageAverage W k f π = 0 := by
  have hden : W - k.val = 1 := by omega
  rw [unusedImageAverage_eq, unusedImages_eq_singleton_last W k π hk]
  simp [hden]

/-- At width two and reveal position zero, a nonconstant function gives
centered outcomes `-1/2` and `1/2`, each on a positive-mass atom. -/
theorem uniformPerm_nextImage_centered_two_witness :
    let f : Fin 2 → ℝ := fun v => if v = 0 then 0 else 1
    f 0 ≠ f 1 ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} ∧
      (f ((Equiv.refl (Fin 2) : PermΩ 2) 0) -
        unusedImageAverage 2 0 f (Equiv.refl (Fin 2) : PermΩ 2) = -(1 / 2 : ℝ)) ∧
      (f ((Equiv.swap 0 1 : PermΩ 2) 0) -
        unusedImageAverage 2 0 f (Equiv.swap 0 1 : PermΩ 2) = 1 / 2) := by
  dsimp
  have hId := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
    (Equiv.refl (Fin 2) : PermΩ 2)).2
  have hSwap := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
    (Equiv.swap 0 1 : PermΩ 2)).2
  have hId' : 0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} := by
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using hId
  have hSwap' : 0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} := by
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using hSwap
  have havg (π : PermΩ 2) :
      unusedImageAverage 2 0 (fun v : Fin 2 => if v = 0 then 0 else 1) π = 1 / 2 := by
    simp [unusedImageAverage, unusedImages]
  refine ⟨by norm_num, hId', hSwap', ?_, ?_⟩ <;>
    simp [havg] <;> norm_num

#print axioms unusedImageAverage
#print axioms uniformPerm_nextImage_centered_condExp
#print axioms unusedImageAverage_denominator_pos
#print axioms uniformPerm_nextImage_centered_one_pointwise
#print axioms unusedImages_eq_singleton_last
#print axioms uniformPerm_nextImage_centered_last_pointwise
#print axioms uniformPerm_nextImage_centered_two_witness

end RBM.Gauss
