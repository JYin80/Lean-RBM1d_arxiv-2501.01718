/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageCentered
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional variance of the next image

For a uniform finite permutation, the conditional variance of the next image
under the generated prefix filtration is the variance of the function over
the images not yet used.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

private theorem varianceAverage_eq_sum (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) (π : PermΩ W) :
    unusedImageAverage W k f π =
      (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ) := by
  unfold unusedImageAverage
  rw [← Finset.sum_filter]
  congr 1
  simp [unusedImages]

private theorem varianceAverage_measurable (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) :
    Measurable[prefixSigma W k.val] (unusedImageAverage W k f) := by
  classical
  unfold unusedImageAverage
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro v hv
  exact Measurable.ite (measurableSet_unusedImage_prefixSigma W k v)
    measurable_const measurable_const

private theorem varianceAverage_integrable (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) : Integrable (unusedImageAverage W k f) (uniformPerm W) :=
  Integrable.of_finite

/-- Conditional variance of a deterministic observable of the next image is
the variance of that observable over the unused images. -/
theorem uniformPerm_nextImage_conditionalVariance
    (W : ℕ) (k : Fin W) (f : Fin W → ℝ) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      (f (ρ k) - unusedImageAverage W k f ρ) ^ 2) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      unusedImageAverage W k (fun v => (f v) ^ 2) π -
        (unusedImageAverage W k f π) ^ 2) := by
  let X : PermΩ W → ℝ := fun ρ => f (ρ k)
  let M : PermΩ W → ℝ := unusedImageAverage W k f
  let X2 : PermΩ W → ℝ := fun ρ => (f (ρ k)) ^ 2
  let G : PermΩ W → ℝ := (2 : ℝ) • M
  let C : PermΩ W → ℝ := G * X
  let Y : PermΩ W → ℝ := X2 - C
  have hX : Integrable X (uniformPerm W) := Integrable.of_finite
  have hX2 : Integrable X2 (uniformPerm W) := Integrable.of_finite
  have hM2 : Integrable (fun π => M π ^ 2) (uniformPerm W) := Integrable.of_finite
  have hC : Integrable C (uniformPerm W) := Integrable.of_finite
  have hY : Integrable Y (uniformPerm W) := Integrable.of_finite
  have hcenter : Integrable (fun π => (X π - M π) ^ 2) (uniformPerm W) :=
    Integrable.of_finite
  have hMsm : StronglyMeasurable[prefixSigma W k.val] M :=
    (varianceAverage_measurable W k f).stronglyMeasurable
  have h2Msm : StronglyMeasurable[prefixSigma W k.val] G := by
    exact hMsm.const_smul (2 : ℝ)
  have hM2cond :
      (uniformPerm W)[(fun π => M π ^ 2) | prefixSigma W k.val]
        =ᵐ[uniformPerm W] fun π => M π ^ 2 := by
    have h := condExp_of_stronglyMeasurable
      (show prefixSigma W k.val ≤ ⊤ from le_top)
      (hMsm.pow 2) hM2
    filter_upwards [] with π
    exact congrFun h π
  have hXcond := uniformPerm_nextImage_weighted_condExp W k f
  have hX2cond := uniformPerm_nextImage_weighted_condExp W k (fun v => (f v) ^ 2)
  have hcross :
      (uniformPerm W)[C | prefixSigma W k.val]
        =ᵐ[uniformPerm W] fun π => 2 * (M π *
          (uniformPerm W)[X | prefixSigma W k.val] π) := by
    have hmul := condExp_mul_of_stronglyMeasurable_left
      (μ := uniformPerm W) (m := prefixSigma W k.val) h2Msm hC hX
    filter_upwards [hmul] with π hπ
    change (uniformPerm W)[(G * X) | prefixSigma W k.val] π = _ at hπ
    rw [hπ]
    simp [G, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hexpand :
      (fun π : PermΩ W => (X π - M π) ^ 2) = Y + (fun π => M π ^ 2) := by
    funext π
    dsimp [Y, C, G, X, X2, M]
    ring
  have hlinear :
      (uniformPerm W)[Y + (fun π => M π ^ 2) | prefixSigma W k.val]
        =ᵐ[uniformPerm W]
      fun π => (uniformPerm W)[X2 | prefixSigma W k.val] π -
        (uniformPerm W)[C | prefixSigma W k.val] π +
        (uniformPerm W)[(fun π => M π ^ 2) | prefixSigma W k.val] π := by
    have hsub := condExp_sub (μ := uniformPerm W) (m := prefixSigma W k.val)
      hX2 hC
    have hadd := condExp_add (μ := uniformPerm W) (m := prefixSigma W k.val)
      hY hM2
    filter_upwards [hsub, hadd] with π hsubπ haddπ
    calc
      (uniformPerm W)[Y + (fun π => M π ^ 2) | prefixSigma W k.val] π =
          ((uniformPerm W)[Y | prefixSigma W k.val] +
            (uniformPerm W)[(fun π => M π ^ 2) | prefixSigma W k.val]) π := haddπ
      _ = _ := by
        simp only [Pi.add_apply, Pi.sub_apply] at hsubπ ⊢
        rw [hsubπ]
  have hcenterExpand := condExp_congr_ae (μ := uniformPerm W)
    (m := prefixSigma W k.val) (Filter.Eventually.of_forall (fun π => congrFun hexpand π))
  filter_upwards [hcenterExpand, hlinear, hX2cond, hXcond, hcross,
    hM2cond] with π hce hlin hX2π hXπ hcrossπ hM2π
  rw [hce, hlin, hX2π, hcrossπ, hM2π, hXπ]
  rw [varianceAverage_eq_sum W k (fun v => (f v) ^ 2) π,
    varianceAverage_eq_sum W k f π]
  rw [← varianceAverage_eq_sum W k f π]
  ring

/-- At width two, the nonconstant observable on the two values has conditional
variance `1/4` at the first reveal, on both positive-mass permutations. -/
theorem uniformPerm_nextImage_conditionalVariance_two_witness :
    let f : Fin 2 → ℝ := fun v => if v = 0 then 0 else 1
    f 0 ≠ f 1 ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} ∧
      (uniformPerm 2)[(fun ρ : PermΩ 2 =>
        (f (ρ 0) - unusedImageAverage 2 0 f ρ) ^ 2) | prefixSigma 2 0]
          =ᵐ[uniformPerm 2] (fun _ => (1 / 4 : ℝ)) := by
  dsimp
  have hId := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
    (Equiv.refl (Fin 2) : PermΩ 2)).2
  have hSwap := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
    (Equiv.swap 0 1 : PermΩ 2)).2
  have hId' : 0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} := by
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using hId
  have hSwap' : 0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} := by
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using hSwap
  refine ⟨by norm_num, hId', hSwap', ?_⟩
  have h := uniformPerm_nextImage_conditionalVariance 2 0
    (fun v : Fin 2 => if v = 0 then 0 else 1)
  have havg (π : PermΩ 2) :
      unusedImageAverage 2 0 (fun v : Fin 2 => if v = 0 then 0 else 1) π = 1 / 2 := by
    simp [unusedImageAverage, unusedImages]
  have hsq (π : PermΩ 2) :
      unusedImageAverage 2 0
        (fun v : Fin 2 => (if v = 0 then 0 else 1) ^ 2) π = 1 / 2 := by
    simp [unusedImageAverage, unusedImages]
  filter_upwards [h] with π hπ
  rw [havg, hsq] at hπ
  norm_num at hπ ⊢
  exact hπ

/-- With one available image, the conditional variance is zero. -/
theorem uniformPerm_nextImage_conditionalVariance_one (f : Fin 1 → ℝ) :
    (fun π : PermΩ 1 =>
      unusedImageAverage 1 0 (fun v => (f v) ^ 2) π -
        (unusedImageAverage 1 0 f π) ^ 2) =ᵐ[uniformPerm 1] fun _ => 0 := by
  have hvar := uniformPerm_nextImage_conditionalVariance 1 0 f
  have hcenter :
      (fun π : PermΩ 1 => (f (π 0) - unusedImageAverage 1 0 f π) ^ 2) =
        fun _ => 0 := by
    funext π
    rw [uniformPerm_nextImage_centered_one_pointwise]
    simp
  have hzero := condExp_congr_ae (μ := uniformPerm 1)
    (m := prefixSigma 1 0) (Filter.Eventually.of_forall (fun π => congrFun hcenter π))
  filter_upwards [hvar, hzero] with π hvarπ hzeroπ
  have hzeroπ' :
      (uniformPerm 1)[(fun ρ : PermΩ 1 =>
        (f (ρ 0) - unusedImageAverage 1 0 f ρ) ^ 2) | prefixSigma 1 0] π = 0 := by
    simpa using hzeroπ
  exact hvarπ.symm.trans hzeroπ'

/-- At the last reveal, exactly one image remains, so the conditional
variance is zero. -/
theorem uniformPerm_nextImage_conditionalVariance_last (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) (hk : k.val + 1 = W) :
    (fun π : PermΩ W =>
      unusedImageAverage W k (fun v => (f v) ^ 2) π -
        (unusedImageAverage W k f π) ^ 2) =ᵐ[uniformPerm W] fun _ => 0 := by
  have hvar := uniformPerm_nextImage_conditionalVariance W k f
  have hcenter :
      (fun π : PermΩ W => (f (π k) - unusedImageAverage W k f π) ^ 2) =
        fun _ => 0 := by
    funext π
    rw [uniformPerm_nextImage_centered_last_pointwise W k f π hk]
    simp
  have hzero := condExp_congr_ae (μ := uniformPerm W)
    (m := prefixSigma W k.val) (Filter.Eventually.of_forall (fun π => congrFun hcenter π))
  filter_upwards [hvar, hzero] with π hvarπ hzeroπ
  have hzeroπ' :
      (uniformPerm W)[(fun ρ : PermΩ W =>
        (f (ρ k) - unusedImageAverage W k f ρ) ^ 2) | prefixSigma W k] π = 0 := by
    simpa using hzeroπ
  exact hvarπ.symm.trans hzeroπ'

#print axioms uniformPerm_nextImage_conditionalVariance
#print axioms uniformPerm_nextImage_conditionalVariance_two_witness
#print axioms uniformPerm_nextImage_conditionalVariance_one
#print axioms uniformPerm_nextImage_conditionalVariance_last

end RBM.Gauss
