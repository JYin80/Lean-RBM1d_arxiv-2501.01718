/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierDoobComponents
import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional MGF of actual-prefix Fourier Doob increments

The real and imaginary finite-cell increments are conditionally centered and
obey a conditional Hoeffding bound on one set of prefixes for all real MGF
arguments. These are finite-permutation auxiliary statements.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

private theorem prefixCellMean_increment_condExp_zero
    (W : ℕ) (k : Fin W) (F : PermΩ W → ℝ)
    (hmeas : Measurable[prefixSigma W k.val] (prefixCellMean W k.val F)) :
    (uniformPerm W)[(fun π => prefixCellMean W (k.val + 1) F π -
      prefixCellMean W k.val F π) | prefixSigma W k.val]
        =ᵐ[uniformPerm W] (fun _ => (0 : ℝ)) := by
  let μ : Measure (PermΩ W) := uniformPerm W
  let m₀ := prefixSigma W k.val
  let m₁ := prefixSigma W (k.val + 1)
  let M₀ := prefixCellMean W k.val F
  let M₁ := prefixCellMean W (k.val + 1) F
  have hmono : m₀ ≤ m₁ := prefixSigma_mono W (by omega : k.val ≤ k.val + 1)
  have hsucc : μ[F | m₁] =ᵐ[μ] M₁ := uniformPerm_prefixCell_condExp W (k.val + 1) F
  have hcur : μ[F | m₀] =ᵐ[μ] M₀ := uniformPerm_prefixCell_condExp W k.val F
  have htower : μ[μ[F | m₁] | m₀] =ᵐ[μ] μ[F | m₀] :=
    condExp_condExp_of_le hmono le_top
  have hnext : μ[M₁ | m₀] =ᵐ[μ] M₀ :=
    (condExp_congr_ae hsucc.symm).trans (htower.trans hcur)
  have hprev : μ[M₀ | m₀] = M₀ :=
    condExp_of_stronglyMeasurable le_top hmeas.stronglyMeasurable Integrable.of_finite
  have hsub : μ[M₁ - M₀ | m₀] =ᵐ[μ] μ[M₁ | m₀] - μ[M₀ | m₀] :=
    condExp_sub Integrable.of_finite Integrable.of_finite m₀
  filter_upwards [hsub, hnext] with π hsubπ hnextπ
  change μ[M₁ - M₀ | m₀] π = 0
  simp only [Pi.sub_apply] at hsubπ
  rw [hsubπ, hnextπ, hprev]
  ring

/-- The real actual-prefix Fourier Doob increment has conditional mean zero. -/
theorem uniformPerm_prefixFourierReal_increment_condExp_zero
    (W : ℕ) (k : Fin W) (x χ : Fin W → ℂ) :
    (uniformPerm W)[(fun π =>
      prefixFourierRealMean W (k.val + 1) x χ π -
      prefixFourierRealMean W k.val x χ π) | prefixSigma W k.val]
        =ᵐ[uniformPerm W] (fun _ => (0 : ℝ)) := by
  exact prefixCellMean_increment_condExp_zero W k
    (fun π => (permutationFourierSum W x χ π).re)
    (prefixFourierRealMean_measurable W k.val x χ)

/-- The imaginary actual-prefix Fourier Doob increment has conditional mean zero. -/
theorem uniformPerm_prefixFourierImag_increment_condExp_zero
    (W : ℕ) (k : Fin W) (x χ : Fin W → ℂ) :
    (uniformPerm W)[(fun π =>
      prefixFourierImagMean W (k.val + 1) x χ π -
      prefixFourierImagMean W k.val x χ π) | prefixSigma W k.val]
        =ᵐ[uniformPerm W] (fun _ => (0 : ℝ)) := by
  exact prefixCellMean_increment_condExp_zero W k
    (fun π => (permutationFourierSum W x χ π).im)
    (prefixFourierImagMean_measurable W k.val x χ)

private theorem actualPrefix_increment_hasCondSubgaussianMGF
    (W : ℕ) (hW : 2 ≤ W) (k : Fin W) (d : PermΩ W → ℝ)
    (hmean : (uniformPerm W)[d | prefixSigma W k.val]
      =ᵐ[uniformPerm W] (fun _ => (0 : ℝ)))
    (hbound : ∀ π, |d π| ≤ 8 / (W : ℝ)) :
    HasCondSubgaussianMGF (prefixSigma W k.val) le_top d
      ⟨64 / (W : ℝ) ^ 2, by positivity⟩ (uniformPerm W) := by
  let a : ℝ := 8 / (W : ℝ)
  let μ : Measure (PermΩ W) := uniformPerm W
  let κ : @Kernel (PermΩ W) (PermΩ W) (prefixSigma W k.val)
      (permΩMeasurableSpace W) :=
    condExpKernel (mΩ := permΩMeasurableSpace W) μ (prefixSigma W k.val)
  let ν : @Measure (PermΩ W) (prefixSigma W k.val) :=
    μ.trim (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd_bound (π : PermΩ W) : d π ∈ Set.Icc (-a) a := by
    exact abs_le.mp (hbound π)
  have hd_int : Integrable d μ := Integrable.of_finite
  have hmean_ν : μ[d | prefixSigma W k.val] =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable
      (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top)
      stronglyMeasurable_condExp stronglyMeasurable_const hmean
  have hkernel_mean : ∀ᵐ π ∂ν, (∫ ρ, d ρ ∂κ π) = 0 := by
    have hbridge := condExp_ae_eq_trim_integral_condExpKernel
      (mΩ := permΩMeasurableSpace W) (μ := μ) (m := prefixSigma W k.val)
      (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top) hd_int
    filter_upwards [hbridge, hmean_ν] with π hbridgeπ hzeroπ
    exact hbridgeπ.symm.trans hzeroπ
  change Kernel.HasSubgaussianMGF d ⟨64 / (W : ℝ) ^ 2, by positivity⟩ κ ν
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim (mΩ := permΩMeasurableSpace W)
      (μ := μ) (m := prefixSigma W k.val)
      (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top)]
    exact Integrable.of_finite
  · filter_upwards [hkernel_mean] with π hπ t
    have hHoeffding :
        HasSubgaussianMGF d ((‖a - (-a)‖₊ / 2) ^ 2) (κ π) := by
      apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      · exact (show @Measurable (PermΩ W) ℝ (permΩMeasurableSpace W) _ d from
          measurable_of_finite _).aemeasurable
      · exact Filter.Eventually.of_forall hd_bound
      · exact hπ
    have hWne : (W : ℝ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
    have hparam : ((‖a - (-a)‖₊ / 2) ^ 2 : NNReal) =
        ⟨64 / (W : ℝ) ^ 2, by positivity⟩ := by
      ext
      simp only [nnnorm, Real.norm_eq_abs, NNReal.coe_pow, NNReal.coe_div,
        NNReal.coe_ofNat, NNReal.coe_mk]
      rw [abs_of_nonneg (show 0 ≤ a - -a by nlinarith)]
      change ((a - -a) / (2 : ℝ)) ^ 2 = 64 / (W : ℝ) ^ 2
      dsimp [a]
      field_simp
      ring
    rw [← hparam]
    exact hHoeffding.mgf_le t

/-- The real Fourier actual-prefix increment has the conditional Hoeffding
parameter `64/W²`, for all real MGF arguments on one a.e. set. -/
theorem uniformPerm_prefixFourierReal_hasCondSubgaussianMGF
    (W : ℕ) (hW : 2 ≤ W) (k : Fin W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) :
    HasCondSubgaussianMGF (prefixSigma W k.val) le_top
      (fun π : PermΩ W => prefixFourierRealMean W (k.val + 1) x χ π -
        prefixFourierRealMean W k.val x χ π)
      ⟨64 / (W : ℝ) ^ 2, by positivity⟩ (uniformPerm W) := by
  apply actualPrefix_increment_hasCondSubgaussianMGF W hW k
  · exact uniformPerm_prefixFourierReal_increment_condExp_zero W k x χ
  · intro π
    exact abs_prefixFourierRealMean_increment_le W hW k x χ hx hχ π

/-- The imaginary Fourier actual-prefix increment has the conditional
Hoeffding parameter `64/W²`. -/
theorem uniformPerm_prefixFourierImag_hasCondSubgaussianMGF
    (W : ℕ) (hW : 2 ≤ W) (k : Fin W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) :
    HasCondSubgaussianMGF (prefixSigma W k.val) le_top
      (fun π : PermΩ W => prefixFourierImagMean W (k.val + 1) x χ π -
        prefixFourierImagMean W k.val x χ π)
      ⟨64 / (W : ℝ) ^ 2, by positivity⟩ (uniformPerm W) := by
  apply actualPrefix_increment_hasCondSubgaussianMGF W hW k
  · exact uniformPerm_prefixFourierImag_increment_condExp_zero W k x χ
  · intro π
    exact abs_prefixFourierImagMean_increment_le W hW k x χ hx hχ π

/-- At width two, both possible permutations have positive mass, and the
first real Fourier Doob increment is nonzero at the identity. The conditional
MGF bound applies to this genuinely nonconstant example. -/
theorem uniformPerm_prefixFourier_condMGF_two_witness :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} ∧
      prefixFourierRealMean 2 1 x χ (Equiv.refl _) -
        prefixFourierRealMean 2 0 x χ (Equiv.refl _) = 2 ∧
      HasCondSubgaussianMGF (prefixSigma 2 0) le_top
        (fun π : PermΩ 2 => prefixFourierRealMean 2 1 x χ π -
          prefixFourierRealMean 2 0 x χ π)
        ⟨16, by norm_num⟩ (uniformPerm 2) := by
  obtain ⟨x, χ, hx, hχ, h0, h1⟩ :=
    prefixFourierRealMean_two_nonconstant_witness
  obtain ⟨_, _, _, _, _, hid, hswap⟩ := prefixCellMean_two_zero_indicator
  refine ⟨x, χ, hx, hχ, hid, hswap, ?_, ?_⟩
  · rw [h0, h1]
    norm_num
  · have hparam : (⟨64 / (2 : ℝ) ^ 2, by positivity⟩ : NNReal) =
        ⟨16, by norm_num⟩ := by
      ext
      norm_num
    rw [← hparam]
    exact uniformPerm_prefixFourierReal_hasCondSubgaussianMGF
      2 (by norm_num) 0 x χ hx hχ

#print axioms uniformPerm_prefixFourierReal_increment_condExp_zero
#print axioms uniformPerm_prefixFourierImag_increment_condExp_zero
#print axioms uniformPerm_prefixFourierReal_hasCondSubgaussianMGF
#print axioms uniformPerm_prefixFourierImag_hasCondSubgaussianMGF
#print axioms uniformPerm_prefixFourier_condMGF_two_witness

end RBM.Gauss
