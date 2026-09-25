/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageCentered
import RBM1D.Gauss.PermutationNextImageIncrementBound
import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional Hoeffding bound for a finite permutation reveal

The centered next image has a conditional sub-Gaussian moment-generating
function, with all real arguments controlled on one set of prefixes of full
measure. This is a finite-permutation auxiliary statement.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

/-- The bounded centered next-image increment has conditional sub-Gaussian
MGF parameter `4 C²` for the prefix before position `k`. -/
theorem uniformPerm_nextImage_hasCondSubgaussianMGF
    (W : ℕ) (k : Fin W) (f : Fin W → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ v, |f v| ≤ C) :
    HasCondSubgaussianMGF (prefixSigma W k.val) le_top
      (fun π : PermΩ W => f (π k) - unusedImageAverage W k f π)
      ⟨4 * C ^ 2, by positivity⟩ (uniformPerm W) := by
  let d : PermΩ W → ℝ := fun π => f (π k) - unusedImageAverage W k f π
  let μ : Measure (PermΩ W) := uniformPerm W
  let κ : @Kernel (PermΩ W) (PermΩ W) (prefixSigma W k.val)
      (permΩMeasurableSpace W) :=
    condExpKernel (mΩ := permΩMeasurableSpace W) μ (prefixSigma W k.val)
  let ν : @Measure (PermΩ W) (prefixSigma W k.val) :=
    μ.trim (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top)
  have hd_bound (π : PermΩ W) : d π ∈ Set.Icc (-(2 * C)) (2 * C) := by
    have hb := permutation_nextImage_increment_le W k π f C hC hf
    have hb' : |d π| ≤ 2 * C := by
      change |f (π k) -
        (∑ v : Fin W, if v ∈ unusedImages W k π then f v else 0) /
          ((W - k.val : ℕ) : ℝ)| ≤ 2 * C
      simpa [Finset.sum_filter] using hb
    exact abs_le.mp hb'
  have hd_int : Integrable d μ := Integrable.of_finite
  have hmean_μ : μ[d | prefixSigma W k.val] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    simpa only [d, μ] using uniformPerm_nextImage_centered_condExp W k f
  have hmean_ν : μ[d | prefixSigma W k.val] =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable
      (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top)
      stronglyMeasurable_condExp
      stronglyMeasurable_const hmean_μ
  have hkernel_mean : ∀ᵐ π ∂ν, (∫ ρ, d ρ ∂κ π) = 0 := by
    have hbridge := condExp_ae_eq_trim_integral_condExpKernel
      (mΩ := permΩMeasurableSpace W) (μ := μ) (m := prefixSigma W k.val)
      (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top) hd_int
    filter_upwards [hbridge, hmean_ν] with π hbridgeπ hzeroπ
    exact hbridgeπ.symm.trans hzeroπ
  change Kernel.HasSubgaussianMGF d ⟨4 * C ^ 2, by positivity⟩ κ ν
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim (mΩ := permΩMeasurableSpace W)
      (μ := μ) (m := prefixSigma W k.val)
      (show prefixSigma W k.val ≤ permΩMeasurableSpace W from le_top)]
    exact Integrable.of_finite
  · filter_upwards [hkernel_mean] with π hπ t
    have hHoeffding :
        HasSubgaussianMGF d ((‖(2 * C) - (-(2 * C))‖₊ / 2) ^ 2) (κ π) := by
      apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      · exact (show @Measurable (PermΩ W) ℝ (permΩMeasurableSpace W) _ d from
          measurable_of_finite _).aemeasurable
      · exact Filter.Eventually.of_forall hd_bound
      · exact hπ
    have hparam : ((‖(2 * C) - (-(2 * C))‖₊ / 2) ^ 2 : NNReal) =
        ⟨4 * C ^ 2, by positivity⟩ := by
      ext
      simp only [nnnorm, Real.norm_eq_abs, NNReal.coe_pow, NNReal.coe_div,
        NNReal.coe_ofNat, NNReal.coe_mk]
      rw [abs_of_nonneg (show 0 ≤ 2 * C - -(2 * C) by nlinarith)]
      change ((2 * C - -(2 * C)) / (2 : ℝ)) ^ 2 = 4 * C ^ 2
      ring
    rw [← hparam]
    exact hHoeffding.mgf_le t

/-- The conditional MGF statement covers a genuinely random centered first
reveal at width two, with positive mass on both distinct outcomes. -/
theorem uniformPerm_nextImage_condMGF_two_witness :
    let f : Fin 2 → ℝ := fun v => if v = 0 then 0 else 1
    f 0 ≠ f 1 ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} ∧
      (f ((Equiv.refl (Fin 2) : PermΩ 2) 0) -
        unusedImageAverage 2 0 f (Equiv.refl (Fin 2) : PermΩ 2) = -(1 / 2 : ℝ)) ∧
      (f ((Equiv.swap 0 1 : PermΩ 2) 0) -
        unusedImageAverage 2 0 f (Equiv.swap 0 1 : PermΩ 2) = 1 / 2) ∧
      HasCondSubgaussianMGF (prefixSigma 2 0) le_top
        (fun π : PermΩ 2 => f (π 0) - unusedImageAverage 2 0 f π)
        ⟨4, by norm_num⟩ (uniformPerm 2) := by
  dsimp
  obtain ⟨hne, hid, hswap, hfirst, hsecond⟩ :=
    uniformPerm_nextImage_centered_two_witness
  refine ⟨hne, hid, hswap, hfirst, hsecond, ?_⟩
  have hf : ∀ v : Fin 2, |(if v = 0 then (0 : ℝ) else 1)| ≤ 1 := by
    intro v
    fin_cases v <;> norm_num
  simpa using uniformPerm_nextImage_hasCondSubgaussianMGF 2 0
    (fun v : Fin 2 => if v = 0 then 0 else 1) 1 (by norm_num) hf

#print axioms uniformPerm_nextImage_hasCondSubgaussianMGF
#print axioms uniformPerm_nextImage_condMGF_two_witness

end RBM.Gauss
