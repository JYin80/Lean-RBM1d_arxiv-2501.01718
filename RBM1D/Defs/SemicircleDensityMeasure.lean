/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Semicircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Support

/-!
# The semicircle density measure

The density immediately before (2.1) of Yau--Yin,
*Delocalization of One-Dimensional Random Band Matrices*.
-/

namespace RBM

open MeasureTheory Set Real intervalIntegral

/-- The semicircle density `ρ_sc(x) = (2π)⁻¹ √((4-x²)₊)`. -/
noncomputable def semicircleDensity (x : ℝ) : ℝ := Real.sqrt (4 - x ^ 2) / (2 * Real.pi)

/-- The measure whose Radon--Nikodym density is `ρ_sc`. -/
noncomputable def semicircleMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (semicircleDensity x))

theorem semicircleDensity_nonneg (x : ℝ) : 0 ≤ semicircleDensity x := by
  unfold semicircleDensity
  positivity

theorem semicircleDensity_even (x : ℝ) : semicircleDensity (-x) = semicircleDensity x := by
  simp [semicircleDensity]

theorem semicircleDensity_zero : 0 < semicircleDensity 0 := by
  unfold semicircleDensity
  positivity

theorem semicircleDensity_eq_zero_of_not_mem {x : ℝ} (hx : x ∉ Icc (-2) 2) :
    semicircleDensity x = 0 := by
  have h : 4 - x ^ 2 ≤ 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx <;> nlinarith
  simp [semicircleDensity, Real.sqrt_eq_zero_of_nonpos h]

theorem semicircleDensity_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-2) 2) :
    0 < semicircleDensity x := by
  have h : 0 < 4 - x ^ 2 := by
    rcases hx with ⟨h₁, h₂⟩
    nlinarith
  unfold semicircleDensity
  positivity

theorem semicircleDensity_continuous : Continuous semicircleDensity := by
  unfold semicircleDensity
  fun_prop

private theorem integral_sqrt_four_sub_sq :
    (∫ x in (-2 : ℝ)..2, Real.sqrt (4 - x ^ 2)) = 2 * Real.pi := by
  have hscale :=
    intervalIntegral.integral_comp_mul_left
      (f := fun x : ℝ => Real.sqrt (4 - x ^ 2)) (a := -1) (b := 1)
      (c := 2) (by norm_num)
  norm_num only [mul_neg, mul_one] at hscale
  have hfun : ∀ x : ℝ, Real.sqrt (4 - (2 * x) ^ 2) =
      2 * Real.sqrt (1 - x ^ 2) := by
    intro x
    have hs : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
      norm_num
    rw [show 4 - (2 * x) ^ 2 = 4 * (1 - x ^ 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs]
  simp_rw [hfun] at hscale
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq] at hscale
  simp only [smul_eq_mul] at hscale
  linarith

theorem semicircleDensity_integral_Icc :
    (∫ x in Icc (-2 : ℝ) 2, semicircleDensity x) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
  simp_rw [semicircleDensity, div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, integral_sqrt_four_sub_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem semicircleDensity_integrable : Integrable semicircleDensity (volume : Measure ℝ) :=
  (semicircleDensity_continuous.continuousOn.integrableOn_Icc).integrable_of_forall_notMem_eq_zero
    (fun _ hx => semicircleDensity_eq_zero_of_not_mem hx)

theorem semicircleMeasure_univ : semicircleMeasure Set.univ = 1 := by
  rw [semicircleMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal semicircleDensity_integrable
    (Filter.Eventually.of_forall semicircleDensity_nonneg)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun _ hx => semicircleDensity_eq_zero_of_not_mem hx)]
  rw [semicircleDensity_integral_Icc]
  norm_num

instance semicircleMeasure_isProbabilityMeasure : IsProbabilityMeasure semicircleMeasure :=
  ⟨semicircleMeasure_univ⟩

theorem semicircleMeasure_compl_Icc : semicircleMeasure (Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [semicircleMeasure, withDensity_apply _ measurableSet_Icc.compl]
  apply (setLIntegral_eq_zero_iff measurableSet_Icc.compl
    semicircleDensity_continuous.measurable.ennreal_ofReal).2
  filter_upwards [] with x
  intro hx
  simp [semicircleDensity_eq_zero_of_not_mem hx]

theorem semicircleMeasure_support_subset :
    semicircleMeasure.support ⊆ Icc (-2 : ℝ) 2 := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  exact mem_ae_iff.mpr semicircleMeasure_compl_Icc

theorem semicircleMeasure_singleton (x : ℝ) : semicircleMeasure ({x} : Set ℝ) = 0 := by
  change (volume.withDensity (fun y : ℝ => ENNReal.ofReal (semicircleDensity y))) {x} = 0
  exact measure_singleton x

theorem semicircleMeasure_Ioo_pos {a b : ℝ} (ha : -2 ≤ a) (hab : a < b)
    (hb : b ≤ 2) : 0 < semicircleMeasure (Ioo a b) := by
  rw [semicircleMeasure, withDensity_apply _ measurableSet_Ioo]
  rw [setLIntegral_pos_iff semicircleDensity_continuous.measurable.ennreal_ofReal]
  have hsubset : Ioo a b ⊆
      Function.support (fun x : ℝ => ENNReal.ofReal (semicircleDensity x)) ∩ Ioo a b := by
    intro x hx
    refine ⟨?_, hx⟩
    rw [Function.mem_support]
    have hxi : x ∈ Ioo (-2 : ℝ) 2 := ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    exact (ENNReal.ofReal_pos.mpr (semicircleDensity_pos_of_mem_Ioo hxi)).ne'
  exact lt_of_lt_of_le (Measure.measure_Ioo_pos (volume : Measure ℝ) |>.2 hab)
    (measure_mono hsubset)

theorem semicircleMeasure_nontrivial :
    0 < semicircleMeasure (Ioo (-1 : ℝ) 1) :=
  semicircleMeasure_Ioo_pos (by norm_num) (by norm_num) (by norm_num)

/-- Reflection through the origin preserves the semicircle measure. -/
theorem semicircleMeasure_map_neg :
    Measure.map (fun x : ℝ => -x) semicircleMeasure = semicircleMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs, semicircleMeasure,
    withDensity_apply _ (hs.preimage measurable_neg), withDensity_apply _ hs]
  have h := setLIntegral_map (μ := (volume : Measure ℝ)) hs
    semicircleDensity_continuous.measurable.ennreal_ofReal measurable_neg
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  simp_rw [semicircleDensity_even] at h
  exact h.symm

#print axioms semicircleDensity
#print axioms semicircleMeasure
#print axioms semicircleDensity_nonneg
#print axioms semicircleDensity_even
#print axioms semicircleDensity_zero
#print axioms semicircleDensity_eq_zero_of_not_mem
#print axioms semicircleDensity_pos_of_mem_Ioo
#print axioms semicircleDensity_continuous
#print axioms semicircleDensity_integral_Icc
#print axioms semicircleDensity_integrable
#print axioms semicircleMeasure_univ
#print axioms semicircleMeasure_isProbabilityMeasure
#print axioms semicircleMeasure_compl_Icc
#print axioms semicircleMeasure_support_subset
#print axioms semicircleMeasure_singleton
#print axioms semicircleMeasure_Ioo_pos
#print axioms semicircleMeasure_nontrivial
#print axioms semicircleMeasure_map_neg

end RBM
