/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleDensityMeasure
import Mathlib.Probability.CDF

/-!
# Reflection symmetry of the semicircle CDF

The normalized semicircle density is the even density immediately before
equation (2.1) of Yau--Yin, *Delocalization of One-Dimensional Random Band
Matrices*. This file records the resulting exact CDF reflection identity.
-/

namespace RBM

open MeasureTheory Set

private theorem semicircleMeasure_real_Iio_eq_Iic (x : ℝ) :
    semicircleMeasure.real (Iio x) = semicircleMeasure.real (Iic x) := by
  have hunion : Iic x = Iio x ∪ {x} := by
    ext y
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
    constructor
    · intro hy
      by_cases h : y < x
      · exact Or.inl h
      · right
        apply le_antisymm hy
        exact le_of_not_gt h
    · rintro (hy | rfl)
      · exact le_of_lt hy
      · exact le_rfl
  have hdisj : Disjoint (Iio x) ({x} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro y hy hys
    simp only [mem_singleton_iff] at hys
    subst y
    exact (lt_irrefl x) hy
  calc
    semicircleMeasure.real (Iio x) =
        semicircleMeasure.real (Iio x) + semicircleMeasure.real ({x} : Set ℝ) := by
          simp [Measure.real, semicircleMeasure_singleton]
    _ = semicircleMeasure.real (Iio x ∪ {x}) := by
      rw [measureReal_union hdisj (measurableSet_singleton x)]
    _ = semicircleMeasure.real (Iic x) := by rw [← hunion]

/-- The normalized semicircle CDF satisfies exact reflection symmetry. -/
theorem semicircleMeasure_cdf_reflection (x : ℝ) :
    ProbabilityTheory.cdf semicircleMeasure (-x) =
      1 - ProbabilityTheory.cdf semicircleMeasure x := by
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  have hpre : (fun y : ℝ => -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    change (-y ≤ -x ↔ x ≤ y)
    constructor <;> intro h <;> linarith
  have hmap := Measure.measure_preimage_of_map_eq_self
    (μ := semicircleMeasure) (s := Iic (-x)) semicircleMeasure_map_neg
    measurable_neg.aemeasurable measurableSet_Iic.nullMeasurableSet
  have hreflect : semicircleMeasure (Iic (-x)) = semicircleMeasure (Ici x) := by
    rw [← hpre]
    exact hmap.symm
  have hreflectReal : semicircleMeasure.real (Iic (-x)) =
      semicircleMeasure.real (Ici x) := by
    change ENNReal.toReal (semicircleMeasure (Iic (-x))) =
      ENNReal.toReal (semicircleMeasure (Ici x))
    exact congrArg ENNReal.toReal hreflect
  have hcomp : Ici x = (Iio x)ᶜ := by
    ext y
    simp only [mem_Ici, mem_compl_iff, mem_Iio]
    constructor <;> intro h
    · exact not_lt.mpr h
    · exact le_of_not_gt h
  have huniv : semicircleMeasure.real Set.univ = 1 := by
    change ENNReal.toReal (semicircleMeasure Set.univ) = 1
    rw [semicircleMeasure_univ]
    rfl
  rw [hreflectReal, hcomp, measureReal_compl measurableSet_Iio,
    semicircleMeasure_real_Iio_eq_Iic, huniv]

/-- A concrete center consequence of CDF reflection symmetry. -/
theorem semicircleMeasure_cdf_zero :
    ProbabilityTheory.cdf semicircleMeasure 0 = (1 : ℝ) / 2 := by
  have h := semicircleMeasure_cdf_reflection 0
  norm_num at h ⊢
  linarith

#print axioms semicircleMeasure_cdf_reflection
#print axioms semicircleMeasure_cdf_zero

end RBM
