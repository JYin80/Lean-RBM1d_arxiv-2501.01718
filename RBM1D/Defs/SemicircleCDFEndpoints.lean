/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleDensityMeasure
import Mathlib.Probability.CDF

/-!
# Endpoint values of the semicircle CDF

The normalized semicircle law has cumulative distribution zero at `-2` and
one at `2`. The set-measure proofs account explicitly for the atomless left
endpoint and for the null upper tail.
-/

namespace RBM

open MeasureTheory Set

private theorem semicircleMeasure_Iic_neg_two :
    semicircleMeasure (Iic (-2 : ℝ)) = 0 := by
  have hbridge : Iic (-2 : ℝ) ⊆ (Icc (-2 : ℝ) 2)ᶜ ∪ ({-2} : Set ℝ) := by
    intro x hx
    by_cases hxe : x = -2
    · right
      simp [hxe]
    · left
      simp only [mem_compl_iff, mem_Icc]
      intro h
      exact hxe (le_antisymm hx h.1)
  have hle : semicircleMeasure (Iic (-2 : ℝ)) ≤
      semicircleMeasure ((Icc (-2 : ℝ) 2)ᶜ) + semicircleMeasure ({-2} : Set ℝ) := by
    calc
      semicircleMeasure (Iic (-2 : ℝ)) ≤
          semicircleMeasure ((Icc (-2 : ℝ) 2)ᶜ ∪ ({-2} : Set ℝ)) := measure_mono hbridge
      _ ≤ semicircleMeasure ((Icc (-2 : ℝ) 2)ᶜ) + semicircleMeasure ({-2} : Set ℝ) :=
        measure_union_le _ _
  rw [semicircleMeasure_compl_Icc, semicircleMeasure_singleton] at hle
  simpa using hle

private theorem semicircleMeasure_Ioi_two :
    semicircleMeasure (Ioi (2 : ℝ)) = 0 := by
  have hbridge : Ioi (2 : ℝ) ⊆ (Icc (-2 : ℝ) 2)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc]
    intro h
    exact (not_le_of_gt hx) h.2
  have hle : semicircleMeasure (Ioi (2 : ℝ)) ≤
      semicircleMeasure ((Icc (-2 : ℝ) 2)ᶜ) := measure_mono hbridge
  rw [semicircleMeasure_compl_Icc] at hle
  exact le_antisymm hle bot_le

private theorem semicircleMeasure_Iic_two :
    semicircleMeasure (Iic (2 : ℝ)) = 1 := by
  have hsum := measure_add_measure_compl (μ := semicircleMeasure)
    (s := Iic (2 : ℝ)) measurableSet_Iic
  rw [show (Iic (2 : ℝ))ᶜ = Ioi (2 : ℝ) by ext x; simp] at hsum
  rw [semicircleMeasure_Ioi_two, add_zero, semicircleMeasure_univ] at hsum
  exact hsum

/-- The semicircle CDF vanishes at the left endpoint of its support. -/
theorem semicircleMeasure_cdf_neg_two :
    ProbabilityTheory.cdf semicircleMeasure (-2) = 0 := by
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, semicircleMeasure_Iic_neg_two]
  rfl

/-- The semicircle CDF equals one at the right endpoint of its support. -/
theorem semicircleMeasure_cdf_two :
    ProbabilityTheory.cdf semicircleMeasure 2 = 1 := by
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, semicircleMeasure_Iic_two]
  rfl

#print axioms semicircleMeasure_cdf_neg_two
#print axioms semicircleMeasure_cdf_two

end RBM
