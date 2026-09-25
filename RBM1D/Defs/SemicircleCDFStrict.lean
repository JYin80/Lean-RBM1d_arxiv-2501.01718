/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleDensitySupportFull
import Mathlib.Probability.CDF

/-!
# Strict increase of the semicircle CDF

The CDF increment on a half-open interval is its semicircle mass. Positive mass
on every nonempty interval inside the support therefore gives strict increase
on the full support interval, including intervals that meet either endpoint.
-/

namespace RBM

open MeasureTheory Set

/-- The semicircle CDF increment over `(a,b]` is exactly its measure. -/
theorem semicircleMeasure_Ioc_cdf (a b : ℝ) :
    semicircleMeasure (Ioc a b) =
      ENNReal.ofReal (ProbabilityTheory.cdf semicircleMeasure b -
        ProbabilityTheory.cdf semicircleMeasure a) := by
  calc
    semicircleMeasure (Ioc a b) =
        (ProbabilityTheory.cdf semicircleMeasure).measure (Ioc a b) := by
      rw [ProbabilityTheory.measure_cdf]
    _ = ENNReal.ofReal (ProbabilityTheory.cdf semicircleMeasure b -
          ProbabilityTheory.cdf semicircleMeasure a) :=
      (ProbabilityTheory.cdf semicircleMeasure).measure_Ioc a b

/-- The semicircle CDF is strictly increasing on its support interval. -/
theorem semicircleMeasure_cdf_strictMonoOn :
    StrictMonoOn (ProbabilityTheory.cdf semicircleMeasure) (Icc (-2 : ℝ) 2) := by
  intro a ha b hb hab
  have hIoo : Ioo a b ⊆ Ioc a b := by
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have hmass : 0 < semicircleMeasure (Ioc a b) := by
    have hpos : 0 < semicircleMeasure (Ioo a b) :=
      semicircleMeasure_Ioo_pos ha.1 hab hb.2
    exact lt_of_lt_of_le hpos (measure_mono hIoo)
  have hdiff_nonneg :
      0 ≤ ProbabilityTheory.cdf semicircleMeasure b -
        ProbabilityTheory.cdf semicircleMeasure a := by
    exact sub_nonneg.mpr ((ProbabilityTheory.monotone_cdf semicircleMeasure) hab.le)
  have hmassR : 0 < (semicircleMeasure (Ioc a b)).toReal :=
    ENNReal.toReal_pos hmass.ne' (measure_ne_top _ _)
  rw [semicircleMeasure_Ioc_cdf, ENNReal.toReal_ofReal hdiff_nonneg] at hmassR
  exact sub_pos.mp hmassR

/-- Nondegenerate interior check: the interval `(-1,1]` has positive mass. -/
theorem semicircleMeasure_Ioc_neg_one_one_pos :
    0 < semicircleMeasure (Ioc (-1 : ℝ) 1) := by
  have h := semicircleMeasure_Ioo_pos (by norm_num : (-2 : ℝ) ≤ -1)
    (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
  exact lt_of_lt_of_le h (measure_mono (by
    intro x hx
    exact ⟨hx.1, hx.2.le⟩))

/-- Endpoint check for intervals of the form `(-2,b]` with `-2 < b ≤ 2`. -/
theorem semicircleMeasure_Ioc_leftEndpoint_pos {b : ℝ}
    (hb : -2 < b) (h'b : b ≤ 2) : 0 < semicircleMeasure (Ioc (-2 : ℝ) b) := by
  have h := semicircleMeasure_Ioo_pos (le_rfl : (-2 : ℝ) ≤ -2) hb h'b
  exact lt_of_lt_of_le h (measure_mono (by
    intro x hx
    exact ⟨hx.1, hx.2.le⟩))

/-- Endpoint check for intervals of the form `(a,2]` with `-2 ≤ a < 2`. -/
theorem semicircleMeasure_Ioc_rightEndpoint_pos {a : ℝ}
    (ha : -2 ≤ a) (h'a : a < 2) : 0 < semicircleMeasure (Ioc a 2) := by
  have h := semicircleMeasure_Ioo_pos ha h'a (le_rfl : (2 : ℝ) ≤ 2)
  exact lt_of_lt_of_le h (measure_mono (by
    intro x hx
    exact ⟨hx.1, hx.2.le⟩))

#print axioms semicircleMeasure_Ioc_cdf
#print axioms semicircleMeasure_cdf_strictMonoOn
#print axioms semicircleMeasure_Ioc_neg_one_one_pos
#print axioms semicircleMeasure_Ioc_leftEndpoint_pos
#print axioms semicircleMeasure_Ioc_rightEndpoint_pos

end RBM
