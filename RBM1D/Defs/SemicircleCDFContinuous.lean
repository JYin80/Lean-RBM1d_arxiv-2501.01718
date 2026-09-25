/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleDensityMeasure
import Mathlib.Probability.CDF

/-!
# Continuity of the semicircle CDF

The atomless semicircle probability measure has a continuous cumulative
distribution function, including at the support endpoints and at the origin.
-/

namespace RBM

open MeasureTheory Set Filter

/-- The CDF of the normalized semicircle density measure is continuous everywhere. -/
theorem semicircleMeasure_cdf_continuous :
    Continuous (ProbabilityTheory.cdf semicircleMeasure) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [continuousAt_iff_continuous_left'_right']
  have hmono : Monotone (ProbabilityTheory.cdf semicircleMeasure) :=
    ProbabilityTheory.monotone_cdf semicircleMeasure
  have hleftLim :
      Function.leftLim (ProbabilityTheory.cdf semicircleMeasure) x =
        ProbabilityTheory.cdf semicircleMeasure x := by
    have hsingle := semicircleMeasure_singleton x
    rw [← ProbabilityTheory.measure_cdf semicircleMeasure,
      StieltjesFunction.measure_singleton] at hsingle
    have hle :
        Function.leftLim (ProbabilityTheory.cdf semicircleMeasure) x ≤
          ProbabilityTheory.cdf semicircleMeasure x := hmono.leftLim_le le_rfl
    have hdiff0 :
        ProbabilityTheory.cdf semicircleMeasure x -
          Function.leftLim (ProbabilityTheory.cdf semicircleMeasure) x = 0 := by
      have hnonpos := (ENNReal.ofReal_eq_zero).mp hsingle
      linarith
    linarith
  exact ⟨hmono.continuousWithinAt_Iio_iff_leftLim_eq.mpr hleftLim,
    continuousWithinAt_Ioi_iff_Ici.mpr
      ((ProbabilityTheory.cdf semicircleMeasure).right_continuous x)⟩

#print axioms semicircleMeasure_cdf_continuous

end RBM
