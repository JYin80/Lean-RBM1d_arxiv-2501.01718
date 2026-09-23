/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Analysis.StretchedExp

/-!
# Time continuity of the far-pair cutoff

These lower-level lemmas use the actual band length and the exact
`(log W) ^ (3/2)` multiplier in `ellStar`. The right endpoint condition
`b < 1` keeps the denominator in `ellHat` nonzero on the entire closed interval.
-/

namespace RBM

namespace CarrierCutoffTime

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual band length is continuous throughout a closed interval below time one. -/
theorem continuousOn_ell (B : Band Ω) (N : ℕ) {a b : ℝ} (hb : b < 1) :
    ContinuousOn (fun u : ℝ => B.ell N u) (Set.Icc a b) := by
  simp only [Band.ell, ellHat]
  refine ContinuousOn.inf ?_ continuousOn_const
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
  have hcast : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact (Real.sqrt_pos.2 (abs_pos.2 (by linarith [hu.2]))).ne'

/-- The exact far-pair cutoff length is continuous on both endpoints of the interval. -/
theorem continuousOn_ellStar_half (B : Band Ω) (N : ℕ) {a b : ℝ}
    (hb : b < 1) :
    ContinuousOn (fun u : ℝ => ellStar (B.W N : ℝ) (B.ell N u) / 2)
      (Set.Icc a b) := by
  have hℓ := continuousOn_ell B N (a := a) hb
  simp only [ellStar]
  fun_prop

end CarrierCutoffTime

end RBM

#print axioms RBM.CarrierCutoffTime.continuousOn_ell
#print axioms RBM.CarrierCutoffTime.continuousOn_ellStar_half
