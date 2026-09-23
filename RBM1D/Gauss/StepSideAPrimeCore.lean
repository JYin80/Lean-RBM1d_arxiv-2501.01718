/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Elementary weight-support constant for the A-prime step

This dependency-light core owns the scalar constant used by the A-prime one-step and
drift-slot arithmetic.  The compatibility facade `RBM1D.Gauss.StepSideAPrime` contains the
remaining bootstrap arithmetic.
-/

namespace RBM

namespace StepSideAPrime

open Real

/-! ### The weight-support constant `cWt = 4e + 2` -/

/-- The constant of the a priori level on the support of the soft-max cutoff weight:
`4e` is the prior bound (`prefNet`'s `N^{2δ}`, times `e` for the soft maximum, times `2` for
the widened weight `χ(·/(2Θ′))`), and the extra `2` is the margin. -/
noncomputable def cWt : ℝ := 4 * exp 1 + 2

theorem cWt_pos : 0 < cWt := by
  have : (0 : ℝ) < exp 1 := exp_pos 1
  unfold cWt; positivity

end StepSideAPrime

end RBM
