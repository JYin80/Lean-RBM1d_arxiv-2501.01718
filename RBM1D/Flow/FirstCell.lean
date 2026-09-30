/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Eq548Producer
import RBM1D.Gauss.FlowHolder

/-!
# Measurability of the event `{‖X_N‖ ≤ N}`

Paper location: §5.3, (5.46)–(5.48).

`RBM.Gauss.measurableSet_normX_le`: in the Gaussian model, the event `{ω | ‖X_N(ω)‖ ≤ N}` is
measurable, where `‖·‖` is the operator norm.
-/

namespace RBM

open MeasureTheory Matrix Filter

open scoped Matrix.Norms.L2Operator

namespace Gauss

end Gauss

section Witness

end Witness

section Caveat

variable {E D : ℝ}

end Caveat

/-! ### The event `{‖X_N‖ ≤ N}` -/

section NormEvent

open Real Gauss Step2FarMart Filter MeasureTheory

namespace Gauss

/-- **The event `{‖X_N‖ ≤ N}` is measurable.**  `ω ↦ ‖X_N(ω)‖` is
measurable by `RBM.Gauss.measurable_norm_Xmat` (the entries are measurable and the
operator norm is continuous), so the sublevel set is measurable. -/
theorem measurableSet_normX_le (d : Dims) (N : ℕ) :
    MeasurableSet {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)} :=
  measurableSet_le (measurable_norm_Xmat d N) measurable_const

end Gauss

end NormEvent

end RBM
