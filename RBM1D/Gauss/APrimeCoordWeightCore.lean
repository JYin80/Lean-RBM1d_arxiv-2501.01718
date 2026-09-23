/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator

/-! # Clean coordinate weight for Gaussian quadratic variation -/

namespace RBM.Gauss

open scoped Matrix.Norms.L2Operator

/-- The model's coordinate weight `∑_α S_α ‖B_α‖²`: a deterministic constant of the band
model, carrying no dependence on the observable. -/
noncomputable def coordWeight (d : Dims) (N : ℕ) : ℝ :=
  ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2

theorem coordWeight_nonneg (d : Dims) (N : ℕ) : 0 ≤ coordWeight d N :=
  Finset.sum_nonneg fun q _ => mul_nonneg (gvar d (crd d N q)).2 (by positivity)

#print axioms RBM.Gauss.coordWeight
#print axioms RBM.Gauss.coordWeight_nonneg

end RBM.Gauss
