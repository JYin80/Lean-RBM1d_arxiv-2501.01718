/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.StepSideAPrimeCore

/-!
# Scalar terms in the A-prime one-step estimate

This dependency-light core owns the three algebraic terms consumed by the one-step facade
and the drift-slot arithmetic.
-/

namespace RBM

namespace APrimeOneStep

open Real
open StepSideAPrime

/-- (5.39): the initial datum slot of `RBM.StepSideAPrime.stepRhs''`. -/
noncomputable def initTerm (x R Ξ : ℝ) : ℝ := x * R ^ 2 * Ξ

/-- (5.40)+(5.41)+(5.42): the drift and quadratic-variation slots of
`RBM.StepSideAPrime.stepRhs''`. -/
noncomputable def driftTerm (m x R Ξ A ε q β γ Jv : ℝ) : ℝ :=
  Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
    + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv)))

/-- The cross-term slot `κ` of the fixed-`ω` generator identity, plus the constant slots that
pay for the bad event, the `max_a` union and the Lyapunov `+1`. -/
noncomputable def tailTerm (x R κ : ℝ) : ℝ := x * R ^ 2 * κ + (x * (R ^ 2 + 1) + 1)

end APrimeOneStep

end RBM
