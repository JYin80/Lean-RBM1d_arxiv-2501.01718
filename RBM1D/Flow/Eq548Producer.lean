/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Defs.MatrixMeasurable
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.LoopLipschitz

/-!
# Measurability of the flow matrix `ω ↦ H_u(ω)`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.47)–(5.48).

`RBM.measurable_H`: for a `Sample`, the map `ω ↦ H_u(ω)` is measurable as a matrix-valued map.
It follows from the entrywise field `RBM.Sample.measurable` (`ω ↦ (H_u)_{ij}` is measurable for
every `i, j`), because a matrix-valued map is measurable when all its entries are.
-/

namespace RBM

open MeasureTheory Filter Matrix

/-! ### 1. Measurability of `ω ↦ H_u(ω)` -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `ω ↦ H_u(ω)` is measurable as a *matrix*-valued map, from the entrywise field
`RBM.Sample.measurable`. -/
theorem measurable_H (X : Sample B) (N : ℕ) (u : ℝ) : Measurable fun ω => X.H N u ω :=
  Measurable.of_eval_matrix _ fun i j => X.measurable N u i j

end Meas

section Near

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end Near

section Modulus

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable {E D : ℝ} {s t : ℕ → ℝ} (X : Sample B)

end Modulus

section Assemble

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end Assemble

section Repaired

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end Repaired

section Sat

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end Sat

section ZeroStart

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {t : ℕ → ℝ}
variable (X : Sample B)

end ZeroStart

section Involution

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {τ : n → n} (hτ : ∀ i, τ (τ i) = i)

end Involution

section LoopValue

variable {L W : ℕ} [NeZero L] [NeZero W]

end LoopValue

section SqrtFlowLipReexport

open scoped Matrix.Norms.L2Operator

end SqrtFlowLipReexport

section ZeroMat
variable {n : Type*} [Fintype n] [DecidableEq n]

end ZeroMat

section ZeroLoop
variable {L W : ℕ} [NeZero L] [NeZero W]

end ZeroLoop

section BadSample

variable {B : Band ℝ} {E D : ℝ}

end BadSample

section Gap
variable {B : Band ℝ} {E D : ℝ}

end Gap

section Parametric

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end Parametric

section ParametricZeroStart

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {t : ℕ → ℝ}
variable (X : Sample B)

end ParametricZeroStart

section ParametricGap
variable {B : Band ℝ} {E D : ℝ}

end ParametricGap

section EventRestricted

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end EventRestricted

section EventGap
variable {B : Band ℝ} {E D : ℝ}

end EventGap

section RealModel

open ProbabilityTheory

end RealModel

section SatParametric

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end SatParametric

end RBM

