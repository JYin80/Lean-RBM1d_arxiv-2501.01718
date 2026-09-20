/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-!
# Measurability of the matrix inverse

`A⁻¹ = Ring.inverse (det A) • adjugate A`, with `det` and `adjugate` polynomial (hence
continuous) and `Ring.inverse = (·)⁻¹` measurable on `ℂ`.  So each entry of `A⁻¹` is a measurable
function of `A`.

Both the fluctuation average (`Gauss/FlucAvg.lean`) and the linear LDE (`Gauss/RowIndep.lean`)
need this; it is proved once here.  The entrywise form `measurable_inv_entries` is the convenient
one when the matrix is given by its entries.
-/

namespace RBM.Gauss

open MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A`. -/
theorem measurable_matrix_inv_apply {M : Θ → Matrix n n ℂ} (hM : Measurable M) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- The entrywise form: from measurability of every entry of `A`, every entry of `A⁻¹` is
measurable. -/
theorem measurable_inv_entries {A : Θ → Matrix n n ℂ}
    (hA : ∀ k l, Measurable fun ω => A ω k l) (k l : n) :
    Measurable fun ω => (A ω)⁻¹ k l :=
  measurable_matrix_inv_apply (Measurable.of_eval fun a => Measurable.of_eval fun b => hA a b) k l

end RBM.Gauss
