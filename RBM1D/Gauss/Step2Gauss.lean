/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridNetLift
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Hierarchy.Step2

/-!
# The matrix-level `lkErr` for the Gaussian model

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3: the loop error of (2.75)/(2.76)
as a function of the matrix, the form in which the grid side of Step 2 reads it.

## Main results

* `RBM.Gauss.lkErrMat` — the matrix-level `Sample.lkErr`.
* `RBM.Gauss.measurable_lkErrMat` — its measurability in the matrix.
* `RBM.Gauss.lkErr_eq_lkErrMat` — `sample d`'s `lkErr` is `lkErrMat` at `Hflow d N u ω`.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### The matrix-level `lkErr` -/

/-- **`lkErrMat`** — the matrix-level `Sample.lkErr`: `‖gloop M (zt E u) I − Kval E N u I‖`,
taking the matrix `M` directly instead of a `Sample`'s `ω`. Exactly `RBM.Gauss.Grid.jSMat`'s
pattern (`Gauss/GridJStar.lean`), for `lkErr` instead of `jS`. -/
def lkErrMat (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I : LoopIdx (ZMod (d.L N))) : ℝ :=
  ‖gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I‖

/-- **Measurability of `lkErrMat` in the matrix `M`**, unconditionally, from
`Grid.measurable_gloop_matrix`. -/
theorem measurable_lkErrMat (E : ℝ) (N : ℕ) (u : ℝ) (I : LoopIdx (ZMod (d.L N))) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => lkErrMat d E N u M I :=
  ((Grid.measurable_gloop_matrix d N (zt E u) I).sub measurable_const).norm

/-- **`sample d`'s `lkErr` is `lkErrMat` evaluated at `Hflow d N u ω`.** Literally `rfl`: `band
d`'s `L`/`W`/`P` are `d`'s by structure projection, and `sample d`'s `H` is `Hflow d` by
definition, exactly the reason `Grid.jS_eq_jSMat` is `rfl`. -/
theorem lkErr_eq_lkErrMat (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) (I : LoopIdx (ZMod (d.L N))) :
    (sample d).lkErr E N u ω I = lkErrMat d E N u (Hflow d N u ω) I := rfl

end RBM.Gauss
