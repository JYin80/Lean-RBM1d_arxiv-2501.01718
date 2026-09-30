/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Plain
import RBM1D.Gauss.Step4Base
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Gauss.SigmaExhaust
import RBM1D.Gauss.GridFarLift
import RBM1D.Gauss.GridFarClosure
import RBM1D.Flow.EnergyUniformReg
import RBM1D.Gauss.Thm25Gauss

/-!
# Theorem 2.2 for the Gaussian model, conditional

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.2, for the true-path Gaussian model `RBM.Gauss.sample d`.

The conclusion below is **literally** the conclusion of the named `RBM1D/Flow` theorem,
instantiated at `X := RBM.Gauss.sample d`, `T := RBM.Gauss.transfer_gauss d`.  It is not
abbreviated with `type_of%`; every conjunct is written out.

## The conditional Theorem 2.2

* **`delocalization_gauss_of_reg` (Theorem 2.2) is conditional** as stated: it takes
  `hT : RBM.Thm221NoELNReg (sample d) κ` as an explicit hypothesis.  That hypothesis is
  discharged for the Gaussian model by `RBM.Gauss.thm221NoELNReg_gauss`
  (`RBM1D/EnergyN/Gauss/Thm221Gauss.lean`), not in this file.

## Main results

* `delocalization_gauss_of_reg` — **Theorem 2.2** (delocalization), conditional on
  `RBM.Thm221NoELNReg (sample d) κ`.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix

variable (d : Dims)

/-! ### Theorem 2.2, conditional -/

/-- **Theorem 2.2 (delocalization) for the Gaussian model, conditional on energy-uniform
Theorem 2.21** (`RBM.Thm221NoELNReg`, `Flow/EnergyUniformReg.lean`). Literally the conclusion of
`RBM.delocalization_of_Thm221N'` (`Flow/EnergyUniform.lean`) at `X := sample d`,
`T := transfer_gauss d`, `hT := hT.toThm221NoELN' hκ`.

**This is a conditional result**: the hypothesis `hT : Thm221NoELNReg (sample d) κ` is not
discharged here; `RBM.Gauss.thm221NoELNReg_gauss` discharges it for the Gaussian model.  This
file only assembles the conditional implication. -/
theorem delocalization_gauss_of_reg (d : Dims) {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELNReg (sample d) κ) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      (band d).P {ω | ∃ p : (band d).Idx N × (band d).Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖((transfer_gauss d).hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            (((transfer_gauss d).hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  delocalization_of_Thm221N' (transfer_gauss d) hκ (hT.toThm221NoELN' hκ) hτ hD

end RBM.Gauss
