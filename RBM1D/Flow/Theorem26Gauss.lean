/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Theorem26Assembly
import RBM1D.EnergyN.Gauss.Thm221Gauss
import RBM1D.EnergyN.Gauss.Thm221RegGauss

/-!
# Theorem 2.6 (2.18) for the Gaussian band model

`theorem2_6_gauss` plugs the Theorem 2.21 inputs `thm221NoELNReg_gauss` and
`boundsNInput_gauss` into `theorem2_6_mat_of_thm221`. The only hypothesis besides
`d`, `κ`, `hκ` is `h51 : LSY22' d`, the external input [51, Theorem 2.2] read at unit density
(`docs/PAPER-VS-LEAN.md` §4).

`RBM.Gauss.testBump` is a concrete nonzero test function on `Fin 1 → ℝ`
(`RBM.Gauss.testBump_isTestFun`).
-/

open MeasureTheory Filter Topology

namespace RBM.Gauss

/-- **Theorem 2.6, (2.18)** for the complex Gaussian block band model, against the GUE matrix model.
`h51`: external [51, Theorem 2.2] at unit density. -/
theorem theorem2_6_gauss (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ) :
    BulkUniversalityMat d κ :=
  theorem2_6_mat_of_thm221 d h51 (fun _ hκ' => thm221NoELNReg_gauss d hκ')
    (fun _ hκ' => thm221NoELNReg_gauss dL3 hκ') (fun _ hκ' => boundsNInput_gauss d hκ') hκ

/-! ### A concrete test function

A smooth compactly supported bump on `Fin 1 → ℝ` with value `1` at `0`, so it is not
identically zero. -/

section TestBump

variable (h51 : LSY22' Dims.exampleGrow)

/-- A concrete bump test function on `Fin 1 → ℝ`: equal to `1` on the closed unit ball around `0`,
supported in the closed ball of radius `2`. -/
noncomputable def testBump : ContDiffBump (0 : Fin 1 → ℝ) :=
  ⟨1, 2, one_pos, one_lt_two⟩

theorem testBump_isTestFun : RBM.IsTestFun (fun x : Fin 1 → ℝ => testBump x) :=
  ⟨testBump.contDiff, testBump.hasCompactSupport⟩

end TestBump

end RBM.Gauss
