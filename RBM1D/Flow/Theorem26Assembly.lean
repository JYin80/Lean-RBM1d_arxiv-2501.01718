/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Theorem26Step1
import RBM1D.Flow.BandLocalLawReg
import RBM1D.Flow.GUELocalLaw
import RBM1D.Flow.FlowRandomLayer
import RBM1D.Flow.Theorem26Flow

/-!
# Theorem 2.6 (2.18), conditional on the Theorem 2.21 inputs

`theorem2_6_mat_of_thm221` discharges the three analytic inputs of `theorem2_6_mat`:
the band local law `hLL` at `κ/2`, the GUE local law `hG` (fed by the band local
law at `dL3`), and Step 2's output (2.24) `h2` (from the flow local law and (7.47)
with `τ0 := min τ1 τ2`). The only remaining hypotheses are the external `LSY22' d`
(`docs/PAPER-VS-LEAN.md` §4) and the three Theorem 2.21 inputs, discharged in the Gaussian model
by `thm221NoELNReg_gauss` and `boundsNInput_gauss`.
-/

open MeasureTheory Filter Topology

namespace RBM.Gauss

/-- **Theorem 2.6 (2.18) against the GUE matrix model, conditional on the Theorem 2.21 inputs**
`hU`, `hU3` (`thm221NoELNReg_gauss`) and `hUN` (`boundsNInput_gauss`); `h51`: external [51]. -/
theorem theorem2_6_mat_of_thm221 (d : Dims) (h51 : LSY22' d)
    (hU : ∀ κ : ℝ, 0 < κ → Thm221NoELNReg (sample d) κ)
    (hU3 : ∀ κ : ℝ, 0 < κ → Thm221NoELNReg (sample dL3) κ)
    (hUN : ∀ κ : ℝ, 0 < κ → BoundsNInput d κ)
    {κ : ℝ} (hκ : 0 < κ) : BulkUniversalityMat d κ := by
  have hκ2 : 0 < κ / 2 := half_pos hκ
  have hLL : BandTracialLocalLaw d (κ / 2) :=
    bandTracialLocalLaw_of_Thm221NoELNReg d hκ2 (hU (κ / 2) hκ2)
  have hG : GUELocalLaw d :=
    gueLocalLaw_of_band d fun κ' hκ' => bandTracialLocalLaw_of_Thm221NoELNReg dL3 hκ' (hU3 κ' hκ')
  obtain ⟨τ1, hτ1, hL1⟩ :=
    flowLocalLaw_of_steps d hκ (boundsCoreNInput_of_Thm221NoELNReg d hκ2 (hU (κ / 2) hκ2))
  obtain ⟨τ2, hτ2, hQ2⟩ := flowEq747_of_steps d hκ (hUN κ hκ)
  have h2 : Step2Output d κ :=
    step2Output_of_flow d hκ (τ0 := min τ1 τ2) (lt_min hτ1 hτ2)
      (fun τU h0 h => hL1 τU h0 (h.trans (min_le_left _ _)))
      (fun τU h0 h => hQ2 τU h0 (h.trans (min_le_right _ _)))
  exact theorem2_6_mat d h51 hκ hLL hG h2

/-! ### Plug-in check

Local stand-ins of exactly the terminal types of `thm221NoELNReg_gauss` and `boundsNInput_gauss`
give Theorem 2.6 for every `d` from `LSY22' d` alone, in one line. -/

/-! ### Axioms -/

end RBM.Gauss
