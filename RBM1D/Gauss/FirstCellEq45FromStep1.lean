/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FirstCellStep1LocalLaw
import RBM1D.Gauss.Eq45FlowBudget

/-!
# The bounded first-cell Eq. (4.5) composition — T829

The accepted Step 1 producer supplies one positive first-cell parameter and a local law on
the corresponding Gaussian sample.  The accepted step-5 producer turns that same local law
into the flow statement and inhabited-event witness.
-/

namespace RBM.Gauss

open Filter

/-- The actual `E = 0`, `κ = 1`, `τ = 1/2` first cell admits the Eq. (4.5) flow conclusion
and a positive, eventually inhabited flow event, with one common parameter. -/
theorem firstCell_eq45_step1_composition :
    ∃ τ' : ℝ, 0 < τ' ∧
      RBM.StepGlue.Eq45Flow (sample Dims.exampleGrow) 0
        (firstCellS τ') (firstCellT τ') ∧
      ∀ᶠ N : ℕ in atTop,
        firstCellS τ' N < firstCellT τ' N ∧
          (flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
            firstCellDelta N).Nonempty := by
  obtain ⟨τ', hτ', hll, _hStep1Event⟩ := firstCell_step1_localLaw_witness
  obtain ⟨hFlow, hEvent⟩ := first_cell_step5_nondegenerate_of_localLaw hτ' hll
  exact ⟨τ', hτ', hFlow, hEvent⟩

#print axioms firstCell_eq45_step1_composition

end RBM.Gauss
