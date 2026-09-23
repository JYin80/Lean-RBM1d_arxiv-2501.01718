/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSlotActual
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget

/-!
# T581: actual restricted first-cell `APrimeSlot`

This file consumes T576's fixed `E = 0`, `D = 60`, `s = 0` first-cell
`APrimeSlot'` and supplies its missing initial field from the actual first-cell
`BoundsCore`.  It exports only the corresponding existential restricted
`APrimeSlot`, retaining T576's positive Good/weight-one/window resident.
-/

namespace RBM.APrimeFirstCellAPrimeSlotActual

open Gauss APrimeModel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- Consume the exact T576 existential without widening any quantifier.  The
same `tauPrime` carries both the fixed first-cell `APrimeSlot` and T576's
eventual positive sample in the literal Good event with weight one. -/
theorem exists_firstCellAPrimeSlotActual :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∃ S : APrimeSlot (sample d) 0 (fun _ => 0) (firstCellT tauPrime) 60,
        (∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
          APrimeFirstCellSlotActual.positiveGoodWeightOnePackage tauPrime delta) ∧
        S.Good = APrimeFirstCellSlotActual.firstCellGood ∧
        S.hyp.W = APrimeFirstCellWeightedMomentActual.firstCellWeight tauPrime := by
  obtain ⟨tauPrime, hTau, S, hS⟩ :=
    APrimeFirstCellSlotActual.exists_firstCellAPrimeSlotAtD60
  obtain ⟨hresident, hGood, _, _, _, _, _, hWeight⟩ := hS
  let Sfull := APrimeSlotFields.aprimeSlot_of_aprimeSlot' S
    (by norm_num)
    (fun N => (APrimeSupportRunning.firstT_bounds hTau N).1)
    (fun N => (APrimeSupportRunning.firstT_bounds hTau N).2.trans_lt (by norm_num))
    (APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg hTau).1
    APrimeFirstCellInitialMomentBudget.firstCell_boundsCore
    (by norm_num)
  refine ⟨tauPrime, hTau, Sfull, hresident, ?_, ?_⟩
  · simpa [Sfull, APrimeSlotFields.aprimeSlot_of_aprimeSlot'] using hGood
  · simpa [Sfull, APrimeSlotFields.aprimeSlot_of_aprimeSlot'] using hWeight

#print axioms exists_firstCellAPrimeSlotActual

end

end RBM.APrimeFirstCellAPrimeSlotActual
