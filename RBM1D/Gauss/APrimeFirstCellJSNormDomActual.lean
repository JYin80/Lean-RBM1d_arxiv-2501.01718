/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSlotActual
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget

/-!
# T578: actual restricted first-cell `JSNormDom`

This file consumes T576's fixed `E = 0`, `D = 60`, `s = 0` first-cell
`APrimeSlot'`.  It only derives the corresponding restricted `JSNormDom`,
while retaining T576's positive Good/weight-one/window witness at the same
existential first-cell parameter.
-/

namespace RBM.APrimeFirstCellJSNormDomActual

open Gauss APrimeModel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The deterministic slot-2 consequence of the exact restricted T576 slot. -/
theorem firstCellJSNormDom_of_aprimeSlot
    {tauPrime : ℝ} (hTau : 0 < tauPrime)
    (S : APrimeSlotFields.APrimeSlot' (sample d) 0
      (fun _ => 0) (firstCellT tauPrime) 60) :
    JSNormDom (sample d) 0 (fun _ => 0) (firstCellT tauPrime) 60 := by
  exact APrimeSlotFields.jsNormDom_of_aprimeSlot' S
    (by norm_num)
    (fun N => (APrimeSupportRunning.firstT_bounds hTau N).1)
    (fun N => (APrimeSupportRunning.firstT_bounds hTau N).2.trans_lt (by norm_num))
    (APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg hTau).1
    APrimeFirstCellInitialMomentBudget.firstCell_boundsCore
    (by norm_num)

/-- Consume the exact T576 existential without widening it.  The same
`tauPrime` carries both the fixed first-cell `JSNormDom` and T576's eventual
positive sample in the literal Good event with weight one. -/
theorem exists_firstCellJSNormDomActual :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      JSNormDom (sample d) 0 (fun _ => 0) (firstCellT tauPrime) 60 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
        APrimeFirstCellSlotActual.positiveGoodWeightOnePackage tauPrime delta := by
  obtain ⟨tauPrime, hTau, S, hS⟩ :=
    APrimeFirstCellSlotActual.exists_firstCellAPrimeSlotAtD60
  exact ⟨tauPrime, hTau, firstCellJSNormDom_of_aprimeSlot hTau S, hS.1⟩

#print axioms firstCellJSNormDom_of_aprimeSlot
#print axioms exists_firstCellJSNormDomActual

end

end RBM.APrimeFirstCellJSNormDomActual
