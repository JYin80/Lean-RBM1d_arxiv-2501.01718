/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGeneratorClosedCellRepair
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetIntegralBound

/-!
# T1139: exact closed-cell cross-budget integral link

The closed-cell generator budget is the actual T1089 positive-time budget
also at the formal endpoint `r = 0`. Consequently the accepted p=1
integrability and polynomial integral cap pass to the exact closed-cell
budget without changing its sample, weight, charge, or coefficient.
-/

namespace RBM.APrimeGeneralMovingClosedCellCrossBudgetIntegral

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.APrimeGeneralMovingCrossHcrossPositive
open RBM.APrimeGeneralMovingCrossBudgetTimeIntegrable

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T1129's piecewise p=1 closed-cell budget is exactly T1089's actual
positive-time budget, including at the formal zero-time point. -/
theorem closedCellCrossBudget_eq_positiveTimeCrossBudget
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) :
    APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
        E D deltaWeight s t N k a r =
      positiveTimeCrossBudget E D deltaWeight s t N k 1 a r := by
  by_cases hr : r = 0
  · subst r
    simp [APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget,
      positiveTimeCrossBudget]
  · simp [APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget, hr]

/-- For fixed p=1, the exact closed-cell budget is interval-integrable on
every active target cell, eventually in N. -/
theorem eventually_intervalIntegrable_closed_cell_cross_budget
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
            E D deltaWeight s t N k a)
          volume (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) := by
  have hInt :=
    eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
  filter_upwards [hInt] with N hIntN
  intro k hk a
  have hEq :
      APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
          E D deltaWeight s t N k a =
        positiveTimeCrossBudget E D deltaWeight s t N k 1 a := by
    funext r
    exact closedCellCrossBudget_eq_positiveTimeCrossBudget
      E D deltaWeight s t N k a r
  rw [hEq]
  exact hIntN k hk a

/-- T1123 and T1133's p=1 polynomial cap for the actual positive-time
budget, transferred to the identical closed-cell budget. -/
theorem eventually_integral_closed_cell_cross_budget_le
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        (∫ r in (s N)..
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
            E D deltaWeight s t N k a r) ≤
          2 * APrimeGeneralMovingCrossEnvelopeIntegral.envelopeConstant 1 N D *
            (√(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) - √(s N)) := by
  have hbound :=
    APrimeGeneralMovingCrossBudgetIntegralBound.eventually_integral_positive_time_cross_budget_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
  filter_upwards [hbound] with N hboundN
  intro k hk a
  have hEq :
      APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
          E D deltaWeight s t N k a =
        positiveTimeCrossBudget E D deltaWeight s t N k 1 a := by
    funext r
    exact closedCellCrossBudget_eq_positiveTimeCrossBudget
      E D deltaWeight s t N k a r
  rw [hEq]
  exact hboundN k hk a

/-- The nondegenerate T995 witness is retained unchanged alongside the
closed-cell integral theorem. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingCrossBudgetIntegralBound.t995_positive_cell_witness

#print axioms closedCellCrossBudget_eq_positiveTimeCrossBudget
#print axioms eventually_intervalIntegrable_closed_cell_cross_budget
#print axioms eventually_integral_closed_cell_cross_budget_le
#print axioms t995_positive_cell_witness

end RBM.APrimeGeneralMovingClosedCellCrossBudgetIntegral
