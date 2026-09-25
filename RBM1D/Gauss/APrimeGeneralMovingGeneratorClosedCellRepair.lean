/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGeneratorPositive
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossTimeZero

/-! # T1129: exact closed-cell p=1 generator bound -/

namespace RBM.APrimeGeneralMovingGeneratorClosedCellRepair

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (s : Nat → Real) (D : Real) (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight 1 N k

noncomputable def coordinate (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v

noncomputable def moment (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.momentAt d E D N 1 Step2.sigPM a s v

noncomputable def drift (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a s v

noncomputable def qv (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v

/-- The zero-time budget is exactly zero; at positive time this is T1089's
accepted explicit budget for the same cell and observable. -/
noncomputable def closedCellCrossBudget (E D deltaWeight : Real) (s t : Nat → Real)
    (N k : Nat) (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  if r = 0 then 0 else
    APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
      E D deltaWeight s t N k 1 a r

theorem eventually_actual_closedCell_momFlowDeriv_le
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (s N) (endpoint s D N k),
      APrimeDuhamelModel.momFlowDeriv d N
          (moment E D N a (s N) (endpoint s D N k))
          (weight E D s t deltaWeight N k)
          (APrimeSmoothWeightActual.weightD d E D deltaWeight s t
            (APrimeGeneralMovingMesh.targetMesh D) 2 1 N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N)) r ≤
        2 * (1 : Real) *
            (∫ ω, weight E D s t deltaWeight N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s D N k)) r ω| ^ (2 * 1)
                ∂(P d)) ^ ((2 * (1 : Real) - 1) / (2 * (1 : Real))) *
            (MomentDuhamel.momNormW (P d) (weight E D s t deltaWeight N k)
              1 (drift E D N a (s N) (endpoint s D N k) r) +
              closedCellCrossBudget E D deltaWeight s t N k a r) +
          (1 : Real) * (2 * (1 : Real) - 1) *
            (∫ ω, weight E D s t deltaWeight N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s D N k)) r ω| ^ (2 * 1)
                ∂(P d)) ^ (((1 : Real) - 1) / (1 : Real)) *
            APrimeModel.rateNormW (P d) (weight E D s t deltaWeight N k)
              1 (qv E D N a (s N) (endpoint s D N k) r) := by
  have hpositive :=
    APrimeGeneralMovingGeneratorPositive.eventually_actual_momFlowDeriv_le
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hconditional :=
    APrimeGeneralMovingGeneratorConditional.eventually_actual_momFlowDeriv_le_of_hcross
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg
  filter_upwards [hpositive, hconditional] with N hpositiveN hconditionalN
  intro k hk a r hr
  by_cases hr0 : r = 0
  · subst r
    have hcross := APrimeGeneralMovingCrossHcrossTimeZero.actual_hcross_r0
      E D deltaWeight s t N k 1 (by norm_num) hk hr a
    have hbase := hconditionalN k hk a 0 hr 0
      APrimeGeneralMovingCrossHcrossTimeZero.zeroBudget_nonneg
    have hresult := hbase (by
      convert hcross using 1 <;> (try simp) <;> (try rfl))
    simp only [closedCellCrossBudget]
    exact hresult
  · have hrnonneg : 0 ≤ r := (hs0 N).trans hr.1
    have hrpos : 0 < r := lt_of_le_of_ne hrnonneg (Ne.symm hr0)
    have hresult := hpositiveN k hk a r hr hrpos
    simp only [closedCellCrossBudget, if_neg hr0]
    exact hresult

/-- T995's existing same-sample, positive-cell witness for the standing
model and actual smooth weight. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_closedCell_momFlowDeriv_le
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingGeneratorClosedCellRepair
