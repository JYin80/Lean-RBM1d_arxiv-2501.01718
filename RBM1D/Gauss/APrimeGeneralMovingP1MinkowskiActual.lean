/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGeneratorClosedCellRepair
import RBM1D.Gauss.APrimeGeneralMovingClosedCellCrossBudgetIntegral
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeTimeIntegrability

/-!
# T1221: actual general-moving p=1 closed-cell Minkowski estimate

This integrates the accepted T1129 pointwise generator bound with the exact
T1139 closed-cell cross budget.  It is a deterministic moving-cell estimate;
it does not assert A′ closure or the paper's stopped-process conclusions.
-/

namespace RBM.APrimeGeneralMovingP1MinkowskiActual

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

noncomputable abbrev d : Dims := APrimeGeneralMovingGeneratorClosedCellRepair.d

noncomputable def endpoint (s _t : ℕ → ℝ) (D : ℝ) (N k : ℕ) : ℝ :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

noncomputable def weight (E D : ℝ) (s t : ℕ → ℝ)
    (deltaWeight : ℝ) (N k : ℕ) : Ω d → ℝ :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight 1 N k

noncomputable def coordinate (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v : ℝ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v

noncomputable def flowY (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v r : ℝ) : Ω d → ℝ :=
  APrimeDuhamelModel.flowY d N (coordinate E D N a s v) r

noncomputable def driftNorm (E D : ℝ) (s t : ℕ → ℝ)
    (deltaWeight : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight 1 N k a r

noncomputable def crossBudget (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
    E D deltaWeight s t N k a r

noncomputable def qvNorm (E D : ℝ) (s t : ℕ → ℝ)
    (deltaWeight : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t deltaWeight 1 N k a r

/-- The literal p=1 closed-cell inequality, with the actual smooth weight and
the exact T1129/T1139 rates. -/
def closedCellMinkowskiBoundAt (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k : ℕ) (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight E D s t deltaWeight N k) 1
      (flowY E D N a (s N) (endpoint s t D N k) (endpoint s t D N k)) ≤
    momNormW (P d) (weight E D s t deltaWeight N k) 1
      (flowY E D N a (s N) (endpoint s t D N k) (s N)) +
      2 * (∫ r in (s N)..(endpoint s t D N k),
        driftNorm E D s t deltaWeight N k a r +
          crossBudget E D deltaWeight s t N k a r) +
      Real.sqrt ((2 * (1 : ℝ) - 1) *
        ∫ r in (s N)..(endpoint s t D N k),
          qvNorm E D s t deltaWeight N k a r)

theorem closedCellCrossBudget_nonneg
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ crossBudget E D deltaWeight s t N k a r := by
  by_cases hr0 : r = 0
  · simp [crossBudget, APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget,
      hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    rw [crossBudget,
      APrimeGeneralMovingClosedCellCrossBudgetIntegral.closedCellCrossBudget_eq_positiveTimeCrossBudget]
    exact APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget_nonneg
      E D deltaWeight s t N k 1 a (by norm_num) hrpos

/-- T1129's exact actual p=1 generator inequality integrates on each moving
closed target cell.  The eventual quantifier is uniform over all active `k`
including `k=0` and every output `a`; the interval may start at zero. -/
theorem eventually_closedCell_p1_weightedMinkowski
    {E D c deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ,
        k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          closedCellMinkowskiBoundAt E D deltaWeight s t N k a := by
  have hgen :=
    APrimeGeneralMovingGeneratorClosedCellRepair.eventually_actual_closedCell_momFlowDeriv_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hcrossInt :=
    RBM.APrimeGeneralMovingClosedCellCrossBudgetIntegral.eventually_intervalIntegrable_closed_cell_cross_budget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  filter_upwards [hgen, hcrossInt, eventually_ge_atTop 2]
    with N hgenN hcrossIntN hN2
  have hN : 0 < N := by omega
  intro k hk a
  let v := endpoint s t D N k
  let w := weight E D s t deltaWeight N k
  let Ψ := APrimeDriftTimeFamily.momentAt d E D N 1 Step2.sigPM a (s N) v
  let Ψ₁ := coordinate E D N a (s N) v
  let wD := APrimeSmoothWeightActual.weightD d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 1 N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
  let φ' := APrimeDuhamelModel.momFlowDeriv d N Ψ w wD
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, endpoint]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hsv : s N ≤ v := hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have htest : Gauss.TestFunT₁ d N (Icc (s N) v) Ψ := by
    simpa [APrimeDriftTimeFamily.NormalizedTestFunBridge, Ψ,
      APrimeDriftTimeFamily.momentAt] using
      APrimeNormalizedTestFun.normalizedTestFunBridge d E D N 1
        Step2.sigPM a hE (hs0 N) hsv hv1
  have hwC1 : Gauss.WeightC1 d N w wD := by
    have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N :=
      APrimeSmoothWeightActual.canonicalM_pos d s t
        (APrimeGeneralMovingMesh.targetMesh D) N
    have hu : ∀ j < k,
        cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j < 1 := by
      intro j hj
      have hjtop : j ≤ cutNetTop s t
          (APrimeGeneralMovingMesh.targetMesh D) N := hj.le.trans hk
      have hjmem := MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hjtop)
      exact hjmem.2.trans_lt (ht1 N)
    dsimp only [w, wD, weight,
      APrimeGeneralMovingSmoothDriftNormBudget.weight]
    exact APrimeSmoothWeightActual.weightC1 d
      (E := E) (D := D) (δ := deltaWeight) (s := s) (t := t)
      (mesh := APrimeGeneralMovingMesh.targetMesh D) (N₀ := 2)
      (p := 1) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      hE ((hst N).trans_lt (ht1 N)) hN hm hu
  have hW0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t deltaWeight 1 N k ω
  have hre := APrimeDriftTimeFamily.momentAt_isModulusPow
    d E D N 1 Step2.sigPM a (s N) v
  have hcont := APrimeDuhamelModel.continuousOn_momFlow
    htest hwC1 hre (Set.Subset.rfl : Icc (s N) v ⊆ Icc (s N) v)
  have hderiv : ∀ u ∈ Ioo (s N) v,
      HasDerivAt
        (fun r : ℝ => ∫ ω, w ω *
          |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * 1) ∂(P d))
        (φ' u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt (hs0 N) hu.1
    exact APrimeDuhamelModel.hasDerivAt_momFlow htest hwC1 hre hu0
      (Icc_mem_nhds hu.1 hu.2)
  have hphiInt : IntervalIntegrable φ' volume (s N) v :=
    APrimeDuhamelModel.intervalIntegrable_momFlowDeriv htest hwC1 hre
      (hs0 N) hsv (Set.Subset.rfl : Icc (s N) v ⊆ Icc (s N) v)
  have hA0 : ∀ u ∈ Icc (s N) v,
      0 ≤ driftNorm E D s t deltaWeight N k a u := by
    intro u hu
    exact momNormW_nonneg (P := P d) hW0 1 _
  have hB0 : ∀ u ∈ Icc (s N) v,
      0 ≤ crossBudget E D deltaWeight s t N k a u := by
    intro u hu
    exact closedCellCrossBudget_nonneg E D deltaWeight s t N k a
      ((hs0 N).trans hu.1)
  have hg0 : ∀ u ∈ Icc (s N) v,
      0 ≤ qvNorm E D s t deltaWeight N k a u := by
    intro u hu
    exact APrimeModel.rateNormW_nonneg hW0 1 _
  have hAint : IntervalIntegrable
      (driftNorm E D s t deltaWeight N k a) volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight 1 N k a)
      volume (s N) v
    exact APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      hE hs0 hst ht1 hN hk a
  have hBint : IntervalIntegrable
      (crossBudget E D deltaWeight s t N k a) volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingGeneratorClosedCellRepair.closedCellCrossBudget
        E D deltaWeight s t N k a) volume (s N) v
    exact hcrossIntN k hk a
  have hABint : IntervalIntegrable
      (fun r => driftNorm E D s t deltaWeight N k a r +
        crossBudget E D deltaWeight s t N k a r) volume (s N) v :=
    hAint.add hBint
  have hgint : IntervalIntegrable
      (qvNorm E D s t deltaWeight N k a) volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingActualSmoothQVNormBudget.g
        E D s t deltaWeight 1 N k a) volume (s N) v
    exact APrimeGeneralMovingActualSmoothQVNormBudget.intervalIntegrable_g
      hE hs0 hst ht1 (by norm_num) hN hk a
  have hprefix : ∀ u ∈ Icc (s N) v,
      IntervalIntegrable
        (fun r => momNormW (P d) w 1
          (APrimeDuhamelModel.flowY d N Ψ₁ r) *
          (driftNorm E D s t deltaWeight N k a r +
            crossBudget E D deltaWeight s t N k a r)) volume (s N) u := by
    intro u hu
    exact APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
      hsv (Set.Subset.rfl : Icc (s N) v ⊆ Icc (s N) v)
      (p := 1) (by norm_num) htest hwC1 hre hABint hu
  have hbound : ∀ u ∈ Ioo (s N) v,
      φ' u ≤
        2 * (1 : ℝ) *
          (∫ ω, w ω *
            |APrimeDuhamelModel.flowY d N Ψ₁ u ω| ^ (2 * 1) ∂(P d)) ^
              ((2 * (1 : ℝ) - 1) / (2 * (1 : ℝ))) *
          (driftNorm E D s t deltaWeight N k a u +
            crossBudget E D deltaWeight s t N k a u) +
        (1 : ℝ) * (2 * (1 : ℝ) - 1) *
          (∫ ω, w ω *
            |APrimeDuhamelModel.flowY d N Ψ₁ u ω| ^ (2 * 1) ∂(P d)) ^
              (((1 : ℝ) - 1) / (1 : ℝ)) *
          APrimeModel.rateNormW (P d) w 1
            (APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a
              (s N) v u) := by
    intro u hu
    have hpoint := hgenN k hk a u ⟨le_of_lt hu.1, hu.2.le⟩
    norm_num [φ', Ψ, Ψ₁, w, v, endpoint, coordinate, weight,
      driftNorm, crossBudget, qvNorm,
      APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift,
      APrimeGeneralMovingActualSmoothQVNormBudget.g,
      APrimeGeneralMovingActualSmoothQVNormBudget.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.weight,
      APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingGeneratorClosedCellRepair.d,
      APrimeGeneralMovingGeneratorClosedCellRepair.endpoint,
      APrimeGeneralMovingGeneratorClosedCellRepair.moment,
      APrimeGeneralMovingGeneratorClosedCellRepair.coordinate,
      APrimeGeneralMovingGeneratorClosedCellRepair.weight,
      APrimeGeneralMovingGeneratorClosedCellRepair.drift,
      APrimeGeneralMovingGeneratorClosedCellRepair.qv,
      d, wD] at hpoint ⊢
    exact hpoint
  have hMink := MomentDuhamel.weightedMinkowski_of_deriv_le hsv
      (p := 1) (by norm_num) hW0 hcont hderiv hphiInt hA0 hB0 hg0
      hABint hgint hprefix (by
        intro u hu
        have hb := hbound u hu
        norm_num [Ψ₁, coordinate, qvNorm,
          APrimeGeneralMovingActualSmoothQVNormBudget.g,
          APrimeGeneralMovingActualSmoothQVNormBudget.qv,
          APrimeGeneralMovingQVNormBudget.qv, d] at hb ⊢
        exact hb)
  norm_num [closedCellMinkowskiBoundAt, flowY, coordinate, endpoint, v,
    weight, driftNorm, crossBudget, qvNorm,
    APrimeGeneralMovingSmoothDriftNormBudget.g,
    APrimeGeneralMovingActualSmoothQVNormBudget.g,
    APrimeGeneralMovingActualSmoothQVNormBudget.qv,
    APrimeGeneralMovingActualSmoothQVNormBudget.weight,
    APrimeGeneralMovingQVNormBudget.qv, d] at hMink ⊢
  exact hMink

/-- T995's same-resident positive-cell witness supplies a nondegenerate
`E=0`, `D=60`, `s=0` context with positive actual smooth weight. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms closedCellCrossBudget_nonneg
#print axioms eventually_closedCell_p1_weightedMinkowski
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingP1MinkowskiActual
