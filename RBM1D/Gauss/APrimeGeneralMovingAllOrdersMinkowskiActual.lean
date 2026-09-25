/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGeneratorAllOrdersClosedCell
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeTimeIntegrability

/-!
# T1231: all-fixed-order actual-weighted closed-cell Minkowski estimate

This integrates the accepted T1225 closed-cell generator estimate, with its
literal actual smooth weight, actual weighted drift norm, piecewise closed-
cell cross budget, and actual weighted QV norm. The order `p` is fixed before
the eventual cutoff in `N`; the result is uniform over active cells and all
outputs and includes both `r = 0` and `k = 0`.
-/

namespace RBM.APrimeGeneralMovingAllOrdersMinkowskiActual

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel
open RBM.APrimeGeneralMovingCrossBudgetTimeIntegrable
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

noncomputable abbrev d : Dims := APrimeGeneralMovingGeneratorAllOrdersClosedCell.d

noncomputable def endpoint (s _t : ℕ → ℝ) (D : ℝ) (N k : ℕ) : ℝ :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

noncomputable def weight (E D : ℝ) (s t : ℕ → ℝ)
    (deltaWeight : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight p N k

noncomputable def coordinate (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v : ℝ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v

noncomputable def flowY (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v r : ℝ) : Ω d → ℝ :=
  APrimeDuhamelModel.flowY d N (coordinate E D N a s v) r

noncomputable def driftNorm (E D : ℝ) (s t : ℕ → ℝ)
    (deltaWeight : ℝ) (p N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r

noncomputable def crossBudget (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k p : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget
    E D deltaWeight s t N k p a r

noncomputable def qvNorm (E D : ℝ) (s t : ℕ → ℝ)
    (deltaWeight : ℝ) (p N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t deltaWeight p N k a r

/-- The exact actual-weighted closed-cell inequality at fixed order `p`. -/
def actualClosedCellMinkowskiBoundAt (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (p N k : ℕ) (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight E D s t deltaWeight p N k) p
      (flowY E D N a (s N) (endpoint s t D N k) (endpoint s t D N k)) ≤
    momNormW (P d) (weight E D s t deltaWeight p N k) p
      (flowY E D N a (s N) (endpoint s t D N k) (s N)) +
      2 * (∫ r in (s N)..(endpoint s t D N k),
        driftNorm E D s t deltaWeight p N k a r +
          crossBudget E D deltaWeight s t N k p a r) +
      Real.sqrt ((2 * (p : ℝ) - 1) *
        ∫ r in (s N)..(endpoint s t D N k),
          qvNorm E D s t deltaWeight p N k a r)

private theorem crossBudget_eq_positiveTime
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k p : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) :
    crossBudget E D deltaWeight s t N k p a r =
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D deltaWeight s t N k p a r := by
  by_cases hr : r = 0
  · subst r
    simp [crossBudget,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget,
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget]
  · simp [crossBudget,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget, hr]

private theorem crossBudget_nonneg
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k p : ℕ)
    (hp : 1 ≤ p) (a : LoopArg (d.L N) 2) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ crossBudget E D deltaWeight s t N k p a r := by
  by_cases hr0 : r = 0
  · simp [crossBudget,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget, hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    rw [crossBudget_eq_positiveTime]
    exact APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget_nonneg
      E D deltaWeight s t N k p a hp hrpos

/-- For each fixed `p ≥ 1`, T1225's literal generator estimate integrates to
the actual weighted Minkowski inequality on every active moving target cell.
One eventual cutoff works for all `k` (including `k = 0`) and every output.
The closed cell may start at zero; the derivative is used only on its open
interior. -/
theorem eventually_actual_closedCell_weightedMinkowski
    {E D c deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ,
        k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          actualClosedCellMinkowskiBoundAt E D deltaWeight s t p N k a := by
  have hgen :=
    APrimeGeneralMovingGeneratorAllOrdersClosedCell.eventually_actual_closedCell_momFlowDeriv_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hcrossInt :=
    eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hgen, hcrossInt, Filter.eventually_ge_atTop 2]
    with N hgenN hcrossIntN hN2
  have hN : 0 < N := by omega
  intro k hk a
  let v := endpoint s t D N k
  let w := weight E D s t deltaWeight p N k
  let Ψ := APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N) v
  let Ψ₁ := coordinate E D N a (s N) v
  let wD := APrimeGeneralMovingGeneratorAllOrdersClosedCell.weightD
    E D s t deltaWeight p N k
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
      APrimeNormalizedTestFun.normalizedTestFunBridge d E D N p Step2.sigPM a
        hE (hs0 N) hsv hv1
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
      APrimeGeneralMovingSmoothDriftNormBudget.weight,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.weightD]
    exact APrimeSmoothWeightActual.weightC1 d
      (E := E) (D := D) (δ := deltaWeight) (s := s) (t := t)
      (mesh := APrimeGeneralMovingMesh.targetMesh D) (N₀ := 2)
      (p := p) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      hE ((hst N).trans_lt (ht1 N)) hN hm hu
  have hW0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t deltaWeight p N k ω
  have hre := APrimeDriftTimeFamily.momentAt_isModulusPow
    d E D N p Step2.sigPM a (s N) v
  have hcont := APrimeDuhamelModel.continuousOn_momFlow
    htest hwC1 hre (Set.Subset.rfl : Icc (s N) v ⊆ Icc (s N) v)
  have hderiv : ∀ u ∈ Ioo (s N) v,
      HasDerivAt
        (fun r : ℝ => ∫ ω, w ω *
          |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p) ∂(P d))
        (φ' u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt (hs0 N) hu.1
    exact APrimeDuhamelModel.hasDerivAt_momFlow htest hwC1 hre hu0
      (Icc_mem_nhds hu.1 hu.2)
  have hphiInt : IntervalIntegrable φ' volume (s N) v :=
    APrimeDuhamelModel.intervalIntegrable_momFlowDeriv htest hwC1 hre
      (hs0 N) hsv (Set.Subset.rfl : Icc (s N) v ⊆ Icc (s N) v)
  have hA0 : ∀ u ∈ Icc (s N) v,
      0 ≤ driftNorm E D s t deltaWeight p N k a u := by
    intro u hu
    exact momNormW_nonneg (P := P d) hW0 p _
  have hB0 : ∀ u ∈ Icc (s N) v,
      0 ≤ crossBudget E D deltaWeight s t N k p a u := by
    intro u hu
    exact crossBudget_nonneg E D deltaWeight s t N k p hp a
      ((hs0 N).trans hu.1)
  have hg0 : ∀ u ∈ Icc (s N) v,
      0 ≤ qvNorm E D s t deltaWeight p N k a u := by
    intro u hu
    exact APrimeModel.rateNormW_nonneg hW0 p _
  have hAint : IntervalIntegrable
      (driftNorm E D s t deltaWeight p N k a) volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a)
      volume (s N) v
    exact APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      hE hs0 hst ht1 hN hk a
  have hBint : IntervalIntegrable
      (crossBudget E D deltaWeight s t N k p a) volume (s N) v := by
    have heq :
        crossBudget E D deltaWeight s t N k p a =
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a := by
      funext r
      exact crossBudget_eq_positiveTime E D deltaWeight s t N k p a r
    rw [heq]
    exact hcrossIntN k hk a
  have hABint : IntervalIntegrable
      (fun r => driftNorm E D s t deltaWeight p N k a r +
        crossBudget E D deltaWeight s t N k p a r) volume (s N) v :=
    hAint.add hBint
  have hgint : IntervalIntegrable
      (qvNorm E D s t deltaWeight p N k a) volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingActualSmoothQVNormBudget.g
        E D s t deltaWeight p N k a) volume (s N) v
    exact APrimeGeneralMovingActualSmoothQVNormBudget.intervalIntegrable_g
      hE hs0 hst ht1 hp hN hk a
  have hprefix : ∀ u ∈ Icc (s N) v,
      IntervalIntegrable
        (fun r => momNormW (P d) w p
          (APrimeDuhamelModel.flowY d N Ψ₁ r) *
          (driftNorm E D s t deltaWeight p N k a r +
            crossBudget E D deltaWeight s t N k p a r)) volume (s N) u := by
    intro u hu
    exact APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
      hsv (Set.Subset.rfl : Icc (s N) v ⊆ Icc (s N) v)
      (p := p) hp htest hwC1 hre hABint hu
  have hbound : ∀ u ∈ Ioo (s N) v,
      φ' u ≤
        2 * (p : ℝ) *
            (∫ ω, w ω *
              |APrimeDuhamelModel.flowY d N Ψ₁ u ω| ^ (2 * p) ∂(P d)) ^
              ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
            (driftNorm E D s t deltaWeight p N k a u +
              crossBudget E D deltaWeight s t N k p a u) +
        (p : ℝ) * (2 * (p : ℝ) - 1) *
            (∫ ω, w ω *
              |APrimeDuhamelModel.flowY d N Ψ₁ u ω| ^ (2 * p) ∂(P d)) ^
              (((p : ℝ) - 1) / (p : ℝ)) *
            APrimeModel.rateNormW (P d) w p
              (APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v u) := by
    intro u hu
    have hpoint := hgenN k hk a u
      ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    simpa [φ', Ψ, Ψ₁, w, wD, v, endpoint, coordinate, weight,
      driftNorm, crossBudget, qvNorm,
      APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      APrimeGeneralMovingActualSmoothQVNormBudget.g,
      APrimeGeneralMovingActualSmoothQVNormBudget.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.weight,
      APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.d,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.endpoint,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.moment,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.coordinate,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.weight,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.weightD,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.drift,
      APrimeGeneralMovingGeneratorAllOrdersClosedCell.qv,
      d] using hpoint
  have hMink := MomentDuhamel.weightedMinkowski_of_deriv_le hsv hp hW0
    hcont hderiv hphiInt hA0 hB0 hg0 hABint hgint hprefix hbound
  have hresult := hMink
  dsimp [actualClosedCellMinkowskiBoundAt, flowY, endpoint, weight,
    driftNorm, crossBudget, qvNorm, coordinate, d] at hresult
  exact hresult

/-- T995's explicit same-resident witness records a satisfiable, nondegenerate
parameter regime for the inherited schedule and actual smooth weight. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms crossBudget_eq_positiveTime
#print axioms crossBudget_nonneg
#print axioms eventually_actual_closedCell_weightedMinkowski
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingAllOrdersMinkowskiActual
