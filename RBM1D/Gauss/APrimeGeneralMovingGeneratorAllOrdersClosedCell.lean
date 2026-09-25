/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDuhamelModel
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeGeneralMovingGeneratorHle
import RBM1D.Gauss.APrimeGeneralMovingWeightedCoordinateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingWeightedDriftIntegrable
import RBM1D.Gauss.APrimeGeneralMovingWeightedQVIntegrable
import RBM1D.Gauss.APrimeGeneralMovingWeightedRateMeasurable
import RBM1D.Gauss.APrimeGeneralMovingWeightedDriftProductIntegrable
import RBM1D.Gauss.APrimeGeneralMovingWeightedQVProductIntegrable
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossPositive
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossTimeZero

/-!
# T1225: all-orders closed-cell general-moving generator bound

For each fixed `p ≥ 1`, this specializes the model Duhamel inequality to the
literal T615 actual smooth weight and the `Step2.sigPM` moving coordinate.
Regularity, sign, actual moment/coordinate/drift/QV, measurability,
integrability, and the pointwise generator premise come from the accepted
all-order producers. Positive time uses T1089's exact `positiveTimeCrossBudget`;
time zero uses the exact zero cross term and budget `0`.
-/

namespace RBM.APrimeGeneralMovingGeneratorAllOrdersClosedCell

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (s _t : Nat → Real) (D : Real) (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight p N k

noncomputable def weightD (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : (d.Idx N × d.Idx N × Bool) → Ω d → Real :=
  APrimeSmoothWeightActual.weightD d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

noncomputable def moment (E D : Real) (N : Nat)
    (p : Nat) (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a s v

noncomputable def coordinate (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v

noncomputable def drift (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a s v

noncomputable def qv (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v

/-- Piecewise actual cross budget: exact zero at time zero and T1089's
positive-time budget for every strictly positive time. -/
noncomputable def closedCellCrossBudget (E D deltaWeight : Real) (s t : Nat → Real)
    (N k p : Nat) (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  if r = 0 then 0 else
    APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
      E D deltaWeight s t N k p a r

private theorem coordinate_contDiff (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) {s v r : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hv1 : v < 1)
    (hr : r ∈ Icc s v) :
    ContDiff ℝ 1 (coordinate E D N a s v r) := by
  obtain ⟨cK, _, hK, _⟩ := Gauss.exists_bdd_Kval_Kprim
    (d := d) E N hE.le hs0 hv1 Step2.sigPM
  have hη := Gauss.window_eta_pos hE hv1
  have hz := Gauss.window_im_ne_zero hE hv1 r hr
  have hzη := Gauss.window_le_abs_im hE hv1 r hr
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn Step2.sigPM) (m := 2) hη hz hzη List.length_ofFn
    (xiOf (mSigma E) Step2.sigPM) ((v : Real) : Complex)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (Step2.sigPM, b))) a
    (hK r hr)
  unfold coordinate APrimeDriftTimeFamily.coordAt
  exact (hraw.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).div_const _

/-- For every fixed `p ≥ 1`, on every active general-moving target cell and
every time in its closed cell, the exact `APrimeDuhamelModel.momFlowDeriv_le`
conclusion holds for T615's actual smooth weight and `Step2.sigPM`, conditional
only on that theorem's literal cross-term premise. The sample, moment endpoint,
coordinate, rates, and weight derivative all use the same `N,k,a,r`. -/
theorem eventually_actual_momFlowDeriv_le_of_hcross
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (s N) (endpoint s t D N k),
      ∀ Bc : Real, 0 ≤ Bc →
      APrimeDuhamelModel.crossPart d N
          (moment E D N p a (s N) (endpoint s t D N k))
          (weightD E D s t deltaWeight p N k) r ≤
        2 * (p : Real) *
          (∫ ω, weight E D s t deltaWeight p N k ω *
            |APrimeDuhamelModel.flowY d N
              (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
              ∂(P d)) ^ ((2 * (p : Real) - 1) / (2 * (p : Real))) * Bc →
      APrimeDuhamelModel.momFlowDeriv d N
          (moment E D N p a (s N) (endpoint s t D N k))
          (weight E D s t deltaWeight p N k)
          (weightD E D s t deltaWeight p N k) r ≤
        2 * (p : Real) *
            (∫ ω, weight E D s t deltaWeight p N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
                ∂(P d)) ^ ((2 * (p : Real) - 1) / (2 * (p : Real))) *
            (MomentDuhamel.momNormW (P d) (weight E D s t deltaWeight p N k)
              p (drift E D N a (s N) (endpoint s t D N k) r) + Bc) +
          (p : Real) * (2 * (p : Real) - 1) *
            (∫ ω, weight E D s t deltaWeight p N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
                ∂(P d)) ^ (((p : Real) - 1) / (p : Real)) *
            APrimeModel.rateNormW (P d) (weight E D s t deltaWeight p N k)
              p (qv E D N a (s N) (endpoint s t D N k) r) := by
  have hYiEv :=
    APrimeGeneralMovingWeightedCoordinateIntegrable.eventually_actual_weighted_flowY_integrable
      (E := E) (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1
      p hp
  have hGiEv :=
    APrimeGeneralMovingWeightedDriftIntegrable.eventually_actual_weighted_drift_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg p hp
  have hQiEv :=
    APrimeGeneralMovingWeightedQVIntegrable.eventually_integrable_hQi
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg (p := p) hp
  have hm1Ev :=
    APrimeGeneralMovingWeightedDriftProductIntegrable.eventually_actual_weighted_drift_product_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg p hp
  have hm2Ev :=
    APrimeGeneralMovingWeightedQVProductIntegrable.eventually_actual_weighted_qv_product_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg p hp
  filter_upwards [hYiEv, hGiEv, hQiEv, hm1Ev, hm2Ev, eventually_ge_atTop 2]
    with N hYiN hGiN hQiN hm1N hm2N hN2
  have hNpos : 0 < N := by omega
  intro k hk a r hr Bc hBc0 hcross
  let v := endpoint s t D N k
  let w := weight E D s t deltaWeight p N k
  let wD := weightD E D s t deltaWeight p N k
  let Ψ := moment E D N p a (s N) v
  let Ψ₁ := coordinate E D N a (s N) v
  let G := drift E D N a (s N) v r
  let Q := qv E D N a (s N) v r
  have hv : v ∈ Icc (s N) (t N) := by
    simpa [v, endpoint] using
      (MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk))
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hsv : s N ≤ v := hv.1
  have hr' : r ∈ Icc (s N) v := by simpa [v] using hr
  have htest : Gauss.TestFunT₁ d N (Icc (s N) v) Ψ := by
    simpa [APrimeDriftTimeFamily.NormalizedTestFunBridge, Ψ, moment] using
      (APrimeNormalizedTestFun.normalizedTestFunBridge d E D N p Step2.sigPM a
        hE (hs0 N) hsv hv1)
  have hwC1 : Gauss.WeightC1 d N w wD := by
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N :=
      APrimeSmoothWeightActual.canonicalM_pos d s t
        (APrimeGeneralMovingMesh.targetMesh D) N
    have hu : ∀ j < k,
        cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j < 1 := by
      intro j hj
      have hjtop : j ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N :=
        hj.le.trans hk
      have hjmem := MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hjtop)
      exact hjmem.2.trans_lt (ht1 N)
    dsimp only [w, wD, weight, weightD,
      APrimeGeneralMovingSmoothDriftNormBudget.weight]
    exact APrimeSmoothWeightActual.weightC1 d
      (E := E) (D := D) (δ := deltaWeight) (s := s) (t := t)
      (mesh := APrimeGeneralMovingMesh.targetMesh D) (N₀ := 2)
      (p := p) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      hE hs1 hNpos hm hu
  have hW0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t deltaWeight p N k ω
  have hQ0 : ∀ ω, 0 ≤ Q ω := by
    intro ω
    change 0 ≤ APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v r ω
    rw [APrimeDriftTimeFamily.qvAt_eq_evolved]
    exact APrimeDuhamelModel.qvRateEvolved_nonneg d N Ψ₁ r ω
  have hYi : Integrable
      (fun ω => w ω *
        |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p)) (P d) := by
    exact (hYiN k hk Step2.sigPM a r hr').2
  have hGi : Integrable (fun ω => w ω * |G ω| ^ (2 * p)) (P d) := by
    exact hGiN k hk a r hr
  have hQi : Integrable (fun ω => w ω * |Q ω| ^ p) (P d) := by
    exact hQiN k hk a r hr
  have hm1 : Integrable
      (fun ω => w ω * |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p - 1) *
        |G ω|) (P d) := by
    exact hm1N k hk a r hr
  have hm2 : Integrable
      (fun ω => w ω * |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p - 2) * Q ω)
      (P d) := by
    exact hm2N k hk a r hr
  have hYm : AEStronglyMeasurable
      (APrimeDuhamelModel.wscale w p (APrimeDuhamelModel.flowY d N Ψ₁ r)) (P d) := by
    have hwmeas : Measurable w := by
      exact APrimeGeneralMovingSmoothDriftNormBudget.measurable_weight
        (deltaWeight := deltaWeight) hE hst ht1 hNpos hk
    have hwr : Measurable (fun ω : Ω d =>
        w ω ^ ((1 : Real) / (2 * (p : Real)))) :=
      (Real.continuous_rpow_const (by positivity :
        (0 : Real) ≤ (1 : Real) / (2 * (p : Real)))).measurable.comp hwmeas
    have hcoord := coordinate_contDiff E D N a hE (hs0 N) hv1 hr'
    have hYmeas : Measurable (fun ω : Ω d =>
        APrimeDuhamelModel.flowY d N Ψ₁ r ω) := by
      rw [show (fun ω : Ω d => APrimeDuhamelModel.flowY d N Ψ₁ r ω) =
        fun ω => ‖Ψ₁ r (Gauss.Hflow d N r ω)‖ by rfl]
      exact ((hcoord.continuous.comp (Gauss.continuous_Hflow d N r)).norm).measurable
    have hscaled : Measurable (fun ω : Ω d =>
        w ω ^ ((1 : Real) / (2 * (p : Real))) *
          APrimeDuhamelModel.flowY d N Ψ₁ r ω) := hwr.mul hYmeas
    have hscaleEq : APrimeDuhamelModel.wscale w p
        (APrimeDuhamelModel.flowY d N Ψ₁ r) =
          fun ω => w ω ^ ((1 : Real) / (2 * (p : Real))) *
            APrimeDuhamelModel.flowY d N Ψ₁ r ω := rfl
    rw [hscaleEq]
    exact hscaled.aestronglyMeasurable (μ := P d)
  have hGm :=
    APrimeGeneralMovingWeightedRateMeasurable.hGm
      (E := E) (D := D) (deltaWeight := deltaWeight)
      hE hs0 hst ht1 hNpos hk a hr' hp
  have hGm' : AEStronglyMeasurable (APrimeDuhamelModel.wscale w p G) (P d) := by
    simpa [w, weight, G, drift, v, endpoint,
      APrimeGeneralMovingWeightedRateMeasurable.weight,
      APrimeGeneralMovingWeightedRateMeasurable.drift,
      APrimeGeneralMovingSmoothDriftNormBudget.drift,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hGm
  have hQm :=
    APrimeGeneralMovingWeightedRateMeasurable.hQm
      (E := E) (D := D) (deltaWeight := deltaWeight)
      hE hs0 hst ht1 hNpos hk a hr' hp
  have hQm' : AEStronglyMeasurable (APrimeDuhamelModel.wscaleQ w p Q) (P d) := by
    simpa [w, weight, Q, qv, v, endpoint,
      APrimeGeneralMovingWeightedRateMeasurable.weight,
      APrimeGeneralMovingWeightedRateMeasurable.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.qv,
      APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingQVNormBudget.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hQm
  have hle := APrimeGeneralMovingGeneratorHle.actual_weight_hle
    (E := E) (D := D) (deltaWeight := deltaWeight) (p := p) (N := N) (k := k)
    hE hs0 hst ht1 hk a Step2.sigPM hr' hp
  have hle' : ∀ ω, w ω *
      ((Gauss.timeD1 Ψ r (Gauss.Hflow d N r ω)).re +
        APrimeDuhamelModel.genPt d N (Ψ r) (Gauss.Hflow d N r ω)) ≤
      w ω * (2 * (p : Real) *
          (|APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p - 1) * |G ω|) +
        (p : Real) * (2 * (p : Real) - 1) *
          (|APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p - 2) * Q ω)) := by
    exact hle
  have hcross' : APrimeDuhamelModel.crossPart d N Ψ wD r ≤
      2 * (p : Real) *
        (∫ ω, w ω * |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * p)
          ∂(P d)) ^
          ((2 * (p : Real) - 1) / (2 * (p : Real))) * Bc := by
    simpa [v, w, Ψ, Ψ₁, wD, moment, coordinate, weightD, endpoint, weight,
      APrimeDriftTimeFamily.momentAt, APrimeDriftTimeFamily.coordAt,
      APrimeGeneralMovingSmoothDriftNormBudget.weight] using hcross
  convert APrimeDuhamelModel.momFlowDeriv_le
    (d := d) (N := N) (T := Icc (s N) v)
    (Ψ := Ψ) (Ψ₁ := Ψ₁) (w := w) (wD := wD)
    (p := p) (Bc := Bc) (hp := hp) htest hwC1 hr'
    hW0 hQ0 hYm hGm' hQm' hYi hGi hQi hm1 hm2 hle' hcross' using 1

/-- The all-fixed-order exact closed-cell generator estimate. For each fixed
`p ≥ 1`, its eventual bound is uniform in every active target-mesh index,
output, and closed-cell time, including `r = 0` and `k = 0`. -/
theorem eventually_actual_closedCell_momFlowDeriv_le
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hdeltaWeight : 0 ≤ deltaWeight)
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (s N) (endpoint s t D N k),
      APrimeDuhamelModel.momFlowDeriv d N
          (moment E D N p a (s N) (endpoint s t D N k))
          (weight E D s t deltaWeight p N k)
          (weightD E D s t deltaWeight p N k) r ≤
        2 * (p : Real) *
            (∫ ω, weight E D s t deltaWeight p N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
                ∂(P d)) ^ ((2 * (p : Real) - 1) / (2 * (p : Real))) *
            (MomentDuhamel.momNormW (P d) (weight E D s t deltaWeight p N k)
              p (drift E D N a (s N) (endpoint s t D N k) r) +
              closedCellCrossBudget E D deltaWeight s t N k p a r) +
          (p : Real) * (2 * (p : Real) - 1) *
            (∫ ω, weight E D s t deltaWeight p N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
                ∂(P d)) ^ (((p : Real) - 1) / (p : Real)) *
            APrimeModel.rateNormW (P d) (weight E D s t deltaWeight p N k)
              p (qv E D N a (s N) (endpoint s t D N k) r) := by
  have hconditional := eventually_actual_momFlowDeriv_le_of_hcross
    (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
    hE hD hs0 hst ht1 hc hreg p hp
  have hpositive :=
    APrimeGeneralMovingCrossHcrossPositive.eventually_positive_time_hcross
      (E := E) (D := D) (c := c) hE hD hs0 hst ht1 hc hreg
      hdeltaWeight p hp
  filter_upwards [hconditional, hpositive, eventually_ge_atTop 2]
    with N hconditionalN hpositiveN hN2
  intro k hk a r hr
  by_cases hr0 : r = 0
  · subst r
    have hcrossZero :=
      APrimeGeneralMovingCrossHcrossTimeZero.actual_hcross_r0
        E D deltaWeight s t N k p hp hk hr a
    have hcrossZero' :
        APrimeDuhamelModel.crossPart d N
            (moment E D N p a (s N) (endpoint s t D N k))
            (weightD E D s t deltaWeight p N k) 0 ≤
          2 * (p : Real) *
            (∫ ω, weight E D s t deltaWeight p N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) 0 ω| ^ (2 * p)
              ∂(P d)) ^ ((2 * (p : Real) - 1) / (2 * (p : Real))) * 0 := by
      simpa only [moment, weightD, endpoint,
        APrimeGeneralMovingCrossHcrossTimeZero.actualWeightD, mul_zero] using hcrossZero
    have hresult := hconditionalN k hk a 0 hr 0 le_rfl hcrossZero'
    simpa [closedCellCrossBudget] using hresult
  · have hrnonneg : 0 ≤ r := (hs0 N).trans hr.1
    have hrpos : 0 < r := lt_of_le_of_ne hrnonneg (Ne.symm hr0)
    obtain ⟨hBc, hcrossBound⟩ := hpositiveN k hk a r hr hrpos
    have hmomentEq :
        (∫ ω, weight E D s t deltaWeight p N k ω *
          |APrimeDuhamelModel.flowY d N
            (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
          ∂(P d)) =
        APrimeGeneralMovingCrossHcrossPositive.actualWeightedMoment
          E D deltaWeight s t N k p a r := by
      rw [APrimeGeneralMovingCrossHcrossPositive.actualWeightedMoment]
      apply integral_congr_ae
      filter_upwards with ω
      simp [APrimeGeneralMovingCrossHcrossPositive.actualFlowY,
        weight, coordinate, endpoint,
        APrimeGeneralMovingSmoothDriftNormBudget.weight]
    have hcrossAligned :
        APrimeDuhamelModel.crossPart d N
            (moment E D N p a (s N) (endpoint s t D N k))
            (weightD E D s t deltaWeight p N k) r ≤
          2 * (p : Real) *
            (∫ ω, weight E D s t deltaWeight p N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * p)
              ∂(P d)) ^ ((2 * (p : Real) - 1) / (2 * (p : Real))) *
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D deltaWeight s t N k p a r := by
      rw [hmomentEq]
      simpa [moment, weightD, endpoint] using
        hcrossBound
    have hresult := hconditionalN k hk a r hr
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D deltaWeight s t N k p a r) hBc hcrossAligned
    simpa [closedCellCrossBudget, hr0] using hresult

/-- T995's scheduled same-resident witness for a genuine positive cell and
strictly positive actual weight; this records nondegeneracy of the model. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms coordinate_contDiff
#print axioms eventually_actual_momFlowDeriv_le_of_hcross
#print axioms eventually_actual_closedCell_momFlowDeriv_le
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingGeneratorAllOrdersClosedCell
