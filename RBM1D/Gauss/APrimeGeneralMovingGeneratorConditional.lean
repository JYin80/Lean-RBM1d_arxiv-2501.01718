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

/-!
# T1093: the one-hole general-moving generator seam

This specializes the model Duhamel inequality to the literal T615 actual
smooth weight and the `Step2.sigPM` moving coordinate at `p = 1`. All
regularity, sign, moment, product-integrability, and pointwise-generator
premises are supplied by accepted producers. The only conditional input is
the exact `hcross` inequality with a named nonnegative budget `Bc`.
-/

namespace RBM.APrimeGeneralMovingGeneratorConditional

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

private noncomputable def endpoint (s _t : Nat → Real) (D : Real) (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

private noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight 1 N k

private noncomputable def weightD (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (N k : Nat) : (d.Idx N × d.Idx N × Bool) → Ω d → Real :=
  APrimeSmoothWeightActual.weightD d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 1 N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

private noncomputable def moment (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.momentAt d E D N 1 Step2.sigPM a s v

private noncomputable def coordinate (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v

private noncomputable def drift (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a s v

private noncomputable def qv (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v

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

/-- For `p = 1`, on every active general-moving target cell and every time in
its closed cell, the exact `APrimeDuhamelModel.momFlowDeriv_le` conclusion
holds for T615's actual smooth weight and `Step2.sigPM`, conditional only on
that theorem's literal cross-term premise. The sample, moment endpoint,
coordinate, rates, and weight derivative all use the same `N,k,a,r`. -/
theorem eventually_actual_momFlowDeriv_le_of_hcross
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (s N) (endpoint s t D N k),
      ∀ Bc : Real, 0 ≤ Bc →
      APrimeDuhamelModel.crossPart d N
          (moment E D N a (s N) (endpoint s t D N k))
          (weightD E D s t deltaWeight N k) r ≤
        2 * (1 : Real) *
          (∫ ω, weight E D s t deltaWeight N k ω *
            |APrimeDuhamelModel.flowY d N
              (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * 1)
              ∂(P d)) ^ ((2 * (1 : Real) - 1) / (2 * (1 : Real))) * Bc →
      APrimeDuhamelModel.momFlowDeriv d N
          (moment E D N a (s N) (endpoint s t D N k))
          (weight E D s t deltaWeight N k)
          (weightD E D s t deltaWeight N k) r ≤
        2 * (1 : Real) *
            (∫ ω, weight E D s t deltaWeight N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * 1)
                ∂(P d)) ^ ((2 * (1 : Real) - 1) / (2 * (1 : Real))) *
            (MomentDuhamel.momNormW (P d) (weight E D s t deltaWeight N k)
              1 (drift E D N a (s N) (endpoint s t D N k) r) + Bc) +
          (1 : Real) * (2 * (1 : Real) - 1) *
            (∫ ω, weight E D s t deltaWeight N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s t D N k)) r ω| ^ (2 * 1)
                ∂(P d)) ^ (((1 : Real) - 1) / (1 : Real)) *
            APrimeModel.rateNormW (P d) (weight E D s t deltaWeight N k)
              1 (qv E D N a (s N) (endpoint s t D N k) r) := by
  have hYiEv :=
    APrimeGeneralMovingWeightedCoordinateIntegrable.eventually_actual_weighted_flowY_integrable
      (E := E) (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1
      1 (by norm_num : 1 ≤ 1)
  have hGiEv :=
    APrimeGeneralMovingWeightedDriftIntegrable.eventually_actual_weighted_drift_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg 1 (by norm_num : 1 ≤ 1)
  have hQiEv :=
    APrimeGeneralMovingWeightedQVIntegrable.eventually_integrable_hQi
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg (p := 1) (by norm_num : 1 ≤ 1)
  have hm1Ev :=
    APrimeGeneralMovingWeightedDriftProductIntegrable.eventually_actual_weighted_drift_product_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg 1 (by norm_num : 1 ≤ 1)
  have hm2Ev :=
    APrimeGeneralMovingWeightedQVProductIntegrable.eventually_actual_weighted_qv_product_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg 1 (by norm_num : 1 ≤ 1)
  filter_upwards [hYiEv, hGiEv, hQiEv, hm1Ev, hm2Ev, eventually_ge_atTop 2]
    with N hYiN hGiN hQiN hm1N hm2N hN2
  have hNpos : 0 < N := by omega
  intro k hk a r hr Bc hBc0 hcross
  let v := endpoint s t D N k
  let w := weight E D s t deltaWeight N k
  let wD := weightD E D s t deltaWeight N k
  let Ψ := moment E D N a (s N) v
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
      (APrimeNormalizedTestFun.normalizedTestFunBridge d E D N 1 Step2.sigPM a
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
      (p := 1) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      hE hs1 hNpos hm hu
  have hW0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t deltaWeight 1 N k ω
  have hQ0 : ∀ ω, 0 ≤ Q ω := by
    intro ω
    change 0 ≤ APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v r ω
    rw [APrimeDriftTimeFamily.qvAt_eq_evolved]
    exact APrimeDuhamelModel.qvRateEvolved_nonneg d N Ψ₁ r ω
  have hYi : Integrable
      (fun ω => w ω *
        |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * 1)) (P d) := by
    exact (hYiN k hk Step2.sigPM a r hr').2
  have hGi : Integrable (fun ω => w ω * |G ω| ^ (2 * 1)) (P d) := by
    exact hGiN k hk a r hr
  have hQi : Integrable (fun ω => w ω * |Q ω| ^ 1) (P d) := by
    exact hQiN k hk a r hr
  have hm1 : Integrable
      (fun ω => w ω * |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * 1 - 1) *
        |G ω|) (P d) := by
    exact hm1N k hk a r hr
  have hm2 : Integrable
      (fun ω => w ω * |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * 1 - 2) * Q ω)
      (P d) := by
    exact hm2N k hk a r hr
  have hYm : AEStronglyMeasurable
      (APrimeDuhamelModel.wscale w 1 (APrimeDuhamelModel.flowY d N Ψ₁ r)) (P d) := by
    have hwmeas : Measurable w := by
      exact APrimeGeneralMovingSmoothDriftNormBudget.measurable_weight
        (deltaWeight := deltaWeight) hE hst ht1 hNpos hk
    have hwr : Measurable (fun ω : Ω d =>
        w ω ^ ((1 : Real) / (2 * (1 : Real)))) :=
      (Real.continuous_rpow_const (by positivity :
        (0 : Real) ≤ (1 : Real) / (2 * (1 : Real)))).measurable.comp hwmeas
    have hcoord := coordinate_contDiff E D N a hE (hs0 N) hv1 hr'
    have hYmeas : Measurable (fun ω : Ω d =>
        APrimeDuhamelModel.flowY d N Ψ₁ r ω) := by
      rw [show (fun ω : Ω d => APrimeDuhamelModel.flowY d N Ψ₁ r ω) =
        fun ω => ‖Ψ₁ r (Gauss.Hflow d N r ω)‖ by rfl]
      exact ((hcoord.continuous.comp (Gauss.continuous_Hflow d N r)).norm).measurable
    have hscaled : Measurable (fun ω : Ω d =>
        w ω ^ (2⁻¹ : Real) * APrimeDuhamelModel.flowY d N Ψ₁ r ω) := by
      convert hwr.mul hYmeas using 1
      funext ω
      congr 1
      norm_num
    have hscaleEq : APrimeDuhamelModel.wscale w 1
        (APrimeDuhamelModel.flowY d N Ψ₁ r) =
          fun ω => w ω ^ (2⁻¹ : Real) *
            APrimeDuhamelModel.flowY d N Ψ₁ r ω := by
      funext ω
      simp only [APrimeDuhamelModel.wscale]
      congr 1
      norm_num
    rw [hscaleEq]
    exact hscaled.aestronglyMeasurable (μ := P d)
  have hGm :=
    APrimeGeneralMovingWeightedRateMeasurable.hGm
      (E := E) (D := D) (deltaWeight := deltaWeight)
      hE hs0 hst ht1 hNpos hk a hr' (by norm_num : 1 ≤ 1)
  have hGm' : AEStronglyMeasurable (APrimeDuhamelModel.wscale w 1 G) (P d) := by
    simpa [w, weight, G, drift, v, endpoint,
      APrimeGeneralMovingWeightedRateMeasurable.weight,
      APrimeGeneralMovingWeightedRateMeasurable.drift,
      APrimeGeneralMovingSmoothDriftNormBudget.drift,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hGm
  have hQm :=
    APrimeGeneralMovingWeightedRateMeasurable.hQm
      (E := E) (D := D) (deltaWeight := deltaWeight)
      hE hs0 hst ht1 hNpos hk a hr' (by norm_num : 1 ≤ 1)
  have hQm' : AEStronglyMeasurable (APrimeDuhamelModel.wscaleQ w 1 Q) (P d) := by
    simpa [w, weight, Q, qv, v, endpoint,
      APrimeGeneralMovingWeightedRateMeasurable.weight,
      APrimeGeneralMovingWeightedRateMeasurable.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.qv,
      APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingQVNormBudget.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hQm
  have hle := APrimeGeneralMovingGeneratorHle.actual_weight_hle
    (E := E) (D := D) (deltaWeight := deltaWeight) (p := 1) (N := N) (k := k)
    hE hs0 hst ht1 hk a Step2.sigPM hr' (by norm_num : 1 ≤ 1)
  have hle' : ∀ ω, w ω *
      ((Gauss.timeD1 Ψ r (Gauss.Hflow d N r ω)).re +
        APrimeDuhamelModel.genPt d N (Ψ r) (Gauss.Hflow d N r ω)) ≤
      w ω * (2 * ((1 : Nat) : Real) *
          (|APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * (1 : Nat) - 1) * |G ω|) +
        ((1 : Nat) : Real) * (2 * ((1 : Nat) : Real) - 1) *
          (|APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * (1 : Nat) - 2) * Q ω)) := by
    exact hle
  have hcross' : APrimeDuhamelModel.crossPart d N Ψ wD r ≤
      2 * ((1 : Nat) : Real) *
        (∫ ω, w ω * |APrimeDuhamelModel.flowY d N Ψ₁ r ω| ^ (2 * (1 : Nat))
          ∂(P d)) ^
          ((2 * ((1 : Nat) : Real) - 1) / (2 * ((1 : Nat) : Real))) * Bc := by
    simpa [v, w, Ψ, Ψ₁, wD, moment, coordinate, weightD, endpoint, weight,
      APrimeDriftTimeFamily.momentAt, APrimeDriftTimeFamily.coordAt,
      APrimeGeneralMovingSmoothDriftNormBudget.weight] using hcross
  convert APrimeDuhamelModel.momFlowDeriv_le
    (d := d) (N := N) (T := Icc (s N) v)
    (Ψ := Ψ) (Ψ₁ := Ψ₁) (w := w) (wD := wD)
    (p := 1) (Bc := Bc) (hp := by norm_num) htest hwC1 hr'
    hW0 hQ0 hYm hGm' hQm' hYi hGi hQi hm1 hm2 hle' hcross' using 1
  all_goals simp [v, w, Ψ₁, G, Q, coordinate, drift, qv, weight, endpoint]

/-- The actual T615 weight's cross premise is inhabited at the zero-prefix
cell: its coordinate derivative vanishes, so `Bc = 0` is an exact witness.
This records the boundary case without extending it to positive cells. -/
theorem k0_cross_hypothesis_witness
    (E D deltaWeight : Real) (s t : Nat → Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) :
    ∃ Bc : Real, 0 ≤ Bc ∧
      APrimeDuhamelModel.crossPart d N
          (moment E D N a (s N) (endpoint s t D N 0))
          (weightD E D s t deltaWeight N 0) r ≤
        2 * (1 : Real) *
          (∫ ω, weight E D s t deltaWeight N 0 ω *
            |APrimeDuhamelModel.flowY d N
              (coordinate E D N a (s N) (endpoint s t D N 0)) r ω| ^ (2 * 1)
              ∂(P d)) ^ ((2 * (1 : Real) - 1) / (2 * (1 : Real))) * Bc := by
  refine ⟨0, le_rfl, ?_⟩
  have hzero : APrimeDuhamelModel.crossPart d N
      (moment E D N a (s N) (endpoint s t D N 0))
      (weightD E D s t deltaWeight N 0) r = 0 := by
    unfold moment weightD endpoint
    exact APrimeCrossJointSplit.crossPart_zero_k0 d E D deltaWeight s t
      (APrimeGeneralMovingMesh.targetMesh D) 2 N
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) 1
      (APrimeSmoothWeightActual.canonicalM_pos d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      (APrimeDriftTimeFamily.momentAt d E D N 1 Step2.sigPM a
        (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0)) r
  rw [hzero]
  simp

/-- The accepted T995 witness realizes a positive actual smooth weight on a
genuine `E = 0`, `D = 60` general-moving window and an active positive cell.
It witnesses the model/weight context; it is not a positive-cell `hcross`
producer. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms coordinate_contDiff
#print axioms eventually_actual_momFlowDeriv_le_of_hcross
#print axioms k0_cross_hypothesis_witness
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingGeneratorConditional
