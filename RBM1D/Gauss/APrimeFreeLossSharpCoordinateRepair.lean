/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossCoordinateBridge
import RBM1D.Gauss.APrimeFreeLossDriftCrossBudget
import RBM1D.Gauss.APrimeFreeLossQVRoot

/-!
# Sharp actual weighted endpoint-coordinate moment

The initial, full drift/cross, and quadratic-variation budgets are combined
without discarding the endpoint ratio.  The result is a moment prerequisite
for the near term in (5.48), not an unweighted stochastic domination bound.
-/

namespace RBM.APrimeFreeLossSharpCoordinateRepair

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The exact actual smooth-weight coordinate bound, with the sharp
endpoint ratio retained. -/
def SharpActualCoordinateMoment (E D lambda C : ℝ) (s t : ℕ → ℝ)
    (p N k : ℕ) : Prop :=
  ∀ a : LoopArg (d.L N) 2,
    AEStronglyMeasurable
      (APrimeFreeLossCoordinateBridge.endpointCoordinate E D s t N k a) (Gauss.P d) ∧
    Integrable
      (fun ω =>
        APrimeSmoothWeightActual.weight d E D lambda s t (mesh D) 2 p N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
          |APrimeFreeLossCoordinateBridge.endpointCoordinate E D s t N k a ω| ^
            (2 * p)) (Gauss.P d) ∧
    ∫ ω,
      APrimeSmoothWeightActual.weight d E D lambda s t (mesh D) 2 p N k
        (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
        |APrimeFreeLossCoordinateBridge.endpointCoordinate E D s t N k a ω| ^
          (2 * p) ∂(Gauss.P d) ≤
      (C * (N : ℝ) ^ (5 * lambda / 32) *
        (Step2Moment.ratR E s N
          (APrimeFreeLossCoordinateBridge.endpoint s t D N k)) ^ (-(2 : ℝ))) ^
        (2 * p)

private theorem initial_scalar {x R : ℝ} (hx : 0 ≤ x) (hR : 0 < R) :
    APrimeOneStep.initTerm x R (APrimeInit.slotXi' x) / R ^ 4 =
      x * APrimeInit.slotXi' x * R ^ (-(2 : ℝ)) := by
  rw [APrimeOneStep.initTerm, Real.rpow_neg hR.le]
  field_simp <;> simp [mul_comm, mul_left_comm, mul_assoc]

private theorem sqrt_budget {Q A z : ℝ} (hA : 0 ≤ A) (hz : 0 ≤ z)
    (hQ : Q ≤ A * z ^ 2) : Real.sqrt Q ≤ Real.sqrt A * z := by
  have hright : 0 ≤ Real.sqrt A * z := mul_nonneg (Real.sqrt_nonneg _) hz
  have hsq : (Real.sqrt A * z) ^ 2 = A * z ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA]
  by_cases hQ0 : 0 ≤ Q
  · nlinarith [Real.sq_sqrt hQ0]
  · have hQle : Q ≤ 0 := le_of_not_ge hQ0
    simpa [Real.sqrt_eq_zero_of_nonpos hQle] using hright


open APrimeFreeLossCoordinateBridge

private theorem coordinate_contDiff (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) {s v r : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hv1 : v < 1)
    (hr : r ∈ Icc s v) :
    ContDiff ℝ 1
      (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v r) := by
  obtain ⟨cK, hcK, hK, hK'⟩ := Gauss.exists_bdd_Kval_Kprim
    (d := d) E N hE.le hs0 hv1 Step2.sigPM
  have hη := Gauss.window_eta_pos hE hv1
  have hz := Gauss.window_im_ne_zero hE hv1 r hr
  have hzη := Gauss.window_le_abs_im hE hv1 r hr
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn Step2.sigPM) (m := 2) hη hz hzη List.length_ofFn
    (xiOf (mSigma E) Step2.sigPM) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (Step2.sigPM, b))) a
    (hK r hr)
  unfold APrimeDriftTimeFamily.coordAt
  exact (hraw.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).div_const _


/-- For each fixed order, the actual weighted endpoint coordinate has a
sharp `R⁻²` norm scale, uniformly over all active cells and outputs. -/
theorem eventually_sharp_actual_coordinate_moment
    {E D c lambda : ℝ} {s t : ℕ → ℝ} {p : ℕ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000) (c / 10000))
    (hp : 1 ≤ p) :
    ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        k ≤ cutNetTop s t (mesh D) N →
        SharpActualCoordinateMoment E D lambda C s t p N k := by
  obtain ⟨Cd, hCd, hDrift⟩ :=
    APrimeFreeLossDriftCrossBudget.exists_positive_C_eventually_actual_drift_plus_full_cross_hbudget
      hE hD hs0 hst ht1 hc hreg hB hlambda hsmall p hp
  let Cq := APrimeFreeLossQVRoot.actualQVIntegralConst E
  have hCq : 0 < Cq :=
    APrimeFreeLossQVRoot.actualQVIntegralConst_pos E hE
  have hQV := APrimeFreeLossQVRoot.eventually_actual_weight_qv_integral_le_budget
    hE hD hs0 hst ht1 hc hreg hB hlambda hsmall p hp
  have hMink :=
    APrimeGeneralMovingAllOrdersMinkowskiActual.eventually_actual_closedCell_weightedMinkowski
      (E := E) (D := D) (c := c) (deltaWeight := lambda) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hlambda.le p hp
  have hinit :=
    APrimeGeneralMovingInitialActualSmoothSlot.eventually_actual_smooth_initial_hinit
      (E := E) (D := D) (c := c) (δ := lambda) (δWeight := lambda)
      (s := s) (t := t) hE hD hs0 hst ht1 hc hreg hB hlambda p hp
  have hYi :=
    APrimeGeneralMovingWeightedCoordinateIntegrable.eventually_actual_weighted_flowY_integrable
      (E := E) (D := D) (deltaWeight := lambda) (s := s) (t := t)
      hE hs0 hst ht1 p hp
  let C : ℝ := 1 + Cd + Real.sqrt ((2 * (p : ℝ) - 1) * Cq)
  have hC : 0 < C := by
    have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hroot : 0 ≤ Real.sqrt ((2 * (p : ℝ) - 1) * Cq) := Real.sqrt_nonneg _
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [hMink, hinit, hYi, hDrift, hQV,
    Filter.eventually_ge_atTop 2] with N hMinkN hinitN hYiN hDriftN hQVN hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hx : 1 ≤ (N : ℝ) ^ (lambda / 8) :=
    Real.one_le_rpow hNreal (by linarith)
  intro k hk a
  let v : ℝ := endpoint s t D N k
  let R : ℝ := Step2Moment.ratR E s N v
  let x : ℝ := (N : ℝ) ^ (lambda / 8)
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, endpoint, APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint, mesh]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hv.1 hv1
  let W : Ω d → ℝ :=
    APrimeGeneralMovingAllOrdersMinkowskiActual.weight E D s t lambda p N k
  let Y : ℝ → Ω d → ℝ := fun r =>
    APrimeGeneralMovingAllOrdersMinkowskiActual.flowY E D N a (s N) v r
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t lambda p N k ω
  have hMinkAt := hMinkN k hk a
  have hG :
      MomentDuhamel.momNormW (P d) W p (Y v) ≤
        MomentDuhamel.momNormW (P d) W p (Y (s N)) +
          2 * (∫ r in (s N)..v,
            APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
                E D s t lambda p N k a r +
              APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
                E D lambda s t N k p a r) +
          Real.sqrt ((2 * (p : ℝ) - 1) *
            ∫ r in (s N)..v,
              APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
                E D s t lambda p N k a r) := by
    simpa [APrimeGeneralMovingAllOrdersMinkowskiActual.actualClosedCellMinkowskiBoundAt,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.weight,
      APrimeGeneralMovingAllOrdersMinkowskiActual.flowY,
      APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm,
      APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget,
      APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm,
      APrimeGeneralMovingSmoothDriftNormBudget.weight, W, Y, v, endpoint, mesh]
      using hMinkAt
  have hNpow0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hNpowPos : (0 : ℝ) < (N : ℝ) := by positivity
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRneg2 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hNcompareDrift :
      (N : ℝ) ^ (4 * (lambda / 1000)) ≤ (N : ℝ) ^ (5 * lambda / 32) :=
    Real.rpow_le_rpow_of_exponent_le hNreal (by nlinarith [hlambda])
  have hNcompareQV :
      (N : ℝ) ^ (2 * (lambda / 1000)) ≤ (N : ℝ) ^ (5 * lambda / 32) :=
    Real.rpow_le_rpow_of_exponent_le hNreal (by nlinarith [hlambda])
  have hDriftAt :
      2 * (∫ r in (s N)..v,
        APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
            E D s t lambda p N k a r +
          APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
            E D lambda s t N k p a r) ≤
        Cd * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(2 : ℝ)) := by
    by_cases hk0 : k = 0
    · subst k
      have hv0 : v = s N := by
        simp [v, endpoint, APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
          cutNetPt_zero]
      simp [hv0]
      positivity
    · have hkpos : 1 ≤ k := by omega
      have h := hDriftN k hkpos hk a
      have heq :
          APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
            E D lambda s t N k p a =
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D lambda s t N k p a := by
        funext r
        by_cases hr : r = 0
        · subst r
          simp [APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget,
            APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget]
        · simp [APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget,
            APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget, hr]
      rw [heq]
      simpa only [APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm,
        APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
        APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
        endpoint, v, R, mesh] using h
  have hQVAt :
      (∫ r in (s N)..v,
        APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
          E D s t lambda p N k a r) ≤
        Cq * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(4 : ℝ)) := by
    simpa only [Cq, APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm,
      APrimeGeneralMovingQVNormBudget.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      endpoint, v, R, mesh] using hQVN k hk a
  have hleft :
      Y (s N) = fun ω =>
        APrimeAssembly.initialEvolvedNormAt (Gauss.sample d) E D s N v a ω := by
    funext ω
    have h := APrimeGeneralMovingInitialFlow.flowY_left_eq_initialEvolvedNormAt
      (E := E) (D := D) (s := s) (t := t) N
      (⟨v, hv⟩ : TimeIcc s t N) hE (ht1 N) a
    simpa [Y, v, endpoint, APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.flowY,
      APrimeGeneralMovingAllOrdersMinkowskiActual.coordinate, mesh] using
        congrFun h ω
  have hinitAt := hinitN k hk a
  have hinit' :
      MomentDuhamel.momNormW (P d) W p (Y (s N)) ≤
        APrimeOneStep.initTerm x R (APrimeInit.slotXi' x) / R ^ 4 := by
    rw [hleft]
    simpa [W, x, R, v, endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.weight,
      APrimeGeneralMovingSmoothDriftNormBudget.weight,
      Step2Moment.ratR, mesh] using hinitAt
  have hinitial :
      MomentDuhamel.momNormW (P d) W p (Y (s N)) ≤
        (N : ℝ) ^ (5 * lambda / 32) * R ^ (-(2 : ℝ)) := by
    rw [initial_scalar (by positivity : 0 ≤ x) hRpos] at hinit'
    have hpow : x * APrimeInit.slotXi' x =
        (N : ℝ) ^ (5 * lambda / 32) := by
      dsimp [x, APrimeInit.slotXi']
      rw [← Real.rpow_mul (by positivity : 0 ≤ (N : ℝ))]
      rw [← Real.rpow_add (by positivity : 0 < (N : ℝ))]
      congr 1
      ring
    rw [hpow] at hinit'
    exact hinit'
  have hDriftSharp :
      2 * (∫ r in (s N)..v,
        APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
            E D s t lambda p N k a r +
          APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
            E D lambda s t N k p a r) ≤
        Cd * (N : ℝ) ^ (5 * lambda / 32) * R ^ (-(2 : ℝ)) := by
    exact hDriftAt.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNcompareDrift hCd.le) hRneg2)
  have hfactor : 0 ≤ 2 * (p : ℝ) - 1 := by
    have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hQVSqrt :
      Real.sqrt ((2 * (p : ℝ) - 1) *
        ∫ r in (s N)..v,
          APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
            E D s t lambda p N k a r) ≤
        Real.sqrt ((2 * (p : ℝ) - 1) * Cq) *
          (N : ℝ) ^ (5 * lambda / 32) * R ^ (-(2 : ℝ)) := by
    have hQ := mul_le_mul_of_nonneg_left hQVAt hfactor
    have hpow :
        ((N : ℝ) ^ (2 * (lambda / 1000)) * R ^ (-(2 : ℝ))) ^ 2 =
          (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(4 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hNpow0, ← Real.rpow_mul hRpos.le]
      congr 1 <;> ring
    have hQ' :
        (2 * (p : ℝ) - 1) *
            (∫ r in (s N)..v,
              APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
                E D s t lambda p N k a r) ≤
          ((2 * (p : ℝ) - 1) * Cq) *
            ((N : ℝ) ^ (2 * (lambda / 1000)) * R ^ (-(2 : ℝ))) ^ 2 := by
      rw [hpow]
      nlinarith [hQ]
    have hroot := sqrt_budget (mul_nonneg hfactor hCq.le)
      (mul_nonneg (Real.rpow_nonneg hNpow0 _) hRneg2) hQ'
    have hcomp := mul_le_mul_of_nonneg_left hNcompareQV
      (Real.sqrt_nonneg ((2 * (p : ℝ) - 1) * Cq))
    have hcomp' := mul_le_mul_of_nonneg_right hcomp hRneg2
    exact hroot.trans (by convert hcomp' using 1 <;> ring)
  have hnorm :
      MomentDuhamel.momNormW (P d) W p (Y v) ≤
        C * (N : ℝ) ^ (5 * lambda / 32) * R ^ (-(2 : ℝ)) := by
    have hsum := add_le_add (add_le_add hinitial hDriftSharp) hQVSqrt
    have hbound := hG.trans hsum
    dsimp [C]
    nlinarith [hbound]
  have hmomentBound :
      ∫ ω, W ω * |Y v ω| ^ (2 * p) ∂(Gauss.P d) ≤
        (C * (N : ℝ) ^ (5 * lambda / 32) * R ^ (-(2 : ℝ))) ^ (2 * p) :=
    APrimeOneStep.integral_le_of_momNormW_le hW0 hp hnorm
  have hIntegrable' :=
    (hYiN k hk Step2.sigPM a v ⟨hv.1, le_rfl⟩).2
  have hIntegrable :
      Integrable
        (fun ω =>
        APrimeSmoothWeightActual.weight d E D lambda s t (mesh D) 2 p N k
              (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
            |endpointCoordinate E D s t N k a ω| ^ (2 * p)) (Gauss.P d) := by
    simpa [W, endpointCoordinate, endpoint, v, mesh, hN, hk,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.flowY,
      APrimeGeneralMovingAllOrdersMinkowskiActual.coordinate,
      APrimeDuhamelModel.flowY,
      APrimeGeneralMovingSmoothDriftNormBudget.weight,
      APrimeSmoothWeightActual.weight] using hIntegrable'
  have hcoordMeas :
      AEStronglyMeasurable (endpointCoordinate E D s t N k a) (Gauss.P d) := by
    have hcoord := coordinate_contDiff E D N a hE (hs0 N) hv1 ⟨hv.1, le_rfl⟩
    have hcont : Continuous (endpointCoordinate E D s t N k a) := by
      change Continuous (fun ω => ‖
        APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v
          v
          (Gauss.Hflow d N v ω)‖)
      exact (hcoord.continuous.comp (Gauss.continuous_Hflow d N v)).norm
    exact hcont.measurable.aestronglyMeasurable
  refine ⟨hcoordMeas, hIntegrable, ?_⟩
  have hIntegrandEq :
      (fun ω => W ω * |Y v ω| ^ (2 * p)) =
        (fun ω =>
          APrimeSmoothWeightActual.weight d E D lambda s t (mesh D) 2 p N k
              (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
            |endpointCoordinate E D s t N k a ω| ^ (2 * p)) := by
    funext ω
    rfl
  rw [← hIntegrandEq]
  exact hmomentBound

/-- A positive-length Gaussian window simultaneously satisfies the incoming
`BoundsCore`, the sharp moment bound, and a positive actual weight on a
resident of the same common event at an active positive cell. -/
theorem quantitative_joint_positive_window_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∃ lambda : ℝ, 0 < lambda ∧
        lambda ≤ min (1 / 10000 : ℝ) (c / 10000) ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ N : ℕ in atTop,
            (∀ k : ℕ, k ≤ cutNetTop s t (mesh 60) N →
              SharpActualCoordinateMoment 0 60 lambda C s t 1 N k) ∧
            s N < t N ∧
            ∃ ω,
              ω ∈ APrimeGeneralMovingCommonSources.commonEvent
                0 60 s t
                  (APrimeFreeLossCoordinateBridge.sourceLoss lambda)
                  (APrimeFreeLossCoordinateBridge.sourceLoss lambda)
                  (APrimeFreeLossCoordinateBridge.sourceLoss lambda) N ∧
              1 ≤ cutNetTop s t (mesh 60) N ∧
              0 < APrimeSmoothWeightActual.weight d 0 60 lambda s t
                (mesh 60) 2 1 N 1
                (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
      hgeometry⟩ :=
    APrimeFreeLossCoordinateBridge.nondegenerate_gaussian_geometry_witness
  let lambda : ℝ := min (c / 20000) (1 / 20000)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min (by positivity) (by norm_num)
  have hlambdaC : lambda ≤ c / 10000 := by
    dsimp [lambda]
    have hmin : min (c / 20000) (1 / 20000) ≤ c / 20000 := min_le_left _ _
    nlinarith
  have hlambda1 : lambda ≤ 1 / 10000 := by
    dsimp [lambda]
    exact (min_le_right _ _).trans (by norm_num)
  have hsmall : lambda ≤ min (1 / 10000 : ℝ) (c / 10000) :=
    le_min hlambda1 hlambdaC
  obtain ⟨C, hC, hsharp⟩ :=
    eventually_sharp_actual_coordinate_moment
      (E := 0) (D := 60) (c := c) (lambda := lambda)
      (s := s) (t := t) (p := 1)
      (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
      hlambda hsmall (by omega)
  have hgeom := hgeometry lambda hlambda hsmall
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    lambda, hlambda, hsmall, C, hC, ?_⟩
  filter_upwards [hsharp, hgeom] with N hsharpN hgeomN
  rcases hgeomN with ⟨hlen, ω, hω, hk, _hplateau, hweight⟩
  exact ⟨hsharpN, hlen, ω, hω, hk, hweight⟩

#print axioms SharpActualCoordinateMoment
#print axioms eventually_sharp_actual_coordinate_moment
#print axioms quantitative_joint_positive_window_witness

end
end RBM.APrimeFreeLossSharpCoordinateRepair
