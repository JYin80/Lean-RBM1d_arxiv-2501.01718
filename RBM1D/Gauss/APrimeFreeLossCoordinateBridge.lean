/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingAllOrdersMinkowskiActual
import RBM1D.Gauss.APrimeGeneralMovingInitialActualSmoothSlot
import RBM1D.Gauss.APrimeGeneralMovingInitialFlow
import RBM1D.Gauss.APrimeGeneralMovingWeightedCoordinateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.APrimeFirstCellCrossOrderWeight
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeSlotArith

/-!
# T1323: conditional actual-coordinate endpoint moment bridge

At the corrected loss schedule, this file combines the accepted actual
closed-cell Minkowski inequality, actual-weight initial slot, and exact
weighted-coordinate integrability with explicit literal N1 and N2 slot
inputs. It produces the same actual-weight endpoint-coordinate moment needed
by the in-flight T1307 consumer. It proves neither slot input, a moving
`hfamily`, nor an A-prime conclusion.
-/

namespace RBM.APrimeFreeLossCoordinateBridge

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The endpoint used by the accepted closed-cell Minkowski producer. -/
noncomputable def endpoint (s t : ℕ → ℝ) (D : ℝ) (N k : ℕ) : ℝ :=
  APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k

/-- The literal `Step2.sigPM` normalized coordinate at the cell endpoint. -/
noncomputable def endpointCoordinate (E D : ℝ) (s : ℕ → ℝ)
    (t : ℕ → ℝ) (N k : ℕ) (a : LoopArg (d.L N) 2) (ω : Ω d) : ℝ :=
  ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N)
    (endpoint s t D N k)
    (endpoint s t D N k)
    (Gauss.Hflow d N (endpoint s t D N k) ω)‖

/-- Literal N1 input to `coordinate_integral_of_small_slots`, at actual loss
`loss`, fixed order `q`, and the moving endpoint of this module. -/
def LiteralN1Slot (E D loss : ℝ) (s t : ℕ → ℝ) (q N k : ℕ)
    (a : LoopArg (d.L N) 2) : Prop :=
  2 * (∫ u in (s N)..endpoint s t D N k,
      APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
          E D s t loss q N k a u +
        APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
          E D loss s t N k q a u) ≤
    APrimeOneStep.driftTerm (mE E).im ((N : ℝ) ^ (loss / 8))
      (Step2Moment.ratR E s N (endpoint s t D N k))
      (APrimeInit.slotXi' ((N : ℝ) ^ (loss / 8)))
      (APrimeSlotArith.slotA ((N : ℝ) ^ (loss / 8))
        (Step2Moment.ratR E s N (endpoint s t D N k)))
      (APrimeSlotArith.slotEps ((N : ℝ) ^ (loss / 8))
        (Step2Moment.ratR E s N (endpoint s t D N k)))
      (APrimeSlotArith.slotQ (Step2Moment.ratR E s N (endpoint s t D N k)))
      (APrimeSlotArith.slotBeta ((N : ℝ) ^ (loss / 8))
        (Step2Moment.ratR E s N (endpoint s t D N k)))
      (APrimeSlotArith.slotGamma ((N : ℝ) ^ (loss / 8))
        (Step2Moment.ratR E s N (endpoint s t D N k)))
      (APrimeSlotArith.slotJv ((N : ℝ) ^ (loss / 8))
        (Step2Moment.ratR E s N (endpoint s t D N k))) /
      (Step2Moment.ratR E s N (endpoint s t D N k)) ^ 4

/-- Literal N2 input to `coordinate_integral_of_small_slots`, at actual loss
`loss`, fixed order `q`, and the same moving endpoint. -/
def LiteralN2Slot (E D loss : ℝ) (s t : ℕ → ℝ) (q N k : ℕ)
    (a : LoopArg (d.L N) 2) : Prop :=
  Real.sqrt ((2 * (q : ℝ) - 1) *
    (∫ u in (s N)..endpoint s t D N k,
      APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
        E D s t loss q N k a u)) ≤
    APrimeOneStep.tailTerm ((N : ℝ) ^ (loss / 8))
      (Step2Moment.ratR E s N (endpoint s t D N k))
      (APrimeInit.slotKappa' ((N : ℝ) ^ (loss / 8))) /
      (Step2Moment.ratR E s N (endpoint s t D N k)) ^ 4

/-- The same output-coordinate moment contract as the next moving-family
consumer: measurability and weighted integrability are explicit, and the
bound keeps the actual smooth weight and the exact endpoint. -/
def SameActualCoordinateMoment (E D loss C₀ : ℝ) (s t : ℕ → ℝ)
    (q N k : ℕ) : Prop :=
  ∀ a : LoopArg (d.L N) 2,
    AEStronglyMeasurable (endpointCoordinate E D s t N k a) (Gauss.P d) ∧
    Integrable
      (fun ω =>
        APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
          |endpointCoordinate E D s t N k a ω| ^ (2 * q)) (Gauss.P d) ∧
    ∫ ω,
      APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
        (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
        |endpointCoordinate E D s t N k a ω| ^ (2 * q) ∂(Gauss.P d) ≤
      (C₀ * (N : ℝ) ^ (5 * loss / 32)) ^ (2 * q)

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

/-- Every fixed order `q ≥ 1` gets a same-actual-weight coordinate moment
bound at the corrected loss. One eventual cutoff works for all active cells,
including `k = 0`, and every output coordinate. The only analytic inputs not
already accepted are the literal N1 and N2 slot inequalities stated below. -/
theorem eventually_same_actual_coordinate_moment_of_literal_slots
    {E D c loss : ℝ} {s t : ℕ → ℝ} {q : ℕ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hloss : 0 < loss)
    (_hlossSmall : loss ≤ min (1 / 10000) (c / 10000))
    (hq : 1 ≤ q)
    (hN1 : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2, LiteralN1Slot E D loss s t q N k a)
    (hN2 : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2, LiteralN2Slot E D loss s t q N k a) :
    ∃ C₀ > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        k ≤ cutNetTop s t (mesh D) N →
        SameActualCoordinateMoment E D loss C₀ s t q N k := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hMink :=
    APrimeGeneralMovingAllOrdersMinkowskiActual.eventually_actual_closedCell_weightedMinkowski
      (E := E) (D := D) (c := c) (deltaWeight := loss) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hloss.le q hq
  have hinit :=
    APrimeGeneralMovingInitialActualSmoothSlot.eventually_actual_smooth_initial_hinit
      (E := E) (D := D) (c := c) (δ := loss) (δWeight := loss)
      (s := s) (t := t) hE hD hs0 hst ht1 hc hreg hB hloss q hq
  have hYi :=
    APrimeGeneralMovingWeightedCoordinateIntegrable.eventually_actual_weighted_flowY_integrable
      (E := E) (D := D) (deltaWeight := loss) (s := s) (t := t)
      hE hs0 hst ht1 q hq
  let C₀ : ℝ := Step2MomentStep.cStep' (mE E).im + 1
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    linarith [Step2MomentStep.cStep'_pos hm]
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hMink, hinit, hYi, hN1, hN2,
    Filter.eventually_ge_atTop 2] with N hMinkN hinitN hYiN hN1N hN2N hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hx : 1 ≤ (N : ℝ) ^ (loss / 8) :=
    Real.one_le_rpow hNreal (by linarith)
  intro k hk a
  let v : ℝ := endpoint s t D N k
  let R : ℝ := Step2Moment.ratR E s N v
  let x : ℝ := (N : ℝ) ^ (loss / 8)
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, endpoint, APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint, mesh]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hv.1 hv1
  let W : Ω d → ℝ :=
    APrimeGeneralMovingAllOrdersMinkowskiActual.weight E D s t loss q N k
  let Y : ℝ → Ω d → ℝ := fun r =>
    APrimeGeneralMovingAllOrdersMinkowskiActual.flowY E D N a (s N) v r
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t loss q N k ω
  have hMinkAt := hMinkN k hk a
  have hG :
      MomentDuhamel.momNormW (P d) W q (Y v) ≤
        MomentDuhamel.momNormW (P d) W q (Y (s N)) +
          2 * (∫ r in (s N)..v,
            APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
                E D s t loss q N k a r +
              APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
                E D loss s t N k q a r) +
          Real.sqrt ((2 * (q : ℝ) - 1) *
            ∫ r in (s N)..v,
              APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
                E D s t loss q N k a r) := by
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
  have hN1At := hN1N k hk a
  have hN1' :
      2 * (∫ u in (s N)..v,
          APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
              E D s t loss q N k a u +
            APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
              E D loss s t N k q a u) ≤
        APrimeOneStep.driftTerm (mE E).im x R
          (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    simpa [LiteralN1Slot, endpoint, APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      v, R, x, mesh] using hN1At
  have hN2At := hN2N k hk a
  have hN2' :
      Real.sqrt ((2 * (q : ℝ) - 1) *
        ∫ u in (s N)..v,
          APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm E D s t loss q N k a u) ≤
        APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ 4 := by
    simpa [LiteralN2Slot, endpoint, APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      v, R, x, mesh] using hN2At
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
      MomentDuhamel.momNormW (P d) W q (Y (s N)) ≤
        APrimeOneStep.initTerm x R (APrimeInit.slotXi' x) / R ^ 4 := by
    rw [hleft]
    simpa [W, x, R, v, endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.weight,
      APrimeGeneralMovingSmoothDriftNormBudget.weight,
      Step2Moment.ratR, mesh] using hinitAt
  have hslot := APrimeInit.coordinate_integral_of_small_slots
    (P := Gauss.P d) (hm) (x := x) (R := R) hx hR
    (a := s N) (b := v) (p := q) hq (W := W) (Y := Y)
    (Adr := APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm E D s t loss q N k a)
    (Bcr := APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget E D loss s t N k q a)
    (g := APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm E D s t loss q N k a)
    hW0 hG hinit' hN1' hN2'
  have hxpower : x ^ (5 / 4 : ℝ) = (N : ℝ) ^ (5 * loss / 32) := by
    dsimp [x]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    congr 1
    ring
  have hmomentBound :
      ∫ ω, W ω * |Y v ω| ^ (2 * q) ∂(Gauss.P d) ≤
        (C₀ * (N : ℝ) ^ (5 * loss / 32)) ^ (2 * q) := by
    have hpow := hslot
    rw [show Step2MomentStep.cStep' (mE E).im + 1 = C₀ by rfl] at hpow
    rw [hxpower] at hpow
    exact hpow
  have hIntegrable' :=
    (hYiN k hk Step2.sigPM a v ⟨hv.1, le_rfl⟩).2
  have hIntegrable :
      Integrable
        (fun ω =>
        APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
              (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
            |endpointCoordinate E D s t N k a ω| ^ (2 * q)) (Gauss.P d) := by
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
      (fun ω => W ω * |Y v ω| ^ (2 * q)) =
        (fun ω =>
          APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
              (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
            |endpointCoordinate E D s t N k a ω| ^ (2 * q)) := by
    funext ω
    rfl
  rw [← hIntegrandEq]
  exact hmomentBound

/-! ## Corrected-loss geometry witness -/

noncomputable def sourceLoss (loss : ℝ) : ℝ := loss / 1000

/-- The corrected source loss has the room required by the accepted
same-loss schedule. -/
theorem corrected_loss_schedule {loss c : ℝ} (hloss : 0 < loss)
    (hsmall : loss ≤ min (1 / 10000) (c / 10000)) :
    0 < sourceLoss loss ∧ sourceLoss loss ≤ loss / 16 ∧
      sourceLoss loss ≤ (2 * loss) / 16 ∧ 2 * loss ≤ c / 20 ∧
      sourceLoss loss + 2 * (2 * loss) + (2 : ℝ) / 15 < 1 := by
  have hloss1 : loss ≤ 1 / 10000 := hsmall.trans (min_le_left _ _)
  have hlossc : loss ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [sourceLoss]; positivity
  · dsimp [sourceLoss]; nlinarith
  · dsimp [sourceLoss]; nlinarith
  · nlinarith
  · dsimp [sourceLoss]; nlinarith

/-- A positive-length `E = 0`, `D = 60` Gaussian window has a nonempty
common event and a same-sample first-cell resident where the widened weight
is one and the actual weight at the corrected loss is positive. This witnesses
the nondegenerate event/weight geometry; the conditional N1/N2 slot inputs
remain separate hypotheses of the main theorem. -/
theorem nondegenerate_gaussian_geometry_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧ Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ loss : ℝ, 0 < loss → loss ≤ min (1 / 10000) (c / 10000) →
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧ ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (sourceLoss loss) (sourceLoss loss) (sourceLoss loss) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (mesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u ω)
              s t (mesh 60) loss 1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 loss s t
              (mesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hcommon⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro loss hloss hsmall
  have hsource := corrected_loss_schedule hloss hsmall
  have hsrc : 0 < sourceLoss loss := hsource.1
  have hcommon' := hcommon (sourceLoss loss) (sourceLoss loss)
    (sourceLoss loss) loss hsrc hsrc hsrc hloss
  filter_upwards [hcommon'] with N hN
  obtain ⟨hwindow, ω, hω, hk, hplateau⟩ := hN
  have hplateau1 :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (mesh 60)) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
        s t (mesh 60) loss 1 N 1 ω = 1 := by
    simpa [APrimeGeneralMovingDetFields.J] using hplateau 1
  have hcross :=
    APrimeFirstCellCrossOrderWeight.widenedW_le_actualWeight_cross_order
      (d := d) (E := 0) (D := 60) (δ := loss) (s := s) (t := t)
      (mesh := mesh 60) (by norm_num) hloss.le N 1 1 1 ω (hst N) (ht1 N)
      (APrimeGeneralMovingMesh.targetMesh_pos 60 N) (by norm_num) (by norm_num)
  have hweight :
      0 < APrimeSmoothWeightActual.weight d 0 60 loss s t
        (mesh 60) 2 1 N 1
        (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
    rw [hplateau1] at hcross
    exact lt_of_lt_of_le (by norm_num) hcross
  exact ⟨hwindow, ω, hω, hk, hplateau1, hweight⟩

#print axioms corrected_loss_schedule
#print axioms eventually_same_actual_coordinate_moment_of_literal_slots
#print axioms nondegenerate_gaussian_geometry_witness

end
end RBM.APrimeFreeLossCoordinateBridge
