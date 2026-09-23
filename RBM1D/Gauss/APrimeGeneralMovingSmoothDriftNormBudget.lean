/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftGlobalPoly
import RBM1D.Gauss.APrimeSmoothToWidenedSupport
import RBM1D.Gauss.APrimeFirstCellDriftNormSplit

/-!
# T615: actual-smooth general-moving drift integral budget

This file combines the same-event pointwise drift profile of T598, the
buffered actual-smooth-to-widened support bridge of T599, and T611's
all-sample polynomial envelope.  The near, far, residual, and quadratic
rows are kept literally.  In particular the quadratic row is capped from
the actual `Step2.jS`, rather than from the unrelated block cap.
-/

namespace RBM.APrimeGeneralMovingSmoothDriftNormBudget

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The endpoint of the target general-moving cut net. -/
noncomputable def endpoint (s _t : Nat -> Real) (D : Real) (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

/-- The buffer exponent used by the widened support and all favorable caps. -/
noncomputable def deltaCap (deltaWeight xi : Real) : Real :=
  deltaWeight + xi

/-- The literal differentiable actual smooth weight. -/
noncomputable def weight (E D : Real) (s t : Nat -> Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d -> Real :=
  APrimeSmoothWeightActual.weight d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

/-- The actual normalized drift at a target-net endpoint. -/
noncomputable def drift (E D : Real) (s t : Nat -> Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Ω d -> Real :=
  APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a (s N)
    (endpoint s t D N k) u

/-- The actual-smooth weighted `L^(2p)` norm of the drift. -/
noncomputable def g (E D : Real) (s t : Nat -> Real)
    (deltaWeight : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Real :=
  MomentDuhamel.momNormW (P d) (weight E D s t deltaWeight p N k) p
    (drift E D s t N k a u)

/-- The exact Step2 running cap, at the buffered exponent. -/
noncomputable def jSCap (E : Real) (s : Nat -> Real)
    (deltaCap : Real) (N : Nat) (u : Real) : Real :=
  (4 * Real.exp 1 + 2) * (N : Real) ^ (2 * deltaCap) *
    (Step2Moment.ratR E s N u) ^ 4

/-- The literal (5.34) row after capping the actual `Step2.jS`. -/
noncomputable def quadCap (E D : Real) (s : Nat -> Real)
    (deltaCap : Real) (N : Nat) (u : Real) : Real :=
  Real.exp 1 * (jSCap E s deltaCap N u) ^ 2 *
    (36 * ((etaT E u)⁻¹ *
      (((d.W N : Real) * B.ell N u * etaT E u)⁻¹)) +
      (d.W N : Real) * (d.L N : Real) * (d.W N : Real) ^ (-D))

/-- T598's full unsimplified profile, with only the actual Step2 row capped. -/
noncomputable def profile (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG deltaCap : Real) (N : Nat)
    (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    (Step2Moment.ratR E s N u) ^ (-2 : Real) *
    (Step2Moment.ratR E s N v) ^ (-2 : Real) *
    (APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
        E D s zetaSrc zetaCtr tauG deltaCap N u +
      APrimeGeneralMovingDriftAtProfile.farSourceCoeff
        E D s t zetaCtr tauG deltaCap N u +
      quadCap E D s deltaCap N u)

theorem measurable_weight
    {E D : Real} {s t : Nat -> Real} {deltaWeight : Real}
    {p N k : Nat} (hE : |E| < 2)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hN : 0 < N)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    Measurable (weight E D s t deltaWeight p N k) := by
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let m := APrimeSmoothWeightActual.canonicalM d s t mesh N
  have hkmesh : k <= cutNetTop s t mesh N := by simpa [mesh] using hk
  have hm : 1 <= m :=
    APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu : ∀ j < k, cutNetPt s mesh N j < 1 := by
    intro j hj
    have hjtop : j <= cutNetTop s t mesh N := hj.le.trans hkmesh
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht1 N)
  have hwC1 := APrimeSmoothWeightActual.weightC1 d
    (E := E) (D := D) (δ := deltaWeight) (s := s) (t := t)
    (mesh := mesh) (N₀ := 2) (p := p) (N := N) (k := k) (m := m)
    hE hs1 hN hm hu
  simpa only [weight, mesh, m] using hwC1.cont.measurable

theorem weight_nonneg (E D : Real) (s t : Nat -> Real)
    (deltaWeight : Real) (p N k : Nat) (omega : Ω d) :
    0 <= weight E D s t deltaWeight p N k omega := by
  unfold weight
  exact APrimeSmoothWeightActual.weight_nonneg d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k _ omega

theorem weight_le_one (E D : Real) (s t : Nat -> Real)
    (deltaWeight : Real) (p N k : Nat) (omega : Ω d) :
    weight E D s t deltaWeight p N k omega <= 1 := by
  unfold weight
  exact APrimeSmoothWeightActual.weight_le_one d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k _ omega

theorem intervalIntegrable_g
    {E D : Real} {s t : Nat -> Real} {deltaWeight : Real}
    {p N k : Nat} (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hN : 0 < N)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable (g E D s t deltaWeight p N k a) volume
      (s N) (endpoint s t D N k) := by
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  exact APrimeDriftTimeFamily.intervalIntegrable_momNormW_driftAt
    d E D N Step2.sigPM a hE (hs0 N) hv.1 (hv.2.trans_lt (ht1 N))
    (weight E D s t deltaWeight p N k)
    (measurable_weight hE hst ht1 hN hk)
    (weight_nonneg E D s t deltaWeight p N k)
    (weight_le_one E D s t deltaWeight p N k) p

private theorem profile_nonneg
    {E D : Real} {s t : Nat -> Real}
    {zetaSrc zetaCtr tauG delta : Real} {N : Nat} {v u : Real}
    (hE : |E| < 2) (hs0 : 0 <= s N) (hst : s N <= t N)
    (ht1 : t N < 1) (hu : u ∈ Icc (s N) v) (hv : v <= t N) :
    0 <= profile E D s t zetaSrc zetaCtr tauG delta N v u := by
  have hu0 : 0 <= u := hs0.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (hv.trans_lt ht1)
  have hs1 : s N < 1 := hst.trans_lt ht1
  have hv1 : v < 1 := hv.trans_lt ht1
  have hetaU : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hellS : 0 < B.ell N (s N) := by
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1)
  have hellU : 1 <= B.ell N u :=
    one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hellU0 : 0 < B.ell N u := zero_lt_one.trans_le hellU
  have hW0 : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
  have hW1 : 1 <= (d.W N : Real) := by exact_mod_cast B.one_le_W N
  have hJbar : 0 <=
      APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u := by
    unfold APrimeGeneralMovingDriftSource.blockCap
    positivity
  have hNear : 0 <= APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
      E D s zetaSrc zetaCtr tauG delta N u := by
    unfold APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
    dsimp only
    have hcNear : 0 <= Lemma57.cNear (d.W N : Real) (B.ell N u) :=
      Lemma57.cNear_nonneg hW1 hellU0
    have hTail : 0 <= tailT (d.W N : Real) (B.ell N u) (etaT E u) D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)) :=
      tailT_nonneg hW0.le _
    positivity
  have hFar : 0 <= APrimeGeneralMovingDriftAtProfile.farSourceCoeff
      E D s t zetaCtr tauG delta N u := by
    unfold APrimeGeneralMovingDriftAtProfile.farSourceCoeff
    dsimp only
    have hcFar : 0 <= Lemma57.cFar (d.W N : Real) (B.ell N u) :=
      Lemma57.cFar_nonneg hW1 hellU0
    have hFlow : 0 <= flowDelta d E t N := by
      unfold flowDelta
      exact Real.rpow_nonneg
        (inv_nonneg.mpr (B.scale_pos' hE N (hs0.trans hst) ht1).le) _
    positivity
  have hQuad : 0 <= quadCap E D s delta N u := by
    unfold quadCap jSCap
    positivity
  unfold profile
  exact mul_nonneg (mul_nonneg (mul_nonneg (Step2.xiK_nonneg _ _ _)
    (Real.rpow_nonneg (Step2Moment.ratR_pos hE hs1 hu1).le _))
    (Real.rpow_nonneg (Step2Moment.ratR_pos hE hs1 hv1).le _))
    (by positivity)

private theorem continuousOn_profile
    {E D : Real} {s t : Nat -> Real}
    {zetaSrc zetaCtr tauG delta : Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 <= s N) (hv : s N <= v)
    (hv1 : v < 1) :
    ContinuousOn (profile E D s t zetaSrc zetaCtr tauG delta N v)
      (Icc (s N) v) := by
  let I : Set Real := Icc (s N) v
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    unfold etaT
    fun_prop
  have hEllPos : ∀ u, u ∈ I -> 0 < B.ell N u := by
    intro u hu
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0.trans hu.1)
        (hu.2.trans_lt hv1))
  have hEtaPos : ∀ u, u ∈ I -> 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hInvEll : ContinuousOn (fun u => (B.ell N u)⁻¹) I :=
    hEll.inv₀ (fun u hu => (hEllPos u hu).ne')
  have hInvEta : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hRu : ContinuousOn (fun u => B.ell N u / B.ell N (s N)) I :=
    hEll.div_const _
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    unfold Step2Moment.ratR
    exact ContinuousOn.div continuousOn_const hEta
      (fun u hu => (hEtaPos u hu).ne')
  have hRatPos : ∀ u, u ∈ I -> 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE (hv.trans_lt hv1) (hu.2.trans_lt hv1)
  have hJbar : ContinuousOn (fun u =>
      APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u) I := by
    unfold APrimeGeneralMovingDriftSource.blockCap
    have hmain : ContinuousOn (fun u =>
        (4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
          Step2Moment.ratR E s N u ^ 4) I :=
      continuousOn_const.mul (hRat.pow 4)
    have hinside : ContinuousOn (fun u =>
        9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
            Step2Moment.ratR E s N u ^ 4) + 2) I :=
      (continuousOn_const.mul hmain).add continuousOn_const
    exact continuousOn_const.add (continuousOn_const.mul hinside)
  have hCNear : ContinuousOn (fun u =>
      Lemma57.cNear (d.W N : Real) (B.ell N u)) I := by
    unfold Lemma57.cNear
    exact (continuousOn_const.add (continuousOn_const.mul hInvEll)).mul
      continuousOn_const
  have hCFar : ContinuousOn (fun u =>
      Lemma57.cFar (d.W N : Real) (B.ell N u)) I := by
    unfold Lemma57.cFar
    exact (continuousOn_const.add (continuousOn_const.mul hInvEll)).mul
      continuousOn_const
  have hGap : ContinuousOn (fun u =>
      APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)) I := by
    unfold APrimeDriftNearAbsorb.gap Lemma57.ellStarStar ellStar
    fun_prop
  have hTail : ContinuousOn (fun u =>
      tailT (d.W N : Real) (B.ell N u) (etaT E u) D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) I := by
    unfold tailT
    refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) continuousOn_const
    · refine ContinuousOn.inv₀ (ContinuousOn.pow
        ((continuousOn_const.mul hEll).mul hEta) 2) ?_
      intro u hu
      have hW : (0 : Real) < d.W N := by exact_mod_cast d.W_pos N
      exact (pow_pos (mul_pos (mul_pos hW (hEllPos u hu)) (hEtaPos u hu)) 2).ne'
    · exact ContinuousOn.rexp (ContinuousOn.neg
        (ContinuousOn.sqrt (ContinuousOn.div hGap hEll
          (fun u hu => (hEllPos u hu).ne'))))
  have hNear : ContinuousOn (fun u =>
      APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
        E D s zetaSrc zetaCtr tauG delta N u) I := by
    unfold APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
    dsimp only
    have hTerm1 : ContinuousOn (fun u =>
        4 * (N : Real) ^ (zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
          (B.ell N u / B.ell N (s N)) ^ 3 *
          Lemma57.cNear (d.W N : Real) (B.ell N u)) I :=
      (((continuousOn_const.mul hInvEta).mul (hRu.pow 3)).mul hCNear)
    have hDen : ContinuousOn (fun u =>
        B.ell N u * etaT E u *
          (B.ell N u / B.ell N (s N)) ^ 2) I :=
      (hEll.mul hEta).mul (hRu.pow 2)
    have hFrac : ContinuousOn (fun u =>
        ((d.L N : Real) *
          APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u) /
            (B.ell N u * etaT E u *
              (B.ell N u / B.ell N (s N)) ^ 2)) I :=
      ContinuousOn.div (continuousOn_const.mul hJbar) hDen
        (fun u hu => by
          exact (mul_pos (mul_pos (hEllPos u hu) (hEtaPos u hu))
            (pow_pos (div_pos (hEllPos u hu)
              (hEllPos (s N) ⟨le_rfl, hv⟩)) 2)).ne')
    have hScaleSq : ContinuousOn (fun u =>
        ((d.W N : Real) * B.ell N u * etaT E u) ^ 2 *
          Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real))) I :=
      (((continuousOn_const.mul hEll).mul hEta).pow 2).mul continuousOn_const
    have hTerm2 : ContinuousOn (fun u =>
        (4 * (N : Real) ^ zetaCtr *
            (((d.L N : Real) *
              APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u) /
              (B.ell N u * etaT E u *
                (B.ell N u / B.ell N (s N)) ^ 2)) *
            (((d.W N : Real) * B.ell N u * etaT E u) ^ 2 *
              Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real))) *
            tailT (d.W N : Real) (B.ell N u) (etaT E u) D
              (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) *
          ((etaT E u)⁻¹ * (B.ell N u / B.ell N (s N)) ^ 3)) I :=
      ((((continuousOn_const.mul hFrac).mul hScaleSq).mul hTail).mul
        (hInvEta.mul (hRu.pow 3)))
    exact hTerm1.add hTerm2
  have hFar : ContinuousOn (fun u =>
      APrimeGeneralMovingDriftAtProfile.farSourceCoeff
        E D s t zetaCtr tauG delta N u) I := by
    unfold APrimeGeneralMovingDriftAtProfile.farSourceCoeff
    dsimp only
    have hScaleInv : ContinuousOn (fun u =>
        ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) I :=
      ContinuousOn.inv₀ ((continuousOn_const.mul hEll).mul hEta)
        (fun u hu => by
          have hW : (0 : Real) < d.W N := by exact_mod_cast d.W_pos N
          exact (mul_pos (mul_pos hW (hEllPos u hu)) (hEtaPos u hu)).ne')
    exact (hInvEta.mul (continuousOn_const.mul hRu)).mul
      (((hCFar.mul hJbar).mul continuousOn_const).add
        ((hJbar.mul (hJbar.sqrt)).mul
          ((continuousOn_const.mul hScaleInv).add
            (continuousOn_const.mul hInvEll))))
  have hJSCap : ContinuousOn (fun u => jSCap E s delta N u) I := by
    unfold jSCap
    exact (continuousOn_const.mul (hRat.pow 4))
  have hScaleInv : ContinuousOn (fun u =>
      ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) I :=
    ContinuousOn.inv₀ ((continuousOn_const.mul hEll).mul hEta)
      (fun u hu => by
        have hW : (0 : Real) < d.W N := by exact_mod_cast d.W_pos N
        exact (mul_pos (mul_pos hW (hEllPos u hu)) (hEtaPos u hu)).ne')
  have hQuad : ContinuousOn (fun u => quadCap E D s delta N u) I := by
    unfold quadCap
    have hfirst : ContinuousOn (fun u =>
        36 * ((etaT E u)⁻¹ *
          (((d.W N : Real) * B.ell N u * etaT E u)⁻¹))) I :=
      continuousOn_const.mul (hInvEta.mul hScaleInv)
    have hsecond : ContinuousOn (fun _u : Real =>
        (d.W N : Real) * (d.L N : Real) * (d.W N : Real) ^ (-D)) I :=
      continuousOn_const
    have hbracket := hfirst.add hsecond
    exact (continuousOn_const.mul (hJSCap.pow 2)).mul hbracket
  have hRatNeg : ContinuousOn (fun u =>
      (Step2Moment.ratR E s N u) ^ (-2 : Real)) I :=
    hRat.rpow_const (fun u hu => Or.inl (hRatPos u hu).ne')
  unfold profile
  exact ((continuousOn_const.mul hRatNeg).mul continuousOn_const).mul
    ((hNear.add hFar).add hQuad)

theorem intervalIntegrable_profile
    {E D : Real} {s t : Nat -> Real}
    {zetaSrc zetaCtr tauG delta : Real} {N k : Nat}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    IntervalIntegrable
      (profile E D s t zetaSrc zetaCtr tauG delta N
        (endpoint s t D N k)) volume (s N) (endpoint s t D N k) := by
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  exact (continuousOn_profile hE (hs0 N) hv.1 (hv.2.trans_lt (ht1 N))).intervalIntegrable_of_Icc hv.1

private theorem integrable_weighted_drift_pow
    {E D : Real} {s t : Nat -> Real} {deltaWeight : Real}
    {p N k : Nat} (hE : |E| < 2) (hs0 : 0 <= s N)
    (hsv : s N <= endpoint s t D N k)
    (hv1 : endpoint s t D N k < 1)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k))
    (henv : ∀ omega : Ω d,
      |drift E D s t N k a u omega| <= (N : Real) ^ (D + 8))
    (hw : Measurable (weight E D s t deltaWeight p N k)) :
    Integrable (fun omega => weight E D s t deltaWeight p N k omega *
      |drift E D s t N k a u omega| ^ (2 * p)) (P d) := by
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d E D N a
      (s N) (endpoint s t D N k) :=
    APrimeDriftTimeFamily.driftScale_pos d hE hsv hv1 N a
  have hdrift : Measurable (drift E D s t N k a u) := by
    have hf := (Gauss.continuous_uker_driftF_omega d E N
      (Gauss.window_im_ne_zero hE hv1 u hu)
      (Gauss.window_norm_mul_lt hE.le hs0 hv1 u hu)
      Step2.sigPM a (((endpoint s t D N k : Real) : Complex))).norm.div_const
        (APrimeDriftTimeFamily.driftScale d E D N a
          (s N) (endpoint s t D N k))
    unfold drift APrimeDriftTimeFamily.driftAt
    exact hf.measurable
  have hmeas : Measurable (fun omega =>
      weight E D s t deltaWeight p N k omega *
        |drift E D s t N k a u omega| ^ (2 * p)) :=
    hw.mul ((continuous_abs.measurable.comp hdrift).pow_const (2 * p))
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (((N : Real) ^ (D + 8)) ^ (2 * p))
  exact Filter.Eventually.of_forall fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (weight_nonneg E D s t deltaWeight p N k omega)
      (pow_nonneg (abs_nonneg _) _))]
    calc
      weight E D s t deltaWeight p N k omega *
          |drift E D s t N k a u omega| ^ (2 * p) <=
          1 * |drift E D s t N k a u omega| ^ (2 * p) :=
        mul_le_mul_of_nonneg_right
          (weight_le_one E D s t deltaWeight p N k omega)
          (pow_nonneg (abs_nonneg _) _)
      _ <= ((N : Real) ^ (D + 8)) ^ (2 * p) := by
        simpa only [one_mul] using
          pow_le_pow_left₀ (abs_nonneg _) (henv omega) (2 * p)

/-- Positive-cell pointwise actual-smooth drift norm bound by the exact
buffered profile plus the paid common-event complement. -/
theorem eventually_g_le_profile_add
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdeltaWeight : 0 < deltaWeight)
    (hxi : 0 < xi)
    (p : Nat) (hp : 1 <= p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat, 1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ u, u ∈ Icc (s N) (endpoint s t D N k) ->
      ∀ a : LoopArg (d.L N) 2,
        g E D s t deltaWeight p N k a u <=
          profile E D s t zetaSrc zetaCtr tauG
            (deltaCap deltaWeight xi) N (endpoint s t D N k) u +
          (N : Real) ^ (-beta) := by
  have hDeltaCap : 0 < deltaCap deltaWeight xi := by
    unfold deltaCap
    linarith
  have hHP := APrimeGeneralMovingCommonSources.highProb_commonEvent
    hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG
      hzetaSrc hzetaCtr htauG
  have hpay := Gauss.eventually_env_mul_prob_rpow_le (P := P d)
    (q := 2 * p) (by omega) hHP (Env := fun N => (N : Real) ^ (D + 8))
    (Cenv := D + 8) (by linarith)
    (Filter.Eventually.of_forall fun _ => le_rfl) hbeta
  have hprofile := APrimeGeneralMovingDriftAtProfile.eventually_driftAt_le_profile
    hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hDeltaCap p hp
  have hcap := APrimeGeneralMovingCommonSources.eventually_block_cap_on_widened_support
    hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hDeltaCap p hp
  have hsupport :=
    APrimeSmoothToWidenedSupport.eventually_actualWeight_pos_implies_widenedW_pos
      d (D := D) (delta := deltaWeight) (xi := xi) hE hst ht1
        (APrimeGeneralMovingMesh.targetMesh_pos D) hxi p hp
  have henv := APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [hpay, hprofile, hcap, hsupport, henv,
    eventually_ge_atTop 2] with N hpayN hprofileN hcapN hsupportN henvN hN2
  intro k hk1 hk u hu a
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hwmeas := measurable_weight (deltaWeight := deltaWeight) (p := p)
    hE hst ht1 (by omega) hk
  have hZi := integrable_weighted_drift_pow (deltaWeight := deltaWeight)
    hE (hs0 N) hv.1 (hv.2.trans_lt (ht1 N)) a hu
    (henvN k hk u hu a) hwmeas
  have hgood : ∀ omega ∈ APrimeGeneralMovingCommonSources.commonEvent
      E D s t zetaSrc zetaCtr tauG N,
      weight E D s t deltaWeight p N k omega *
          |drift E D s t N k a u omega| <=
        weight E D s t deltaWeight p N k omega *
          profile E D s t zetaSrc zetaCtr tauG
            (deltaCap deltaWeight xi) N (endpoint s t D N k) u := by
    intro omega homega
    by_cases hw0 : weight E D s t deltaWeight p N k omega = 0
    · simp [hw0]
    · have hwpos : 0 < weight E D s t deltaWeight p N k omega :=
        lt_of_le_of_ne (weight_nonneg E D s t deltaWeight p N k omega)
          (Ne.symm hw0)
      have hwide := hsupportN k hk omega (by simpa [weight] using hwpos)
      have hdrift := hprofileN k hk1 hk omega homega hwide u hu a
      have hJ := (hcapN k hk1 hk omega homega hwide u hu).1
      have hJ0 : 0 <= Step2.jS (sample d) E D N u omega := by
        have hW0 : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
        exact (Step2.one_le_jStar hW0 (fun b => norm_nonneg _)).trans' (by norm_num)
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      have hu1 : u < 1 := hu.2.trans_lt (hv.2.trans_lt (ht1 N))
      have hRatPos : 0 < Step2Moment.ratR E s N u :=
        Step2Moment.ratR_pos hE hs1 hu1
      have hJnorm :
          Step2.jS (sample d) E D N u omega /
              Step2Moment.ratR E s N u ^ 4 <=
            (4 * Real.exp 1 + 2) *
              (N : Real) ^ (2 * deltaCap deltaWeight xi) := by
        simpa [APrimeGeneralMovingDetFields.J, Step2Moment.jSnorm] using hJ
      have hJcap : Step2.jS (sample d) E D N u omega <=
          jSCap E s (deltaCap deltaWeight xi) N u := by
        unfold jSCap
        exact (div_le_iff₀ (pow_pos hRatPos 4)).mp hJnorm
      have hquad : APrimeGeneralMovingDriftAtProfile.quadCoeff
          E D N u omega <= quadCap E D s (deltaCap deltaWeight xi) N u := by
        have heta : 0 <= etaT E u := (Step2.etaT_pos' hE hu1).le
        have hell : 0 <= B.ell N u := by
          exact (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
            (B.one_le_L N) ((hs0 N).trans hu.1) hu1)).le
        have hbracket : 0 <=
            36 * ((etaT E u)⁻¹ *
              (((d.W N : Real) * B.ell N u * etaT E u)⁻¹)) +
              (d.W N : Real) * (d.L N : Real) * (d.W N : Real) ^ (-D) := by
          positivity
        unfold APrimeGeneralMovingDriftAtProfile.quadCoeff quadCap
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hJ0 hJcap 2) (Real.exp_pos 1).le)
          hbracket
      have hdrift0 : 0 <= drift E D s t N k a u omega := by
        unfold drift APrimeDriftTimeFamily.driftAt
        exact div_nonneg (norm_nonneg _)
          (APrimeDriftTimeFamily.driftScale_pos d hE hv.1
            (hv.2.trans_lt (ht1 N)) N a).le
      rw [abs_of_nonneg hdrift0]
      apply mul_le_mul_of_nonneg_left _
        (weight_nonneg E D s t deltaWeight p N k omega)
      calc
        drift E D s t N k a u omega <=
            Step2.xiK (d.L N) (d.W N) (mE E).im *
              (Step2Moment.ratR E s N u) ^ (-2 : Real) *
              (Step2Moment.ratR E s N (endpoint s t D N k)) ^ (-2 : Real) *
              (APrimeGeneralMovingDriftAtProfile.nearSourceCoeff E D s
                  zetaSrc zetaCtr tauG (deltaCap deltaWeight xi) N u +
                APrimeGeneralMovingDriftAtProfile.farSourceCoeff E D s t
                  zetaCtr tauG (deltaCap deltaWeight xi) N u +
                APrimeGeneralMovingDriftAtProfile.quadCoeff E D N u omega) := by
          simpa [drift, endpoint] using hdrift
        _ <= profile E D s t zetaSrc zetaCtr tauG
              (deltaCap deltaWeight xi) N (endpoint s t D N k) u := by
          unfold profile
          have hfac : 0 <= Step2.xiK (d.L N) (d.W N) (mE E).im *
              (Step2Moment.ratR E s N u) ^ (-2 : Real) *
              (Step2Moment.ratR E s N (endpoint s t D N k)) ^ (-2 : Real) := by
            exact mul_nonneg (mul_nonneg (Step2.xiK_nonneg _ _ _)
              (Real.rpow_nonneg hRatPos.le _))
              (Real.rpow_nonneg
                (Step2Moment.ratR_pos hE hs1
                  (hv.2.trans_lt (ht1 N))).le _)
          have hsum := add_le_add_right hquad
            (APrimeGeneralMovingDriftAtProfile.nearSourceCoeff E D s
              zetaSrc zetaCtr tauG (deltaCap deltaWeight xi) N u +
             APrimeGeneralMovingDriftAtProfile.farSourceCoeff E D s t
              zetaCtr tauG (deltaCap deltaWeight xi) N u)
          exact mul_le_mul_of_nonneg_left hsum hfac
  have hsplit := APrimeFirstCellDriftNormSplit.drift_norm_le_of_weighted_event
    (P0 := P d) hp
    (weight_nonneg E D s t deltaWeight p N k)
    (weight_le_one E D s t deltaWeight p N k) hZi
    (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      E D s t zetaSrc zetaCtr tauG N)
    (profile_nonneg hE (hs0 N) (hst N) (ht1 N) hu hv.2)
    (Real.rpow_nonneg (by positivity : (0 : Real) <= N) (D + 8))
    ENNReal.toReal_nonneg hgood (henvN k hk u hu a)
    (le_rfl : ((P d) (APrimeGeneralMovingCommonSources.commonEvent
      E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal <= _)
  change g E D s t deltaWeight p N k a u <= _
  calc
    g E D s t deltaWeight p N k a u <=
        profile E D s t zetaSrc zetaCtr tauG
            (deltaCap deltaWeight xi) N (endpoint s t D N k) u +
          (N : Real) ^ (D + 8) *
            (((P d) (APrimeGeneralMovingCommonSources.commonEvent
              E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal) ^
                ((1 : Real) / (2 * p)) := by
      simpa [g, drift, one_div, Nat.cast_mul] using hsplit
    _ <= profile E D s t zetaSrc zetaCtr tauG
            (deltaCap deltaWeight xi) N (endpoint s t D N k) u +
          (N : Real) ^ (-beta) := by
      have hpayN' : (N : Real) ^ (D + 8) *
          (((P d) (APrimeGeneralMovingCommonSources.commonEvent
            E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal) ^
              ((1 : Real) / (2 * (p : Real))) <=
            (N : Real) ^ (-beta) := by
        simpa [Nat.cast_mul] using hpayN
      exact add_le_add le_rfl hpayN'

/-- The all-cell actual-smooth drift integral budget.  The initial cell is
handled only by `cutNetPt_zero` and `integral_same`; no pointwise vanishing
of the moving-start drift is asserted. -/
theorem eventually_actual_smooth_drift_integral_le_exact_profile
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdeltaWeight : 0 < deltaWeight)
    (hxi : 0 < xi)
    (p : Nat) (hp : 1 <= p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable (g E D s t deltaWeight p N k a) volume
            (s N) (endpoint s t D N k) /\
        IntervalIntegrable
          (profile E D s t zetaSrc zetaCtr tauG
            (deltaCap deltaWeight xi) N (endpoint s t D N k)) volume
            (s N) (endpoint s t D N k) /\
        (∫ u in (s N)..(endpoint s t D N k),
            g E D s t deltaWeight p N k a u) <=
          (∫ u in (s N)..(endpoint s t D N k),
            profile E D s t zetaSrc zetaCtr tauG
              (deltaCap deltaWeight xi) N (endpoint s t D N k) u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
  have hpoint := eventually_g_le_profile_add hE hD hs0 hst ht1 hc hreg hB
    hzetaSrc hzetaCtr htauG hdeltaWeight hxi p hp beta hbeta
  filter_upwards [hpoint, eventually_ge_atTop 1] with N hpointN hN
  intro k hk a
  have hgi := intervalIntegrable_g (deltaWeight := deltaWeight)
    (p := p) hE hs0 hst ht1 (by omega) hk a
  have hPi := intervalIntegrable_profile (zetaSrc := zetaSrc)
    (zetaCtr := zetaCtr) (tauG := tauG)
    (delta := deltaCap deltaWeight xi) hE hs0 hst ht1 hk
  refine And.intro hgi (And.intro hPi ?_)
  by_cases hkpos : 1 <= k
  . have hv : s N <= endpoint s t D N k :=
      (MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)).1
    have hdom : IntervalIntegrable (fun u =>
        profile E D s t zetaSrc zetaCtr tauG
          (deltaCap deltaWeight xi) N (endpoint s t D N k) u +
          (N : Real) ^ (-beta)) volume (s N) (endpoint s t D N k) :=
      hPi.add intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hv hgi hdom
      (fun u hu => hpointN k hkpos hk u hu a)
    calc
      (∫ u in (s N)..(endpoint s t D N k),
          g E D s t deltaWeight p N k a u) <=
          ∫ u in (s N)..(endpoint s t D N k),
            (profile E D s t zetaSrc zetaCtr tauG
              (deltaCap deltaWeight xi) N (endpoint s t D N k) u +
              (N : Real) ^ (-beta)) := hmono
      _ = (∫ u in (s N)..(endpoint s t D N k),
            profile E D s t zetaSrc zetaCtr tauG
              (deltaCap deltaWeight xi) N (endpoint s t D N k) u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
        rw [intervalIntegral.integral_add hPi intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  . have hk0 : k = 0 := by omega
    subst k
    simp only [endpoint, cutNetPt_zero, intervalIntegral.integral_same,
      sub_self, zero_mul, add_zero]
    exact le_rfl

/-- A positive first cell realizes the same common event and positive actual
smooth support used by the favorable branch, with `deltaWeight` and
`deltaCap` genuinely distinct. -/
theorem positive_first_cell_budget_hypotheses_witness :
    exists tauPrime c : Real, exists s t : Nat -> Real,
      0 < tauPrime /\ 0 < c /\
      (forall N, s N = 0) /\
      (forall N, 0 <= s N) /\
      (forall N, s N <= t N) /\
      (forall N, t N < 1) /\
      Cond272Reg B 0 s t c /\
      BoundsCore (sample d) 0 s /\
      0 < (1 / 200 : Real) /\
      0 < (1 / 200 : Real) /\
      deltaCap (1 / 200 : Real) (1 / 200 : Real) = 1 / 100 /\
      ∀ᶠ N : Nat in atTop,
        s N < t N /\
        exists omega,
          omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t (1 / 100) (1 / 100) (1 / 100) N /\
          1 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N /\
          0 < weight 0 60 s t (1 / 200) 1 N 1 omega := by
  obtain ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, _hstep, hall⟩ :=
    APrimeGeneralMovingDriftAtProfile.positive_cell_full_drift_hypotheses_witness
  have hresident := hall (1 / 100) (1 / 100) (1 / 100) (1 / 200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨tauPrime, c, s, t, htauPrime, hc, hsEq, hs0, hst, ht1, hreg, hB,
    by norm_num, by norm_num, by norm_num [deltaCap], ?_⟩
  filter_upwards [hresident] with N hN
  obtain ⟨hlen, omega, homega, hactive, hwide⟩ := hN
  have hactual := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := (1 / 200 : Real))
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) (by norm_num) N 1 1 omega (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwideOne := hwide 1
  have hweightOne : weight 0 60 s t (1 / 200) 1 N 1 omega = 1 := by
    apply le_antisymm (weight_le_one 0 60 s t (1 / 200) 1 N 1 omega)
    simpa [weight, APrimeGeneralMovingDetFields.J] using
      hwideOne.symm.le.trans hactual
  refine ⟨hlen, omega, homega, hactive, ?_⟩
  rw [hweightOne]
  norm_num

#print axioms endpoint
#print axioms deltaCap
#print axioms weight
#print axioms drift
#print axioms g
#print axioms jSCap
#print axioms quadCap
#print axioms profile
#print axioms measurable_weight
#print axioms weight_nonneg
#print axioms weight_le_one
#print axioms intervalIntegrable_g
#print axioms intervalIntegrable_profile
#print axioms eventually_g_le_profile_add
#print axioms eventually_actual_smooth_drift_integral_le_exact_profile
#print axioms positive_first_cell_budget_hypotheses_witness

end
end RBM.APrimeGeneralMovingSmoothDriftNormBudget
