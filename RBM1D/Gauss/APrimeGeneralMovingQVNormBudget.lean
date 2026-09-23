/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingQVProfile
import RBM1D.Gauss.APrimeQVRateTime
import RBM1D.Gauss.APrimeQVGlobalPoly
import RBM1D.Gauss.APrimeFirstCellDriftNormSplit

/-!
# T591: all-cell general-moving widened-weight QV integral budget

The literal T584 profile is used on the same common event as T579.  The
complement is paid from the all-sample polynomial QV envelope.  The initial
net point is handled only after time integration, by its zero interval.
-/

namespace RBM.APrimeGeneralMovingQVNormBudget

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The endpoint of the target general-moving cut net. -/
noncomputable def endpoint (s _t : Nat -> Real) (D : Real) (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

/-- The target-mesh widened prefix weight used by T584. -/
noncomputable def weight (E D : Real) (s t : Nat -> Real)
    (delta : Real) (p N k : Nat) : Ω d -> Real :=
  APrimeWeight.widenedW
    (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
    (APrimeGeneralMovingDetFields.J E D s) s t
    (APrimeGeneralMovingMesh.targetMesh D) delta p N k

/-- The actual uncut evolved quadratic-variation rate at a target-net endpoint. -/
noncomputable def qv (E D : Real) (s t : Nat -> Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Ω d -> Real :=
  APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N)
    (endpoint s t D N k) u

/-- The widened-weight `L^p` norm of the actual uncut QV rate. -/
noncomputable def g (E D : Real) (s t : Nat -> Real) (delta : Real)
    (p N k : Nat) (a : LoopArg (d.L N) 2) (u : Real) : Real :=
  APrimeModel.rateNormW (P d) (weight E D s t delta p N k) p
    (qv E D s t N k a u)

/-- T584's exact square-of-the-whole-root profile. -/
noncomputable def Qexact (E D : Real) (s t : Nat -> Real)
    (zetaSrc tauG delta : Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Real :=
  ((APrimeDriftTimeFamily.driftScale d E D N a (s N)
      (endpoint s t D N k))⁻¹ *
    APrimeFullQV.rootProfile B E N u (endpoint s t D N k) D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
      (APrimeGeneralMovingQVProfile.generalMovingBlockCap
        E s tauG delta N u)
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((d.W N : Real)⁻¹) a) ^ 2

/-- The literal all-sample envelope obtained from `Keta = 1`. -/
noncomputable def qvEnvelope (D : Real) (N : Nat) : Real :=
  2 ^ (21 : Nat) * (N : Real) ^ (2 * D + 16)

theorem measurable_weight (E D : Real) (s t : Nat -> Real)
    (delta : Real) (p N k : Nat) :
    Measurable (weight E D s t delta p N k) := by
  unfold weight APrimeWeight.widenedW
  split_ifs
  · exact (APrimeWeight.measurable_prefixSoftW
      (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D) N)
      (APrimeGeneralMovingDetFields.J E D s) s
      (APrimeGeneralMovingMesh.targetMesh D) N k _
      (fun u => APrimeSlotFields.measurable_jSnorm
        (sample d) E D s N u)).pow_const (2 * p)
  · exact measurable_const

theorem weight_nonneg (E D : Real) (s t : Nat -> Real)
    (delta : Real) (p N k : Nat) (omega : Ω d) :
    0 <= weight E D s t delta p N k omega :=
  by
    unfold weight
    exact APrimeWeight.widenedW_nonneg _ _ _ _ _ _ _ _ _ _ omega

theorem weight_le_one (E D : Real) (s t : Nat -> Real)
    (delta : Real) (p N k : Nat) (omega : Ω d) :
    weight E D s t delta p N k omega <= 1 :=
  by
    unfold weight
    exact APrimeWeight.widenedW_le_one _ _ _ _ _ _ _ _ _ _ omega

theorem eventually_abs_qv_le_envelope
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall u, u ∈ Icc (s N) (endpoint s t D N k) ->
      forall a : LoopArg (d.L N) 2, forall omega : Ω d,
        |qv E D s t N k a u omega| <= qvEnvelope D N := by
  have heta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  filter_upwards [APrimeQVGlobalPoly.eventually_qvAt_le_poly d
      (E := E) (D := D) (Kη := 1) hE (by linarith) (by norm_num),
    heta, eventually_ge_atTop 1] with N hpoly hetaN hN
  intro k hk u hu a omega
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint s t D N k < 1 := hv.2.trans_lt (ht1 N)
  have hfloor : (N : Real) ^ (-(1 : Real)) <=
      etaT E (endpoint s t D N k) :=
    hetaN.trans (Gauss.etaT_le_of_le hE hv.2)
  have hq := hpoly (s N) (endpoint s t D N k) (hs0 N) hv.1 hv1
    hfloor Step2.sigPM a u hu omega
  change |APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N)
    (endpoint s t D N k) u omega| <= qvEnvelope D N
  rw [abs_of_nonneg hq.1]
  unfold qvEnvelope
  convert hq.2 using 1
  ring_nf

theorem eventually_qvEnvelope_le_rpow {D : Real} (_hD : 60 <= D) :
    ∀ᶠ N : Nat in atTop,
      qvEnvelope D N <= (N : Real) ^ (2 * D + 17) := by
  filter_upwards [eventually_ge_atTop (2 ^ (21 : Nat))] with N hN
  have hconst : (2 : Real) ^ (21 : Nat) <= N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by
    exact_mod_cast (show 0 < N by omega)
  unfold qvEnvelope
  calc
    2 ^ (21 : Nat) * (N : Real) ^ (2 * D + 16) <=
        (N : Real) * (N : Real) ^ (2 * D + 16) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNpos.le _)
    _ = (N : Real) ^ (1 : Real) * (N : Real) ^ (2 * D + 16) := by
      rw [Real.rpow_one]
    _ = (N : Real) ^ ((1 : Real) + (2 * D + 16)) :=
      (Real.rpow_add hNpos 1 (2 * D + 16)).symm
    _ = (N : Real) ^ (2 * D + 17) := by ring_nf

theorem intervalIntegrable_g
    {E D : Real} {s t : Nat -> Real} {delta : Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hp : 1 <= p)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable (g E D s t delta p N k a) volume
      (s N) (endpoint s t D N k) := by
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  exact APrimeQVRateTime.intervalIntegrable_rateNormW_qvAt
    d E D N p Step2.sigPM a hE (hs0 N) hv.1
    (hv.2.trans_lt (ht1 N)) hp (weight E D s t delta p N k)
    (measurable_weight E D s t delta p N k)
    (weight_nonneg E D s t delta p N k)
    (weight_le_one E D s t delta p N k)

set_option maxHeartbeats 800000 in
-- Expanding the exact square-root profile exposes several large nested
-- continuity terms; the extra budget is only for elaborating this proof.
private theorem continuousOn_Qexact
    {E D : Real} {s t : Nat -> Real} {zetaSrc tauG delta : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    ContinuousOn (Qexact E D s t zetaSrc tauG delta N k a)
      (Icc (s N) (endpoint s t D N k)) := by
  have hv : endpoint s t D N k <= t N :=
    (MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)).2
  have hv0 : s N <= endpoint s t D N k :=
    (MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)).1
  have hv1 : endpoint s t D N k < 1 := hv.trans_lt (ht1 N)
  let I : Set Real := Icc (s N) (endpoint s t D N k)
  have hEll : ContinuousOn (fun u => B.ell N u) I := by
    exact Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    unfold etaT
    fun_prop
  have hEll_ne : forall u, u ∈ I -> B.ell N u ≠ 0 := by
    intro u hu
    have hpos : 0 < B.ell N u := by
      have hell := one_le_ellHat_of_nonneg (B.one_le_L N)
        ((hs0 N).trans hu.1) (hu.2.trans_lt hv1)
      simpa only [Band.ell] using
        (show 0 < ellHat (B.L N) (u : Complex) by linarith)
    exact hpos.ne'
  have hEta_ne : forall u, u ∈ I -> etaT E u ≠ 0 := by
    intro u hu
    exact (Step2.etaT_pos' hE (hu.2.trans_lt hv1)).ne'
  have hInvEll : ContinuousOn (fun u => (B.ell N u)⁻¹) I :=
    hEll.inv₀ hEll_ne
  have hInvEta : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ hEta_ne
  have hScale : ContinuousOn (fun u =>
      (B.W N : Real) * B.ell N u * etaT E u) I :=
    (continuousOn_const.mul hEll).mul hEta
  have hScale_ne : forall u, u ∈ I ->
      (B.W N : Real) * B.ell N u * etaT E u ≠ 0 := by
    intro u hu
    have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
    have hell : 0 < B.ell N u := by
      have h := one_le_ellHat_of_nonneg (B.one_le_L N)
        ((hs0 N).trans hu.1) (hu.2.trans_lt hv1)
      simpa only [Band.ell] using
        (show 0 < ellHat (B.L N) (u : Complex) by linarith)
    exact (mul_pos (mul_pos hW hell)
      (Step2.etaT_pos' hE (hu.2.trans_lt hv1))).ne'
  have hInvScale : ContinuousOn (fun u =>
      ((B.W N : Real) * B.ell N u * etaT E u)⁻¹) I :=
    hScale.inv₀ hScale_ne
  have hRat : ContinuousOn (fun u => etaT E (s N) / etaT E u) I :=
    ContinuousOn.div continuousOn_const hEta hEta_ne
  have hJbar : ContinuousOn (fun u =>
      1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
            (etaT E (s N) / etaT E u) ^ 4) + 2)) I := by
    have hmain := (hRat.pow 4).const_mul
      ((N : Real)^tauG * 9 * Real.exp (Real.sqrt 3) *
        (4 * Real.exp 1 + 2) * (N : Real)^(2*delta))
    have htwo : ContinuousOn (fun _ : Real =>
        (N : Real)^tauG * 2) I := continuousOn_const
    have hone : ContinuousOn (fun _ : Real => (1 : Real)) I := continuousOn_const
    convert hone.add (hmain.add htwo) using 1
    funext u
    simp only [Pi.add_apply, Pi.pow_apply]
    ring
  have hSourceC4 : ContinuousOn (fun u =>
      APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u) I := by
    unfold APrimeGeneralMovingRawSources.sourceC4 Band.scale
    exact (continuousOn_const.mul ((hEll.div_const _).pow 3)).mul
      (hInvScale.pow 3)
  have hCNear : ContinuousOn (fun u =>
      Lemma57.cNear2 (B.W N : Real) (B.ell N u)) I := by
    unfold Lemma57.cNear2
    exact (continuousOn_const.add (continuousOn_const.mul hInvEll)).mul
      continuousOn_const
  have hCFar : ContinuousOn (fun u =>
      Lemma57.cFar2 (B.W N : Real) (B.ell N u)) I := by
    unfold Lemma57.cFar2
    exact (continuousOn_const.add (continuousOn_const.mul hInvEll)).mul
      continuousOn_const
  have hNear : ContinuousOn (fun u =>
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
        (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
        (etaT E u)) I := by
    unfold APrimeQVEndpoint.diagNearRate
    exact ((continuousOn_const.mul hInvEta).mul hCNear).mul
      ((hEll.div_const _).pow 5)
  have hTwoJ : ContinuousOn (fun u => 2 *
      (1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
            (etaT E (s N) / etaT E u) ^ 4) + 2))) I :=
    continuousOn_const.mul hJbar
  have hFar : ContinuousOn (fun u =>
      APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D
        (1 + (N : Real)^tauG *
          (9 * Real.exp (Real.sqrt 3) *
            ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
              (etaT E (s N) / etaT E u) ^ 4) + 2))
        (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)) I := by
    unfold APrimeQVEndpoint.diagFarRate
    have hQ2 := hCFar.mul
      ((hTwoJ.pow 2).mul (hScale.mul (hSourceC4.sqrt.const_mul 2)))
    have hQ3 := ((hTwoJ.pow 3).const_mul 72).mul hInvScale
    have hLeak := (hTwoJ.pow 3).const_mul
      (4 * (B.W N : Real) * (B.L N : Real) * (B.W N : Real) ^ (-D))
    have hres := ((hInvEta.const_mul 2).mul (hQ2.add hQ3)).add hLeak
    convert hres using 1
  have hRatio : ContinuousOn (fun u =>
      (1 - u) / (1 - endpoint s t D N k)) I :=
    (continuousOn_const.sub continuousOn_id).div_const _
  have hKernel : ContinuousOn (fun u =>
      ((1 - u) / (1 - endpoint s t D N k)) ^ 2 *
        Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
        Step2.tT B E N D (endpoint s t D N k)
          (zdist (B.L N) (a 0 - a 1))) I :=
    (hRatio.pow 2).mul continuousOn_const |>.mul continuousOn_const
  have hNearMultiplier : ContinuousOn (fun u =>
      ((((1 - u) / (1 - endpoint s t D N k)) ^ 2 *
          Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
          Step2.tT B E N D (endpoint s t D N k)
            (zdist (B.L N) (a 0 - a 1))) *
        (if (zdist (B.L N) (a 0 - a 1) : Real) <=
            6 * ellStar (B.W N : Real) (B.ell N (endpoint s t D N k))
          then 1 else 0)) +
        256 * Real.exp 3 *
          ((1 - u) / (1 - endpoint s t D N k)) ^ 2 *
          (B.W N : Real) ^ (-D) *
          Step2.tT B E N D (endpoint s t D N k)
            (zdist (B.L N) (a 0 - a 1))) I := by
    have hchi := hKernel.const_mul
      (if (zdist (B.L N) (a 0 - a 1) : Real) <=
          6 * ellStar (B.W N : Real) (B.ell N (endpoint s t D N k))
        then 1 else 0)
    have hleak := (hRatio.pow 2).const_mul
      (256 * Real.exp 3 * (B.W N : Real) ^ (-D) *
        Step2.tT B E N D (endpoint s t D N k)
          (zdist (B.L N) (a 0 - a 1)))
    convert hchi.add hleak using 1
    funext u
    simp only [Pi.add_apply, Pi.pow_apply]
    ring
  unfold Qexact
  apply ContinuousOn.pow
  apply ContinuousOn.mul continuousOn_const
  unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
    APrimeFullQV.rootProfile Step2Moment.ratR
  change ContinuousOn _ I
  exact ((hNear.add continuousOn_const).sqrt.mul hNearMultiplier).add
    (hFar.sqrt.mul hKernel)

theorem intervalIntegrable_Qexact
    {E D : Real} {s t : Nat -> Real} {zetaSrc tauG delta : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable (Qexact E D s t zetaSrc tauG delta N k a) volume
      (s N) (endpoint s t D N k) := by
  have hcont := continuousOn_Qexact (E := E) (D := D) (s := s) (t := t)
    (zetaSrc := zetaSrc) (tauG := tauG) (delta := delta)
    hE hs0 hst ht1 hk a
  have hv : s N <= endpoint s t D N k :=
    (MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)).1
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hv).2 hcont.integrableOn_Icc

private theorem integrable_weighted_qv_pow
    {E D : Real} {s t : Nat -> Real} {delta : Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : 0 <= s N)
    (hsv : s N <= endpoint s t D N k)
    (hv1 : endpoint s t D N k < 1)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k))
    (henv : forall omega : Ω d,
      |qv E D s t N k a u omega| <= qvEnvelope D N) :
    Integrable (fun omega =>
      weight E D s t delta p N k omega *
        |qv E D s t N k a u omega| ^ p) (P d) := by
  let uu : Icc (s N) (endpoint s t D N k) := ⟨u, hu⟩
  have hq : Measurable (qv E D s t N k a u) := by
    have hembed : Measurable (fun omega : Ω d => (uu, omega)) :=
      measurable_const.prodMk measurable_id
    have hjoint := APrimeQVRateTime.measurable_qvAt_on_window
      d E D N Step2.sigPM a hE hs0 hsv hv1
    have hcomp := hjoint.comp hembed
    simpa only [qv, Function.comp_def] using hcomp
  have hmeas : Measurable (fun omega =>
      weight E D s t delta p N k omega *
        |qv E D s t N k a u omega| ^ p) :=
    (measurable_weight E D s t delta p N k).mul
      ((continuous_abs.measurable.comp hq).pow_const p)
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((qvEnvelope D N) ^ p)
  exact Filter.Eventually.of_forall fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (weight_nonneg E D s t delta p N k omega)
      (pow_nonneg (abs_nonneg _) _))]
    calc
      weight E D s t delta p N k omega *
          |qv E D s t N k a u omega| ^ p <=
          1 * |qv E D s t N k a u omega| ^ p :=
        mul_le_mul_of_nonneg_right
          (weight_le_one E D s t delta p N k omega)
          (pow_nonneg (abs_nonneg _) _)
      _ <= (qvEnvelope D N) ^ p := by
        simpa only [one_mul] using
          pow_le_pow_left₀ (abs_nonneg _) (henv omega) p

/-- On every positive active cell, the widened weighted norm of the actual
uncut QV rate is bounded by T584's exact profile plus the paid complement. -/
theorem eventually_g_le_Qexact_add
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc)
    (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG)
    (hdelta : 0 < delta)
    (hroom : tauG + 2 * delta + 2 / 15 < 1)
    (p : Nat) (hp : 1 <= p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, forall k : Nat, 1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall u, u ∈ Icc (s N) (endpoint s t D N k) ->
      forall a : LoopArg (d.L N) 2,
        g E D s t delta p N k a u <=
          Qexact E D s t zetaSrc tauG delta N k a u +
            (N : Real) ^ (-beta) := by
  have hHP := APrimeGeneralMovingCommonSources.highProb_commonEvent
    hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG
      hzetaSrc hzetaCtr htauG
  have hpay := Gauss.eventually_env_mul_prob_rpow_le (P := P d)
    (q := p) (by omega) hHP (Env := qvEnvelope D)
    (Cenv := 2 * D + 17) (by linarith)
    (eventually_qvEnvelope_le_rpow hD) hbeta
  filter_upwards [
    APrimeGeneralMovingQVProfile.eventually_qv_profile_on_common_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdelta
      hroom p hp,
    eventually_abs_qv_le_envelope hE hD hs0 hst ht1 hc hreg,
    hpay] with N hprofile henv hpayN
  intro k hk1 hk u hu a
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hZi := integrable_weighted_qv_pow (delta := delta) (p := p)
    hE (hs0 N) hv.1
    (hv.2.trans_lt (ht1 N)) a hu (henv k hk u hu a)
  have hsplit := APrimeFirstCellDriftNormSplit.weighted_norm_le_of_weighted_event
    (P0 := P d) (q := p) (by omega)
    (good := Qexact E D s t zetaSrc tauG delta N k a u)
    (Env := qvEnvelope D N)
    (pr := ((P d) (APrimeGeneralMovingCommonSources.commonEvent
      E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal)
    (weight_nonneg E D s t delta p N k)
    (weight_le_one E D s t delta p N k) hZi
    (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      E D s t zetaSrc zetaCtr tauG N)
    (sq_nonneg _) (by unfold qvEnvelope; positivity) ENNReal.toReal_nonneg
    (fun omega homega => by
      by_cases hw : weight E D s t delta p N k omega = 0
      · simp [hw]
      · have hwpos : 0 < weight E D s t delta p N k omega :=
          lt_of_le_of_ne (weight_nonneg E D s t delta p N k omega)
            (Ne.symm hw)
        have hrow := hprofile k hk1 hk omega homega hwpos u hu a
        have hq0 : 0 <= qv E D s t N k a u omega :=
          APrimeDuhamelModel.qvRateEvolved_nonneg d N
            (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
              (s N) (endpoint s t D N k)) u omega
        rw [abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_left (by
          simpa [qv, Qexact, endpoint] using hrow.2)
          (weight_nonneg E D s t delta p N k omega))
    (henv k hk u hu a)
    (le_rfl : ((P d)
      (APrimeGeneralMovingCommonSources.commonEvent
        E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal <= _)
  change g E D s t delta p N k a u <= _
  calc
    g E D s t delta p N k a u <=
        Qexact E D s t zetaSrc tauG delta N k a u +
          qvEnvelope D N *
            (((P d) (APrimeGeneralMovingCommonSources.commonEvent
              E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal) ^
                ((1 : Real) / p) := by
      simpa [g, qv, APrimeModel.rateNormW, one_div] using hsplit
    _ <= Qexact E D s t zetaSrc tauG delta N k a u +
          (N : Real) ^ (-beta) := add_le_add le_rfl hpayN

/-- The all-`k` exact widened-weight QV integral budget.  At `k=0` only the
equality of the integration endpoints is used; no pointwise QV vanishing is
asserted. -/
theorem eventually_widened_qv_integral_le_exact_profile
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc)
    (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG)
    (hdelta : 0 < delta)
    (hroom : tauG + 2 * delta + 2 / 15 < 1)
    (p : Nat) (hp : 1 <= p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall a : LoopArg (d.L N) 2,
        IntervalIntegrable (g E D s t delta p N k a) volume
            (s N) (endpoint s t D N k) /\
        IntervalIntegrable
            (Qexact E D s t zetaSrc tauG delta N k a) volume
            (s N) (endpoint s t D N k) /\
        (∫ u in (s N)..(endpoint s t D N k),
            g E D s t delta p N k a u) <=
          (∫ u in (s N)..(endpoint s t D N k),
            Qexact E D s t zetaSrc tauG delta N k a u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
  have hpoint := eventually_g_le_Qexact_add hE hD hs0 hst ht1 hc hreg hB
    hzetaSrc hzetaCtr htauG hdelta hroom p hp beta hbeta
  filter_upwards [hpoint] with N hpointN
  intro k hk a
  have hgi := intervalIntegrable_g (delta := delta) hE hs0 hst ht1 hp hk a
  have hQi := intervalIntegrable_Qexact (zetaSrc := zetaSrc)
    (tauG := tauG) (delta := delta) hE hs0 hst ht1 hk a
  refine ⟨hgi, hQi, ?_⟩
  by_cases hkpos : 1 <= k
  · have hv : s N <= endpoint s t D N k :=
      (MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)).1
    have hdom : IntervalIntegrable (fun u =>
        Qexact E D s t zetaSrc tauG delta N k a u +
          (N : Real) ^ (-beta)) volume (s N) (endpoint s t D N k) :=
      hQi.add intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hv hgi hdom
      (fun u hu => hpointN k hkpos hk u hu a)
    calc
      (∫ u in (s N)..(endpoint s t D N k),
          g E D s t delta p N k a u) <=
          ∫ u in (s N)..(endpoint s t D N k),
            (Qexact E D s t zetaSrc tauG delta N k a u +
              (N : Real) ^ (-beta)) := hmono
      _ = (∫ u in (s N)..(endpoint s t D N k),
            Qexact E D s t zetaSrc tauG delta N k a u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
        rw [intervalIntegral.integral_add hQi intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  · have hk0 : k = 0 := by omega
    subst k
    simp only [endpoint, cutNetPt_zero, intervalIntegral.integral_same,
      sub_self, zero_mul, add_zero]
    exact le_rfl

/-- A genuine positive first cell realizes the exact same common event and
positive widened support used by the budget theorem; `beta = 1` is an
additional independent positive complement exponent. -/
theorem positive_first_cell_budget_hypotheses_witness :
    exists tauPrime c : Real, exists s t : Nat -> Real,
      0 < tauPrime /\ 0 < c /\
      (forall N, s N = 0) /\
      (forall N, 0 <= s N) /\
      (forall N, s N <= t N) /\
      (forall N, t N < 1) /\
      Cond272Reg B 0 s t c /\
      BoundsCore (Gauss.sample d) 0 s /\
      (1 / 100 : Real) + 2 * (1 / 100 : Real) + 2 / 15 < 1 /\
      0 < (1 : Real) /\
      ∀ᶠ N : Nat in atTop,
        s N < t N /\
        exists omega,
          omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t (1 / 100) (1 / 100) (1 / 100) N /\
          1 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N /\
          0 < weight 0 60 s t (1 / 100) 1 N 1 omega := by
  obtain ⟨tauPrime, c, s, t, htauPrime, hc, hsEq, hs0, hst, ht1,
      hreg, hB, hroom, hw⟩ :=
    APrimeGeneralMovingQVProfile.positive_first_cell_profile_hypotheses_witness
  refine ⟨tauPrime, c, s, t, htauPrime, hc, hsEq, hs0, hst, ht1,
    hreg, hB, hroom, by norm_num, ?_⟩
  filter_upwards [hw] with N hN
  obtain ⟨hlen, omega, homega, hactive, hwide⟩ := hN
  exact ⟨hlen, omega, homega, hactive, by simpa [weight] using hwide⟩

#print axioms endpoint
#print axioms weight
#print axioms qv
#print axioms g
#print axioms Qexact
#print axioms qvEnvelope
#print axioms measurable_weight
#print axioms weight_nonneg
#print axioms weight_le_one
#print axioms eventually_abs_qv_le_envelope
#print axioms eventually_qvEnvelope_le_rpow
#print axioms intervalIntegrable_g
#print axioms intervalIntegrable_Qexact
#print axioms eventually_g_le_Qexact_add
#print axioms eventually_widened_qv_integral_le_exact_profile
#print axioms positive_first_cell_budget_hypotheses_witness

end
end RBM.APrimeGeneralMovingQVNormBudget
