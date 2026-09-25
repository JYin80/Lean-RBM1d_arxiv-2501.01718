/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothQVProfile
import RBM1D.Gauss.APrimeGeneralMovingQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget

/-!
# T993: actual-smooth general-moving QV norm integral budget

The favorable estimate uses the literal smooth prefix at `deltaWeight` and
T603's absorbed profile at `deltaCap = deltaWeight + xi`. The complement is
paid with T591's all-sample QV envelope on the same common event.
-/

namespace RBM.APrimeGeneralMovingActualSmoothQVNormBudget

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def endpoint (s t : Nat → Real) (D : Real) (N k : Nat) : Real :=
  APrimeGeneralMovingQVNormBudget.endpoint s t D N k

noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight p N k

noncomputable def qv (E D : Real) (s t : Nat → Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Ω d → Real :=
  APrimeGeneralMovingQVNormBudget.qv E D s t N k a u

noncomputable def g (E D : Real) (s t : Nat → Real) (deltaWeight : Real)
    (p N k : Nat) (a : LoopArg (d.L N) 2) (u : Real) : Real :=
  APrimeModel.rateNormW (P d) (weight E D s t deltaWeight p N k) p
    (qv E D s t N k a u)

noncomputable def Qabs (E D : Real) (s t : Nat → Real)
    (zetaSrc tauG deltaCap : Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Real :=
  (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u
    (endpoint s t D N k) D
    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u)
    a) ^ 2

theorem measurable_weight {E D : Real} {s t : Nat → Real}
    {deltaWeight : Real} {p N k : Nat} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    Measurable (weight E D s t deltaWeight p N k) := by
  exact APrimeGeneralMovingSmoothDriftNormBudget.measurable_weight
    (deltaWeight := deltaWeight) (p := p) hE hst ht1 hN hk

theorem weight_nonneg (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) (omega : Ω d) :
    0 ≤ weight E D s t deltaWeight p N k omega := by
  exact APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
    E D s t deltaWeight p N k omega

theorem weight_le_one (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) (omega : Ω d) :
    weight E D s t deltaWeight p N k omega ≤ 1 := by
  exact APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one
    E D s t deltaWeight p N k omega

theorem intervalIntegrable_g
    {E D : Real} {s t : Nat → Real} {deltaWeight : Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable (g E D s t deltaWeight p N k a) volume
      (s N) (endpoint s t D N k) := by
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  exact APrimeQVRateTime.intervalIntegrable_rateNormW_qvAt
    d E D N p Step2.sigPM a hE (hs0 N) hv.1
    (hv.2.trans_lt (ht1 N)) hp (weight E D s t deltaWeight p N k)
    (measurable_weight hE hst ht1 hN hk)
    (weight_nonneg E D s t deltaWeight p N k)
    (weight_le_one E D s t deltaWeight p N k)


private theorem integrable_weighted_qv_pow
    {E D : Real} {s t : Nat → Real} {deltaWeight : Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hsv : s N ≤ endpoint s t D N k)
    (hv1 : endpoint s t D N k < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (hN : 0 < N)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k))
    (henv : ∀ omega : Ω d,
      |qv E D s t N k a u omega| ≤
        APrimeGeneralMovingQVNormBudget.qvEnvelope D N) :
    Integrable (fun omega =>
      weight E D s t deltaWeight p N k omega *
        |qv E D s t N k a u omega| ^ p) (P d) := by
  let uu : Icc (s N) (endpoint s t D N k) := ⟨u, hu⟩
  have hq : Measurable (qv E D s t N k a u) := by
    have hembed : Measurable (fun omega : Ω d => (uu, omega)) :=
      measurable_const.prodMk measurable_id
    have hjoint := APrimeQVRateTime.measurable_qvAt_on_window
      d E D N Step2.sigPM a hE hs0 hsv hv1
    have hcomp := hjoint.comp hembed
    simpa only [qv, APrimeGeneralMovingQVNormBudget.qv,
      endpoint, APrimeGeneralMovingQVNormBudget.endpoint,
      Function.comp_def] using hcomp
  have hmeas : Measurable (fun omega =>
      weight E D s t deltaWeight p N k omega *
        |qv E D s t N k a u omega| ^ p) :=
    (measurable_weight hE hst ht1 hN hk).mul
      ((continuous_abs.measurable.comp hq).pow_const p)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    ((APrimeGeneralMovingQVNormBudget.qvEnvelope D N) ^ p)
  exact Filter.Eventually.of_forall fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (weight_nonneg E D s t deltaWeight p N k omega)
      (pow_nonneg (abs_nonneg _) _))]
    calc
      weight E D s t deltaWeight p N k omega *
          |qv E D s t N k a u omega| ^ p ≤
          1 * |qv E D s t N k a u omega| ^ p :=
        mul_le_mul_of_nonneg_right
          (weight_le_one E D s t deltaWeight p N k omega)
          (pow_nonneg (abs_nonneg _) _)
      _ ≤ (APrimeGeneralMovingQVNormBudget.qvEnvelope D N) ^ p := by
        simpa only [one_mul] using
          pow_le_pow_left₀ (abs_nonneg _) (henv omega) p


/-- Same-event, positive-cell actual-smooth QV norm bound with the full
absorbed root kept under one square and the common-event complement paid. -/
theorem eventually_g_le_Qabs_add
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hxi : 0 < xi)
    (hdeltaCap : 0 < deltaWeight + xi)
    (hzetaTau : zetaSrc ≤ tauG)
    (htauDeltaCap : tauG ≤ (deltaWeight + xi) / 16)
    (hdeltaCapC : deltaWeight + xi ≤ c / 20)
    (hcapRoom : tauG + 2 * (deltaWeight + xi) + (2 : Real) / 15 < 1)
    (p : Nat) (hp : 1 ≤ p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat, 1 ≤ k →
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N) (endpoint s t D N k),
      ∀ a : LoopArg (d.L N) 2,
        g E D s t deltaWeight p N k a u ≤
          Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u +
            (N : Real) ^ (-beta) := by
  have hHP := APrimeGeneralMovingCommonSources.highProb_commonEvent
    hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG
      hzetaSrc hzetaCtr htauG
  have hpay := Gauss.eventually_env_mul_prob_rpow_le (P := P d)
    (q := p) (by omega) hHP
    (Env := APrimeGeneralMovingQVNormBudget.qvEnvelope D)
    (Cenv := 2 * D + 17) (by linarith)
    (APrimeGeneralMovingQVNormBudget.eventually_qvEnvelope_le_rpow hD)
    hbeta
  have hprofile :=
    APrimeGeneralMovingSmoothQVProfile.eventually_qv_le_absorbed_on_actual_smooth_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hxi
      hdeltaCap hzetaTau htauDeltaCap hdeltaCapC hcapRoom p hp
  have henv := APrimeGeneralMovingQVNormBudget.eventually_abs_qv_le_envelope
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [hpay, hprofile, henv, eventually_ge_atTop 2]
    with N hpayN hprofileN henvN hN2
  intro k hk1 hk u hu a
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hZi := integrable_weighted_qv_pow
    (deltaWeight := deltaWeight) (p := p) hE (hs0 N) hst ht1
    hv.1 (hv.2.trans_lt (ht1 N)) hk (by omega) a hu
    (henvN k hk u hu a)
  have hsplit := APrimeFirstCellDriftNormSplit.weighted_norm_le_of_weighted_event
    (P0 := P d) (q := p) (by omega)
    (good := Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u)
    (Env := APrimeGeneralMovingQVNormBudget.qvEnvelope D N)
    (pr := ((P d) (APrimeGeneralMovingCommonSources.commonEvent
      E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal)
    (weight_nonneg E D s t deltaWeight p N k)
    (weight_le_one E D s t deltaWeight p N k) hZi
    (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      E D s t zetaSrc zetaCtr tauG N)
    (sq_nonneg _) (by unfold APrimeGeneralMovingQVNormBudget.qvEnvelope; positivity)
    ENNReal.toReal_nonneg
    (fun omega homega => by
      by_cases hw : weight E D s t deltaWeight p N k omega = 0
      · simp [hw]
      · have hwpos : 0 < weight E D s t deltaWeight p N k omega :=
          lt_of_le_of_ne (weight_nonneg E D s t deltaWeight p N k omega)
            (Ne.symm hw)
        have hrow := hprofileN k hk1 hk omega homega
          (by simpa [weight, APrimeGeneralMovingSmoothDriftNormBudget.weight] using hwpos) u hu a
        have hq0 : 0 ≤ qv E D s t N k a u omega :=
          APrimeDuhamelModel.qvRateEvolved_nonneg d N
            (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
              (s N) (endpoint s t D N k)) u omega
        rw [abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_left
          (by simpa [qv, Qabs, endpoint,
            APrimeGeneralMovingQVNormBudget.qv,
            APrimeGeneralMovingQVNormBudget.endpoint] using hrow.2)
          (weight_nonneg E D s t deltaWeight p N k omega))
    (henvN k hk u hu a)
    (le_rfl : ((P d)
      (APrimeGeneralMovingCommonSources.commonEvent
        E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal ≤ _)
  change g E D s t deltaWeight p N k a u ≤ _
  calc
    g E D s t deltaWeight p N k a u ≤
        Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u +
          APrimeGeneralMovingQVNormBudget.qvEnvelope D N *
            (((P d) (APrimeGeneralMovingCommonSources.commonEvent
              E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal) ^
                ((1 : Real) / p) := by
      simpa [g, qv, APrimeModel.rateNormW, one_div] using hsplit
    _ ≤ Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u +
          (N : Real) ^ (-beta) := add_le_add le_rfl hpayN


private theorem continuousOn_Qabs
    {E D : Real} {s t : Nat → Real} {zetaSrc tauG deltaCap : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    ContinuousOn (Qabs E D s t zetaSrc tauG deltaCap N k a)
      (Icc (s N) (endpoint s t D N k)) := by
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint s t D N k < 1 := hv.2.trans_lt (ht1 N)
  let I : Set Real := Icc (s N) (endpoint s t D N k)
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    unfold etaT
    fun_prop
  have hEllPos : ∀ u ∈ I, 0 < B.ell N u := by
    intro u hu
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N)
        ((hs0 N).trans hu.1) (hu.2.trans_lt hv1))
  have hEtaPos : ∀ u ∈ I, 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hInvEll : ContinuousOn (fun u => (B.ell N u)⁻¹) I :=
    hEll.inv₀ (fun u hu => (hEllPos u hu).ne')
  have hInvEta : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    unfold Step2Moment.ratR
    exact ContinuousOn.div continuousOn_const hEta
      (fun u hu => (hEtaPos u hu).ne')
  have hRatPos : ∀ u ∈ I, 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE
      ((hst N).trans_lt (ht1 N)) (hu.2.trans_lt hv1)
  have hRatNeg : ContinuousOn (fun u =>
      Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (hRatPos u hu).ne')
  have hJ : ContinuousOn (fun u =>
      APrimeGeneralMovingQVProfile.generalMovingBlockCap
        E s tauG deltaCap N u) I := by
    unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
    exact continuousOn_const.add
      (continuousOn_const.mul
        ((continuousOn_const.mul
          (continuousOn_const.mul (hRat.pow 4))).add continuousOn_const))
  have hNear : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
        2 * (B.W N : Real)⁻¹) I := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate Lemma57.cNear2
    exact ((((continuousOn_const.mul hInvEta).mul
      ((continuousOn_const.add (continuousOn_const.mul hInvEll)).mul
        continuousOn_const)).mul ((hEll.div_const _).pow 5)).add
          continuousOn_const)
  have hScale : ContinuousOn (fun u => B.scale E N u) I := by
    unfold Band.scale
    exact (continuousOn_const.mul hEll).mul hEta
  have hScalePos : ∀ u ∈ I, 0 < B.scale E N u := by
    intro u hu
    have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
    change 0 < (B.W N : Real) * B.ell N u * etaT E u
    exact mul_pos (mul_pos hW (hEllPos u hu)) (hEtaPos u hu)
  have hScaleNeg : ContinuousOn (fun u =>
      B.scale E N u ^ (-(1 / 3 : Real))) I :=
    hScale.rpow_const (fun u hu => Or.inl (hScalePos u hu).ne')
  have hFar : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap
          E s tauG deltaCap N u)) I := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    exact ((continuousOn_const.mul hInvEta).mul hScaleNeg).mul (hJ.pow 3)
  unfold Qabs APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  exact (((hRatNeg.mul continuousOn_const).mul
    ((hNear.sqrt.mul continuousOn_const).add
      (hFar.sqrt.mul continuousOn_const))).pow 2)

theorem intervalIntegrable_Qabs
    {E D : Real} {s t : Nat → Real} {zetaSrc tauG deltaCap : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable (Qabs E D s t zetaSrc tauG deltaCap N k a)
      volume (s N) (endpoint s t D N k) := by
  have hv : s N ≤ endpoint s t D N k :=
    (MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)).1
  exact (continuousOn_Qabs hE hs0 hst ht1 hk a).intervalIntegrable_of_Icc hv


/-- The all-active-cell integral bound for the literal differentiable smooth
weight.  The `k=0` branch uses only the zero-length interval. -/
theorem eventually_actual_smooth_qv_integral_le_absorbed_profile
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hxi : 0 < xi)
    (hdeltaCap : 0 < deltaWeight + xi)
    (hzetaTau : zetaSrc ≤ tauG)
    (htauDeltaCap : tauG ≤ (deltaWeight + xi) / 16)
    (hdeltaCapC : deltaWeight + xi ≤ c / 20)
    (hcapRoom : tauG + 2 * (deltaWeight + xi) + (2 : Real) / 15 < 1)
    (p : Nat) (hp : 1 ≤ p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable (g E D s t deltaWeight p N k a) volume
          (s N) (endpoint s t D N k) ∧
        IntervalIntegrable
          (Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a) volume
          (s N) (endpoint s t D N k) ∧
        (∫ u in (s N)..(endpoint s t D N k),
          g E D s t deltaWeight p N k a u) ≤
          (∫ u in (s N)..(endpoint s t D N k),
            Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
  have hpoint := eventually_g_le_Qabs_add hE hD hs0 hst ht1 hc hreg hB
    hzetaSrc hzetaCtr htauG hxi hdeltaCap hzetaTau htauDeltaCap
    hdeltaCapC hcapRoom p hp beta hbeta
  filter_upwards [hpoint, eventually_ge_atTop 2] with N hpointN hN
  intro k hk a
  have hgi := intervalIntegrable_g (deltaWeight := deltaWeight)
    hE hs0 hst ht1 hp (by omega) hk a
  have hQi := intervalIntegrable_Qabs (zetaSrc := zetaSrc)
    (tauG := tauG) (deltaCap := deltaWeight + xi)
    hE hs0 hst ht1 hk a
  refine ⟨hgi, hQi, ?_⟩
  by_cases hkpos : 1 ≤ k
  · have hv : s N ≤ endpoint s t D N k :=
      (MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)).1
    have hdom : IntervalIntegrable (fun u =>
        Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u +
          (N : Real) ^ (-beta)) volume (s N) (endpoint s t D N k) :=
      hQi.add intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hv hgi hdom
      (fun u hu => hpointN k hkpos hk u hu a)
    calc
      (∫ u in (s N)..(endpoint s t D N k),
          g E D s t deltaWeight p N k a u) ≤
          ∫ u in (s N)..(endpoint s t D N k),
            (Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u +
              (N : Real) ^ (-beta)) := hmono
      _ = (∫ u in (s N)..(endpoint s t D N k),
            Qabs E D s t zetaSrc tauG (deltaWeight + xi) N k a u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
        rw [intervalIntegral.integral_add hQi intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  · have hk0 : k = 0 := by omega
    subst k
    simp only [endpoint, APrimeGeneralMovingQVNormBudget.endpoint,
      cutNetPt_zero, intervalIntegral.integral_same,
      sub_self, zero_mul, add_zero]
    exact le_rfl


/-- The unabsorbed full QV profile keeps both the far and endpoint
`W^(-D)` leakage rows visible, with the literal near residual. -/
theorem eventually_g_le_Qexact_add
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hxi : 0 < xi)
    (hdeltaCap : 0 < deltaWeight + xi)
    (hcapRoom : tauG + 2 * (deltaWeight + xi) + 2 / 15 < 1)
    (p : Nat) (hp : 1 ≤ p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat, 1 ≤ k →
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N) (endpoint s t D N k),
      ∀ a : LoopArg (d.L N) 2,
        g E D s t deltaWeight p N k a u ≤
          APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
            (deltaWeight + xi) N k a u + (N : Real) ^ (-beta) := by
  have hHP := APrimeGeneralMovingCommonSources.highProb_commonEvent
    hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG
      hzetaSrc hzetaCtr htauG
  have hpay := Gauss.eventually_env_mul_prob_rpow_le (P := P d)
    (q := p) (by omega) hHP
    (Env := APrimeGeneralMovingQVNormBudget.qvEnvelope D)
    (Cenv := 2 * D + 17) (by linarith)
    (APrimeGeneralMovingQVNormBudget.eventually_qvEnvelope_le_rpow hD)
    hbeta
  have hprofile :=
    APrimeGeneralMovingQVProfile.eventually_qv_profile_on_common_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG
      hdeltaCap hcapRoom p hp
  have hsupport :=
    APrimeSmoothToWidenedSupport.eventually_actualWeight_pos_implies_widenedW_pos
      d (D := D) (delta := deltaWeight) (xi := xi) hE hst ht1
      (APrimeGeneralMovingMesh.targetMesh_pos D) hxi p hp
  have henv := APrimeGeneralMovingQVNormBudget.eventually_abs_qv_le_envelope
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [hpay, hprofile, hsupport, henv,
    eventually_ge_atTop 2] with N hpayN hprofileN hsupportN henvN hN2
  intro k hk1 hk u hu a
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hZi := integrable_weighted_qv_pow
    (deltaWeight := deltaWeight) (p := p) hE (hs0 N) hst ht1
    hv.1 (hv.2.trans_lt (ht1 N)) hk (by omega) a hu
    (henvN k hk u hu a)
  have hsplit := APrimeFirstCellDriftNormSplit.weighted_norm_le_of_weighted_event
    (P0 := P d) (q := p) (by omega)
    (good := APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc
      tauG (deltaWeight + xi) N k a u)
    (Env := APrimeGeneralMovingQVNormBudget.qvEnvelope D N)
    (pr := ((P d) (APrimeGeneralMovingCommonSources.commonEvent
      E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal)
    (weight_nonneg E D s t deltaWeight p N k)
    (weight_le_one E D s t deltaWeight p N k) hZi
    (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      E D s t zetaSrc zetaCtr tauG N)
    (sq_nonneg _) (by unfold APrimeGeneralMovingQVNormBudget.qvEnvelope; positivity)
    ENNReal.toReal_nonneg
    (fun omega homega => by
      by_cases hw : weight E D s t deltaWeight p N k omega = 0
      · simp [hw]
      · have hwpos : 0 < weight E D s t deltaWeight p N k omega :=
          lt_of_le_of_ne (weight_nonneg E D s t deltaWeight p N k omega)
            (Ne.symm hw)
        have hwide := hsupportN k hk omega
          (by simpa [weight, APrimeGeneralMovingSmoothDriftNormBudget.weight]
            using hwpos)
        have hrow := hprofileN k hk1 hk omega homega hwide u hu a
        have hq0 : 0 ≤ qv E D s t N k a u omega :=
          APrimeDuhamelModel.qvRateEvolved_nonneg d N
            (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
              (s N) (endpoint s t D N k)) u omega
        rw [abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_left
          (by simpa [qv, endpoint,
            APrimeGeneralMovingQVNormBudget.qv,
            APrimeGeneralMovingQVNormBudget.endpoint,
            APrimeGeneralMovingQVNormBudget.Qexact] using hrow.2)
          (weight_nonneg E D s t deltaWeight p N k omega))
    (henvN k hk u hu a)
    (le_rfl : ((P d)
      (APrimeGeneralMovingCommonSources.commonEvent
        E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal ≤ _)
  change g E D s t deltaWeight p N k a u ≤ _
  calc
    g E D s t deltaWeight p N k a u ≤
        APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
          (deltaWeight + xi) N k a u +
          APrimeGeneralMovingQVNormBudget.qvEnvelope D N *
            (((P d) (APrimeGeneralMovingCommonSources.commonEvent
              E D s t zetaSrc zetaCtr tauG N)ᶜ).toReal) ^
                ((1 : Real) / p) := by
      simpa [g, qv, APrimeModel.rateNormW, one_div] using hsplit
    _ ≤ APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
          (deltaWeight + xi) N k a u + (N : Real) ^ (-beta) :=
      add_le_add le_rfl hpayN


/-- The all-cell integral bound in the unabsorbed T591 profile; both
leakage terms remain literal inside the whole-root square. -/
theorem eventually_actual_smooth_qv_integral_le_exact_profile
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hxi : 0 < xi)
    (hdeltaCap : 0 < deltaWeight + xi)
    (hcapRoom : tauG + 2 * (deltaWeight + xi) + 2 / 15 < 1)
    (p : Nat) (hp : 1 ≤ p)
    (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable (g E D s t deltaWeight p N k a) volume
          (s N) (endpoint s t D N k) ∧
        IntervalIntegrable
          (APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
            (deltaWeight + xi) N k a) volume
          (s N) (endpoint s t D N k) ∧
        (∫ u in (s N)..(endpoint s t D N k),
          g E D s t deltaWeight p N k a u) ≤
          (∫ u in (s N)..(endpoint s t D N k),
            APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
              (deltaWeight + xi) N k a u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
  have hpoint := eventually_g_le_Qexact_add hE hD hs0 hst ht1 hc hreg hB
    hzetaSrc hzetaCtr htauG hxi hdeltaCap hcapRoom p hp beta hbeta
  filter_upwards [hpoint, eventually_ge_atTop 2] with N hpointN hN
  intro k hk a
  have hgi := intervalIntegrable_g (deltaWeight := deltaWeight)
    hE hs0 hst ht1 hp (by omega) hk a
  have hQi := APrimeGeneralMovingQVNormBudget.intervalIntegrable_Qexact
    (zetaSrc := zetaSrc) (tauG := tauG) (delta := deltaWeight + xi)
    hE hs0 hst ht1 hk a
  refine ⟨hgi, hQi, ?_⟩
  by_cases hkpos : 1 ≤ k
  · have hv : s N ≤ endpoint s t D N k :=
      (MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)).1
    have hdom : IntervalIntegrable (fun u =>
        APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
          (deltaWeight + xi) N k a u + (N : Real) ^ (-beta))
          volume (s N) (endpoint s t D N k) :=
      hQi.add intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hv hgi hdom
      (fun u hu => hpointN k hkpos hk u hu a)
    calc
      (∫ u in (s N)..(endpoint s t D N k),
          g E D s t deltaWeight p N k a u) ≤
          ∫ u in (s N)..(endpoint s t D N k),
            (APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
              (deltaWeight + xi) N k a u + (N : Real) ^ (-beta)) := hmono
      _ = (∫ u in (s N)..(endpoint s t D N k),
            APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG
              (deltaWeight + xi) N k a u) +
          (endpoint s t D N k - s N) * (N : Real) ^ (-beta) := by
        dsimp only [endpoint]
        rw [intervalIntegral.integral_add hQi intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  · have hk0 : k = 0 := by omega
    subst k
    simp only [endpoint, APrimeGeneralMovingQVNormBudget.endpoint,
      cutNetPt_zero, intervalIntegral.integral_same,
      sub_self, zero_mul, add_zero]
    exact le_rfl


/-- Nondegenerate same-resident `k=1` witness for the favorable branch.
It has positive window length and positive literal smooth weight on the
same common-event sample. -/
theorem positive_cell_hypotheses_witness :
    ∃ c : Real, ∃ s t : Nat → Real,
      ∃ deltaCap deltaWeight xi tauG zetaSrc zetaCtr : Real,
      |(0 : Real)| < 2 ∧ (60 : Real) ≤ 60 ∧ (1 : Nat) ≤ 1 ∧
      0 < c ∧ 0 < deltaCap ∧
      deltaWeight = deltaCap / 2 ∧ xi = deltaCap / 2 ∧
      0 ≤ deltaWeight ∧ 0 < xi ∧ deltaWeight + xi = deltaCap ∧
      0 < tauG ∧ 0 < zetaSrc ∧ 0 < zetaCtr ∧
      zetaSrc ≤ tauG ∧ tauG ≤ deltaCap / 16 ∧ deltaCap ≤ c / 20 ∧
      tauG + 2 * deltaCap + (2 : Real) / 15 < 1 ∧
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      (∀ N, 0 < APrimeGeneralMovingMesh.targetMesh 60 N) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      ∀ᶠ N : Nat in atTop,
        s N < t N ∧
        ∃ omega,
          omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t zetaSrc zetaCtr tauG N ∧
          1 ≤ cutNetTop s t
            (APrimeGeneralMovingMesh.targetMesh 60) N ∧
          APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u omega => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u omega)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              deltaWeight 1 N 1 omega = 1 ∧
          0 < weight 0 60 s t deltaWeight 1 N 1 omega := by
  simpa only [weight, APrimeGeneralMovingSmoothDriftNormBudget.weight] using
    APrimeGeneralMovingSmoothQVProfile.same_resident_positive_cell_actual_weight_witness

#print axioms endpoint
#print axioms weight
#print axioms qv
#print axioms g
#print axioms Qabs
#print axioms measurable_weight
#print axioms weight_nonneg
#print axioms weight_le_one
#print axioms intervalIntegrable_g
#print axioms eventually_g_le_Qabs_add
#print axioms intervalIntegrable_Qabs
#print axioms eventually_actual_smooth_qv_integral_le_absorbed_profile
#print axioms eventually_g_le_Qexact_add
#print axioms eventually_actual_smooth_qv_integral_le_exact_profile
#print axioms positive_cell_hypotheses_witness

end
end RBM.APrimeGeneralMovingActualSmoothQVNormBudget
