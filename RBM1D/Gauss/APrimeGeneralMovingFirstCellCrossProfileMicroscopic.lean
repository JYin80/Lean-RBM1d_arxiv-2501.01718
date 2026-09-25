/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral

/-!
# T1255: microscopic deterministic cross-profile integral on the first cell

This is the exact integral of the deterministic T1029 cross profile on the
active first positive target cell.  It retains the endpoint `ratR(v)⁻²` and
uses the public T1245 pointwise estimate before integration.  The statement is
not the stopped stochastic cross estimate in the paper.
-/

namespace RBM.APrimeGeneralMovingFirstCellCrossProfileMicroscopic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

private noncomputable def profileCap (E : Real) (s : Nat → Real)
    (tauG delta : Real) (N : Nat) (u : Real) : Real :=
  APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG delta N u

private theorem continuousOn_absorbedRootProfile
    {E zetaSrc tauG deltaCap : Real} {s : Nat → Real} {N : Nat}
    {v D : Real} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (a : LoopArg (B.L N) 2) :
    ContinuousOn
      (fun u => APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
        zetaSrc N u v D (profileCap E s tauG deltaCap N u) a)
      (Icc (s N) v) := by
  let I : Set Real := Icc (s N) v
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
      (hsv.trans_lt hv1) (hu.2.trans_lt hv1)
  have hRatNeg : ContinuousOn (fun u =>
      Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (hRatPos u hu).ne')
  have hJ : ContinuousOn (fun u => profileCap E s tauG deltaCap N u) I := by
    unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap
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
        (profileCap E s tauG deltaCap N u)) I := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    exact ((continuousOn_const.mul hInvEta).mul hScaleNeg).mul (hJ.pow 3)
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  exact (hRatNeg.mul continuousOn_const).mul
    ((hNear.sqrt.mul continuousOn_const).add
      (hFar.sqrt.mul continuousOn_const))

private theorem intervalIntegrable_crossProfile
    {E D : Real} {s t : Nat → Real}
    {zetaSrc tauG deltaWeight deltaCap : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (B.L N) 2) :
    let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
    IntervalIntegrable
      (APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc
        tauG deltaWeight deltaCap N k a) volume (s N) v := by
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hBase : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹) volume
      (s N) v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
    rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
    intro u hu
    exact ⟨(hs0 N).trans hu.1, hu.2⟩
  have hFactor : ContinuousOn (fun u =>
      (1/2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a) (Icc (s N) v) := by
    exact continuousOn_const.mul
      (continuousOn_absorbedRootProfile (E := E) (zetaSrc := zetaSrc)
        (tauG := tauG) (deltaCap := deltaCap) (s := s) (N := N)
        (v := v) (D := D) hE hs0 hv.1 hv1 a)
  have hinv : ∀ u : Real,
      (2 * Real.sqrt u)⁻¹ = (Real.sqrt u)⁻¹ / 2 := by
    intro u
    rw [mul_inv_rev]
    norm_num
    ring
  change IntervalIntegrable (fun u =>
      (2 * Real.sqrt u)⁻¹ *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a) volume (s N) v
  have hfun : (fun u => (2 * Real.sqrt u)⁻¹ *
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t zetaSrc tauG deltaWeight N k *
      APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (profileCap E s tauG deltaCap N u) a) =
      (fun u => Real.sqrt u⁻¹ * ((1/2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a)) := by
    funext u
    rw [hinv u]
    rw [← Real.sqrt_inv u]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hfun]
  exact hBase.mul_continuousOn (by simpa only [Set.uIcc_of_le hv.1] using hFactor)

set_option maxHeartbeats 1000000 in
/-- The integral of the literal deterministic T1029 cross profile on the
active first positive target cell.  The endpoint transport factor remains
`ratR(v)⁻²`; the power gain comes solely from the exact first-cell mesh width.
-/
theorem eventually_integral_firstCell_crossProfile_le_microscopic
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 0 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop,
      1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (B.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u) ≤
          2 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real)^(13*δ/640 - 2*D - 8) *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
  have hPoint :=
    RBM.APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hEtaLower :=
    Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hMeshEq := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  filter_upwards [hPoint, hEtaLower, hMeshEq, eventually_ge_atTop 1]
    with N hPointN hEtaLowerN hMeshN hN
  intro hactive a
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let v := cutNetPt s mesh N 1
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hNnonneg : (0 : Real) ≤ N := hNpos.le
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hactive)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hEtaTLower : (N : Real)^(-(1 : Real)) ≤ etaT E (t N) := hEtaLowerN
  have hEtaTInv : (etaT E (t N))⁻¹ ≤ (N : Real) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hNpos (-(1 : Real))) hEtaTLower
    simpa only [Real.rpow_neg_one, inv_inv] using hi
  have hEtaSInv : (etaT E (s N))⁻¹ ≤ (N : Real) := by
    calc
      (etaT E (s N))⁻¹ ≤ (etaT E (t N))⁻¹ :=
        inv_anti₀ (Step2.etaT_pos' hE (ht1 N))
          (etaT_le_of_le hE (hst N))
      _ ≤ (N : Real) := hEtaTInv
  have hGap : v - s N = 1 / mesh N := by
    dsimp [v, mesh, CutHypTheta.cutNetPt]
    ring
  have hMeshValue : mesh N = (N : Real)^(4*D+18) := hMeshN
  have hGapPower : v - s N = (N : Real)^(-(4*D+18)) := by
    have hInv : 1 / (N : Real)^(4*D+18) = (N : Real)^(-(4*D+18)) := by
      rw [Real.rpow_neg hNpos.le, one_div]
    rw [hGap, hMeshValue, hInv]
  have hGap0 : 0 ≤ v - s N := sub_nonneg.mpr hv.1
  have hSqrtGap : Real.sqrt (v - s N) = (N : Real)^(-(2*D+9)) := by
    rw [hGapPower, Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hSqrtDiff0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hv.1)
  have hSqrtDiffSq :
      (Real.sqrt v - Real.sqrt (s N))^2 ≤ v - s N := by
    have hcross : 0 ≤ 2 * Real.sqrt (s N) *
        (Real.sqrt v - Real.sqrt (s N)) :=
      mul_nonneg (by positivity) hSqrtDiff0
    have hvSq : (Real.sqrt v)^2 = v := Real.sq_sqrt hv0
    have hsSq : (Real.sqrt (s N))^2 = s N := Real.sq_sqrt (hs0 N)
    nlinarith
  have hSqrtDiffSq' :
      (Real.sqrt v - Real.sqrt (s N))^2 ≤ (Real.sqrt (v - s N))^2 := by
    rw [Real.sq_sqrt hGap0]
    exact hSqrtDiffSq
  have hSqrtDiff : Real.sqrt v - Real.sqrt (s N) ≤
      (N : Real)^(-(2*D+9)) := by
    have hle := (sq_le_sq₀ hSqrtDiff0 (Real.sqrt_nonneg _)).mp hSqrtDiffSq'
    rw [hSqrtGap] at hle
    exact hle
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hv1
  let K := APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst
  let C := K * (N : Real)^(13*δ/640) * (etaT E (s N))⁻¹ *
    Step2Moment.ratR E s N v^(-(2 : Real))
  have hKpos : 0 < K :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hEtaSpos : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hCnonneg : 0 ≤ C := by
    change 0 ≤ K * (N : Real)^(13*δ/640) * (etaT E (s N))⁻¹ *
      Step2Moment.ratR E s N v^(-(2 : Real))
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hKpos.le (Real.rpow_nonneg hNnonneg _))
        (inv_nonneg.mpr hEtaSpos.le))
      (Real.rpow_nonneg hRpos.le _)
  have hCrossInt : IntervalIntegrable
      (APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a)
      volume (s N) v := by
    simpa only [v, mesh] using
      intervalIntegrable_crossProfile
        (zetaSrc := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (tauG := APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (deltaCap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
        hE hs0 hst ht1 hactive a
  have hEnvelopeInt : IntervalIntegrable (fun u : Real => C / Real.sqrt u)
      volume (s N) v :=
    APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      C (s N) v (hs0 N) hv.1
  have hpointwise : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u ≤
          C / Real.sqrt u := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simp [C, K, APrimeGeneralMovingCrossProfileSlot.crossProfile]
    · have huPos : 0 < u :=
        lt_of_le_of_ne ((hs0 N).trans hu.1) (Ne.symm hu0)
      have hmic := hPointN 1 hactive a u hu huPos
      simpa [C, K] using hmic
  have hmono := intervalIntegral.integral_mono_on hv.1 hCrossInt
    hEnvelopeInt hpointwise
  have hIntegralEnvelope :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      C (s N) v (hs0 N) hv.1
  have hIntegralBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u) ≤
        2 * C * (N : Real)^(-(2*D+9)) := by
    calc
      _ ≤ ∫ u in (s N)..v, C / Real.sqrt u := hmono
      _ = 2 * C * (Real.sqrt v - Real.sqrt (s N)) := hIntegralEnvelope
      _ ≤ 2 * C * (N : Real)^(-(2*D+9)) :=
        mul_le_mul_of_nonneg_left hSqrtDiff (by positivity)
  have hRinv0 : 0 ≤ Step2Moment.ratR E s N v^(-(2 : Real)) :=
    Real.rpow_nonneg hRpos.le _
  have hNalpha0 : 0 ≤ (N : Real)^(13*δ/640) :=
    Real.rpow_nonneg hNnonneg _
  have hEtaProduct :
      (N : Real)^(13*δ/640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : Real)) ≤
        (N : Real)^(13*δ/640) * (N : Real) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEtaSInv hNalpha0) hRinv0
  have hPowerCombine :
      (N : Real)^(13*δ/640) * (N : Real) *
        (N : Real)^(-(2*D+9)) =
      (N : Real)^(13*δ/640 - 2*D - 8) := by
    calc
      (N : Real)^(13*δ/640) * (N : Real) *
          (N : Real)^(-(2*D+9)) =
        (N : Real)^(13*δ/640) * (N : Real)^(1 : Real) *
          (N : Real)^(-(2*D+9)) := by rw [Real.rpow_one]
      _ = (N : Real)^(13*δ/640 + 1) *
          (N : Real)^(-(2*D+9)) := by rw [← Real.rpow_add hNpos]
      _ = (N : Real)^(13*δ/640 + 1 + -(2*D+9)) := by
        rw [← Real.rpow_add hNpos]
      _ = (N : Real)^(13*δ/640 - 2*D - 8) := by
        congr 1
        ring
  calc
    _ ≤ 2 * C * (N : Real)^(-(2*D+9)) := hIntegralBound
    _ = 2 * K * ((N : Real)^(13*δ/640) *
          (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : Real))) *
        (N : Real)^(-(2*D+9)) := by dsimp [C]; ring
    _ ≤ 2 * K * ((N : Real)^(13*δ/640) * (N : Real) *
          Step2Moment.ratR E s N v^(-(2 : Real))) *
        (N : Real)^(-(2*D+9)) := by
      calc
        _ = (2 * K * ((N : Real)^(13*δ/640) *
              (etaT E (s N))⁻¹ *
              Step2Moment.ratR E s N v^(-(2 : Real)))) *
            (N : Real)^(-(2*D+9)) := by ring
        _ ≤ (2 * K * ((N : Real)^(13*δ/640) * (N : Real) *
              Step2Moment.ratR E s N v^(-(2 : Real)))) *
            (N : Real)^(-(2*D+9)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hEtaProduct
              (mul_nonneg (by norm_num) hKpos.le))
            (Real.rpow_nonneg hNnonneg _)
        _ = _ := by ring
    _ = 2 * K * ((N : Real)^(13*δ/640) * (N : Real) *
          (N : Real)^(-(2*D+9))) *
        Step2Moment.ratR E s N v^(-(2 : Real)) := by ring
    _ = 2 * K * (N : Real)^(13*δ/640 - 2*D - 8) *
        Step2Moment.ratR E s N v^(-(2 : Real)) := by
      rw [hPowerCombine]

#print axioms eventually_integral_firstCell_crossProfile_le_microscopic
#print axioms APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingFirstCellCrossProfileMicroscopic
