/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodReduction
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.APrimeGeneralMovingTransitionPrefixGradient
import RBM1D.Gauss.APrimeGeneralMovingTransitionQV
import RBM1D.Gauss.APrimeGeneralMovingJointGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormBadIntegralAllOrders
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1305: free-loss norm-good cross event split

The event argument is rebuilt from the raw transition, common-event, and
norm-bad producers with the corrected loss schedule.  The output retains the
literal cross profile and the two distinct inverse-N payments.
-/

namespace RBM.APrimeFreeLossCrossEventSplit

open Filter MeasureTheory Set Gauss CutHypTheta
open Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

private noncomputable def sourceLoss (loss : ℝ) : ℝ := loss / 1000
private noncomputable def weightLoss (loss : ℝ) : ℝ := loss
private noncomputable def bufferLoss (loss : ℝ) : ℝ := loss
private noncomputable def capLoss (loss : ℝ) : ℝ := 2 * loss

private theorem free_loss_rooms {loss c : ℝ} (hloss : 0 < loss)
    (hsmall : loss ≤ min (1 / 10000 : ℝ) (c / 10000)) (hc : 0 < c) :
    0 < sourceLoss loss ∧ 0 < weightLoss loss ∧ 0 < bufferLoss loss ∧
    0 < capLoss loss ∧ weightLoss loss + bufferLoss loss = capLoss loss ∧
    sourceLoss loss ≤ weightLoss loss / 16 ∧
    sourceLoss loss ≤ capLoss loss / 16 ∧
    weightLoss loss ≤ c / 20 ∧ capLoss loss ≤ c / 20 ∧
    sourceLoss loss + 2 * weightLoss loss + (2 : ℝ) / 15 < 1 ∧
    sourceLoss loss + 2 * capLoss loss + (2 : ℝ) / 15 < 1 := by
  have hloss1 : loss ≤ 1 / 10000 := hsmall.trans (min_le_left _ _)
  have hlossc : loss ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [sourceLoss]; positivity
  · dsimp [weightLoss]; exact hloss
  · dsimp [bufferLoss]; exact hloss
  · dsimp [capLoss]; linarith
  · dsimp [weightLoss, bufferLoss, capLoss]; ring
  · dsimp [sourceLoss, weightLoss]; nlinarith
  · dsimp [sourceLoss, capLoss]; nlinarith
  · dsimp [weightLoss]; nlinarith
  · dsimp [capLoss]; nlinarith
  · dsimp [sourceLoss, weightLoss]; nlinarith
  · dsimp [sourceLoss, capLoss]; nlinarith

private theorem absorbedRootProfile_nonneg
    {E zetaSrc tauG deltaCap : ℝ} {s : ℕ → ℝ} {N : ℕ}
    {u v D : ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hu : s N ≤ u) (hv : u ≤ v) (hv1 : v < 1)
    (a : LoopArg (d.L N) 2) :
    0 ≤ APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
      (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a := by
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  have hu1 : u < 1 := hv.trans_lt hv1
  have hs1 : s N < 1 := hu.trans_lt hu1
  have hRu : 0 < Step2Moment.ratR E s N u :=
    Step2Moment.ratR_pos hE hs1 hu1
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hW : 0 < B.W N := by exact_mod_cast B.W_pos N
  have hEll : 0 < B.ell N u := by
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N |>.trans hu)
        (hv.trans_lt hv1))
  have hEta : 0 < etaT E u := Step2.etaT_pos' hE (hv.trans_lt hv1)
  have hJ : 0 ≤ APrimeGeneralMovingQVProfile.generalMovingBlockCap
      E s tauG deltaCap N u := by
    unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
    positivity
  have hEllS : 0 < B.ell N (s N) := by
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
        ((hu.trans hv).trans_lt hv1))
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hNear : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
      2 * (B.W N : ℝ)⁻¹ := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    have hcNear : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) (B.ell N u) :=
      Lemma57.cNear2_nonneg hW1 hEll
    positivity
  have hFar : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
      (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    have hscale : 0 < B.scale E N u := by
      change 0 < (B.W N : ℝ) * B.ell N u * etaT E u
      positivity
    have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
        6 * ellStar (B.W N : ℝ) (B.ell N v) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    positivity
  have hxi : 0 ≤ Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  positivity

private theorem continuousOn_absorbedRootProfile_local
    {E zetaSrc tauG deltaCap : ℝ} {s : ℕ → ℝ} {N : ℕ}
    {v D : ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (a : LoopArg (d.L N) 2) :
    ContinuousOn
      (fun u => APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
        zetaSrc N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)
      (Icc (s N) v) := by
  let I : Set ℝ := Icc (s N) v
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    unfold etaT
    fun_prop
  have hEllPos : ∀ u ∈ I, 0 < B.ell N u := by
    intro u hu
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans hu.1)
        (hu.2.trans_lt hv1))
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
    exact Step2Moment.ratR_pos hE (hsv.trans_lt hv1) (hu.2.trans_lt hv1)
  have hRatNeg : ContinuousOn (fun u =>
      Step2Moment.ratR E s N u ^ (-(2 : ℝ))) I :=
    hRat.rpow_const (fun u hu => Or.inl (hRatPos u hu).ne')
  have hJ : ContinuousOn (fun u =>
      APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) I := by
    unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
    exact continuousOn_const.add
      (continuousOn_const.mul
        ((continuousOn_const.mul
          (continuousOn_const.mul (hRat.pow 4))).add continuousOn_const))
  have hNear : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
        2 * (B.W N : ℝ)⁻¹) I := by
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
    have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    change 0 < (B.W N : ℝ) * B.ell N u * etaT E u
    exact mul_pos (mul_pos hW (hEllPos u hu)) (hEtaPos u hu)
  have hScaleNeg : ContinuousOn (fun u =>
      B.scale E N u ^ (-(1 / 3 : ℝ))) I :=
    hScale.rpow_const (fun u hu => Or.inl (hScalePos u hu).ne')
  have hFar : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u)) I := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    exact ((continuousOn_const.mul hInvEta).mul hScaleNeg).mul (hJ.pow 3)
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  exact (hRatNeg.mul continuousOn_const).mul
    ((hNear.sqrt.mul continuousOn_const).add (hFar.sqrt.mul continuousOn_const))

private theorem intervalIntegrable_crossProfile_local
    {E D : ℝ} {s t : ℕ → ℝ} {zetaSrc tauG deltaWeight deltaCap : ℝ}
    {N k : ℕ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (mesh D) N)
    (a : LoopArg (d.L N) 2) :
    let v := cutNetPt s (mesh D) N k
    IntervalIntegrable
      (RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        zetaSrc tauG deltaWeight deltaCap N k a) volume (s N) v := by
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hBase : IntervalIntegrable (fun u : ℝ => Real.sqrt u⁻¹) volume
      (s N) v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
    rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
    intro u hu
    exact ⟨(hs0 N).trans hu.1, hu.2⟩
  have hFactor : ContinuousOn (fun u =>
      (1 / 2 : ℝ) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)
      (Icc (s N) v) := by
    exact continuousOn_const.mul
      (continuousOn_absorbedRootProfile_local (E := E) (zetaSrc := zetaSrc)
        (tauG := tauG) (deltaCap := deltaCap) (s := s) (N := N)
        (v := v) (D := D) hE hs0 hv.1 hv1 a)
  have hinv : ∀ u : ℝ, (2 * Real.sqrt u)⁻¹ = (Real.sqrt u)⁻¹ / 2 := by
    intro u
    rw [mul_inv_rev]
    norm_num
    ring
  change IntervalIntegrable (fun u =>
      (2 * Real.sqrt u)⁻¹ *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)
      volume (s N) v
  have hfun : (fun u => (2 * Real.sqrt u)⁻¹ *
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t zetaSrc tauG deltaWeight N k *
      APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a) =
      (fun u => Real.sqrt u⁻¹ * ((1 / 2 : ℝ) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)) := by
    funext u
    rw [hinv u]
    rw [← Real.sqrt_inv u]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hfun]
  exact hBase.mul_continuousOn (by simpa only [Set.uIcc_of_le hv.1] using hFactor)

set_option maxHeartbeats 1000000 in
/-- For each fixed `p ≥ 1`, the literal T1201 norm-good budget has the
free-loss event split, uniformly over every active cell (including `k = 0`),
output, and positive time in its closed cell.  The profile is evaluated at
`zetaSrc = tauG = lambda/1000`, `deltaWeight = xi = lambda`, and
`deltaCap = 2 lambda`. -/
theorem eventually_normGoodCrossBudget_le_freeLossProfile_add_payment
    {E D c loss : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hloss : 0 < loss)
    (hsmall : loss ≤ min (1 / 10000 : ℝ) (c / 10000))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        ∀ u ∈ Icc (s N) (cutNetPt s (mesh D) N k),
          0 < u →
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D loss s t N k p a u ≤
            (15 * (p : ℝ) / 4) *
                RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile
                  E D s t (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a u +
              (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / √u := by
  let zetaSrc := sourceLoss loss
  let zetaCtr := sourceLoss loss
  let tauG := sourceLoss loss
  let deltaWeight := weightLoss loss
  let xi := bufferLoss loss
  let deltaCap := capLoss loss
  let Ξ : ℕ → Set (Gauss.Ω d) := fun N =>
    APrimeGeneralMovingCommonSources.commonEvent E D s t zetaSrc zetaCtr tauG N
  let K : ℝ := 15 * (p : ℝ) / 4
  let Kbad : ℝ := 15 * (p : ℝ) / 8
  rcases free_loss_rooms hloss hsmall hc with
    ⟨hzsrc, hdw, hxi, hcap, hdeltaEq, hprefixTau, hqvTau,
      hprefixC, hcapC, hprefixRoom, hcapRoom⟩
  have hsourceTau : zetaSrc ≤ tauG := by rfl
  have hHP : HighProb (Gauss.P d) Ξ := by
    exact APrimeGeneralMovingCommonSources.highProb_commonEvent
      hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG hzsrc hzsrc hzsrc
  have hEnvPoly : ∀ᶠ N : ℕ in atTop,
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ≤
        (N : ℝ)^(2 * D + 17) :=
    APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow hD
  have hEnvJoint :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdw.le
  have hPay := Gauss.eventually_env_mul_prob_rpow_le
    (P := Gauss.P d) (q := 2 * p) (by omega) hHP
    (Env := APrimeGeneralMovingJointGlobalPoly.jointEnvelope D)
    (Cenv := 2 * D + 17) (by linarith) hEnvPoly
    (D := 1) (by norm_num)
  have hJointInt :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdw.le p hp
  have hPrefix :=
    APrimeGeneralMovingTransitionPrefixGradient.eventually_prefixGradient_le_on_smooth_transition
      hE hD hs0 hst ht1 hc hreg hB (zetaSrc := zetaSrc) (zetaCtr := zetaCtr)
      (tauG := tauG) (delta := deltaWeight)
      hzsrc hzsrc hzsrc hdw hsourceTau
      hprefixTau hprefixC hprefixRoom
  have hQV :=
    APrimeGeneralMovingTransitionQV.eventually_qv_le_absorbed_on_smooth_transition_buffered
      hE hD hs0 hst ht1 hc hreg hB (zetaSrc := zetaSrc) (zetaCtr := zetaCtr)
      (tauG := tauG) (deltaWeight := deltaWeight) (xi := xi)
      hzsrc hzsrc hzsrc hxi
      (by rw [hdeltaEq]; exact hcap) hsourceTau
      (by rw [hdeltaEq]; exact hqvTau)
      (by rw [hdeltaEq]; exact hcapC)
      (by rw [hdeltaEq]; exact hcapRoom)
  have hNdim := B.dim
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hEnvPoly,
      hEnvJoint, hNdim, eventually_ge_atTop 1]
    with N hPayN hJointN hPrefixN hQVN hEnvN hEnvJointN hdim hN
  have hNpos : 0 < N := by omega
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay :
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
          ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
        (N : ℝ)^(-1 : ℝ) := by
    simpa [Ξ] using hPayN
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKbad0 : 0 ≤ Kbad := by dsimp [Kbad]; positivity
  intro k hk a u hu huPos
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have huIcc : u ∈ Icc (s N) v := by simpa [v] using hu
  have hu0 : 0 ≤ u := (hs0 N).trans huIcc.1
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hRoot0 := absorbedRootProfile_nonneg
    (E := E) (zetaSrc := zetaSrc) (tauG := tauG) (deltaCap := deltaCap)
    (s := s) (N := N) (u := u) (v := v) (D := D)
    hE hs0 huIcc.1 huIcc.2 hv1 a
  have hPrefixRate0 :=
    APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
      E D s t zetaSrc tauG deltaWeight N k
  have hProfile0 : 0 ≤
      RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        zetaSrc tauG deltaWeight deltaCap N k a u := by
    unfold RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile
    positivity
  by_cases hk0 : k = 0
  · subst k
    have hrateZero : ∀ r, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
        E D deltaWeight s t N 0 a r = 0 := by
      intro r
      funext ω
      have hz := APrimeGeneralMovingJointMeasurable.jointRate_k_zero
        (E := E) (D := D) (deltaWeight := deltaWeight) (s := s) (t := t)
        hNpos Step2.sigPM a (cutNetPt s (mesh D) N 0) r
      have hzw := congrFun hz ω
      simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hzw]
    have hp0 : p ≠ 0 := by omega
    have hqpos : 0 < (↑p : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by positivity
    have hbudgetZero :
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N 0 p a u = 0 := by
      have hmoment : MomentDuhamel.momNorm (Gauss.P d) (2 * p)
          (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
            E D deltaWeight s t N 0 a u) = 0 := by
        unfold MomentDuhamel.momNorm
        simp [hrateZero, hqpos.ne']
        exact hp0
      unfold APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
      rw [hmoment]
      simp
    have hnonneg : 0 ≤
        K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          zetaSrc tauG deltaWeight deltaCap N 0 a u +
          Kbad * (N : ℝ)^(-1 : ℝ) / √u := by positivity
    change APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
      E D deltaWeight s t N 0 p a u ≤ _
    calc
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N 0 p a u = 0 := hbudgetZero
      _ ≤ K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N 0 a u +
          Kbad * (N : ℝ)^(-1 : ℝ) / √u := hnonneg
  · have hkpos : 1 ≤ k := by omega
    let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
    let Z : Gauss.Ω d → ℝ := fun ω =>
      APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
        Step2.sigPM a v u ω
    let Zgood : Gauss.Ω d → ℝ :=
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
        E D deltaWeight s t N k a u
    have hZi : Integrable (fun ω => |Z ω|^(2 * p)) (Gauss.P d) := by
      simpa [Z, v, m, mesh] using hJointN k hk Step2.sigPM a u hu
    have hGoodMeas : MeasurableSet (APrimeGeneralMovingGoodMesh.good N) :=
      APrimeGeneralMovingGoodMesh.measurableSet_good N
    have hZgoodPow : ∀ ω,
        |Zgood ω|^(2 * p) =
          (APrimeGeneralMovingGoodMesh.good N).indicator
            (fun ω => |Z ω|^(2 * p)) ω := by
      intro ω
      by_cases hω : ω ∈ APrimeGeneralMovingGoodMesh.good N
      · simp [Zgood, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
          Z, m, v, hω]
      · have hq : 2 * p ≠ 0 := by omega
        simp [Zgood, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
          Z, m, v, hω, hq]
    have hZgoodInt : Integrable (fun ω => |Zgood ω|^(2 * p)) (Gauss.P d) := by
      refine (hZi.indicator hGoodMeas).congr
        (Filter.Eventually.of_forall fun ω => ?_)
      exact (hZgoodPow ω).symm
    have hPowBound : ∀ ω, |Zgood ω|^(2 * p) ≤ |Z ω|^(2 * p) := by
      intro ω
      by_cases hω : ω ∈ APrimeGeneralMovingGoodMesh.good N
      · simp [Zgood, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
          Z, m, v, hω]
      · have hq : 2 * p ≠ 0 := by omega
        simp [Zgood, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
          Z, m, v, hω, hq]
    have hIntCompare := integral_mono hZgoodInt hZi hPowBound
    have hMomCompare :
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ≤
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z := by
      unfold MomentDuhamel.momNorm
      exact Real.rpow_le_rpow
        (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _)
        hIntCompare (by positivity)
    have hEnvAll : ∀ ω,
        APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
            (mesh D) N k m ω *
          √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a
            (s N) v u ω) ≤
            APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
      intro ω
      have hh := hEnvJointN k hk Step2.sigPM a u hu ω
      simpa [m, mesh] using hh
    have hGoodPrefix : ∀ ω ∈ Ξ N ∩
        APrimeCrossJointSplit.transition d E D deltaWeight s
          (mesh D) N k m,
        APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
          (mesh D) N k m ω ≤
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k := by
      intro ω hω
      apply hPrefixN k hkpos hk ω
      simpa [Ξ, mesh, zetaSrc, zetaCtr, tauG, deltaWeight] using hω
    have hGoodQV : ∀ ω ∈ Ξ N ∩
        APrimeCrossJointSplit.transition d E D deltaWeight s
          (mesh D) N k m,
        APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v u ω ≤
          (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)^2 := by
      intro ω hω
      have hqv := hQVN k hkpos hk ω hω.1 hω.2 u hu a
      simpa [APrimeGeneralMovingQVProfile.generalMovingBlockCap,
        zetaSrc, zetaCtr, tauG, deltaWeight, xi, deltaCap, hdeltaEq] using hqv
    have hRho : 0 ≤ ((Gauss.P d) (Ξ N)ᶜ).toReal := ENNReal.toReal_nonneg
    have hEventNorm := APrimeCrossJointSplit.jointRate_norm_le_event
      d E D deltaWeight s (mesh D) N k m p Step2.sigPM a v u hNpos hp
      (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
        E D s t zetaSrc zetaCtr tauG N)
      (b := APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t zetaSrc tauG deltaWeight N k)
      (q := (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)^2)
      (Eall := APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N)
      (ρ := ((Gauss.P d) (Ξ N)ᶜ).toReal)
      hPrefixRate0 (sq_nonneg _) hEnv0 hRho hGoodPrefix hGoodQV hEnvAll
      (by simpa [Ξ] using hEnvPay) hZi
    have hFullNorm : MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k *
          APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
          (N : ℝ)^(-1 : ℝ) := by
      have hEventNormPay :
          (∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d)) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
            APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
            (N : ℝ)^(-1 : ℝ) := by
        have hEventNormZ :
            (∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d)) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
              APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                  E D s t zetaSrc tauG deltaWeight N k *
                Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
                  E s zetaSrc N u v D
                  (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)^2) +
              APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := by
          simpa [Z, m, v, mesh, Nat.cast_mul] using hEventNorm
        calc
          _ ≤ APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
                E s zetaSrc N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)^2) +
              APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := hEventNormZ
          _ = APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
              APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRoot0]
          _ ≤ _ := add_le_add le_rfl (by simpa [Ξ] using hEnvPay)
      simpa [MomentDuhamel.momNorm, Nat.cast_mul] using hEventNormPay
    have hGoodNorm :
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ≤
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
          (N : ℝ)^(-1 : ℝ) := hMomCompare.trans hFullNorm
    have hcoeff :
        APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √u) = Kbad / √u := by
      unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
      dsimp [Kbad]
      push_cast
      field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp)),
        (Real.sqrt_pos.2 huPos).ne']
      ring
    have hcoeff0 : 0 ≤ Kbad / √u := by dsimp [Kbad]; positivity
    have hBudgetPoint :
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a u ≤
          Kbad / √u *
            (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
              (N : ℝ)^(-1 : ℝ)) := by
      unfold APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
      rw [hcoeff]
      exact mul_le_mul_of_nonneg_left hGoodNorm hcoeff0
    have hProfilePoint :
        Kbad / √u *
            (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a) =
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N k a u := by
      change Kbad / √u *
          (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a) =
        K * ((2 * √u)⁻¹ *
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k *
          APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)
      have hsqrt : √u ≠ 0 := (Real.sqrt_pos.2 huPos).ne'
      dsimp [K, Kbad]
      field_simp [hsqrt]
      ring
    have hErrPoint : Kbad / √u * (N : ℝ)^(-1 : ℝ) =
        Kbad * (N : ℝ)^(-1 : ℝ) / √u := by ring
    calc
      _ ≤ Kbad / √u *
          (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
            (N : ℝ)^(-1 : ℝ)) := hBudgetPoint
      _ = _ := by
        rw [mul_add, hProfilePoint, hErrPoint]
        simp [K, Kbad, zetaSrc, zetaCtr, tauG, deltaWeight, deltaCap,
          sourceLoss, weightLoss, bufferLoss, capLoss]

set_option maxHeartbeats 1000000 in
/-- Integrating the free-loss event split gives the literal cross-profile
integral with its all-order coefficient and the norm-good complement payment.
The result is uniform on all active cells, including the zero cell. -/
theorem eventually_integral_normGoodCrossBudget_le_freeLossProfile_add_payment
    {E D c loss : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hloss : 0 < loss)
    (hsmall : loss ≤ min (1 / 10000 : ℝ) (c / 10000))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D loss s t N k p a r) ≤
            (15 * (p : ℝ) / 4) *
              (∫ r in (s N)..v,
                RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                  (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r) +
            (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
              (√v - √(s N)) := by
  have hlossnonneg : 0 ≤ loss := hloss.le
  have hpoint := eventually_normGoodCrossBudget_le_freeLossProfile_add_payment
    hE hD hs0 hst ht1 hc hreg hB hloss hsmall p hp
  have hgoodInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hlossnonneg p hp
  filter_upwards [hpoint, hgoodInt, eventually_ge_atTop 1]
    with N hpointN hgoodIntN hN
  have hNpos : 0 < N := by omega
  let K : ℝ := 15 * (p : ℝ) / 4
  let Kbad : ℝ := 15 * (p : ℝ) / 8
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKbad0 : 0 ≤ Kbad := by dsimp [Kbad]; positivity
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hsv : s N ≤ v := hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hProfileInt := intervalIntegrable_crossProfile_local
    (E := E) (D := D) (s := s) (t := t)
    (zetaSrc := sourceLoss loss) (tauG := sourceLoss loss)
    (deltaWeight := loss) (deltaCap := 2 * loss)
    hE hs0 hst ht1 hk a
  have hGoodInt := hgoodIntN k hk a
  have hPaymentInt : IntervalIntegrable
      (fun r : ℝ => Kbad * (N : ℝ)^(-1 : ℝ) / √r) volume (s N) v :=
    APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      (Kbad * (N : ℝ)^(-1 : ℝ)) (s N) v (hs0 N) hsv
  have hRhsInt : IntervalIntegrable
      (fun r => K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r +
        Kbad * (N : ℝ)^(-1 : ℝ) / √r)
      volume (s N) v := (hProfileInt.const_mul K).add hPaymentInt
  have hpointwise : ∀ r ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D loss s t N k p a r ≤
        K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r +
          Kbad * (N : ℝ)^(-1 : ℝ) / √r := by
    intro r hr
    have hr0 : 0 ≤ r := (hs0 N).trans hr.1
    by_cases hrpos : 0 < r
    · have h := hpointN k hk a r (by simpa [v] using hr) hrpos
      simpa [K, Kbad] using h
    · have hrEq : r = 0 := le_antisymm (le_of_not_gt hrpos) hr0
      subst r
      simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
        RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile]
  have hmono := intervalIntegral.integral_mono_on hsv hGoodInt hRhsInt hpointwise
  have hPaymentEval :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      (Kbad * (N : ℝ)^(-1 : ℝ)) (s N) v (hs0 N) hsv
  have hfinal :
      (∫ r in (s N)..v,
        K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r +
        Kbad * (N : ℝ)^(-1 : ℝ) / √r) =
      (15 * (p : ℝ) / 4) *
          (∫ r in (s N)..v,
            RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (√v - √(s N)) := by
    rw [intervalIntegral.integral_add (hProfileInt.const_mul K) hPaymentInt,
      intervalIntegral.integral_const_mul, hPaymentEval]
    simp only [K, Kbad]
    dsimp [v]
    ring_nf
  change (∫ r in (s N)..v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D loss s t N k p a r) ≤ _
  rw [← hfinal]
  exact hmono

set_option maxHeartbeats 1000000 in
/-- The literal full positive-time cross budget is bounded by the exact
free-loss cross-profile integral.  The two `(15 p / 4) N⁻¹` endpoint payments
are kept separate: one is the common-event complement from the norm-good
split, and the other is the norm-bad contribution in T1207. -/
theorem eventually_integral_positiveTimeCrossBudget_le_freeLossProfile_add_two_payments
    {E D c loss : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hloss : 0 < loss)
    (hsmall : loss ≤ min (1 / 10000 : ℝ) (c / 10000))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D loss s t N k p a r) ≤
          (15 * (p : ℝ) / 4) *
              (∫ r in (s N)..v,
                RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                  (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r) +
            (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
              (√v - √(s N)) +
            (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
              (√v - √(s N)) := by
  have hgood := eventually_integral_normGoodCrossBudget_le_freeLossProfile_add_payment
    hE hD hs0 hst ht1 hc hreg hB hloss hsmall p hp
  have hsplit :=
    APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      hE hD hs0 hst ht1 hc hreg hloss.le p hp
  filter_upwards [hgood, hsplit] with N hgoodN hsplitN
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hgoodBound := hgoodN k hk a
  have hsplitBound := hsplitN k hk a
  change (∫ r in (s N)..v,
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D loss s t N k p a r) ≤ _
  calc
    _ ≤ (∫ r in (s N)..v,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D loss s t N k p a r) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (√v - √(s N)) := by simpa [v] using hsplitBound
    _ ≤ (15 * (p : ℝ) / 4) *
          (∫ r in (s N)..v,
            RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              (sourceLoss loss) (sourceLoss loss) loss (2 * loss) N k a r) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (√v - √(s N)) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (√v - √(s N)) := by
      simpa [v] using add_le_add_right hgoodBound
        ((15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) * (√v - √(s N)))

/-! This witness realizes the new source-loss schedule on the same sample as
the literal common event and a strictly positive actual smooth weight. -/
theorem nondegenerate_free_loss_positive_cell_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧ Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ loss : ℝ, 0 < loss → loss ≤ min (1 / 10000 : ℝ) (c / 10000) →
        ∀ᶠ N : ℕ in atTop,
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
              (sourceLoss loss) (sourceLoss loss) (sourceLoss loss) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 loss s t (mesh 60)
              2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hresident⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro loss hloss hsmall
  have hsource := hresident (sourceLoss loss) (sourceLoss loss) (sourceLoss loss) loss
    (by dsimp [sourceLoss]; positivity)
    (by dsimp [sourceLoss]; positivity)
    (by dsimp [sourceLoss]; positivity)
    hloss
  filter_upwards [hsource] with N hN
  obtain ⟨_hwindow, ω, hω, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (mesh 60)) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
        s t (mesh 60) loss 1 N 1 ω = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := loss) (s := s) (t := t) (mesh := mesh 60)
    (by norm_num) hloss.le N 1 1 ω (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos : 0 < APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t (mesh 60)) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
      s t (mesh 60) loss 1 N 1 ω := by
    rw [hwideOne]
    norm_num
  exact ⟨ω, hω, hactive, hwidePos.trans_le hcompare⟩

/-- An explicit positive loss realizes the witness above: choose half the
smallness ceiling, so the admissible loss range is formally nonempty. -/
theorem exists_explicit_free_loss_positive_cell_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧ Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∃ loss : ℝ, 0 < loss ∧
        loss ≤ min (1 / 10000 : ℝ) (c / 10000) ∧
        ∀ᶠ N : ℕ in atTop,
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
              (sourceLoss loss) (sourceLoss loss) (sourceLoss loss) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 loss s t (mesh 60)
              2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hForall⟩ :=
    nondegenerate_free_loss_positive_cell_witness
  let loss : ℝ := min (1 / 20000 : ℝ) (c / 20000)
  have hloss : 0 < loss := by
    dsimp [loss]
    exact lt_min (by norm_num) (by positivity)
  have hsmall : loss ≤ min (1 / 10000 : ℝ) (c / 10000) := by
    apply le_min
    · dsimp [loss]
      calc
        min (1 / 20000 : ℝ) (c / 20000) ≤ 1 / 20000 := min_le_left _ _
        _ ≤ 1 / 10000 := by norm_num
    · dsimp [loss]
      calc
        min (1 / 20000 : ℝ) (c / 20000) ≤ c / 20000 := min_le_right _ _
        _ ≤ c / 10000 := by nlinarith [hc]
  exact ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    loss, hloss, hsmall, hForall loss hloss hsmall⟩

#print axioms eventually_normGoodCrossBudget_le_freeLossProfile_add_payment
#print axioms eventually_integral_normGoodCrossBudget_le_freeLossProfile_add_payment
#print axioms eventually_integral_positiveTimeCrossBudget_le_freeLossProfile_add_two_payments
#print axioms nondegenerate_free_loss_positive_cell_witness
#print axioms exists_explicit_free_loss_positive_cell_witness

end
end RBM.APrimeFreeLossCrossEventSplit
