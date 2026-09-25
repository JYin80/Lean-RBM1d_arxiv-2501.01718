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
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot

/-!
# T1215: all-fixed-order norm-good moving cross-budget slot

The proof splits the literal transition-indicated joint rate on the same
T995 common event used by the accepted prefix and QV producers.  On that
event, transition membership gives the pointwise favorable profile.  On its
complement, T617's all-sample envelope is paid by the arbitrary-order
`HighProb` bound.  The argument works at `q = 2p` with `p` fixed before the
eventual matrix-size cutoff.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetNormGoodAllOrdersSlot

open Filter MeasureTheory Set Gauss CutHypTheta
open Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

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
/-- For each fixed `p ≥ 1`, the actual T1201 norm-good cross budget on every
active moving target-mesh cell has the T995 small-slot bound.  The constant
is chosen before the eventual cutoff and is independent of `N`, `k`, and `a`.
The exact moving endpoint and literal norm-good restriction are retained. -/
theorem eventually_integral_normGoodCrossBudget_allOrders_le_small_slot
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k p a r) ≤
            C * (N : ℝ)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
  let zetaSrc := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ
  let zetaCtr := APrimeGeneralMovingSlotLossSchedule.zetaCtr δ
  let tauG := APrimeGeneralMovingSlotLossSchedule.tauG δ
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  let xi := APrimeGeneralMovingSlotLossSchedule.xi δ
  let deltaCap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  let Ξ : ℕ → Set (Gauss.Ω d) := fun N =>
    APrimeGeneralMovingCommonSources.commonEvent E D s t zetaSrc zetaCtr tauG N
  let K : ℝ := 15 * (p : ℝ) / 4
  let Kbad : ℝ := 15 * (p : ℝ) / 8
  let C : ℝ := K *
    (|RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| + 2)
  have hrooms := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hrooms with ⟨hdw, hxi, hcap, htau, hzsrc, hzctr, hbuffer,
      hzsrcTau, htauCap, hcapC, hcapRoom, _, _⟩
  have hdeltaEq : deltaWeight + xi = deltaCap := by
    change δ / 100 + δ / 100 = δ / 50
    ring
  have hprefixTau : tauG ≤ deltaWeight / 16 := by
    change δ / 1600 ≤ (δ / 100) / 16
    nlinarith
  have hprefixC : deltaWeight ≤ c / 20 := by
    change δ / 100 ≤ c / 20
    have hδc : δ ≤ c / 100 := hδsmall.trans (min_le_right 1 (c / 100))
    nlinarith
  have hprefixRoom : tauG + 2 * deltaWeight + (2 : ℝ) / 15 < 1 := by
    change δ / 1600 + 2 * (δ / 100) + (2 : ℝ) / 15 < 1
    have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left 1 (c / 100))
    nlinarith
  have hHP : HighProb (Gauss.P d) Ξ := by
    exact APrimeGeneralMovingCommonSources.highProb_commonEvent
      hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG hzsrc hzctr htau
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
      hE hD hs0 hst ht1 hc hreg hB hzsrc hzctr htau hdw hzsrcTau
      hprefixTau hprefixC hprefixRoom
  have hQV :=
    let htauCap' : tauG ≤ (deltaWeight + xi) / 16 := by
      calc
        tauG ≤ deltaCap / 16 := htauCap
        _ = (deltaWeight + xi) / 16 := by rw [hdeltaEq]
    let hcapC' : deltaWeight + xi ≤ c / 20 := by
      rw [hdeltaEq]
      exact hcapC
    let hcapRoom' : tauG + 2 * (deltaWeight + xi) + (2 : ℝ) / 15 < 1 := by
      rw [hdeltaEq]
      exact hcapRoom
    APrimeGeneralMovingTransitionQV.eventually_qv_le_absorbed_on_smooth_transition_buffered
      hE hD hs0 hst ht1 hc hreg hB hzsrc hzctr htau hxi
      (by rw [hdeltaEq]; exact hcap) hzsrcTau
      htauCap' hcapC' hcapRoom'
  have hCrossProfile :=
    RBM.APrimeGeneralMovingCrossProfileSlot.eventually_integral_crossProfile_le_small_slot
      (E := E) (D := D) (s := s) (t := t) (δ := δ)
      hE (by linarith) hs0 hst ht1 hc hreg hδ hδsmall
  have hBudgetInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdw.le p hp
  have hThirty := hreg.1.pow_thirty_le hE hst ht1
  have hCpos : 0 < C := by
    dsimp [C, K]
    positivity
  refine ⟨C, hCpos, ?_⟩
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hCrossProfile, hBudgetInt,
      hThirty, hEnvPoly, hEnvJoint, B.dim, eventually_ge_atTop 1]
    with N hPayN hJointN hPrefixN hQVN hCrossN hBudgetN hThirtyN hEnvN
      hEnvJointN hdim hN
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay :
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
          ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
        (N : ℝ)^(-1 : ℝ) := by
    simpa [Ξ] using hPayN
  have hCrossScale : 0 ≤ K := by dsimp [K]; positivity
  have hKbad : 0 ≤ Kbad := by dsimp [Kbad]; positivity
  intro k hk a
  by_cases hk0 : k = 0
  · subst k
    let v0 := cutNetPt s (mesh D) N 0
    have hv0 : v0 ∈ Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
    have hrateZero : ∀ r, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
        E D deltaWeight s t N 0 a r = 0 := by
      intro r
      funext ω
      have hz := RBM.APrimeGeneralMovingJointMeasurable.jointRate_k_zero
        (E := E) (D := D) (deltaWeight := deltaWeight) (s := s) (t := t)
        hNpos Step2.sigPM a v0 r
      have hzw := congrFun hz ω
      simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, v0, hzw]
    have hbudgetZero : ∀ r, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D deltaWeight s t N 0 p a r = 0 := by
      intro r
      have hp0 : p ≠ 0 := by omega
      have hqpos : 0 < (↑p : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by positivity
      have hmoment : MomentDuhamel.momNorm (Gauss.P d) (2 * p)
          (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
            E D deltaWeight s t N 0 a r) = 0 := by
        unfold MomentDuhamel.momNorm
        simp [hrateZero, hqpos.ne']
        exact hp0
      unfold APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
      rw [hmoment]
      simp
    have hfun : (fun r => APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D deltaWeight s t N 0 p a r) = fun _ => 0 := by
      funext r
      exact hbudgetZero r
    rw [hfun]
    have hR0 : 0 < Step2Moment.ratR E s N v0 :=
      Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N))
        (hv0.2.trans_lt (ht1 N))
    have hNpow : 0 ≤ (N : ℝ)^(5 * δ / 32) :=
      Real.rpow_nonneg (by positivity) _
    have hRpow : 0 ≤ Step2Moment.ratR E s N v0^(-(2 : ℝ)) :=
      Real.rpow_nonneg hR0.le _
    have hTargetNonneg : 0 ≤ C * (N : ℝ)^(5 * δ / 32) *
        Step2Moment.ratR E s N v0^(-(2 : ℝ)) :=
      mul_nonneg (mul_nonneg hCpos.le hNpow) hRpow
    simpa using hTargetNonneg
  · have hkpos : 1 ≤ k := by omega
    let v := cutNetPt s (mesh D) N k
    have hv : v ∈ Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
    have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
    have hv0 : 0 ≤ v := (hs0 N).trans hv.1
    have hBudget : IntervalIntegrable
        (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k p a) volume (s N) v := by
      simpa [v, deltaWeight] using hBudgetN k hk a
    have hCrossInt : IntervalIntegrable
        (RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          zetaSrc tauG deltaWeight deltaCap N k a)
          volume (s N) v := by
      exact intervalIntegrable_crossProfile_local hE hs0 hst ht1 hk a
    have hBaseInt : IntervalIntegrable (fun r : ℝ => (1 : ℝ) / √r)
        volume (s N) v := by
      simpa [one_div] using
        (APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
          1 (s N) v (hs0 N) hv.1)
    have hRightInt : IntervalIntegrable
        (fun r : ℝ => K *
          RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N k a r +
          Kbad * (N : ℝ)^(-1 : ℝ) / √r) volume (s N) v := by
      exact (hCrossInt.const_mul K).add
        ((APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
          (Kbad * (N : ℝ)^(-1 : ℝ)) (s N) v (hs0 N) hv.1))
    have hRpos : 0 < Step2Moment.ratR E s N v :=
      Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
    have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
      Step2Moment.one_le_ratR hE hv.1 hv1
    let hvTime : TimeIcc s t N := ⟨v, hv⟩
    have hR30 : (Step2Moment.ratR E s N v) ^ (30 : ℕ) ≤ B.scale E N v := by
      have hh := hThirtyN hvTime
      simpa only [Step2Moment.ratR] using hh
    have hScaleN : B.scale E N v ≤ (N : ℝ) := by
      obtain ⟨_, _, hEtaLe, _, hEllL⟩ := EEBridge.eeFacts B hE hs0 ht1 N hvTime
      have hEtaLeV : etaT E v ≤ 1 := by simpa [hvTime] using hEtaLe
      have hEllLv : B.ell N v ≤ B.L N := by simpa [hvTime] using hEllL
      have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hdim.1
      change (B.W N : ℝ) * B.ell N v * etaT E v ≤ (N : ℝ)
      calc
        (B.W N : ℝ) * B.ell N v * etaT E v ≤
            (B.W N : ℝ) * ((B.L N : ℝ) * etaT E v) := by
          have hW : (0 : ℝ) ≤ B.W N := by positivity
          have hEta : 0 ≤ etaT E v := by positivity
          calc
            (B.W N : ℝ) * B.ell N v * etaT E v =
                (B.W N : ℝ) * (B.ell N v * etaT E v) := by ring
            _ ≤ (B.W N : ℝ) * ((B.L N : ℝ) * etaT E v) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hEllLv hEta) hW
        _ ≤ (B.W N : ℝ) * ((B.L N : ℝ) * 1) := by
          have hW : (0 : ℝ) ≤ B.W N := by positivity
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEtaLeV (by positivity)) hW
        _ = (B.W N : ℝ) * (B.L N : ℝ) := by ring
        _ ≤ (N : ℝ) := hWL
    have hR28 : (1 : ℝ) ≤ (Step2Moment.ratR E s N v) ^ (28 : ℕ) :=
      one_le_pow₀ hR1
    have hR2Nat : (Step2Moment.ratR E s N v) ^ (2 : ℕ) ≤ (N : ℝ) := by
      have hpow : (Step2Moment.ratR E s N v) ^ (2 : ℕ) ≤
          (Step2Moment.ratR E s N v) ^ (30 : ℕ) := by
        calc
          _ = Step2Moment.ratR E s N v ^ 2 * 1 := by simp
          _ ≤ Step2Moment.ratR E s N v ^ 2 *
                Step2Moment.ratR E s N v ^ (28 : ℕ) :=
            mul_le_mul_of_nonneg_left hR28 (sq_nonneg _)
          _ = _ := by rw [← pow_add]
      exact hpow.trans (hR30.trans hScaleN)
    have hR2 : (Step2Moment.ratR E s N v) ^ (2 : ℝ) ≤ (N : ℝ) := by
      have heq : (Step2Moment.ratR E s N v) ^ (2 : ℝ) =
          (Step2Moment.ratR E s N v) ^ (2 : ℕ) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast (Step2Moment.ratR E s N v) 2)
      rw [heq]
      exact hR2Nat
    have hTargetError : (N : ℝ)^(-1 : ℝ) ≤
        (N : ℝ)^(5 * δ / 32) *
          Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
      have hR2pos : 0 < Step2Moment.ratR E s N v ^ (2 : ℝ) :=
        Real.rpow_pos_of_pos hRpos _
      have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hNeps : 1 ≤ (N : ℝ)^(5 * δ / 32) :=
        Real.one_le_rpow hN1 (by positivity)
      have hcross : Step2Moment.ratR E s N v ^ (2 : ℝ) ≤
          (N : ℝ)^(5 * δ / 32) * (N : ℝ) := by
        calc
          _ ≤ (N : ℝ) := hR2
          _ ≤ (N : ℝ)^(5 * δ / 32) * (N : ℝ) := by
            nlinarith [mul_le_mul_of_nonneg_right hNeps hNposR.le]
      have hdiv : 1 / (N : ℝ) ≤
          (N : ℝ)^(5 * δ / 32) / Step2Moment.ratR E s N v ^ (2 : ℝ) := by
        apply (div_le_div_iff₀ hNposR hR2pos).2
        simpa only [one_mul] using hcross
      have hNinv : (N : ℝ)^(-1 : ℝ) = 1 / (N : ℝ) := by
        rw [Real.rpow_neg hNposR.le, Real.rpow_one, inv_eq_one_div]
      have hRinv : Step2Moment.ratR E s N v^(-(2 : ℝ)) =
          1 / Step2Moment.ratR E s N v ^ (2 : ℝ) := by
        rw [Real.rpow_neg hRpos.le, Real.rpow_two, inv_eq_one_div]
      calc
        _ = 1 / (N : ℝ) := hNinv
        _ ≤ (N : ℝ)^(5 * δ / 32) /
            Step2Moment.ratR E s N v ^ (2 : ℝ) := hdiv
        _ = (N : ℝ)^(5 * δ / 32) *
            Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
          rw [hRinv]
          ring
    have hSqrtDiff : Real.sqrt v - Real.sqrt (s N) ≤ 1 := by
      have hSqrtV : Real.sqrt v ≤ 1 := by
        apply Real.sqrt_le_one.mpr
        linarith [hv1]
      have hSqrtS : 0 ≤ Real.sqrt (s N) := Real.sqrt_nonneg _
      linarith
    have hErrorIntegral :
        (∫ r in (s N)..v, Kbad * (N : ℝ)^(-1 : ℝ) / √r) ≤
          K * (N : ℝ)^(-1 : ℝ) := by
      rw [APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
        (Kbad * (N : ℝ)^(-1 : ℝ)) (s N) v (hs0 N) hv.1]
      dsimp [K, Kbad]
      have hnonneg : 0 ≤ 2 * (15 * (p : ℝ) / 8 * (N : ℝ)^(-1 : ℝ)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hSqrtDiff hnonneg]
    have hpoint : ∀ r ∈ Icc (s N) v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r ≤
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              zetaSrc tauG deltaWeight deltaCap N k a r +
            Kbad * (N : ℝ)^(-1 : ℝ) / √r := by
      intro r hr
      have hr0 : 0 ≤ r := (hs0 N).trans hr.1
      by_cases hrpos : 0 < r
      · let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
        let Z : Gauss.Ω d → ℝ := fun ω =>
          APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
            Step2.sigPM a v r ω
        let Zgood : Gauss.Ω d → ℝ :=
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
            E D deltaWeight s t N k a r
        have hZi : Integrable (fun ω => |Z ω|^(2 * p)) (Gauss.P d) := by
          simpa [Z, v, m, mesh] using hJointN k hk Step2.sigPM a r hr
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
        have hZnonneg : ∀ ω, 0 ≤ Z ω := by
          intro ω
          exact APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
            (mesh D) N k m Step2.sigPM a v r hNpos ω
        have hPowBound : ∀ ω, |Zgood ω|^(2 * p) ≤ |Z ω|^(2 * p) := by
          intro ω
          by_cases hω : ω ∈ APrimeGeneralMovingGoodMesh.good N
          · simp [Zgood, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
              Z, m, v, hω]
          · have hq : 2 * p ≠ 0 := by omega
            simp [Zgood, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
              Z, m, v, hω, hq]
        have hIntCompare := integral_mono hZgoodInt hZi hPowBound
        have hIntNonneg : 0 ≤ ∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d) :=
          integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _
        have hMomCompare :
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ≤
              MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z := by
          unfold MomentDuhamel.momNorm
          exact Real.rpow_le_rpow
            (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _)
            hIntCompare (by positivity)
        have hprefixRate :=
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
            E D s t zetaSrc tauG deltaWeight N k
        have hRoot0 : 0 ≤
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a := by
          unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
          have hRu : 0 < Step2Moment.ratR E s N r :=
            Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N))
              (hr.2.trans_lt hv1)
          have hRv : 0 < Step2Moment.ratR E s N v := hRpos
          have hW : 0 < B.W N := by exact_mod_cast B.W_pos N
          have hEll : 0 < B.ell N r := by
            have hru1 : r < 1 := hr.2.trans_lt hv1
            exact zero_lt_one.trans_le
              (one_le_ellHat_of_nonneg (B.one_le_L N) hr0 hru1)
          have hEta : 0 < etaT E r := Step2.etaT_pos' hE (hr.2.trans_lt hv1)
          have hJ : 0 ≤ APrimeGeneralMovingQVProfile.generalMovingBlockCap
              E s tauG deltaCap N r := by
            unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
            positivity
          have hnear : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate
              E s zetaSrc N r + 2 * (B.W N : ℝ)⁻¹ := by
            unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
            have hEllS : 0 < B.ell N (s N) := by
              exact zero_lt_one.trans_le (one_le_ellHat_of_nonneg
                (B.one_le_L N) (hs0 N) ((hst N).trans_lt (ht1 N)))
            have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
            have hcNear : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) (B.ell N r) :=
              Lemma57.cNear2_nonneg hW1 hEll
            positivity
          have hfar : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate
              E N r (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) := by
            unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
            have hscale : 0 < B.scale E N r := by
              change 0 < (B.W N : ℝ) * B.ell N r * etaT E r
              positivity
            have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
                6 * ellStar (B.W N : ℝ) (B.ell N v) then (1 : ℝ) else 0) := by
              split_ifs <;> norm_num
            positivity
          have hxi : 0 ≤ Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im :=
            Step2.xiK_nonneg _ _ _
          positivity
        have hq0 : 0 ≤
            (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2 :=
          sq_nonneg _
        have hEnvAll : ∀ ω, APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
            (mesh D) N k m ω *
            √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v r ω) ≤
              APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
          intro ω
          have hh := hEnvJointN k hk Step2.sigPM a r hr ω
          simpa [m, mesh] using hh
        have hGoodPrefix : ∀ ω ∈ Ξ N ∩
            APrimeCrossJointSplit.transition d E D deltaWeight s
              (mesh D) N k m,
            APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
              (mesh D) N k m ω ≤
                APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                  E D s t zetaSrc tauG deltaWeight N k := by
          intro ω hω
          apply hPrefixN k (by omega) hk ω
          simpa [Ξ, mesh, deltaWeight] using hω
        have hGoodQV : ∀ ω ∈ Ξ N ∩
            APrimeCrossJointSplit.transition d E D deltaWeight s
              (mesh D) N k m,
            APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v r ω ≤
              (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2 := by
          intro ω hω
          have hqv := hQVN k (by omega) hk ω hω.1 hω.2 r hr a
          simpa [APrimeGeneralMovingQVProfile.generalMovingBlockCap,
            deltaWeight, xi, deltaCap, tauG, zetaSrc, hbuffer] using hqv
        have hRho : 0 ≤ ((Gauss.P d) (Ξ N)ᶜ).toReal := ENNReal.toReal_nonneg
        have hEventNorm := APrimeCrossJointSplit.jointRate_norm_le_event
          d E D deltaWeight s (mesh D) N k m p Step2.sigPM a v r hNpos hp
          (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
            E D s t zetaSrc zetaCtr tauG N)
          (b := APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k)
          (q := (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2)
          (Eall := APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N)
          (ρ := ((Gauss.P d) (Ξ N)ᶜ).toReal)
          hprefixRate hq0 hEnv0 hRho hGoodPrefix hGoodQV hEnvAll le_rfl hZi
        have hFullNorm : MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤
            APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
              (N : ℝ)^(-1 : ℝ) := by
          have hEventNormPay :
              (∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d)) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
                APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                    E D s t zetaSrc tauG deltaWeight N k *
                  APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
                  (N : ℝ)^(-1 : ℝ) := by
            have hEventNormZ :
                (∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d)) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
                  APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                      E D s t zetaSrc tauG deltaWeight N k *
                    Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
                      E s zetaSrc N r v D
                      (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2) +
                    APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                      ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := by
              simpa [Z, m, v, mesh, Nat.cast_mul] using hEventNorm
            calc
              _ ≤ APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                    E D s t zetaSrc tauG deltaWeight N k *
                  Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
                    E s zetaSrc N r v D
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2) +
                  APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                    ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := hEventNormZ
              _ = APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                    E D s t zetaSrc tauG deltaWeight N k *
                  APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
                  APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                    ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := by
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRoot0]
              _ ≤ _ := add_le_add le_rfl hEnvPay
          simpa [MomentDuhamel.momNorm, Nat.cast_mul] using hEventNormPay
        have hgoodNorm :
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ≤
              APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
                APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                  (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
              (N : ℝ)^(-1 : ℝ) := hMomCompare.trans hFullNorm
        have hcoefEq :
            APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ) * √r) = Kbad / √r := by
          unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
          dsimp [Kbad]
          push_cast
          field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp)),
            (Real.sqrt_pos.2 hrpos).ne']
          ring
        have hcoef0 : 0 ≤ Kbad / √r := by dsimp [Kbad]; positivity
        have hBudgetPoint :
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
                E D deltaWeight s t N k p a r ≤
              Kbad / √r *
                (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                  E D s t zetaSrc tauG deltaWeight N k *
                  APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
                  (N : ℝ)^(-1 : ℝ)) := by
          unfold APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          rw [hcoefEq]
          exact mul_le_mul_of_nonneg_left hgoodNorm hcoef0
        have hProfilePoint :
            Kbad / √r *
                (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                  E D s t zetaSrc tauG deltaWeight N k *
                  APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a) =
              K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                zetaSrc tauG deltaWeight deltaCap N k a r := by
          change Kbad / √r *
              (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
                APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                  (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a) =
            K * ((2 * √r)⁻¹ *
              APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)
          have hsqrt : √r ≠ 0 := (Real.sqrt_pos.2 hrpos).ne'
          dsimp [K, Kbad]
          field_simp [hsqrt]
          ring
        have hErrPoint : Kbad / √r * (N : ℝ)^(-1 : ℝ) =
            Kbad * (N : ℝ)^(-1 : ℝ) / √r := by ring
        calc
          _ ≤ Kbad / √r *
              (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
                APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
                  (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
                (N : ℝ)^(-1 : ℝ)) := hBudgetPoint
          _ = _ := by rw [mul_add, hProfilePoint, hErrPoint]
      · have hrEq : r = 0 := le_antisymm (not_lt.mp hrpos) hr0
        subst r
        simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
          RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile]
    have hIntMono := intervalIntegral.integral_mono_on hv.1 hBudget hRightInt hpoint
    have hCrossSmall := hCrossN k hk a
    have hCrossSmall' :
        (∫ r in (s N)..v,
          RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N k a r) ≤
          RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
            ((N : ℝ)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) := by
      simpa [v, zetaSrc, tauG, deltaWeight, deltaCap, mul_assoc] using hCrossSmall
    have hProfileTerm :
        (∫ r in (s N)..v,
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N k a r) ≤
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
            (N : ℝ)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul]
      calc
        _ ≤ K * (RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
            ((N : ℝ)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hCrossSmall' hCrossScale
        _ = _ := by ring
    have hRightIntegral :
        (∫ r in (s N)..v,
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N k a r +
          Kbad * (N : ℝ)^(-1 : ℝ) / √r) ≤
          C * (N : ℝ)^(5 * δ / 32) *
            Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
      rw [intervalIntegral.integral_add (hCrossInt.const_mul K)
          (APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
            (Kbad * (N : ℝ)^(-1 : ℝ)) (s N) v (hs0 N) hv.1),
        intervalIntegral.integral_const_mul]
      let q : ℝ := (N : ℝ)^(5 * δ / 32) *
        Step2Moment.ratR E s N v^(-(2 : ℝ))
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hCoeff :
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E + K ≤ C := by
        have hcp : RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E + 1 ≤
            |RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| + 2 := by
          linarith [le_abs_self
            (RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E)]
        calc
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E + K =
              K * (RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E + 1) := by ring
          _ ≤ K * (|RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| + 2) :=
            mul_le_mul_of_nonneg_left hcp hCrossScale
          _ = C := by dsimp [C]
      have hProfileTerm' :
          K * (∫ r in (s N)..v,
            RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              zetaSrc tauG deltaWeight deltaCap N k a r) ≤
            K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E * q := by
        rw [← intervalIntegral.integral_const_mul]
        simpa [q, mul_assoc] using hProfileTerm
      have hError' :
          (∫ r in (s N)..v, Kbad * (N : ℝ)^(-1 : ℝ) / √r) ≤ K * q := by
        calc
          _ ≤ K * (N : ℝ)^(-1 : ℝ) := hErrorIntegral
          _ ≤ K * q := mul_le_mul_of_nonneg_left hTargetError hCrossScale
      have hCombine :
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E * q +
            K * q ≤ C * q := by
        calc
          _ = (K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E + K) * q := by ring
          _ ≤ C * q := mul_le_mul_of_nonneg_right hCoeff hq0
      calc
        _ ≤ K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E * q +
              K * q := add_le_add hProfileTerm' hError'
        _ ≤ C * q := hCombine
        _ = _ := by dsimp [q]; ring
    change (∫ r in (s N)..v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k p a r) ≤
        C * (N : ℝ)^(5 * δ / 32) *
          Step2Moment.ratR E s N v^(-(2 : ℝ))
    exact hIntMono.trans hRightIntegral

/-! The inherited T995 witness realizes the scheduled numerical and
regularity assumptions, BoundsCore, and a positive common-event cell. -/
noncomputable abbrev nondegenerate_scheduled_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_integral_normGoodCrossBudget_allOrders_le_small_slot
#print axioms nondegenerate_scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingCrossBudgetNormGoodAllOrdersSlot
