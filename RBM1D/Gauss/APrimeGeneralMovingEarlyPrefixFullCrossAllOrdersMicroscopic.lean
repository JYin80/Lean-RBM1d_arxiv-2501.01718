/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodAllOrdersSlot
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot

/-!
# T1281: all-order full cross-budget integral on an early moving prefix

This is a fixed-order smooth-prefix auxiliary bound. It composes the accepted
T1207, T1215, T1245, and T995 producers. It is not the stopped estimate from
the paper and proves neither N1 nor a general A-prime conclusion.
-/

namespace RBM.APrimeGeneralMovingEarlyPrefixFullCrossAllOrdersMicroscopic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open RBM.MomentDuhamel
open RBM.APrimeGeneralMovingCrossBudgetGoodReduction
open RBM.APrimeGeneralMovingCrossHcrossPositive
open RBM.APrimeGeneralMovingCrossEnvelopeIntegral

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's same-event, nondegenerate active first-positive-cell witness. -/
noncomputable abbrev nondegenerate_positive_first_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- The first positive index of the T995 D=60 witness is in its growing
prefix range eventually. -/
theorem eventually_one_le_N_rpow_sixty :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ)^(60 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Real.one_le_rpow hNreal (by norm_num : (0 : ℝ) ≤ (60 : ℝ))

set_option maxHeartbeats 1000000 in
-- The same-event moment split expands a large family of Gaussian rate definitions.
/-- The accepted T1215 all-order norm-good pointwise bridge, with its internal
same-event argument made explicit for the microscopic prefix consumer. -/
theorem eventually_pointwise_normGoodCrossBudget_le_crossProfile_add_error_allOrders
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k →
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2, ∀ r : ℝ,
        r ∈ Icc (s N) (cutNetPt s (mesh D) N k) →
        0 < r →
        normGoodCrossBudget E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r ≤
          (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a r +
            (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt r := by
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
  have hQV := by
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
    exact APrimeGeneralMovingTransitionQV.eventually_qv_le_absorbed_on_smooth_transition_buffered
      hE hD hs0 hst ht1 hc hreg hB hzsrc hzctr htau hxi
      (by rw [hdeltaEq]; exact hcap) hzsrcTau htauCap' hcapC' hcapRoom'
  have hEnvJointPoly :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdw.le
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hEnvPoly, hEnvJointPoly,
      B.dim, eventually_ge_atTop 1]
    with N hPayN hJointN hPrefixN hQVN hEnvN hEnvJointN hdim hN
  have hNpos : 0 < N := by omega
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay :
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
          ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) ≤
        (N : ℝ)^(-1 : ℝ) := by
    simpa [Ξ] using hPayN
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKbad : 0 ≤ Kbad := by dsimp [Kbad]; positivity
  intro k hkpos hk a r hr hrpos
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hv1
  let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
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
    have hW : 0 < B.W N := by exact_mod_cast B.W_pos N
    have hEll : 0 < B.ell N r := by
      exact zero_lt_one.trans_le
        (one_le_ellHat_of_nonneg (B.one_le_L N) hrpos.le (hr.2.trans_lt hv1))
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
  have hEnvAll : ∀ ω,
      APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
          (mesh D) N k m ω *
        √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v r ω) ≤
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
    intro ω
    have hh := hEnvJointN k hk Step2.sigPM a r hr ω
    simpa [m, mesh] using hh
  have hGoodPrefix : ∀ ω ∈ Ξ N ∩
      APrimeCrossJointSplit.transition d E D deltaWeight s (mesh D) N k m,
      APrimeCrossJointSplit.prefixGradient d E D deltaWeight s (mesh D) N k m ω ≤
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k := by
    intro ω hω
    apply hPrefixN k hkpos hk ω
    simpa [Ξ, mesh, deltaWeight] using hω
  have hGoodQV : ∀ ω ∈ Ξ N ∩
      APrimeCrossJointSplit.transition d E D deltaWeight s (mesh D) N k m,
      APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v r ω ≤
        (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2 := by
    intro ω hω
    have hqv := hQVN k hkpos hk ω hω.1 hω.2 r hr a
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
        (∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d))^((1 : ℝ)/(2 * p : ℕ)) ≤
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
            (N : ℝ)^(-1 : ℝ) := by
      have hEventNormZ :
          (∫ ω, |Z ω|^(2 * p) ∂(Gauss.P d))^((1 : ℝ)/(2 * p : ℕ)) ≤
            APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
                E s zetaSrc N r v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2) +
              APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ)/(2 * p : ℕ)) := by
        simpa [Z, m, v, mesh, Nat.cast_mul] using hEventNorm
      calc
        _ ≤ APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
              E s zetaSrc N r v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a)^2) +
            APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
              ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ)/(2 * p : ℕ)) := hEventNormZ
        _ = APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
            APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
              ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ)/(2 * p : ℕ)) := by
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
    field_simp [show (p : ℝ) ≠ 0 by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp)),
      (Real.sqrt_pos.2 hrpos).ne']
    ring
  have hcoef0 : 0 ≤ Kbad / √r := by dsimp [Kbad]; positivity
  have hBudgetPoint :
      normGoodCrossBudget E D deltaWeight s t N k p a r ≤
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
        K * APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
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
  have hCrossPoint :
      normGoodCrossBudget E D deltaWeight s t N k p a r ≤
        K * APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            zetaSrc tauG deltaWeight deltaCap N k a r +
          Kbad * (N : ℝ)^(-1 : ℝ) / √r := by
    calc
      _ ≤ Kbad / √r *
          (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N r v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N r) a +
            (N : ℝ)^(-1 : ℝ)) := hBudgetPoint
      _ = _ := by rw [mul_add, hProfilePoint, hErrPoint]
  simpa [K, Kbad, zetaSrc, tauG, deltaWeight, deltaCap] using hCrossPoint

private theorem eventually_sqrtGap_le_early_prefix
    {D : ℝ} {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      (k : ℝ) ≤ (N : ℝ)^D →
      let v := cutNetPt s (mesh D) N k
      Real.sqrt v - Real.sqrt (s N) ≤ (N : ℝ)^(-(3 * D / 2 + 9)) := by
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hMesh' : ∀ᶠ N : ℕ in atTop,
      mesh D N = (N : ℝ)^(4 * D + 18) := by
    simpa [mesh] using hMesh
  filter_upwards [hMesh', eventually_ge_atTop 1] with N hMeshN hN
  intro k hk hkPower
  let v : ℝ := cutNetPt s (mesh D) N k
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset (show k ≤ cutNetTop s t (mesh D) N by exact hk))
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hMeshCell : v - s N = (k : ℝ) / mesh D N := by
    dsimp [v, CutHypTheta.cutNetPt]
    ring
  have hLengthBound : v - s N ≤ (N : ℝ)^(-3 * D - 18) := by
    calc
      v - s N = (k : ℝ) / (N : ℝ)^(4 * D + 18) := by
        rw [hMeshCell, hMeshN]
      _ ≤ (N : ℝ)^D / (N : ℝ)^(4 * D + 18) :=
        div_le_div_of_nonneg_right hkPower (by positivity)
      _ = (N : ℝ)^(-3 * D - 18) := by
        rw [← Real.rpow_sub hNpos]
        congr 1
        ring
  have hsqrtMono : Real.sqrt (s N) ≤ Real.sqrt v := Real.sqrt_le_sqrt hv.1
  have habs := RBM.abs_sqrt_sub_sqrt_le (hs0 N) hv0
  have habs' : |Real.sqrt v - Real.sqrt (s N)| ≤ Real.sqrt |v - s N| := by
    calc
      _ = |Real.sqrt (s N) - Real.sqrt v| := abs_sub_comm _ _
      _ ≤ Real.sqrt |s N - v| := habs
      _ = Real.sqrt |v - s N| := by rw [abs_sub_comm]
  rw [abs_of_nonneg (sub_nonneg.mpr hsqrtMono),
    abs_of_nonneg (sub_nonneg.mpr hv.1)] at habs'
  have hSqrtEq : Real.sqrt ((N : ℝ)^(-3 * D - 18)) =
      (N : ℝ)^(-(3 * D / 2 + 9)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hSqrtLength : Real.sqrt (v - s N) ≤
      Real.sqrt ((N : ℝ)^(-3 * D - 18)) :=
    Real.sqrt_le_sqrt hLengthBound
  calc
    Real.sqrt v - Real.sqrt (s N) ≤ Real.sqrt (v - s N) := habs'
    _ ≤ Real.sqrt ((N : ℝ)^(-3 * D - 18)) := hSqrtLength
    _ = (N : ℝ)^(-(3 * D / 2 + 9)) := hSqrtEq

set_option maxHeartbeats 1000000 in
-- The cellwise moment and integral bounds are expanded in one fixed-order proof.
/-- For every fixed p ≥ 1, one cutoff works before all active prefix indices
and outputs. It bounds the literal full positive-time T1089 cross budget at
the actual T995 loss schedule by the microscopic profile and payment. -/
private theorem eventually_integral_positiveTimeCrossBudget_le_early_prefix_positiveIndex
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, 1 ≤ k → k ≤ cutNetTop s t (mesh D) N →
      (k : ℝ) ≤ (N : ℝ)^D →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        (∫ r in (s N)..v,
          positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r) ≤
          (15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
              Step2Moment.ratR E s N v^(-(2 : ℝ)) +
            (15 * (p : ℝ) / 2) * (N : ℝ)^(-3 * D / 2 - 10) := by
  have hDeltaWeight : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hGoodPoint :=
    eventually_pointwise_normGoodCrossBudget_le_crossProfile_add_error_allOrders
      (E := E) (D := D) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hGoodInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hDeltaWeight p hp
  have hProfilePoint :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE (le_trans (by norm_num : (0 : ℝ) ≤ 60) hD)
      hs0 hst ht1 hc hreg hδ hδsmall
  have hFull :=
    APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      (E := E) (D := D) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hDeltaWeight p hp
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hMesh' : ∀ᶠ N : ℕ in atTop,
      mesh D N = (N : ℝ)^(4 * D + 18) := by
    simpa [mesh] using hMesh
  have hGap := eventually_sqrtGap_le_early_prefix (D := D) hs0 hst
  have hEtaLowerT :=
    Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  filter_upwards [hGoodPoint, hGoodInt, hProfilePoint, hFull, hMesh',
      hGap, hEtaLowerT, eventually_ge_atTop 1]
    with N hGoodPointN hGoodIntN hProfilePointN hFullN hMeshN hGapN
      hEtaLowerTN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hEtaTpos : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hEtaSpos : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hEtaST : etaT E (t N) ≤ etaT E (s N) :=
    Gauss.etaT_le_of_le hE (hst N)
  have hEtaInvT : (etaT E (t N))⁻¹ ≤ (N : ℝ) := by
    have hEtaLower : 1 / (N : ℝ) ≤ etaT E (t N) := by
      simpa [Real.rpow_neg_one] using hEtaLowerTN
    have hInv := one_div_le_one_div_of_le
      (by positivity : 0 < 1 / (N : ℝ)) hEtaLower
    simpa [one_div] using hInv
  have hEtaInvS : (etaT E (s N))⁻¹ ≤ (N : ℝ) := by
    have hInvST : (etaT E (s N))⁻¹ ≤ (etaT E (t N))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hEtaTpos hEtaST
    exact hInvST.trans hEtaInvT
  intro k hkpos hk hkPower a
  let v : ℝ := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset (show k ≤ cutNetTop s t (mesh D) N by exact hk))
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hBudgetInt :
      IntervalIntegrable
        (normGoodCrossBudget E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a) volume (s N) v := by
    simpa [v, mesh] using hGoodIntN k (by simpa [mesh] using hk) a
  have hProfileN := hProfilePointN k (by simpa [mesh] using hk) a
  have hNormN := hGoodPointN k hkpos (by simpa [mesh] using hk) a
  let coeff : ℝ :=
    (15 * (p : ℝ) / 4) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
        Step2Moment.ratR E s N v^(-(2 : ℝ)) +
      (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)
  let boundFn : ℝ → ℝ := fun r => coeff / Real.sqrt r
  have hRpowNonneg : 0 ≤ Step2Moment.ratR E s N v^(-(2 : ℝ)) :=
    Real.rpow_nonneg hRpos.le _
  have hEtaInvSNonneg : 0 ≤ (etaT E (s N))⁻¹ :=
    inv_nonneg.mpr hEtaSpos.le
  have hConstPos : 0 <
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hCoeffNonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hBoundInt : IntervalIntegrable boundFn volume (s N) v := by
    dsimp [boundFn]
    exact intervalIntegrable_invSqrtEnvelope coeff (s N) v (hs0 N) hv.1
  have hPoint : ∀ r ∈ Icc (s N) v,
      normGoodCrossBudget E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N k p a r ≤ boundFn r := by
    intro r hr
    by_cases hrZero : r = 0
    · subst r
      simp [boundFn, coeff, normGoodCrossBudget,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget]
    · have hrpos : 0 < r := lt_of_le_of_ne ((hs0 N).trans hr.1) (Ne.symm hrZero)
      have hNorm := hNormN r hr hrpos
      have hProf := hProfileN r hr hrpos
      have hProfilePart :
          (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a r ≤
            ((15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) / Real.sqrt r := by
        calc
          _ ≤ (15 * (p : ℝ) / 4) *
              (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
                Step2Moment.ratR E s N v^(-(2 : ℝ)) / Real.sqrt r) :=
            mul_le_mul_of_nonneg_left hProf (by positivity)
          _ = _ := by ring
      have hErrorEq :
          (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt r =
          ((15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)) / Real.sqrt r := by ring
      have hCoeffEq :
          ((15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) / Real.sqrt r +
            ((15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)) / Real.sqrt r =
          coeff / Real.sqrt r := by
        dsimp [coeff]
        ring
      calc
        _ ≤ (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a r +
            (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt r := hNorm
        _ ≤ ((15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) / Real.sqrt r +
            ((15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)) / Real.sqrt r := by
          exact add_le_add hProfilePart (le_of_eq hErrorEq)
        _ = coeff / Real.sqrt r := hCoeffEq
        _ = boundFn r := rfl
  have hMono := intervalIntegral.integral_mono_on hv.1 hBudgetInt hBoundInt hPoint
  have hBoundIntegral :
      (∫ r in (s N)..v, boundFn r) =
        coeff * (2 * (Real.sqrt v - Real.sqrt (s N))) := by
    dsimp [boundFn]
    rw [integral_invSqrtEnvelope coeff (s N) v (hs0 N) hv.1]
    ring
  have hGoodIntegral :
      (∫ r in (s N)..v,
        normGoodCrossBudget E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a r) ≤
        coeff * (2 * (N : ℝ)^(-(3 * D / 2 + 9))) := by
    calc
      _ ≤ ∫ r in (s N)..v, boundFn r := hMono
      _ = coeff * (2 * (Real.sqrt v - Real.sqrt (s N))) := hBoundIntegral
      _ ≤ coeff * (2 * (N : ℝ)^(-(3 * D / 2 + 9))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hGapN k hk hkPower) (by norm_num))
          hCoeffNonneg
  have hFirst :
      ((15 * (p : ℝ) / 4) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : ℝ))) *
        (2 * (N : ℝ)^(-(3 * D / 2 + 9))) ≤
      (15 * (p : ℝ) / 2) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
          Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
    have hShort :
        (N : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9)) =
          (N : ℝ)^(-(3 * D / 2 + 8)) := by
      calc
        (N : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9)) =
            (N : ℝ)^(-(3 * D / 2 + 9)) * (N : ℝ) := by ring
        _ = (N : ℝ)^(-(3 * D / 2 + 9) + 1) :=
          (Real.rpow_add_one hNpos.ne' (-(3 * D / 2 + 9))).symm
        _ = (N : ℝ)^(1 + (-(3 * D / 2 + 9))) := by congr 1; ring
        _ = (N : ℝ)^(-(3 * D / 2 + 8)) := by congr 1; ring
    have hPower :
        (N : ℝ)^(13 * δ / 640) * (N : ℝ)^(-(3 * D / 2 + 8)) =
          (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hEtaShort := mul_le_mul_of_nonneg_right hEtaInvS
      (Real.rpow_nonneg hNpos.le (-(3 * D / 2 + 9)))
    have hFactor0 : 0 ≤ (15 * (p : ℝ) / 2) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : ℝ)^(13 * δ / 640) * Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
      have hNalpha : 0 ≤ (N : ℝ)^(13 * δ / 640) :=
        Real.rpow_nonneg hNpos.le _
      positivity
    calc
      _ = ((15 * (p : ℝ) / 2) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : ℝ))) *
          ((N : ℝ)^(-(3 * D / 2 + 9))) := by ring
      _ ≤ ((15 * (p : ℝ) / 2) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^(13 * δ / 640) * (N : ℝ) *
          Step2Moment.ratR E s N v^(-(2 : ℝ))) *
          ((N : ℝ)^(-(3 * D / 2 + 9))) := by
        calc
          _ = ((15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640) *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) *
              ((etaT E (s N))⁻¹ * (N : ℝ)^(-(3 * D / 2 + 9))) := by ring
          _ ≤ ((15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640) *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) *
              ((N : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9))) :=
            mul_le_mul_of_nonneg_left hEtaShort hFactor0
          _ = _ := by ring
      _ = (15 * (p : ℝ) / 2) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
          Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
        calc
          _ = ((15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) *
              ((N : ℝ)^(13 * δ / 640) *
                ((N : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9)))) := by ring
          _ = ((15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              Step2Moment.ratR E s N v^(-(2 : ℝ))) *
              ((N : ℝ)^(13 * δ / 640) * (N : ℝ)^(-(3 * D / 2 + 8))) := by
            rw [hShort]
          _ = _ := by rw [hPower]; ring
  have hSecond :
      ((15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)) *
        (2 * (N : ℝ)^(-(3 * D / 2 + 9))) ≤
      (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10) := by
    have hPower : (N : ℝ)^(-1 : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9)) =
        (N : ℝ)^(-3 * D / 2 - 10) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [show ((15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)) *
        (2 * (N : ℝ)^(-(3 * D / 2 + 9))) =
          (15 * (p : ℝ) / 4) *
            ((N : ℝ)^(-1 : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9))) by ring,
      hPower]
  have hFinalGood :
      coeff * (2 * (N : ℝ)^(-(3 * D / 2 + 9))) ≤
        (15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
            Step2Moment.ratR E s N v^(-(2 : ℝ)) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10) := by
    dsimp [coeff] at hGoodIntegral ⊢
    rw [add_mul] at hGoodIntegral
    calc
      _ = ((15 * (p : ℝ) / 4) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : ℝ))) *
          (2 * (N : ℝ)^(-(3 * D / 2 + 9))) +
        ((15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)) *
          (2 * (N : ℝ)^(-(3 * D / 2 + 9))) := by ring
      _ ≤ _ := add_le_add hFirst hSecond
  have hGoodBound :
      (∫ r in (s N)..v,
        normGoodCrossBudget E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a r) ≤
        (15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
            Step2Moment.ratR E s N v^(-(2 : ℝ)) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10) :=
    hGoodIntegral.trans hFinalGood
  have hFullBound := hFullN k hk a
  have hPayment :
      (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (Real.sqrt v - Real.sqrt (s N)) ≤
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10) := by
    have hPow : (N : ℝ)^(-1 : ℝ) *
        (N : ℝ)^(-(3 * D / 2 + 9)) =
        (N : ℝ)^(-3 * D / 2 - 10) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc
      _ = (15 * (p : ℝ) / 4) *
          ((N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N))) := by ring
      _ ≤ (15 * (p : ℝ) / 4) *
          ((N : ℝ)^(-1 : ℝ) * (N : ℝ)^(-(3 * D / 2 + 9))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hGapN k hk hkPower) (by positivity)
      _ = (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10) := by rw [hPow]
  calc
    (∫ r in (s N)..v,
        positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a r) ≤
        (∫ r in (s N)..v,
          normGoodCrossBudget E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) := by
      simpa [v, mesh, positiveTimeCrossBudget, normGoodCrossBudget] using hFullBound
    _ ≤
        ((15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
            Step2Moment.ratR E s N v^(-(2 : ℝ)) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10)) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-3 * D / 2 - 10) :=
      add_le_add hGoodBound hPayment
    _ = _ := by ring

/-- For every fixed p ≥ 1, one cutoff works before all active prefix indices
including k=0, and all output loop arguments. It bounds the literal full
positive-time T1089 cross budget at the actual T995 loss schedule. -/
theorem eventually_integral_positiveTimeCrossBudget_le_early_prefix_allOrders_microscopic
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      (k : ℝ) ≤ (N : ℝ)^D →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        (∫ r in (s N)..v,
          positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r) ≤
          (15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
              Step2Moment.ratR E s N v^(-(2 : ℝ)) +
            (15 * (p : ℝ) / 2) * (N : ℝ)^(-3 * D / 2 - 10) := by
  have hDeltaWeight : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hPositive :=
    eventually_integral_positiveTimeCrossBudget_le_early_prefix_positiveIndex
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  filter_upwards [hPositive, eventually_ge_atTop 1] with N hPositiveN hN
  intro k hk hkPower a
  by_cases hk0 : k = 0
  · subst k
    let v : ℝ := cutNetPt s (mesh D) N 0
    have hv : v ∈ Icc (s N) (t N) := by
      have hvEq : v = s N := by
        dsimp [v]
        exact CutHypTheta.cutNetPt_zero s (mesh D) N
      rw [hvEq]
      exact ⟨le_rfl, hst N⟩
    have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
    have hNpos : 0 < N := by omega
    have hRateZero : ∀ r,
        APrimeCrossJointSplit.jointRate d E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s (mesh D) N 0
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
          Step2.sigPM a v r = 0 := by
      intro r
      exact APrimeGeneralMovingJointMeasurable.jointRate_k_zero hNpos
        Step2.sigPM a v r
    have hp0 : p ≠ 0 := by omega
    have hqpos : 0 < (p : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by positivity
    have hMomentZero : ∀ r,
        MomentDuhamel.momNorm (Gauss.P d) (2 * p)
          (APrimeCrossJointSplit.jointRate d E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s (mesh D) N 0
            (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            Step2.sigPM a v r) = 0 := by
      intro r
      unfold MomentDuhamel.momNorm
      simp [hRateZero r, hqpos.ne']
      exact hp0
    have hBudgetZero : ∀ r,
        positiveTimeCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N 0 p a r = 0 := by
      intro r
      unfold positiveTimeCrossBudget
      rw [hMomentZero]
      simp
    have hIntegralZero :
        (∫ r in (s N)..v, positiveTimeCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N 0 p a r) = 0 := by
      rw [show (fun r => positiveTimeCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N 0 p a r) =
            (fun _ => 0) from funext hBudgetZero]
      simp
    have hRpos : 0 < Step2Moment.ratR E s N v :=
      Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hMainNonneg : 0 ≤ (15 * (p : ℝ) / 2) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) *
        Step2Moment.ratR E s N v^(-(2 : ℝ)) := by
      have hConst :=
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
      have hNpow : 0 < (N : ℝ)^(13 * δ / 640 - 3 * D / 2 - 8) :=
        Real.rpow_pos_of_pos hNposR (13 * δ / 640 - 3 * D / 2 - 8)
      have hRpow : 0 < Step2Moment.ratR E s N v^(-(2 : ℝ)) :=
        Real.rpow_pos_of_pos hRpos (-(2 : ℝ))
      positivity
    dsimp only
    rw [hIntegralZero]
    positivity
  · have hkpos : 1 ≤ k := by omega
    exact hPositiveN k hkpos hk hkPower a

noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_pointwise_normGoodCrossBudget_le_crossProfile_add_error_allOrders
#print axioms eventually_integral_positiveTimeCrossBudget_le_early_prefix_allOrders_microscopic
#print axioms nondegenerate_positive_cell_witness
#print axioms eventually_one_le_N_rpow_sixty

end
end RBM.APrimeGeneralMovingEarlyPrefixFullCrossAllOrdersMicroscopic
