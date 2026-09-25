/- 
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodAllOrdersSlot
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral

/-!
# T1279: all-order full cross-budget bound on the first positive cell

For each fixed p ≥ 1, this integrates the exact T1207 full-to-norm-good
reduction and the literal all-order norm-good pointwise estimate on the first
positive target-mesh cell. The profile input is the accepted T1245 pointwise
T1029 cross-profile producer under the T995 loss schedule.
-/

namespace RBM.APrimeGeneralMovingFirstCellFullCrossAllOrdersMicroscopic

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

/-- T995's explicit nondegenerate same-event witness for the active first
positive cell and positive actual smooth weight. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

set_option maxHeartbeats 1000000 in
-- The all-order moment comparison expands the literal joint-rate integrand.
/-- The pointwise all-order estimate at the heart of T1211, made explicit
here because that file keeps it private inside its integrated proof. -/
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
      k ≤ cutNetTop s t (mesh D) N →
      1 ≤ k →
      ∀ a : LoopArg (d.L N) 2, ∀ r : ℝ,
        r ∈ Icc (s N) (cutNetPt s (mesh D) N k) →
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
    (Cenv := 2 * D + 17) (by linarith) hEnvPoly (D := 1) (by norm_num)
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
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hEnvPoly, hEnvJoint,
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
  intro k hk hkpos a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hv1
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
        apply hPrefixN k hkpos hk ω
        simpa [Ξ, mesh, deltaWeight] using hω
      have hGoodQV : ∀ ω ∈ Ξ N ∩
          APrimeCrossJointSplit.transition d E D deltaWeight s
            (mesh D) N k m,
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

  exact hpoint

set_option maxHeartbeats 1000000 in
-- The interval-integral comparison expands several exact profile factors.
/-- For each fixed p ≥ 1, the exact full positive-time cross budget on the
active first positive target-mesh cell has the microscopic all-order bound.
The eventual cutoff is common to every output loop argument. -/
theorem eventually_integral_firstCell_positiveTimeCrossBudget_allOrders_le
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        (∫ u in (s N)..cutNetPt s (mesh D) N 1,
          positiveTimeCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 p a u) ≤
          (15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ)^(13 * δ / 640 - 2 * D - 8) *
            Step2Moment.ratR E s N (cutNetPt s (mesh D) N 1)^(-(2 : ℝ)) +
          (15 * (p : ℝ) / 2) * (N : ℝ)^(-2 * D - 10) := by
  have hdeltaWeight :
      0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hfull :=
    APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hgoodInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hgoodPoint :=
    eventually_pointwise_normGoodCrossBudget_le_crossProfile_add_error_allOrders
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hprofilePoint :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (c := c) (s := s) (t := t) (δ := δ)
      hE (by linarith) hs0 hst ht1 hc hreg hδ hδsmall
  have hmesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hEta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  filter_upwards [hfull, hgoodInt, hgoodPoint, hprofilePoint, hmesh,
      hEta, eventually_ge_atTop 1] with
    N hfullN hgoodIntN hgoodPointN hprofilePointN hmeshN hEtaN hN
  have hNnat : 1 ≤ N := by omega
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  intro hk a
  let v := cutNetPt s (mesh D) N 1
  have hvWindow : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hvWindow.1
  have hv1 : v < 1 := hvWindow.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hsv
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hsv.trans_lt hv1) hv1
  have hRpow0 : 0 ≤ Step2Moment.ratR E s N v^(-(2 : ℝ)) :=
    Real.rpow_nonneg hRpos.le _
  have hEtaTLower : (N : ℝ)^(-(1 : ℝ)) ≤ etaT E (t N) := hEtaN
  have hEtaTtoS : etaT E (t N) ≤ etaT E (s N) :=
    Gauss.etaT_le_of_le hE (hst N)
  have hEtaS : (N : ℝ)^(-(1 : ℝ)) ≤ etaT E (s N) :=
    hEtaTLower.trans hEtaTtoS
  have hEtaSpos : 0 < etaT E (s N) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hEtaS
  have hEtaInv : (etaT E (s N))⁻¹ ≤ (N : ℝ) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hEtaS
    simpa only [Real.rpow_neg hNpos.le, Real.rpow_one, inv_inv] using hi
  have hgap0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hvsub : v - s N = 1 / mesh D N := by
    dsimp [v, CutHypTheta.cutNetPt]
    ring
  have hrecip :
      (1 : ℝ) / (N : ℝ)^(4 * D + 18) =
        (N : ℝ)^(-(4 * D + 18)) := by
    rw [Real.rpow_neg hNpos.le]
    simp only [one_div]
  have hpow : ((N : ℝ)^(-(2 * D + 9)))^2 =
      (N : ℝ)^(-(4 * D + 18)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hroot : Real.sqrt ((1 : ℝ) / (N : ℝ)^(4 * D + 18)) =
      (N : ℝ)^(-(2 * D + 9)) := by
    rw [hrecip, ← hpow]
    exact Real.sqrt_sq (Real.rpow_nonneg hNpos.le _)
  have hgap : Real.sqrt v - Real.sqrt (s N) ≤ (N : ℝ)^(-(2 * D + 9)) := by
    have habs := RBM.abs_sqrt_sub_sqrt_le (le_trans (hs0 N) hsv) (hs0 N)
    have hrootGap : Real.sqrt (v - s N) = (N : ℝ)^(-(2 * D + 9)) := by
      calc
        Real.sqrt (v - s N) = Real.sqrt (1 / mesh D N) := by rw [hvsub]
        _ = Real.sqrt ((1 : ℝ) / (N : ℝ)^(4 * D + 18)) := by
          rw [show mesh D N = (N : ℝ)^(4 * D + 18) from hmeshN]
        _ = _ := hroot
    rw [abs_of_nonneg hgap0,
      abs_of_nonneg (sub_nonneg.mpr hsv)] at habs
    calc
      Real.sqrt v - Real.sqrt (s N) ≤ Real.sqrt (v - s N) := habs
      _ = (N : ℝ)^(-(2 * D + 9)) := hrootGap
  let R := Step2Moment.ratR E s N v
  let alpha := 13 * δ / 640
  let Kprofile :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst
  let Cprof := (15 * (p : ℝ) / 4) * Kprofile * (N : ℝ)^alpha *
      (etaT E (s N))⁻¹ * R^(-(2 : ℝ))
  let Cbad := (15 * (p : ℝ) / 8) * (N : ℝ)^(-(1 : ℝ))
  let Cgood := Cprof + Cbad
  have hKprofile : 0 < Kprofile := by
    dsimp [Kprofile]
    exact APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hCprof0 : 0 ≤ Cprof := by dsimp [Cprof, R, alpha]; positivity
  have hCbad0 : 0 ≤ Cbad := by dsimp [Cbad]; positivity
  have hCgood0 : 0 ≤ Cgood := add_nonneg hCprof0 hCbad0
  have hgoodPointwise : ∀ u ∈ Icc (s N) v,
      normGoodCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 p a u ≤ Cgood / Real.sqrt u := by
    intro u hu
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    by_cases huEq : u = 0
    · subst u
      simp [normGoodCrossBudget,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget]
    · have huPos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huEq)
      have hng := hgoodPointN 1 hk (by norm_num) a u hu
      have hprof := hprofilePointN 1 hk a u hu huPos
      have hprofCoeff : 0 ≤ (15 * (p : ℝ) / 4) := by positivity
      have hProfScale := mul_le_mul_of_nonneg_left hprof hprofCoeff
      have hprofileBound :
          (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u ≤
            Cprof / Real.sqrt u := by
        calc
          _ ≤ (15 * (p : ℝ) / 4) *
              (Kprofile * (N : ℝ)^(13 * δ / 640) *
                (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) / Real.sqrt u) := hProfScale
          _ = Cprof / Real.sqrt u := by dsimp [Cprof, alpha]; ring
      have hErrEq :
          (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt u =
            Cbad / Real.sqrt u := by dsimp [Cbad]
      calc
        _ ≤ (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u +
              (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt u := hng
        _ ≤ Cprof / Real.sqrt u + Cbad / Real.sqrt u :=
          add_le_add hprofileBound (le_of_eq hErrEq)
        _ = Cgood / Real.sqrt u := by dsimp [Cgood]; rw [add_div]
  have hgoodInt : IntervalIntegrable
      (normGoodCrossBudget E D
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N 1 p a)
      volume (s N) v := by simpa [mesh] using hgoodIntN 1 hk a
  have hEnvelopeInt : IntervalIntegrable (fun u => Cgood / Real.sqrt u)
      volume (s N) v :=
    intervalIntegrable_invSqrtEnvelope Cgood (s N) v (hs0 N) hsv
  have hgoodIntegral :
      (∫ u in (s N)..v,
        normGoodCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 p a u) ≤ 2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ ∫ u in (s N)..v, Cgood / Real.sqrt u :=
        intervalIntegral.integral_mono_on hsv hgoodInt hEnvelopeInt hgoodPointwise
      _ = 2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) :=
        integral_invSqrtEnvelope Cgood (s N) v (hs0 N) hsv
  have hfullCell :
      (∫ u in (s N)..v,
        positiveTimeCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 p a u) ≤
        (∫ u in (s N)..v,
          normGoodCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 p a u) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) := by
    simpa [v, mesh] using hfullN 1 hk a
  have hcombined :
      (∫ u in (s N)..v,
        positiveTimeCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 p a u) ≤
        (15 * (p : ℝ) / 2) * Kprofile * (N : ℝ)^alpha *
            (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N)) +
          (15 * (p : ℝ) / 2) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ 2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) +
            (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
              (Real.sqrt v - Real.sqrt (s N)) :=
        hfullCell.trans (add_le_add hgoodIntegral le_rfl)
      _ = _ := by dsimp [Cgood, Cprof, Cbad]; ring
  have hInvGap :
      (etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ)^(-2 * D - 8) := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ)^(-(2 * D + 9)) :=
        mul_le_mul hEtaInv hgap hgap0 (by positivity)
      _ = (N : ℝ)^(-2 * D - 8) := by
        calc
          (N : ℝ) * (N : ℝ)^(-(2 * D + 9)) =
              (N : ℝ)^(1 : ℝ) * (N : ℝ)^(-(2 * D + 9)) := by rw [Real.rpow_one]
          _ = (N : ℝ)^(1 - (2 * D + 9)) := by
            rw [← Real.rpow_add hNpos]
            congr 1
          _ = (N : ℝ)^(-2 * D - 8) := by congr 1; ring
  have hNpowMain :
      (N : ℝ)^alpha * ((etaT E (s N))⁻¹ *
          (Real.sqrt v - Real.sqrt (s N))) ≤
        (N : ℝ)^(alpha - 2 * D - 8) := by
    calc
      _ ≤ (N : ℝ)^alpha * (N : ℝ)^(-2 * D - 8) :=
        mul_le_mul_of_nonneg_left hInvGap (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ)^(alpha - 2 * D - 8) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hNpowBad :
      (N : ℝ)^(-1 : ℝ) * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ)^(-2 * D - 10) := by
    calc
      _ ≤ (N : ℝ)^(-1 : ℝ) * (N : ℝ)^(-(2 * D + 9)) :=
        mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ)^(-2 * D - 10) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hmainRate :
      Kprofile * (N : ℝ)^alpha * (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) ≤
        Kprofile * (N : ℝ)^(alpha - 2 * D - 8) * R^(-(2 : ℝ)) := by
    have hfactor : 0 ≤ Kprofile * R^(-(2 : ℝ)) :=
      mul_nonneg
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos.le
        hRpow0
    calc
      _ = (Kprofile * R^(-(2 : ℝ))) *
          ((N : ℝ)^alpha * ((etaT E (s N))⁻¹ *
            (Real.sqrt v - Real.sqrt (s N)))) := by ring
      _ ≤ (Kprofile * R^(-(2 : ℝ))) * (N : ℝ)^(alpha - 2 * D - 8) :=
        mul_le_mul_of_nonneg_left hNpowMain hfactor
      _ = _ := by ring
  have hcombinedSmall :
      (15 * (p : ℝ) / 2) * Kprofile * (N : ℝ)^alpha *
          (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) +
        (15 * (p : ℝ) / 2) * (N : ℝ)^(-1 : ℝ) *
          (Real.sqrt v - Real.sqrt (s N)) ≤
      (15 * (p : ℝ) / 2) * Kprofile *
          (N : ℝ)^(alpha - 2 * D - 8) * R^(-(2 : ℝ)) +
        (15 * (p : ℝ) / 2) * (N : ℝ)^(-2 * D - 10) := by
    have hcoef : 0 ≤ (15 * (p : ℝ) / 2) := by positivity
    exact add_le_add
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmainRate hcoef)
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hNpowBad hcoef)
  have hfinal := hcombined.trans hcombinedSmall
  simpa [v, mesh, R, alpha, Kprofile, positiveTimeCrossBudget] using hfinal

#print axioms eventually_pointwise_normGoodCrossBudget_le_crossProfile_add_error_allOrders
#print axioms eventually_integral_firstCell_positiveTimeCrossBudget_allOrders_le
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingFirstCellFullCrossAllOrdersMicroscopic
