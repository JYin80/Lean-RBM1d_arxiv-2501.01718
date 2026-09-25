/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodAllOrdersSlot

/-!
# T1277: all-order pointwise norm-good cross-budget bridge

This exposes the positive-time pointwise estimate used privately in the
accepted all-order integrated producer.  It keeps that producer's literal
common event, transition, weights, and scheduled losses.
-/

namespace RBM.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise

open Filter MeasureTheory Set Gauss CutHypTheta
open Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

set_option maxHeartbeats 1000000 in
/-- For each fixed `p ≥ 1`, one eventual cutoff works uniformly over every
active target-mesh cell, output, and positive running time in its closed cell.
The literal norm-good cross budget is bounded by the scheduled T1029 profile
and the all-order norm-bad payment. -/
theorem eventually_normGoodCrossBudget_le_crossProfile_add_bad_allOrders_pointwise
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
      ∀ a : LoopArg (d.L N) 2,
        ∀ u ∈ Icc (s N) (cutNetPt s (mesh D) N k),
          0 < u →
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k p a u ≤
            (15 * (p : ℝ) / 4) *
                RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                  (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                  (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                  (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                  (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u +
              (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / √u := by
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
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hEnvPoly,
      hEnvJoint, B.dim, eventually_ge_atTop 1]
    with N hPayN hJointN hPrefixN hQVN hEnvN hEnvJointN hdim hN
  have hNpos : 0 < N := by omega
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay :
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
          ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
        (N : ℝ)^(-1 : ℝ) := by
    simpa [Ξ] using hPayN
  intro k hk a u hu huPos
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have huIcc : u ∈ Icc (s N) v := by simpa [v] using hu
  have hu0 : 0 ≤ u := (hs0 N).trans huIcc.1
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hRoot0 : 0 ≤
      APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
        (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
    have hRu : 0 < Step2Moment.ratR E s N u :=
      Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) (huIcc.2.trans_lt hv1)
    have hRv : 0 < Step2Moment.ratR E s N v := hRpos
    have hW : 0 < B.W N := by exact_mod_cast B.W_pos N
    have hEll : 0 < B.ell N u := by
      exact zero_lt_one.trans_le
        (one_le_ellHat_of_nonneg (B.one_le_L N) hu0 (huIcc.2.trans_lt hv1))
    have hEta : 0 < etaT E u := Step2.etaT_pos' hE (huIcc.2.trans_lt hv1)
    have hJ : 0 ≤ APrimeGeneralMovingQVProfile.generalMovingBlockCap
        E s tauG deltaCap N u := by
      unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
      positivity
    have hnear : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate
        E s zetaSrc N u + 2 * (B.W N : ℝ)⁻¹ := by
      unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
      have hEllS : 0 < B.ell N (s N) := by
        exact zero_lt_one.trans_le (one_le_ellHat_of_nonneg
          (B.one_le_L N) (hs0 N) ((hst N).trans_lt (ht1 N)))
      have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
      have hcNear : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) (B.ell N u) :=
        Lemma57.cNear2_nonneg hW1 hEll
      positivity
    have hfar : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate
        E N u (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) := by
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
  have hPrefixRate :=
    APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
      E D s t zetaSrc tauG deltaWeight N k
  have hProfileNonneg :
      0 ≤ RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        zetaSrc tauG deltaWeight deltaCap N k a u := by
    unfold RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile
    have hsqrt : 0 < 2 * Real.sqrt u := by positivity
    positivity
  by_cases hk0 : k = 0
  · subst k
    let v0 := cutNetPt s (mesh D) N 0
    have hrateZero : ∀ r, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
        E D deltaWeight s t N 0 a r = 0 := by
      intro r
      funext ω
      have hz := RBM.APrimeGeneralMovingJointMeasurable.jointRate_k_zero
        (E := E) (D := D) (deltaWeight := deltaWeight) (s := s) (t := t)
        hNpos Step2.sigPM a v0 r
      have hzw := congrFun hz ω
      simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, v0, hzw]
    have hp0 : p ≠ 0 := by omega
    have hqpos : 0 < (↑p : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by positivity
    have hmoment : MomentDuhamel.momNorm (Gauss.P d) (2 * p)
        (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N 0 a u) = 0 := by
      unfold MomentDuhamel.momNorm
      simp [hrateZero, hqpos.ne']
      exact hp0
    have hbudget : APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D deltaWeight s t N 0 p a u = 0 := by
      unfold APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
      rw [hmoment]
      simp
    rw [hbudget]
    have hProfileTerm : 0 ≤ (15 * (p : ℝ) / 4) *
        RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          zetaSrc tauG deltaWeight deltaCap N 0 a u :=
      mul_nonneg (by positivity) hProfileNonneg
    have hErr : 0 ≤ (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / √u := by
      positivity
    exact add_nonneg hProfileTerm hErr
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
    have hZnonneg : ∀ ω, 0 ≤ Z ω := by
      intro ω
      exact APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
        (mesh D) N k m Step2.sigPM a v u hNpos ω
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
    have hq0 : 0 ≤
        (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)^2 :=
      sq_nonneg _
    have hEnvAll : ∀ ω,
        APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
            (mesh D) N k m ω *
          √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v u ω) ≤
            APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
      intro ω
      have hh := hEnvJointN k hk Step2.sigPM a u hu ω
      simpa [m, mesh] using hh
    have hGoodPrefix : ∀ ω ∈ Ξ N ∩
        APrimeCrossJointSplit.transition d E D deltaWeight s (mesh D) N k m,
        APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
            (mesh D) N k m ω ≤
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t zetaSrc tauG deltaWeight N k := by
      intro ω hω
      apply hPrefixN k hkpos hk ω
      simpa [Ξ, mesh, deltaWeight] using hω
    have hGoodQV : ∀ ω ∈ Ξ N ∩
        APrimeCrossJointSplit.transition d E D deltaWeight s (mesh D) N k m,
        APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v u ω ≤
          (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a)^2 := by
      intro ω hω
      have hqv := hQVN k hkpos hk ω hω.1 hω.2 u hu a
      simpa [APrimeGeneralMovingQVProfile.generalMovingBlockCap,
        deltaWeight, xi, deltaCap, tauG, zetaSrc, hbuffer] using hqv
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
      hPrefixRate hq0 hEnv0 hRho hGoodPrefix hGoodQV hEnvAll le_rfl hZi
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
          _ ≤ _ := add_le_add le_rfl hEnvPay
      simpa [MomentDuhamel.momNorm, Nat.cast_mul] using hEventNormPay
    have hgoodNorm :
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ≤
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
              (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
          (N : ℝ)^(-1 : ℝ) := hMomCompare.trans hFullNorm
    have hcoefEq :
        APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √u) = Kbad / √u := by
      unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
      dsimp [Kbad]
      push_cast
      field_simp [show (p : ℝ) ≠ 0 by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp)),
        (Real.sqrt_pos.2 huPos).ne']
      ring
    have hcoef0 : 0 ≤ Kbad / √u := by dsimp [Kbad]; positivity
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
      rw [hcoefEq]
      exact mul_le_mul_of_nonneg_left hgoodNorm hcoef0
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
    have hCrossPoint :
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a u ≤
          K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              zetaSrc tauG deltaWeight deltaCap N k a u +
            Kbad * (N : ℝ)^(-1 : ℝ) / √u := by
      calc
        _ ≤ Kbad / √u *
            (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t zetaSrc tauG deltaWeight N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a +
              (N : ℝ)^(-1 : ℝ)) := hBudgetPoint
        _ = _ := by rw [mul_add, hProfilePoint, hErrPoint]
    simpa [K, Kbad, zetaSrc, tauG, deltaWeight, deltaCap] using hCrossPoint

noncomputable abbrev nondegenerate_scheduled_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_normGoodCrossBudget_le_crossProfile_add_bad_allOrders_pointwise
#print axioms nondegenerate_scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise
