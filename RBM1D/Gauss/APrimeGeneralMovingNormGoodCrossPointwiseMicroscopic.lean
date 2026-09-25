/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodReduction
import RBM1D.Gauss.APrimeGeneralMovingJointGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingTransitionPrefixGradient
import RBM1D.Gauss.APrimeGeneralMovingTransitionQV
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.Lemma514Q716
import RBM1D.Gauss.Lemma514QRoute

/-!
# T1247: microscopic pointwise norm-good cross bound

For the exact T995 schedule and the actual norm-good restriction of T1089's
joint rate, the p=1 norm-good cross budget is bounded pointwise on every
closed active cell by the accepted T1029 cross profile plus its paid
polynomial-envelope remainder.  The remainder retains its inverse-square-root
time singularity, so integration gives the endpoint difference
`2 * (sqrt v - sqrt (s N))`.
-/

namespace RBM.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D
private noncomputable def profileCap (E : Real) (s : Nat → Real)
    (tauG delta : Real) (N : Nat) (u : Real) : Real :=
  APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG delta N u

/-- T995's explicit nondegenerate positive-cell and common-event witness. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

private theorem absorbedRootProfile_nonneg
    {E : Real} {s : Nat → Real} {zetaSrc tauG deltaCap : Real}
    {N : Nat} {u v D : Real} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hu : u ∈ Icc (s N) v) (hv1 : v < 1)
    (a : LoopArg (B.L N) 2) :
    0 ≤ APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
      (profileCap E s tauG deltaCap N u) a := by
  have hu1 : u < 1 := hu.2.trans_lt hv1
  have hEta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hRu : 0 < Step2Moment.ratR E s N u :=
    Step2Moment.ratR_pos hE (hu.1.trans_lt hu1) hu1
  have hsLEv : s N ≤ v := hu.1.trans hu.2
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hsLEv.trans_lt hv1) hv1
  have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
  have hEllU : 0 < B.ell N u := by
    have := one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans hu.1) hu1
    simpa only [Band.ell] using (zero_lt_one.trans_le this)
  have hEllS : 0 < B.ell N (s N) := by
    have hs1 : s N < 1 := hu.1.trans_lt hu1
    have := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (zero_lt_one.trans_le this)
  have hCnear : 0 ≤ Lemma57.cNear2 (B.W N : Real) (B.ell N u) :=
    Lemma57.cNear2_nonneg (by exact_mod_cast B.W_pos N) hEllU
  have hNear : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate
      E s zetaSrc N u + 2 * (B.W N : Real)⁻¹ := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    positivity
  have hJ : 0 ≤ profileCap E s tauG deltaCap N u := by
    unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap
    positivity
  have hScale : 0 < B.scale E N u := by
    change 0 < (B.W N : Real) * B.ell N u * etaT E u
    positivity
  have hFar : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
      (profileCap E s tauG deltaCap N u) := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    positivity
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  have hXi : 0 ≤ Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hChi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : Real) <=
      6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
    split_ifs <;> norm_num
  positivity

/-- For p=1, the literal norm-good budget is pointwise bounded by the
accepted T1029 cross profile plus the exact paid envelope term.  The estimate
holds uniformly eventually over every active cell, output, and positive time
in the closed cell. -/
theorem eventually_normGoodCrossBudget_le_crossProfile_microscopic
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      let v := cutNetPt s (mesh D) N k
      ∀ u ∈ Icc (s N) v, 0 < u →
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u ≤
          (15 / 4 : Real) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u +
            (15 / 8 : Real) * (N : Real)^(-1 : Real) * Real.sqrt u⁻¹ := by
  let zetaSrc := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ
  let zetaCtr := APrimeGeneralMovingSlotLossSchedule.zetaCtr δ
  let tauG := APrimeGeneralMovingSlotLossSchedule.tauG δ
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  let xi := APrimeGeneralMovingSlotLossSchedule.xi δ
  let deltaCap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  let Ξ : Nat → Set (Gauss.Ω d) := fun N =>
    APrimeGeneralMovingCommonSources.commonEvent E D s t zetaSrc zetaCtr tauG N
  have hrooms := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hrooms with ⟨hdw, hxi, hcap, htau, hzsrc, hzctr, hbuffer, hzsrcTau,
      htauCap, hcapC, hcapRoom, _, _⟩
  have hdeltaEq : deltaWeight + xi = deltaCap := by
    change δ / 100 + δ / 100 = δ / 50
    ring
  have hprefixTau : tauG ≤ deltaWeight / 16 := by
    change δ / 1600 ≤ (δ / 100) / 16
    exact le_of_eq (by ring)
  have hprefixC : deltaWeight ≤ c / 20 := by
    dsimp [deltaWeight, APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    have hδc := hδsmall.trans (min_le_right 1 (c / 100))
    nlinarith
  have hprefixRoom : tauG + 2 * deltaWeight + (2 : Real) / 15 < 1 := by
    have hDwLeCap : deltaWeight ≤ deltaCap := by
      dsimp [deltaWeight, deltaCap,
        APrimeGeneralMovingSlotLossSchedule.deltaWeight,
        APrimeGeneralMovingSlotLossSchedule.deltaCap]
      linarith [hδ.le]
    dsimp [tauG, deltaWeight, deltaCap,
      APrimeGeneralMovingSlotLossSchedule.tauG,
      APrimeGeneralMovingSlotLossSchedule.deltaWeight,
      APrimeGeneralMovingSlotLossSchedule.deltaCap] at *
    nlinarith [hcapRoom, hDwLeCap]
  have hHP : HighProb (Gauss.P d) Ξ := by
    exact APrimeGeneralMovingCommonSources.highProb_commonEvent
      hE hD hs0 hst ht1 hc hreg hB zetaSrc zetaCtr tauG hzsrc hzctr htau
  have hEnv :=
    APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow hD
  have hProduct :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdw.le
  have hPay := Gauss.eventually_env_mul_prob_rpow_le
    (P := Gauss.P d) (q := 2) (by omega) hHP
    (Cenv := 2 * D + 17) (by positivity) hEnv (D := 1) (by norm_num)
  have hJointInt :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg (hdw.le) 1 (by norm_num)
  have hPrefix :=
    APrimeGeneralMovingTransitionPrefixGradient.eventually_prefixGradient_le_on_smooth_transition
      hE hD hs0 hst ht1 hc hreg hB hzsrc hzctr htau hdw
      hzsrcTau hprefixTau hprefixC hprefixRoom
  have hQV :=
    APrimeGeneralMovingTransitionQV.eventually_qv_le_absorbed_on_smooth_transition_buffered
      hE hD hs0 hst ht1 hc hreg hB hzsrc hzctr htau hxi
      (by rw [hbuffer]; exact hcap) hzsrcTau
      (by rw [hbuffer]; exact htauCap)
      (by rw [hbuffer]; exact hcapC)
      (calc
        tauG + 2 * (deltaWeight + xi) + (2 : Real) / 15 =
            tauG + 2 * deltaCap + (2 : Real) / 15 := by rw [hbuffer]
        _ < 1 := hcapRoom)
  have hMeasΞ : ∀ N, MeasurableSet (Ξ N) := by
    intro N
    exact APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      E D s t zetaSrc zetaCtr tauG N
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hEnv, hProduct, B.dim,
      eventually_ge_atTop 1]
    with N hPayN hJointN hPrefixN hQVN hEnvN hProductN hdim hN
  have hNpos : 0 < N := by omega
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay : APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
      ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : Real) / (2 : Nat)) ≤
        (N : Real)^(-1 : Real) := by
    have hp := hPayN
    simpa [Ξ] using hp
  intro k hk a v u hu huPos
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hUwindow : u ∈ Icc (s N) (cutNetPt s (mesh D) N k) := by
    simpa [v] using hu
  let Z : Gauss.Ω d → Real := fun ω =>
    APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
      E D deltaWeight s t N k a u ω
  let H : Real :=
    APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
      E D s t zetaSrc tauG deltaWeight N k *
    APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
      (profileCap E s tauG deltaCap N u) a
  let hRate : Gauss.Ω d → Real := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a v u ω
  have hRatInt : Integrable (fun ω => |hRate ω| ^ (2 : Nat)) (Gauss.P d) := by
    simpa [hRate, v, deltaWeight] using hJointN k hk Step2.sigPM a u hUwindow
  have hGoodMeas : MeasurableSet (APrimeGeneralMovingGoodMesh.good N) :=
    APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hZint : Integrable (fun ω => |Z ω| ^ (2 : Nat)) (Gauss.P d) := by
    have hEq : (fun ω => |Z ω| ^ (2 : Nat)) =
        (APrimeGeneralMovingGoodMesh.good N).indicator
          (fun ω => |hRate ω| ^ (2 : Nat)) := by
      funext ω
      by_cases hgood : ω ∈ APrimeGeneralMovingGoodMesh.good N
      · simp [Z, hRate, hgood,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate]
        <;> rfl
      · simp [Z, hRate, hgood,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate]
    rw [hEq]
    exact hRatInt.indicator hGoodMeas
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg
      (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
        E D s t zetaSrc tauG deltaWeight N k)
      (absorbedRootProfile_nonneg hE hs0 hUwindow hv1 a)
  have hZΞ : ∀ ω ∈ Ξ N, |Z ω| ≤ H := by
    intro ω hωΞ
    by_cases hgood : ω ∈ APrimeGeneralMovingGoodMesh.good N
    · change |(APrimeGeneralMovingGoodMesh.good N).indicator
          (fun ω => APrimeCrossJointSplit.jointRate d E D deltaWeight s
            (mesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            Step2.sigPM a v u ω) ω| ≤ H
      rw [Set.indicator_of_mem hgood]
      by_cases hkpos : 1 ≤ k
      · let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
        let tr := APrimeCrossJointSplit.transition d E D deltaWeight s
          (mesh D) N k m
        by_cases htr : ω ∈ tr
        · have hprefix := hPrefixN k hkpos hk ω ⟨hωΞ, htr⟩
          have hqv := hQVN k hkpos hk ω hωΞ htr u hUwindow a
          have hprofile0 := absorbedRootProfile_nonneg
            (E := E) (s := s) (zetaSrc := zetaSrc) (tauG := tauG)
            (deltaCap := deltaCap) (N := N) (u := u) (v := v) (D := D)
            hE hs0 hUwindow hv1 a
          have hroot : Real.sqrt (APrimeDriftTimeFamily.qvAt d E D N
                Step2.sigPM a (s N) v u ω) ≤
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc
                N u v D (profileCap E s tauG deltaCap N u) a := by
            rw [Real.sqrt_le_iff]
            have hqv' : APrimeDriftTimeFamily.qvAt d E D N
                Step2.sigPM a (s N) v u ω ≤
                (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc
                  N u v D (profileCap E s tauG deltaCap N u) a) ^ 2 := by
              rw [← hdeltaEq]
              simpa [profileCap, zetaSrc, tauG, xi] using hqv
            exact ⟨hprofile0, hqv'⟩
          have hpref0 : 0 ≤ APrimeCrossJointSplit.prefixGradient d E D
              deltaWeight s (mesh D) N k m ω := by
            unfold APrimeCrossJointSplit.prefixGradient
            exact div_nonneg (Real.sqrt_nonneg _)
              (APrimeSmoothWeightActual.threshold_pos
                (δ := deltaWeight) hNpos).le
          have hprefixRate0 :=
            APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
              E D s t zetaSrc tauG deltaWeight N k
          have hProd :
              APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
                  (mesh D) N k m ω *
                Real.sqrt (APrimeDriftTimeFamily.qvAt d E D N
                  Step2.sigPM a (s N) v u ω) ≤
              APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                  E D s t zetaSrc tauG deltaWeight N k *
                APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc
                  N u v D (profileCap E s tauG deltaCap N u) a := by
            calc
              _ ≤ APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
                    (mesh D) N k m ω *
                  APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc
                    N u v D (profileCap E s tauG deltaCap N u) a :=
                mul_le_mul_of_nonneg_left hroot hpref0
              _ ≤ _ := mul_le_mul_of_nonneg_right hprefix hprofile0
          have hAbs : |APrimeCrossJointSplit.jointRate d E D deltaWeight s
                (mesh D) N k m Step2.sigPM a v u ω| ≤ H := by
            rw [APrimeCrossJointSplit.jointRate,
              Set.indicator_of_mem htr,
              abs_of_nonneg (mul_nonneg hpref0 (Real.sqrt_nonneg _))]
            simpa [H, m, tr, APrimeCrossJointSplit.prefixGradient] using hProd
          simpa [hRate, m, v] using hAbs
        · simp [m, tr, APrimeCrossJointSplit.jointRate, htr]
          exact hH0
      · have hk0 : k = 0 := by omega
        subst k
        have hzero :=
          APrimeGeneralMovingCrossHcrossPositive.zeroPrefix_jointRate_eq_zero
            E D deltaWeight s t N a v u (by omega)
        rw [hzero]
        simpa using hH0
    · simp [Z, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
        hgood, H, hH0]
  have hZall : ∀ ω, |Z ω| ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
    intro ω
    have hraw := hProductN k hk Step2.sigPM a u hUwindow ω
    by_cases hgood : ω ∈ APrimeGeneralMovingGoodMesh.good N
    · change |(APrimeGeneralMovingGoodMesh.good N).indicator
          (fun ω => APrimeCrossJointSplit.jointRate d E D deltaWeight s
            (mesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            Step2.sigPM a v u ω) ω| ≤ _
      rw [Set.indicator_of_mem hgood, abs_of_nonneg
          (APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
            (mesh D) N k (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            Step2.sigPM a v u hNpos ω)]
      by_cases htr : ω ∈ APrimeCrossJointSplit.transition d E D deltaWeight s
          (mesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      · simpa [APrimeCrossJointSplit.jointRate, htr] using hraw
      · simp [APrimeCrossJointSplit.jointRate, htr]
        exact hEnv0
    · simp [Z, APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
        hgood, hEnv0]
  have hP : ((Gauss.P d) (Ξ N)ᶜ).toReal ≤
      ((Gauss.P d) (Ξ N)ᶜ).toReal := le_rfl
  have hMom := Gauss.momNorm_le_affine_on_event
    (P := Gauss.P d) (q := 2) (by omega)
    (Y := fun _ : Gauss.Ω d => 0) (Z := Z)
    (fun _ => le_rfl) (integrable_const _) hZint (hMeasΞ N)
    (c := 0) (d := H)
    (Env := APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N)
    (pr := ((Gauss.P d) (Ξ N)ᶜ).toReal)
    (by norm_num) hH0 hEnv0 ENNReal.toReal_nonneg
    (fun ω hω => by simpa using hZΞ ω hω) hZall hP
  have hMomPay : MomentDuhamel.momNorm (Gauss.P d) 2 Z ≤ H +
      (N : Real)^(-1 : Real) := by
    calc
      _ ≤ (0 * MomentDuhamel.momNorm (Gauss.P d) 2
            (fun _ : Gauss.Ω d => 0)) + H +
          APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
            ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : Real) / (2 : Nat)) := hMom
      _ = H + APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
            ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : Real) / (2 : Nat)) := by ring
      _ ≤ H + (N : Real)^(-1 : Real) := add_le_add_right hEnvPay H
  have hCoeffEq :
      APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
          (4 * (1 : Real) * Real.sqrt u) =
        (15 / 8 : Real) * (Real.sqrt u)⁻¹ := by
    rw [APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff_one]
    field_simp [ne_of_gt (Real.sqrt_pos.2 huPos)]
    ring
  have hcoef0 : 0 ≤ (15 / 8 : Real) * (Real.sqrt u)⁻¹ := by positivity
  have hMomCoef :
      (15 / 8 : Real) * (Real.sqrt u)⁻¹ *
          MomentDuhamel.momNorm (Gauss.P d) 2 Z ≤
        (15 / 8 : Real) * (Real.sqrt u)⁻¹ * (H + (N : Real)^(-1 : Real)) :=
    mul_le_mul_of_nonneg_left hMomPay hcoef0
  have hCrossCoeff :
      (15 / 8 : Real) * (Real.sqrt u)⁻¹ * H =
        (15 / 4 : Real) * APrimeGeneralMovingCrossProfileSlot.crossProfile
          E D s t zetaSrc tauG deltaWeight deltaCap N k a u := by
    have hinv : (2 * Real.sqrt u)⁻¹ = (Real.sqrt u)⁻¹ / 2 := by
      rw [mul_inv_rev]
      norm_num
      ring
    have hprofile :
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
            deltaWeight deltaCap N k a u =
          (2 * Real.sqrt u)⁻¹ *
            APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t zetaSrc tauG deltaWeight N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
              (profileCap E s tauG deltaCap N u) a := by rfl
    rw [hprofile]
    dsimp [H]
    rw [hinv]
    ring_nf
  unfold APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
  simp only [Nat.cast_one, Nat.mul_one, mul_one] at hCoeffEq ⊢
  change
    (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
      (4 * Real.sqrt u)) *
      MomentDuhamel.momNorm (Gauss.P d) 2
        (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N k a u) ≤ _
  rw [hCoeffEq]
  have hMomCoef' := by simpa [Z] using hMomCoef
  calc
    _ ≤ (15 / 8 : Real) * (Real.sqrt u)⁻¹ *
        (H + (N : Real)^(-1 : Real)) := hMomCoef'
    _ = (15 / 4 : Real) *
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
            deltaWeight deltaCap N k a u +
        (15 / 8 : Real) * (N : Real)^(-1 : Real) * Real.sqrt u⁻¹ := by
      rw [mul_add, hCrossCoeff]
      rw [Real.sqrt_inv]
      ring_nf

#print axioms eventually_normGoodCrossBudget_le_crossProfile_microscopic
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic
