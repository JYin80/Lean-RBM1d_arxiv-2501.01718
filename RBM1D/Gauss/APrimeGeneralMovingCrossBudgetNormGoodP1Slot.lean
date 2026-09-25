/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingDriftCrossProfileJointSlot
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingTransitionQV
import RBM1D.Gauss.APrimeGeneralMovingTransitionPrefixGradient
import RBM1D.Gauss.Lemma514Q716
import RBM1D.Gauss.Lemma514QRoute

/-!
# T1211: p=1 norm-good general-moving cross-budget slot

The literal T1201 norm-good cross budget is integrated at the general-moving
T995 small-slot scale.  The moment split is conditional on the common source
event and the strict transition at the same sample; no residence of their
intersection is used.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetNormGoodP1Slot

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

/-- The exact nondegenerate T995 model context is kept available to downstream
consumers of this slot. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

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
    {zetaSrc tauG deltaWeight deltaCap : Real} {N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (mesh D) N) (a : LoopArg (B.L N) 2) :
    let v := cutNetPt s (mesh D) N k
    IntervalIntegrable
      (APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        zetaSrc tauG deltaWeight deltaCap N k a)
      volume (s N) v := by
  let v := cutNetPt s (mesh D) N k
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
      (1 / 2 : Real) *
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
      (fun u => Real.sqrt u⁻¹ * ((1 / 2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a)) := by
    funext u
    rw [hinv u, ← Real.sqrt_inv u]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hfun]
  exact hBase.mul_continuousOn (by simpa only [Set.uIcc_of_le hv.1] using hFactor)

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

/-- For `p = 1`, the literal T1201 norm-good budget has a fixed small-slot
integral bound on every active general-moving target cell. -/
theorem eventually_integral_normGoodCrossBudget_le_small_slot
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in atTop, ∀ k : Nat,
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ u in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k 1 a u) ≤
            C * (N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : Real)) := by
  let zetaSrc := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ
  let zetaCtr := APrimeGeneralMovingSlotLossSchedule.zetaCtr δ
  let tauG := APrimeGeneralMovingSlotLossSchedule.tauG δ
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  let xi := APrimeGeneralMovingSlotLossSchedule.xi δ
  let deltaCap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  let Ξ : Nat → Set (Gauss.Ω d) := fun N =>
    APrimeGeneralMovingCommonSources.commonEvent E D s t zetaSrc zetaCtr tauG N
  let C : Real := (15 / 4 : Real) *
    (|APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| + 1)
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
  have hCrossInt :=
    APrimeGeneralMovingCrossProfileSlot.eventually_integral_crossProfile_le_small_slot
      (E := E) (D := D) (s := s) (t := t) (δ := δ)
      hE (by linarith) hs0 hst ht1 hc hreg hδ hδsmall
  have hBudgetInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdw.le 1 (by norm_num)
  have hThirty := hreg.1.pow_thirty_le hE hst ht1
  have hMeasΞ : ∀ N, MeasurableSet (Ξ N) := by
    intro N
    exact APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      E D s t zetaSrc zetaCtr tauG N
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hCrossInt, hBudgetInt,
      hThirty, hProduct, B.dim, eventually_ge_atTop 1]
    with N hPayN hJointN hPrefixN hQVN hCrossN hBudgetN hThirtyN hProductN hdim hN
  have hNpos : 0 < N := by omega
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay : APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
      ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : Real) / (2 : Nat)) ≤
        (N : Real)^(-1 : Real) := by
    simpa [Ξ] using hPayN
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hIntBudget := hBudgetN k hk a
  have hIntCross := intervalIntegrable_crossProfile
    (E := E) (D := D) (s := s) (t := t) (zetaSrc := zetaSrc)
    (tauG := tauG) (deltaWeight := deltaWeight) (deltaCap := deltaCap)
    (N := N) (k := k) hE hs0 hst ht1 hk a
  have hIntBase : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹)
      volume (s N) v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
    rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
    intro u hu
    exact ⟨(hs0 N).trans hu.1, hu.2⟩
  let boundFn : Real → Real := fun u =>
    (15 / 4 : Real) *
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
          deltaWeight deltaCap N k a u +
      (15 / 8 : Real) * (N : Real)^(-1 : Real) * Real.sqrt u⁻¹
  have hIntBound : IntervalIntegrable boundFn volume (s N) v := by
    dsimp [boundFn]
    exact (hIntCross.const_mul (15 / 4 : Real)).add
      (hIntBase.const_mul ((15 / 8 : Real) * (N : Real)^(-1 : Real)))
  let hRate : Real → Gauss.Ω d → Real := fun u ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a v u ω
  have hPoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k 1 a u ≤ boundFn u := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simp [boundFn,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
        APrimeGeneralMovingCrossProfileSlot.crossProfile]
    · have huPos : 0 < u := lt_of_le_of_ne (hs0 N |>.trans hu.1) (Ne.symm hu0)
      let Z : Gauss.Ω d → Real := fun ω =>
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N k a u ω
      let H : Real :=
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t zetaSrc tauG deltaWeight N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (profileCap E s tauG deltaCap N u) a
      have hUwindow : u ∈ Icc (s N) (cutNetPt s (mesh D) N k) := by
        simpa [v] using hu
      have hUtime : u ∈ Icc (s N) (t N) :=
        ⟨hUwindow.1, hUwindow.2.trans hv.2⟩
      have hRatInt : Integrable (fun ω => |hRate u ω| ^ (2 : Nat)) (Gauss.P d) := by
        simpa [hRate, v, deltaWeight] using hJointN k hk Step2.sigPM a u hUwindow
      have hGoodMeas : MeasurableSet (APrimeGeneralMovingGoodMesh.good N) :=
        APrimeGeneralMovingGoodMesh.measurableSet_good N
      have hZint : Integrable (fun ω => |Z ω| ^ (2 : Nat)) (Gauss.P d) := by
        have hEq : (fun ω => |Z ω| ^ (2 : Nat)) =
            (APrimeGeneralMovingGoodMesh.good N).indicator
              (fun ω => |hRate u ω| ^ (2 : Nat)) := by
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
              have hRate0 := APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
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
                  _ ≤ _ :=
                    mul_le_mul_of_nonneg_right hprefix hprofile0
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
            (15 / 8 : Real) * (Real.sqrt u)⁻¹ *
              (H + (N : Real)^(-1 : Real)) :=
        mul_le_mul_of_nonneg_left hMomPay hcoef0
      have hCrossCoeff : (15 / 8 : Real) * (Real.sqrt u)⁻¹ * H =
          (15 / 4 : Real) *
            APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
              deltaWeight deltaCap N k a u := by
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
                  (profileCap E s tauG deltaCap N u) a := by
          rfl
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
              E D deltaWeight s t N k a u) ≤ boundFn u
      rw [hCoeffEq]
      have hMomCoef' := by simpa [Z] using hMomCoef
      dsimp [boundFn]
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
  have hMono := intervalIntegral.integral_mono_on hv.1 hIntBudget hIntBound hPoint
  have hIs := APrimeTimeInt.integral_sqrt_inv (hs0 N)
  have hIv := APrimeTimeInt.integral_sqrt_inv hv0
  have hBaseSV : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹) volume
      (s N) v := hIntBase
  have hAdj := intervalIntegral.integral_add_adjacent_intervals
    (APrimeTimeInt.intervalIntegrable_sqrt_inv (hs0 N)) hBaseSV
  rw [hIs, hIv] at hAdj
  have hSingEq : (∫ u in (s N)..v, Real.sqrt u⁻¹) =
      2 * (Real.sqrt v - Real.sqrt (s N)) := by linarith
  have hSqrtV : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv1.le
  have hSqrtS : 0 ≤ Real.sqrt (s N) := Real.sqrt_nonneg _
  have hSingLe : (∫ u in (s N)..v, Real.sqrt u⁻¹) ≤ 2 := by
    rw [hSingEq]
    nlinarith
  have hIntegralBound :
      (∫ u in (s N)..v, boundFn u) ≤
        (15 / 4 : Real) *
          (|APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| + 1) *
          (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
    have hCrossBound := hCrossN k hk a
    have hRpos : 0 < Step2Moment.ratR E s N v :=
      Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
    have hTargetNonneg : 0 ≤ (N : Real)^(5 * δ / 32) *
        Step2Moment.ratR E s N v^(-(2 : Real)) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hRpos.le _)
    have hCrossBoundAbs :
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
            deltaWeight deltaCap N k a u) ≤
          |APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| *
            ((N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : Real))) := by
      calc
        _ ≤ APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
              (N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : Real)) := hCrossBound
        _ = APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
              ((N : Real)^(5 * δ / 32) *
                Step2Moment.ratR E s N v^(-(2 : Real))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self _) hTargetNonneg
    have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
      Step2Moment.one_le_ratR hE hv.1 hv1
    have hR30 : Step2Moment.ratR E s N v ^ (30 : Nat) ≤ (N : Real) := by
      let vv : TimeIcc s t N := ⟨v, hv⟩
      have hmargin := hThirtyN vv
      have hscale : B.scale E N v ≤ (N : Real) := by
        obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N vv
        have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
          exact_mod_cast hdim.1
        change (B.W N : Real) * B.ell N v * etaT E v ≤ (N : Real)
        calc
          _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
          _ = (B.W N : Real) * (B.L N : Real) := by ring
          _ ≤ (N : Real) := hWL
      simpa [vv, Step2Moment.ratR] using hmargin.trans hscale
    have hR28 : 1 ≤ Step2Moment.ratR E s N v ^ (28 : Nat) := one_le_pow₀ hR1
    have hR2Nat : Step2Moment.ratR E s N v ^ (2 : Nat) ≤
        Step2Moment.ratR E s N v ^ (30 : Nat) := by
      calc
        _ = Step2Moment.ratR E s N v ^ 2 * 1 := by simp
        _ ≤ Step2Moment.ratR E s N v ^ 2 *
            Step2Moment.ratR E s N v ^ 28 :=
          mul_le_mul_of_nonneg_left hR28 (sq_nonneg _)
        _ = Step2Moment.ratR E s N v ^ 30 := by rw [← pow_add]
    have hR2 : Step2Moment.ratR E s N v ^ (2 : Nat) ≤ (N : Real) :=
      hR2Nat.trans hR30
    have hInv : (N : Real)^(-1 : Real) ≤
        Step2Moment.ratR E s N v^(-(2 : Real)) := by
      have hdiv := one_div_le_one_div_of_le (sq_pos_of_pos hRpos) hR2
      have hNpow : (N : Real)^(-1 : Real) = 1 / (N : Real) := by
        rw [Real.rpow_neg (by exact_mod_cast hNpos.le), Real.rpow_one]
        simp [one_div]
      have hRpow : Step2Moment.ratR E s N v^(-(2 : Real)) =
          1 / Step2Moment.ratR E s N v ^ (2 : Nat) := by
        rw [Real.rpow_neg hRpos.le]
        simp [one_div]
      rw [hNpow, hRpow]
      exact hdiv
    have hNpow1 : 1 ≤ (N : Real)^(5 * δ / 32) :=
      Real.one_le_rpow hN1 (by positivity)
    have hErr : (N : Real)^(-1 : Real) ≤
        (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
      calc
        _ ≤ Step2Moment.ratR E s N v^(-(2 : Real)) := hInv
        _ ≤ (N : Real)^(5 * δ / 32) *
            Step2Moment.ratR E s N v^(-(2 : Real)) :=
          by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hNpow1
                (Real.rpow_nonneg hRpos.le _))
    rw [show (∫ u in (s N)..v, boundFn u) =
        (15 / 4 : Real) *
          (∫ u in (s N)..v,
            APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
              deltaWeight deltaCap N k a u) +
        (15 / 8 : Real) * (N : Real)^(-1 : Real) *
          (∫ u in (s N)..v, Real.sqrt u⁻¹) by
          change (∫ u in (s N)..v,
              (15 / 4 : Real) *
                  APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t zetaSrc tauG
                    deltaWeight deltaCap N k a u +
                ((15 / 8 : Real) * (N : Real)^(-1 : Real)) * Real.sqrt u⁻¹) = _
          rw [intervalIntegral.integral_add
              (hIntCross.const_mul (15 / 4 : Real))
              (hIntBase.const_mul ((15 / 8 : Real) * (N : Real)^(-1 : Real))),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
        ]
    calc
      _ ≤ (15 / 4 : Real) *
            (|APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| *
              ((N : Real)^(5 * δ / 32) *
                Step2Moment.ratR E s N v^(-(2 : Real)))) +
          (15 / 8 : Real) * (N : Real)^(-1 : Real) * 2 := by
        have hSingCoeff0 : 0 ≤ (15 / 8 : Real) * (N : Real)^(-1 : Real) := by
          positivity
        exact add_le_add
          (mul_le_mul_of_nonneg_left hCrossBoundAbs (by norm_num))
          (mul_le_mul_of_nonneg_left hSingLe hSingCoeff0)
      _ ≤ (15 / 4 : Real) *
            (|APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| *
              ((N : Real)^(5 * δ / 32) *
                Step2Moment.ratR E s N v^(-(2 : Real)))) +
          (15 / 4 : Real) *
            ((N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : Real))) := by
        have hErr' := mul_le_mul_of_nonneg_left hErr
          (by norm_num : (0 : Real) ≤ 15 / 4)
        nlinarith
      _ = (15 / 4 : Real) *
            (|APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E| + 1) *
              (N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v^(-(2 : Real)) := by ring
  dsimp [C] at hIntegralBound ⊢
  calc
    (∫ u in (s N)..v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k 1 a u) ≤
      ∫ u in (s N)..v, boundFn u := hMono
    _ ≤ C * (N : Real)^(5 * δ / 32) *
        Step2Moment.ratR E s N v^(-(2 : Real)) := hIntegralBound

#print axioms eventually_integral_normGoodCrossBudget_le_small_slot
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingCrossBudgetNormGoodP1Slot
