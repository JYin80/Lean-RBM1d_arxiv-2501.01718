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
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingDriftGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeSlotArith

/-!
# T1283: all-fixed-order early-prefix drift-plus-full-cross N1 consumer

For each fixed moment order, combine the accepted pointwise all-order
norm-good cross estimate with T1207's full-budget payment on a prefix whose
length is at most `N^(-3D-18)`. T611 bounds the literal T615 weighted drift
by `N^(D+8)` on every sample, so its integral on that prefix is at most
`N^(-2D-10)`. The combined contribution is eventually below the actual
T230 drift slot. This is a growing-prefix N1 result, not a general A-prime
claim.
-/

namespace RBM.APrimeGeneralMovingEarlyPrefixAllOrdersN1Consumer

open Filter MeasureTheory Set Gauss CutHypTheta
open Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

private theorem drift_slot_lower_bound {E x R : ℝ}
    (hE : |E| < 2) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    1 / (2 * (mE E).im) ≤
      APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
        (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
        (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
        (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 := by
  have hmPos : 0 < (mE E).im := mE_im_pos hE
  have hRpos : 0 < R := by linarith
  have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
  have hApos : 0 < APrimeSlotArith.slotA x R := by
    unfold APrimeSlotArith.slotA
    positivity
  have hEpsNonneg : 0 ≤ APrimeSlotArith.slotEps x R := by
    unfold APrimeSlotArith.slotEps
    positivity
  have hBetaNonneg : 0 ≤ APrimeSlotArith.slotBeta x R := by
    unfold APrimeSlotArith.slotBeta
    positivity
  have hGammaNonneg : 0 ≤ APrimeSlotArith.slotGamma x R := by
    unfold APrimeSlotArith.slotGamma
    positivity
  have hJvNonneg : 0 ≤ APrimeSlotArith.slotJv x R := by
    unfold APrimeSlotArith.slotJv
    positivity
  have hXiNonneg : 0 ≤ APrimeInit.slotXi' x :=
    le_trans (by norm_num) (APrimeInit.slotXi'_ge_one hx)
  have hnear := APrimeSlotArith.driftTerm_ge_near
    (m := (mE E).im) (x := x) (R := R)
    (Ξ := APrimeInit.slotXi' x)
    (A := APrimeSlotArith.slotA x R)
    (ε := APrimeSlotArith.slotEps x R)
    (q := APrimeSlotArith.slotQ R)
    (β := APrimeSlotArith.slotBeta x R)
    (γ := APrimeSlotArith.slotGamma x R)
    (Jv := APrimeSlotArith.slotJv x R)
    hmPos (by positivity) hRpos.le hXiNonneg hApos hEpsNonneg
    hBetaNonneg hGammaNonneg hJvNonneg
  have hxpos : 0 < x := by linarith
  have hpow : x * APrimeInit.slotXi' x = x ^ (5 / 4 : ℝ) := by
    unfold APrimeInit.slotXi'
    calc
      x * x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + 1 / 4) := (Real.rpow_add hxpos 1 (1 / 4)).symm
      _ = x ^ (5 / 4 : ℝ) := by congr 1; norm_num
  have hnearEq :
      APrimeInit.slotXi' x *
        (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 =
        x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    rw [show APrimeSlotArith.slotQ R = R ^ 2 / 2 by rfl]
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hRpos, ne_of_gt hmPos]
    rw [show APrimeInit.slotXi' x * x = x * APrimeInit.slotXi' x by ring,
      hpow]
  have hnearDiv := div_le_div_of_nonneg_right hnear (le_of_lt (pow_pos hRpos 4))
  have hxpow : 1 ≤ x ^ (5 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hconstNear : 1 / (2 * (mE E).im) ≤
      x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    have h := mul_le_mul_of_nonneg_right hxpow
      (by positivity : 0 ≤ (2 * (mE E).im)⁻¹)
    simpa [div_eq_mul_inv] using h
  exact hconstNear.trans (hnearEq ▸ hnearDiv)

private theorem target_prefix_length_bound
    {D : ℝ} {s : ℕ → ℝ} {N k : ℕ}
    (hN : 0 < N)
    (hMesh : APrimeGeneralMovingMesh.targetMesh D N = (N : ℝ) ^ (4 * D + 18))
    (hEarly : (k : ℝ) ≤ (N : ℝ) ^ D) :
    cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k - s N ≤
      (N : ℝ) ^ (-3 * D - 18) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hvEq : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k - s N =
      (k : ℝ) / APrimeGeneralMovingMesh.targetMesh D N := by
    simp [CutHypTheta.cutNetPt]
  have hpow : (N : ℝ) ^ D / (N : ℝ) ^ (4 * D + 18) =
      (N : ℝ) ^ (-3 * D - 18) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  rw [hvEq, hMesh]
  calc
    (k : ℝ) / (N : ℝ) ^ (4 * D + 18) ≤
        (N : ℝ) ^ D / (N : ℝ) ^ (4 * D + 18) :=
      div_le_div_of_nonneg_right hEarly (by positivity)
    _ = (N : ℝ) ^ (-3 * D - 18) := hpow

private theorem eventually_integral_actual_g_le_early_prefix
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      (k : ℝ) ≤ (N : ℝ) ^ D →
      ∀ a : LoopArg (d.L N) 2,
        (∫ u in (s N)..cutNetPt s (mesh D) N k,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
          (N : ℝ) ^ (-2 * D - 10) := by
  have hEnvelope :=
    APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
      hE hD hs0 hst ht1 hc hreg
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  filter_upwards [hEnvelope, hMesh, Filter.eventually_ge_atTop 2] with N hEnvelopeN hMeshN hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  intro k hk hEarly a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hgi := APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
    (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
    (p := p) hE hs0 hst ht1 hNpos hk a
  have hpoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u ≤
        (N : ℝ) ^ (D + 8) := by
    intro u hu
    have hEnvPoint := hEnvelopeN k hk u hu a
    letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
    have hnorm := APrimeModel.momNormW_le_of_le_on
      (P := Gauss.P d)
      (W := APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k)
      (Y := APrimeGeneralMovingSmoothDriftNormBudget.drift E D s t N k a u)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k)
      hp (c := (N : ℝ) ^ (D + 8)) (by positivity) (G := Set.univ)
      (by intro ω _; simpa [APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
        APrimeGeneralMovingSmoothDriftNormBudget.drift, v, mesh] using hEnvPoint ω)
      (by intro ω hω; exact (hω (Set.mem_univ ω)).elim)
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift] using hnorm
  have hmono := intervalIntegral.integral_mono_on hv.1 hgi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (N : ℝ) ^ (D + 8)) volume (s N) v) hpoint
  have hMeshN : APrimeGeneralMovingMesh.targetMesh D N = (N : ℝ) ^ (4 * D + 18) := by
    simpa [mesh] using hMeshN
  have hlen := target_prefix_length_bound (s := s) hNpos hMeshN hEarly
  have hcalc :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
        (N : ℝ) ^ (-2 * D - 10) := by
    calc
      (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
          (v - s N) * (N : ℝ) ^ (D + 8) := by
        calc
          _ ≤ ∫ u in (s N)..v, (N : ℝ) ^ (D + 8) := hmono
          _ = (v - s N) * (N : ℝ) ^ (D + 8) := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
      _ ≤ (N : ℝ) ^ (-3 * D - 18) * (N : ℝ) ^ (D + 8) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = (N : ℝ) ^ (-2 * D - 10) := by
        have hNnat : 0 < N := by omega
        have hNrealPos : 0 < (N : ℝ) := by exact_mod_cast hNnat
        rw [← Real.rpow_add hNrealPos]
        congr 1
        ring
  simpa [v, mesh] using hcalc

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

set_option maxHeartbeats 5000000 in
/-- For each fixed `p ≥ 1`, the actual T1201 norm-good cross budget on every
active moving target-mesh cell has the T995 small-slot bound.  The constant
is chosen before the eventual cutoff and is independent of `N`, `k`, and `a`.
The exact moving endpoint and literal norm-good restriction are retained. -/
theorem eventually_integral_actual_drift_full_cross_le_N1_slot
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
      (k : ℝ) ≤ (N : ℝ) ^ D →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        let x := (N : ℝ) ^ (δ / 8)
        let R := Step2Moment.ratR E s N v
        2 * (∫ r in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a r +
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r) ≤
          APrimeOneStep.driftTerm (mE E).im x R
            (APrimeInit.slotXi' x)
            (APrimeSlotArith.slotA x R)
            (APrimeSlotArith.slotEps x R)
            (APrimeSlotArith.slotQ R)
            (APrimeSlotArith.slotBeta x R)
            (APrimeSlotArith.slotGamma x R)
            (APrimeSlotArith.slotJv x R) / R ^ 4 := by
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
  have hBudgetInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdw.le p hp
  have hThirty := hreg.1.pow_thirty_le hE hst ht1
  have hdw0 : 0 ≤ deltaWeight := by
    dsimp [deltaWeight, APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hFullCross :=
    APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      hE hD hs0 hst ht1 hc hreg hdw0 p hp
  have hFullInt :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hdw0 p hp
  have hMicro :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (s := s) (t := t)
      hE (by linarith) hs0 hst ht1 hc hreg hδ hδsmall
  have hDriftEnvelope :=
    APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
      hE hD hs0 hst ht1 hc hreg
  have hDriftIntegral :=
    eventually_integral_actual_g_le_early_prefix
      hE hD hs0 hst ht1 hc hreg hδ hδsmall p hp
  have hEtaLower :=
    Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  let alpha : ℝ := 13 * δ / 640
  let eMain : ℝ := alpha - 3 * D / 2 - 8
  let eError : ℝ := -3 * D / 2 - 10
  let mainCoeff : ℝ := (15 * (p : ℝ) / 2) *
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst
  let errorCoeff : ℝ := 15 * (p : ℝ) / 2
  have hdeltaOne : δ ≤ 1 := hδsmall.trans (min_le_left 1 (c / 100))
  have hMainExponent : eMain < -1 := by
    dsimp [eMain, alpha]
    nlinarith
  have hErrorExponent : eError < -1 := by
    dsimp [eError]
    linarith
  have hDriftExponent : -2 * D - 10 < -1 := by linarith
  have hMainAbsorb := APrimeSlotArith.eventually_const_mul_rpow_le
    (c := mainCoeff) (η := eMain) (θ := -1) hMainExponent
  have hErrorAbsorb := APrimeSlotArith.eventually_const_mul_rpow_le
    (c := errorCoeff) (η := eError) (θ := -1) hErrorExponent
  have hSlotAbsorb := APrimeSlotArith.eventually_const_mul_rpow_le
    (c := 12 * (mE E).im) (η := -1) (θ := 0) (by norm_num)
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hPay, hJointInt, hPrefix, hQV, hBudgetInt,
      hThirty, hEnvPoly, hEnvJoint, B.dim, eventually_ge_atTop 2,
      hFullCross, hFullInt, hMicro, hDriftEnvelope, hDriftIntegral,
      hEtaLower, hMesh, hMainAbsorb, hErrorAbsorb, hSlotAbsorb]
    with N hPayN hJointN hPrefixN hQVN hBudgetN hThirtyN hEnvN
      hEnvJointN hdim hN hFullCrossN hFullIntN hMicroN hDriftEnvelopeN
      hDriftIntegralN hEtaLowerN hMeshN hMainAbsorbN hErrorAbsorbN hSlotAbsorbN
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by
    have h : 1 ≤ N := by omega
    exact_mod_cast h
  have hNrealPos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hEnv0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hEnvPay :
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
          ((Gauss.P d (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤
        (N : ℝ)^(-1 : ℝ) := by
    simpa [Ξ] using hPayN
  have hKbad : 0 ≤ Kbad := by dsimp [Kbad]; positivity
  intro k hk hEarly a
  by_cases hk0 : k = 0
  · subst k
    have hv0 : cutNetPt s (mesh D) N 0 = s N := by
      simp [CutHypTheta.cutNetPt]
    have hvtime : s N < 1 := (hst N).trans_lt (ht1 N)
    have hR1 : 1 ≤ Step2Moment.ratR E s N (s N) := by
      exact Step2Moment.one_le_ratR hE (le_rfl) hvtime
    have hx : 1 ≤ (N : ℝ) ^ (δ / 8) :=
      Real.one_le_rpow hN1 (by positivity)
    have hslot := drift_slot_lower_bound hE hx hR1
    have hslotNonneg : 0 ≤
        APrimeOneStep.driftTerm (mE E).im ((N : ℝ) ^ (δ / 8))
          (Step2Moment.ratR E s N (s N))
          (APrimeInit.slotXi' ((N : ℝ) ^ (δ / 8)))
          (APrimeSlotArith.slotA ((N : ℝ) ^ (δ / 8))
            (Step2Moment.ratR E s N (s N)))
          (APrimeSlotArith.slotEps ((N : ℝ) ^ (δ / 8))
            (Step2Moment.ratR E s N (s N)))
          (APrimeSlotArith.slotQ (Step2Moment.ratR E s N (s N)))
          (APrimeSlotArith.slotBeta ((N : ℝ) ^ (δ / 8))
            (Step2Moment.ratR E s N (s N)))
          (APrimeSlotArith.slotGamma ((N : ℝ) ^ (δ / 8))
            (Step2Moment.ratR E s N (s N)))
          (APrimeSlotArith.slotJv ((N : ℝ) ^ (δ / 8))
            (Step2Moment.ratR E s N (s N))) /
          (Step2Moment.ratR E s N (s N)) ^ 4 := by
      have hmPos : 0 < (mE E).im := mE_im_pos hE
      exact le_trans (by positivity) hslot
    simpa [hv0, deltaWeight] using hslotNonneg
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
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap
                  E s tauG deltaCap N r) a) ^ 2 := by
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
                      (APrimeGeneralMovingQVProfile.generalMovingBlockCap
                        E s tauG deltaCap N r) a) ^ 2) +
                    APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N *
                      ((Gauss.P d (Ξ N)ᶜ).toReal)^((1 : ℝ) / (2 * p : ℕ)) := by
              simpa [Z, m, v, mesh, Nat.cast_mul] using hEventNorm
            calc
              _ ≤ APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                    E D s t zetaSrc tauG deltaWeight N k *
                  Real.sqrt ((APrimeGeneralMovingQVAbsorption.absorbedRootProfile
                    E s zetaSrc N r v D
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap
                      E s tauG deltaCap N r) a) ^ 2) +
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
          field_simp [show (p : ℝ) ≠ 0 by
              exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp)),
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
    let x := (N : ℝ) ^ (δ / 8)
    let R := Step2Moment.ratR E s N v
    have hx : 1 ≤ x := by
      dsimp [x]
      exact Real.one_le_rpow hN1 (by positivity)
    have hR1 : 1 ≤ R := Step2Moment.one_le_ratR hE hv.1 hv1
    have hRpos : 0 < R := Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
    have hslot := drift_slot_lower_bound hE hx hR1
    have hgi := APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      (deltaWeight := deltaWeight) (p := p) hE hs0 hst ht1 hNpos hk a
    have hfullInt : IntervalIntegrable
        (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a) volume (s N) v := by
      simpa [v, mesh, deltaWeight] using hFullIntN k hk a
    have hsumInt : IntervalIntegrable
        (fun r => APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r +
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r) volume (s N) v := hgi.add hfullInt
    have hEarlyLength := target_prefix_length_bound (s := s) hNpos
      (by simpa [mesh] using hMeshN) hEarly
    have hGapNonneg : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt hv.1)
    have hGapSq : (Real.sqrt v - Real.sqrt (s N)) ^ 2 ≤ v - s N := by
      have hvSq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv0
      have hsSq : (Real.sqrt (s N)) ^ 2 = s N := Real.sq_sqrt (hs0 N)
      nlinarith [mul_nonneg (Real.sqrt_nonneg (s N)) hGapNonneg]
    have hGapSqrt : Real.sqrt v - Real.sqrt (s N) ≤ Real.sqrt (v - s N) :=
      (Real.le_sqrt hGapNonneg (sub_nonneg.mpr hv.1)).2 hGapSq
    let eHalf : ℝ := -3 * D / 2 - 9
    have hSqrtPower : Real.sqrt ((N : ℝ) ^ (-3 * D - 18)) =
        (N : ℝ) ^ eHalf := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNrealPos.le]
      congr 1
      dsimp [eHalf]
      ring
    have hGapBound : Real.sqrt v - Real.sqrt (s N) ≤ (N : ℝ) ^ eHalf := by
      calc
        _ ≤ Real.sqrt (v - s N) := hGapSqrt
        _ ≤ Real.sqrt ((N : ℝ) ^ (-3 * D - 18)) := Real.sqrt_le_sqrt hEarlyLength
        _ = (N : ℝ) ^ eHalf := hSqrtPower
    have hEtaAtS : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (s N) := by
      calc
        _ ≤ etaT E (t N) := hEtaLowerN
        _ ≤ etaT E (s N) := Gauss.etaT_le_of_le hE (hst N)
    have hEtaSPos : 0 < etaT E (s N) :=
      Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
    have hEtaInvS : (etaT E (s N))⁻¹ ≤ (N : ℝ) := by
      have hi := inv_anti₀ (Real.rpow_pos_of_pos hNrealPos (-(1 : ℝ))) hEtaAtS
      simpa only [Real.rpow_neg hNrealPos.le, Real.rpow_one, inv_inv] using hi
    have hEtaInvSPow : (etaT E (s N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
      simpa [Real.rpow_one] using hEtaInvS
    have hRinv0 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
    have hRinvLe : R ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
    have hMainPower : (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ *
        (Real.sqrt v - Real.sqrt (s N)) ≤ (N : ℝ) ^ eMain := by
      have hEtaGap : (etaT E (s N))⁻¹ *
          (Real.sqrt v - Real.sqrt (s N)) ≤
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ eHalf := by
        calc
          _ ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ eHalf :=
            mul_le_mul hEtaInvSPow hGapBound hGapNonneg (by positivity)
          _ = _ := by rw [Real.rpow_one]
      calc
        _ = (N : ℝ) ^ alpha *
            ((etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N))) := by ring
        _ ≤ (N : ℝ) ^ alpha *
            ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ eHalf) :=
          mul_le_mul_of_nonneg_left hEtaGap (Real.rpow_nonneg hNrealPos.le _)
        _ = (N : ℝ) ^ eMain := by
          rw [← Real.rpow_add hNrealPos]
          rw [← Real.rpow_add hNrealPos]
          congr 1
          dsimp [eMain, alpha, eHalf]
          ring
    have hErrorPower : (N : ℝ) ^ (-(1 : ℝ)) *
        (Real.sqrt v - Real.sqrt (s N)) ≤ (N : ℝ) ^ eError := by
      calc
        _ ≤ (N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ eHalf :=
          mul_le_mul_of_nonneg_left hGapBound
            (Real.rpow_nonneg hNrealPos.le _)
        _ = (N : ℝ) ^ eError := by
          rw [← Real.rpow_add hNrealPos]
          congr 1
          dsimp [eError, eHalf]
          ring
    have hpointFinal : ∀ r ∈ Icc (s N) v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r ≤
          ((15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) +
            (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ))) / Real.sqrt r := by
      intro r hr
      by_cases hrpos : 0 < r
      · have hOld := hpoint r hr
        have hMicroscopic := hMicroN k hk a r hr hrpos
        have hMicroscopic' :
            RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              zetaSrc tauG deltaWeight deltaCap N k a r ≤
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) / Real.sqrt r := by
          simpa [v, mesh, zetaSrc, tauG, deltaWeight, deltaCap, alpha, R] using hMicroscopic
        have hKpos : 0 ≤ K := by dsimp [K]; positivity
        calc
          _ ≤ K * RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                zetaSrc tauG deltaWeight deltaCap N k a r +
              Kbad * (N : ℝ) ^ (-(1 : ℝ)) / Real.sqrt r := hOld
          _ ≤ K *
                (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                  (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) / Real.sqrt r) +
              Kbad * (N : ℝ) ^ (-(1 : ℝ)) / Real.sqrt r := by
            gcongr
          _ = _ := by dsimp [K, Kbad]; ring
      · have hr0 : 0 ≤ r := (hs0 N).trans hr.1
        have hrEq : r = 0 := le_antisymm (not_lt.mp hrpos) hr0
        subst r
        have hOld := hpoint 0 hr
        simpa [RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile] using hOld
    let Cpoint : ℝ :=
      (15 * (p : ℝ) / 4) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) +
      (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ))
    have hPointInt : IntervalIntegrable (fun r : ℝ => Cpoint / Real.sqrt r)
        volume (s N) v := by
      exact APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
        Cpoint (s N) v (hs0 N) hv.1
    have hGoodMono := intervalIntegral.integral_mono_on hv.1 hBudget hPointInt hpointFinal
    have hGoodLe :
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r) ≤
          2 * Cpoint * (Real.sqrt v - Real.sqrt (s N)) := by
      calc
        _ ≤ ∫ r in (s N)..v, Cpoint / Real.sqrt r := hGoodMono
        _ = 2 * Cpoint * (Real.sqrt v - Real.sqrt (s N)) :=
          APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
            Cpoint (s N) v (hs0 N) hv.1
    have hFullCrossSmall :
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r) ≤
          (15 * (p : ℝ) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
                (Real.sqrt v - Real.sqrt (s N)) +
            (15 * (p : ℝ) / 2) * (N : ℝ) ^ (-(1 : ℝ)) *
                (Real.sqrt v - Real.sqrt (s N)) := by
      have hFull := hFullCrossN k hk a
      have hFull' :
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D deltaWeight s t N k p a r) ≤
            (∫ r in (s N)..v,
              APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
                E D deltaWeight s t N k p a r) +
              (15 * (p : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
                (Real.sqrt v - Real.sqrt (s N)) := by
        simpa [v, mesh, deltaWeight] using hFull
      calc
        _ ≤ (∫ r in (s N)..v,
              APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
                E D deltaWeight s t N k p a r) +
              (15 * (p : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
                (Real.sqrt v - Real.sqrt (s N)) := hFull'
        _ ≤ 2 * Cpoint * (Real.sqrt v - Real.sqrt (s N)) +
              (15 * (p : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
                (Real.sqrt v - Real.sqrt (s N)) := by
          nlinarith [hGoodLe]
        _ = _ := by dsimp [Cpoint]; ring
    have hMainTerm :
        (15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N)) ≤ mainCoeff * (N : ℝ) ^ eMain := by
      have hcp : 0 ≤ mainCoeff := by
        have hC :
            0 < APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
        dsimp [mainCoeff]
        positivity
      calc
        _ = mainCoeff *
            ((N : ℝ) ^ alpha * (etaT E (s N))⁻¹ *
              (Real.sqrt v - Real.sqrt (s N))) * R ^ (-(2 : ℝ)) := by
                dsimp [mainCoeff]
                ring
        _ ≤ mainCoeff * (N : ℝ) ^ eMain * R ^ (-(2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMainPower hcp) hRinv0
        _ ≤ mainCoeff * (N : ℝ) ^ eMain := by
          calc
            _ = (mainCoeff * (N : ℝ) ^ eMain) * R ^ (-(2 : ℝ)) := by ring
            _ ≤ (mainCoeff * (N : ℝ) ^ eMain) * 1 :=
              mul_le_mul_of_nonneg_left hRinvLe (by positivity)
            _ = _ := by ring
    have hErrorTerm :
        (15 * (p : ℝ) / 2) * (N : ℝ) ^ (-(1 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) ≤ errorCoeff * (N : ℝ) ^ eError := by
      have hscaled := mul_le_mul_of_nonneg_left hErrorPower
        (by positivity : 0 ≤ (15 * (p : ℝ) / 2))
      calc
        _ = (15 * (p : ℝ) / 2) *
            ((N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt v - Real.sqrt (s N))) := by ring
        _ ≤ _ := by simpa [errorCoeff] using hscaled
    have hCrossEstimate :
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r) ≤
          mainCoeff * (N : ℝ) ^ eMain + errorCoeff * (N : ℝ) ^ eError := by
      exact (hFullCrossSmall.trans (add_le_add hMainTerm hErrorTerm))
    have hDriftBound :
        (∫ r in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r) ≤
          (N : ℝ) ^ (-(1 : ℝ)) := by
      calc
        _ ≤ (N : ℝ) ^ (-2 * D - 10) := by
          simpa [v, mesh, deltaWeight] using hDriftIntegralN k hk hEarly a
        _ ≤ (N : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hDriftExponent.le
    have hCrossBoundN' :
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r) ≤ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by
      calc
        _ ≤ mainCoeff * (N : ℝ) ^ eMain + errorCoeff * (N : ℝ) ^ eError :=
          hCrossEstimate
        _ ≤ (N : ℝ) ^ (-(1 : ℝ)) + (N : ℝ) ^ (-(1 : ℝ)) :=
          add_le_add hMainAbsorbN hErrorAbsorbN
        _ = 2 * (N : ℝ) ^ (-(1 : ℝ)) := by ring
    have hTotalLe :
        2 * ((∫ r in (s N)..v,
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r) +
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D deltaWeight s t N k p a r)) ≤
          6 * (N : ℝ) ^ (-(1 : ℝ)) := by
      have hAdd := add_le_add hDriftBound hCrossBoundN'
      calc
        _ ≤ 2 * ((N : ℝ) ^ (-(1 : ℝ)) +
            2 * (N : ℝ) ^ (-(1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hAdd (by norm_num)
        _ = 6 * (N : ℝ) ^ (-(1 : ℝ)) := by ring
    have hSlotAbsorbN' : 12 * (mE E).im * (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 := by
      simpa [Real.rpow_zero] using hSlotAbsorbN
    have hSmallSlot : 6 * (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 / (2 * (mE E).im) := by
      have hmPos : 0 < (mE E).im := mE_im_pos hE
      apply (le_div_iff₀ (by positivity : 0 < 2 * (mE E).im)).2
      calc
        6 * (N : ℝ) ^ (-(1 : ℝ)) * (2 * (mE E).im) =
            12 * (mE E).im * (N : ℝ) ^ (-(1 : ℝ)) := by ring
        _ ≤ 1 := hSlotAbsorbN'
    have hTargetIntegral :
        2 * ((∫ r in (s N)..v,
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r) +
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D deltaWeight s t N k p a r)) ≤
          APrimeOneStep.driftTerm (mE E).im x R
            (APrimeInit.slotXi' x)
            (APrimeSlotArith.slotA x R)
            (APrimeSlotArith.slotEps x R)
            (APrimeSlotArith.slotQ R)
            (APrimeSlotArith.slotBeta x R)
            (APrimeSlotArith.slotGamma x R)
            (APrimeSlotArith.slotJv x R) / R ^ 4 :=
      hTotalLe.trans (hSmallSlot.trans hslot)
    have hgiV : IntervalIntegrable
        (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a)
        volume (s N) v := by
      simpa [v, mesh, deltaWeight,
        APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hgi
    change 2 * (∫ r in (s N)..v,
      APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r +
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D deltaWeight s t N k p a r) ≤ _
    rw [intervalIntegral.integral_add hgiV hfullInt]
    exact hTargetIntegral

/-! The T995 witness also satisfies the early-prefix cutoff `k = 1 ≤ N^60`.
The same sample carries the event, active cell, widened weight, and positive
actual smooth weight. -/
theorem nondegenerate_scheduled_early_prefix_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ min 1 (c / 100) →
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            (1 : ℝ) ≤ (N : ℝ) ^ 60 ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t
              (APrimeGeneralMovingMesh.targetMesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh 60) N) ω := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hResident⟩ :=
    APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro δ hδ hsmall
  have hResidentδ := hResident δ hδ hsmall
  filter_upwards [hResidentδ, Filter.eventually_ge_atTop 1] with N hN hN1
  obtain ⟨hwindow, ω, hω, hactive, hwide, hpositive⟩ := hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hprefix : (1 : ℝ) ≤ (N : ℝ) ^ 60 := by
    exact one_le_pow₀ hNreal
  exact ⟨hwindow, ω, hω, hactive, hprefix, hwide, hpositive⟩

#print axioms eventually_integral_actual_drift_full_cross_le_N1_slot
#print axioms nondegenerate_scheduled_early_prefix_witness

end
end RBM.APrimeGeneralMovingEarlyPrefixAllOrdersN1Consumer
