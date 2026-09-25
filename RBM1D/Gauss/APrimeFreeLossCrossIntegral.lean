/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot

/-!
# T1309: free-loss conditional integration of the literal cross profile

Assume uniform bounds for the actual transition-prefix gradient rate and the
complete absorbed root profile, with source losses `h = λ / 1000`, actual
weight loss `λ`, and cap `2 λ`. Their product has `N^(3h) η_s⁻¹ R_v⁻²`
scale. The remaining `u⁻¹/²` kernel integrates through `s = 0`; the endpoint
`k = 0` is handled as a degenerate interval.

This is only the deterministic conditional integration arrow. It proves
neither of the two profile bounds nor an event-level/final A-prime estimate.
-/

namespace RBM.APrimeFreeLossCrossIntegral

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

noncomputable def profileCap (E : Real) (s : Nat → Real)
    (h deltaCap : Real) (N : Nat) (u : Real) : Real :=
  APrimeGeneralMovingQVProfile.generalMovingBlockCap E s h deltaCap N u

private theorem continuousOn_absorbedRootProfile
    {E h deltaCap : Real} {s : Nat → Real} {N : Nat}
    {v D : Real} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (a : LoopArg (B.L N) 2) :
    ContinuousOn
      (fun u => APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
        h N u v D (profileCap E s h deltaCap N u) a)
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
    exact Step2Moment.ratR_pos hE (hsv.trans_lt hv1) (hu.2.trans_lt hv1)
  have hRatNeg : ContinuousOn (fun u =>
      Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (hRatPos u hu).ne')
  have hJ : ContinuousOn (fun u => profileCap E s h deltaCap N u) I := by
    unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap
    exact continuousOn_const.add
      (continuousOn_const.mul
        ((continuousOn_const.mul
          (continuousOn_const.mul (hRat.pow 4))).add continuousOn_const))
  have hNear : ContinuousOn (fun u =>
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u +
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
        (profileCap E s h deltaCap N u)) I := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    exact ((continuousOn_const.mul hInvEta).mul hScaleNeg).mul (hJ.pow 3)
  unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
  exact (hRatNeg.mul continuousOn_const).mul
    ((hNear.sqrt.mul continuousOn_const).add
      (hFar.sqrt.mul continuousOn_const))

private theorem intervalIntegrable_crossProfile
    {E D : Real} {s t : Nat → Real} {lambda : Real}
    {N k : Nat} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (B.L N) 2) :
    let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
    IntervalIntegrable
      (APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        (lambda / 1000) (lambda / 1000) lambda (2 * lambda) N k a)
      volume (s N) v := by
  let h : Real := lambda / 1000
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
  have hRoot := continuousOn_absorbedRootProfile (E := E) (h := h)
    (deltaCap := 2 * lambda) (s := s) (N := N) (v := v) (D := D)
    hE hs0 hv.1 hv1 a
  have hFactor : ContinuousOn (fun u =>
      (1 / 2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t h h lambda N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
          (profileCap E s h (2 * lambda) N u) a) (Icc (s N) v) := by
    exact continuousOn_const.mul hRoot
  have hinv : ∀ u : Real,
      (2 * Real.sqrt u)⁻¹ = (Real.sqrt u)⁻¹ / 2 := by
    intro u
    rw [mul_inv_rev]
    norm_num
    ring
  have hfun :
      (fun u => (2 * Real.sqrt u)⁻¹ *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t h h lambda N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
          (profileCap E s h (2 * lambda) N u) a) =
      (fun u => Real.sqrt u⁻¹ * ((1 / 2 : Real) *
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t h h lambda N k *
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
          (profileCap E s h (2 * lambda) N u) a)) := by
    funext u
    rw [hinv, ← Real.sqrt_inv u]
    simp only [div_eq_mul_inv]
    ac_rfl
  change IntervalIntegrable (fun u => (2 * Real.sqrt u)⁻¹ *
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t h h lambda N k *
      APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
        (profileCap E s h (2 * lambda) N u) a) volume (s N) v
  rw [hfun]
  exact hBase.mul_continuousOn
    (by simpa only [Set.uIcc_of_le hv.1] using hFactor)

private theorem integral_eta_sqrt_inv_le {E s v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    (etaT E s)⁻¹ * (∫ u in s..v, Real.sqrt u⁻¹) ≤
      2 / (mE E).im := by
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hm : 0 < (mE E).im := mE_im_pos hE
  have heta : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hIntS := APrimeTimeInt.integral_sqrt_inv hs0
  have hIntV := APrimeTimeInt.integral_sqrt_inv (hs0.trans hsv)
  have hbaseSV : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹) volume s v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv (hs0.trans hsv)).mono_set
    rw [Set.uIcc_of_le hsv, Set.uIcc_of_le (hs0.trans hsv)]
    intro u hu
    exact ⟨hs0.trans hu.1, hu.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (APrimeTimeInt.intervalIntegrable_sqrt_inv hs0) hbaseSV
  rw [hIntS, hIntV] at hadd
  have hIntEq : (∫ u in s..v, Real.sqrt u⁻¹) =
      2 * (Real.sqrt v - Real.sqrt s) := by linarith
  rw [hIntEq]
  have hsqrtv : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hsqrts : s ≤ Real.sqrt s := by
    have hsqrts1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1.le
    nlinarith [Real.sqrt_nonneg s, Real.sq_sqrt hs0]
  unfold etaT
  have hdiff : Real.sqrt v - Real.sqrt s ≤ 1 - s := by linarith
  have hbound : 2 * (Real.sqrt v - Real.sqrt s) ≤ 2 * (1 - s) := by nlinarith
  have hden : 0 < (1 - s) * (mE E).im := by positivity
  calc
    _ ≤ (etaT E s)⁻¹ * (2 * (1 - s)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr heta.le)
    _ = 2 / (mE E).im := by
      unfold etaT
      have h1s : 1 - s ≠ 0 := by linarith
      field_simp [h1s, ne_of_gt hm]

/-- If the actual free-loss transition rate and the entire absorbed root
profile have the stated uniform closed-cell bounds, their literal product
integrates to the claimed `N^(3h) R_v⁻²` scale on every active target cell.
The first cell may start at `s = 0`; the singular kernel is integrable there.
At `k = 0`, `cutNetPt_zero` makes the interval degenerate and its integral is
exactly zero. -/
theorem eventually_integral_crossProfile_le_of_uniform_profiles
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (_hD : 0 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (_hc : 0 < c)
    {lambda C_T C_A : Real} (_hlambda : 0 < lambda)
    (_hlambdaSmall : lambda ≤ min (1 / 10000) (c / 10000))
    (hCT : 0 < C_T) (hCA : 0 < C_A)
    (hTransition : ∀ᶠ N : Nat in atTop,
      ∀ k : Nat, k ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N →
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
          E D s t (lambda / 1000) (lambda / 1000) lambda N k ≤
        C_T * (N : Real)^(lambda / 1000) *
          (etaT E (s N))^(-(1 / 2 : Real)))
    (hAbsorbed : ∀ᶠ N : Nat in atTop,
      ∀ k : Nat, k ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (B.L N) 2,
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      ∀ u ∈ Icc (s N) v,
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
          (lambda / 1000) N u v D
          (profileCap E s (lambda / 1000) (2 * lambda) N u) a ≤
        C_A * (N : Real)^(2 * (lambda / 1000)) *
          (etaT E (s N))^(-(1 / 2 : Real)) *
          Step2Moment.ratR E s N v^(-(2 : Real))) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (B.L N) 2,
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          (lambda / 1000) (lambda / 1000) lambda (2 * lambda) N k a u) ≤
        (C_T * C_A / (mE E).im) *
          (N : Real)^(3 * (lambda / 1000)) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
  have hNevent := hTransition.and hAbsorbed
  filter_upwards [hNevent, eventually_ge_atTop 1] with N ⟨hTransitionN, hAbsorbedN⟩ hN
  intro k hk a
  let h : Real := lambda / 1000
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hS : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hNreal : (1 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hNpos : (0 : Real) < (N : Real) := by linarith
  have hR : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hRpow : 0 ≤ Step2Moment.ratR E s N v^(-(2 : Real)) :=
    Real.rpow_nonneg hR.le _
  have hIm : 0 < (mE E).im := mE_im_pos hE
  have hTarget0 : 0 ≤ (C_T * C_A / (mE E).im) *
      (N : Real)^(3 * h) * Step2Moment.ratR E s N v^(-(2 : Real)) := by
    positivity
  have hCrossInt : IntervalIntegrable
      (APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
        h h lambda (2 * lambda) N k a) volume (s N) v := by
    simpa only [h, v] using intervalIntegrable_crossProfile
      (E := E) (D := D) (s := s) (t := t) (lambda := lambda)
      (N := N) (k := k) hE hs0 hst ht1 hk a
  by_cases hk0 : k = 0
  · subst k
    simpa [h, v, cutNetPt_zero] using hTarget0
  · have hActivePos : 0 < k := Nat.pos_of_ne_zero hk0
    have hEtaS : 0 < etaT E (s N) := hS
    have hSourceBound := hTransitionN k hk
    have hT0 : 0 ≤ APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
        E D s t h h lambda N k :=
      APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate_nonneg
        E D s t h h lambda N k
    have hRateBound0 : 0 ≤ C_T * (N : Real)^h *
        (etaT E (s N))^(-(1 / 2 : Real)) := by positivity
    have hBaseExp : (N : Real)^h * (N : Real)^(2 * h) =
        (N : Real)^(3 * h) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hEtaExp : (etaT E (s N))^(-(1 / 2 : Real)) *
        (etaT E (s N))^(-(1 / 2 : Real)) = (etaT E (s N))⁻¹ := by
      rw [← Real.rpow_add hS]
      rw [show -(1 / 2 : Real) + -(1 / 2 : Real) = -1 by norm_num,
        Real.rpow_neg hS.le, Real.rpow_one]
    have hpoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          h h lambda (2 * lambda) N k a u ≤
        ((C_T * C_A / 2) * (N : Real)^(3 * h) *
            (etaT E (s N))⁻¹ *
            Step2Moment.ratR E s N v^(-(2 : Real))) * Real.sqrt u⁻¹ := by
      intro u hu
      have huWindow : u ∈ Icc (s N) (t N) :=
        ⟨hu.1, hu.2.trans hv.2⟩
      have hRootBound := hAbsorbedN k hk a u hu
      have hRoot0 : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
          (profileCap E s h (2 * lambda) N u) a := by
        have hEllU : 0 < B.ell N u := zero_lt_one.trans_le
          (one_le_ellHat_of_nonneg (B.one_le_L N)
            ((hs0 N).trans huWindow.1) (huWindow.2.trans_lt (ht1 N)))
        have hEtaU : 0 < etaT E u :=
          Step2.etaT_pos' hE (huWindow.2.trans_lt (ht1 N))
        have hRu : 0 < Step2Moment.ratR E s N u :=
          Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N))
            (huWindow.2.trans_lt (ht1 N))
        have hScaleU : 0 < B.scale E N u := by
          change 0 < (B.W N : Real) * B.ell N u * etaT E u
          have hW : (0 : Real) < B.W N := by exact_mod_cast B.W_pos N
          positivity
        have hNear0 : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate E s h N u +
            2 * (B.W N : Real)⁻¹ := by
          unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
          have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
          have hEllS : 0 < B.ell N (s N) := zero_lt_one.trans_le
            (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
              ((hst N).trans_lt (ht1 N)))
          have hCNear : 0 ≤ Lemma57.cNear2 (B.W N : Real) (B.ell N u) :=
            Lemma57.cNear2_nonneg hW1 hEllU
          positivity
        have hCap0 : 0 ≤ profileCap E s h (2 * lambda) N u := by
          unfold profileCap APrimeGeneralMovingQVProfile.generalMovingBlockCap
          positivity
        have hFar0 : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
            (profileCap E s h (2 * lambda) N u) := by
          unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
          positivity
        have hXi0 : 0 ≤ Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
          Step2.xiK_nonneg _ _ _
        have hChi0 : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : Real) <=
            6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
          split_ifs <;> norm_num
        unfold APrimeGeneralMovingQVAbsorption.absorbedRootProfile
        positivity
      have hRootBound0 : 0 ≤ C_A * (N : Real)^(2 * h) *
          (etaT E (s N))^(-(1 / 2 : Real)) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by positivity
      have hProduct :
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t h h lambda N k *
            APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
              (profileCap E s h (2 * lambda) N u) a ≤
          C_T * C_A * (N : Real)^(3 * h) * (etaT E (s N))⁻¹ *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
        calc
          _ ≤ (C_T * (N : Real)^h * (etaT E (s N))^(-(1 / 2 : Real))) *
              (C_A * (N : Real)^(2 * h) * (etaT E (s N))^(-(1 / 2 : Real)) *
                Step2Moment.ratR E s N v^(-(2 : Real))) :=
            mul_le_mul hSourceBound hRootBound hRoot0 hRateBound0
          _ = _ := by
            calc
              _ = C_T * C_A *
                  ((N : Real)^h * (N : Real)^(2 * h)) *
                  ((etaT E (s N))^(-(1 / 2 : Real)) *
                    (etaT E (s N))^(-(1 / 2 : Real))) *
                  Step2Moment.ratR E s N v^(-(2 : Real)) := by ring
              _ = _ := by rw [hBaseExp, hEtaExp]
              _ = _ := by ring
      have hinv : (2 * Real.sqrt u)⁻¹ = Real.sqrt u⁻¹ / 2 := by
        rw [mul_inv_rev]
        norm_num
        ring
      have hu0 : 0 ≤ Real.sqrt u⁻¹ := by positivity
      calc
        _ = Real.sqrt u⁻¹ * ((1 / 2 : Real) *
            (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t h h lambda N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u v D
                (profileCap E s h (2 * lambda) N u) a)) := by
          unfold APrimeGeneralMovingCrossProfileSlot.crossProfile
          rw [hinv]
          change Real.sqrt u⁻¹ / 2 *
              APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                E D s t h h lambda N k *
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap
                  E s h (2 * lambda) N u) a =
            Real.sqrt u⁻¹ * ((1 / 2 : Real) *
              (APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
                  E D s t h h lambda N k *
                APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s h N u
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) D
                  (APrimeGeneralMovingQVProfile.generalMovingBlockCap
                    E s h (2 * lambda) N u) a))
          ring
        _ ≤ Real.sqrt u⁻¹ * ((1 / 2 : Real) *
            (C_T * C_A * (N : Real)^(3 * h) * (etaT E (s N))⁻¹ *
              Step2Moment.ratR E s N v^(-(2 : Real)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hProduct (by norm_num)) hu0
        _ = ((C_T * C_A / 2) * (N : Real)^(3 * h) *
            (etaT E (s N))⁻¹ * Step2Moment.ratR E s N v^(-(2 : Real))) *
              Real.sqrt u⁻¹ := by ring
    let coeff := (C_T * C_A / 2) * (N : Real)^(3 * h) *
      (etaT E (s N))⁻¹ * Step2Moment.ratR E s N v^(-(2 : Real))
    have hCoeff0 : 0 ≤ coeff := by dsimp [coeff]; positivity
    have hBaseInt : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹)
        volume (s N) v := by
      apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
      rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
      intro x hx
      exact ⟨(hs0 N).trans hx.1, hx.2⟩
    have hDomInt : IntervalIntegrable (fun u : Real => coeff * Real.sqrt u⁻¹)
        volume (s N) v := hBaseInt.const_mul coeff
    have hmono := intervalIntegral.integral_mono_on hv.1 hCrossInt hDomInt hpoint
    have hEtaInt := integral_eta_sqrt_inv_le hE (hs0 N) hv.1 hv1
    have hIntegralBound :
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            h h lambda (2 * lambda) N k a u) ≤
          (C_T * C_A / (mE E).im) * (N : Real)^(3 * h) *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
      calc
        _ ≤ ∫ u in (s N)..v, coeff * Real.sqrt u⁻¹ := hmono
        _ = coeff * (∫ u in (s N)..v, Real.sqrt u⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
        _ = ((C_T * C_A / 2) * (N : Real)^(3 * h) *
            Step2Moment.ratR E s N v^(-(2 : Real))) *
              ((etaT E (s N))⁻¹ * (∫ u in (s N)..v, Real.sqrt u⁻¹)) := by
          dsimp [coeff]
          ring
        _ ≤ ((C_T * C_A / 2) * (N : Real)^(3 * h) *
            Step2Moment.ratR E s N v^(-(2 : Real))) *
              (2 / (mE E).im) := by
          apply mul_le_mul_of_nonneg_left hEtaInt
          positivity
        _ = _ := by ring
    change (∫ u in (s N)..v,
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          h h lambda (2 * lambda) N k a u) ≤ _
    exact hIntegralBound

/-! The common-source producer supplies a concrete nondegenerate
moving-window/model witness for the underlying mesh and regularity domain.
The two profile bounds remain the explicit conditional inputs of the theorem
above. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingCommonSources.positive_length_common_support_witness

#print axioms eventually_integral_crossProfile_le_of_uniform_profiles
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeFreeLossCrossIntegral
