/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingFullDriftProfileSlotRepair
import RBM1D.Gauss.APrimeGeneralMovingNearMainStrictExponent
import RBM1D.Gauss.APrimeGeneralMovingFarLinearStrictExponent
import RBM1D.Gauss.APrimeGeneralMovingFarNonlinearStrictExponent
import RBM1D.Gauss.APrimeGeneralMovingQuadraticStrictExponent
import RBM1D.Gauss.APrimeGeneralMovingDriftNearTailSlot

/-! # T1251: strict exponent for the exact full T615 drift profile

This module combines the five literal summands in the T1055/T615 full
deterministic profile under the T995 loss schedule. It is an estimate for
that formalized profile, not a replacement for the paper's stopped-process
claim or a paper-level closure result. -/

namespace RBM.APrimeGeneralMovingFullDriftStrictExponent

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open APrimeGeneralMovingFarLinearStrictExponent

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem continuousOn_nearMain {E : Real} {s : Nat → Real} {N : Nat}
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaSrc zetaCtr : Real) :
    ContinuousOn (fun u => APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
      E s zetaSrc zetaCtr N v u) (Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hsEll : 0 < B.ell N (s N) :=
    zero_lt_one.trans_le (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1)
  have hratio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u ∈ Icc (s N) v, 1 - u ≠ 0 := by
      intro u hu
      linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRpos : ∀ u, u ∈ Icc (s N) v → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRpow : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) (Icc (s N) v) :=
    hR.rpow_const (fun u hu => Or.inl (ne_of_gt (hRpos u hu)))
  have hc : ContinuousOn (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    have hEllpos : ∀ u, u ∈ Icc (s N) v → B.ell N u ≠ 0 := by
      intro u hu
      exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
        (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1)))
    have hinv : ContinuousOn (fun u => (B.ell N u)⁻¹) (Icc (s N) v) :=
      hEll.inv₀ hEllpos
    have hpoly : ContinuousOn (fun u =>
        2 * Real.log (d.W N : Real) ^ (3 : Real) + 2 * (B.ell N u)⁻¹)
        (Icc (s N) v) := by fun_prop
    have hexp : ContinuousOn (fun _ : Real =>
        Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)))
        (Icc (s N) v) := continuousOn_const
    have hEq : (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u)) =
        (fun u => (2 * Real.log (d.W N : Real) ^ (3 : Real) +
          2 * (B.ell N u)⁻¹) * Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real))) := by
      funext u
      simp [Lemma57.cNear, div_eq_mul_inv]
    exact hEq ▸ hpoly.mul hexp
  unfold APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Icc (s N) v) :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hratio3 : ContinuousOn (fun u => (B.ell N u / B.ell N (s N)) ^ 3)
      (Icc (s N) v) := hratio.pow 3
  have hinner : ContinuousOn (fun u =>
      4 * (N : Real) ^ (zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
        (B.ell N u / B.ell N (s N)) ^ 3 * Lemma57.cNear (d.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    have hscalar : ContinuousOn (fun _ : Real =>
        4 * (N : Real) ^ (zetaCtr + zetaSrc)) (Icc (s N) v) := continuousOn_const
    have hprod := (hscalar.mul hEtaInv).mul (hratio3.mul hc)
    convert hprod using 1
    ext u
    simp only [Pi.mul_apply]
    ring
  exact ((continuousOn_const.mul hRpow).mul continuousOn_const).mul hinner

private theorem continuousOn_nearTail {E D : Real} {s : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2)
    (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (ζ τ κ : Real) :
    ContinuousOn (fun u => APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail
      E D s ζ τ κ N v u) (Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hEll0 : ∀ u ∈ Icc (s N) v, B.ell N u ≠ 0 := by
    intro u hu
    have h := one_le_ellHat_of_nonneg (B.one_le_L N)
      (hs0.trans hu.1) (hu.2.trans_lt hv1)
    have hh : 1 ≤ B.ell N u := by simpa only [Band.ell] using h
    exact ne_of_gt (by linarith)
  have hsEll : B.ell N (s N) ≠ 0 := by
    have h := one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1
    have hh : 1 ≤ B.ell N (s N) := by simpa only [Band.ell] using h
    exact ne_of_gt (by linarith)
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEta0 : ∀ u ∈ Icc (s N) v, etaT E u ≠ 0 := by
    intro u hu
    exact (Step2.etaT_pos' hE (hu.2.trans_lt hv1)).ne'
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hden (by
      intro u hu
      linarith [hu.2])
  have hRpos : ∀ u ∈ Icc (s N) v, Step2Moment.ratR E s N u ≠ 0 := by
    intro u hu
    exact (Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)).ne'
  have hGap : ContinuousOn
      (fun u => APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    unfold APrimeDriftNearAbsorb.gap Lemma57.ellStarStar ellStar
    fun_prop
  have hTail : ContinuousOn
      (fun u => tailT (d.W N : Real) (B.ell N u) (etaT E u) D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)))
      (Icc (s N) v) := by
    have hA : ContinuousOn
        (fun u => ((d.W N : Real) * B.ell N u * etaT E u) ^ 2)
        (Icc (s N) v) := by fun_prop
    have hA0 : ∀ u ∈ Icc (s N) v,
        ((d.W N : Real) * B.ell N u * etaT E u) ^ 2 ≠ 0 := by
      intro u hu
      have hW : 0 < (d.W N : Real) := by exact_mod_cast B.W_pos N
      have he : 0 < B.ell N u := by
        have hh := one_le_ellHat_of_nonneg (B.one_le_L N)
          (hs0.trans hu.1) (hu.2.trans_lt hv1)
        have hhh : 1 ≤ B.ell N u := by simpa only [Band.ell] using hh
        linarith
      have ht : 0 < etaT E u := Step2.etaT_pos' hE (hu.2.trans_lt hv1)
      positivity
    have hInv := hA.inv₀ hA0
    have hDiv := hGap.div hEll hEll0
    have hExp := Real.continuous_exp.comp_continuousOn hDiv.sqrt.neg
    change ContinuousOn
      (fun u => Real.exp (-Real.sqrt
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u) / B.ell N u)))
      (Icc (s N) v) at hExp
    change ContinuousOn
      (fun u => (((d.W N : Real) * B.ell N u * etaT E u) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt
          (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u) / B.ell N u)) +
          (d.W N : Real) ^ (-D)) (Icc (s N) v)
    exact (hInv.mul hExp).add continuousOn_const
  have hRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  have hRpow : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) (Icc (s N) v) :=
    hR.rpow_const (fun u hu => Or.inl (hRpos u hu))
  let F : Real → Real := fun u =>
    4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (Step2Moment.ratR E s N u) ^ (-2 : Real) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) *
      ((N : Real) ^ ζ * (d.L N : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s τ κ N u *
        (d.W N : Real) ^ 2 * B.ell N u *
        (B.ell N u / B.ell N (s N)) *
        Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)) *
        tailT (d.W N : Real) (B.ell N u) (etaT E u) D
          (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)))
  have hF : ContinuousOn F (Icc (s N) v) := by
    dsimp [F, APrimeGeneralMovingDriftSource.blockCap]
    fun_prop
  apply hF.congr
  intro u hu
  have hellne := hEll0 u hu
  have he := hEta0 u hu
  have hrune : B.ell N u / B.ell N (s N) ≠ 0 := div_ne_zero hellne hsEll
  dsimp [F, APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail]
  field_simp [hellne, hsEll, he, hrune]

private theorem intervalIntegrable_nearMain {E : Real} {s : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (zetaSrc zetaCtr : Real) :
    IntervalIntegrable
      (fun u => APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
        E s zetaSrc zetaCtr N v u) volume (s N) v :=
  (continuousOn_nearMain hE hs0 hsv hv1 zetaSrc zetaCtr).intervalIntegrable_of_Icc hsv

private theorem intervalIntegrable_nearTail {E D : Real} {s : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (ζ τ κ : Real) :
    IntervalIntegrable
      (fun u => APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail
        E D s ζ τ κ N v u) volume (s N) v :=
  (continuousOn_nearTail hE hs0 hsv hv1 ζ τ κ).intervalIntegrable_of_Icc hsv

/-- Expanding T1055's exact full-profile identity and T1017's near-source
split yields the literal five-row integrand used by the strict component bounds. -/
theorem profile_eq_five_components
    (E D : Real) (s t : Nat → Real) (δ : Real) (N : Nat) (v u : Real) :
    APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
      (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u =
      APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain E s
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) N v u +
      APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail E D s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u +
      APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u +
      APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear E D s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u +
      APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic E D s
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u := by
  rw [APrimeGeneralMovingFullDriftProfileSlotRepair.profile_eq_four_components]
  rw [APrimeGeneralMovingDriftNearCombinedSlot.normalized_near_source_split]

/-- At the T995 schedule, the exact T615 full deterministic drift profile has
an all-active-cell `δ/8` integral bound. The endpoint factor is retained and
the quantifier includes the zero-length cell `k = 0`. -/
theorem eventually_full_profile_integral_le_delta_eighth
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        (12 / (mE E).im + 1) * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
  have hmain :=
    APrimeGeneralMovingNearMainStrictExponent.eventually_near_main_integral_le_delta_eighth
      hE hD hs0 hst ht1 hc hδ hδsmall
  have htail :=
    APrimeGeneralMovingDriftNearTailSlot.eventually_near_tail_integral_le_strict_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hfar :=
    eventually_far_linear_integral_le_strict_exponent_endpoint
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hnonlin :=
    APrimeGeneralMovingFarNonlinearStrictExponent.eventually_far_nonlinear_integral_le_delta_eighth
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hquad :=
    APrimeGeneralMovingQuadraticStrictExponent.eventually_quadratic_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  filter_upwards [hmain, htail.2, hfar, hnonlin, hquad] with
    N hmainN htailN hfarN hnonlinN hquadN
  intro k hk
  dsimp only
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  let fmain : Real → Real := fun u =>
    APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain E s
      (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) N v u
  let ftail : Real → Real := fun u =>
    APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail E D s
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  let ffar : Real → Real := fun u =>
    APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  let fnonlin : Real → Real := fun u =>
    APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear E D s
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  let fquad : Real → Real := fun u =>
    APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic E D s
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  have hmainInt : IntervalIntegrable fmain volume (s N) v := by
    dsimp [fmain]
    exact intervalIntegrable_nearMain hE (hs0 N) hv.1 hv1
      (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
  have htailInt : IntervalIntegrable ftail volume (s N) v := by
    dsimp [ftail]
    exact intervalIntegrable_nearTail hE (hs0 N) hv.1 hv1
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
  have hfarInt : IntervalIntegrable ffar volume (s N) v :=
    APrimeGeneralMovingFullDriftProfileSlotRepair.intervalIntegrable_normalizedFarLinear
      (D := D) hE (hs0 N) hv.1 hv1 δ
  have hnonlinInt : IntervalIntegrable fnonlin volume (s N) v :=
    APrimeGeneralMovingDriftFarNonlinearSlot.intervalIntegrable_normalizedFarNonlinear
      (D := D) hE (hs0 N) hv.1 hv1
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
  have hquadInt : IntervalIntegrable fquad volume (s N) v :=
    APrimeGeneralMovingDriftQuadraticSlotRepair.intervalIntegrable_normalizedQuadratic
      (D := D) hE (hs0 N) hv.1 hv1
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
  have hprofileSplit :
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) =
      (fun u => ((((fmain u + ftail u) + ffar u) + fnonlin u) + fquad u)) := by
    funext u
    simpa only [fmain, ftail, ffar, fnonlin, fquad] using
      profile_eq_five_components E D s t δ N v u
  have hprofileIntEq :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) =
      (((((∫ u in (s N)..v, fmain u) + (∫ u in (s N)..v, ftail u)) +
        (∫ u in (s N)..v, ffar u)) + (∫ u in (s N)..v, fnonlin u)) +
        (∫ u in (s N)..v, fquad u)) := by
    rw [hprofileSplit,
      intervalIntegral.integral_add
        (((hmainInt.add htailInt).add hfarInt).add hnonlinInt) hquadInt,
      intervalIntegral.integral_add ((hmainInt.add htailInt).add hfarInt) hnonlinInt,
      intervalIntegral.integral_add (hmainInt.add htailInt) hfarInt,
      intervalIntegral.integral_add hmainInt htailInt]
  have hmainCell := hmainN k hk
  have hmainBound : (∫ u in (s N)..v, fmain u) ≤
      (8 / (mE E).im) * (N : Real) ^ (δ / 8) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [fmain, APrimeGeneralMovingNearMainStrictExponent.normalizedNearMain_eq_T1001]
      using hmainCell
  have htailBound := htailN k hk
  have hfarBound := hfarN k hk
  have hnonlinBound := hnonlinN k hk
  have hquadBound := hquadN k hk
  have htailBound' : (∫ u in (s N)..v, ftail u) ≤
      (N : Real) ^ (δ / 8) * Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [ftail] using htailBound
  have hfarBound' : (∫ u in (s N)..v, ffar u) ≤
      (1 / (mE E).im) * (N : Real) ^ (δ / 8) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [ffar] using hfarBound
  have hnonlinBound' : (∫ u in (s N)..v, fnonlin u) ≤
      (2 / (mE E).im) * (N : Real) ^ (δ / 8) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [fnonlin, APrimeGeneralMovingFarNonlinearStrictExponent.farNonlinearConstant]
      using hnonlinBound
  have hquadBound' : (∫ u in (s N)..v, fquad u) ≤
      (1 / (mE E).im) * (N : Real) ^ (δ / 8) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [fquad, APrimeGeneralMovingQuadraticStrictExponent.normalizedQuadratic,
      APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic]
      using hquadBound
  have hsum := add_le_add (add_le_add (add_le_add hmainBound htailBound') hfarBound')
    (add_le_add hnonlinBound' hquadBound')
  calc
    _ = (((((∫ u in (s N)..v, fmain u) + (∫ u in (s N)..v, ftail u)) +
        (∫ u in (s N)..v, ffar u)) + (∫ u in (s N)..v, fnonlin u)) +
        (∫ u in (s N)..v, fquad u)) := hprofileIntEq
    _ = (((∫ u in (s N)..v, fmain u) + (∫ u in (s N)..v, ftail u)) +
        (∫ u in (s N)..v, ffar u)) +
        ((∫ u in (s N)..v, fnonlin u) + (∫ u in (s N)..v, fquad u)) := by ring
    _ ≤ 8 / (mE E).im * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N v ^ (-2 : Real) +
        (N : Real) ^ (δ / 8) * Step2Moment.ratR E s N v ^ (-2 : Real) +
        1 / (mE E).im * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N v ^ (-2 : Real) +
        (2 / (mE E).im * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N v ^ (-2 : Real) +
         1 / (mE E).im * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N v ^ (-2 : Real)) := hsum
    _ = ((8 / (mE E).im + 1 + 1 / (mE E).im) *
          (N : Real) ^ (δ / 8) * Step2Moment.ratR E s N v ^ (-2 : Real) +
          (2 / (mE E).im + 1 / (mE E).im) *
          (N : Real) ^ (δ / 8) * Step2Moment.ratR E s N v ^ (-2 : Real)) := by ring
    _ = (12 / (mE E).im + 1) * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by ring

/-- The exact T995 same-event positive-cell witness, including positive actual
smooth weight on an active cell. It supplies a nondegenerate realization of
the hypotheses used for the full-profile estimate. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms profile_eq_five_components
#print axioms eventually_full_profile_integral_le_delta_eighth
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingFullDriftStrictExponent
