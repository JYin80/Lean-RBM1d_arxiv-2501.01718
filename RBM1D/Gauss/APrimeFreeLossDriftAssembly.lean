/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossNear
import RBM1D.Gauss.APrimeFreeLossFarLinear
import RBM1D.Gauss.APrimeFreeLossFarNonlinear
import RBM1D.Gauss.APrimeFreeLossQuadratic
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget

/-!
# T1313: corrected-loss assembly of the literal T615 drift profile

The source rows are imported only from the independently accepted T1293,
T1295, T1297, and T1299 modules. The final consumer is T615's exact
actual-smooth drift integral producer.
-/

namespace RBM.APrimeFreeLossDriftAssembly

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
  APrimeGeneralMovingSmoothDriftNormBudget

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def sourceLoss (lambda : Real) : Real := lambda / 1000

noncomputable def profileConstant (E : Real) : Real :=
  8 / (mE E).im + 8 +
    2 * APrimeFreeLossFarLinear.farLinearConstant / (mE E).im +
    2 / (mE E).im + 1 / (21 * (mE E).im)

noncomputable def assemblyConstant (E : Real) : Real := profileConstant E + 1

private theorem intervalIntegrable_nearMain
    {E : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaSrc zetaCtr : Real) :
    IntervalIntegrable
      (fun u => APrimeFreeLossNear.normalizedNearMain
        E s zetaSrc zetaCtr N v u) volume (s N) v := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u
        unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
        rw [Step2.etaT_ratio hE]]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hden (by
      intro u hu
      linarith [hu.2])
  have hRpos : ∀ u, u ∈ Icc (s N) v →
      0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRpow : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) (Icc (s N) v) :=
    hR.rpow_const (fun u hu => Or.inl (ne_of_gt (hRpos u hu)))
  have hEtaPos : ∀ u, u ∈ Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Icc (s N) v) :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hEllPos : ∀ u, u ∈ Icc (s N) v → B.ell N u ≠ 0 := by
    intro u hu
    exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
      (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1)))
  have hEllInv : ContinuousOn (fun u => (B.ell N u)⁻¹) (Icc (s N) v) :=
    hEll.inv₀ hEllPos
  have hRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  have hCnear : ContinuousOn (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    have hpoly : ContinuousOn (fun u =>
        2 * Real.log (d.W N : Real) ^ (3 : Real) + 2 * (B.ell N u)⁻¹)
        (Icc (s N) v) := by fun_prop
    have hexp : ContinuousOn (fun _ : Real =>
        Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)))
        (Icc (s N) v) := continuousOn_const
    have hEq : (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u)) =
        (fun u => (2 * Real.log (d.W N : Real) ^ (3 : Real) +
          2 * (B.ell N u)⁻¹) *
          Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real))) := by
      funext u
      simp [Lemma57.cNear, div_eq_mul_inv]
    exact hEq ▸ hpoly.mul hexp
  have hCont : ContinuousOn
      (fun u => APrimeFreeLossNear.normalizedNearMain
        E s zetaSrc zetaCtr N v u) (Icc (s N) v) := by
    unfold APrimeFreeLossNear.normalizedNearMain
      APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
    have hratio3 : ContinuousOn (fun u => (B.ell N u / B.ell N (s N)) ^ 3)
        (Icc (s N) v) := hRatio.pow 3
    have hinner : ContinuousOn (fun u =>
        4 * (N : Real) ^ (zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
          (B.ell N u / B.ell N (s N)) ^ 3 *
          Lemma57.cNear (d.W N : Real) (B.ell N u)) (Icc (s N) v) := by
      have hscalar : ContinuousOn (fun _ : Real =>
          4 * (N : Real) ^ (zetaCtr + zetaSrc)) (Icc (s N) v) := continuousOn_const
      have hprod := (hscalar.mul hEtaInv).mul (hratio3.mul hCnear)
      convert hprod using 1
      ext u
      simp only [Pi.mul_apply]
      ring
    exact ((continuousOn_const.mul hRpow).mul continuousOn_const).mul hinner
  exact hCont.intervalIntegrable_of_Icc hsv

private theorem intervalIntegrable_nearTail
    {E D : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaCtr tauG deltaCap : Real) :
    IntervalIntegrable
      (fun u => APrimeFreeLossNear.normalizedNearTail
        E D s zetaCtr tauG deltaCap N v u) volume (s N) v := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  let I := Icc (s N) v
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hEll0 : ∀ u ∈ I, B.ell N u ≠ 0 := by
    intro u hu
    have h := one_le_ellHat_of_nonneg (B.one_le_L N)
      (hs0.trans hu.1) (hu.2.trans_lt hv1)
    have hh : 1 ≤ B.ell N u := by simpa only [Band.ell] using h
    exact ne_of_gt (by linarith)
  have hsEll : B.ell N (s N) ≠ 0 := by
    have h := one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1
    have hh : 1 ≤ B.ell N (s N) := by simpa only [Band.ell] using h
    exact ne_of_gt (by linarith)
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEta0 : ∀ u ∈ I, etaT E u ≠ 0 := by
    intro u hu
    exact (Step2.etaT_pos' hE (hu.2.trans_lt hv1)).ne'
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u
        unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
        rw [Step2.etaT_ratio hE]]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) I :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hden (by
      intro u hu
      dsimp [I] at hu
      linarith [hu.2])
  have hRpos : ∀ u ∈ I, Step2Moment.ratR E s N u ≠ 0 := by
    intro u hu
    exact (Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)).ne'
  have hRpow : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) I :=
    hR.rpow_const (fun u hu => Or.inl (hRpos u hu))
  have hGap : ContinuousOn
      (fun u => APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)) I := by
    unfold APrimeDriftNearAbsorb.gap Lemma57.ellStarStar ellStar
    fun_prop
  have hTail : ContinuousOn
      (fun u => tailT (d.W N : Real) (B.ell N u) (etaT E u) D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) I := by
    have hA : ContinuousOn
        (fun u => ((d.W N : Real) * B.ell N u * etaT E u) ^ 2) I := by fun_prop
    have hA0 : ∀ u ∈ I, ((d.W N : Real) * B.ell N u * etaT E u) ^ 2 ≠ 0 := by
      intro u hu
      have hW : 0 < (d.W N : Real) := by exact_mod_cast B.W_pos N
      have hEllPos : 0 < B.ell N u := by
        have hh := one_le_ellHat_of_nonneg (B.one_le_L N)
          (hs0.trans hu.1) (hu.2.trans_lt hv1)
        have hhh : 1 ≤ B.ell N u := by simpa only [Band.ell] using hh
        linarith
      have hEtaPos : 0 < etaT E u := Step2.etaT_pos' hE (hu.2.trans_lt hv1)
      positivity
    have hInv := hA.inv₀ hA0
    have hDiv := hGap.div hEll hEll0
    have hExp := Real.continuous_exp.comp_continuousOn hDiv.sqrt.neg
    change ContinuousOn
      (fun u => Real.exp (-Real.sqrt
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u) / B.ell N u))) I at hExp
    change ContinuousOn
      (fun u => (((d.W N : Real) * B.ell N u * etaT E u) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt
          (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u) / B.ell N u)) +
          (d.W N : Real) ^ (-D)) I
    exact (hInv.mul hExp).add continuousOn_const
  have hRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N)) I :=
    hEll.div_const _
  have hRinv : ContinuousOn
      (fun u => Step2Moment.ratR E s N u ^ (-2 : Real)) I :=
    hR.rpow_const (fun u hu => Or.inl (hRpos u hu))
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ hEta0
  let F : Real → Real := fun u =>
    4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (Step2Moment.ratR E s N u) ^ (-2 : Real) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) *
      ((N : Real) ^ zetaCtr * (d.L N : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s tauG deltaCap N u *
        (d.W N : Real) ^ 2 * B.ell N u *
        (B.ell N u / B.ell N (s N)) *
        Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)) *
        tailT (d.W N : Real) (B.ell N u) (etaT E u) D
          (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)))
  have hF : ContinuousOn F I := by
    dsimp [F, APrimeGeneralMovingDriftSource.blockCap]
    have hR4 : ContinuousOn
        (fun u => (Step2Moment.ratR E s N u) ^ (4 : Nat)) I := hR.pow 4
    fun_prop
  have hCont : ContinuousOn
      (fun u => APrimeFreeLossNear.normalizedNearTail
        E D s zetaCtr tauG deltaCap N v u) I := by
    apply hF.congr
    intro u hu
    have hellne := hEll0 u hu
    have he := hEta0 u hu
    have hrune : B.ell N u / B.ell N (s N) ≠ 0 := div_ne_zero hellne hsEll
    dsimp [F, APrimeFreeLossNear.normalizedNearTail,
      APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail]
    field_simp [hellne, hsEll, he, hrune]
  exact hCont.intervalIntegrable_of_Icc hsv

private theorem intervalIntegrable_farLinear
    {E D : Real} {s t : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaCtr tauG deltaCap : Real) :
    IntervalIntegrable
      (fun u => APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear
        E D s t zetaCtr tauG deltaCap N v u) volume (s N) v := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  let I : Set Real := Icc (s N) v
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u
        unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
        rw [Step2.etaT_ratio hE]]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) I :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hden (by
      intro u hu
      dsimp [I] at hu
      linarith [hu.2])
  have hRpos : ∀ u, u ∈ I → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRinv : ContinuousOn
      (fun u => Step2Moment.ratR E s N u ^ (-2 : Real)) I :=
    hR.rpow_const (fun u hu => Or.inl (ne_of_gt (hRpos u hu)))
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ (by
      intro u hu
      exact (Step2.etaT_pos' hE (hu.2.trans_lt hv1)).ne')
  have hEllInv : ContinuousOn (fun u => (B.ell N u)⁻¹) I :=
    hEll.inv₀ (by
      intro u hu
      exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
        (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1))))
  have hcap : ContinuousOn
      (fun u => APrimeGeneralMovingDriftSource.blockCap E s tauG deltaCap N u) I := by
    unfold APrimeGeneralMovingDriftSource.blockCap Step2Moment.ratR
    have hR4 : ContinuousOn (fun u => Step2Moment.ratR E s N u ^ (4 : Nat)) I :=
      hR.pow 4
    fun_prop
  have hratio : ContinuousOn (fun u => B.ell N u / B.ell N (s N)) I :=
    hEll.div_const _
  have hCf : ContinuousOn (fun u => Lemma57.cFar (d.W N : Real) (B.ell N u)) I := by
    unfold Lemma57.cFar
    have hpoly : ContinuousOn (fun u =>
        4 * Real.log (d.W N : Real) ^ (3 / 2 : Real) + 8 * (B.ell N u)⁻¹) I := by
      fun_prop
    exact hpoly.mul continuousOn_const
  have hCont : ContinuousOn
      (fun u => APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear
        E D s t zetaCtr tauG deltaCap N v u) I := by
    unfold APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear
    fun_prop
  exact hCont.intervalIntegrable_of_Icc hsv

private theorem intervalIntegrable_quadratic
    {E D : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (capLoss : Real) :
    IntervalIntegrable
      (fun u => APrimeFreeLossQuadratic.normalizedQuadratic
        E D s capLoss N v u) volume (s N) v := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  let I : Set Real := Icc (s N) v
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u
        unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
        rw [Step2.etaT_ratio hE]]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) I :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hden (by
      intro u hu
      dsimp [I] at hu
      linarith [hu.2])
  have hRatPos : ∀ u, u ∈ I → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRatInv : ContinuousOn
      (fun u => Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (ne_of_gt (hRatPos u hu)))
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    rw [show (fun u => etaT E u) =
      (fun u => (mE E).im * (1 - u)) by
        funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ I → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hScaleInv : ContinuousOn (fun u =>
      ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) I := by
    apply ContinuousOn.inv₀ ((continuousOn_const.mul hEll).mul hEta)
    intro u hu
    have hW : (0 : Real) < d.W N := by exact_mod_cast B.W_pos N
    exact (mul_pos (mul_pos hW
      (zero_lt_one.trans_le (one_le_ellHat_of_nonneg (B.one_le_L N)
        (hs0.trans hu.1) (hu.2.trans_lt hv1)))) (hEtaPos u hu)).ne'
  have hJSCap : ContinuousOn
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.jSCap
        E s capLoss N u) I := by
    unfold APrimeGeneralMovingSmoothDriftNormBudget.jSCap
    exact continuousOn_const.mul (hRat.pow 4)
  have hQuad : ContinuousOn
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.quadCap
        E D s capLoss N u) I := by
    unfold APrimeGeneralMovingSmoothDriftNormBudget.quadCap
    have hfirst : ContinuousOn (fun u =>
        36 * ((etaT E u)⁻¹ *
          (((d.W N : Real) * B.ell N u * etaT E u)⁻¹))) I :=
      continuousOn_const.mul (hEtaInv.mul hScaleInv)
    have hsecond : ContinuousOn (fun _u : Real =>
        (d.W N : Real) * (d.L N : Real) * (d.W N : Real) ^ (-D)) I :=
      continuousOn_const
    exact (continuousOn_const.mul (hJSCap.pow 2)).mul (hfirst.add hsecond)
  have hNorm : ContinuousOn
      (fun u => APrimeFreeLossQuadratic.normalizedQuadratic
        E D s capLoss N v u) I := by
    unfold APrimeFreeLossQuadratic.normalizedQuadratic
    fun_prop
  exact hNorm.intervalIntegrable_of_Icc hsv

/-- The actual T615 profile is the sum of precisely the five audited rows.
The near split and the nonlinear split are the producer-level identities;
the quadratic summand is the literal capped (5.34) term. -/
theorem literal_profile_eq_five_rows
    (E D : Real) (s t : Nat → Real) (lambda : Real) (N : Nat)
    (v u : Real) :
    APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
        (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
        (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N v u =
      APrimeFreeLossNear.normalizedNearMain E s
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.hLoss lambda) N v u +
      APrimeFreeLossNear.normalizedNearTail E D s
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.capLoss lambda) N v u +
      APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
          (APrimeFreeLossFarLinear.sourceLoss lambda)
          (APrimeFreeLossFarLinear.sourceLoss lambda)
          (APrimeFreeLossFarLinear.deltaCap lambda) N v u +
      APrimeFreeLossFarNonlinear.normalizedFarNonlinear E D s
          (APrimeFreeLossFarNonlinear.sourceLoss lambda)
          (APrimeFreeLossFarNonlinear.sourceLoss lambda)
          (APrimeFreeLossFarNonlinear.capLoss lambda) N v u +
      APrimeFreeLossQuadratic.normalizedQuadratic E D s
          (APrimeFreeLossQuadratic.deltaCap lambda) N v u := by
  let pref := Step2.xiK (d.L N) (d.W N) (mE E).im *
      Step2Moment.ratR E s N u ^ (-2 : Real) *
      Step2Moment.ratR E s N v ^ (-2 : Real)
  have hcap : APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda =
      2 * lambda := by
    simp [APrimeGeneralMovingSmoothDriftNormBudget.deltaCap]
    ring
  have hnear : pref * APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
      E D s (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
      (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N u =
      APrimeFreeLossNear.normalizedNearMain E s
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.hLoss lambda) N v u +
        APrimeFreeLossNear.normalizedNearTail E D s
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.capLoss lambda) N v u := by
    rw [hcap]
    simpa [pref, sourceLoss, APrimeFreeLossNear.hLoss,
      APrimeFreeLossNear.capLoss] using
      APrimeFreeLossNear.literal_near_source_split E D s
        (APrimeFreeLossNear.hLoss lambda)
        (APrimeFreeLossNear.hLoss lambda)
        (APrimeFreeLossNear.hLoss lambda)
        (APrimeFreeLossNear.capLoss lambda) N v u
  have hfar : pref * APrimeGeneralMovingDriftAtProfile.farSourceCoeff
      E D s t (sourceLoss lambda) (sourceLoss lambda)
      (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N u =
      APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
          (APrimeFreeLossFarLinear.sourceLoss lambda)
          (APrimeFreeLossFarLinear.sourceLoss lambda)
          (APrimeFreeLossFarLinear.deltaCap lambda) N v u +
        APrimeFreeLossFarNonlinear.normalizedFarNonlinear E D s
          (APrimeFreeLossFarNonlinear.sourceLoss lambda)
          (APrimeFreeLossFarNonlinear.sourceLoss lambda)
          (APrimeFreeLossFarNonlinear.capLoss lambda) N v u := by
    rw [hcap]
    rw [APrimeFreeLossFarNonlinear.exact_T615_nonlinear_identity
      E D s t (APrimeFreeLossFarNonlinear.sourceLoss lambda)
      (APrimeFreeLossFarNonlinear.sourceLoss lambda)
      (APrimeFreeLossFarNonlinear.capLoss lambda) N v u]
    simp only [pref, sourceLoss,
      APrimeFreeLossFarLinear.sourceLoss, APrimeFreeLossFarLinear.deltaCap,
      APrimeFreeLossFarNonlinear.sourceLoss, APrimeFreeLossFarNonlinear.capLoss,
      APrimeGeneralMovingDriftAtProfile.farSourceCoeff,
      APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear]
    dsimp
    simp only [Band.ell, band_L, Dims.exampleGrow_L]
    ring_nf
  change pref * (APrimeGeneralMovingDriftAtProfile.nearSourceCoeff
        E D s (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
        (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N u +
      APrimeGeneralMovingDriftAtProfile.farSourceCoeff
        E D s t (sourceLoss lambda) (sourceLoss lambda)
        (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N u +
      APrimeGeneralMovingSmoothDriftNormBudget.quadCap E D s
        (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N u) = _
  have hquad : pref * APrimeGeneralMovingSmoothDriftNormBudget.quadCap
      E D s (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N u =
      APrimeFreeLossQuadratic.normalizedQuadratic E D s
        (APrimeFreeLossQuadratic.deltaCap lambda) N v u := by
    unfold APrimeFreeLossQuadratic.normalizedQuadratic
      APrimeGeneralMovingSmoothDriftNormBudget.quadCap
      APrimeGeneralMovingSmoothDriftNormBudget.jSCap
    dsimp [pref, APrimeGeneralMovingSmoothDriftNormBudget.deltaCap,
      APrimeFreeLossQuadratic.deltaCap]
    simp only [Band.ell, band_L, Dims.exampleGrow_L]
    ring_nf
  rw [mul_add, mul_add, hnear, hfar, hquad]
  ring

/-- For every fixed order `p ≥ 1`, all five literal rows of T615's profile
integrate on every active cell (including `k = 0`) to the corrected
`N^(4h) R_v^(-2)` budget. The actual weighted drift integral has the same
power after payment of the `beta = 1` complement by the endpoint margin. -/
theorem eventually_full_profile_and_actual_drift_integrals_le
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        (∫ u in (s N)..
            APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k,
          APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
            (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
            (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
            N (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k) u)
          ≤ profileConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
              (Step2Moment.ratR E s N
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k)) ^
                (-2 : Real) ∧
        (∫ u in (s N)..
            APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u)
          ≤ assemblyConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
              (Step2Moment.ratR E s N
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k)) ^
                (-2 : Real) := by
  have hNear := APrimeFreeLossNear.eventually_corrected_near_rows_integral
    hE hD hs0 hst ht1 hc hreg (lam := lambda) hlambda hsmall
  have hFarLinear :=
    APrimeFreeLossFarLinear.eventually_far_linear_integral_le_endpoint_margins
      hE hD hs0 hst ht1 hc hreg lambda hlambda hsmall
  have hFarNonlinear :=
    APrimeFreeLossFarNonlinear.eventually_far_nonlinear_integral_le_negative
      hE hD hs0 hst ht1 hc hreg hlambda hsmall
  have hQuadratic := APrimeFreeLossQuadratic.eventually_t615_quadratic_integral_le
    hE hD hs0 hst ht1 hc hreg hB hlambda hsmall
  have hConsumer :=
    eventually_actual_smooth_drift_integral_le_exact_profile
      hE hD hs0 hst ht1 hc hreg hB
      (zetaSrc := sourceLoss lambda)
      (zetaCtr := sourceLoss lambda)
      (tauG := sourceLoss lambda)
      (deltaWeight := lambda) (xi := lambda)
      (by dsimp [sourceLoss]; positivity)
      (by dsimp [sourceLoss]; positivity)
      (by dsimp [sourceLoss]; positivity)
      hlambda hlambda p hp 1 (by norm_num)
  have hMargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hNear, hFarLinear, hFarNonlinear, hQuadratic, hConsumer,
      hMargin, B.dim, eventually_ge_atTop 1]
    with N hNearN hFarLinearN hFarNonlinearN hQuadraticN hConsumerN
      hMarginN hdimN hN
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have him : 0 < (mE E).im := mE_im_pos hE
  have hRoom :=
    APrimeFreeLossFarLinear.corrected_integral_exponent_room hc hlambda hsmall
  have hRoomC : 4 * lambda + 4 * sourceLoss lambda < c / 12 := by
    simpa [sourceLoss, APrimeFreeLossFarLinear.sourceLoss] using hRoom.1
  have hRoomW : 4 * lambda + 4 * sourceLoss lambda < 13 / 24 := by
    simpa [sourceLoss, APrimeFreeLossFarLinear.sourceLoss] using hRoom.2
  have hLossPos : 0 < sourceLoss lambda := by
    dsimp [sourceLoss]
    positivity
  have hFarLinearPowerC :
      (N : Real) ^ (4 * lambda + 4 * sourceLoss lambda) *
          (N : Real) ^ (-(c / 12)) ≤
        (N : Real) ^ (4 * sourceLoss lambda) := by
    rw [← Real.rpow_add hNpos]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    linarith [hRoomC]
  have hFarLinearPowerW :
      (N : Real) ^ (4 * lambda + 4 * sourceLoss lambda) *
          (N : Real) ^ (-(13 / 24 : Real)) ≤
        (N : Real) ^ (4 * sourceLoss lambda) := by
    rw [← Real.rpow_add hNpos]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    linarith [hRoomW]
  have hFarLinearPower :
      (N : Real) ^ (4 * lambda + 4 * sourceLoss lambda) *
          ((N : Real) ^ (-(c / 12)) + (N : Real) ^ (-(13 / 24 : Real))) ≤
        2 * (N : Real) ^ (4 * sourceLoss lambda) := by
    calc
      _ = (N : Real) ^ (4 * lambda + 4 * sourceLoss lambda) *
            (N : Real) ^ (-(c / 12)) +
          (N : Real) ^ (4 * lambda + 4 * sourceLoss lambda) *
            (N : Real) ^ (-(13 / 24 : Real)) := by ring
      _ ≤ _ := add_le_add hFarLinearPowerC hFarLinearPowerW
      _ = _ := by ring
  intro k hk a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvIcc : v ∈ Icc (s N) (t N) := by
    simpa only [v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hvIcc.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hRinv : 0 ≤ Step2Moment.ratR E s N v ^ (-2 : Real) := by positivity
  have hQone : 1 ≤ (N : Real) ^ (4 * sourceLoss lambda) :=
    Real.one_le_rpow hN1 (by positivity)
  have hTailPow : (N : Real) ^ (-(21 : Real)) ≤
      (N : Real) ^ (4 * sourceLoss lambda) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hLossPos])
  have hDecayPow : (N : Real) ^ (-(c / 20)) ≤
      (N : Real) ^ (4 * sourceLoss lambda) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hc, hLossPos])
  have hNearRows := hNearN k hk a
  have hMainBound := hNearRows.1
  have hTailBound := hNearRows.2
  have hLinearBound := hFarLinearN k hk
  have hNonlinearBound := hFarNonlinearN k hk
  have hQuadraticBound := hQuadraticN k hk
  have hLinearWeak :
      (∫ u in (s N)..v,
        APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
          (APrimeFreeLossFarLinear.sourceLoss lambda)
          (APrimeFreeLossFarLinear.sourceLoss lambda)
          (APrimeFreeLossFarLinear.deltaCap lambda) N v u) ≤
        (2 * APrimeFreeLossFarLinear.farLinearConstant / (mE E).im) *
          (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hLinearRaw :
        (∫ u in (s N)..v,
          APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
            (APrimeFreeLossFarLinear.sourceLoss lambda)
            (APrimeFreeLossFarLinear.sourceLoss lambda)
            (APrimeFreeLossFarLinear.deltaCap lambda) N v u) ≤
          (APrimeFreeLossFarLinear.farLinearConstant / (mE E).im) *
            (N : Real) ^ (4 * lambda +
              4 * APrimeFreeLossFarLinear.sourceLoss lambda) *
            ((N : Real) ^ (-(c / 12)) +
              (N : Real) ^ (-(13 / 24 : Real))) *
            Step2Moment.ratR E s N v ^ (-2 : Real) := by
      simpa only [v] using hLinearBound
    have hconst : 0 ≤ APrimeFreeLossFarLinear.farLinearConstant := by
      unfold APrimeFreeLossFarLinear.farLinearConstant
      positivity
    have hcoef : 0 ≤ APrimeFreeLossFarLinear.farLinearConstant / (mE E).im :=
      div_nonneg hconst him.le
    calc
      _ ≤ (APrimeFreeLossFarLinear.farLinearConstant / (mE E).im) *
          (N : Real) ^ (4 * lambda +
            4 * APrimeFreeLossFarLinear.sourceLoss lambda) *
          ((N : Real) ^ (-(c / 12)) + (N : Real) ^ (-(13 / 24 : Real))) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := hLinearRaw
      _ = ((APrimeFreeLossFarLinear.farLinearConstant / (mE E).im) *
            ((N : Real) ^ (4 * lambda +
              4 * APrimeFreeLossFarLinear.sourceLoss lambda) *
              ((N : Real) ^ (-(c / 12)) +
                (N : Real) ^ (-(13 / 24 : Real))))) *
            Step2Moment.ratR E s N v ^ (-2 : Real) := by ring
      _ ≤ ((APrimeFreeLossFarLinear.farLinearConstant / (mE E).im) *
            (2 * (N : Real) ^ (4 * sourceLoss lambda))) *
            Step2Moment.ratR E s N v ^ (-2 : Real) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hFarLinearPower hcoef) hRinv
      _ = _ := by ring_nf
  have hTailWeak :
      (∫ u in (s N)..v,
        APrimeFreeLossNear.normalizedNearTail E D s
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.capLoss lambda) N v u) ≤
        8 * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hTailRaw :
        (∫ u in (s N)..v,
          APrimeFreeLossNear.normalizedNearTail E D s
            (APrimeFreeLossNear.hLoss lambda)
            (APrimeFreeLossNear.hLoss lambda)
            (APrimeFreeLossNear.capLoss lambda) N v u) ≤
          8 * (N : Real) ^ (-(21 : Real)) *
            Step2Moment.ratR E s N v ^ (-2 : Real) := by
      simpa only [v] using hTailBound
    calc
      _ ≤ 8 * (N : Real) ^ (-(21 : Real)) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := hTailRaw
      _ ≤ 8 * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTailPow (by norm_num : 0 ≤ (8 : Real))) hRinv
  have hNonlinearWeak :
      (∫ u in (s N)..v,
        APrimeFreeLossFarNonlinear.normalizedFarNonlinear E D s
          (APrimeFreeLossFarNonlinear.sourceLoss lambda)
          (APrimeFreeLossFarNonlinear.sourceLoss lambda)
          (APrimeFreeLossFarNonlinear.capLoss lambda) N v u) ≤
        (2 / (mE E).im) * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hNonlinearRaw :
        (∫ u in (s N)..v,
          APrimeFreeLossFarNonlinear.normalizedFarNonlinear E D s
            (APrimeFreeLossFarNonlinear.sourceLoss lambda)
            (APrimeFreeLossFarNonlinear.sourceLoss lambda)
            (APrimeFreeLossFarNonlinear.capLoss lambda) N v u) ≤
          2 / (mE E).im * (N : Real) ^ (-(c / 20)) *
            Step2Moment.ratR E s N v ^ (-2 : Real) := by
      simpa only [v] using hNonlinearBound
    have hcoef : 0 ≤ 2 / (mE E).im := by positivity
    calc
      _ ≤ (2 / (mE E).im) *
          ((N : Real) ^ (-(c / 20)) *
            Step2Moment.ratR E s N v ^ (-2 : Real)) := by
        simpa only [mul_assoc] using hNonlinearRaw
      _ ≤ (2 / (mE E).im) *
          ((N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hDecayPow hRinv) hcoef
      _ = _ := by ring
  have hQuadraticWeak :
      (∫ u in (s N)..v,
        APrimeFreeLossQuadratic.normalizedQuadratic E D s
          (APrimeFreeLossQuadratic.deltaCap lambda) N v u) ≤
        (1 / (21 * (mE E).im)) * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hQuadraticRaw :
        (∫ u in (s N)..v,
          APrimeFreeLossQuadratic.normalizedQuadratic E D s
            (APrimeFreeLossQuadratic.deltaCap lambda) N v u) ≤
          ((N : Real) ^ (-(c / 20)) *
            Step2Moment.ratR E s N v ^ (-(2 : Real))) /
            (21 * (mE E).im) := by
      simpa only [v] using hQuadraticBound
    have hcoef : 0 ≤ 1 / (21 * (mE E).im) := by positivity
    calc
      _ ≤ ((N : Real) ^ (-(c / 20)) *
          Step2Moment.ratR E s N v ^ (-(2 : Real))) /
          (21 * (mE E).im) := hQuadraticRaw
      _ = (1 / (21 * (mE E).im)) *
          ((N : Real) ^ (-(c / 20)) *
            Step2Moment.ratR E s N v ^ (-(2 : Real))) := by ring
      _ ≤ (1 / (21 * (mE E).im)) *
          ((N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        exact mul_le_mul_of_nonneg_right hDecayPow hRinv
      _ = _ := by ring
  have hMainBound' :
      (∫ u in (s N)..v,
        APrimeFreeLossNear.normalizedNearMain E s
          (APrimeFreeLossNear.hLoss lambda)
          (APrimeFreeLossNear.hLoss lambda) N v u) ≤
        (8 / (mE E).im) * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [sourceLoss, APrimeFreeLossNear.hLoss, v,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hMainBound
  let nearMain : Real → Real := fun u =>
    APrimeFreeLossNear.normalizedNearMain E s
      (APrimeFreeLossNear.hLoss lambda)
      (APrimeFreeLossNear.hLoss lambda) N v u
  let nearTail : Real → Real := fun u =>
    APrimeFreeLossNear.normalizedNearTail E D s
      (APrimeFreeLossNear.hLoss lambda)
      (APrimeFreeLossNear.hLoss lambda)
      (APrimeFreeLossNear.capLoss lambda) N v u
  let farLinear : Real → Real := fun u =>
    APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear E D s t
      (APrimeFreeLossFarLinear.sourceLoss lambda)
      (APrimeFreeLossFarLinear.sourceLoss lambda)
      (APrimeFreeLossFarLinear.deltaCap lambda) N v u
  let farNonlinear : Real → Real := fun u =>
    APrimeFreeLossFarNonlinear.normalizedFarNonlinear E D s
      (APrimeFreeLossFarNonlinear.sourceLoss lambda)
      (APrimeFreeLossFarNonlinear.sourceLoss lambda)
      (APrimeFreeLossFarNonlinear.capLoss lambda) N v u
  let quadratic : Real → Real := fun u =>
    APrimeFreeLossQuadratic.normalizedQuadratic E D s
      (APrimeFreeLossQuadratic.deltaCap lambda) N v u
  have hMainInt := intervalIntegrable_nearMain hE (hs0 N) hvIcc.1 hv1
    (APrimeFreeLossNear.hLoss lambda) (APrimeFreeLossNear.hLoss lambda)
  have hTailInt := intervalIntegrable_nearTail (D := D) hE (hs0 N) hvIcc.1 hv1
    (APrimeFreeLossNear.hLoss lambda) (APrimeFreeLossNear.hLoss lambda)
    (APrimeFreeLossNear.capLoss lambda)
  have hFarLinearInt := intervalIntegrable_farLinear (D := D) (t := t) (s := s)
    hE (hs0 N) hvIcc.1 hv1
    (APrimeFreeLossFarLinear.sourceLoss lambda)
    (APrimeFreeLossFarLinear.sourceLoss lambda)
    (APrimeFreeLossFarLinear.deltaCap lambda)
  have hFarNonlinearInt :=
    APrimeGeneralMovingDriftFarNonlinearSlot.intervalIntegrable_normalizedFarNonlinear
      (D := D) hE (hs0 N) hvIcc.1 hv1
      (APrimeFreeLossFarNonlinear.sourceLoss lambda)
      (APrimeFreeLossFarNonlinear.sourceLoss lambda)
      (APrimeFreeLossFarNonlinear.capLoss lambda)
  have hQuadraticInt :=
    intervalIntegrable_quadratic (D := D) hE (hs0 N) hvIcc.1 hv1
      (APrimeFreeLossQuadratic.deltaCap lambda)
  have hFirstTwo := hMainInt.add hTailInt
  have hFirstThree := hFirstTwo.add hFarLinearInt
  have hFirstFour := hFirstThree.add hFarNonlinearInt
  have hRowsInt : IntervalIntegrable
      (fun u => nearMain u + nearTail u + farLinear u + farNonlinear u + quadratic u)
      volume (s N) v := by
    simpa [nearMain, nearTail, farLinear, farNonlinear, quadratic] using
      hFirstFour.add hQuadraticInt
  have hProfileInt : IntervalIntegrable
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
        (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
        (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N v u)
      volume (s N) v := by
    have heq : (fun u => APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
        (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
        (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda) N v u) =
        (fun u => nearMain u + nearTail u + farLinear u + farNonlinear u + quadratic u) := by
      funext u
      simpa [nearMain, nearTail, farLinear, farNonlinear, quadratic,
        sourceLoss, APrimeFreeLossNear.hLoss, APrimeFreeLossNear.capLoss,
        APrimeFreeLossFarLinear.sourceLoss, APrimeFreeLossFarLinear.deltaCap,
        APrimeFreeLossFarNonlinear.sourceLoss, APrimeFreeLossFarNonlinear.capLoss,
        APrimeFreeLossQuadratic.deltaCap,
        APrimeGeneralMovingSmoothDriftNormBudget.deltaCap] using
        literal_profile_eq_five_rows E D s t lambda N v u
    rw [heq]
    exact hRowsInt
  have hProfileIntegralEq :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
          (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
          N v u) =
      (∫ u in (s N)..v, nearMain u) +
      (∫ u in (s N)..v, nearTail u) +
      (∫ u in (s N)..v, farLinear u) +
      (∫ u in (s N)..v, farNonlinear u) +
      (∫ u in (s N)..v, quadratic u) := by
    calc
      _ = ∫ u in (s N)..v,
          nearMain u + nearTail u + farLinear u + farNonlinear u + quadratic u := by
            apply intervalIntegral.integral_congr
            intro u hu
            exact (show (fun x => APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
                (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
                (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
                N v x) =
                (fun x => nearMain x + nearTail x + farLinear x + farNonlinear x + quadratic x)
                from by
                  funext x
                  simpa [nearMain, nearTail, farLinear, farNonlinear, quadratic,
                    sourceLoss, APrimeFreeLossNear.hLoss, APrimeFreeLossNear.capLoss,
                    APrimeFreeLossFarLinear.sourceLoss, APrimeFreeLossFarLinear.deltaCap,
                    APrimeFreeLossFarNonlinear.sourceLoss,
                    APrimeFreeLossFarNonlinear.capLoss,
                    APrimeFreeLossQuadratic.deltaCap,
                    APrimeGeneralMovingSmoothDriftNormBudget.deltaCap] using
                    literal_profile_eq_five_rows E D s t lambda N v x) ▸ rfl
      _ = (∫ u in (s N)..v,
          nearMain u + nearTail u + farLinear u + farNonlinear u) +
          (∫ u in (s N)..v, quadratic u) := by
            rw [intervalIntegral.integral_add hFirstFour hQuadraticInt]
      _ = ((∫ u in (s N)..v,
          nearMain u + nearTail u + farLinear u) +
          (∫ u in (s N)..v, farNonlinear u)) +
          (∫ u in (s N)..v, quadratic u) := by
            rw [intervalIntegral.integral_add hFirstThree hFarNonlinearInt]
      _ = (((∫ u in (s N)..v,
          nearMain u + nearTail u) +
          (∫ u in (s N)..v, farLinear u)) +
          (∫ u in (s N)..v, farNonlinear u)) +
          (∫ u in (s N)..v, quadratic u) := by
            rw [intervalIntegral.integral_add hFirstTwo hFarLinearInt]
      _ = ((((∫ u in (s N)..v, nearMain u) +
          (∫ u in (s N)..v, nearTail u)) +
          (∫ u in (s N)..v, farLinear u)) +
          (∫ u in (s N)..v, farNonlinear u)) +
          (∫ u in (s N)..v, quadratic u) := by
            rw [intervalIntegral.integral_add hMainInt hTailInt]
      _ = _ := by ring
  have hProfileBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
          (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
          N v u) ≤
        profileConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hMainBound' := by
      simpa [nearMain, sourceLoss, APrimeFreeLossNear.hLoss, v] using hMainBound'
    have hTailWeak' := by
      simpa [nearTail, sourceLoss, APrimeFreeLossNear.hLoss,
        APrimeFreeLossNear.capLoss, v] using hTailWeak
    have hLinearWeak' := by
      simpa [farLinear, sourceLoss, APrimeFreeLossFarLinear.sourceLoss,
        APrimeFreeLossFarLinear.deltaCap, v] using hLinearWeak
    have hNonlinearWeak' := by
      simpa [farNonlinear, sourceLoss,
        APrimeFreeLossFarNonlinear.sourceLoss,
        APrimeFreeLossFarNonlinear.capLoss, v] using hNonlinearWeak
    have hQuadraticWeak' := by
      simpa [quadratic, sourceLoss, APrimeFreeLossQuadratic.deltaCap, v] using
        hQuadraticWeak
    rw [hProfileIntegralEq]
    have hcoeff : profileConstant E =
        8 / (mE E).im + 8 +
          2 * APrimeFreeLossFarLinear.farLinearConstant / (mE E).im +
          2 / (mE E).im + 1 / (21 * (mE E).im) := by
      rfl
    rw [hcoeff]
    nlinarith [hMainBound', hTailWeak', hLinearWeak',
      hNonlinearWeak', hQuadraticWeak']
  have hConsumerData := hConsumerN k hk a
  rcases hConsumerData with ⟨_hgi, ⟨_hpi, hActualRaw⟩⟩
  have hActualRaw' :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) ≤
        (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
            (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
            (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
            N v u) + (v - s N) * (N : Real) ^ (-1 : Real) := by
    simpa [v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.deltaCap] using hActualRaw
  let vv : TimeIcc s t N := ⟨v, hvIcc⟩
  have hR30 : Step2Moment.ratR E s N v ^ (30 : Nat) ≤ B.scale E N v := by
    have hh := hMarginN vv
    simpa only [vv, Step2Moment.ratR] using hh
  have hScaleN : B.scale E N v ≤ (N : Real) := by
    obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N vv
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast hdimN.1
    change (B.W N : Real) * B.ell N v * etaT E v ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hvIcc.1 hv1
  have hR2Nat : Step2Moment.ratR E s N v ^ (2 : Nat) ≤ (N : Real) := by
    have hR28 : 1 ≤ Step2Moment.ratR E s N v ^ (28 : Nat) := one_le_pow₀ hR1
    have hR2to30 : Step2Moment.ratR E s N v ^ (2 : Nat) ≤
        Step2Moment.ratR E s N v ^ (30 : Nat) := by
      calc
        _ = Step2Moment.ratR E s N v ^ 2 * 1 := by simp
        _ ≤ Step2Moment.ratR E s N v ^ 2 *
              Step2Moment.ratR E s N v ^ (28 : Nat) :=
          mul_le_mul_of_nonneg_left hR28 (sq_nonneg _)
        _ = Step2Moment.ratR E s N v ^ (30 : Nat) := by rw [← pow_add]
    exact hR2to30.trans (hR30.trans hScaleN)
  have hR2real : Step2Moment.ratR E s N v ^ (2 : Real) ≤ (N : Real) := by
    have heq : Step2Moment.ratR E s N v ^ (2 : Real) =
        Step2Moment.ratR E s N v ^ (2 : Nat) := by
      simpa only [Nat.cast_ofNat] using
        (Real.rpow_natCast (Step2Moment.ratR E s N v) 2)
    rw [heq]
    exact hR2Nat
  have hNinv_le_Rinv : (N : Real) ^ (-1 : Real) ≤
      Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hNinv : (N : Real) ^ (-1 : Real) = (N : Real)⁻¹ := by
      rw [Real.rpow_neg hNpos.le]
      simp
    have hRinv : Step2Moment.ratR E s N v ^ (-2 : Real) =
        (Step2Moment.ratR E s N v ^ (2 : Real))⁻¹ := by
      rw [Real.rpow_neg hRv.le]
    rw [hNinv, hRinv]
    exact inv_anti₀ (by positivity) hR2real
  have hLen : 0 ≤ v - s N ∧ v - s N ≤ 1 := by
    constructor
    · linarith [hvIcc.1]
    · linarith [hvIcc.2, ht1 N, hs0 N]
  have hComplement : (v - s N) * (N : Real) ^ (-1 : Real) ≤
      (N : Real) ^ (4 * sourceLoss lambda) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
    have hNpow0 : 0 ≤ (N : Real) ^ (-1 : Real) := by positivity
    have hT : 0 ≤ Step2Moment.ratR E s N v ^ (-2 : Real) := hRinv
    calc
      _ ≤ (N : Real) ^ (-1 : Real) := by
        calc
          _ ≤ 1 * (N : Real) ^ (-1 : Real) :=
            mul_le_mul_of_nonneg_right hLen.2 hNpow0
          _ = _ := by ring
      _ ≤ Step2Moment.ratR E s N v ^ (-2 : Real) := hNinv_le_Rinv
      _ = 1 * Step2Moment.ratR E s N v ^ (-2 : Real) := by ring
      _ ≤ (N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real) :=
          mul_le_mul_of_nonneg_right hQone hT
  have hActualBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) ≤
        assemblyConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
    calc
      _ ≤ (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
            (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
            (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
            N v u) + (v - s N) * (N : Real) ^ (-1 : Real) := hActualRaw'
      _ ≤ profileConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real) +
          (N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real) :=
          add_le_add hProfileBound hComplement
      _ = assemblyConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real) := by
          rw [assemblyConstant]
          ring
  have hProfileBoundEndpoint := hProfileBound
  simpa [v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
    (show
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (sourceLoss lambda) (sourceLoss lambda) (sourceLoss lambda)
          (APrimeGeneralMovingSmoothDriftNormBudget.deltaCap lambda lambda)
          N v u) ≤ profileConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
          Step2Moment.ratR E s N v ^ (-2 : Real) ∧
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) ≤
          assemblyConstant E * (N : Real) ^ (4 * sourceLoss lambda) *
            Step2Moment.ratR E s N v ^ (-2 : Real) from
      ⟨hProfileBoundEndpoint, hActualBound⟩)

/-- The corrected losses have one common resident, an active positive mesh
cell, a sample in the common event, and positive actual smooth weight. -/
abbrev corrected_schedule_same_event_positive_cell_witness :=
  APrimeFreeLossFarLinear.corrected_same_loss_positive_cell_witness

#print axioms literal_profile_eq_five_rows
#print axioms eventually_full_profile_and_actual_drift_integrals_le
#print axioms corrected_schedule_same_event_positive_cell_witness

end

end RBM.APrimeFreeLossDriftAssembly
