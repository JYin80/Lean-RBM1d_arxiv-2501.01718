/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftFarLinearEndpointSlotRepair

/-!
# T1295: exact T615 far-linear integral under the corrected same-loss schedule

This module imports T1003 and uses its public `normalizedFarLinear` directly.
It proves only the first summand of T615's far source, with the corrected
schedule `deltaWeight = xi = lambda`, `deltaCap = 2 lambda`, and each source
loss equal to `lambda / 1000`. The two endpoint gains remain separate in the
integral estimate: `N^(-c/12)` from `flowDelta` and `N^(-13/24)` from `W⁻¹`.
The exact terminal `ratR(v)^(-2)` is retained, uniformly over all active cells.
-/

namespace RBM.APrimeFreeLossFarLinear

open APrimeGeneralMovingDriftFarLinearSlot (normalizedFarLinear)

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The corrected common loss used by the actual smooth weight and its buffer. -/
noncomputable def deltaWeight (lambda : Real) : Real := lambda
noncomputable def xi (lambda : Real) : Real := lambda
noncomputable def deltaCap (lambda : Real) : Real := 2 * lambda

/-- The three T615 source losses are selected after the target loss. -/
noncomputable def sourceLoss (lambda : Real) : Real := lambda / 1000

/-- The absolute coefficient obtained from the literal block-cap estimate. -/
noncomputable def farLinearConstant : Real :=
  8 * (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) / 5

private theorem corrected_schedule_arithmetic {lambda c : Real}
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    0 < deltaWeight lambda ∧ 0 < xi lambda ∧ 0 < deltaCap lambda ∧
      0 < sourceLoss lambda ∧ deltaWeight lambda + xi lambda = deltaCap lambda ∧
      sourceLoss lambda ≤ deltaCap lambda / 16 ∧
      deltaCap lambda ≤ c / 20 ∧
      sourceLoss lambda + 4 * lambda + 2 / 15 < 1 := by
  have hlambdaC : lambda ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  have hlambda1 : lambda ≤ (1 / 10000 : Real) := hsmall.trans (min_le_left _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hlambda
  · exact hlambda
  · dsimp [deltaCap]; positivity
  · dsimp [sourceLoss]; positivity
  · dsimp [deltaWeight, xi, deltaCap]; ring
  · dsimp [sourceLoss, deltaCap]; nlinarith
  · dsimp [deltaCap]; nlinarith
  · dsimp [sourceLoss]; nlinarith

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem blockCap_le_const
    {E : Real} {s : Nat → Real} {tau delta : Real} {N : Nat} {u : Real}
    (hN : 1 ≤ N) (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (hR : 1 ≤ Step2Moment.ratR E s N u) :
    APrimeGeneralMovingDriftSource.blockCap E s tau delta N u ≤
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        (N : Real) ^ (tau + 2 * delta) * Step2Moment.ratR E s N u ^ 4 := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
  have hR4 : 1 ≤ Step2Moment.ratR E s N u ^ 4 := one_le_pow₀ hR
  have htauPow : 1 ≤ (N : Real) ^ tau := Real.one_le_rpow hn htau
  have hdeltaPow : 1 ≤ (N : Real) ^ (2 * delta) :=
    Real.one_le_rpow hn (by positivity)
  have hX1 : 1 ≤ (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
      Step2Moment.ratR E s N u ^ 4 := by
    nlinarith [mul_le_mul htauPow hdeltaPow (by positivity) (by positivity),
      mul_le_mul (mul_le_mul htauPow hdeltaPow (by positivity) (by positivity)) hR4
        (by positivity) (by positivity)]
  have htauX : (N : Real) ^ tau ≤
      (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
    have hmul : 1 ≤ (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
      nlinarith [mul_le_mul hdeltaPow hR4 (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hmul
      (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real) ^ tau * (N : Real) ^ (2 * delta) =
      (N : Real) ^ (tau + 2 * delta) := by rw [Real.rpow_add hn0]
  unfold APrimeGeneralMovingDriftSource.blockCap
  calc
    1 + (N : Real) ^ tau *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
            Step2Moment.ratR E s N u ^ 4) + 2) <=
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        ((N : Real) ^ tau * (N : Real) ^ (2 * delta)) *
          Step2Moment.ratR E s N u ^ 4 := by
      let X := (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4
      have hmain : (N : Real) ^ tau *
          (9 * Real.exp (Real.sqrt 3) *
            ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
              Step2Moment.ratR E s N u ^ 4)) =
          (9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) * X := by
        dsimp [X]
        ring
      rw [mul_add, hmain]
      dsimp only [X] at hX1 htauX ⊢
      nlinarith
    _ = _ := by rw [hpow]

private theorem continuousOn_farLinear {E D : Real} {s t : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (zetaCtr tauG delta : Real) :
    ContinuousOn (fun u => normalizedFarLinear E D s t zetaCtr tauG delta N v u)
      (Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u, u ∈ Icc (s N) v → 1 - u ≠ 0 := by
      intro u hu; linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRatPos : ∀ u, u ∈ Icc (s N) v →
      0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRatInv : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) (Icc (s N) v) :=
    hRat.rpow_const (fun u hu => Or.inl (ne_of_gt (hRatPos u hu)))
  have hEllPos : ∀ u, u ∈ Icc (s N) v → B.ell N u ≠ 0 := by
    intro u hu
    exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
      (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1)))
  have hEllInv : ContinuousOn (fun u => (B.ell N u)⁻¹) (Icc (s N) v) :=
    hEll.inv₀ hEllPos
  have hcFar : ContinuousOn (fun u => Lemma57.cFar (B.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    unfold Lemma57.cFar
    have hpoly : ContinuousOn (fun u =>
        4 * Real.log (B.W N : Real) ^ (3 / 2 : Real) + 8 * (B.ell N u)⁻¹)
        (Icc (s N) v) := by fun_prop
    exact hpoly.mul continuousOn_const
  have hcap : ContinuousOn
      (fun u => APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u)
      (Icc (s N) v) := by
    unfold APrimeGeneralMovingDriftSource.blockCap Step2Moment.ratR
    have hpow : ContinuousOn (fun u =>
        (Step2Moment.ratR E s N u) ^ (4 : Nat)) (Icc (s N) v) := by
      exact hRat.pow 4
    fun_prop
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Icc (s N) v) :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hEllRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  unfold normalizedFarLinear
  have hmain : ContinuousOn (fun u =>
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) *
        ((etaT E u)⁻¹ * (4 * (N : Real)^zetaCtr *
          (B.ell N u / B.ell N (s N))) *
          (Lemma57.cFar (B.W N : Real) (B.ell N u) *
            APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u *
            (flowDelta d E t N + (B.W N : Real)⁻¹)))) (Icc (s N) v) := by
    fun_prop
  exact hmain

private theorem scale_le_N (hE : |E| < 2) {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {N : Nat} (hdim : B.W N * B.L N ≤ N) (u : TimeIcc s t N) :
    B.scale E N (u : Real) ≤ (N : Real) := by
  obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hdim
  change (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) ≤ (N : Real)
  calc
    _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
    _ = (B.W N : Real) * (B.L N : Real) := by ring
    _ ≤ (N : Real) := hWL

private theorem integral_ratio_eta_inv_five_halves
    {E s0 v : Real} (hE : |E| < 2) (hs0 : s0 ≤ v) (hv1 : v < 1) :
    (∫ u in s0..v,
        (APrimeDriftIntegralBudget.ratio s0 u) ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) ≤
      (APrimeDriftIntegralBudget.ratio s0 v) ^ (5 / 2 : Real) /
        ((5 / 2 : Real) * (mE E).im) := by
  have hs1 : s0 < 1 := hs0.trans_lt hv1
  have hm := mE_im_pos hE
  have hi := APrimeDriftIntegralBudget.integral_ratio_power
    hs1 hs0 hv1 hm.ne' (by norm_num : (5 / 2 : Real) ≠ 0)
  have hfun : (fun u => APrimeDriftIntegralBudget.ratio s0 u ^ (5 / 2 : Real) *
      (etaT E u)⁻¹) =
      (fun u => APrimeDriftIntegralBudget.ratio s0 u ^ (5 / 2 : Real) /
        ((mE E).im * (1 - u))) := by
    funext u
    rw [Step2.etaT_eq]
    ring
  rw [hfun, hi]
  have hR : 1 ≤ APrimeDriftIntegralBudget.ratio s0 v := by
    unfold APrimeDriftIntegralBudget.ratio
    rw [le_div_iff₀ (by linarith : 0 < 1 - v)]
    linarith
  have hden : 0 < (mE E).im * (5 / 2 : Real) := by positivity
  have hpow : 1 ≤ APrimeDriftIntegralBudget.ratio s0 v ^ (5 / 2 : Real) :=
    Real.one_le_rpow hR (by norm_num)
  calc
    (APrimeDriftIntegralBudget.ratio s0 v ^ (5 / 2 : Real) - 1) /
        ((mE E).im * (5 / 2 : Real)) ≤
      APrimeDriftIntegralBudget.ratio s0 v ^ (5 / 2 : Real) /
        ((mE E).im * (5 / 2 : Real)) := by
          exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
    _ = APrimeDriftIntegralBudget.ratio s0 v ^ (5 / 2 : Real) /
        ((5 / 2 : Real) * (mE E).im) := by congr 1 <;> ring

/-- Keep the two separate endpoint gains from the flow and bandwidth terms.
The thirty-power Cond272 margin yields `R^(5/2) S^(-1/6) ≤ N^(-c/12)`;
the bounds `S ≤ N` and `W ≥ N^(5/8)` yield `R^(5/2)/W ≤ N^(-13/24)`. -/
private theorem endpoint_flow_factor_le_margins
    {N : Nat} {R S W c : Real}
    (hN : 1 ≤ (N : Real)) (hc : 0 < c)
    (hSlo : (N : Real)^c ≤ S) (hShi : S ≤ N)
    (hW : (N : Real)^(5 / 8 : Real) ≤ W)
    (hR : 1 ≤ R) (hR30 : R ^ (30 : Real) ≤ S) :
    R ^ (5 / 2 : Real) * (S⁻¹) ^ (1 / 6 : Real) +
      R ^ (5 / 2 : Real) / W ≤
        (N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real)) := by
  have hN0 : 0 < (N : Real) := by linarith
  have hS1 : 1 ≤ S := by
    calc
      1 ≤ (N : Real)^c := Real.one_le_rpow hN hc.le
      _ ≤ S := hSlo
  have hS0 : 0 < S := by linarith
  have hR0 : 0 < R := by linarith
  have hNc0 : 0 < (N : Real)^c := Real.rpow_pos_of_pos hN0 c
  have hRpowS : R ^ (5 / 2 : Real) ≤ S ^ (1 / 12 : Real) := by
    calc
      R ^ (5 / 2 : Real) = (R ^ (30 : Real)) ^ (1 / 12 : Real) := by
        rw [← Real.rpow_mul hR0.le]
        congr 1 <;> norm_num
      _ ≤ S ^ (1 / 12 : Real) :=
        Real.rpow_le_rpow (by positivity) hR30 (by norm_num)
  have hSroot : ((N : Real)^c) ^ (1 / 12 : Real) ≤ S ^ (1 / 12 : Real) :=
    Real.rpow_le_rpow (by positivity) hSlo (by norm_num)
  have hSrootInv : (S ^ (1 / 12 : Real))⁻¹ ≤
      (((N : Real)^c) ^ (1 / 12 : Real))⁻¹ :=
    by simpa [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNc0 _) hSroot
  have hSneg : S ^ (-(1 / 12 : Real)) ≤
      ((N : Real)^c) ^ (-(1 / 12 : Real)) := by
    rw [Real.rpow_neg hS0.le, Real.rpow_neg hNc0.le]
    exact hSrootInv
  have hSnegN : ((N : Real)^c) ^ (-(1 / 12 : Real)) =
      (N : Real)^(-(c / 12)) := by
    rw [← Real.rpow_mul hN0.le]
    congr 1 <;> ring
  have hFlowEq : (S⁻¹) ^ (1 / 6 : Real) = S ^ (-(1 / 6 : Real)) := by
    rw [Real.inv_rpow hS0.le, ← Real.rpow_neg hS0.le]
  have hFlow : R ^ (5 / 2 : Real) * (S⁻¹) ^ (1 / 6 : Real) ≤
      (N : Real)^(-(c / 12)) := by
    rw [hFlowEq]
    calc
      R ^ (5 / 2 : Real) * S ^ (-(1 / 6 : Real)) ≤
          S ^ (1 / 12 : Real) * S ^ (-(1 / 6 : Real)) :=
        mul_le_mul_of_nonneg_right hRpowS (Real.rpow_nonneg hS0.le _)
      _ = S ^ (-(1 / 12 : Real)) := by
        rw [← Real.rpow_add hS0]
        congr 1 <;> ring
      _ ≤ (N : Real)^(-(c / 12)) := hSneg.trans_eq hSnegN
  have hRpowN : R ^ (5 / 2 : Real) ≤ (N : Real) ^ (1 / 12 : Real) := by
    have hR30N : R ^ (30 : Real) ≤ (N : Real) := hR30.trans hShi
    calc
      R ^ (5 / 2 : Real) = (R ^ (30 : Real)) ^ (1 / 12 : Real) := by
        rw [← Real.rpow_mul hR0.le]
        congr 1 <;> norm_num
      _ ≤ (N : Real) ^ (1 / 12 : Real) :=
        Real.rpow_le_rpow (by positivity) hR30N (by norm_num)
  have hW0 : 0 < W := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hN0 (5 / 8 : Real)) hW
  have hNpow0 : 0 < (N : Real) ^ (5 / 8 : Real) :=
    Real.rpow_pos_of_pos hN0 _
  have hBandwidth : R ^ (5 / 2 : Real) / W ≤
      (N : Real)^(-(13 / 24 : Real)) := by
    have hdiv1 : R ^ (5 / 2 : Real) / W ≤ (N : Real)^(1 / 12 : Real) / W :=
      div_le_div_of_nonneg_right hRpowN (le_of_lt hW0)
    have hdiv2 : (N : Real)^(1 / 12 : Real) / W ≤
        (N : Real)^(1 / 12 : Real) / (N : Real)^(5 / 8 : Real) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hNpow0 hW
    have hpow : (N : Real)^(1 / 12 : Real) / (N : Real)^(5 / 8 : Real) =
        (N : Real)^(-(13 / 24 : Real)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]
      congr 1 <;> norm_num
    exact hdiv1.trans (hdiv2.trans_eq hpow)
  linarith

private theorem eventually_cFar_le {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {theta : Real} (htheta : 0 < theta) :
    ∀ᶠ N : Nat in atTop, ∀ u ∈ Icc (s N) (t N),
      Lemma57.cFar (B.W N : Real) (B.ell N u) ≤ (N : Real)^theta := by
  filter_upwards [Step2FarInputs.eventually_cFar_one_le B htheta] with N hc u hu
  have hW : 1 ≤ (B.W N : Real) := by exact_mod_cast B.W_pos N
  have hEll : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N)
    ((hs0 N).trans hu.1) (hu.2.trans_lt (ht1 N))
  exact (Step2FarInputs.cFar_le_cFar_one hW hEll).trans hc

private theorem ratio_square_le
    {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) (hsu : s N ≤ u) (hu1 : u < 1) :
    (B.ell N u / B.ell N (s N)) ^ 2 ≤ Step2Moment.ratR E s N u := by
  have hh := Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hsu hu1
  rw [ratR_eq_ratio hE]
  simpa [APrimeDriftIntegralBudget.ratio, Step2.etaT_ratio hE] using hh

private theorem ratio_times_cap_integrand_le
    {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsu : s N ≤ u) (hu1 : u < 1) :
    (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        (B.ell N u / B.ell N (s N)) *
        (Step2Moment.ratR E s N u) ^ (4 : Nat) ≤
      (Step2Moment.ratR E s N u) ^ (5 / 2 : Real) := by
  let r := Step2Moment.ratR E s N u
  let q := B.ell N u / B.ell N (s N)
  have hr : 0 < r := Step2Moment.ratR_pos hE
    (lt_of_le_of_lt hsu hu1) hu1
  have hellU : 0 < B.ell N u := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0.trans hsu) hu1)
  have hellS : 0 < B.ell N (s N) := zero_lt_one.trans_le
    (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 (lt_of_le_of_lt hsu hu1))
  have hq0 : 0 ≤ q := div_nonneg hellU.le hellS.le
  have hq2 : q ^ 2 ≤ r := by
    dsimp [r, q]
    exact ratio_square_le hE hsu hu1
  have hq : q ≤ r ^ (1 / 2 : Real) := by
    have hsqrt : q ≤ Real.sqrt r := by
      rw [Real.le_sqrt hq0 hr.le]
      simpa [pow_two] using hq2
    simpa only [Real.sqrt_eq_rpow] using hsqrt
  have hiden : r ^ (-2 : Real) * r ^ (4 : Nat) = r ^ (2 : Real) := by
    rw [← Real.rpow_natCast r 4, ← Real.rpow_add hr]
    congr 1 <;> norm_num
  have hprod : r ^ (-2 : Real) * q * r ^ (4 : Nat) =
      q * r ^ (2 : Real) := by
    calc
      r ^ (-2 : Real) * q * r ^ (4 : Nat) = q *
          (r ^ (-2 : Real) * r ^ (4 : Nat)) := by ring
      _ = q * r ^ (2 : Real) := by rw [hiden]
  rw [hprod]
  calc
    q * r ^ (2 : Real) ≤ r ^ (1 / 2 : Real) * r ^ (2 : Real) :=
      mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hr.le _)
    _ = r ^ (5 / 2 : Real) := by
      rw [← Real.rpow_add hr]
      congr 1 <;> ring

/-- **The exact T615 far-linear row under the corrected same-loss schedule.**
It integrates precisely the first summand of `farSourceCoeff`, retains both
endpoint gains and the terminal `ratR(v)^(-2)`, and is uniform over all active
cells, including `k = 0`. -/
theorem eventually_far_linear_integral_le_endpoint_margins
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c) :
    ∀ lambda : Real, 0 < lambda →
      lambda ≤ min (1 / 10000 : Real) (c / 10000) →
      ∀ᶠ N : Nat in atTop, ∀ k : Nat,
        k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        (∫ u in (s N)..v,
          normalizedFarLinear E D s t (sourceLoss lambda) (sourceLoss lambda)
            (deltaCap lambda) N v u) ≤
          (farLinearConstant / (mE E).im) *
            (N : Real) ^ (4 * lambda + 4 * sourceLoss lambda) *
            ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) *
            (Step2Moment.ratR E s N v)^(-2 : Real) := by
  intro lambda hlambda hsmall
  let theta : Real := sourceLoss lambda
  let capC : Real := 3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)
  let alpha : Real := sourceLoss lambda + sourceLoss lambda +
      2 * deltaCap lambda + 2 * theta
  have htheta : 0 < theta := by dsimp [theta, sourceLoss]; positivity
  have hschedule := corrected_schedule_arithmetic hlambda hsmall
  have hcapC : 0 < capC := by positivity
  have hcapCspec : farLinearConstant = 8 * capC / 5 := by
    simp [farLinearConstant, capC]
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im htheta
  have hcfar := eventually_cFar_le hs0 hst ht1 htheta
  have hWgrow := Gauss.Dims.bandwidth_grow
  have hmargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hxi, hcfar, hWgrow, hmargin, hreg.2,
      B.dim, eventually_ge_atTop 1] with
    N hxiN hcfarN hWgrowN hmarginN hregN hdim hN
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : Real) := by linarith
  have hWlower : (N : Real) ^ (5 / 8 : Real) ≤ (B.W N : Real) := by
    change (N : Real) ^ (5 / 8 : Real) ≤ (Dims.growW N : Real)
    have heq : (5 / 8 : Real) = 1 / 2 + 1 / 8 := by norm_num
    rw [heq]
    exact hWgrowN
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hdim.1
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvIcc : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv : TimeIcc s t N := ⟨v, hvIcc⟩
  have hv1 : v < 1 := hvIcc.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  let hTimeT : TimeIcc s t N := ⟨t N, ⟨hst N, le_rfl⟩⟩
  have hRatV : 0 < Step2Moment.ratR E s N v := Step2Moment.ratR_pos hE hs1 hv1
  have hRatV1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hvIcc.1 hv1
  have hR30t : (Step2Moment.ratR E s N (t N)) ^ (30 : Real) ≤
      B.scale E N (t N) := by
    have hh := hmarginN hTimeT
    have hh' : (Step2Moment.ratR E s N (hTimeT : Real)) ^ (30 : Nat) ≤
        B.scale E N (hTimeT : Real) := by
      change (etaT E (s N) / etaT E (hTimeT : Real)) ^ (30 : Nat) ≤ _
      exact hh
    simpa [hTimeT, Real.rpow_natCast] using hh'
  have hRatMono : Step2Moment.ratR E s N v ≤ Step2Moment.ratR E s N (t N) := by
    have hvform : Step2Moment.ratR E s N v = (1 - s N) / (1 - v) := by
      rw [Step2Moment.ratR, Step2.etaT_ratio hE]
    have htform : Step2Moment.ratR E s N (t N) = (1 - s N) / (1 - t N) := by
      rw [Step2Moment.ratR, Step2.etaT_ratio hE]
    rw [hvform, htform]
    have hvden : 0 < 1 - v := by linarith [hv1]
    have htden : 0 < 1 - t N := by linarith [ht1 N]
    rw [div_le_div_iff₀ hvden htden]
    have hprod : 0 ≤ (1 - s N) * (t N - v) :=
      mul_nonneg (by linarith [hst N, ht1 N]) (by linarith [hvIcc.2])
    nlinarith [hprod]
  have hR30 : (Step2Moment.ratR E s N v) ^ (30 : Real) ≤ B.scale E N (t N) := by
    exact (Real.rpow_le_rpow (by positivity) hRatMono (by norm_num)).trans hR30t
  have hScaleN : B.scale E N (t N) ≤ N := by
    have hh := scale_le_N hE hs0 ht1 hdim.1 hTimeT
    simpa [hTimeT] using hh
  have hW0 : 0 < (B.W N : Real) := by exact_mod_cast B.W_pos N
  have hFactor := endpoint_flow_factor_le_margins hN1 hc hregN hScaleN hWlower
    hRatV1 hR30
  have heta : 0 < (mE E).im := mE_im_pos hE
  have hInt : IntervalIntegrable
      (fun u => normalizedFarLinear E D s t
        (sourceLoss lambda)
        (sourceLoss lambda)
        (deltaCap lambda) N v u)
      volume (s N) v :=
    (continuousOn_farLinear hE (hs0 N) hvIcc.1 hv1 _ _ _).intervalIntegrable_of_Icc hvIcc.1
  have hKernelInt : IntervalIntegrable
      (fun u => (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
        (etaT E u)⁻¹) volume (s N) v := by
    have hpi := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := (5 / 2 : Real)) hvIcc.1 hv1 heta.ne'
    have heq : (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im
        (s N) (5 / 2 : Real) u) =
        (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp [heta.ne']
    rw [← heq]
    exact hpi
  have hpoint : ∀ u ∈ Icc (s N) v,
      normalizedFarLinear E D s t
        (sourceLoss lambda)
        (sourceLoss lambda)
        (deltaCap lambda) N v u ≤
      (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (sourceLoss lambda) *
        (N : Real) ^ (sourceLoss lambda +
          2 * deltaCap lambda) *
        (N : Real)^theta * capC *
        (flowDelta d E t N + (B.W N : Real)⁻¹) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
        ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) := by
    intro u hu
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hratU : 0 < Step2Moment.ratR E s N u :=
      Step2Moment.ratR_pos hE (hu.1.trans_lt hu1) hu1
    have hratU1 : 1 ≤ Step2Moment.ratR E s N u :=
      Step2Moment.one_le_ratR hE hu.1 hu1
    rcases hschedule with
      ⟨_, _, hdeltaCapPos, htauGPos, _, _, _, _⟩
    have hcap := blockCap_le_const hN htauGPos.le hdeltaCapPos.le hratU1
    have hfar0 : Lemma57.cFar (B.W N : Real) (B.ell N u) ≤ (N : Real)^theta :=
      hcfarN u ⟨hu.1, (le_trans hu.2 hvIcc.2)⟩
    have hratioSq := ratio_square_le hE hu.1 hu1
    have hratioPart := ratio_times_cap_integrand_le hE (hs0 N) hu.1 hu1
    have hcoeff0 : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im :=
      Step2.xiK_nonneg _ _ _
    have hEllU : 0 < B.ell N u := zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans hu.1) hu1)
    have hEllS : 0 < B.ell N (s N) := zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1)
    have hcoeff1 : 0 ≤ Lemma57.cFar (B.W N : Real) (B.ell N u) :=
      Lemma57.cFar_nonneg (by exact_mod_cast B.one_le_W N) hEllU
    have hscalePos : 0 < B.scale E N (t N) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 c) hregN
    have hflow0 : 0 ≤ flowDelta d E t N := by
      unfold flowDelta
      positivity
    have hrest : 0 ≤ flowDelta d E t N + (B.W N : Real)⁻¹ :=
      add_nonneg hflow0 (inv_nonneg.mpr (by positivity))
    have hcap' : APrimeGeneralMovingDriftSource.blockCap E s
        (sourceLoss lambda)
        (deltaCap lambda) N u ≤
      capC * (N : Real) ^ (sourceLoss lambda +
        2 * deltaCap lambda) *
        (Step2Moment.ratR E s N u) ^ (4 : Nat) := by
      simpa [capC] using hcap
    have hnum :
      (B.ell N u / B.ell N (s N)) *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s
          (sourceLoss lambda)
          (deltaCap lambda) N u ≤
      capC * (N : Real) ^ (sourceLoss lambda +
        2 * deltaCap lambda) *
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) := by
      have hratioPart' := ratio_times_cap_integrand_le hE (hs0 N) hu.1 hu1
      calc
        _ ≤ (B.ell N u / B.ell N (s N)) *
            (Step2Moment.ratR E s N u) ^ (-2 : Real) *
              (capC * (N : Real) ^ (sourceLoss lambda +
                2 * deltaCap lambda) *
                (Step2Moment.ratR E s N u) ^ (4 : Nat)) := by
              exact mul_le_mul_of_nonneg_left hcap'
                (mul_nonneg (div_nonneg hEllU.le hEllS.le)
                  (Real.rpow_nonneg hratU.le _))
        _ = capC * (N : Real) ^
              (sourceLoss lambda +
                2 * deltaCap lambda) *
              ((Step2Moment.ratR E s N u) ^ (-2 : Real) *
                (B.ell N u / B.ell N (s N)) *
                (Step2Moment.ratR E s N u) ^ (4 : Nat)) := by ring
        _ ≤ capC * (N : Real) ^
              (sourceLoss lambda +
                2 * deltaCap lambda) *
              (Step2Moment.ratR E s N u) ^ (5 / 2 : Real) :=
                mul_le_mul_of_nonneg_left hratioPart'
                  (by positivity)
        _ = capC * (N : Real) ^
              (sourceLoss lambda +
                2 * deltaCap lambda) *
              (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) := by
                rw [ratR_eq_ratio hE]
    rw [ratR_eq_ratio hE] at hnum
    have hXiPow : Step2.xiK (d.L N) (d.W N) (mE E).im ≤ (N : Real)^theta := hxiN
    have hEtaPos : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hEta0 : 0 ≤ (etaT E u)⁻¹ := (inv_nonneg.mpr hEtaPos.le)
    have hRvInv : 0 ≤ (Step2Moment.ratR E s N v)^(-2 : Real) := by positivity
    have hNv : 0 ≤ (N : Real)^theta := Real.rpow_nonneg hN0.le _
    have hNz : 0 ≤ (N : Real) ^
        (sourceLoss lambda) := Real.rpow_nonneg hN0.le _
    have hNg : 0 ≤ (N : Real) ^
        (sourceLoss lambda +
          2 * deltaCap lambda) :=
      Real.rpow_nonneg hN0.le _
    have hkernel0 : 0 ≤ (APrimeDriftIntegralBudget.ratio (s N) u) ^
        (5 / 2 : Real) * (etaT E u)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (by rw [← ratR_eq_ratio hE]; exact hratU.le) _) hEta0
    have hinner0 : 0 ≤ (B.ell N u / B.ell N (s N)) *
        (Step2Moment.ratR E s N u)^(-2 : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s
          (sourceLoss lambda)
          (deltaCap lambda) N u := by
      have hcap0 : 0 ≤ APrimeGeneralMovingDriftSource.blockCap E s
          (sourceLoss lambda)
          (deltaCap lambda) N u := by
        unfold APrimeGeneralMovingDriftSource.blockCap
        positivity
      exact mul_nonneg (mul_nonneg (div_nonneg hEllU.le hEllS.le)
        (Real.rpow_nonneg hratU.le _)) hcap0
    rw [ratR_eq_ratio hE] at hinner0
    unfold normalizedFarLinear
    rw [ratR_eq_ratio hE]
    calc
      _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (sourceLoss lambda) *
          (flowDelta d E t N + (B.W N : Real)⁻¹) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) *
          (etaT E u)⁻¹ * Lemma57.cFar (B.W N : Real) (B.ell N u)) *
          ((B.ell N u / B.ell N (s N)) *
            (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-2 : Real) *
            APrimeGeneralMovingDriftSource.blockCap E s
              (sourceLoss lambda)
              (deltaCap lambda) N u) := by
            simp [B, d, band, normalizedFarLinear]
            ring_nf
      _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (sourceLoss lambda) *
          (flowDelta d E t N + (B.W N : Real)⁻¹) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) *
          (etaT E u)⁻¹ * (N : Real)^theta) *
          (capC * (N : Real) ^ (sourceLoss lambda +
            2 * deltaCap lambda) *
            (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real)) := by
          gcongr
      _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (sourceLoss lambda) *
          (N : Real) ^ (sourceLoss lambda +
            2 * deltaCap lambda) *
          (N : Real)^theta * capC *
          (flowDelta d E t N + (B.W N : Real)⁻¹) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
            (etaT E u)⁻¹) := by ring
  let C : Real := 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (sourceLoss lambda) *
      (N : Real) ^ (sourceLoss lambda +
        2 * deltaCap lambda) *
      (N : Real)^theta * capC *
      (flowDelta d E t N + (B.W N : Real)⁻¹) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real)
  have hmono := intervalIntegral.integral_mono_on hvIcc.1 hInt
    (hKernelInt.const_mul C) (by
      intro u hu
      simpa [C, mul_assoc] using hpoint u hu)
  have hmonoBound : (∫ u in (s N)..v,
      normalizedFarLinear E D s t
        (sourceLoss lambda)
        (sourceLoss lambda)
        (deltaCap lambda) N v u) ≤
      C * (∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) := by
    calc
      _ ≤ ∫ u in (s N)..v, C *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
            (etaT E u)⁻¹) := hmono
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hKernel := integral_ratio_eta_inv_five_halves hE hvIcc.1 hv1
  have hC0 : 0 ≤ C := by
    have hxi0 := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    have hW0' : 0 < (B.W N : Real) := by exact_mod_cast B.W_pos N
    have hscalePos : 0 < B.scale E N (t N) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 c) hregN
    have hflow0 : 0 ≤ flowDelta d E t N := by unfold flowDelta; positivity
    dsimp [C]
    positivity
  have hRvInv : 0 ≤ (Step2Moment.ratR E s N v)^(-2 : Real) := by positivity
  have hCbound : C *
      (∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) ≤
      (farLinearConstant / (mE E).im) *
        (N : Real)^alpha *
        ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) *
        (Step2Moment.ratR E s N v)^(-2 : Real) := by
    have hgeom :
      (Step2Moment.ratR E s N v) ^ (5 / 2 : Real) *
      (flowDelta d E t N + (B.W N : Real)⁻¹) ≤
          (N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real)) := by
      have hflowEq : flowDelta d E t N =
          (B.scale E N (t N))⁻¹ ^ (1 / 6 : Real) := by rfl
      calc
        _ = Step2Moment.ratR E s N v ^ (5 / 2 : Real) *
            (B.scale E N (t N))⁻¹ ^ (1 / 6 : Real) +
            Step2Moment.ratR E s N v ^ (5 / 2 : Real) / (B.W N : Real) := by
              rw [hflowEq, mul_add]
              simp [div_eq_mul_inv]
        _ ≤ (N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real)) := hFactor
    have hscalePos : 0 < B.scale E N (t N) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 c) hregN
    have hflow0 : 0 ≤ flowDelta d E t N := by
      unfold flowDelta
      exact Real.rpow_nonneg (inv_nonneg.mpr hscalePos.le) _
    let hG : Real := (Step2Moment.ratR E s N v) ^ (5 / 2 : Real) *
        (flowDelta d E t N + (B.W N : Real)⁻¹)
    have hG0 : 0 ≤ hG := by
      dsimp [hG]
      exact mul_nonneg (Real.rpow_nonneg hRatV.le _)
        (add_nonneg hflow0 (inv_nonneg.mpr hW0.le))
    have hxiG : Step2.xiK (d.L N) (d.W N) (mE E).im * hG ≤
        (N : Real)^theta *
          ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) := by
      calc
        _ ≤ (N : Real)^theta * hG := mul_le_mul_of_nonneg_right hxiN (by positivity)
        _ ≤ (N : Real)^theta *
            ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) :=
          mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hN0.le _)
        _ = _ := by ring
    have hpowN :
      (N : Real) ^ (sourceLoss lambda) *
        (N : Real) ^ (sourceLoss lambda +
          2 * deltaCap lambda) *
        (N : Real)^theta * (N : Real)^theta = (N : Real)^alpha := by
      have hza : (N : Real) ^ (sourceLoss lambda) *
          (N : Real) ^ (sourceLoss lambda +
            2 * deltaCap lambda) =
          (N : Real) ^ (sourceLoss lambda +
            (sourceLoss lambda +
              2 * deltaCap lambda)) := by
        rw [← Real.rpow_add hN0]
      have hthetaPow : (N : Real)^theta * (N : Real)^theta =
          (N : Real)^(theta + theta) := by rw [← Real.rpow_add hN0]
      have hexp : (sourceLoss lambda +
          (sourceLoss lambda +
            2 * deltaCap lambda)) +
          (theta + theta) = alpha := by
        dsimp [alpha, deltaCap, sourceLoss, theta]
        ring
      calc
        _ = ((N : Real) ^ (sourceLoss lambda) *
            (N : Real) ^ (sourceLoss lambda +
              2 * deltaCap lambda)) *
            ((N : Real)^theta * (N : Real)^theta) := by ring
        _ = (N : Real) ^
            (sourceLoss lambda +
              (sourceLoss lambda +
                2 * deltaCap lambda)) *
            (N : Real)^(theta + theta) := by rw [hza, hthetaPow]
        _ = (N : Real)^alpha := by rw [← Real.rpow_add hN0, hexp]
    calc
      _ ≤ C * ((APrimeDriftIntegralBudget.ratio (s N) v) ^ (5 / 2 : Real) /
          ((5 / 2 : Real) * (mE E).im)) :=
            mul_le_mul_of_nonneg_left hKernel hC0
      _ = (4 * capC / ((5 / 2 : Real) * (mE E).im)) *
          ((N : Real) ^ (sourceLoss lambda) *
            (N : Real) ^ (sourceLoss lambda +
              2 * deltaCap lambda) *
            (N : Real)^theta *
            (Step2.xiK (d.L N) (d.W N) (mE E).im * hG)) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
          dsimp [C, hG]
          rw [← ratR_eq_ratio hE]
          ring
      _ ≤ (4 * capC / ((5 / 2 : Real) * (mE E).im)) *
          ((N : Real) ^ (sourceLoss lambda) *
            (N : Real) ^ (sourceLoss lambda +
              2 * deltaCap lambda) *
            (N : Real)^theta *
            ((N : Real)^theta *
              ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))))) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
          gcongr
      _ = (4 * capC / ((5 / 2 : Real) * (mE E).im)) *
          (((N : Real) ^ (sourceLoss lambda) *
            (N : Real) ^ (sourceLoss lambda + 2 * deltaCap lambda) *
            (N : Real)^theta * (N : Real)^theta) *
            ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real)))) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by ring
      _ = (farLinearConstant / (mE E).im) * (N : Real)^alpha *
          ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
          rw [hpowN, hcapCspec]
          ring
  calc
    (∫ u in (s N)..v,
        normalizedFarLinear E D s t
          (sourceLoss lambda)
          (sourceLoss lambda)
          (deltaCap lambda) N v u) ≤
      C * (∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) := hmonoBound
    _ ≤ (farLinearConstant / (mE E).im) * (N : Real)^alpha *
        ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) *
        (Step2Moment.ratR E s N v)^(-2 : Real) := hCbound
    _ = (farLinearConstant / (mE E).im) *
        (N : Real)^(4 * lambda + 4 * sourceLoss lambda) *
        ((N : Real)^(-(c / 12)) + (N : Real)^(-(13 / 24 : Real))) *
        (Step2Moment.ratR E s N v)^(-2 : Real) := by
      congr 2
      dsimp [alpha, deltaCap, sourceLoss, theta]
      ring

/-- The corrected loss leaves both requested polynomial margins strictly
positive after the factor `N^(4 lambda + 4 h)`. -/
theorem corrected_integral_exponent_room {c lambda : Real}
    (hc : 0 < c) (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    4 * lambda + 4 * sourceLoss lambda < c / 12 ∧
      4 * lambda + 4 * sourceLoss lambda < 13 / 24 := by
  have hlambdaC : lambda ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  have hlambda1 : lambda ≤ (1 / 10000 : Real) :=
    hsmall.trans (min_le_left _ _)
  constructor
  · dsimp [sourceLoss]
    nlinarith
  · dsimp [sourceLoss]
    nlinarith

/-- A same-sample, positive-cell witness for the corrected common-loss
schedule. In particular, the shared source event is nonempty and the actual
smooth weight is positive at `deltaWeight = lambda`. -/
theorem corrected_same_loss_positive_cell_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧ Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∃ lambda : Real, 0 < lambda ∧
        lambda ≤ min (1 / 10000 : Real) (c / 10000) ∧
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (sourceLoss lambda) (sourceLoss lambda)
                (sourceLoss lambda) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (APrimeGeneralMovingDetFields.J 0 60 s) s t
              (APrimeGeneralMovingMesh.targetMesh 60)
              (deltaWeight lambda) 1 N 1 omega = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 (deltaWeight lambda)
              s t (APrimeGeneralMovingMesh.targetMesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh 60) N) omega := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hpos⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  have hLambdaConst : 0 < (1 / 20000 : Real) := by norm_num
  have hLambdaC : 0 < c / 20000 := by positivity
  let lambda : Real := min (1 / 20000 : Real) (c / 20000)
  have hlambda : 0 < lambda := lt_min hLambdaConst hLambdaC
  have hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000) := by
    have hleft : lambda ≤ (1 / 10000 : Real) := by
      dsimp [lambda]
      exact (min_le_left _ _).trans (by norm_num)
    have hright : lambda ≤ c / 10000 := by
      dsimp [lambda]
      exact (min_le_right _ _).trans (by nlinarith [hc])
    exact le_min hleft hright
  have hsource : 0 < sourceLoss lambda := by
    dsimp [sourceLoss]; positivity
  have hweight : 0 < deltaWeight lambda := by
    dsimp [deltaWeight]; exact hlambda
  have hresident := hpos (sourceLoss lambda) (sourceLoss lambda)
    (sourceLoss lambda) (deltaWeight lambda)
    hsource hsource hsource hweight
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    lambda, hlambda, hsmall, ?_⟩
  filter_upwards [hresident] with N hN
  obtain ⟨hwindow, omega, homega, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t
        (APrimeGeneralMovingMesh.targetMesh 60)
        (deltaWeight lambda) 1 N 1 omega = 1 := hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := deltaWeight lambda)
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) hweight.le N 1 1 omega (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos :
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t
        (APrimeGeneralMovingMesh.targetMesh 60)
        (deltaWeight lambda) 1 N 1 omega := by
    rw [hwideOne]
    norm_num
  have hactual := hwidePos.trans_le hcompare
  exact ⟨hwindow, omega, homega, hactive, hwideOne, hactual⟩

#print axioms deltaWeight
#print axioms xi
#print axioms deltaCap
#print axioms sourceLoss
#print axioms farLinearConstant
#print axioms corrected_schedule_arithmetic
#print axioms eventually_far_linear_integral_le_endpoint_margins
#print axioms corrected_integral_exponent_room
#print axioms corrected_same_loss_positive_cell_witness

end
end RBM.APrimeFreeLossFarLinear
