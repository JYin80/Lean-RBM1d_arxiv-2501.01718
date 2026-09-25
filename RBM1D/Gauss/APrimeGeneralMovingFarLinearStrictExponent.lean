/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftFarLinearEndpointSlotRepair

/-!
# T1239: sharpen the exact moving far-linear endpoint exponent

This module imports T1003 and uses its public `normalizedFarLinear` directly.
Only the first summand of T615's far source is integrated here. The estimate
retains the exact transport factors `xiK * ratR(u)^(-2) * ratR(v)^(-2)`
through the final bound. No other T615 row or full A-prime conclusion is claimed.
-/

namespace RBM.APrimeGeneralMovingFarLinearStrictExponent

open APrimeGeneralMovingDriftFarLinearSlot (normalizedFarLinear)

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

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

private theorem endpoint_flow_factor_le_two
    {N : Nat} {R S W c : Real}
    (hN : 1 ≤ (N : Real)) (hc : 0 < c)
    (hSlo : (N : Real)^c ≤ S) (hShi : S ≤ N)
    (hW : (N : Real)^(5 / 8 : Real) ≤ W)
    (hR : 1 ≤ R) (hR30 : R ^ (30 : Real) ≤ S) :
    R ^ (5 / 2 : Real) * (S⁻¹) ^ (1 / 6 : Real) +
      R ^ (5 / 2 : Real) / W ≤ 2 := by
  have hS1 : 1 ≤ S := by
    calc
      1 ≤ (N : Real)^c := Real.one_le_rpow hN hc.le
      _ ≤ S := hSlo
  have hS0 : 0 < S := by linarith
  have hN0 : 0 < (N : Real) := by linarith
  have hR0 : 0 < R := by linarith
  have hRpowS : R ^ (5 / 2 : Real) ≤ S ^ (1 / 12 : Real) := by
    calc
      R ^ (5 / 2 : Real) = (R ^ (30 : Real)) ^ (1 / 12 : Real) := by
        rw [← Real.rpow_mul hR0.le]
        congr 1 <;> norm_num
      _ ≤ S ^ (1 / 12 : Real) :=
        Real.rpow_le_rpow (by positivity) hR30 (by norm_num)
  have hRpowN : R ^ (5 / 2 : Real) ≤ (N : Real) ^ (1 / 12 : Real) := by
    have hR30N : R ^ (30 : Real) ≤ (N : Real) := hR30.trans hShi
    calc
      R ^ (5 / 2 : Real) = (R ^ (30 : Real)) ^ (1 / 12 : Real) := by
        rw [← Real.rpow_mul hR0.le]
        congr 1 <;> norm_num
      _ ≤ (N : Real) ^ (1 / 12 : Real) :=
        Real.rpow_le_rpow (by positivity) hR30N (by norm_num)
  have hFlowEq : (S⁻¹) ^ (1 / 6 : Real) = S ^ (-(1 / 6 : Real)) := by
    rw [Real.inv_rpow hS0.le, ← Real.rpow_neg hS0.le]
  have hFlow : R ^ (5 / 2 : Real) * (S⁻¹) ^ (1 / 6 : Real) ≤ 1 := by
    rw [hFlowEq]
    calc
      R ^ (5 / 2 : Real) * S ^ (-(1 / 6 : Real)) ≤
          S ^ (1 / 12 : Real) * S ^ (-(1 / 6 : Real)) :=
        mul_le_mul_of_nonneg_right hRpowS (Real.rpow_nonneg hS0.le _)
      _ = S ^ (-(1 / 12 : Real)) := by
        rw [← Real.rpow_add hS0]
        congr 1 <;> ring
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hS1 (by norm_num)
  have hNcmp : (N : Real) ^ (1 / 12 : Real) ≤ (N : Real) ^ (5 / 8 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hW0 : 0 < W := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hN0 (5 / 8 : Real)) hW
  have hBandwidth : R ^ (5 / 2 : Real) / W ≤ 1 := by
    apply (div_le_iff₀ hW0).2
    simpa [one_mul] using hRpowN.trans (hNcmp.trans hW)
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

/-- **T1239's strict-exponent all-cell integrated row.** It is exactly the first
far-linear summand of `farSourceCoeff`, with its actual endpoint transport.
The pre-endpoint integral contributes `ratR(v)^(5/2)`. Cond272’s
thirtieth-power margin absorbs this against each of `flowDelta` and `W⁻¹`,
leaving the exact terminal `ratR(v)^(-2)` in the bound. This includes `k=0`. -/
theorem eventually_far_linear_integral_le_strict_exponent_endpoint
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedFarLinear E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        (1 / (mE E).im) * (N : Real) ^ (δ / 8) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
  let theta : Real := δ / 100
  let capC : Real := 3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)
  let alpha : Real :=
    APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
      APrimeGeneralMovingSlotLossSchedule.tauG δ +
      2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ + 2 * theta
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hgap : 0 < δ / 8 - alpha := by
    dsimp [alpha, theta, APrimeGeneralMovingSlotLossSchedule.zetaCtr,
      APrimeGeneralMovingSlotLossSchedule.tauG,
      APrimeGeneralMovingSlotLossSchedule.deltaCap]
    norm_num
    linarith
  have hcapC : 0 < capC := by positivity
  have hconst := eventually_le_rpow (16 * capC / 5) hgap
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im htheta
  have hcfar := eventually_cFar_le hs0 hst ht1 htheta
  have hWgrow := Gauss.Dims.bandwidth_grow
  have hmargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hconst, hxi, hcfar, hWgrow, hmargin, hreg.2,
      B.dim, eventually_ge_atTop 1] with
    N hconstN hxiN hcfarN hWgrowN hmarginN hregN hdim hN
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
  have hFactor := endpoint_flow_factor_le_two hN1 hc hregN hScaleN hWlower
    hRatV1 hR30
  have heta : 0 < (mE E).im := mE_im_pos hE
  have hInt : IntervalIntegrable
      (fun u => normalizedFarLinear E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u)
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
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u ≤
      (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
        (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
          2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
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
    rcases APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall with
      ⟨_, _, hdeltaCapPos, htauGPos, _, _, _, _, _, _, _, _, _⟩
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
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u ≤
      capC * (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
        2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
        (Step2Moment.ratR E s N u) ^ (4 : Nat) := by
      simpa [capC] using hcap
    have hnum :
      (B.ell N u / B.ell N (s N)) *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u ≤
      capC * (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
        2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) := by
      have hratioPart' := ratio_times_cap_integrand_le hE (hs0 N) hu.1 hu1
      calc
        _ ≤ (B.ell N u / B.ell N (s N)) *
            (Step2Moment.ratR E s N u) ^ (-2 : Real) *
              (capC * (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
                (Step2Moment.ratR E s N u) ^ (4 : Nat)) := by
              exact mul_le_mul_of_nonneg_left hcap'
                (mul_nonneg (div_nonneg hEllU.le hEllS.le)
                  (Real.rpow_nonneg hratU.le _))
        _ = capC * (N : Real) ^
              (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
              ((Step2Moment.ratR E s N u) ^ (-2 : Real) *
                (B.ell N u / B.ell N (s N)) *
                (Step2Moment.ratR E s N u) ^ (4 : Nat)) := by ring
        _ ≤ capC * (N : Real) ^
              (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
              (Step2Moment.ratR E s N u) ^ (5 / 2 : Real) :=
                mul_le_mul_of_nonneg_left hratioPart'
                  (by positivity)
        _ = capC * (N : Real) ^
              (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
              (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) := by
                rw [ratR_eq_ratio hE]
    rw [ratR_eq_ratio hE] at hnum
    have hXiPow : Step2.xiK (d.L N) (d.W N) (mE E).im ≤ (N : Real)^theta := hxiN
    have hEtaPos : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hEta0 : 0 ≤ (etaT E u)⁻¹ := (inv_nonneg.mpr hEtaPos.le)
    have hRvInv : 0 ≤ (Step2Moment.ratR E s N v)^(-2 : Real) := by positivity
    have hNv : 0 ≤ (N : Real)^theta := Real.rpow_nonneg hN0.le _
    have hNz : 0 ≤ (N : Real) ^
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) := Real.rpow_nonneg hN0.le _
    have hNg : 0 ≤ (N : Real) ^
        (APrimeGeneralMovingSlotLossSchedule.tauG δ +
          2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) :=
      Real.rpow_nonneg hN0.le _
    have hkernel0 : 0 ≤ (APrimeDriftIntegralBudget.ratio (s N) u) ^
        (5 / 2 : Real) * (etaT E u)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (by rw [← ratR_eq_ratio hE]; exact hratU.le) _) hEta0
    have hinner0 : 0 ≤ (B.ell N u / B.ell N (s N)) *
        (Step2Moment.ratR E s N u)^(-2 : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u := by
      have hcap0 : 0 ≤ APrimeGeneralMovingDriftSource.blockCap E s
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u := by
        unfold APrimeGeneralMovingDriftSource.blockCap
        positivity
      exact mul_nonneg (mul_nonneg (div_nonneg hEllU.le hEllS.le)
        (Real.rpow_nonneg hratU.le _)) hcap0
    rw [ratR_eq_ratio hE] at hinner0
    unfold normalizedFarLinear
    rw [ratR_eq_ratio hE]
    calc
      _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
          (flowDelta d E t N + (B.W N : Real)⁻¹) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) *
          (etaT E u)⁻¹ * Lemma57.cFar (B.W N : Real) (B.ell N u)) *
          ((B.ell N u / B.ell N (s N)) *
            (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-2 : Real) *
            APrimeGeneralMovingDriftSource.blockCap E s
              (APrimeGeneralMovingSlotLossSchedule.tauG δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u) := by
            simp [B, d, band, normalizedFarLinear]
            ring_nf
      _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
          (flowDelta d E t N + (B.W N : Real)⁻¹) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) *
          (etaT E u)⁻¹ * (N : Real)^theta) *
          (capC * (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
            2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
            (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real)) := by
          gcongr
      _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
            2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
          (N : Real)^theta * capC *
          (flowDelta d E t N + (B.W N : Real)⁻¹) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
            (etaT E u)⁻¹) := by ring
  let C : Real := 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
      (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
        2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
      (N : Real)^theta * capC *
      (flowDelta d E t N + (B.W N : Real)⁻¹) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real)
  have hmono := intervalIntegral.integral_mono_on hvIcc.1 hInt
    (hKernelInt.const_mul C) (by
      intro u hu
      simpa [C, mul_assoc] using hpoint u hu)
  have hmonoBound : (∫ u in (s N)..v,
      normalizedFarLinear E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
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
      (16 * capC / 5) / (mE E).im *
        (N : Real)^alpha * (Step2Moment.ratR E s N v)^(-2 : Real) := by
    have hgeom :
      (Step2Moment.ratR E s N v) ^ (5 / 2 : Real) *
      (flowDelta d E t N + (B.W N : Real)⁻¹) ≤ 2 := by
      have hfactor := hFactor
      have hflowEq : flowDelta d E t N =
          (B.scale E N (t N))⁻¹ ^ (1 / 6 : Real) := by rfl
      calc
        _ = Step2Moment.ratR E s N v ^ (5 / 2 : Real) *
            (B.scale E N (t N))⁻¹ ^ (1 / 6 : Real) +
            Step2Moment.ratR E s N v ^ (5 / 2 : Real) / (B.W N : Real) := by
              rw [hflowEq, mul_add]
              simp [div_eq_mul_inv]
        _ ≤ 2 := hfactor
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
        2 * (N : Real)^theta := by
      calc
        _ ≤ (N : Real)^theta * hG := mul_le_mul_of_nonneg_right hxiN (by positivity)
        _ ≤ (N : Real)^theta * 2 :=
          mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hN0.le _)
        _ = 2 * (N : Real)^theta := by ring
    have hpowN :
      (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
        (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
          2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
        (N : Real)^theta * (N : Real)^theta = (N : Real)^alpha := by
      have hza : (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
            2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) =
          (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
            (APrimeGeneralMovingSlotLossSchedule.tauG δ +
              2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ)) := by
        rw [← Real.rpow_add hN0]
      have hthetaPow : (N : Real)^theta * (N : Real)^theta =
          (N : Real)^(theta + theta) := by rw [← Real.rpow_add hN0]
      have hexp : (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
          (APrimeGeneralMovingSlotLossSchedule.tauG δ +
            2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ)) +
          (theta + theta) = alpha := by
        dsimp [alpha, APrimeGeneralMovingSlotLossSchedule.zetaCtr,
          APrimeGeneralMovingSlotLossSchedule.tauG,
          APrimeGeneralMovingSlotLossSchedule.deltaCap, theta]
        ring
      calc
        _ = ((N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
            (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
              2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ)) *
            ((N : Real)^theta * (N : Real)^theta) := by ring
        _ = (N : Real) ^
            (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ +
              (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ)) *
            (N : Real)^(theta + theta) := by rw [hza, hthetaPow]
        _ = (N : Real)^alpha := by rw [← Real.rpow_add hN0, hexp]
    calc
      _ ≤ C * ((APrimeDriftIntegralBudget.ratio (s N) v) ^ (5 / 2 : Real) /
          ((5 / 2 : Real) * (mE E).im)) :=
            mul_le_mul_of_nonneg_left hKernel hC0
      _ = (4 * capC / ((5 / 2 : Real) * (mE E).im)) *
          ((N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
            (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
              2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
            (N : Real)^theta *
            (Step2.xiK (d.L N) (d.W N) (mE E).im * hG)) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
          dsimp [C, hG]
          rw [← ratR_eq_ratio hE]
          ring
      _ ≤ (4 * capC / ((5 / 2 : Real) * (mE E).im)) *
          ((N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
            (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
              2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
            (N : Real)^theta * (2 * (N : Real)^theta)) *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
          gcongr
      _ = (16 * capC / 5) / (mE E).im * (N : Real)^alpha *
          (Step2Moment.ratR E s N v)^(-2 : Real) := by
          calc
            _ = (8 * capC / ((5 / 2 : Real) * (mE E).im)) *
                ((N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
                  (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.tauG δ +
                    2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
                  (N : Real)^theta * (N : Real)^theta) *
                (Step2Moment.ratR E s N v)^(-2 : Real) := by ring
            _ = (16 * capC / 5) / (mE E).im * (N : Real)^alpha *
                (Step2Moment.ratR E s N v)^(-2 : Real) := by
                rw [hpowN]
                ring
  calc
    (∫ u in (s N)..v,
        normalizedFarLinear E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
      C * (∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (5 / 2 : Real) *
          (etaT E u)⁻¹) := hmonoBound
    _ ≤ (16 * capC / 5) / (mE E).im * (N : Real)^alpha *
        (Step2Moment.ratR E s N v)^(-2 : Real) := hCbound
    _ ≤ (1 / (mE E).im) * (N : Real)^(δ / 8) *
        (Step2Moment.ratR E s N v)^(-2 : Real) := by
      have hAbsorb := hconstN
      have hmpos := mE_im_pos hE
      have hNpow : (N : Real)^alpha * (N : Real)^(δ / 8 - alpha) =
          (N : Real)^(δ / 8) := by
        rw [← Real.rpow_add hN0]
        congr 1 <;> ring
      rw [← hNpow]
      calc
        (16 * capC / 5) / (mE E).im * (N : Real)^alpha *
            (Step2Moment.ratR E s N v)^(-2 : Real) =
            (16 * capC / 5) * ((N : Real)^alpha / (mE E).im) *
              (Step2Moment.ratR E s N v)^(-2 : Real) := by ring
        _ ≤ (N : Real)^(δ / 8 - alpha) *
            ((N : Real)^alpha / (mE E).im) *
              (Step2Moment.ratR E s N v)^(-2 : Real) := by
              have hNoverIm : 0 ≤ (N : Real)^alpha / (mE E).im :=
                div_nonneg (Real.rpow_nonneg hN0.le _) (mE_im_pos hE).le
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hAbsorb hNoverIm) hRvInv
        _ = (1 / (mE E).im) *
            ((N : Real)^alpha * (N : Real)^(δ / 8 - alpha)) *
              (Step2Moment.ratR E s N v)^(-2 : Real) := by ring

/-- T995's nondegenerate positive-cell witness, carried alongside this
far-linear estimate so the slot's assumptions are jointly satisfiable. -/
noncomputable abbrev scheduled_positive_cell_witness_for_endpoint :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_far_linear_integral_le_strict_exponent_endpoint
#print axioms scheduled_positive_cell_witness_for_endpoint

end
end RBM.APrimeGeneralMovingFarLinearStrictExponent
