/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFullQV
import RBM1D.Gauss.APrimeRawSourcesGeneralDims
import RBM1D.Gauss.APrimeGoodSetFlowGeneralDims
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.EntryBoundTime

/-!
# T1497 (amend-1): M6 restated with a per-`u` `jS`-cap premise

`RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS` is `docs/reports/T1488-prove.md`'s target
**M6** (`(5.36)` on a high-probability event with the blockwise `J`), restated with an extra
per-`u` implication premise `Step2.jS ... ≤ N^{1/2}`.  This premise is exactly what makes the
`hJcap : jG ≤ N` hypothesis of `RBM.APrimeFullQV.early_raw_full` derivable from the Step-1
hypotheses alone, via `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow`: on its event,
`jG ≤ 1 + N^τ' (9 e^{√3} jS + 2)`, and `jS ≤ N^{1/2}` with `τ' := 1/4` gives `jG ≤ N` eventually
(`1/4 + 1/2 < 1`).

The `SourceEvent` (length-four and length-six loop bounds) is supplied at the shrunk reference
length `RBM.APrimeRawSourcesGeneralDims.sourceEll d s ζ N` and the inflated block bound
`RBM.APrimeRawSourcesGeneralDims.sourceC4 d E s ζ N u`, already built for general `d : Dims` in
`RBM.APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale`.  Since
`sourceC4 d E s ζ N u = N^ζ · EarlyQVRateEv.sDet (band d) E N u ℓ_s` exactly, and `sourceEll`
shrinks `ℓ_s` by exactly the factor `(2 N^ζ)^{-1/5}`, `diagShape'` at the shrunk source is at
most `2 N^ζ` times `diagShape'` at `(ℓ_s, sDet)` (`diagNearRate` scales by the exact factor
`2 N^ζ`; `diagFarRate` is affine in `√Smax` with nonnegative coefficients, hence scales by at
most the same factor).  Choosing `ζ := τ / 2` absorbs this loss into the target's own `N^τ`.
-/

namespace RBM.Gauss.Step2

open Filter MeasureTheory

/-! ### Two deterministic monotonicity facts for `diagShape'` -/

/-- `diagNearRate` scales by the exact factor `2 q` when the reference length shrinks by
`(2 q)^{-1/5}`. -/
private theorem ellSource_ratio_pow5_eq {ℓu ℓs q : ℝ} (hℓs : 0 < ℓs) (hq : 0 < q) :
    (ℓu / (ℓs * (2 * q) ^ (-((1 : ℝ) / 5)))) ^ 5 = (2 * q) * (ℓu / ℓs) ^ 5 := by
  have hb : (0 : ℝ) < 2 * q := by positivity
  have hr : ((2 * q) ^ (-((1 : ℝ) / 5))) ^ 5 = (2 * q)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num [Real.rpow_neg_one]
  rw [div_pow, mul_pow, hr, div_pow]
  field_simp

private theorem diagNearRate_ellSource_eq
    {Ω : Type*} [MeasurableSpace Ω] (Bnd : RBM.Band Ω) (N : ℕ)
    {ℓu ℓs ηu q : ℝ} (hℓs : 0 < ℓs) (hq : 0 < q) :
    RBM.APrimeQVEndpoint.diagNearRate Bnd N ℓu (ℓs * (2 * q) ^ (-((1 : ℝ) / 5))) ηu =
      (2 * q) * RBM.APrimeQVEndpoint.diagNearRate Bnd N ℓu ℓs ηu := by
  unfold RBM.APrimeQVEndpoint.diagNearRate
  rw [ellSource_ratio_pow5_eq hℓs hq]
  ring

/-- `diagFarRate` is at most `2 q` times bigger when `Smax` is scaled by `q ≥ 1`, since it is
affine in `√Smax` with nonnegative coefficients and `√(q S) ≤ q √S` for `q ≥ 1`, `S ≥ 0`. -/
private theorem diagFarRate_le_two_mul_of_Smax_scale
    {Ω : Type*} [MeasurableSpace Ω] (Bnd : RBM.Band Ω) (N : ℕ)
    {ℓu ηu D J Smax q : ℝ} (hW1 : 1 ≤ (Bnd.W N : ℝ)) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hJ : 0 ≤ J) (hSmax : 0 ≤ Smax) (hq : 1 ≤ q) :
    RBM.APrimeQVEndpoint.diagFarRate Bnd N ℓu ηu D J (q * Smax) ≤
      (2 * q) * RBM.APrimeQVEndpoint.diagFarRate Bnd N ℓu ηu D J Smax := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hJ2 : (0 : ℝ) ≤ 2 * J := by linarith
  have hsqrtq : Real.sqrt q ≤ q := by
    have hqq2 : q ≤ q ^ 2 := by nlinarith
    have h := Real.sqrt_le_sqrt hqq2
    rwa [Real.sqrt_sq hq0] at h
  have hsqrt_mul : Real.sqrt (q * Smax) ≤ q * Real.sqrt Smax := by
    rw [Real.sqrt_mul hq0]
    exact mul_le_mul_of_nonneg_right hsqrtq (Real.sqrt_nonneg _)
  have hcfar : 0 ≤ RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu := RBM.Lemma57.cFar2_nonneg hW1 hℓu
  have hc1 : (0 : ℝ) ≤ 2 * ηu⁻¹ * (RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu *
      ((2 * J) ^ 2 * ((Bnd.W N : ℝ) * ℓu * ηu * 2))) := by positivity
  have hc0 : (0 : ℝ) ≤ 2 * ηu⁻¹ * (72 * (2 * J) ^ 3 * ((Bnd.W N : ℝ) * ℓu * ηu)⁻¹)
      + 4 * (Bnd.W N : ℝ) * (Bnd.L N : ℝ) * (Bnd.W N : ℝ) ^ (-D) * (2 * J) ^ 3 := by positivity
  have hexpand : ∀ S : ℝ, RBM.APrimeQVEndpoint.diagFarRate Bnd N ℓu ηu D J S =
      (2 * ηu⁻¹ * (RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu *
          ((2 * J) ^ 2 * ((Bnd.W N : ℝ) * ℓu * ηu * 2)))) * Real.sqrt S +
      (2 * ηu⁻¹ * (72 * (2 * J) ^ 3 * ((Bnd.W N : ℝ) * ℓu * ηu)⁻¹)
        + 4 * (Bnd.W N : ℝ) * (Bnd.L N : ℝ) * (Bnd.W N : ℝ) ^ (-D) * (2 * J) ^ 3) := by
    intro S
    unfold RBM.APrimeQVEndpoint.diagFarRate
    ring
  rw [hexpand, hexpand]
  have hstep : (2 * ηu⁻¹ * (RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu *
        ((2 * J) ^ 2 * ((Bnd.W N : ℝ) * ℓu * ηu * 2)))) * Real.sqrt (q * Smax) ≤
      (2 * ηu⁻¹ * (RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu *
        ((2 * J) ^ 2 * ((Bnd.W N : ℝ) * ℓu * ηu * 2)))) * (q * Real.sqrt Smax) :=
    mul_le_mul_of_nonneg_left hsqrt_mul hc1
  have hqm1 : (0 : ℝ) ≤ q - 1 := by linarith
  have hfin1 : (2 * ηu⁻¹ * (RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu *
        ((2 * J) ^ 2 * ((Bnd.W N : ℝ) * ℓu * ηu * 2)))) * (q * Real.sqrt Smax) ≤
      (2 * q) * ((2 * ηu⁻¹ * (RBM.Lemma57.cFar2 (Bnd.W N : ℝ) ℓu *
        ((2 * J) ^ 2 * ((Bnd.W N : ℝ) * ℓu * ηu * 2)))) * Real.sqrt Smax) := by
    nlinarith [mul_nonneg hc1 (Real.sqrt_nonneg Smax)]
  have hfin0 : (2 * ηu⁻¹ * (72 * (2 * J) ^ 3 * ((Bnd.W N : ℝ) * ℓu * ηu)⁻¹)
        + 4 * (Bnd.W N : ℝ) * (Bnd.L N : ℝ) * (Bnd.W N : ℝ) ^ (-D) * (2 * J) ^ 3) ≤
      (2 * q) * (2 * ηu⁻¹ * (72 * (2 * J) ^ 3 * ((Bnd.W N : ℝ) * ℓu * ηu)⁻¹)
        + 4 * (Bnd.W N : ℝ) * (Bnd.L N : ℝ) * (Bnd.W N : ℝ) ^ (-D) * (2 * J) ^ 3) := by
    nlinarith [mul_nonneg hc0 hqm1]
  nlinarith [hstep.trans hfin1, hfin0]

/-- The full `diagShape'` scales by at most `2 q` when the reference length shrinks by
`(2 q)^{-1/5}` and `Smax` inflates by `q`, for `q ≥ 1`. -/
private theorem diagShape'_shrink_le
    {Ω : Type*} [MeasurableSpace Ω] (Bnd : RBM.Band Ω) (N : ℕ)
    {ℓu ℓs q ηu D J Smax ε : ℝ}
    (hℓs : 0 < ℓs) (hW1 : 1 ≤ (Bnd.W N : ℝ)) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hJ : 0 ≤ J) (hSmax : 0 ≤ Smax) (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (a : RBM.LoopArg (Bnd.L N) (0 + 2)) :
    RBM.APrimeQVEndpoint.diagShape' Bnd N ℓu (ℓs * (2 * q) ^ (-((1 : ℝ) / 5))) ηu D J (q * Smax)
        ε a ≤
      (2 * q) * RBM.APrimeQVEndpoint.diagShape' Bnd N ℓu ℓs ηu D J Smax ε a := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hnear := diagNearRate_ellSource_eq Bnd N (ℓu := ℓu) (ηu := ηu) hℓs hq0
  have hfar := diagFarRate_le_two_mul_of_Smax_scale Bnd N (ℓu := ℓu) (D := D) (J := J)
    hW1 hℓu hηu hJ hSmax hq
  have hAnear0 : 0 ≤ RBM.APrimeQVEndpoint.diagNearRate Bnd N ℓu ℓs ηu := by
    unfold RBM.APrimeQVEndpoint.diagNearRate
    have := RBM.Lemma57.cNear2_nonneg hW1 hℓu
    positivity
  unfold RBM.APrimeQVEndpoint.diagShape'
  rw [hnear]
  set χ : ℝ := (if (RBM.zdist (Bnd.L N) (a 0 - a 1) : ℝ) ≤
      4 * RBM.ellStar (Bnd.W N : ℝ) ℓu then (1 : ℝ) else 0) with hχdef
  have hχ0 : 0 ≤ χ := by rw [hχdef]; split_ifs <;> norm_num
  set T : ℝ := RBM.tailT (Bnd.W N : ℝ) ℓu ηu D (RBM.zdist (Bnd.L N) (a 0 - a 1)) with hTdef
  have hT0 : 0 ≤ T := by
    rw [hTdef]; exact RBM.tailT_nonneg (by positivity) _
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  have hχε : 0 ≤ ε * χ := mul_nonneg hε hχ0
  have hqm1 : 0 ≤ q - 1 := by linarith
  have hstep_near : (2 * q * RBM.APrimeQVEndpoint.diagNearRate Bnd N ℓu ℓs ηu + 2 * ε) * χ *
        T ^ 2 ≤
      (2 * q) * (RBM.APrimeQVEndpoint.diagNearRate Bnd N ℓu ℓs ηu * χ * T ^ 2 +
        2 * ε * χ * T ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg hχε hT2) hqm1, hAnear0, hχ0, hT2, hq]
  have hstep_far : RBM.APrimeQVEndpoint.diagFarRate Bnd N ℓu ηu D J (q * Smax) * T ^ 2 ≤
      (2 * q) * (RBM.APrimeQVEndpoint.diagFarRate Bnd N ℓu ηu D J Smax * T ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hfar hT2]
  nlinarith [hstep_near, hstep_far]

/-! ### Fixed numeric threshold for `hJcap` -/

/-- `1 + N^{1/4} (9 e^{√3} N^{1/2} + 2) ≤ N` eventually: the exponent `1/4 + 1/2 < 1`. -/
private theorem eventually_jcap_bound :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) * (9 * Real.exp (Real.sqrt 3) * (N : ℝ) ^ ((1 : ℝ) / 2) + 2)
        ≤ (N : ℝ) := by
  have hconst := RBM.eventually_le_rpow (3 + 9 * Real.exp (Real.sqrt 3))
    (show (0 : ℝ) < 1 / 8 by norm_num)
  filter_upwards [hconst, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have h34 : (N : ℝ) ^ ((3 : ℝ) / 4) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
  have h14 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) := Real.one_le_rpow hN1' (by norm_num)
  have hmul : (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hexp_pos := Real.exp_pos (Real.sqrt 3)
  have heq : (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((7 : ℝ) / 8) = (N : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hrpow0 : 0 ≤ (N : ℝ) ^ ((7 : ℝ) / 8) := Real.rpow_nonneg hN0.le _
  have hstep : (3 + 9 * Real.exp (Real.sqrt 3)) * (N : ℝ) ^ ((7 : ℝ) / 8) ≤ (N : ℝ) := by
    calc (3 + 9 * Real.exp (Real.sqrt 3)) * (N : ℝ) ^ ((7 : ℝ) / 8)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((7 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right hN hrpow0
      _ = (N : ℝ) := heq
  calc (1 : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) *
        (9 * Real.exp (Real.sqrt 3) * (N : ℝ) ^ ((1 : ℝ) / 2) + 2)
      = 1 + 9 * Real.exp (Real.sqrt 3) * (N : ℝ) ^ ((3 : ℝ) / 4) + 2 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [← hmul]; ring
    _ ≤ (N : ℝ) ^ ((7 : ℝ) / 8) + 9 * Real.exp (Real.sqrt 3) * (N : ℝ) ^ ((7 : ℝ) / 8) +
          2 * (N : ℝ) ^ ((7 : ℝ) / 8) := by
        gcongr
    _ = (3 + 9 * Real.exp (Real.sqrt 3)) * (N : ℝ) ^ ((7 : ℝ) / 8) := by ring
    _ ≤ (N : ℝ) := hstep

/-! ### The main theorem -/

/-- **M6, restated with a per-`u` `jS`-cap premise (T1497, amend-1).** For `d : Dims` under the
Step-1 hypotheses, `∀ τ > 0`, on a high-probability event: for every `u` in the flow window with
`Step2.jS ... ≤ N^{1/2}`, and every two-loop argument `a`, the actual quadratic variation is at
most `N^τ` times `diagShape'` at the blockwise `J`, the deterministic Lemma 5.7 `Smax`
(`EarlyQVRateEv.sDet`), and the explicit `nearEpsilon` remainder. -/
theorem highProb_quadVar_diagShape_of_jS (d : RBM.Gauss.Dims) {E : ℝ} {s t : ℕ → ℝ} {κ c : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : RBM.BoundsCore (RBM.Gauss.sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : RBM.Cond272 (RBM.Gauss.band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (RBM.Gauss.band d).scale E N (t N)) {D : ℝ}
    (hD : 60 ≤ D) :
    ∀ τ : ℝ, 0 < τ →
      RBM.HighProb (RBM.Gauss.P d) (fun N => {ω | ∀ u : RBM.TimeIcc s t N,
        RBM.Step2.jS (RBM.Gauss.sample d) E D N (u : ℝ) ω ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
        ∀ a : RBM.LoopArg (d.L N) 2,
          RBM.Gauss.quadVar (RBM.Gauss.band d).toDims N
              (fun M' => RBM.MomentDuhamel.lkFun (RBM.Gauss.band d) E N (u : ℝ) M'
                RBM.Step2.sigPM a)
              (RBM.Gauss.Hflow d N (u : ℝ) ω) ≤
            (N : ℝ) ^ τ * RBM.APrimeQVEndpoint.diagShape' (RBM.Gauss.band d) N
              ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N))
              (RBM.etaT E (u : ℝ)) D
              (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
                ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D)
              (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
                ((RBM.Gauss.band d).ell N (s N)))
              (RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
                ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
                (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
                  ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D)) a}) := by
  intro τ hτ
  have hE2 : |E| < 2 := by linarith
  have hζpos : 0 < (τ / 2 : ℝ) := by linarith
  -- The four Gaussian source/good/entry inputs, all discharged from the Step-1 hypotheses for
  -- general `d : Dims`.
  have hSource := RBM.APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale d hE2 hs0
    hst ht1 hc0 ⟨hcond, hreg⟩ hB (τ / 2) hζpos
  have hGood := RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow d hE2 hs0 hst ht1 hc0
    ⟨hcond, hreg⟩ hB
  have hEta := RBM.Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE2 ht1 hc0 hreg
  have hDelta := RBM.Gauss.flowDelta_le_rpow_neg d hreg
  have hEntry := RBM.Gauss.entryBoundFlow_floor d hE2 hs0 hst ht1 zero_le_one hEta
    (by linarith : (0 : ℝ) < c / 6) hDelta (by linarith : (0 : ℝ) ≤ D)
  have hJGHP := RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow d hE2 hs0 hst ht1 hcond D
    (by linarith : (0 : ℝ) ≤ D) hEntry hGood (show (0 : ℝ) < (1 / 4 : ℝ) by norm_num)
  -- Deterministic eventual facts.
  have hscaleFacts := RBM.Step1.eventually_scale_facts hE2 hst ht1 hcond hreg
  have hWlarge := (RBM.Gauss.band d).eventually_le_W (Real.exp ((4 * D) ^ 2))
  have hNWfact := RBM.Step2.eventually_le_W_sq (RBM.Gauss.band d)
  have hjcapNum := eventually_jcap_bound
  have h2N : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := RBM.eventually_le_rpow 2 hζpos
  have hHP := hSource.1.inter hJGHP
  refine hHP.mono ?_
  filter_upwards [hSource.2.2.2, hscaleFacts, hEta, hWlarge, hNWfact, d.dim, hjcapNum, h2N,
    eventually_ge_atTop 1] with N hSourceEvN hscaleN hEtaN hWlargeN hNWN hdimN hJcapNumN h2NN hN1
  intro ω hω
  obtain ⟨hωSource, hωJG⟩ := hω
  intro u hjSle a
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  -- Positivity of `ℓu`, `ℓs`.
  have hℓupos : 0 < (RBM.Gauss.band d).ell N (u : ℝ) := by
    have h1 := RBM.one_le_ellHat_of_nonneg ((RBM.Gauss.band d).one_le_L N) hu0 hu1
    have h2 : (1 : ℝ) ≤ (RBM.Gauss.band d).ell N (u : ℝ) := by
      show (1 : ℝ) ≤ RBM.ellHat ((RBM.Gauss.band d).L N) ((u : ℝ) : ℂ); exact h1
    linarith
  have hℓspos : 0 < (RBM.Gauss.band d).ell N (s N) := by
    have h1 := RBM.one_le_ellHat_of_nonneg ((RBM.Gauss.band d).one_le_L N) (hs0 N) hs1
    have h2 : (1 : ℝ) ≤ (RBM.Gauss.band d).ell N (s N) := by
      show (1 : ℝ) ≤ RBM.ellHat ((RBM.Gauss.band d).L N) ((s N : ℝ) : ℂ); exact h1
    linarith
  have hηupos : 0 < RBM.etaT E (u : ℝ) := by
    have := RBM.EEBridge.eeFacts (RBM.Gauss.band d) hE2 hs0 ht1 N u
    linarith [this.2.1]
  have hJnn : 0 ≤ RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
      ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D := by
    have h1 := RBM.APrimeJG.one_le_jG (RBM.Gauss.sample d) E N (u : ℝ) ω
      (ℓu := (RBM.Gauss.band d).ell N (u : ℝ)) (ηu := RBM.etaT E (u : ℝ)) (D := D)
      (show (0 : ℝ) < ((RBM.Gauss.band d).W N : ℝ) by exact_mod_cast (RBM.Gauss.band d).W_pos N)
    linarith
  -- Deterministic side conditions of `early_raw_full`.
  have hW : Real.exp 1 ≤ ((RBM.Gauss.band d).W N : ℝ) := by
    have h1 : Real.exp 1 ≤ Real.exp ((4 * D) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (4 * D)])
    exact h1.trans hWlargeN
  have hlog : (4 * D) ^ 2 ≤ Real.log ((RBM.Gauss.band d).W N : ℝ) := by
    have h1 := Real.log_le_log (Real.exp_pos ((4 * D) ^ 2)) hWlargeN
    rwa [Real.log_exp] at h1
  have hlog4 : (4 : ℝ) ≤ Real.log ((RBM.Gauss.band d).W N : ℝ) := by
    have h1 : (4 : ℝ) ≤ (4 * D) ^ 2 := by nlinarith [hD, sq_nonneg (D - 60)]
    linarith [hlog]
  have heta : (N : ℝ)⁻¹ ≤ RBM.etaT E (u : ℝ) := by
    have h1 : RBM.etaT E (t N) ≤ RBM.etaT E (u : ℝ) := RBM.Gauss.etaT_le_of_le hE2 u.2.2
    have h2 := hEtaN.trans h1
    simpa only [Real.rpow_neg_one] using h2
  have hA : 1 ≤ (RBM.Gauss.band d).scale E N (u : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
    exact h1.trans (hscaleN u).1
  have hAN : (RBM.Gauss.band d).scale E N (u : ℝ) ≤ (N : ℝ) := by
    obtain ⟨_, _, heta1, _, hellL⟩ := RBM.EEBridge.eeFacts (RBM.Gauss.band d) hE2 hs0 ht1 N u
    have hWLcast : ((RBM.Gauss.band d).W N : ℝ) * ((RBM.Gauss.band d).L N : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hdimN.1
    have hWnn : (0 : ℝ) ≤ ((RBM.Gauss.band d).W N : ℝ) := by positivity
    have hℓnn : (0 : ℝ) ≤ (RBM.Gauss.band d).ell N (u : ℝ) := hℓupos.le
    show ((RBM.Gauss.band d).W N : ℝ) * (RBM.Gauss.band d).ell N (u : ℝ) * RBM.etaT E (u : ℝ) ≤
        (N : ℝ)
    calc ((RBM.Gauss.band d).W N : ℝ) * (RBM.Gauss.band d).ell N (u : ℝ) * RBM.etaT E (u : ℝ)
        ≤ ((RBM.Gauss.band d).W N : ℝ) * ((RBM.Gauss.band d).L N : ℝ) * 1 := by
          have h1 : (RBM.Gauss.band d).ell N (u : ℝ) * RBM.etaT E (u : ℝ) ≤
              ((RBM.Gauss.band d).L N : ℝ) * 1 := by
            have := mul_le_mul hellL heta1 (RBM.EEBridge.eeFacts (RBM.Gauss.band d) hE2 hs0 ht1 N
              u).2.1.le (by positivity)
            simpa using this
          nlinarith [hWnn, h1]
      _ = ((RBM.Gauss.band d).W N : ℝ) * ((RBM.Gauss.band d).L N : ℝ) := by ring
      _ ≤ (N : ℝ) := hWLcast
  have hWL : ((RBM.Gauss.band d).W N : ℝ) * ((RBM.Gauss.band d).L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdimN.1
  have hNW : (N : ℝ) ≤ ((RBM.Gauss.band d).W N : ℝ) ^ 2 := hNWN
  -- `hJcap`, from the per-`u` `jS ≤ N^{1/2}` premise.
  have hjG1 := hωJG u
  have hjSbound : (9 * Real.exp (Real.sqrt 3)) *
      RBM.Step2.jS (RBM.Gauss.sample d) E D N (u : ℝ) ω + 2 ≤
      9 * Real.exp (Real.sqrt 3) * (N : ℝ) ^ ((1 : ℝ) / 2) + 2 := by
    gcongr
  have hjcapStep : (1 : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) *
      (9 * Real.exp (Real.sqrt 3) * RBM.Step2.jS (RBM.Gauss.sample d) E D N (u : ℝ) ω + 2) ≤
      (1 : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) *
        (9 * Real.exp (Real.sqrt 3) * (N : ℝ) ^ ((1 : ℝ) / 2) + 2) := by
    gcongr
  have hJcap : RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
      ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D ≤ (N : ℝ) :=
    hjG1.trans (hjcapStep.trans hJcapNumN)
  -- The `SourceEvent`, at the shrunk reference length.
  have hsource := (hSourceEvN ω hωSource u).1
  have hℓpos : 0 < RBM.APrimeRawSourcesGeneralDims.sourceEll d s (τ / 2) N := by
    unfold RBM.APrimeRawSourcesGeneralDims.sourceEll
    positivity
  have hraw := RBM.APrimeFullQV.early_raw_full (RBM.Gauss.sample d) hE2 hu0 hu1 N ω a hsource
    hℓpos hD hW hlog4 hlog hN1' heta hA hAN hWL hNW hJcap
  have hEllEq : RBM.APrimeRawSourcesGeneralDims.sourceEll d s (τ / 2) N =
      (RBM.Gauss.band d).ell N (s N) * (2 * (N : ℝ) ^ (τ / 2)) ^ (-((1 : ℝ) / 5)) := rfl
  have hC4eq : RBM.APrimeRawSourcesGeneralDims.sourceC4 d E s (τ / 2) N (u : ℝ) =
      (N : ℝ) ^ (τ / 2) * RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
        ((RBM.Gauss.band d).ell N (s N)) := by
    unfold RBM.APrimeRawSourcesGeneralDims.sourceC4 RBM.EarlyQVRateEv.sDet
    ring
  rw [hEllEq, hC4eq] at hraw
  have hqge1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' hζpos.le
  have hSDetnn : 0 ≤ RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
      ((RBM.Gauss.band d).ell N (s N)) := RBM.EarlyQVRateEv.sDet_nonneg (RBM.Gauss.band d) E N hu0
    hu1 hℓspos
  have hεnn : 0 ≤ RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
      ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
      (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
        (RBM.etaT E (u : ℝ)) D) := by
    unfold RBM.EEDef.nearEpsilon; positivity
  have hW1 : 1 ≤ ((RBM.Gauss.band d).W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hW
  have hshrink := diagShape'_shrink_le (RBM.Gauss.band d) N (ℓu := (RBM.Gauss.band d).ell N
      (u : ℝ)) (ℓs := (RBM.Gauss.band d).ell N (s N)) (q := (N : ℝ) ^ (τ / 2))
    (ηu := RBM.etaT E (u : ℝ)) (D := D)
    (J := RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
      (RBM.etaT E (u : ℝ)) D)
    (Smax := RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
      ((RBM.Gauss.band d).ell N (s N)))
    (ε := RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
      ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
      (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
        (RBM.etaT E (u : ℝ)) D))
    hℓspos hW1 hℓupos hηupos hJnn hSDetnn hεnn hqge1 a
  have hcomb := hraw.1.trans hshrink
  -- The `diagShape'` at the un-shrunk source, nonnegative.
  have hshape0 : 0 ≤ RBM.APrimeQVEndpoint.diagShape' (RBM.Gauss.band d) N
      ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N)) (RBM.etaT E (u : ℝ)) D
      (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
        (RBM.etaT E (u : ℝ)) D)
      (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ) ((RBM.Gauss.band d).ell N (s N)))
      (RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
        ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
        (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D)) a := by
    have hAnear0 : 0 ≤ RBM.APrimeQVEndpoint.diagNearRate (RBM.Gauss.band d) N
        ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N))
        (RBM.etaT E (u : ℝ)) := by
      unfold RBM.APrimeQVEndpoint.diagNearRate
      have := RBM.Lemma57.cNear2_nonneg hW1 hℓupos
      positivity
    have hAfar0 : 0 ≤ RBM.APrimeQVEndpoint.diagFarRate (RBM.Gauss.band d) N
        ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
        (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D)
        (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
          ((RBM.Gauss.band d).ell N (s N))) := by
      unfold RBM.APrimeQVEndpoint.diagFarRate
      have hc1 := RBM.Lemma57.cFar2_nonneg hW1 hℓupos
      have hJ2 : (0 : ℝ) ≤ 2 * RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
          ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D := by linarith [hJnn]
      positivity
    have hχ0 : 0 ≤ (if (RBM.zdist ((RBM.Gauss.band d).L N) (a 0 - a 1) : ℝ) ≤
        4 * RBM.ellStar ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).ell N (u : ℝ))
        then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hT0 : 0 ≤ RBM.tailT ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).ell N (u : ℝ))
        (RBM.etaT E (u : ℝ)) D (RBM.zdist ((RBM.Gauss.band d).L N) (a 0 - a 1)) :=
      RBM.tailT_nonneg (by positivity) _
    have hT2 : 0 ≤ (RBM.tailT ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).ell N (u : ℝ))
        (RBM.etaT E (u : ℝ)) D (RBM.zdist ((RBM.Gauss.band d).L N) (a 0 - a 1))) ^ 2 :=
      sq_nonneg _
    have hsum : (0 : ℝ) ≤ RBM.APrimeQVEndpoint.diagNearRate (RBM.Gauss.band d) N
        ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N)) (RBM.etaT E (u : ℝ)) +
        2 * RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
          ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
          (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
            (RBM.etaT E (u : ℝ)) D) := by linarith [hAnear0, hεnn]
    have hterm1 : (0 : ℝ) ≤ (RBM.APrimeQVEndpoint.diagNearRate (RBM.Gauss.band d) N
          ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N)) (RBM.etaT E (u : ℝ)) +
          2 * RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
            ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
            (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
              ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D)) *
        (if (RBM.zdist ((RBM.Gauss.band d).L N) (a 0 - a 1) : ℝ) ≤
            4 * RBM.ellStar ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).ell N (u : ℝ))
            then (1 : ℝ) else 0) *
        (RBM.tailT ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D (RBM.zdist ((RBM.Gauss.band d).L N) (a 0 - a 1))) ^ 2 :=
      mul_nonneg (mul_nonneg hsum hχ0) hT2
    have hterm2 : (0 : ℝ) ≤ RBM.APrimeQVEndpoint.diagFarRate (RBM.Gauss.band d) N
        ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
        (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D)
        (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
          ((RBM.Gauss.band d).ell N (s N))) *
        (RBM.tailT ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D (RBM.zdist ((RBM.Gauss.band d).L N) (a 0 - a 1))) ^ 2 :=
      mul_nonneg hAfar0 hT2
    unfold RBM.APrimeQVEndpoint.diagShape'
    exact add_nonneg hterm1 hterm2
  have hpow : 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
    have heqpow : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_right h2NN (Real.rpow_nonneg hN0.le (τ / 2))
      _ = (N : ℝ) ^ τ := heqpow
  calc RBM.Gauss.quadVar (RBM.Gauss.band d).toDims N
        (fun M' => RBM.MomentDuhamel.lkFun (RBM.Gauss.band d) E N (u : ℝ) M' RBM.Step2.sigPM a)
        (RBM.Gauss.Hflow d N (u : ℝ) ω)
      = RBM.Gauss.quadVar (RBM.Gauss.band d).toDims N
        (fun M' => RBM.MomentDuhamel.lkFun (RBM.Gauss.band d) E N (u : ℝ) M' RBM.Step2.sigPM a)
        ((RBM.Gauss.sample d).H N (u : ℝ) ω) := by rw [RBM.Gauss.sample_H]
    _ ≤ (2 * (N : ℝ) ^ (τ / 2)) * RBM.APrimeQVEndpoint.diagShape' (RBM.Gauss.band d) N
        ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N))
        (RBM.etaT E (u : ℝ)) D
        (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D)
        (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
          ((RBM.Gauss.band d).ell N (s N)))
        (RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
          ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
          (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
            (RBM.etaT E (u : ℝ)) D)) a := hcomb
    _ ≤ (N : ℝ) ^ τ * RBM.APrimeQVEndpoint.diagShape' (RBM.Gauss.band d) N
        ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N))
        (RBM.etaT E (u : ℝ)) D
        (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
          (RBM.etaT E (u : ℝ)) D)
        (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
          ((RBM.Gauss.band d).ell N (s N)))
        (RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
          ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
          (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω ((RBM.Gauss.band d).ell N (u : ℝ))
            (RBM.etaT E (u : ℝ)) D)) a :=
      mul_le_mul_of_nonneg_right hpow hshape0

/-- Convenience corollary (T2): any envelope `Θ N ≤ N^{1/2}` eventually also works as the
per-`u` `jS`-cap premise. -/
theorem highProb_quadVar_diagShape_of_jS_le (d : RBM.Gauss.Dims) {E : ℝ} {s t : ℕ → ℝ} {κ c : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : RBM.BoundsCore (RBM.Gauss.sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : RBM.Cond272 (RBM.Gauss.band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (RBM.Gauss.band d).scale E N (t N)) {D : ℝ}
    (hD : 60 ≤ D) {Θ : ℕ → ℝ} (hΘ : ∀ᶠ N : ℕ in atTop, Θ N ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) :
    ∀ τ : ℝ, 0 < τ →
      RBM.HighProb (RBM.Gauss.P d) (fun N => {ω | ∀ u : RBM.TimeIcc s t N,
        RBM.Step2.jS (RBM.Gauss.sample d) E D N (u : ℝ) ω ≤ Θ N →
        ∀ a : RBM.LoopArg (d.L N) 2,
          RBM.Gauss.quadVar (RBM.Gauss.band d).toDims N
              (fun M' => RBM.MomentDuhamel.lkFun (RBM.Gauss.band d) E N (u : ℝ) M'
                RBM.Step2.sigPM a)
              (RBM.Gauss.Hflow d N (u : ℝ) ω) ≤
            (N : ℝ) ^ τ * RBM.APrimeQVEndpoint.diagShape' (RBM.Gauss.band d) N
              ((RBM.Gauss.band d).ell N (u : ℝ)) ((RBM.Gauss.band d).ell N (s N))
              (RBM.etaT E (u : ℝ)) D
              (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
                ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D)
              (RBM.EarlyQVRateEv.sDet (RBM.Gauss.band d) E N (u : ℝ)
                ((RBM.Gauss.band d).ell N (s N)))
              (RBM.EEDef.nearEpsilon ((RBM.Gauss.band d).W N : ℝ) ((RBM.Gauss.band d).L N : ℝ)
                ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D
                (RBM.APrimeJG.jG (RBM.Gauss.sample d) E N (u : ℝ) ω
                  ((RBM.Gauss.band d).ell N (u : ℝ)) (RBM.etaT E (u : ℝ)) D)) a}) := by
  intro τ hτ
  have hmain := highProb_quadVar_diagShape_of_jS d hκ hE hB hs0 hst ht1 hcond hc0 hreg hD τ hτ
  refine hmain.mono ?_
  filter_upwards [hΘ] with N hΘN ω hω u hjSle a
  exact hω u (hjSle.trans hΘN) a

end RBM.Gauss.Step2
