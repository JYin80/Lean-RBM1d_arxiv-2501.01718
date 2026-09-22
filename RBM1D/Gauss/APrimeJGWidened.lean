/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeJGModel
import RBM1D.Gauss.APrimeExponents

/-!
# T293: budget with the actual block-level Green control

The widened level is used only on the common (4.2)/good event and the calibrated
soft-weight support. Nonemptiness of that intersection belongs to T295.
-/

namespace RBM.APrimeJGWidened

open Filter Real

noncomputable def level (n τ Λ : ℝ) : ℝ :=
  1 + n ^ τ * (APrimeJGModel.entryFactor * StepSideAPrime.cWt * Λ + 2)

noncomputable def levelConst : ℝ :=
  APrimeJGModel.entryFactor * StepSideAPrime.cWt + 3

theorem levelConst_pos : 0 < levelConst := by
  unfold levelConst
  have hA := APrimeJGModel.entryFactor_pos
  have hC := StepSideAPrime.cWt_pos
  nlinarith [mul_pos hA hC]

/-- The event-level output of T286 remains polynomial once `Λ` is. -/
theorem level_le_monomial {n τ Λ : ℝ} (hn : 1 ≤ n) (hτ : 0 ≤ τ) (hΛ : 1 ≤ Λ) :
    level n τ Λ ≤ levelConst * n ^ τ * Λ := by
  have hx : 1 ≤ n ^ τ := Real.one_le_rpow hn hτ
  have hx0 : 0 ≤ n ^ τ := by positivity
  have hA : 0 ≤ APrimeJGModel.entryFactor * StepSideAPrime.cWt := by
    exact mul_nonneg APrimeJGModel.entryFactor_pos.le StepSideAPrime.cWt_pos.le
  have h1 : 1 ≤ n ^ τ * Λ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hΛ)]
  have h2 : 2 * n ^ τ ≤ 2 * n ^ τ * Λ := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hΛ)]
  unfold level levelConst
  nlinarith

/-- On the actual common event, the block maximum `jG` has exactly the widened
level. The two premises are the conclusions of T280f's (4.2) event producer and
T269's soft-weight support bound, respectively. -/
theorem jG_le_level_of_common_event (d : Gauss.Dims) (E D : ℝ)
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) {τ Λ : ℝ}
    (hprior : Step2.jS (Gauss.sample d) E D N u ω ≤ StepSideAPrime.cWt * Λ)
    (hentry : APrimeJG.jG (Gauss.sample d) E N u ω
        ((Gauss.band d).ell N u) (etaT E u) D ≤
      1 + (N : ℝ) ^ τ *
        (APrimeJGModel.entryFactor * Step2.jS (Gauss.sample d) E D N u ω + 2)) :
    APrimeJG.jG (Gauss.sample d) E N u ω
      ((Gauss.band d).ell N u) (etaT E u) D ≤ level (N : ℝ) τ Λ := by
  have h := APrimeJGModel.jG_le_relaxed_of_prior
    (q := (N : ℝ) ^ τ) (by positivity) hprior hentry
  simpa [level, mul_assoc] using h

/-- A polynomial prior level gives the polynomial cap required by T280g's
`nearEpsilon_le_inv`. The constant is absorbed after the exponent is fixed. -/
theorem eventually_level_le_pow {τ a : ℝ} (hτ : 0 ≤ τ) (_ha : 0 ≤ a)
    {Λ : ℕ → ℝ} (hΛ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Λ N)
    (hΛa : ∀ᶠ N : ℕ in atTop, Λ N ≤ (N : ℝ) ^ a) :
    ∀ᶠ N : ℕ in atTop,
      level (N : ℝ) τ (Λ N) ≤ (N : ℝ) ^ (a + τ + 1) := by
  filter_upwards [hΛ1, hΛa, eventually_ge_atTop 1,
    eventually_le_rpow levelConst one_pos] with N hΛN hΛpow hN hCN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hx0 : 0 ≤ (N : ℝ) ^ τ := by positivity
  have hC0 : 0 ≤ levelConst := levelConst_pos.le
  calc
    level (N : ℝ) τ (Λ N)
        ≤ levelConst * (N : ℝ) ^ τ * Λ N := level_le_monomial hn hτ hΛN
    _ ≤ levelConst * (N : ℝ) ^ τ * (N : ℝ) ^ a :=
      mul_le_mul_of_nonneg_left hΛpow (mul_nonneg hC0 hx0)
    _ ≤ (N : ℝ) * (N : ℝ) ^ τ * (N : ℝ) ^ a := by
      rw [Real.rpow_one] at hCN
      gcongr
    _ = (N : ℝ) ^ (a + τ + 1) := by
      calc
        (N : ℝ) * (N : ℝ) ^ τ * (N : ℝ) ^ a
            = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ τ * (N : ℝ) ^ a := by
              rw [Real.rpow_one]
        _ = (N : ℝ) ^ (1 + τ + a) := by
              rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
        _ = (N : ℝ) ^ (a + τ + 1) := by ring

/-- Polynomial endpoint control makes `Λ=N^(2δ)R⁴` polynomial. -/
theorem priorLevel_le_pow {n δ K R : ℝ} (hn : 1 ≤ n)
    (_hδ : 0 ≤ δ) (_hK : 0 ≤ K) (hR1 : 1 ≤ R) (hR : R ≤ n ^ K) :
    n ^ (2 * δ) * R ^ 4 ≤ n ^ (2 * δ + 4 * K) := by
  have hn0 : 0 < n := by linarith
  have hR4 : R ^ 4 ≤ (n ^ K) ^ 4 := pow_le_pow_left₀ (by linarith) hR 4
  have hp : (n ^ K) ^ 4 = n ^ (4 * K) := by
    rw [show 4 * K = K * 4 by ring, Real.rpow_mul hn0.le]
    norm_num [Real.rpow_natCast]
  calc
    n ^ (2 * δ) * R ^ 4 ≤ n ^ (2 * δ) * (n ^ K) ^ 4 :=
      mul_le_mul_of_nonneg_left hR4 (by positivity)
    _ = n ^ (2 * δ) * n ^ (4 * K) := by rw [hp]
    _ = n ^ (2 * δ + 4 * K) := (Real.rpow_add hn0 _ _).symm

/-- The particular widened block level has the polynomial cap used by
`APrimeNearRem.nearEpsilon_le_inv`; `D` may be chosen after this exponent. -/
theorem eventually_widened_level_poly {δ τ K : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hK : 0 ≤ K) {R : ℕ → ℝ}
    (hR1 : ∀ᶠ N : ℕ in atTop, 1 ≤ R N)
    (hR : ∀ᶠ N : ℕ in atTop, R N ≤ (N : ℝ) ^ K) :
    ∀ᶠ N : ℕ in atTop,
      level (N : ℝ) τ ((N : ℝ) ^ (2 * δ) * R N ^ 4) ≤
        (N : ℝ) ^ (2 * δ + 4 * K + τ + 1) := by
  have hΛ1 : ∀ᶠ N : ℕ in atTop,
      1 ≤ (N : ℝ) ^ (2 * δ) * R N ^ 4 := by
    filter_upwards [hR1, eventually_ge_atTop 1] with N hRN hN
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpow : 1 ≤ (N : ℝ) ^ (2 * δ) :=
      Real.one_le_rpow hn (by linarith)
    nlinarith [show (1 : ℝ) ≤ R N ^ 4 from one_le_pow₀ hRN]
  have hΛpoly : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * δ) * R N ^ 4 ≤ (N : ℝ) ^ (2 * δ + 4 * K) := by
    filter_upwards [hR1, hR, eventually_ge_atTop 1] with N hRN hRpow hN
    exact priorLevel_le_pow (by exact_mod_cast hN) hδ hK hRN hRpow
  exact eventually_level_le_pow hτ (by linarith) hΛ1 hΛpoly

/-- Model-level polynomial `jG` cap on whatever common calibrated-support event
T295 produces. This theorem makes no claim that the event is inhabited. -/
theorem eventually_jG_le_poly_on_common_event (d : Gauss.Dims) (E D : ℝ)
    {s t : ℕ → ℝ} {Good : ℕ → Set (Gauss.Ω d)}
    {δ τ K : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    {R : ℕ → ℝ}
    (hR1 : ∀ᶠ N : ℕ in atTop, 1 ≤ R N)
    (hR : ∀ᶠ N : ℕ in atTop, R N ≤ (N : ℝ) ^ K)
    (hprior : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N,
      ∀ u : TimeIcc s t N,
        Step2.jS (Gauss.sample d) E D N (u : ℝ) ω ≤
          StepSideAPrime.cWt * ((N : ℝ) ^ (2 * δ) * R N ^ 4))
    (hentry : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N,
      ∀ u : TimeIcc s t N,
        APrimeJG.jG (Gauss.sample d) E N (u : ℝ) ω
          ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D ≤
          1 + (N : ℝ) ^ τ *
            (APrimeJGModel.entryFactor *
              Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2)) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N, ∀ u : TimeIcc s t N,
      APrimeJG.jG (Gauss.sample d) E N (u : ℝ) ω
        ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D ≤
        (N : ℝ) ^ (2 * δ + 4 * K + τ + 1) := by
  filter_upwards [hprior, hentry,
    eventually_widened_level_poly hδ hτ hK hR1 hR]
    with N hp he hcap ω hω u
  exact (jG_le_level_of_common_event d E D N (u : ℝ) ω (hp ω hω u)
    (he ω hω u)).trans hcap

/-- T280g's near remainder accepts the widened level once the polynomial
cap has fixed `k`; the decay order `D` is then chosen after `k`. -/
theorem nearEpsilon_le_inv_of_widened_level
    {W L ℓu ηu D J N k τ Λ : ℝ}
    (hW : Real.exp 1 ≤ W) (hL : 0 < L) (hℓu : 0 < ℓu)
    (hηu : 0 < ηu) (hN : 1 ≤ N) (hk : 0 ≤ k)
    (hJ0 : 0 ≤ J) (hD : 2 * k + 14 ≤ D)
    (hη : N⁻¹ ≤ ηu) (hA : 1 ≤ W * ℓu * ηu)
    (hAN : W * ℓu * ηu ≤ N) (hWL : W * L ≤ N)
    (hNW : N ≤ W ^ 2) (hJ : J ≤ level N τ Λ)
    (hlevel : level N τ Λ ≤ N ^ k)
    (hlog4 : 4 ≤ Real.log W)
    (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    EEDef.nearEpsilon W L ℓu ηu D J ≤ W⁻¹ := by
  exact EEDef.nearEpsilon_le_inv hW hL hℓu hηu hN hk hJ0 hD
    hη hA hAN hWL hNW (hJ.trans hlevel) hlog4 hlog

/-- The block-level far rate in T280g is monotone in the running `J`. -/
theorem diagFarRate_mono {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    {N : ℕ} {ℓu ηu D Smax J J' : ℝ}
    (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hJ0 : 0 ≤ J) (hJJ' : J ≤ J') :
    APrimeQVEndpoint.diagFarRate B N ℓu ηu D J Smax ≤
      APrimeQVEndpoint.diagFarRate B N ℓu ηu D J' Smax := by
  have hcf : 0 ≤ Lemma57.cFar2 (B.W N : ℝ) ℓu :=
    Lemma57.cFar2_nonneg hW hℓu
  have hA : 0 < (B.W N : ℝ) * ℓu * ηu := by positivity
  have hWD : 0 ≤ (B.W N : ℝ) ^ (-D) := by positivity
  have hL : 0 ≤ (B.L N : ℝ) := by positivity
  unfold APrimeQVEndpoint.diagFarRate
  gcongr

/-- Exact polynomial replacement of the running level in the T280g far rate.
Its quadratic and cubic summands now carry `N^(2τ)` and `N^(3τ)`. -/
theorem diagFarRate_le_widened_poly {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    {N : ℕ} {ℓu ηu D Smax J τ Λ : ℝ}
    (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hN : 1 ≤ (N : ℝ)) (hτ : 0 ≤ τ) (hΛ : 1 ≤ Λ)
    (hJ0 : 0 ≤ J) (hJ : J ≤ level (N : ℝ) τ Λ) :
    APrimeQVEndpoint.diagFarRate B N ℓu ηu D J Smax ≤
      APrimeQVEndpoint.diagFarRate B N ℓu ηu D
        (levelConst * (N : ℝ) ^ τ * Λ) Smax := by
  exact diagFarRate_mono hW hℓu hηu hJ0
    (hJ.trans (level_le_monomial hN hτ hΛ))

/-- The two far-rate powers after replacing `J` by the widened polynomial cap.
The cubic tail and the cubic inverse-scale row pay the same `3τ`. -/
theorem diagFarRate_widened_poly_eq {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    {N : ℕ} {ℓu ηu D Smax τ Λ : ℝ} (hN : 1 ≤ (N : ℝ)) :
    APrimeQVEndpoint.diagFarRate B N ℓu ηu D
        (levelConst * (N : ℝ) ^ τ * Λ) Smax =
      2 * ηu⁻¹ *
        (Lemma57.cFar2 (B.W N : ℝ) ℓu *
            (4 * levelConst ^ 2 * (N : ℝ) ^ (2 * τ) * Λ ^ 2 *
              ((B.W N : ℝ) * ℓu * ηu * (2 * Real.sqrt Smax))) +
          576 * levelConst ^ 3 * (N : ℝ) ^ (3 * τ) * Λ ^ 3 *
            ((B.W N : ℝ) * ℓu * ηu)⁻¹) +
        32 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) *
          levelConst ^ 3 * (N : ℝ) ^ (3 * τ) * Λ ^ 3 := by
  have hn0 : (0 : ℝ) < N := by linarith
  have h2 : (N : ℝ) ^ (2 * τ) = ((N : ℝ) ^ τ) ^ 2 := by
    rw [show 2 * τ = τ * 2 by ring, Real.rpow_mul hn0.le]
    norm_num [Real.rpow_natCast]
  have h3 : (N : ℝ) ^ (3 * τ) = ((N : ℝ) ^ τ) ^ 3 := by
    rw [show 3 * τ = τ * 3 by ring, Real.rpow_mul hn0.le]
    norm_num [Real.rpow_natCast]
  rw [h2, h3]
  unfold APrimeQVEndpoint.diagFarRate
  ring

/-- The widened running level gives the exact QBd analogue; the old
`APrimePrior.QBd` is deliberately not reused with a false `J≤cWt Λ`. -/
noncomputable def QBdWide (n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε : ℝ) : ℝ :=
  APrimePrior.qvShape Wr ℓu ℓs ηu D (level n τ Λ) Smax 0 Lr Tu /
      (Tt * R ^ 4) ^ 2 + 2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2

noncomputable def QBdWidePoly (n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε : ℝ) : ℝ :=
  APrimePrior.qvShape Wr ℓu ℓs ηu D (levelConst * n ^ τ * Λ) Smax 0 Lr Tu /
      (Tt * R ^ 4) ^ 2 + 2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2

/-- All three far pieces of the corrected QBd: one quadratic term and two
cubic terms. The near and epsilon pieces do not acquire an `N^τ` loss. -/
theorem QBdWidePoly_eq {n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε : ℝ}
    (hn : 1 ≤ n) :
    QBdWidePoly n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε =
      (2 * (ηu⁻¹ *
        (Lemma57.cNear2 Wr ℓu * (ℓu / ℓs) ^ 5 +
          Lemma57.cFar2 Wr ℓu *
            (4 * levelConst ^ 2 * n ^ (2 * τ) * Λ ^ 2 *
              (Wr * ℓu * ηu * (2 * Real.sqrt Smax))) +
          576 * levelConst ^ 3 * n ^ (3 * τ) * Λ ^ 3 *
            (Wr * ℓu * ηu)⁻¹) * Tu ^ 2 +
        16 * Wr * Lr * Wr ^ (-D) * levelConst ^ 3 *
          n ^ (3 * τ) * Λ ^ 3 * Tu ^ 2)) /
          (Tt * R ^ 4) ^ 2 +
        2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have h2 : n ^ (2 * τ) = (n ^ τ) ^ 2 := by
    rw [show 2 * τ = τ * 2 by ring, Real.rpow_mul hn0.le]
    norm_num [Real.rpow_natCast]
  have h3 : n ^ (3 * τ) = (n ^ τ) ^ 3 := by
    rw [show 3 * τ = τ * 3 by ring, Real.rpow_mul hn0.le]
    norm_num [Real.rpow_natCast]
  rw [h2, h3]
  unfold QBdWidePoly APrimePrior.qvShape
  ring

/-- The corrected QBd envelope has the same polynomial replacement as the
T280g far rate, without assuming the rejected `J≤cWt Λ`. -/
theorem QBdWide_le_poly {n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε : ℝ}
    (hn : 1 ≤ n) (hτ : 0 ≤ τ) (hΛ : 1 ≤ Λ)
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hL : 0 ≤ Lr)
    (hden : 0 < (Tt * R ^ 4) ^ 2) :
    QBdWide n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε ≤
      QBdWidePoly n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε := by
  unfold QBdWide QBdWidePoly
  gcongr
  · have hA : 0 ≤ APrimeJGModel.entryFactor * StepSideAPrime.cWt * Λ := by
      exact mul_nonneg
        (mul_nonneg APrimeJGModel.entryFactor_pos.le StepSideAPrime.cWt_pos.le)
        (by linarith)
    have hJ0 : 0 ≤ level n τ Λ := by
      unfold level
      positivity
    exact APrimePrior.qvShape_mono hW hℓu hηu hL hJ0
      (level_le_monomial hn hτ hΛ)

theorem QBdWide_le_of_shape {n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε J Q : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hL : 0 ≤ Lr)
    (hJ0 : 0 ≤ J) (hJ : J ≤ level n τ Λ)
    (hden : 0 < (Tt * R ^ 4) ^ 2)
    (hQ : Q ≤ APrimePrior.qvShape Wr ℓu ℓs ηu D J Smax 0 Lr Tu) :
    Q / (Tt * R ^ 4) ^ 2 + 2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2
      ≤ QBdWide n τ Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε := by
  unfold QBdWide
  gcongr
  exact hQ.trans (APrimePrior.qvShape_mono hW hℓu hηu hL hJ0 hJ)

/-- The two inverse-scale far rows retain strict margin at the selectable
`δ₀=c/20` when the stochastic exponent is chosen after `δ`. The quadratic
row is squared after `Smax`, hence its extra `4τ`; the cubic row pays `3τ`. -/
theorem widened_far_rows_budget {c δ τ : ℝ} (hc : 0 < c)
    (_hδ : 0 ≤ δ) (hδ0 : δ ≤ c / 20) (_hτ : 0 ≤ τ) (hτδ : τ ≤ δ / 16) :
    8 * δ + 4 * τ < c * (1 - ((23 / 2 : ℝ) / 30)) ∧
      6 * δ + 3 * τ < c * (1 - (9 : ℝ) / 30) := by
  constructor <;> norm_num <;> linarith

/-- Quantitative slack under the actual separate-scale `(2.72)` interpolation.
The quadratic coefficient is squared in the later budget, so it pays `4τ`. -/
theorem widened_far_rows_slack {c δ τ : ℝ} (_hc : 0 < c)
    (_hδ : 0 ≤ δ) (hδ0 : δ ≤ c / 20)
    (_hτ : 0 ≤ τ) (hτδ : τ ≤ δ / 16) :
    (49 / 240 : ℝ) * c ≤ c * (1 - ((23 / 2 : ℝ) / 30)) - (8 * δ + 4 * τ) ∧
      (25 / 64 : ℝ) * c ≤ c * (1 - (9 : ℝ) / 30) - (6 * δ + 3 * τ) := by
  constructor <;> norm_num <;> linarith

/-- The exponent parameters themselves have a strictly positive simultaneous
witness. This does not assert nonemptiness of the model's common event. -/
theorem widened_far_rows_numeric_witness :
    ∃ c δ τ : ℝ, 0 < c ∧ 0 < δ ∧ 0 < τ ∧ δ ≤ c / 20 ∧ τ ≤ δ / 16 ∧
      8 * δ + 4 * τ < c * (1 - ((23 / 2 : ℝ) / 30)) ∧
      6 * δ + 3 * τ < c * (1 - (9 : ℝ) / 30) := by
  refine ⟨1, 1 / 20, 1 / 320, ?_⟩
  norm_num

/-- The two actual inverse-scale rows, including the widened block-level loss,
are absorbed by the same `(2.73)` interpolation when `δ₀=c/20` and `τ≤δ/16`. -/
theorem eventually_widened_far_margin_rows {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c δ τ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hδ0 : δ ≤ c / 20)
    (hτ : 0 ≤ τ) (hτδ : τ ≤ δ / 16)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ (8 * δ + 4 * τ) *
          (etaT E (s N) / etaT E (u : ℝ)) ^ ((23 / 2 : ℝ)) ≤ B.scale E N (u : ℝ) ∧
      (N : ℝ) ^ (6 * δ + 3 * τ) *
          (etaT E (s N) / etaT E (u : ℝ)) ^ (9 : ℝ) ≤ B.scale E N (u : ℝ) := by
  have hb := widened_far_rows_budget hc hδ hδ0 hτ hτδ
  have hquad := APrimeExponents.eventually_monomial_margin hE hst ht1 hc hreg
    (a := 8 * δ + 4 * τ) (b := 23 / 2) (δ := 1)
    (by norm_num) (by norm_num) (by simpa using hb.1.le)
  have hcubic := APrimeExponents.eventually_monomial_margin hE hst ht1 hc hreg
    (a := 6 * δ + 3 * τ) (b := 9) (δ := 1)
    (by norm_num) (by norm_num) (by simpa using hb.2.le)
  filter_upwards [hquad, hcubic] with N hq hc u
  exact ⟨by simpa using hq u, by simpa using hc u⟩

#print axioms level_le_monomial
#print axioms eventually_level_le_pow
#print axioms QBdWide_le_of_shape
#print axioms QBdWide_le_poly
#print axioms QBdWidePoly_eq
#print axioms widened_far_rows_budget
#print axioms widened_far_rows_slack
#print axioms widened_far_rows_numeric_witness
#print axioms eventually_jG_le_poly_on_common_event
#print axioms nearEpsilon_le_inv_of_widened_level
#print axioms diagFarRate_le_widened_poly
#print axioms diagFarRate_widened_poly_eq
#print axioms eventually_widened_far_margin_rows

end RBM.APrimeJGWidened
