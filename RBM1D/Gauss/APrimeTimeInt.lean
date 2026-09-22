/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2MomentStep
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# T268 — (S6): the time integral and the exponent accounting

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48); the statement is `(S6)` of `docs/reports/V548-referee.md` §6,
with the arithmetic of its Appendix A (A7, A8, A10).

Everything here is **deterministic real analysis**: no probability space, no matrix, no flow.
The cross term of the weighted Grönwall step produces, after the pointwise bound `(S5)`, an
integrand of the shape `u^{-1/2} √(κ̂ · Q_u)`, and this file turns that into the final budget.

## What is proved

* **(a)** `integral_inv_sqrt_mul_sqrt_le` — the time Cauchy–Schwarz
  `∫_s^t u^{-1/2} √(Q_u) du ≤ (log (t/s))^{1/2} (∫_s^t Q_u du)^{1/2}`.
  Proved by Young's inequality `√(ab) ≤ (l a + l⁻¹ b)/2` integrated against
  `∫_s^t u⁻¹ du = log (t/s)` and optimized in `l`; the two degenerate corners
  (`∫Q = 0`, `log (t/s) = 0`) are the `l → 0` and `l → ∞` limits.

* **(b)** `log_div_le_etaT_mul_log` — `log (t/s) ≤ (2C₀/Im m) · η_s · log N` on `N^{-C₀} ≤ s`,
  **covering both logarithmic regimes of Appendix A7** through the two auxiliary lemmas
  `log_div_le_etaT_of_half_le` (`s ≥ 1/2`: `log (t/s) ≤ (t-s)/s ≤ 2(η_s - η_t)/Im m
  ≤ 2η_s/Im m`) and `log_div_le_of_le_half` (`N^{-C₀} ≤ s ≤ 1/2`: `log (t/s) ≤ log (1/s)
  ≤ C₀ log N`, and there `η_s ≥ ½ Im m`, which is `half_im_le_etaT`).

* **(b₀)** `integral_early_le` / `integral_early_le_budget` — the **third** regime, `s = 0`.
  The first cell of the p.24 net starts at `u₀ = 0`, where `log (t/s)` diverges and (a)+(b) are
  unusable; A10 replaces them, with **no logarithm at all**:
  `∫_0^t u^{-1/2} du = 2√t ≤ √2` for `t ≤ 1/2`, times the *supremum* of the rate on that
  segment (where `η_u ≥ ½ Im m` is of order one).  The window is split `[0,1/2] ∪ [1/2,t]`.

* **(c)** `kappaNear_le` / `kappaNear_le_rpow` — Appendix A8:
  `κ̂_j^{near} = N^{-4δ} R_j^{-8} η_j^{-1} r_j^5 ≤ N^{-4δ} η_s^{-11/2} η_j^{9/2}` is increasing
  in `η_j ≤ η_s`, so its maximum is at `j = 0`: `κ̂_j^{near} ≤ N^{ε-4δ} η_s^{-1}`.

* **(d)** `integral_inv_sqrt_mul_sqrt_kappa_le` — the product:
  `∫_s^t u^{-1/2} √(κ̂ Q_u) du ≤ N^{ε-2δ} R^{-2} (C m^{-1} log N)^{1/2}`,
  where `R = η_s/η_t` and the near-field budget `∫_s^t Q̂^{near} ≤ (Im m)^{-1} R^{-4}` is the
  hat-normalized form of `RBM.Step2MomentStep.integral_nearInt_le` (A1).

  The right-hand side really carries `N^{-2δ}` *and* `R^{-2}`; it is not a bare constant.

* `sat_timeInt` — the satisfiability witness, on `R = 2 > 1`, with `Q > 0` pointwise and
  `κ̂ > 0`, for every admissible energy `|E| < 2`.

## The far field

The far-field half of the same accounting is **not** redone here: it is
`RBM.Lemma57.ee_far_le` in the sharp `(J*)²`-shape (T262), and under (2.72)'s `A_t ≥ R^{30}`
the referee's closing computation `(t-s)·κ̂^{far} ≲ R^{-12.5} + N^{2δ}R^{-25} ≪ 1` needs no
raising of `A_ge`.  The report's "sharp far field carries `W^{-1}`" is a typo: the `W^{-1}` of
(5.71)/(5.72) is cancelled by the `W ∑_b` of (5.22).

## A10

`∫_s^t u^{-1/2} du = 2(√t - √s) ≤ 2` is integrable down to `s = 0`, so the *left* endpoint of
(a) may be `0`; `log (t/s)` however diverges there, so **(b) is stated only for `0 < s`** and
the two regimes are separated by `s = 1/2`.  `s = 0` never enters (b).
-/

namespace RBM
namespace APrimeTimeInt

open MeasureTheory

/-! ## Young's inequality -/

/-- `√a · √b ≤ (l a + l⁻¹ b)/2` for `a, b ≥ 0` and `l > 0`: the scalar form of the time
Cauchy–Schwarz inequality, before integration. -/
theorem sqrt_mul_sqrt_le_half {a b l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l) :
    Real.sqrt a * Real.sqrt b ≤ (l * a + l⁻¹ * b) / 2 := by
  have hx : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hy : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hkey : (0 : ℝ) ≤ l⁻¹ * (l * Real.sqrt a - Real.sqrt b) ^ 2 :=
    mul_nonneg (inv_pos.mpr hl).le (sq_nonneg _)
  have hexp : l⁻¹ * (l * Real.sqrt a - Real.sqrt b) ^ 2
      = l * Real.sqrt a ^ 2 - 2 * (Real.sqrt a * Real.sqrt b) + l⁻¹ * Real.sqrt b ^ 2 := by
    field_simp
    ring
  rw [hexp, hx, hy] at hkey
  linarith

/-! ## (a) The time Cauchy–Schwarz inequality -/

/-- **(a)** `∫_s^t u^{-1/2} √(Q_u) du ≤ (log (t/s))^{1/2} · (∫_s^t Q_u du)^{1/2}`. -/
theorem integral_inv_sqrt_mul_sqrt_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {Q : ℝ → ℝ}
    (hQ0 : ∀ u ∈ Set.Icc s t, 0 ≤ Q u)
    (hQint : IntervalIntegrable Q volume s t)
    (hIint : IntervalIntegrable (fun u => Real.sqrt u⁻¹ * Real.sqrt (Q u)) volume s t) :
    (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u))
      ≤ Real.sqrt (Real.log (t / s)) * Real.sqrt (∫ u in s..t, Q u) := by
  have ht : 0 < t := hs.trans_le hst
  have hinvint : IntervalIntegrable (fun u : ℝ => u⁻¹) volume s t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hst]
    exact ContinuousOn.inv₀ continuousOn_id fun x hx => ne_of_gt (lt_of_lt_of_le hs hx.1)
  have hLval : (∫ u in s..t, u⁻¹) = Real.log (t / s) := integral_inv_of_pos hs ht
  have hL0 : 0 ≤ Real.log (t / s) :=
    Real.log_nonneg ((one_le_div hs).mpr hst)
  have hJ0 : (0 : ℝ) ≤ ∫ u in s..t, Q u := intervalIntegral.integral_nonneg hst hQ0
  -- the one-parameter family of bounds
  have key : ∀ l : ℝ, 0 < l →
      (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u))
        ≤ (l * Real.log (t / s) + l⁻¹ * ∫ u in s..t, Q u) / 2 := by
    intro l hl
    have hRint : IntervalIntegrable (fun u : ℝ => l / 2 * u⁻¹ + l⁻¹ / 2 * Q u) volume s t :=
      (hinvint.const_mul (l / 2)).add (hQint.const_mul (l⁻¹ / 2))
    have hmono : (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u))
        ≤ ∫ u in s..t, (l / 2 * u⁻¹ + l⁻¹ / 2 * Q u) := by
      refine intervalIntegral.integral_mono_on hst hIint hRint fun u hu => ?_
      have hu0 : (0 : ℝ) ≤ u⁻¹ := by
        have : 0 < u := lt_of_lt_of_le hs hu.1
        positivity
      have := sqrt_mul_sqrt_le_half hu0 (hQ0 u hu) hl
      linarith
    have hsplit : (∫ u in s..t, (l / 2 * u⁻¹ + l⁻¹ / 2 * Q u))
        = l / 2 * Real.log (t / s) + l⁻¹ / 2 * ∫ u in s..t, Q u := by
      rw [intervalIntegral.integral_add (hinvint.const_mul (l / 2)) (hQint.const_mul (l⁻¹ / 2)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hLval]
    rw [hsplit] at hmono
    linarith
  rcases eq_or_lt_of_le hJ0 with hJz | hJpos
  · -- `∫ Q = 0`: the `l → 0` corner
    have hzero : (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u)) ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hl : 0 < 2 * ε / (Real.log (t / s) + 1) := by positivity
      have h := key _ hl
      rw [← hJz] at h
      have hfrac : Real.log (t / s) / (Real.log (t / s) + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      have : 2 * ε / (Real.log (t / s) + 1) * Real.log (t / s) / 2
          = ε * (Real.log (t / s) / (Real.log (t / s) + 1)) := by
        field_simp
      nlinarith [h, hfrac, hε.le]
    refine hzero.trans ?_
    rw [← hJz]
    simp
  · rcases eq_or_lt_of_le hL0 with hLz | hLpos
    · -- `log (t/s) = 0`: the `l → ∞` corner
      have hzero : (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u)) ≤ 0 := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have hl : 0 < (∫ u in s..t, Q u) / ε := by positivity
        have h := key _ hl
        rw [← hLz] at h
        have hinv : ((∫ u in s..t, Q u) / ε)⁻¹ * (∫ u in s..t, Q u) = ε := by
          rw [inv_div, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hJpos), mul_one]
        rw [hinv] at h
        linarith
      refine hzero.trans ?_
      rw [← hLz]
      simp
    · -- the generic case: `l = √J/√L`
      set SL := Real.sqrt (Real.log (t / s)) with hSL
      set SJ := Real.sqrt (∫ u in s..t, Q u) with hSJ
      have hSL0 : 0 < SL := Real.sqrt_pos.mpr hLpos
      have hSJ0 : 0 < SJ := Real.sqrt_pos.mpr hJpos
      have hSL2 : SL ^ 2 = Real.log (t / s) := Real.sq_sqrt hL0
      have hSJ2 : SJ ^ 2 = ∫ u in s..t, Q u := Real.sq_sqrt hJ0
      have h := key (SJ / SL) (by positivity)
      have hval : (SJ / SL * Real.log (t / s) + (SJ / SL)⁻¹ * ∫ u in s..t, Q u) / 2 = SL * SJ := by
        rw [← hSL2, ← hSJ2]
        field_simp
        ring
      rw [hval] at h
      exact h

/-! ## (b) The logarithmic time window (Appendix A7) -/

/-- `1 ≤ log N` for `N ≥ 3`; the `log N ≥ 1` slack that lets regime 1 of A7 be written in the
same shape as regime 2. -/
theorem one_le_log_of_three_le {N : ℝ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- **Regime 1 of A7** (`s ≥ 1/2`): `log (t/s) ≤ (t-s)/s ≤ 2(η_s - η_t)/Im m ≤ 2 η_s/Im m`.
No `log N` is needed here; the window itself is short. -/
theorem log_div_le_etaT_of_half_le {E : ℝ} (hE : |E| < 2) {s t : ℝ}
    (hs : 1 / 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Real.log (t / s) ≤ 2 * etaT E s / (mE E).im := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hs0 : 0 < s := by linarith
  have h1 : Real.log (t / s) ≤ t / s - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le hs0 hst) hs0)
  have h2 : t / s - 1 = (t - s) / s := by field_simp
  have h3 : (t - s) / s ≤ 2 * (t - s) := by
    rw [div_le_iff₀ hs0]
    nlinarith
  have h4 : 2 * etaT E s / (mE E).im = 2 * (1 - s) := by
    rw [etaT]; field_simp
  linarith

/-- **`η_s ≥ ½ Im m` for `s ≤ 1/2`** — the second half of regime 2 of A7. -/
theorem half_im_le_etaT {E : ℝ} (hE : |E| < 2) {s : ℝ} (hs : s ≤ 1 / 2) :
    (mE E).im / 2 ≤ etaT E s := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  rw [etaT]
  nlinarith

/-- **Regime 2 of A7** (`N^{-C₀} ≤ s ≤ 1/2`, `t ≤ 1`): `log (t/s) ≤ log (1/s) ≤ C₀ log N`. -/
theorem log_div_le_of_le_half {N C₀ s t : ℝ} (hN : 1 ≤ N) (hs0 : 0 < s)
    (hsN : N ^ (-C₀) ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Real.log (t / s) ≤ C₀ * Real.log N := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have h1 : Real.log (t / s) = Real.log t - Real.log s :=
    Real.log_div (ne_of_gt ht0) (ne_of_gt hs0)
  have h2 : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht
  have h3 : Real.log (N ^ (-C₀)) ≤ Real.log s :=
    Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hsN
  have h4 : Real.log (N ^ (-C₀)) = -C₀ * Real.log N := Real.log_rpow hN0 _
  linarith

/-- **(b)** `log (t/s) ≤ (2 C₀ / Im m) · η_s · log N` on the window `N^{-C₀} ≤ s ≤ t ≤ 1`.

**Both regimes of A7 are covered**, split at `s = 1/2`:
* `s ≥ 1/2`: `log (t/s) ≤ 2 η_s / Im m` (`log_div_le_etaT_of_half_le`), and `C₀ ≥ 1`,
  `log N ≥ 1` absorb the missing factors;
* `N^{-C₀} ≤ s ≤ 1/2`: `log (t/s) ≤ C₀ log N` (`log_div_le_of_le_half`) and
  `η_s ≥ ½ Im m` (`half_im_le_etaT`), so `(2C₀/Im m) η_s log N ≥ C₀ log N`.

`s = 0` is **excluded** (`0 < s` via `N^{-C₀} ≤ s`): `log (t/s)` diverges there.  The left
endpoint `0` is admissible for (a) only, where `∫_0^t u^{-1/2} du = 2√t` (A10). -/
theorem log_div_le_etaT_mul_log {E : ℝ} (hE : |E| < 2) {N C₀ s t : ℝ}
    (hC₀ : 1 ≤ C₀) (hN : 3 ≤ N) (hs0 : 0 < s) (hsN : N ^ (-C₀) ≤ s)
    (hst : s ≤ t) (ht : t ≤ 1) :
    Real.log (t / s) ≤ 2 * C₀ / (mE E).im * etaT E s * Real.log N := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le hN
  have hηs : 0 ≤ etaT E s := by
    rw [etaT]; nlinarith
  rcases le_or_gt s (1 / 2) with hcase | hcase
  · have h := log_div_le_of_le_half hN1 hs0 hsN hst ht
    have h2 := half_im_le_etaT hE hcase
    have hKey : C₀ ≤ 2 * C₀ / (mE E).im * etaT E s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith
    nlinarith
  · have h := log_div_le_etaT_of_half_le hE hcase.le hst ht
    have e2 : 2 * C₀ / (mE E).im * etaT E s * Real.log N
        = 2 * C₀ * etaT E s * Real.log N / (mE E).im := by
      field_simp
    have e1 : 2 * etaT E s / (mE E).im = 2 * etaT E s / (mE E).im := rfl
    have hCl : (1 : ℝ) ≤ C₀ * Real.log N := by nlinarith
    have hnum : 2 * etaT E s ≤ 2 * C₀ * etaT E s * Real.log N := by
      nlinarith [mul_le_mul_of_nonneg_left hCl (by linarith : (0 : ℝ) ≤ 2 * etaT E s)]
    have hdiv : 2 * etaT E s / (mE E).im ≤ 2 * C₀ * etaT E s * Real.log N / (mE E).im := by
      gcongr
    rw [e2]
    linarith [hdiv]

/-! ## (b₀) The first cell `s = 0` (Appendix A10)

`log (t/s)` diverges at `s = 0`, so the Cauchy–Schwarz route of (a)+(b) is unavailable on the
first cell of the p.24 net, whose left endpoint **is** `u₀ = 0` (D17: the first cell is not a
mathematical gap).  A10 supplies the replacement, and it needs **no logarithm at all**:
`∫_0^t u^{-1/2} du = 2(√t - √0) = 2√t ≤ √2` for `t ≤ 1/2`, which is finite because `u^{-1/2}`
is integrable at `0`.  Multiplying by the **supremum** of the rate over the segment — where
`η_u = (1-u) Im m ≥ ½ Im m` is of order one — already gives the budget.

The window is therefore split as `[0, 1/2] ∪ [1/2, t]`: the first piece by A10 below, the
second by regime 1 of A7 (`log_div_le_etaT_of_half_le`).  T264's `(G)`
(`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le`) admits `0` as its left endpoint, so the
two pieces concatenate. -/

/-- `√(u⁻¹) = u^{-1/2}` for `0 ≤ u` (including `u = 0`, where both sides are `0`). -/
theorem sqrt_inv_eq_rpow {u : ℝ} (hu : 0 ≤ u) : Real.sqrt u⁻¹ = u ^ (-(1 / 2) : ℝ) := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h]; norm_num
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one u, ← Real.rpow_mul h.le]
    norm_num

/-- `u^{-1/2}` is interval-integrable on `[0, t]`: the singularity at the left endpoint is
integrable (A10). -/
theorem intervalIntegrable_sqrt_inv {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => Real.sqrt u⁻¹) volume 0 t := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le ht]
  refine MeasureTheory.IntegrableOn.congr_fun (f := fun u : ℝ => u ^ (-(1 / 2) : ℝ)) ?_ ?_
    measurableSet_Ioc
  · rw [← Set.uIoc_of_le ht, ← intervalIntegrable_iff]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  · intro u hu
    exact (sqrt_inv_eq_rpow hu.1.le).symm

/-- **A10**: `∫_0^t u^{-1/2} du = 2√t`.  In particular `∫_0^{1/2} u^{-1/2} du = √2 ≤ 2`. -/
theorem integral_sqrt_inv {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, Real.sqrt u⁻¹) = 2 * Real.sqrt t := by
  have hcong : (∫ u in (0 : ℝ)..t, Real.sqrt u⁻¹) = ∫ u in (0 : ℝ)..t, u ^ (-(1 / 2) : ℝ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le ht] at hu
    exact sqrt_inv_eq_rpow hu.1
  rw [hcong, integral_rpow (Or.inl (by norm_num))]
  norm_num [Real.sqrt_eq_rpow]
  ring

/-- **(b₀)** the first cell, by A10: no `log` is involved, only the **supremum** `Qm` of the
rate on the segment times `∫_0^t u^{-1/2} du = 2√t`. -/
theorem integral_early_le {t κ Qm : ℝ} (ht0 : 0 ≤ t) (hκ0 : 0 ≤ κ) {Q : ℝ → ℝ}
    (hQle : ∀ u ∈ Set.Icc (0 : ℝ) t, Q u ≤ Qm)
    (hint : IntervalIntegrable (fun u => Real.sqrt u⁻¹ * Real.sqrt (κ * Q u)) volume 0 t) :
    (∫ u in (0 : ℝ)..t, Real.sqrt u⁻¹ * Real.sqrt (κ * Q u))
      ≤ 2 * Real.sqrt t * Real.sqrt (κ * Qm) := by
  have hb := intervalIntegrable_sqrt_inv ht0
  have hmono : (∫ u in (0 : ℝ)..t, Real.sqrt u⁻¹ * Real.sqrt (κ * Q u))
      ≤ ∫ u in (0 : ℝ)..t, Real.sqrt (κ * Qm) * Real.sqrt u⁻¹ := by
    refine intervalIntegral.integral_mono_on ht0 hint (hb.const_mul _) fun u hu => ?_
    have h1 : Real.sqrt (κ * Q u) ≤ Real.sqrt (κ * Qm) :=
      Real.sqrt_le_sqrt (by nlinarith [hQle u hu])
    have h2 : (0 : ℝ) ≤ Real.sqrt u⁻¹ := Real.sqrt_nonneg _
    calc Real.sqrt u⁻¹ * Real.sqrt (κ * Q u)
        ≤ Real.sqrt u⁻¹ * Real.sqrt (κ * Qm) := mul_le_mul_of_nonneg_left h1 h2
      _ = Real.sqrt (κ * Qm) * Real.sqrt u⁻¹ := mul_comm _ _
  rw [intervalIntegral.integral_const_mul, integral_sqrt_inv ht0] at hmono
  linarith [hmono, mul_comm (Real.sqrt (κ * Qm)) (2 * Real.sqrt t)]

/-- **(b₀)+(d) on the first cell**: the same final shape as (d), with `N^{-2δ}` and `R^{-2}`
genuinely present, obtained **without** any `log (t/s)`.

On `[0, t]` with `t ≤ 1/2` one has `η_t/η_0 = 1 - t ≥ 1/2`, so `R^{-2} = (η_t/η_0)^2 ≥ 1/4`:
the factor `R^{-2}` is of order one here (it is *not* a gain on the first cell), which is why
the explicit constant `4` appears.  The gain on this cell is exactly the `N^{-2δ}`. -/
theorem integral_early_le_budget {E : ℝ} (hE : |E| < 2) {t κ Qm N ε δ : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hN : 1 ≤ N) (hε : 0 ≤ ε)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ (ε - 4 * δ) * (etaT E 0)⁻¹) (hQm : 0 ≤ Qm)
    {Q : ℝ → ℝ} (hQle : ∀ u ∈ Set.Icc (0 : ℝ) t, Q u ≤ Qm)
    (hint : IntervalIntegrable (fun u => Real.sqrt u⁻¹ * Real.sqrt (κ * Q u)) volume 0 t) :
    (∫ u in (0 : ℝ)..t, Real.sqrt u⁻¹ * Real.sqrt (κ * Q u))
      ≤ 4 * N ^ (ε - 2 * δ) * (etaT E t / etaT E 0) ^ 2
          * Real.sqrt (2 * Qm * (mE E).im⁻¹) := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have he0 : etaT E 0 = (mE E).im := by rw [etaT]; ring
  have heratio : etaT E t / etaT E 0 = 1 - t := by
    rw [etaT, etaT]
    field_simp
    ring
  have hstep := integral_early_le ht0 hκ0 hQle hint
  refine hstep.trans ?_
  set Z : ℝ := 4 * N ^ (ε - 2 * δ) * (etaT E t / etaT E 0) ^ 2
      * Real.sqrt (2 * Qm * (mE E).im⁻¹) with hZ
  have hrat0 : (1 : ℝ) / 2 ≤ etaT E t / etaT E 0 := by rw [heratio]; linarith
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    have : (0 : ℝ) < N ^ (ε - 2 * δ) := Real.rpow_pos_of_pos hN0 _
    positivity
  have hsq : ((2 : ℝ) * Real.sqrt t * Real.sqrt (κ * Qm)) ^ 2 = 4 * t * (κ * Qm) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht0, Real.sq_sqrt (by positivity)]
    ring
  have hNsq : (N ^ (ε - 2 * δ)) ^ (2 : ℕ) = N ^ (2 * (ε - 2 * δ)) := by
    rw [← Real.rpow_natCast (N ^ (ε - 2 * δ)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hZsq : Z ^ 2 = 16 * N ^ (2 * (ε - 2 * δ)) * (etaT E t / etaT E 0) ^ 4
      * (2 * Qm * (mE E).im⁻¹) := by
    rw [hZ, mul_pow, mul_pow, mul_pow, hNsq,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Qm * (mE E).im⁻¹)]
    ring
  have hexp : N ^ (ε - 4 * δ) ≤ N ^ (2 * (ε - 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hNpos : (0 : ℝ) < N ^ (ε - 4 * δ) := Real.rpow_pos_of_pos hN0 _
  have hkappa : κ ≤ N ^ (ε - 4 * δ) * (mE E).im⁻¹ := by rwa [he0] at hκ
  have hbound : 4 * t * (κ * Qm) ≤ Z ^ 2 := by
    have h1 : 4 * t * (κ * Qm) ≤ 2 * (N ^ (ε - 4 * δ) * (mE E).im⁻¹ * Qm) := by
      have hP : (0 : ℝ) ≤ κ * Qm := mul_nonneg hκ0 hQm
      have hA : (0 : ℝ) ≤ (2 - 4 * t) * (κ * Qm) := mul_nonneg (by linarith) hP
      have hmul : κ * Qm ≤ N ^ (ε - 4 * δ) * (mE E).im⁻¹ * Qm :=
        mul_le_mul_of_nonneg_right hkappa hQm
      nlinarith [hA, hmul]
    refine h1.trans ?_
    rw [hZsq]
    have hr2 : (1 : ℝ) / 4 ≤ (etaT E t / etaT E 0) ^ 2 := by nlinarith [hrat0]
    have h4 : (1 : ℝ) / 16 ≤ (etaT E t / etaT E 0) ^ 4 := by
      nlinarith [hr2, mul_self_nonneg ((etaT E t / etaT E 0) ^ 2 - 1 / 4)]
    have hQmm : 0 ≤ Qm * (mE E).im⁻¹ := by positivity
    have h2 : N ^ (ε - 4 * δ) * (mE E).im⁻¹ * Qm
        ≤ N ^ (2 * (ε - 2 * δ)) * (mE E).im⁻¹ * Qm := by
      have := mul_le_mul_of_nonneg_right hexp hQmm
      nlinarith [this]
    have hNsq0 : (0 : ℝ) < N ^ (2 * (ε - 2 * δ)) := Real.rpow_pos_of_pos hN0 _
    nlinarith [h2, h4, hQmm, hNsq0]
  calc (2 : ℝ) * Real.sqrt t * Real.sqrt (κ * Qm)
      = Real.sqrt (((2 : ℝ) * Real.sqrt t * Real.sqrt (κ * Qm)) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (Z ^ 2) := Real.sqrt_le_sqrt (by rw [hsq]; exact hbound)
    _ = Z := Real.sqrt_sq hZ0

/-! ## (c) The near-field early-time rate (Appendix A8) -/

/-- `κ̂_j^{near} = N^{-4δ} R_j^{-8} η_j^{-1} r_j^5` with `R_j = η_s/η_j` (A8). -/
noncomputable def kappaNear (N δ ηs ηj rj : ℝ) : ℝ :=
  N ^ (-(4 * δ)) * (ηj / ηs) ^ 8 * ηj⁻¹ * rj ^ 5

/-- **(c)** `κ̂_j^{near} ≤ N^{-4δ} η_s^{-1}`.

With `r_j ≤ R_j^{1/2}` (A1's `r_u^5 ≤ (η_s/η_u)^{5/2}`) one has
`κ̂_j^{near} ≤ N^{-4δ} η_j^{-1} R_j^{-11/2} = N^{-4δ} η_s^{-11/2} η_j^{9/2}`, which is
**increasing in `η_j`** on `η_j ≤ η_s`; its maximum is therefore at `j = 0`, i.e. `η_j = η_s`,
where it equals `N^{-4δ} η_s^{-1}`.  In the proof the monotonicity is the single inequality
`r^5 ≤ r^{14}` for `r = (η_s/η_j)^{1/2} ≥ 1`. -/
theorem kappaNear_le {N δ ηs ηj rj : ℝ} (hN : 1 ≤ N) (hηj : 0 < ηj) (hle : ηj ≤ ηs)
    (hrj0 : 0 ≤ rj) (hrj : rj ≤ Real.sqrt (ηs / ηj)) :
    kappaNear N δ ηs ηj rj ≤ N ^ (-(4 * δ)) * ηs⁻¹ := by
  have hηs : 0 < ηs := lt_of_lt_of_le hηj hle
  have hA : (0 : ℝ) < N ^ (-(4 * δ)) := Real.rpow_pos_of_pos (by linarith) _
  have hr0 : (0 : ℝ) ≤ Real.sqrt (ηs / ηj) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (ηs / ηj) ^ 2 = ηs / ηj := Real.sq_sqrt (by positivity)
  have hr1 : (1 : ℝ) ≤ Real.sqrt (ηs / ηj) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ((one_le_div hηj).mpr hle)
  have hηsr : ηs = ηj * Real.sqrt (ηs / ηj) ^ 2 := by
    rw [hr2]; field_simp
  have h5 : rj ^ 5 ≤ Real.sqrt (ηs / ηj) ^ 5 := by
    exact pow_le_pow_left₀ hrj0 hrj 5
  have h14 : Real.sqrt (ηs / ηj) ^ 5 ≤ Real.sqrt (ηs / ηj) ^ 14 :=
    pow_le_pow_right₀ hr1 (by norm_num)
  have hmain : ηj ^ 7 * rj ^ 5 ≤ ηs ^ 7 := by
    have hpow : ηs ^ 7 = ηj ^ 7 * Real.sqrt (ηs / ηj) ^ 14 := by
      nth_rewrite 1 [hηsr]; ring
    rw [hpow]
    have hj7 : (0 : ℝ) < ηj ^ 7 := by positivity
    nlinarith [h5, h14, hj7]
  have hkey : (ηj / ηs) ^ 8 * ηj⁻¹ * rj ^ 5 ≤ ηs⁻¹ := by
    have e : (ηj / ηs) ^ 8 * ηj⁻¹ * rj ^ 5 = ηj ^ 7 * rj ^ 5 / ηs ^ 8 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity : (0 : ℝ) < ηs ^ 8)]
    have e2 : ηs⁻¹ * ηs ^ 8 = ηs ^ 7 := by field_simp
    rw [e2]
    exact hmain
  have hassoc : N ^ (-(4 * δ)) * (ηj / ηs) ^ 8 * ηj⁻¹ * rj ^ 5
      = N ^ (-(4 * δ)) * ((ηj / ηs) ^ 8 * ηj⁻¹ * rj ^ 5) := by ring
  rw [kappaNear, hassoc]
  exact mul_le_mul_of_nonneg_left hkey hA.le

/-- **(c)** with the `N^ε` slack of `(S6)`: `κ̂_j^{near} ≤ N^{ε-4δ} η_s^{-1}`. -/
theorem kappaNear_le_rpow {N δ ε ηs ηj rj : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hηj : 0 < ηj)
    (hle : ηj ≤ ηs) (hrj0 : 0 ≤ rj) (hrj : rj ≤ Real.sqrt (ηs / ηj)) :
    kappaNear N δ ηs ηj rj ≤ N ^ (ε - 4 * δ) * ηs⁻¹ := by
  have hηs : 0 < ηs := lt_of_lt_of_le hηj hle
  refine (kappaNear_le hN hηj hle hrj0 hrj).trans ?_
  have hexp : N ^ (-(4 * δ)) ≤ N ^ (ε - 4 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-! ## (d) The product -/

/-- **(d)** the full cross-term budget on a window with `0 < s`:

`∫_s^t u^{-1/2} √(κ̂ Q_u) du ≤ N^{ε-2δ} · R^{-2} · (C m^{-1} log N)^{1/2}`, `R = η_s/η_t`.

The three inputs are (a) (time Cauchy–Schwarz), (b) (`log (t/s) ≤ C η_s log N`) and (c)
(`κ̂ ≤ N^{ε-4δ} η_s^{-1}`), together with the hat-normalized near-field budget
`∫_s^t Q̂ ≤ m^{-1} R^{-4}` (A1 / `RBM.Step2MomentStep.integral_nearInt_le` divided by the
level `Λ² = R^8`).  The `η_s` of (b) cancels the `η_s^{-1}` of (c) exactly; the only loss is
`N^{(ε-4δ)/2} ≤ N^{ε-2δ}`.

The right-hand side carries `N^{-2δ}` **and** `R^{-2}`: it is not a bare constant. -/
theorem integral_inv_sqrt_mul_sqrt_kappa_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {Q : ℝ → ℝ}
    (hQ0 : ∀ u ∈ Set.Icc s t, 0 ≤ Q u)
    (hQint : IntervalIntegrable Q volume s t)
    (hIint : IntervalIntegrable (fun u => Real.sqrt u⁻¹ * Real.sqrt (Q u)) volume s t)
    {κ N ε δ C m ηs ηt : ℝ}
    (hκ0 : 0 ≤ κ) (hN : 1 ≤ N) (hε : 0 ≤ ε) (hm : 0 < m) (hC : 0 ≤ C)
    (hηt : 0 < ηt) (hηts : ηt ≤ ηs)
    (hκ : κ ≤ N ^ (ε - 4 * δ) * ηs⁻¹)
    (hlog : Real.log (t / s) ≤ C * ηs * Real.log N)
    (hQbd : (∫ u in s..t, Q u) ≤ m⁻¹ * (ηt / ηs) ^ 4) :
    (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (κ * Q u))
      ≤ N ^ (ε - 2 * δ) * (ηt / ηs) ^ 2 * Real.sqrt (C * m⁻¹ * Real.log N) := by
  have hηs : 0 < ηs := lt_of_lt_of_le hηt hηts
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hL0 : 0 ≤ Real.log (t / s) := Real.log_nonneg ((one_le_div hs).mpr hst)
  have hJ0 : (0 : ℝ) ≤ ∫ u in s..t, Q u := intervalIntegral.integral_nonneg hst hQ0
  have hrw : (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (κ * Q u))
      = Real.sqrt κ * ∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    change Real.sqrt u⁻¹ * Real.sqrt (κ * Q u)
      = Real.sqrt κ * (Real.sqrt u⁻¹ * Real.sqrt (Q u))
    rw [Real.sqrt_mul hκ0]
    ring
  rw [hrw]
  have ha := integral_inv_sqrt_mul_sqrt_le hs hst hQ0 hQint hIint
  have hstep : Real.sqrt κ * (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (Q u))
      ≤ Real.sqrt κ * (Real.sqrt (Real.log (t / s)) * Real.sqrt (∫ u in s..t, Q u)) :=
    mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg _)
  refine hstep.trans ?_
  have hcomb : Real.sqrt κ * (Real.sqrt (Real.log (t / s)) * Real.sqrt (∫ u in s..t, Q u))
      = Real.sqrt (κ * (Real.log (t / s) * ∫ u in s..t, Q u)) := by
    rw [Real.sqrt_mul hκ0, Real.sqrt_mul hL0]
  rw [hcomb]
  set Y : ℝ := N ^ (ε - 2 * δ) * (ηt / ηs) ^ 2 * Real.sqrt (C * m⁻¹ * Real.log N) with hY
  have hNr : (0 : ℝ) < N ^ (ε - 2 * δ) := Real.rpow_pos_of_pos hN0 _
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hNsq : (N ^ (ε - 2 * δ)) ^ (2 : ℕ) = N ^ (2 * (ε - 2 * δ)) := by
    rw [← Real.rpow_natCast (N ^ (ε - 2 * δ)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hYsq : Y ^ 2 = N ^ (2 * (ε - 2 * δ)) * (ηt / ηs) ^ 4 * (C * m⁻¹ * Real.log N) := by
    rw [hY, mul_pow, mul_pow, hNsq,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ C * m⁻¹ * Real.log N)]
    ring
  have hAnn : (0 : ℝ) ≤ N ^ (ε - 4 * δ) * ηs⁻¹ := by positivity
  have hBnn : (0 : ℝ) ≤ C * ηs * Real.log N := by positivity
  have hDnn : (0 : ℝ) ≤ m⁻¹ * (ηt / ηs) ^ 4 := by positivity
  have hprod : κ * (Real.log (t / s) * ∫ u in s..t, Q u)
      ≤ N ^ (ε - 4 * δ) * ηs⁻¹ * ((C * ηs * Real.log N) * (m⁻¹ * (ηt / ηs) ^ 4)) := by
    refine mul_le_mul hκ ?_ (mul_nonneg hL0 hJ0) hAnn
    exact mul_le_mul hlog hQbd hJ0 hBnn
  refine le_trans (Real.sqrt_le_sqrt (hprod.trans ?_)) (le_of_eq (Real.sqrt_sq hY0))
  rw [hYsq]
  have hcancel : N ^ (ε - 4 * δ) * ηs⁻¹ * ((C * ηs * Real.log N) * (m⁻¹ * (ηt / ηs) ^ 4))
      = N ^ (ε - 4 * δ) * (ηt / ηs) ^ 4 * (C * m⁻¹ * Real.log N) := by
    field_simp
  rw [hcancel]
  have hexp : N ^ (ε - 4 * δ) ≤ N ^ (2 * (ε - 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hrest : (0 : ℝ) ≤ (ηt / ηs) ^ 4 * (C * m⁻¹ * Real.log N) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hexp hrest]

/-! ## Satisfiability witness

`R = η_s/η_t = 2 > 1`, `Q > 0` pointwise, `κ̂ > 0` and equal to `kappaNear` at its **maximizing**
index `j = 0` (so (c) is attained, not slack), and the near-field budget holds with **equality**.
Nothing is degenerate: no `Q ≡ 0`, no `s = t`, no `κ̂ = 0`. -/

/-- **A compiled satisfiability witness** for (a)–(d): for every admissible energy `|E| < 2`
there is a genuinely non-degenerate window on which all hypotheses hold simultaneously and the
conclusion of (d) is the stated `N^{ε-2δ} R^{-2} (C m^{-1} log N)^{1/2}` with `R = 2`. -/
theorem sat_timeInt {E : ℝ} (hE : |E| < 2) :
    ∃ (s t κ ηs ηt C : ℝ) (Q : ℝ → ℝ),
      0 < s ∧ s < t ∧ t ≤ 1 ∧ ηs = etaT E s ∧ ηt = etaT E t ∧
      ηs / ηt = 2 ∧ 0 < κ ∧ (∀ u, 0 < Q u) ∧ 0 < C ∧
      κ = kappaNear 3 (1 / 8) ηs ηs 1 ∧
      κ ≤ (3 : ℝ) ^ ((0 : ℝ) - 4 * (1 / 8)) * ηs⁻¹ ∧
      Real.log (t / s) ≤ C * ηs * Real.log 3 ∧
      (∫ u in s..t, Q u) = (mE E).im⁻¹ * (ηt / ηs) ^ 4 ∧
      (∫ u in s..t, Real.sqrt u⁻¹ * Real.sqrt (κ * Q u))
        ≤ (3 : ℝ) ^ ((0 : ℝ) - 2 * (1 / 8)) * (ηt / ηs) ^ 2
            * Real.sqrt (C * (mE E).im⁻¹ * Real.log 3) := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have he1 : etaT E (1 / 2) = (mE E).im / 2 := by rw [etaT]; ring
  have he2 : etaT E (3 / 4) = (mE E).im / 4 := by rw [etaT]; ring
  have hηs : 0 < etaT E (1 / 2) := by rw [he1]; linarith
  have hηt : 0 < etaT E (3 / 4) := by rw [he2]; linarith
  have hratio : etaT E (1 / 2) / etaT E (3 / 4) = 2 := by
    rw [he1, he2]; field_simp; norm_num
  have hrat4 : etaT E (3 / 4) / etaT E (1 / 2) = 1 / 2 := by
    rw [he1, he2]; field_simp; norm_num
  have hκeq : kappaNear 3 (1 / 8) (etaT E (1 / 2)) (etaT E (1 / 2)) 1
      = (3 : ℝ) ^ (-(4 * (1 / 8)) : ℝ) * (etaT E (1 / 2))⁻¹ := by
    rw [kappaNear]
    rw [div_self (ne_of_gt hηs)]
    ring
  have hκ0 : 0 < kappaNear 3 (1 / 8) (etaT E (1 / 2)) (etaT E (1 / 2)) 1 := by
    rw [hκeq]
    have : (0 : ℝ) < (3 : ℝ) ^ (-(4 * (1 / 8)) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hκle : kappaNear 3 (1 / 8) (etaT E (1 / 2)) (etaT E (1 / 2)) 1
      ≤ (3 : ℝ) ^ ((0 : ℝ) - 4 * (1 / 8)) * (etaT E (1 / 2))⁻¹ :=
    kappaNear_le_rpow (by norm_num) le_rfl hηs le_rfl zero_le_one
      (by rw [div_self (ne_of_gt hηs)]; simp)
  have hsN : (3 : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one]; norm_num
  have hlog := log_div_le_etaT_mul_log hE (C₀ := 1) (N := 3) (s := 1 / 2) (t := 3 / 4)
    le_rfl le_rfl (by norm_num) hsN (by norm_num) (by norm_num)
  have hQint : IntervalIntegrable (fun _ : ℝ => (mE E).im⁻¹ / 4) volume (1 / 2) (3 / 4) :=
    intervalIntegrable_const
  have hIint : IntervalIntegrable
      (fun u : ℝ => Real.sqrt u⁻¹ * Real.sqrt ((mE E).im⁻¹ / 4)) volume (1 / 2) (3 / 4) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 3 / 4)]
    refine ContinuousOn.mul ?_ continuousOn_const
    refine Real.continuous_sqrt.comp_continuousOn ?_
    exact ContinuousOn.inv₀ continuousOn_id fun x hx => ne_of_gt (by linarith [hx.1])
  have hQval : (∫ _u in (1 / 2 : ℝ)..(3 / 4), (mE E).im⁻¹ / 4)
      = (mE E).im⁻¹ * (etaT E (3 / 4) / etaT E (1 / 2)) ^ 4 := by
    rw [intervalIntegral.integral_const, hrat4]
    norm_num
    ring
  refine ⟨1 / 2, 3 / 4, kappaNear 3 (1 / 8) (etaT E (1 / 2)) (etaT E (1 / 2)) 1,
    etaT E (1 / 2), etaT E (3 / 4), 2 * 1 / (mE E).im, fun _ => (mE E).im⁻¹ / 4,
    by norm_num, by norm_num, by norm_num, rfl, rfl, hratio, hκ0, fun _ => by positivity,
    by positivity, rfl, hκle, hlog, hQval, ?_⟩
  refine integral_inv_sqrt_mul_sqrt_kappa_le (s := 1 / 2) (t := 3 / 4)
    (Q := fun _ => (mE E).im⁻¹ / 4) (κ := kappaNear 3 (1 / 8) (etaT E (1 / 2)) (etaT E (1 / 2)) 1)
    (N := 3) (ε := 0) (δ := 1 / 8) (C := 2 * 1 / (mE E).im) (m := (mE E).im)
    (ηs := etaT E (1 / 2)) (ηt := etaT E (3 / 4))
    (by norm_num) (by norm_num) (fun u _ => by positivity) hQint hIint
    hκ0.le (by norm_num) le_rfl hm (by positivity) hηt (by rw [he1, he2]; linarith)
    hκle hlog (le_of_eq hQval)

/-! ## Deviations (temporary id `T268a`)

`T268a` — **the `s = 0` cell and its explicit constant `4`.**

① *Paper position*: §5.3, the accounting of (5.39)–(5.48); the net of p.24 whose first cell has
left endpoint `u₀ = 0`.  In the referee's list this is `(S6)` of `docs/reports/V548-referee.md`
§6 together with Appendix A10; `(S6)` itself only names the two logarithmic regimes of A7.

② *Is the paper changed?*  **No.**  Nothing here contradicts the paper; the `s = 0` cell is
handled by an inequality the paper's own accounting already contains (`u^{-1/2}` is integrable
at `0`), and D17 has already ruled that the first cell is not a mathematical gap.  The only
addition is bookkeeping: on `[0, 1/2]` the factor `R^{-2} = (η_t/η_0)^2` lies in `[1/4, 1]`, so
it is *not* a gain there, and an explicit constant `4` is carried in
`integral_early_le_budget` to keep the conclusion in the same shape as (d).  The gain on that
cell is the `N^{-2δ}` alone.

③ *Lines*: about 60 (`sqrt_inv_eq_rpow` … `integral_early_le_budget`).

④ *Renumbering*: none.

`T268b` — **the hat-normalization of the near-field budget.**

① *Paper position*: A1 of the referee's Appendix A, i.e.
`RBM.Step2MomentStep.integral_nearInt_le`, which reads `∫_s^v nearInt ≤ (Im m)^{-1} R^{4}`,
while `(S6)` quotes `∫_s^t Q̂^{near} ≤ (Im m)^{-1} R^{-4}`.

② *Is the paper changed?*  **No.**  The two differ only by the level `Λ² = R^8` by which `Q` is
normalized to `Q̂` upstream; `(d)` here takes the hat-normalized form `m^{-1} R^{-4}` as a
hypothesis, so whichever normalization the producer supplies, the shape is explicit and cannot
silently drift.

③ *Lines*: 1 (the hypothesis `hQbd`).

④ *Renumbering*: none.
-/

end APrimeTimeInt
end RBM
