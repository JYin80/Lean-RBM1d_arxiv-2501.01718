/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.APrimeNearRem
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Hierarchy.Lemma57
import RBM1D.Hierarchy.Step2
import RBM1D.Flow.FlowFamiliesCore

/-!
# (5.44) on the grid: the label-free time sum `Λ_k` (T1508, amend-1)

Ticket `docs/tickets/T1508-amend-1.md`; paper (5.44), p. 58, in the shape the label-weighted
Azuma of T1504 (T1″) consumes (supervisor 2026-09-26-0048 §1a, item R1).

The upstream `qv_conv_le` (T1509/T1512) delivers per-step coefficients
`c k b j = Δ (√Q_j r_{j,k}² xiK T_{u_k}(b))²` with `r_{j,k} = (1 - u_{j+1})/(1 - u_k)`, so
`Σ_j c k b j = xiK² T_{u_k}(b)² Λ_k` with the label-free scalar `Λ_k`. This file bounds `Λ_k`.

## Main definitions

* `qvJ E s δ ε N w = N^{2ε} · Step2.thr E s δ N w = N^{2ε} N^δ (η_s/η_w)^4`.
* `Qd B E s δ ε D N w`: the per-time rate of T1497 (`Gauss/Step2QVEvent.lean:194`) with `jG`
  replaced by `qvJ`, i.e. `diagShape'` with the near-field indicator dropped and the common
  `tailT²` factored out.
* `qvSumConst E = 1200 / Im m(E)`.

## Main results

* `qv_time_sum_le` (**T2′**): for `κ > 0`, eventually in `N`, uniformly in the endpoint
  `u_* ∈ [s,t]`, the step count `K ≥ 1` and `k ≤ K`,
  `Σ_{j<k} Δ Qd(u_j) ((1-u_j)/(1-u_k))^4 ≤ qvSumConst E · N^κ · ((η_s/η_{u_k})^4 + 1)`.
  **The exponent 4 is attained exactly.**
* `qv_time_sum_le'`: the same bound for the propagator factor `((1-u_{j+1})/(1-u_k))^4` of
  `qv_conv_le`.

## Route

The whole summand is dominated pointwise, for `s ≤ w ≤ v = u_k`, by
`(34 N^κ + 1152) η_s³/η_v⁴ + 3 (η_s/η_v)^4`; then `Σ_{j<k} Δ = u_k - s ≤ 1 - s = η_s/Im m`.
The near term is the sharp one: with `r_w = ℓ_w/ℓ_s` kept at the *same* time as `η_w`, the
cap-robust inequality `r_w² η_w ≤ η_s` gives `r_w⁵ η_w³ ≤ η_s³`, so
`η_w⁻¹ r_w⁵ (η_w/η_v)^4 ≤ η_s³/η_v⁴` and the sum is `≤ (η_s/η_v)^4/Im m`: exponent exactly `4`.
(Taking the supremum of each factor separately would lose, `≈ R^{6.5}`; integrating instead of
summing only improves the constant `1 → 2/3`.) Since no Riemann-sum error is incurred, no mesh
condition on `Δ` is needed. The `J`-powers of the far terms are absorbed by the `N^{-c}` gain of
step2's `hreg`, for every `0 < δ ≤ c/24` and `2ε ≤ δ`; `nearEpsilon ≤ W⁻¹` is
`RBM.EEDef.nearEpsilon_le_inv`; `cNear2 ≤ N^κ` is the stretched-exponential absorption.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Filter Real RBM

namespace QVSum

/-! ## Cap-robust ratio bound -/

/-- `ℓ̂(x) · √(1-x) = min(1, L·√(1-x))`. -/
theorem ellHat_mul_sqrt_one_sub (L : ℕ) {x : ℝ} (hx1 : x < 1) :
    ellHat L (x : ℂ) * Real.sqrt (1 - x) = min 1 ((L : ℝ) * Real.sqrt (1 - x)) := by
  have h1x : 0 < 1 - x := by linarith
  have hsqrt : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 h1x
  rw [ellHat_ofReal L hx1, min_mul_of_nonneg _ _ hsqrt.le, one_div_mul_cancel hsqrt.ne']

/-- `ℓ̂(x)√(1-x)` is non-increasing in `x` (whether or not the cap `L` is active). -/
theorem ellHat_mul_sqrt_one_sub_le (L : ℕ) {s w : ℝ} (hw1 : w < 1) (hsw : s ≤ w) :
    ellHat L (w : ℂ) * Real.sqrt (1 - w) ≤ ellHat L (s : ℂ) * Real.sqrt (1 - s) := by
  rw [ellHat_mul_sqrt_one_sub L hw1, ellHat_mul_sqrt_one_sub L (hsw.trans_lt hw1)]
  exact min_le_min le_rfl
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Nat.cast_nonneg L))

/-- **Cap-robust ratio bound (K1)**: `ℓ_w² (1-w) ≤ ℓ_s² (1-s)` for `s ≤ w < 1`. -/
theorem ellHat_sq_mul_one_sub_le (L : ℕ) {s w : ℝ} (hw1 : w < 1) (hsw : s ≤ w) :
    ellHat L (w : ℂ) ^ 2 * (1 - w) ≤ ellHat L (s : ℂ) ^ 2 * (1 - s) := by
  have hs1 : s < 1 := hsw.trans_lt hw1
  have h := ellHat_mul_sqrt_one_sub_le L hw1 hsw
  have h0 : 0 ≤ ellHat L (w : ℂ) * Real.sqrt (1 - w) := by
    rw [ellHat_mul_sqrt_one_sub L hw1]
    exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg L) (Real.sqrt_nonneg _))
  have hsq := pow_le_pow_left₀ h0 h 2
  have ew : (ellHat L (w : ℂ) * Real.sqrt (1 - w)) ^ 2 = ellHat L (w : ℂ) ^ 2 * (1 - w) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  have es : (ellHat L (s : ℂ) * Real.sqrt (1 - s)) ^ 2 = ellHat L (s : ℂ) ^ 2 * (1 - s) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  rw [ew, es] at hsq
  exact hsq

/-! ## Absorption: `cNear2`, `cFar2` are `N^{o(1)}` uniformly in the scale -/

/-- `cNear2 W ℓ ≤ (2 (log W)^3 + 2) exp(4 (log W)^{3/4})` for `1 ≤ ℓ`. -/
theorem cNear2_le_of_one_le {W ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    Lemma57.cNear2 W ℓ ≤
      (2 * Real.log W ^ (3 : ℝ) + 2) * Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) := by
  have hdiv : 2 / ℓ ≤ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ℓ)]; nlinarith
  have hpoly : 2 * Real.log W ^ (3 : ℝ) + 2 / ℓ ≤ 2 * Real.log W ^ (3 : ℝ) + 2 := by linarith
  unfold Lemma57.cNear2
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le

/-- `cFar2 W ℓ ≤ 2 cNear2 W ℓ` for `W ≥ e`, `ℓ > 0`. -/
theorem cFar2_le_two_cNear2 {W ℓ : ℝ} (hW : Real.exp 1 ≤ W) (hℓ : 0 < ℓ) :
    Lemma57.cFar2 W ℓ ≤ 2 * Lemma57.cNear2 W ℓ := by
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hlog1 : 1 ≤ Real.log W := by
    have := Real.log_le_log (Real.exp_pos 1) hW
    simpa using this
  set x : ℝ := Real.log W ^ (3 / 4 : ℝ)
  set y : ℝ := Real.log W ^ (3 / 2 : ℝ)
  have hxy : y ^ (2 : ℕ) = Real.log W ^ (3 : ℝ) := by
    rw [show y = Real.log W ^ (3/2 : ℝ) from rfl,
      ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log W)]
    norm_num
  have hy1 : 1 ≤ y := Real.one_le_rpow hlog1 (by norm_num)
  have hpoly : 4 * y + 4 / ℓ ≤ 2 * (2 * Real.log W ^ (3 : ℝ) + 2 / ℓ) := by
    rw [← hxy]
    have hsq : y ≤ y ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (by linarith : (0:ℝ) ≤ y)]
    linear_combination 4 * hsq
  have hexp : Real.exp x ≤ Real.exp (4 * x) := by
    apply Real.exp_le_exp.mpr
    have hx : 0 ≤ x := Real.rpow_nonneg (Real.log_nonneg hW1) _
    linarith
  have hp0 : 0 ≤ 2 * Real.log W ^ (3 : ℝ) + 2 / ℓ := by positivity
  unfold Lemma57.cFar2 Lemma57.cNear2 Lemma57.loss1
  change (4 * y + 4 / ℓ) * Real.exp x ≤
    2 * ((2 * Real.log W ^ (3 : ℝ) + 2 / ℓ) * Real.exp (4 * x))
  nlinarith [mul_nonneg (sub_nonneg.mpr hpoly) (Real.exp_pos x).le,
    mul_nonneg hp0 (sub_nonneg.mpr hexp)]

/-- **Stretched-exponential absorption**, `Band`-generic: for every `τ > 0`, eventually in `N`,
`cNear2 (B.W N) ℓ ≤ N^τ` uniformly over every scale `ℓ ≥ 1`. -/
theorem eventually_cNear2_le_rpow {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {τ : ℝ}
    (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ ℓ : ℝ, 1 ≤ ℓ → Lemma57.cNear2 (B.W N : ℝ) ℓ ≤ (N : ℝ) ^ τ := by
  have ha : 0 < τ / 2 := by positivity
  have hlog := (Asymptotics.isLittleO_iff_nat_mul_le'.1
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) ha)) 4
  have hlogW := (RBM.Step2.tendsto_W B).eventually hlog
  have hexpW := (RBM.Step2.tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 4 ha)
  have hfour := ((tendsto_rpow_atTop ha).comp (RBM.Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [hlogW, hexpW, hfour, B.dim]
    with N hlogN hexpN hfourN hdim ℓ hℓ
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := B.one_le_W N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hWN : (B.W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ (B.L N : ℝ) := by exact_mod_cast B.one_le_L N
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hcN2 := cNear2_le_of_one_le (W := (B.W N : ℝ)) hℓ
  have hlog0 : 0 ≤ Real.log (B.W N : ℝ) := Real.log_nonneg hW1
  have hlogN' : 4 * Real.log (B.W N : ℝ) ^ (3 : ℝ) ≤ (B.W N : ℝ) ^ (τ / 2) := by
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg hW0.le _)] using hlogN
  have hpoly : 2 * Real.log (B.W N : ℝ) ^ (3 : ℝ) + 2 ≤ (B.W N : ℝ) ^ (τ / 2) := by
    have hfourN' : (4 : ℝ) ≤ (B.W N : ℝ) ^ (τ / 2) := by
      simpa only [Function.comp_apply] using hfourN
    linarith
  have hexp' : Real.exp (4 * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) ≤ (B.W N : ℝ) ^ (τ / 2) := by
    simpa only [one_mul] using hexpN
  calc Lemma57.cNear2 (B.W N : ℝ) ℓ
      ≤ (2 * Real.log (B.W N : ℝ) ^ (3 : ℝ) + 2) *
          Real.exp (4 * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) := hcN2
    _ ≤ (B.W N : ℝ) ^ (τ / 2) * (B.W N : ℝ) ^ (τ / 2) :=
        mul_le_mul hpoly hexp' (Real.exp_pos _).le (Real.rpow_nonneg hW0.le _)
    _ = (B.W N : ℝ) ^ τ := by rw [← Real.rpow_add hW0]; congr 1; ring
    _ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow hW0.le hWN hτ.le

/-! ## Pointwise arithmetic of the three rates -/

/-- **(K2)** From `r² η_w ≤ η_s` and `η_w ≤ η_s`: `r⁵ η_w³ ≤ η_s³` (natural powers only; the
pointwise form of `r ≤ (η_s/η_w)^{1/2}` used inside the time sum). -/
theorem pow5_mul_pow3_le {r ηw ηs : ℝ} (hr0 : 0 ≤ r) (hηw : 0 ≤ ηw) (hws : ηw ≤ ηs)
    (hK1 : r ^ 2 * ηw ≤ ηs) : r ^ 5 * ηw ^ 3 ≤ ηs ^ 3 := by
  have hηs : 0 ≤ ηs := hηw.trans hws
  have h1 : (r * ηw) ^ 2 ≤ ηs ^ 2 := by
    calc (r * ηw) ^ 2 = (r ^ 2 * ηw) * ηw := by ring
      _ ≤ ηs * ηs := mul_le_mul hK1 hws hηw hηs
      _ = ηs ^ 2 := by ring
  have h2 : r * ηw ≤ ηs := (pow_le_pow_iff_left₀ (by positivity) hηs (by norm_num)).1 h1
  have h3 : (r ^ 2 * ηw) ^ 2 ≤ ηs ^ 2 := pow_le_pow_left₀ (by positivity) hK1 2
  calc r ^ 5 * ηw ^ 3 = (r ^ 2 * ηw) ^ 2 * (r * ηw) := by ring
    _ ≤ ηs ^ 2 * ηs := mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = ηs ^ 3 := by ring

/-- **Near term, pointwise, with the propagator factor.** -/
theorem near_mul_le {ℓw ℓs ηw ηs ηv c2 cN : ℝ} (hℓs : 0 < ℓs) (hℓw : 0 ≤ ℓw) (hηw : 0 < ηw)
    (hηv : 0 < ηv) (hws : ηw ≤ ηs) (hK1 : (ℓw / ℓs) ^ 2 * ηw ≤ ηs) (hc0 : 0 ≤ c2)
    (hc : c2 ≤ cN) :
    2 * ηw⁻¹ * c2 * (ℓw / ℓs) ^ 5 * (ηw / ηv) ^ 4 ≤ 2 * cN * (ηs ^ 3 / ηv ^ 4) := by
  have hr0 : 0 ≤ ℓw / ℓs := div_nonneg hℓw hℓs.le
  have key := pow5_mul_pow3_le hr0 hηw.le hws hK1
  have heq : 2 * ηw⁻¹ * c2 * (ℓw / ℓs) ^ 5 * (ηw / ηv) ^ 4 =
      2 * c2 * ((ℓw / ℓs) ^ 5 * ηw ^ 3 / ηv ^ 4) := by
    field_simp
  rw [heq]
  have hcN : 0 ≤ cN := hc0.trans hc
  gcongr

/-- **Far terms, pointwise, with the propagator factor.** The first part carries `η_w⁻¹` and is
bounded by `(16 cF + 1152) η_s³/η_v⁴`, the `W^{-D}` part by `32 W L W^{-D} J³ (η_s/η_v)^4`. -/
theorem far_mul_le {W L D J A S ηw ηs ηv c2 cF : ℝ} (hW0 : 0 < W) (hL0 : 0 ≤ L)
    (hηw : 0 < ηw) (hηv : 0 < ηv) (hws : ηw ≤ ηs) (hJ0 : 0 ≤ J) (hA0 : 0 < A) (hS0 : 0 ≤ S)
    (hJ3 : J ^ 3 ≤ A) (hJS : J ^ 4 * A ^ 2 * S ≤ 1) (hc0 : 0 ≤ c2) (hc : c2 ≤ cF) :
    (2 * ηw⁻¹ * (c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹)
        + 4 * W * L * W ^ (-D) * (2 * J) ^ 3) * (ηw / ηv) ^ 4
      ≤ (16 * cF + 1152) * (ηs ^ 3 / ηv ^ 4) + 32 * (W * L * W ^ (-D) * J ^ 3) * (ηs / ηv) ^ 4 := by
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hsS : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hq0 : 0 ≤ J ^ 2 * (A * Real.sqrt S) := by positivity
  have hq : J ^ 2 * (A * Real.sqrt S) ≤ 1 := by
    have hsq : (J ^ 2 * (A * Real.sqrt S)) ^ 2 = J ^ 4 * A ^ 2 * S := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hS0]; ring
    have h2 : (J ^ 2 * (A * Real.sqrt S)) ^ 2 ≤ 1 ^ 2 := by rw [hsq]; simpa using hJS
    exact (pow_le_pow_iff_left₀ hq0 zero_le_one (by norm_num)).1 h2
  have hp0 : 0 ≤ J ^ 3 * A⁻¹ := by positivity
  have hp : J ^ 3 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hJ3
  have hbr : c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹ ≤
      8 * cF + 576 := by
    have e : c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹ =
        8 * c2 * (J ^ 2 * (A * Real.sqrt S)) + 576 * (J ^ 3 * A⁻¹) := by ring
    rw [e]
    have h1 : 8 * c2 * (J ^ 2 * (A * Real.sqrt S)) ≤ 8 * cF * 1 :=
      mul_le_mul (by linarith) hq hq0 (by linarith)
    nlinarith
  have hbr0 : 0 ≤ c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹ := by
    positivity
  have hη1 : ηw⁻¹ * (ηw / ηv) ^ 4 ≤ ηs ^ 3 / ηv ^ 4 := by
    have e : ηw⁻¹ * (ηw / ηv) ^ 4 = ηw ^ 3 / ηv ^ 4 := by field_simp
    rw [e]; gcongr
  have hη2 : (ηw / ηv) ^ 4 ≤ (ηs / ηv) ^ 4 := by gcongr
  have hη10 : 0 ≤ ηw⁻¹ * (ηw / ηv) ^ 4 := by positivity
  have e2 : (2 * ηw⁻¹ * (c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹)
        + 4 * W * L * W ^ (-D) * (2 * J) ^ 3) * (ηw / ηv) ^ 4 =
      2 * (c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹) *
          (ηw⁻¹ * (ηw / ηv) ^ 4)
        + 32 * (W * L * W ^ (-D) * J ^ 3) * (ηw / ηv) ^ 4 := by ring
  rw [e2]
  have hcF : 0 ≤ cF := hc0.trans hc
  have t1 : 2 * (c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹) *
      (ηw⁻¹ * (ηw / ηv) ^ 4) ≤ 2 * (8 * cF + 576) * (ηs ^ 3 / ηv ^ 4) :=
    mul_le_mul (by linarith) hη1 hη10 (by positivity)
  have t2 : 32 * (W * L * W ^ (-D) * J ^ 3) * (ηw / ηv) ^ 4 ≤
      32 * (W * L * W ^ (-D) * J ^ 3) * (ηs / ηv) ^ 4 :=
    mul_le_mul_of_nonneg_left hη2 (by positivity)
  nlinarith

/-- **The `J`-power absorption (uses `δ ≤ c/24`).** With `x = N^δ`, `g = N^c`, `x^{24} ≤ g`,
`J ≤ x² R⁴`, `g R^{30} ≤ A` and `r² ≤ R`: `J ≤ A`, `J³ ≤ A`, `J⁴ r³ ≤ A`. -/
theorem J_pow_le {x R r g A J : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R)
    (hxg : x ^ 24 ≤ g) (hA : g * R ^ 30 ≤ A) (hJ0 : 0 ≤ J) (hJ : J ≤ x ^ 2 * R ^ 4) :
    J ≤ A ∧ J ^ 3 ≤ A ∧ J ^ 4 * r ^ 3 ≤ A := by
  have hR0 : 0 ≤ R := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hrR : r ≤ R := by
    have : r ^ 2 ≤ R ^ 2 := hr.trans (by nlinarith)
    exact (pow_le_pow_iff_left₀ hr0 hR0 (by norm_num)).1 this
  have hbig : x ^ 24 * R ^ 30 ≤ A :=
    (mul_le_mul_of_nonneg_right hxg (by positivity)).trans hA
  have hxm : ∀ a b : ℕ, a ≤ 24 → b ≤ 30 → x ^ a * R ^ b ≤ x ^ 24 * R ^ 30 := by
    intro a b ha hb
    exact mul_le_mul (pow_le_pow_right₀ hx ha) (pow_le_pow_right₀ hR hb) (by positivity)
      (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · calc J ≤ x ^ 2 * R ^ 4 := hJ
      _ ≤ x ^ 24 * R ^ 30 := hxm 2 4 (by norm_num) (by norm_num)
      _ ≤ A := hbig
  · calc J ^ 3 ≤ (x ^ 2 * R ^ 4) ^ 3 := pow_le_pow_left₀ hJ0 hJ 3
      _ = x ^ 6 * R ^ 12 := by ring
      _ ≤ x ^ 24 * R ^ 30 := hxm 6 12 (by norm_num) (by norm_num)
      _ ≤ A := hbig
  · calc J ^ 4 * r ^ 3 ≤ (x ^ 2 * R ^ 4) ^ 4 * R ^ 3 :=
          mul_le_mul (pow_le_pow_left₀ hJ0 hJ 4) (pow_le_pow_left₀ hr0 hrR 3) (by positivity)
            (by positivity)
      _ = x ^ 8 * R ^ 19 := by ring
      _ ≤ x ^ 24 * R ^ 30 := hxm 8 19 (by norm_num) (by norm_num)
      _ ≤ A := hbig

end QVSum

/-! ## The rate `Qd` and the constant -/

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `J w := N^{2ε} · thr w = N^{2ε} N^δ (η_s/η_w)^4` (`RBM.Step2.thr`, Step2.lean:626). -/
noncomputable def qvJ (E : ℝ) (s : ℕ → ℝ) (δ ε : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N w

/-- **The per-time rate `Qd w`**: verbatim the right-hand-side rate of T1497
(`RBM.Gauss.highProb_quadVar_diagShape_of_jS`, `Gauss/Step2QVEvent.lean:194`) with `jG` replaced
by `J w = qvJ …`, i.e. `diagShape'` with the near-field indicator dropped and the common
`tailT²` factored out:
`diagNearRate(ℓ_w, ℓ_s, η_w) + 2 nearEpsilon(W, L, ℓ_w, η_w, D, J w)
  + diagFarRate(ℓ_w, η_w, D, J w, sDet(w, ℓ_s))`. -/
noncomputable def Qd (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (δ ε D : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  APrimeQVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w)
    + 2 * EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D
        (qvJ E s δ ε N w)
    + APrimeQVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D (qvJ E s δ ε N w)
        (EarlyQVRateEv.sDet B E N w (B.ell N (s N)))

/-- The explicit constant of (T2′): `1200 / Im m(E)`; it depends only on `E`. -/
noncomputable def qvSumConst (E : ℝ) : ℝ := 1200 / (mE E).im

end Defs

namespace QVSum

/-- **Pointwise domination of the whole summand** at one size parameter `N`: for
`s ≤ w ≤ v ≤ t < 1`,
`Qd(w) ((1-w)/(1-v))^4 ≤ (34 N^κ + 1152) η_s³/η_v⁴ + 3 (η_s/η_v)^4`. -/
theorem Qd_mul_le {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℝ} (hE : |E| < 2)
    {s : ℕ → ℝ} {δ ε D c κ : ℝ} {N : ℕ} {t w v : ℝ}
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsw : s N ≤ w) (hwv : w ≤ v) (hvt : v ≤ t)
    (ht1 : t < 1)
    (hreg : (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 ≤ B.scale E N t)
    (hδ0 : 0 ≤ δ) (hδc : 24 * δ ≤ c) (hεδ : 2 * ε ≤ δ) (hD : 60 ≤ D)
    (hWbig : Real.exp ((4 * D) ^ 2 + 4) ≤ (B.W N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N) (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hcN : ∀ ℓ : ℝ, 1 ≤ ℓ → Lemma57.cNear2 (B.W N : ℝ) ℓ ≤ (N : ℝ) ^ κ) :
    Qd B E s δ ε D N w * ((1 - w) / (1 - v)) ^ 4 ≤
      (34 * (N : ℝ) ^ κ + 1152) * (etaT E (s N) ^ 3 / etaT E v ^ 4)
        + 3 * (etaT E (s N) / etaT E v) ^ 4 := by
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hwt : w ≤ t := hwv.trans hvt
  have hw1 : w < 1 := hwt.trans_lt ht1
  have hv1 : v < 1 := hvt.trans_lt ht1
  have hs1 : s N < 1 := hsw.trans_lt hw1
  have hw0 : 0 ≤ w := hs0.trans hsw
  have hηw : 0 < etaT E w := Step2.etaT_pos' hE hw1
  have hηv : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hηt : 0 < etaT E t := Step2.etaT_pos' hE ht1
  have hηs : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hηws : etaT E w ≤ etaT E (s N) := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηtw : etaT E t ≤ etaT E w := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηw1 : etaT E w ≤ 1 := by
    simp only [Step2.etaT_eq]
    calc (1 - w) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
      _ = 1 := one_mul 1
  have hratio : (1 - w) / (1 - v) = etaT E w / etaT E v := (Step2.etaT_ratio hE w v).symm
  -- scales
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hL0 : (0 : ℝ) < (B.L N : ℝ) := by exact_mod_cast (show 0 < B.L N by omega)
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := B.one_le_W N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hℓw1 : 1 ≤ B.ell N w := one_le_ellHat_of_nonneg hL1 hw0 hw1
  have hℓw0 : 0 < B.ell N w := by linarith
  have hℓtL : B.ell N t ≤ (B.L N : ℝ) := by
    simp only [Band.ell, ellHat]; exact min_le_right _ _
  have hℓwL : B.ell N w ≤ (B.L N : ℝ) := by
    simp only [Band.ell, ellHat]; exact min_le_right _ _
  have hℓt0 : 0 < B.ell N t := Step3.ellHat_pos_of_lt_one hL1 ht1
  -- (K1): `r_w² η_w ≤ η_s`
  have hK1 : (B.ell N w / B.ell N (s N)) ^ 2 * etaT E w ≤ etaT E (s N) := by
    have hK := ellHat_sq_mul_one_sub_le (B.L N) hw1 hsw
    change B.ell N w ^ 2 * (1 - w) ≤ B.ell N (s N) ^ 2 * (1 - s N) at hK
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simp only [Step2.etaT_eq]
    calc B.ell N w ^ 2 * ((1 - w) * (mE E).im) = (B.ell N w ^ 2 * (1 - w)) * (mE E).im := by
          ring
      _ ≤ (B.ell N (s N) ^ 2 * (1 - s N)) * (mE E).im := mul_le_mul_of_nonneg_right hK hm0.le
      _ = (1 - s N) * (mE E).im * B.ell N (s N) ^ 2 := by ring
  -- the scale `A_w` and its lower bound from `hreg`
  have hAdef : B.scale E N w = (B.W N : ℝ) * B.ell N w * etaT E w := rfl
  have hA0 : 0 < B.scale E N w := by rw [hAdef]; positivity
  have hAtw : B.scale E N t ≤ B.scale E N w :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hw1.le) (Set.mem_Iic.2 ht1.le) hwt
  set Rw : ℝ := etaT E (s N) / etaT E w with hRw
  set Rt : ℝ := etaT E (s N) / etaT E t with hRt
  have hRw1 : 1 ≤ Rw := (one_le_div hηw).2 hηws
  have hRwt : Rw ≤ Rt := div_le_div_of_nonneg_left hηs.le hηt hηtw
  have hRt1 : 1 ≤ Rt := hRw1.trans hRwt
  have hg1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1 (by linarith)
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have hxg : ((N : ℝ) ^ δ) ^ 24 ≤ (N : ℝ) ^ c := by
    rw [Step2.natCast_rpow_pow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hgA : (N : ℝ) ^ c * Rw ^ 30 ≤ B.scale E N w :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hRwt 30)
      (by linarith)).trans (hreg.trans hAtw)
  have hAt1 : 1 ≤ B.scale E N t := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ c * Rt ^ 30 := one_le_mul_of_one_le_of_one_le hg1 (one_le_pow₀ hRt1)
    exact this.trans hreg
  -- `J`
  set J : ℝ := qvJ E s δ ε N w with hJdef
  have hJeq : J = (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * Rw ^ 4) := rfl
  have hJ0 : 0 ≤ J := by rw [hJeq]; positivity
  have hJx : J ≤ ((N : ℝ) ^ δ) ^ 2 * Rw ^ 4 := by
    have h2e : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
    rw [hJeq]
    calc (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * Rw ^ 4) ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * Rw ^ 4) :=
          mul_le_mul_of_nonneg_right h2e (by positivity)
      _ = ((N : ℝ) ^ δ) ^ 2 * Rw ^ 4 := by ring
  have hr0 : 0 ≤ B.ell N w / B.ell N (s N) := by positivity
  have hr : (B.ell N w / B.ell N (s N)) ^ 2 ≤ Rw := by
    rw [hRw, le_div_iff₀ hηw]; exact hK1
  obtain ⟨hJA, hJ3, hJ4⟩ := J_pow_le hx1 hRw1 hr0 hr hxg hgA hJ0 hJx
  have hS0 : 0 ≤ EarlyQVRateEv.sDet B E N w (B.ell N (s N)) :=
    EarlyQVRateEv.sDet_nonneg B E N hw0 hw1 hℓs
  have hS : J ^ 4 * B.scale E N w ^ 2 * EarlyQVRateEv.sDet B E N w (B.ell N (s N)) ≤ 1 := by
    have e : J ^ 4 * B.scale E N w ^ 2 * EarlyQVRateEv.sDet B E N w (B.ell N (s N)) =
        J ^ 4 * (B.ell N w / B.ell N (s N)) ^ 3 / B.scale E N w := by
      unfold EarlyQVRateEv.sDet
      field_simp
    rw [e]
    exact div_le_one_of_le₀ hJ4 hA0.le
  -- `W` is large
  have hlog : (4 * D) ^ 2 + 4 ≤ Real.log (B.W N : ℝ) := (Real.le_log_iff_exp_le hW0).2 hWbig
  have hD2 : 0 ≤ (4 * D) ^ 2 := sq_nonneg _
  have hWe : Real.exp 1 ≤ (B.W N : ℝ) :=
    (Real.exp_le_exp.2 (by linarith)).trans hWbig
  have hW6 : (6 : ℝ) ≤ (B.W N : ℝ) := by
    have := Real.add_one_le_exp ((4 * D) ^ 2 + 4)
    have h1 : (1 : ℝ) ≤ (4 * D) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  -- near term
  have hnear := near_mul_le hℓs hℓw0.le hηw hηv hηws hK1
    (Lemma57.cNear2_nonneg hW1 hℓw0) (hcN _ hℓw1)
  -- far terms
  have hcF : Lemma57.cFar2 (B.W N : ℝ) (B.ell N w) ≤ 2 * (N : ℝ) ^ κ :=
    (cFar2_le_two_cNear2 hWe hℓw0).trans (by linarith [hcN _ hℓw1])
  have hfar := far_mul_le (W := (B.W N : ℝ)) (L := (B.L N : ℝ)) (D := D) hW0 hL0.le hηw hηv hηws
    hJ0 hA0 hS0 hJ3 hS (Lemma57.cFar2_nonneg hW1 hℓw0) hcF
  have hfar3 : 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) ≤ 1 := by
    have hAN : B.scale E N w ≤ N := by
      rw [hAdef]
      calc (B.W N : ℝ) * B.ell N w * etaT E w ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 := by gcongr
        _ ≤ N := by linarith
    have hJ3N : J ^ 3 ≤ N := hJ3.trans hAN
    have hWLJ : (B.W N : ℝ) * (B.L N : ℝ) * J ^ 3 ≤ (B.W N : ℝ) ^ 4 := by
      calc (B.W N : ℝ) * (B.L N : ℝ) * J ^ 3 ≤ (N : ℝ) * N :=
            mul_le_mul hWL hJ3N (by positivity) (by linarith)
        _ ≤ (B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2 :=
            mul_le_mul hNW hNW (by linarith) (by positivity)
        _ = (B.W N : ℝ) ^ 4 := by ring
    have hWD : (B.W N : ℝ) ^ (-D) ≤ ((B.W N : ℝ) ^ 6)⁻¹ := by
      calc (B.W N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-(6 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = ((B.W N : ℝ) ^ 6)⁻¹ := by
            rw [Real.rpow_neg hW0.le]; norm_cast
    have hWD0 : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    have e : 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) =
        32 * ((B.W N : ℝ) * (B.L N : ℝ) * J ^ 3) * (B.W N : ℝ) ^ (-D) := by ring
    rw [e]
    calc 32 * ((B.W N : ℝ) * (B.L N : ℝ) * J ^ 3) * (B.W N : ℝ) ^ (-D)
        ≤ 32 * (B.W N : ℝ) ^ 4 * ((B.W N : ℝ) ^ 6)⁻¹ :=
          mul_le_mul (by linarith) hWD hWD0 (by positivity)
      _ = 32 / (B.W N : ℝ) ^ 2 := by field_simp
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          have h36 : (6 : ℝ) ^ 2 ≤ (B.W N : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hW6 2
          norm_num at h36
          linarith
  -- nearEpsilon
  have hnE : EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J ≤
      (B.W N : ℝ)⁻¹ := by
    have hηt' : (N : ℝ)⁻¹ ≤ etaT E w := by
      have hNt : 1 ≤ (N : ℝ) * etaT E t := by
        calc (1 : ℝ) ≤ B.scale E N t := hAt1
          _ = (B.W N : ℝ) * B.ell N t * etaT E t := rfl
          _ ≤ (B.W N : ℝ) * (B.L N : ℝ) * etaT E t := by gcongr
          _ ≤ N * etaT E t := by gcongr
      have : (N : ℝ)⁻¹ ≤ etaT E t := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]; linarith
      exact this.trans hηtw
    have hA1 : 1 ≤ (B.W N : ℝ) * B.ell N w * etaT E w := hAt1.trans hAtw
    have hAN : (B.W N : ℝ) * B.ell N w * etaT E w ≤ N := by
      calc (B.W N : ℝ) * B.ell N w * etaT E w ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 := by gcongr
        _ ≤ N := by linarith
    have hJN : J ≤ (N : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]; exact hJA.trans (by rw [hAdef]; exact hAN)
    exact EEDef.nearEpsilon_le_inv hWe hL0 hℓw0 hηw hN1 zero_le_one hJ0 (by linarith) hηt' hA1
      hAN hWL hNW hJN (by linarith) (by linarith)
  -- assembly
  have hP0 : 0 ≤ (etaT E w / etaT E v) ^ 4 := by positivity
  have hPY : (etaT E w / etaT E v) ^ 4 ≤ (etaT E (s N) / etaT E v) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hηws hηv.le) 4
  have hWinv : (B.W N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hnEP : EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J *
      (etaT E w / etaT E v) ^ 4 ≤ (etaT E (s N) / etaT E v) ^ 4 :=
    calc EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J *
          (etaT E w / etaT E v) ^ 4 ≤ (B.W N : ℝ)⁻¹ * (etaT E w / etaT E v) ^ 4 :=
          mul_le_mul_of_nonneg_right hnE hP0
      _ ≤ 1 * (etaT E (s N) / etaT E v) ^ 4 := mul_le_mul hWinv hPY hP0 zero_le_one
      _ = (etaT E (s N) / etaT E v) ^ 4 := one_mul _
  have hY0 : 0 ≤ (etaT E (s N) / etaT E v) ^ 4 := by positivity
  have hfar3Y : 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) *
      (etaT E (s N) / etaT E v) ^ 4 ≤ (etaT E (s N) / etaT E v) ^ 4 :=
    calc 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) *
          (etaT E (s N) / etaT E v) ^ 4 ≤ 1 * (etaT E (s N) / etaT E v) ^ 4 :=
          mul_le_mul_of_nonneg_right hfar3 hY0
      _ = (etaT E (s N) / etaT E v) ^ 4 := one_mul _
  have hX0 : 0 ≤ etaT E (s N) ^ 3 / etaT E v ^ 4 := by positivity
  have hnear' : APrimeQVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w) *
      (etaT E w / etaT E v) ^ 4 ≤ 2 * (N : ℝ) ^ κ * (etaT E (s N) ^ 3 / etaT E v ^ 4) := by
    unfold APrimeQVEndpoint.diagNearRate; exact hnear
  have hfar' : APrimeQVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D J
        (EarlyQVRateEv.sDet B E N w (B.ell N (s N))) * (etaT E w / etaT E v) ^ 4 ≤
      (16 * (2 * (N : ℝ) ^ κ) + 1152) * (etaT E (s N) ^ 3 / etaT E v ^ 4) +
        32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) *
          (etaT E (s N) / etaT E v) ^ 4 := by
    unfold APrimeQVEndpoint.diagFarRate; exact hfar
  have e1 : Qd B E s δ ε D N w * (etaT E w / etaT E v) ^ 4 =
      APrimeQVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w) *
          (etaT E w / etaT E v) ^ 4
        + 2 * (EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J *
          (etaT E w / etaT E v) ^ 4)
        + APrimeQVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D J
          (EarlyQVRateEv.sDet B E N w (B.ell N (s N))) * (etaT E w / etaT E v) ^ 4 := by
    unfold Qd; rw [← hJdef]; ring
  rw [hratio, e1]
  linarith

/-- The final scalar arithmetic of (T2′): with `a = N^κ ≥ 1`, `b = 1/Im m ≥ 1`, `Y = R⁴ ≥ 0`
and `σ = 1 - s ≤ 1`. -/
theorem final_arith {a b Y σ : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hY : 0 ≤ Y) (hσ1 : σ ≤ 1) :
    (34 * a + 1152) * (b * Y) + 3 * σ * Y ≤ 1200 * b * a * (Y + 1) := by
  have hbY : 0 ≤ b * Y := by positivity
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  have h1 : (34 * a + 1152) * (b * Y) ≤ 1186 * a * (b * Y) :=
    mul_le_mul_of_nonneg_right (by linarith) hbY
  have h2 : σ * Y ≤ a * (b * Y) := by
    calc σ * Y ≤ 1 * Y := mul_le_mul_of_nonneg_right hσ1 hY
      _ ≤ (a * b) * Y := mul_le_mul_of_nonneg_right hab hY
      _ = a * (b * Y) := by ring
  have h3 : 0 ≤ a * b := by positivity
  nlinarith

/-- Every rate is non-negative, so `Qd ≥ 0` on `[0,1)`. -/
theorem Qd_nonneg {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℝ} (hE : |E| < 2)
    {s : ℕ → ℝ} {δ ε D : ℝ} {N : ℕ} {w : ℝ} (hs1 : s N < 1) (hw0 : 0 ≤ w)
    (hw1 : w < 1) : 0 ≤ Qd B E s δ ε D N w := by
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := B.one_le_W N
  have hℓw0 : 0 < B.ell N w := Step3.ellHat_pos_of_lt_one hL1 hw1
  have hℓs0 : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hηw : 0 < etaT E w := Step2.etaT_pos' hE hw1
  have hJ0 : 0 ≤ qvJ E s δ ε N w := by
    unfold qvJ Step2.thr; positivity
  have h1 := Lemma57.cNear2_nonneg hW1 hℓw0
  have h2 := Lemma57.cFar2_nonneg hW1 hℓw0
  have hS0 : 0 ≤ EarlyQVRateEv.sDet B E N w (B.ell N (s N)) :=
    EarlyQVRateEv.sDet_nonneg B E N hw0 hw1 hℓs0
  have hN : 0 ≤ APrimeQVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w) := by
    unfold APrimeQVEndpoint.diagNearRate
    exact mul_nonneg (mul_nonneg (by positivity) h1) (by positivity)
  have hnE : 0 ≤ EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D
      (qvJ E s δ ε N w) := by
    unfold EEDef.nearEpsilon; positivity
  have hF : 0 ≤ APrimeQVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D (qvJ E s δ ε N w)
      (EarlyQVRateEv.sDet B E N w (B.ell N (s N))) := by
    unfold APrimeQVEndpoint.diagFarRate
    have hJ3 : 0 ≤ (2 * qvJ E s δ ε N w) ^ 3 := pow_nonneg (by linarith) 3
    have hWD : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
    refine add_nonneg (mul_nonneg (by positivity) (add_nonneg ?_ ?_)) ?_
    · exact mul_nonneg h2 (by positivity)
    · exact mul_nonneg (mul_nonneg (by norm_num) hJ3) (by positivity)
    · exact mul_nonneg (by positivity) hJ3
  unfold Qd
  linarith

end QVSum

open QVSum in
/-- **(T2′) `RBM.Gauss.Grid.qv_time_sum_le`** — (5.44) on the grid, label-free, with the
propagator factor and endpoint `u_k`.

Hypotheses: `|E| < 2`, `0 ≤ s ≤ t < 1`, `Cond272`, step2's `hreg` with gain `c > 0`,
`0 < δ ≤ c/24`, `0 ≤ ε`, `2ε ≤ δ`, `60 ≤ D`. Conclusion: for every `κ > 0`, eventually in `N`,
uniformly in the endpoint `u_* = T N ∈ [s N, t N]`, the number of steps `K = Kq N ≥ 1`, and
every `k ≤ K`, with `u_j = Grid.time s T Kq N j = s N + j Δ`, `Δ = Grid.step s T Kq N`:
`Λ_k = Σ_{j<k} Δ · Qd(u_j) · ((1-u_j)/(1-u_k))^4 ≤ (1200/Im m) · N^κ · ((η_s/η_{u_k})^4 + 1)`.

The exponent `4` is exact. No mesh condition on `Δ` is needed (the bound is a pointwise
domination of the whole summand followed by `Σ_{j<k} Δ = u_k - s`). `Cond272` and `0 ≤ ε` are
listed by the ticket but not used (`Cond272` follows from `hreg`, `RBM.Step2.cond272_of_strict`);
`0 < c` follows from `0 < δ ≤ c/24`. -/
theorem qv_time_sum_le {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (_hcond : Cond272 B E s t) {c : ℝ} (_hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 24) (_hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hD : 60 ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N →
        ∑ j ∈ Finset.range k, step s T Kq N * Qd B E s δ ε D N (time s T Kq N j) *
            ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4
          ≤ qvSumConst E * (N : ℝ) ^ κ *
              ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 + 1) := by
  intro κ hκ
  filter_upwards [eventually_cNear2_le_rpow B hκ,
    (Step2.tendsto_W B).eventually_ge_atTop (Real.exp ((4 * D) ^ 2 + 4)),
    hreg, B.dim, Step2.eventually_le_W_sq B, eventually_ge_atTop 1]
    with N hcN hWbig hregN hdim hNW hN1 T Kq hsT hTt hK k hk
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hKpos : (0 : ℝ) < (Kq N : ℝ) := by exact_mod_cast hK
  have hΔ0 : 0 ≤ step s T Kq N := div_nonneg (by linarith) hKpos.le
  have hKΔ : (Kq N : ℝ) * step s T Kq N = T N - s N := by
    unfold step; field_simp
  have hjΔ : ∀ j : ℕ, j ≤ k → (j : ℝ) * step s T Kq N ≤ T N - s N := by
    intro j hj
    have : (j : ℝ) ≤ Kq N := by exact_mod_cast hj.trans hk
    rw [← hKΔ]; exact mul_le_mul_of_nonneg_right this hΔ0
  have hvt : time s T Kq N k ≤ t N := by
    unfold time; linarith [hjΔ k le_rfl]
  have hsv : s N ≤ time s T Kq N k := by
    unfold time; have : 0 ≤ (k : ℝ) * step s T Kq N := by positivity
    linarith
  have hmem : ∀ j ∈ Finset.range k, s N ≤ time s T Kq N j ∧ time s T Kq N j ≤ time s T Kq N k := by
    intro j hj
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.1 hj).le
    unfold time
    constructor
    · have : 0 ≤ (j : ℝ) * step s T Kq N := by positivity
      linarith
    · have := mul_le_mul_of_nonneg_right hjk hΔ0
      linarith
  set M : ℝ := (34 * (N : ℝ) ^ κ + 1152) *
      (etaT E (s N) ^ 3 / etaT E (time s T Kq N k) ^ 4)
      + 3 * (etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 with hMdef
  have hv1 : time s T Kq N k < 1 := hvt.trans_lt (ht1 N)
  have hηv : 0 < etaT E (time s T Kq N k) := Step2.etaT_pos' hE hv1
  have hηs : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hterm : ∀ j ∈ Finset.range k,
      step s T Kq N * Qd B E s δ ε D N (time s T Kq N j) *
          ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4 ≤ step s T Kq N * M := by
    intro j hj
    obtain ⟨h1, h2⟩ := hmem j hj
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (Qd_mul_le B hE hN1' (hs0 N) h1 h2 hvt (ht1 N) hregN hδ0.le (by linarith) hεδ hD hWbig
        hWL hNW hcN) hΔ0
  have hkΔ : (k : ℝ) * step s T Kq N ≤ 1 - s N := by
    have := hjΔ k le_rfl
    linarith [hTt, ht1 N]
  have hXY : (1 - s N) * (etaT E (s N) ^ 3 / etaT E (time s T Kq N k) ^ 4) =
      (mE E).im⁻¹ * (etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 := by
    have e : etaT E (s N) = (1 - s N) * (mE E).im := rfl
    rw [e]; field_simp
  have hb : 1 ≤ (mE E).im⁻¹ := (one_le_inv₀ hm0).2 hm1
  have ha : 1 ≤ (N : ℝ) ^ κ := Real.one_le_rpow hN1' hκ.le
  calc ∑ j ∈ Finset.range k, step s T Kq N * Qd B E s δ ε D N (time s T Kq N j) *
          ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4
      ≤ ∑ _j ∈ Finset.range k, step s T Kq N * M := Finset.sum_le_sum hterm
    _ = (k : ℝ) * step s T Kq N * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ (1 - s N) * M := mul_le_mul_of_nonneg_right hkΔ hM0
    _ = (34 * (N : ℝ) ^ κ + 1152) *
          ((mE E).im⁻¹ * (etaT E (s N) / etaT E (time s T Kq N k)) ^ 4)
          + 3 * (1 - s N) * (etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 := by
        rw [hMdef, ← hXY]; ring
    _ ≤ 1200 * (mE E).im⁻¹ * (N : ℝ) ^ κ *
          ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 + 1) :=
        final_arith ha hb (by positivity) (by linarith [hs0 N])
    _ = qvSumConst E * (N : ℝ) ^ κ *
          ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 + 1) := by
        unfold qvSumConst; ring

open QVSum in
/-- **Corollary `qv_time_sum_le'`**: the same bound for the sum with the propagator factor
`((1 - u_{j+1})/(1 - u_k))^4` produced by `qv_conv_le` (T1509/T1512). For `j < k`,
`0 ≤ 1 - u_{j+1} ≤ 1 - u_j`, and `Δ Qd(u_j) ≥ 0`, so this sum is dominated termwise by `Λ_k`. -/
theorem qv_time_sum_le' {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 24) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hD : 60 ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N →
        ∑ j ∈ Finset.range k, step s T Kq N * Qd B E s δ ε D N (time s T Kq N j) *
            ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 4
          ≤ qvSumConst E * (N : ℝ) ^ κ *
              ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 4 + 1) := by
  intro κ hκ
  filter_upwards [qv_time_sum_le B hE hs0 hst ht1 hcond hc0 hreg hδ0 hδc hε0 hεδ hD κ hκ]
    with N hN T Kq hsT hTt hK k hk
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (hN T Kq hsT hTt hK k hk)
  have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
  have hKpos : (0 : ℝ) < (Kq N : ℝ) := by exact_mod_cast hK
  have hΔ0 : 0 ≤ step s T Kq N := div_nonneg (by linarith) hKpos.le
  have hKΔ : (Kq N : ℝ) * step s T Kq N = T N - s N := by
    unfold step; field_simp
  have hkΔ : (k : ℝ) * step s T Kq N ≤ T N - s N := by
    have : (k : ℝ) ≤ Kq N := by exact_mod_cast hk
    rw [← hKΔ]; exact mul_le_mul_of_nonneg_right this hΔ0
  have hjk' : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hjk
  have hv1 : time s T Kq N k < 1 := by
    unfold time; linarith [ht1 N]
  have hj1 : time s T Kq N j ≤ time s T Kq N (j + 1) := by
    unfold time; push_cast; nlinarith
  have hj1k : time s T Kq N (j + 1) ≤ time s T Kq N k := by
    unfold time; have := mul_le_mul_of_nonneg_right hjk' hΔ0; linarith
  have hj0 : 0 ≤ time s T Kq N j := by
    unfold time; have : 0 ≤ (j : ℝ) * step s T Kq N := by positivity
    linarith [hs0 N]
  have hjlt1 : time s T Kq N j < 1 := by linarith
  have hQ : 0 ≤ Qd B E s δ ε D N (time s T Kq N j) :=
    Qd_nonneg B hE ((hst N).trans_lt (ht1 N)) hj0 hjlt1
  have hden : 0 < 1 - time s T Kq N k := by linarith
  have hfac : ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 4 ≤
      ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4 :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hden.le)
      (div_le_div_of_nonneg_right (by linarith) hden.le) 4
  exact mul_le_mul_of_nonneg_left hfac (mul_nonneg hΔ0 hQ)

/-! ## Joint satisfiability of the hypotheses of (T2′) -/

/-- **Nondegenerate witness for the hypotheses of `qv_time_sum_le`, for every band `B`.**
`E = 0`, `s = 0`, `t N = 1 - (N+1)^{-1/200}` (a genuine window: `s N < t N` for `N ≥ 1`, and
`η_s/η_t = (N+1)^{1/200} → ∞`), `c = 1/4`, `δ = c/24 = 1/96`, `ε = δ/2`, `D = 60`. -/
theorem qv_time_sum_le_hyps_witness {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) :
    ∃ (E : ℝ) (s t : ℕ → ℝ) (c δ ε D : ℝ),
      |E| < 2 ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      (∀ N : ℕ, 1 ≤ N → s N < t N) ∧
      (∀ N : ℕ, etaT E (s N) / etaT E (t N) = ((N : ℝ) + 1) ^ (1 / 200 : ℝ)) ∧
      Cond272 B E s t ∧ 0 < c ∧
      (∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N)) ∧
      0 < δ ∧ δ ≤ c / 24 ∧ 0 ≤ ε ∧ 2 * ε ≤ δ ∧ 60 ≤ D := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hm0 : 0 < (mE 0).im := mE_im_pos hE
  set a : ℝ := 1 / 200 with ha
  let p : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ (-a)
  have hq1 : ∀ N : ℕ, (1 : ℝ) ≤ (N : ℝ) + 1 := fun N => by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hp0 : ∀ N, 0 < p N := fun N => Real.rpow_pos_of_pos (by linarith [hq1 N]) _
  have hp1 : ∀ N, p N ≤ 1 := fun N =>
    Real.rpow_le_one_of_one_le_of_nonpos (hq1 N) (by norm_num [ha])
  have hpinv : ∀ N, (p N)⁻¹ = ((N : ℝ) + 1) ^ a := fun N => by
    simp only [p]; rw [Real.rpow_neg (by linarith [hq1 N]), inv_inv]
  let t : ℕ → ℝ := fun N => 1 - p N
  have ht1 : ∀ N, t N < 1 := fun N => by simp only [t]; linarith [hp0 N]
  have hst : ∀ N, (0 : ℝ) ≤ t N := fun N => by simp only [t]; linarith [hp1 N]
  have hR : ∀ N : ℕ, etaT 0 ((fun _ => (0 : ℝ)) N) / etaT 0 (t N) = ((N : ℝ) + 1) ^ a := by
    intro N
    rw [Step2.etaT_ratio hE]
    simp only [t, sub_zero, sub_sub_cancel, one_div]
    exact hpinv N
  -- the gained (2.72)
  have hreg : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 / 4 : ℝ) * (etaT 0 ((fun _ => (0 : ℝ)) N) / etaT 0 (t N)) ^ 30 ≤
        B.scale 0 N (t N) := by
    have hev := eventually_le_rpow (2 / (mE 0).im) (by norm_num : (0 : ℝ) < 19 / 200)
    filter_upwards [hev, B.bandwidth, eventually_ge_atTop 1] with N hevN hbw hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have hq0 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    rw [hR N]
    -- `W ≥ N^{1/2}`
    have hW : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (B.W N : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [B.c_pos])).trans hbw
    -- `(N+1)^{31a} ≤ 2 N^{31a}`
    have h31 : ((N : ℝ) + 1) ^ (31 * a) ≤ 2 * (N : ℝ) ^ (31 * a) := by
      have h2N : (N : ℝ) + 1 ≤ 2 * N := by linarith
      calc ((N : ℝ) + 1) ^ (31 * a) ≤ (2 * (N : ℝ)) ^ (31 * a) :=
            Real.rpow_le_rpow hq0.le h2N (by norm_num [ha])
        _ = (2 : ℝ) ^ (31 * a) * (N : ℝ) ^ (31 * a) := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 2 * (N : ℝ) ^ (31 * a) := by
            gcongr
            calc (2 : ℝ) ^ (31 * a) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [ha])
              _ = 2 := Real.rpow_one 2
    -- the key inequality `N^{1/4} (N+1)^{31a} ≤ Im m · W`
    have hkey : (N : ℝ) ^ (1 / 4 : ℝ) * ((N : ℝ) + 1) ^ (31 * a) ≤ (mE 0).im * (B.W N : ℝ) := by
      have hsplit : (N : ℝ) ^ (1 / 2 : ℝ) =
          (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (31 * a) * (N : ℝ) ^ (19 / 200 : ℝ) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num [ha]
      have h2m : 2 ≤ (mE 0).im * (N : ℝ) ^ (19 / 200 : ℝ) := by
        rw [div_le_iff₀ hm0] at hevN; linarith
      have hP : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (31 * a) := by positivity
      calc (N : ℝ) ^ (1 / 4 : ℝ) * ((N : ℝ) + 1) ^ (31 * a)
          ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (2 * (N : ℝ) ^ (31 * a)) :=
            mul_le_mul_of_nonneg_left h31 (by positivity)
        _ = 2 * ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (31 * a)) := by ring
        _ ≤ ((mE 0).im * (N : ℝ) ^ (19 / 200 : ℝ)) *
              ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (31 * a)) := mul_le_mul_of_nonneg_right h2m hP
        _ = (mE 0).im * (N : ℝ) ^ (1 / 2 : ℝ) := by rw [hsplit]; ring
        _ ≤ (mE 0).im * (B.W N : ℝ) := mul_le_mul_of_nonneg_left hW hm0.le
    -- unfold the scale at `t N`
    have hℓ1 : 1 ≤ B.ell N (t N) := one_le_ellHat_of_nonneg (B.one_le_L N) (hst N) (ht1 N)
    have hη : etaT 0 (t N) = p N * (mE 0).im := by
      rw [Step2.etaT_eq]; simp only [t, sub_sub_cancel]
    have hpow : (((N : ℝ) + 1) ^ a) ^ 30 * ((N : ℝ) + 1) ^ a = ((N : ℝ) + 1) ^ (31 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]; norm_num
    have hpa : p N * ((N : ℝ) + 1) ^ a = 1 := by
      rw [← hpinv N]; exact mul_inv_cancel₀ (hp0 N).ne'
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    change (N : ℝ) ^ (1 / 4 : ℝ) * (((N : ℝ) + 1) ^ a) ^ 30 ≤
      (B.W N : ℝ) * B.ell N (t N) * etaT 0 (t N)
    rw [hη]
    have hqa : 0 < ((N : ℝ) + 1) ^ a := Real.rpow_pos_of_pos hq0 _
    rw [← mul_le_mul_iff_of_pos_right hqa]
    calc (N : ℝ) ^ (1 / 4 : ℝ) * (((N : ℝ) + 1) ^ a) ^ 30 * ((N : ℝ) + 1) ^ a
        = (N : ℝ) ^ (1 / 4 : ℝ) * ((N : ℝ) + 1) ^ (31 * a) := by rw [mul_assoc, hpow]
      _ ≤ (mE 0).im * (B.W N : ℝ) := hkey
      _ = (B.W N : ℝ) * 1 * ((p N * ((N : ℝ) + 1) ^ a) * (mE 0).im) := by rw [hpa]; ring
      _ ≤ (B.W N : ℝ) * B.ell N (t N) * ((p N * ((N : ℝ) + 1) ^ a) * (mE 0).im) := by
          gcongr
      _ = (B.W N : ℝ) * B.ell N (t N) * (p N * (mE 0).im) * ((N : ℝ) + 1) ^ a := by ring
  have hs0 : ∀ N : ℕ, (0 : ℝ) ≤ (fun _ => (0 : ℝ)) N := fun _ => le_rfl
  have hcond : Cond272 B 0 (fun _ => (0 : ℝ)) t :=
    Step2.cond272_of_strict hE hst ht1 (by norm_num : (0 : ℝ) < 1 / 4) hreg
  refine ⟨0, fun _ => 0, t, 1 / 4, 1 / 96, 1 / 192, 60, hE, hs0, hst, ht1, ?_, hR, hcond,
    by norm_num, hreg, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl⟩
  intro N hN
  have hN' : (1 : ℝ) < (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have : p N < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN' (by norm_num [ha])
  simp only [t]; linarith

end RBM.Gauss.Grid

end
