/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.NearFieldRemainder
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Hierarchy.Lemma57
import RBM1D.Hierarchy.Step2
import RBM1D.Flow.FlowFamiliesCore

/-!
# (5.44) on the grid: the label-free time sum `Λ_k`

Paper (5.44), in the shape the label-weighted Azuma bound `stopped_duhamel_azuma_union`
consumes.

The upstream `qv_conv_le` delivers per-step coefficients
`c k b j = Δ (√Q_j r_{j,k}² xiK T_{u_k}(b))²` with `r_{j,k} = (1 - u_{j+1})/(1 - u_k)`, so
`Σ_j c k b j = xiK² T_{u_k}(b)² Λ_k` with the label-free scalar `Λ_k`. This file bounds `Λ_k`.

## Main definitions

* `qvJ E s δ ε N w = N^{2ε} · Step2.thr E s δ N w = N^{2ε} N^δ (η_s/η_w)^4`.
* `Qd B E s δ ε D N w`: the per-time rate of the quadratic-variation event of
  `Gauss/Step2QVEvent.lean` with `jG` replaced by `qvJ`, i.e. `diagShape'` with the near-field
  indicator dropped and the common `tailT²` factored out.
* `qvSumConst E = 1200 / Im m(E)`.

## Main results

* `near_mul_le`, `far_mul_le`, `pow5_mul_pow3_le`, `final_arith`, `Qd_nonneg`: the pointwise
  domination of the summand along the route below, towards the bound (for `κ > 0`, eventually in
  `N`, uniformly in the endpoint `u_* ∈ [s,t]`, the step count `K ≥ 1` and `k ≤ K`)
  `Σ_{j<k} Δ Qd(u_j) ((1-u_j)/(1-u_k))^4 ≤ qvSumConst E · N^κ · ((η_s/η_{u_k})^4 + 1)`.
  **The exponent 4 is attained exactly.**
* `ellHat_mul_sqrt_one_sub_le`, `ellHat_sq_mul_one_sub_le`, `cFar2_le_two_cNear2`,
  `eventually_cNear2_le_rpow`: the cap-robust ratio bound and the stretched-exponential
  absorption.

## Route

The whole summand is dominated pointwise, for `s ≤ w ≤ v = u_k`, by
`(34 N^κ + 1152) η_s³/η_v⁴ + 3 (η_s/η_v)^4`; then `Σ_{j<k} Δ = u_k - s ≤ 1 - s = η_s/Im m`.
The near term is the sharp one: with `r_w = ℓ_w/ℓ_s` kept at the *same* time as `η_w`, the
cap-robust inequality `r_w² η_w ≤ η_s` gives `r_w⁵ η_w³ ≤ η_s³`, so
`η_w⁻¹ r_w⁵ (η_w/η_v)^4 ≤ η_s³/η_v⁴` and the sum is `≤ (η_s/η_v)^4/Im m`: exponent exactly `4`.
(Taking the supremum of each factor separately would lose, `≈ R^{6.5}`; integrating instead of
summing only improves the constant `1 → 2/3`.) Since no Riemann-sum error is incurred, no mesh
condition on `Δ` is needed. The `J`-powers of the far terms are absorbed by the `N^{-c}` gain of
the regime condition of Step 2, for every `0 < δ ≤ c/24` and `2ε ≤ δ`; `nearEpsilon ≤ W⁻¹` is
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

/-- **Cap-robust ratio bound**: `ℓ_w² (1-w) ≤ ℓ_s² (1-s)` for `s ≤ w < 1`. -/
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

end QVSum

/-! ## The rate `Qd` and the constant -/

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `J w := N^{2ε} · thr w = N^{2ε} N^δ (η_s/η_w)^4` (`RBM.Step2.thr`, Step2.lean). -/
noncomputable def qvJ (E : ℝ) (s : ℕ → ℝ) (δ ε : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N w

/-- **The per-time rate `Qd w`**: the right-hand-side rate of the quadratic-variation event of
`Gauss/Step2QVEvent.lean` with `jG` replaced
by `J w = qvJ …`, i.e. `diagShape'` with the near-field indicator dropped and the common
`tailT²` factored out:
`diagNearRate(ℓ_w, ℓ_s, η_w) + 2 nearEpsilon(W, L, ℓ_w, η_w, D, J w)
  + diagFarRate(ℓ_w, η_w, D, J w, sDet(w, ℓ_s))`. -/
noncomputable def Qd (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (δ ε D : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  QVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w)
    + 2 * EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D
        (qvJ E s δ ε N w)
    + QVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D (qvJ E s δ ε N w)
        (EarlyQVRateEv.sDet B E N w (B.ell N (s N)))

/-- The explicit constant of the time-sum bound (5.44) (`qv_time_sum_le_plainN`):
`1200 / Im m(E)`; it depends only on `E`. -/
noncomputable def qvSumConst (E : ℝ) : ℝ := 1200 / (mE E).im

end Defs

namespace QVSum

/-- The final scalar arithmetic of the time-sum bound (5.44): with `a = N^κ ≥ 1`,
`b = 1/Im m ≥ 1`, `Y = R⁴ ≥ 0` and `σ = 1 - s ≤ 1`. -/
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
  have hN : 0 ≤ QVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w) := by
    unfold QVEndpoint.diagNearRate
    exact mul_nonneg (mul_nonneg (by positivity) h1) (by positivity)
  have hnE : 0 ≤ EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D
      (qvJ E s δ ε N w) := by
    unfold EEDef.nearEpsilon; positivity
  have hF : 0 ≤ QVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D (qvJ E s δ ε N w)
      (EarlyQVRateEv.sDet B E N w (B.ell N (s N))) := by
    unfold QVEndpoint.diagFarRate
    have hJ3 : 0 ≤ (2 * qvJ E s δ ε N w) ^ 3 := pow_nonneg (by linarith) 3
    have hWD : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
    refine add_nonneg (mul_nonneg (by positivity) (add_nonneg ?_ ?_)) ?_
    · exact mul_nonneg h2 (by positivity)
    · exact mul_nonneg (mul_nonneg (by norm_num) hJ3) (by positivity)
    · exact mul_nonneg (by positivity) hJ3
  unfold Qd
  linarith

end QVSum

end RBM.Gauss.Grid

end
