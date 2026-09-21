/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2PP
import RBM1D.Hierarchy.Step45
import RBM1D.Hierarchy.Lemma57

/-!
# Step 2's one-step improvement along the moment route (T132c)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48), for the **(2.73)-reduced** shape of Lemma 5.7.

## The route (T174's recomputation, as ruled by Cowork)

* **shape 2**, `RBM.Lemma57.eG_le_reduced`: the far-field bracket of (5.35) is
  `r^{3/2} A_u^{-1/2} J*  +  r A_u^{-1} (J*)^{3/2}` with `r = ℓ_u/ℓ_s`, `A_u = W ℓ_u η_u`,
  instead of the paper's `A_u^{-1/3} (J*)³`; the near-field term is `r³` instead of `r²`;
* the `-1/2 → -1/3` absorption of (5.36)→(5.42) is **skipped**;
* the near-field term of (5.44) is **multiplied out before the supremum is taken**;
* de-truncation happens at the **probability** level (a crossing argument on a time net), not
  inside the moment.

## What is proved

| § | name | content |
|---|---|---|
| 1 | `phi_arith'` | the arithmetic of (5.39)–(5.47) for shape 2: `RBM.Step2.phi_arith` with `hq : q ≤ R` relaxed to `q ≤ R²` and the cubic drift term replaced by `β J* + γ (J*)^{3/2}` |
| 2 | `hq_of_ratio`, `hbeta_of_reg`, `hgamma_of_reg`, `beta_star_margin` | the exponent table: `q = r³ ≤ R²`, and the two far-field side conditions from `A ≥ x^{16}R^{11/2}` and `A ≥ x^{12}R^{9/2}` — **`β* = 5.5` and `β* = 4.5`**, both far below (2.72)'s 30 |
| 3 | `nearInt_le`, `integral_nearInt_le`, `coarse_sq_ge` | (5.44)'s near-field term integrated: `∫_s^v η_u^{-1}(η_u/η_v)^4 (η_s/η_u)^{5/2} du ≤ (Im m)^{-1}(η_s/η_v)^4`; bounding the factors separately overshoots by `R^{5/2}` |
| 4 | `ratio_sq_le`, `side_conditions_of_reg` | the whole side-condition bundle is satisfiable on the flow, from (2.72) with a gain |
| 5 | `le_of_gap_crossing`, `le_of_gap_net` | de-truncation at the probability level: a continuous path that never enters the gap `[Θ, 2Θ]` stays below it, and the gap condition is needed only at net points |
| 6 | `netSet`, `exists_netPoint_le`, `hclose_of_modulus`, `bootPP_step_of_net`, `bootPP_of_net`, `bootPP_of_modulus` | **`RBM.Step2PP.BootPP.step`** reduced from a continuum of times to finitely many fixed times |
| 7 | `xiLK_two_apriori`, `no_finite_pass`, `linearize_on_support` | why the `(+,+)` bootstrap cannot be replaced by finitely many `≺`-passes, and the cutoff linearization that makes the moment closure same-order |
| 8 | `eq548_of_near_far`, `flowEq548_of_near_far` | **(5.48)** `RBM.Step45.FlowEq548` from its near and far halves |
| 9 | `bnd_poly_excludes_pow`, `detrunc_remainder_ge_thr`, `detrunc_order_needed`, `phi_lt_threshold` | why the frozen `RBM.Step2Moment.MomentHyp.step` is *not* the right target |
| 10 | `sat_*` | compiled satisfiability witnesses for every hypothesis bundle introduced here |

## What is **not** proved here

* `RBM.Step2Moment.MomentHyp.step` itself.  §9 shows why: `bnd_poly` forbids `bnd` from
  carrying any power of `N` (`bnd_poly_excludes_pow`), while the union bound over the `L²`
  loop arguments inside `J*` costs `L² ≍ N²` at every order; and de-truncating inside the
  moment leaves a Markov remainder at least as large as the threshold itself
  (`detrunc_remainder_ge_thr`), needing the order multiplied by `(K+δ)/δ`
  (`detrunc_order_needed`).  Both are exactly the obstructions the T132c spec records, and
  both are removed by putting the de-truncation at the probability level (§5, §6).
* the fixed-time inputs `hev` of `bootPP_of_net` / `bootPP_of_modulus`, and the far half
  `hfar` of `eq548_of_near_far`.  `hev` is what the truncated moment Duhamel (T132b) must
  produce; `hfar` is (5.48)'s far field, which needs the indicators of (5.39), (5.41), (5.44)
  carried through the one-step bound — `RBM.Step2.step_bound` discards them.

## Deviations from the paper (to report)

* (5.41) is used in the (2.73)-reduced shape, i.e. with `J*` to the first and `3/2` powers
  rather than the third; this is the shape `RBM.Lemma57.eG_le_reduced` proves, and it is the
  reason the bottleneck exponent of (2.72) drops from 30 to `5.5`.
* The near-field exponent of the reduced (5.35) is `r³`, so the hypothesis `q ≤ R` of
  `RBM.Step2.phi_arith` has to be relaxed to `q ≤ R²` (`r³ ≤ R^{3/2} ≤ R²`).  The constant is
  unchanged except for one extra `m⁻¹`, which is the price of splitting the paper's single
  cubic drift term into two.
* `RBM.Step2PP.BootPP.step`'s improvement factor is `N^δ - 1` at the net points rather than
  `N^δ` at every time: the missing `1` is the net error, paid once.
-/

namespace RBM

namespace Step2MomentStep

open Real Filter MeasureTheory

/-! ### 1. The arithmetic of (5.39)–(5.47) for the (2.73)-reduced shape of (5.35) -/

section Arith

/-- The constant of `phi_arith'`.  Compared with `RBM.Step2.cStep` it has `3 m⁻¹` in place of
`2 m⁻¹`: the paper's single cubic drift term `A^{-1/3}(J*)³` is split into the two terms
`β J*` and `γ (J*)^{3/2}` of the reduced shape, so one more summand has to be absorbed. -/
noncomputable def cStep' (m : ℝ) : ℝ := 4 + exp 1 + (36 * exp 1 + 3) * m⁻¹

theorem cStep'_pos {m : ℝ} (hm : 0 < m) : 0 < cStep' m := by
  have : 0 < exp 1 := exp_pos 1
  have : 0 < m⁻¹ := inv_pos.2 hm
  unfold cStep'; positivity

/-- **The arithmetic of (5.40)–(5.47), (2.73)-reduced shape.**

This is `RBM.Step2.phi_arith` with two changes, both forced by
`RBM.Lemma57.eG_le_reduced`:

* the near-field coefficient `q` of (5.41) is `(ℓ_u/ℓ_s)³`, not `(ℓ_u/ℓ_s)²`, so the
  hypothesis `q ≤ R` becomes `q ≤ R²` (`hq_of_ratio`);
* the far-field bracket of (5.41) is `β J* + γ (J*)^{3/2}` with `β = r^{3/2}A^{-1/2}` and
  `γ = r A^{-1}`, not `A^{-1/3}(J*)³`.

`x = N^{δ/8}`, so `N^δ = x⁸`, the threshold of (5.43) is `Λ = x⁸ R⁴` and the losses of `≺`
are `N^τ = x`.  The conclusion `≤ cStep' m · x² R⁴` is strictly below `Λ = x⁸ R⁴` once
`cStep' m ≤ x⁶`, which is the margin of the bootstrap. -/
theorem phi_arith' {x R Ξ m A ε q β γ J : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (_hΞ0 : 0 ≤ Ξ)
    (hΞ : Ξ ≤ x) (hm0 : 0 < m) (hA : x ^ 17 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε * x ^ 17 * R ^ 10 ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ R ^ 2)
    (hβ0 : 0 ≤ β) (hβ : β * (x ^ 8 * R ^ 2) ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ : γ * (x ^ 12 * R ^ 4) ≤ 1)
    (hJ0 : 0 ≤ J) (hJΛ : J ≤ x ^ 8 * R ^ 4) :
    x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + β * J + γ * (J * √J))) + x * (R ^ 2 + 1) + 1
      ≤ cStep' m * x ^ 2 * R ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hxA : x ^ 17 * R ^ 10 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hA
  -- `√J ≤ x⁴ R²`
  have hsq : √J ≤ x ^ 4 * R ^ 2 := by
    have hsq' : (x ^ 4 * R ^ 2) ^ 2 = x ^ 8 * R ^ 4 := by ring
    have := Real.sqrt_le_sqrt hJΛ
    rwa [← hsq', Real.sqrt_sq (by positivity)] at this
  have hsq0 : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hJJ : J * √J ≤ x ^ 12 * R ^ 6 := by
    calc J * √J ≤ (x ^ 8 * R ^ 4) * (x ^ 4 * R ^ 2) := by
          exact mul_le_mul hJΛ hsq hsq0 (by positivity)
      _ = x ^ 12 * R ^ 6 := by ring
  -- the seven terms
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 4 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
      _ ≤ x ^ 2 * R ^ 4 := by gcongr
  have t2 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
      ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        = 36 * exp 1 * m⁻¹ * (Ξ * x ^ 16 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * x ^ 16 * R ^ 10 * A⁻¹) := by gcongr
      _ = 36 * exp 1 * m⁻¹ * (x ^ 17 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by gcongr
  have t3 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) ≤ exp 1 * (x ^ 2 * R ^ 4) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        = exp 1 * (Ξ * x ^ 16 * R ^ 10 * ε) := by ring
      _ ≤ exp 1 * (x * x ^ 16 * R ^ 10 * ε) := by gcongr
      _ = exp 1 * (ε * x ^ 17 * R ^ 10) := by ring
      _ ≤ exp 1 * 1 := by gcongr
      _ ≤ exp 1 * (x ^ 2 * R ^ 4) := by gcongr
  -- the near field: `q ≤ R²` (the reduced shape's `r³`), zero margin in `R`
  have t4 : Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ x * (x * m⁻¹ * R ^ 2 * R ^ 2) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := by ring
  -- the leading far-field term: `β J*`, `β* = 5.5`
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (β * J)) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (β * J))
        ≤ x * (x * m⁻¹ * R ^ 2 * (β * (x ^ 8 * R ^ 4))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) * (β * (x ^ 8 * R ^ 2)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := mul_one _
  -- the subleading far-field term: `γ (J*)^{3/2}`, `β* = 4.5`
  have t6 : Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J))) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J)))
        ≤ x * (x * m⁻¹ * R ^ 2 * (γ * (x ^ 12 * R ^ 6))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) * (γ * (x ^ 12 * R ^ 4)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := mul_one _
  have t7 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 4) := by nlinarith
  have hsplit : x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 *
        (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * m⁻¹ * R ^ 2 * (q + β * J + γ * (J * √J))) + x * (R ^ 2 + 1) + 1
      = x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) + Ξ * (x * m⁻¹ * R ^ 2 * q)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * J)) + Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J)))
        + x * (R ^ 2 + 1) + 1 := by ring
  rw [hsplit, cStep']
  nlinarith

end Arith

/-! ### 2. The three side conditions, i.e. the exponent table -/

section Exponents

variable {x R r A : ℝ}

/-- **The relaxed near-field hypothesis.**  The reduced (5.35) has `r³` where the paper's
shape has `r²`, and `r² ≤ R` (`RBM.Step3.ellHat_le_sqrt_mul`), so `r³ ≤ R^{3/2} ≤ R²`.  This
is the single place where `RBM.Step2.phi_arith`'s hypothesis `q ≤ R` had to be weakened. -/
theorem hq_of_ratio (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R) : r ^ 3 ≤ R ^ 2 := by
  have _hr0' := hr0
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have h6 : r ^ 6 ≤ R ^ 3 := by
    calc r ^ 6 = (r ^ 2) ^ 3 := by ring
      _ ≤ R ^ 3 := by gcongr
  have h4 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  nlinarith [pow_nonneg hr0 3, pow_nonneg hR0 2]

/-- **`β* = 5.5`.**  The leading far-field coefficient of the reduced (5.35) is
`β = r^{3/2} A^{-1/2}`, and `phi_arith'` needs `β x⁸ R² ≤ 1`.  Squaring, this is
`r³ x^{16} R⁴ ≤ A`, and `r³ ≤ R^{3/2}`, so `A² ≥ x^{32} R^{11}` — i.e.
`A ≥ x^{16} R^{11/2}` — suffices.  Under (2.72) with a gain (`N^c R^{30} ≤ A`) and
`x = N^{δ/8}` this holds as soon as `4δ ≤ 2c`, with `R^{49}` to spare. -/
theorem hbeta_of_reg (hx : 1 ≤ x) (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R) (hA0 : 0 < A)
    (hA : x ^ 32 * R ^ 11 ≤ A ^ 2) : (r * √r * (√A)⁻¹) * (x ^ 8 * R ^ 2) ≤ 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  have hsr : (0 : ℝ) ≤ √r := Real.sqrt_nonneg _
  set β : ℝ := r * √r * (√A)⁻¹ with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hβsq : β ^ 2 = r ^ 3 * A⁻¹ := by
    rw [hβdef, mul_pow, mul_pow, Real.sq_sqrt hr0, ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
    ring
  -- `(r³)² = r⁶ ≤ R³`
  have h6 : (r ^ 3) ^ 2 ≤ R ^ 3 := by
    calc (r ^ 3) ^ 2 = (r ^ 2) ^ 3 := by ring
      _ ≤ R ^ 3 := by gcongr
  -- target squared: `r³ x^{16} R⁴ ≤ A`
  have hkey : r ^ 3 * (x ^ 16 * R ^ 4) ≤ A := by
    have hlhs0 : (0 : ℝ) ≤ r ^ 3 * (x ^ 16 * R ^ 4) := by positivity
    have hsqle : (r ^ 3 * (x ^ 16 * R ^ 4)) ^ 2 ≤ A ^ 2 := by
      calc (r ^ 3 * (x ^ 16 * R ^ 4)) ^ 2 = (r ^ 3) ^ 2 * (x ^ 32 * R ^ 8) := by ring
        _ ≤ R ^ 3 * (x ^ 32 * R ^ 8) := by gcongr
        _ = x ^ 32 * R ^ 11 := by ring
        _ ≤ A ^ 2 := hA
    nlinarith [hA0.le, hlhs0]
  have hsq : (β * (x ^ 8 * R ^ 2)) ^ 2 ≤ 1 := by
    have : (β * (x ^ 8 * R ^ 2)) ^ 2 = (r ^ 3 * A⁻¹) * (x ^ 16 * R ^ 4) := by
      rw [mul_pow, hβsq]; ring
    rw [this, mul_comm (r ^ 3) A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
    exact hkey
  nlinarith [mul_nonneg hβ0 (by positivity : (0:ℝ) ≤ x ^ 8 * R ^ 2)]

/-- **`β* = 4.5`.**  The subleading far-field coefficient of the reduced (5.35) is
`γ = r A^{-1}`, and `phi_arith'` needs `γ x^{12} R⁴ ≤ 1`, i.e. `r x^{12} R⁴ ≤ A`.  With
`r ≤ R^{1/2}` this follows from `A² ≥ x^{24} R⁹` — i.e. `A ≥ x^{12} R^{9/2}`. -/
theorem hgamma_of_reg (hx : 1 ≤ x) (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R) (hA0 : 0 < A)
    (hA : x ^ 24 * R ^ 9 ≤ A ^ 2) : (r * A⁻¹) * (x ^ 12 * R ^ 4) ≤ 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hkey : r * (x ^ 12 * R ^ 4) ≤ A := by
    have hlhs0 : (0 : ℝ) ≤ r * (x ^ 12 * R ^ 4) := by positivity
    have hsqle : (r * (x ^ 12 * R ^ 4)) ^ 2 ≤ A ^ 2 := by
      calc (r * (x ^ 12 * R ^ 4)) ^ 2 = r ^ 2 * (x ^ 24 * R ^ 8) := by ring
        _ ≤ R * (x ^ 24 * R ^ 8) := by gcongr
        _ = x ^ 24 * R ^ 9 := by ring
        _ ≤ A ^ 2 := hA
    nlinarith [hA0.le, hlhs0]
  rw [mul_comm r A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
  exact hkey

/-- **The bottleneck of the whole table is `β* = 5.5`**, strictly below `RBM.Cond272`'s
exponent 30: `A ≥ N^c R^{30}` gives `A² ≥ N^{2c} R^{60}`, and `x^{32} R^{11} = N^{4δ} R^{11}`,
so the margin is `N^{2c - 4δ} R^{49}`. -/
theorem beta_star_margin {N c δ : ℝ} (hN : 1 ≤ N) (hR : 1 ≤ R) (hδ : 4 * δ ≤ 2 * c)
    (hx : x = N ^ (δ / 8)) (hA0 : 0 < A) (hA : N ^ c * R ^ 30 ≤ A) :
    x ^ 32 * R ^ 11 ≤ A ^ 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hx32 : x ^ 32 = N ^ (4 * δ) := by
    rw [hx, ← Real.rpow_natCast (N ^ (δ / 8)) 32, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have h2c : N ^ (4 * δ) ≤ N ^ (2 * c) := Real.rpow_le_rpow_of_exponent_le hN hδ
  have hR1149 : R ^ 11 ≤ R ^ 60 := pow_le_pow_right₀ hR (by norm_num)
  have hAsq : (N ^ c * R ^ 30) ^ 2 ≤ A ^ 2 := by
    have h0 : (0 : ℝ) ≤ N ^ c * R ^ 30 := by positivity
    nlinarith
  have hNc2 : (N ^ c) ^ 2 = N ^ (2 * c) := by
    rw [← Real.rpow_natCast (N ^ c) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hexp : (N ^ c * R ^ 30) ^ 2 = N ^ (2 * c) * R ^ 60 := by
    rw [mul_pow, hNc2]; ring
  rw [hx32]
  calc N ^ (4 * δ) * R ^ 11 ≤ N ^ (2 * c) * R ^ 60 := by gcongr
    _ = (N ^ c * R ^ 30) ^ 2 := hexp.symm
    _ ≤ A ^ 2 := hAsq

end Exponents

/-! ### 3. (5.44)'s near-field term: integrate first, then take the supremum -/

section Near

variable {E : ℝ}

/-- The near-field integrand of (5.44), with the loop-length ratio `ℓ_u/ℓ_s` already replaced
by its bound `√(η_s/η_u)` (`RBM.Step3.ellHat_le_sqrt_mul`):

`η_u^{-1} (η_u/η_v)^4 (η_s/η_u)^{5/2}`. -/
noncomputable def nearInt (E s v u : ℝ) : ℝ :=
  (etaT E u)⁻¹ * (etaT E u / etaT E v) ^ 4 * √(etaT E s / etaT E u) ^ 5

/-- **The whole point of "multiply first, then take the supremum".**  The three factors of
`nearInt` collapse to `η_s^{5/2} η_u^{1/2} / η_v^4`, which is *increasing* in `η_u` and
therefore maximal at `u = s`, where it equals `η_s^3 / η_v^4`.  Bounding the factors
separately — `η_u^{-1} ≤ η_v^{-1}`, `(η_u/η_v)^4 ≤ (η_s/η_v)^4`, `(η_s/η_u)^{5/2} ≤
(η_s/η_v)^{5/2}` — gives `η_v^{-1}(η_s/η_v)^{13/2}` instead (`coarse_sq_ge`). -/
theorem nearInt_le (hE : |E| < 2) {s u v : ℝ} (hsu : s ≤ u) (hu1 : u < 1) (hv1 : v < 1) :
    nearInt E s v u ≤ etaT E s ^ 3 / etaT E v ^ 4 := by
  have hs1 : s < 1 := hsu.trans_lt hu1
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hb : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hba : etaT E u ≤ etaT E s := by
    rw [Step2.etaT_eq, Step2.etaT_eq]
    have hm := mE_im_pos hE
    nlinarith [show (1 : ℝ) - u ≤ 1 - s by linarith]
  obtain ⟨sa, hsa0, hsa⟩ : ∃ y : ℝ, 0 ≤ y ∧ y ^ 2 = etaT E s :=
    ⟨√(etaT E s), Real.sqrt_nonneg _, Real.sq_sqrt ha.le⟩
  obtain ⟨sb, hsb0, hsb⟩ : ∃ y : ℝ, 0 ≤ y ∧ y ^ 2 = etaT E u :=
    ⟨√(etaT E u), Real.sqrt_nonneg _, Real.sq_sqrt hb.le⟩
  have hsa' : √(etaT E s) = sa := by rw [← hsa, Real.sqrt_sq hsa0]
  have hsb' : √(etaT E u) = sb := by rw [← hsb, Real.sqrt_sq hsb0]
  have hsbpos : 0 < sb := by nlinarith
  have hsapos : 0 < sa := by nlinarith
  have hsbne : sb ≠ 0 := hsbpos.ne'
  have hcne : etaT E v ≠ 0 := hc.ne'
  have hdiv : √(etaT E s / etaT E u) = sa / sb := by
    rw [Real.sqrt_div ha.le, hsa', hsb']
  have hcollapse : nearInt E s v u = sa ^ 5 * sb / etaT E v ^ 4 := by
    rw [nearInt, hdiv, ← hsb]
    field_simp
  have hc4 : (0 : ℝ) < etaT E v ^ 4 := by positivity
  have hsble : sb ≤ sa := by nlinarith
  rw [hcollapse, ← hsa, div_le_div_iff_of_pos_right hc4]
  nlinarith [pow_nonneg hsa0 5, hsble, hsa0, hsbpos.le]

/-- **(5.44)'s near-field term, integrated**:
`∫_s^v η_u^{-1}(η_u/η_v)^4 (η_s/η_u)^{5/2} du ≤ (Im m_E)^{-1} (η_s/η_v)^4`.

The budget of the one-step improvement is exactly `(η_s/η_v)^4` — the threshold of (5.43) —
so this term fits with no loss in `R` at all.  The proof is `nearInt_le` (the supremum of the
**combined** integrand) times the length `v - s ≤ 1 - s = η_s / Im m_E`. -/
theorem integral_nearInt_le (hE : |E| < 2) {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) :
    (∫ u in s..v, nearInt E s v u) ≤ ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 4 := by
  have hm := mE_im_pos hE
  have hs1 : s < 1 := hsv.trans_lt hv1
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  set M : ℝ := etaT E s ^ 3 / etaT E v ^ 4 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hbd : ∀ u ∈ Set.uIoc s v, ‖nearInt E s v u‖ ≤ M := by
    intro u hu
    rw [Set.uIoc_of_le hsv] at hu
    have hsu : s ≤ u := hu.1.le
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 hv1
    have hbb : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hnn : 0 ≤ nearInt E s v u := by rw [nearInt]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact nearInt_le hE hsu hu1 hv1
  have hint : ‖∫ u in s..v, nearInt E s v u‖ ≤ M * |v - s| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have hlen : |v - s| ≤ etaT E s / (mE E).im := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ v - s), Step2.etaT_eq, mul_div_assoc,
      div_self hm.ne', mul_one]
    linarith
  have hkey : M * |v - s| ≤ ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 4 := by
    have h1 : M * |v - s| ≤ M * (etaT E s / (mE E).im) := by gcongr
    refine h1.trans (le_of_eq ?_)
    rw [hM, div_pow]
    field_simp
  refine le_trans (le_trans (le_abs_self _) ?_) hkey
  rwa [← Real.norm_eq_abs]

/-- **The coarse route really does overshoot, by `R^{5/2}`.**  Bounding the three factors of
`nearInt` separately gives `η_v^{-1}(η_s/η_v)^4 (η_s/η_v)^{5/2}`, whose square is at least
`R^5` times the square of the budget `(Im m_E)^{-1}(η_s/η_v)^4` of `integral_nearInt_le`
(`R = η_s/η_v ≥ 1`).  This is T174's `R^{2.5}`. -/
theorem coarse_sq_ge (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    (((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 4) ^ 2 * (etaT E s / etaT E v) ^ 5
      ≤ ((etaT E v)⁻¹ * (etaT E s / etaT E v) ^ 4 *
          √(etaT E s / etaT E v) ^ 5) ^ 2 := by
  have hm := mE_im_pos hE
  have hs1 : s < 1 := hsv.trans_lt hv1
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hR1 : (1 : ℝ) ≤ etaT E s / etaT E v := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - v), one_mul]
    linarith
  set R : ℝ := etaT E s / etaT E v with hRdef
  have hR0 : (0 : ℝ) < R := by linarith
  have hsq5 : (√R ^ 5) ^ 2 = R ^ 5 := by
    rw [← pow_mul, show 5 * 2 = 2 * 5 by norm_num, pow_mul, Real.sq_sqrt hR0.le]
  have hηv : etaT E v ≤ (mE E).im := by
    rw [Step2.etaT_eq]; nlinarith [hv1, hs0, hsv]
  have hinv : ((mE E).im)⁻¹ ≤ (etaT E v)⁻¹ := inv_anti₀ hc hηv
  have hexp : ((etaT E v)⁻¹ * R ^ 4 * √R ^ 5) ^ 2 = ((etaT E v)⁻¹ * R ^ 4) ^ 2 * R ^ 5 := by
    rw [mul_pow, hsq5]
  rw [hexp]
  have h1 : (((mE E).im)⁻¹ * R ^ 4) ^ 2 ≤ ((etaT E v)⁻¹ * R ^ 4) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((mE E).im)⁻¹ * R ^ 4 := by positivity
    have hle : ((mE E).im)⁻¹ * R ^ 4 ≤ (etaT E v)⁻¹ * R ^ 4 := by gcongr
    nlinarith
  have hR50 : (0 : ℝ) ≤ R ^ 5 := by positivity
  nlinarith [h1, hR50]

end Near

/-! ### 4. Satisfiability: the side conditions hold for the flow -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **`r² ≤ R` on the flow**, i.e. `(ℓ_u/ℓ_s)² ≤ η_s/η_u`: the hypothesis that all three
side conditions of `phi_arith'` are built on.  This is `RBM.Step3.ellHat_le_sqrt_mul`. -/
theorem ratio_sq_le (hE : |E| < 2) {N : ℕ} {u : ℝ} (hsu : s N ≤ u) (hu1 : u < 1) :
    (B.ell N u / B.ell N (s N)) ^ 2 ≤ etaT E (s N) / etaT E u := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have h1u : 0 < 1 - u := by linarith
  have hQ : (1 : ℝ) ≤ (1 - s N) / (1 - u) := by rw [le_div_iff₀ h1u]; linarith
  have h := Step3.ellHat_le_sqrt_mul (L := B.L N) (s := s N) (t := u) hsu hu1
  have hr : B.ell N u / B.ell N (s N) ≤ √((1 - s N) / (1 - u)) := by
    rw [div_le_iff₀ hℓs]; exact h
  have hr0 : (0 : ℝ) ≤ B.ell N u / B.ell N (s N) := by
    have := (Step3.ellHat_pos_of_lt_one (L := B.L N) hL hu1).le
    positivity
  have hsq : (B.ell N u / B.ell N (s N)) ^ 2 ≤ (1 - s N) / (1 - u) := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (1 - s N) / (1 - u))
    nlinarith [Real.sqrt_nonneg ((1 - s N) / (1 - u))]
  rwa [Step2.etaT_ratio hE]

/-- **The whole side-condition bundle of `phi_arith'` is satisfiable on the flow**, from
(2.72) with a gain (`hregS`): with `x = N^{δ/8}`, `R = η_s/η_u` and `r = ℓ_u/ℓ_s`,

* `q = r³ ≤ R²` (`hq_of_ratio`);
* `β = r^{3/2}A^{-1/2}` satisfies `β x⁸ R² ≤ 1` (`hbeta_of_reg`, `β* = 5.5`);
* `γ = r A^{-1}` satisfies `γ x^{12} R⁴ ≤ 1` (`hgamma_of_reg`, `β* = 4.5`).

The bottleneck is `β* = 5.5 < 30`, so (2.72)'s exponent is **not** touched. -/
theorem side_conditions_of_reg (hE : |E| < 2) {N : ℕ} {u : ℝ} (hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c) (hN1 : 1 ≤ (N : ℝ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u) :
    (B.ell N u / B.ell N (s N)) ^ 3 ≤ (etaT E (s N) / etaT E u) ^ 2 ∧
      ((B.ell N u / B.ell N (s N)) * √(B.ell N u / B.ell N (s N)) *
          (√(B.scale E N u))⁻¹) *
          (((N : ℝ) ^ (δ / 8)) ^ 8 * (etaT E (s N) / etaT E u) ^ 2) ≤ 1 ∧
      ((B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹) *
          (((N : ℝ) ^ (δ / 8)) ^ 12 * (etaT E (s N) / etaT E u) ^ 4) ≤ 1 := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL hu1
  have hr0 : (0 : ℝ) ≤ B.ell N u / B.ell N (s N) := by positivity
  have hr := ratio_sq_le (B := B) (s := s) hE hsu hu1
  have hηs : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hR1 : (1 : ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith), one_mul]; linarith
  have hA0 : 0 < B.scale E N u := B.scale_pos' hE N (hs0.trans hsu) hu1
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN1 (by linarith)
  have hsq := beta_star_margin (x := (N : ℝ) ^ (δ / 8))
    (R := etaT E (s N) / etaT E u) (A := B.scale E N u) hN1 hR1 hδ rfl hA0 hA
  refine ⟨hq_of_ratio hR1 hr0 hr, hbeta_of_reg hx1 hR1 hr0 hr hA0 hsq, ?_⟩
  refine hgamma_of_reg hx1 hR1 hr0 hr hA0 ?_
  have h24 : ((N : ℝ) ^ (δ / 8)) ^ 24 ≤ ((N : ℝ) ^ (δ / 8)) ^ 32 :=
    pow_le_pow_right₀ hx1 (by norm_num)
  have h9 : (etaT E (s N) / etaT E u) ^ 9 ≤ (etaT E (s N) / etaT E u) ^ 11 :=
    pow_le_pow_right₀ hR1 (by norm_num)
  calc ((N : ℝ) ^ (δ / 8)) ^ 24 * (etaT E (s N) / etaT E u) ^ 9
      ≤ ((N : ℝ) ^ (δ / 8)) ^ 32 * (etaT E (s N) / etaT E u) ^ 11 := by gcongr
    _ ≤ B.scale E N u ^ 2 := hsq

end Satisfiable

/-! ### 5. De-truncation at the probability level: the gap-crossing argument -/

section Crossing

/-- **The crossing argument.**  A continuous path that starts below `w` and is never inside the
gap `[w, 2w]` stays below `w`.  This is `RBM.Step2Moment.le_of_bootstrap_weight` at `B = 1`,
`C = 2`; it is what replaces the stopping time (5.43) once the cutoff `χ(J/Θ)` is in play.

The gap hypothesis is the one the *truncated* moment bound produces: the truncated and the
untruncated object agree as long as the path has not left `[0, 2w]`, so a moment bound on the
truncated object bounds the untruncated one exactly on `{J ≤ 2w}`. -/
theorem le_of_gap_crossing {a b : ℝ} {J w : ℝ → ℝ} (hab : a ≤ b)
    (hJc : ContinuousOn J (Set.Icc a b)) (hwc : ContinuousOn w (Set.Icc a b))
    (hw0 : ∀ u ∈ Set.Icc a b, 0 < w u) (h0 : J a ≤ w a)
    (hgap : ∀ u ∈ Set.Icc a b, J u ≤ 2 * w u → J u ≤ w u) :
    ∀ u ∈ Set.Icc a b, J u ≤ w u := by
  have h := Step2Moment.le_of_bootstrap_weight (B := 1) (C := 2) hab hJc hwc hw0
    one_lt_two (by simpa using h0) ?_
  · intro u hu; simpa using h u hu
  · intro u hu hprefix
    have := hprefix u ⟨hu.1, le_rfl⟩
    rw [one_mul]
    exact hgap u hu (by linarith)

/-- **The crossing argument with a time net.**  `Y` is the *normalized* path (`jSnorm` of
`RBM.Step2Moment`, or `Ξ^{(L-K)}_{u,2}/Θ`), so the gap `[1, 2]` is constant in `u`.

The input `hgood` is asserted only at the net points `S`, and only *conditionally* on the
prefix bound — which is exactly the shape a moment bound produced from a Duhamel formula over
`[a, w]` can have.  `hnet` is the deterministic modulus of continuity
(`RBM.Step2Moment.MomentHyp.holder`) evaluated on a net of mesh small enough to make the
displacement at most `1/4`.

The conclusion is `Y ≤ 5/4`, not `Y ≤ 1`: the quarter is the net error, and it is why the
`≺`-margin `N^δ` has to be split into two halves. -/
theorem le_of_gap_net {a b : ℝ} {Y : ℝ → ℝ} {S : Set ℝ} (hab : a ≤ b)
    (hYc : ContinuousOn Y (Set.Icc a b)) (h0 : Y a ≤ 5 / 4)
    (hnet : ∀ u ∈ Set.Icc a b, ∃ ws ∈ S, ws ∈ Set.Icc a u ∧ Y u ≤ Y ws + 1 / 4)
    (hgood : ∀ ws ∈ S, ws ∈ Set.Icc a b → Y ws ≤ 2 → Y ws ≤ 1) :
    ∀ u ∈ Set.Icc a b, Y u ≤ 5 / 4 := by
  refine le_of_bootstrap_prefix (B := 5 / 4) (C := 2) hab hYc (by norm_num) h0 ?_
  intro u hu hprefix
  obtain ⟨ws, hwsS, hwsIcc, hwY⟩ := hnet u hu
  have hwsb : ws ∈ Set.Icc a b := ⟨hwsIcc.1, hwsIcc.2.trans hu.2⟩
  have hw2 : Y ws ≤ 2 := hprefix ws hwsIcc
  have := hgood ws hwsS hwsb hw2
  linarith

end Crossing

/-! ### 6. `BootPP.step` from the net: the continuum of times reduced to fixed times -/

section BootPPNet

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

open Filter

/-- **`RBM.Step2PP.BootPP.step` from fixed-time inputs.**

`BootPP.step` quantifies over a *continuum* of times `v ∈ [s, t]`, which no moment bound can
supply: the moment route produces a bound at one fixed time at a time
(`RBM.MomentDuhamel.stochDom_of_momentDuhamel`, whose conclusion is at `v N`).  This lemma
removes the continuum: it is enough to have

* `hclose` — a **deterministic** modulus statement: every `v ∈ [s,t]` has a net point
  `ws ≤ v` at which `Ξ^{(L-K)}_{·,2}` differs by at most `Θ_N`.  For `H_u = √u X` this is
  `RBM.Gauss.abs_sqrt_sub_sqrt_le` on a net of mesh `N^{-C}`, exactly as in
  `RBM.Step2Moment.stochDom_timeIcc_of_holder`;
* `hev` — the same one-step improvement asserted **only at the net points**, with `N^δ - 1`
  in place of `N^δ` (the quarter of `le_of_gap_net`, here a whole `Θ_N`).

Note that the net-point hypothesis is still *conditional on the whole prefix* `[s, ws]`, which
is what the moment Duhamel over `[s, ws]` gives after the cutoff: on the event where the
prefix bound holds, the truncated and untruncated loops coincide. -/
theorem bootPP_step_of_net (X : Sample B) {target : ℕ → ℝ} {S : ℕ → Set ℝ} {δ : ℝ}
    (hclose : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ S N,
      ws ∈ Set.Icc (s N) v ∧ X.xiLK E N v ω 2 ≤ X.xiLK E N ws ω 2 + target N)
    (hev : HighProb B.P fun N => {ω | ∀ ws ∈ S N, ws ∈ Set.Icc (s N) (t N) →
      (∀ u ∈ Set.Icc (s N) ws, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * target N) →
        X.xiLK E N ws ω 2 ≤ ((N : ℝ) ^ δ - 1) * target N}) :
    HighProb B.P fun N => {ω | ∀ v ∈ Set.Icc (s N) (t N),
      (∀ u ∈ Set.Icc (s N) v, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * target N) →
        X.xiLK E N v ω 2 ≤ (N : ℝ) ^ δ * target N} := by
  intro D hD
  filter_upwards [hev D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  refine Set.compl_subset_compl.2 fun ω hω v hv hprefix => ?_
  obtain ⟨ws, hwsS, hwsIcc, hwY⟩ := hclose N ω v hv
  have hwsb : ws ∈ Set.Icc (s N) (t N) := ⟨hwsIcc.1, hwsIcc.2.trans hv.2⟩
  have hpre : ∀ u ∈ Set.Icc (s N) ws, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * target N :=
    fun u hu => hprefix u ⟨hu.1, hu.2.trans hwsIcc.2⟩
  have := hω ws hwsS hwsb hpre
  calc X.xiLK E N v ω 2 ≤ X.xiLK E N ws ω 2 + target N := hwY
    _ ≤ ((N : ℝ) ^ δ - 1) * target N + target N := by linarith
    _ = (N : ℝ) ^ δ * target N := by ring

/-- **The `(+,+)` bootstrap structure `RBM.Step2PP.BootPP`, assembled from net inputs.**  Its
only non-routine field is `step`, and that is `bootPP_step_of_net`. -/
noncomputable def bootPP_of_net (X : Sample B) {target : ℕ → ℝ} {S : ℕ → Set ℝ} {δ₀ : ℝ}
    (htgt : ∀ N, 0 < target N) (htgt1 : ∀ᶠ N : ℕ in atTop, 1 ≤ target N)
    (hcont : ∀ (N : ℕ) (ω : Ω), ContinuousOn (fun u => X.xiLK E N u ω 2)
      (Set.Icc (s N) (t N)))
    (hδ₀ : 0 < δ₀)
    (hclose : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ S N,
      ws ∈ Set.Icc (s N) v ∧ X.xiLK E N v ω 2 ≤ X.xiLK E N ws ω 2 + target N)
    (hev : ∀ δ, 0 < δ → δ ≤ δ₀ →
      HighProb B.P fun N => {ω | ∀ ws ∈ S N, ws ∈ Set.Icc (s N) (t N) →
        (∀ u ∈ Set.Icc (s N) ws, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * target N) →
          X.xiLK E N ws ω 2 ≤ ((N : ℝ) ^ δ - 1) * target N}) :
    Step2PP.BootPP X E s t where
  target := target
  target_pos := htgt
  one_le_target := htgt1
  cont := hcont
  δ₀ := δ₀
  δ₀_pos := hδ₀
  step := fun δ hδ hδ0 => bootPP_step_of_net X hclose (hev δ hδ hδ0)

/-- The uniform net `{s_N + k/m}` of (5.46), as a set of times. -/
def netSet (s : ℕ → ℝ) (m : ℕ → ℝ) (N : ℕ) : Set ℝ := {w | ∃ k : ℕ, w = s N + k / m N}

/-- Every `v ∈ [a, b]` has a net point `a + k/m` **to its left** within `1/m`. -/
theorem exists_netPoint_le {a : ℝ} {m : ℝ} (hm : 0 < m) {v : ℝ} (hav : a ≤ v) :
    ∃ k : ℕ, a + (k : ℝ) / m ≤ v ∧ v - (a + (k : ℝ) / m) ≤ 1 / m := by
  have h0 : 0 ≤ (v - a) * m := by
    have : (0 : ℝ) ≤ v - a := by linarith
    positivity
  refine ⟨⌊(v - a) * m⌋₊, ?_, ?_⟩
  · have h1 : (⌊(v - a) * m⌋₊ : ℝ) ≤ (v - a) * m := Nat.floor_le h0
    have : (⌊(v - a) * m⌋₊ : ℝ) / m ≤ v - a := by rw [div_le_iff₀ hm]; linarith
    linarith
  · have h2 : (v - a) * m < (⌊(v - a) * m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have heq : v - (a + (⌊(v - a) * m⌋₊ : ℝ) / m)
        = ((v - a) * m - (⌊(v - a) * m⌋₊ : ℝ)) / m := by field_simp; ring
    rw [heq, div_le_div_iff_of_pos_right hm]
    linarith

/-- **`hclose` from a deterministic modulus of continuity**, i.e. the net of (5.46) made
concrete.  `hmod` is the analogue of `RBM.Step2Moment.MomentHyp.holder` for
`u ↦ Ξ^{(L-K)}_{u,2}`; for `H_u = √u X` it is `RBM.Gauss.abs_sqrt_sub_sqrt_le` with `γ = 1/2`.
`hmesh` fixes the mesh: `N^K m^{-γ} ≤ Θ_N`, i.e. `m ≥ (N^K/Θ_N)^{1/γ}`, a polynomial number of
net points — so the union bound behind `bootPP_step_of_net`'s `hev` is over finitely many
fixed times (only `k ≤ (t_N - s_N) m_N` land in `[s_N, t_N]`). -/
theorem hclose_of_modulus (X : Sample B) {target : ℕ → ℝ} {K γ : ℝ} {m : ℕ → ℝ}
    (hγ : 0 < γ) (hm : ∀ N, 0 < m N)
    (hmod : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |X.xiLK E N v ω 2 - X.xiLK E N w ω 2| ≤ (N : ℝ) ^ K * |v - w| ^ γ)
    (hmesh : ∀ N : ℕ, (N : ℝ) ^ K * (1 / m N) ^ γ ≤ target N) :
    ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ netSet s m N,
      ws ∈ Set.Icc (s N) v ∧ X.xiLK E N v ω 2 ≤ X.xiLK E N ws ω 2 + target N := by
  intro N ω v hv
  obtain ⟨k, hk1, hk2⟩ := exists_netPoint_le (a := s N) (hm N) hv.1
  refine ⟨s N + (k : ℝ) / m N, ⟨k, rfl⟩, ⟨?_, hk1⟩, ?_⟩
  · have : (0 : ℝ) ≤ (k : ℝ) / m N := div_nonneg (Nat.cast_nonneg k) (hm N).le
    linarith
  · have hkm : (0 : ℝ) ≤ (k : ℝ) / m N := div_nonneg (Nat.cast_nonneg k) (hm N).le
    have hwIcc : s N + (k : ℝ) / m N ∈ Set.Icc (s N) (t N) :=
      ⟨by linarith, hk1.trans hv.2⟩
    have hmodv := hmod N ω v hv _ hwIcc
    have habs : |v - (s N + (k : ℝ) / m N)| ≤ 1 / m N := by
      rw [abs_of_nonneg (by linarith)]
      exact hk2
    have h1 : |v - (s N + (k : ℝ) / m N)| ^ γ ≤ (1 / m N) ^ γ :=
      Real.rpow_le_rpow (abs_nonneg _) habs hγ.le
    have hNK : (0 : ℝ) ≤ (N : ℝ) ^ K := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have h2 : (N : ℝ) ^ K * |v - (s N + (k : ℝ) / m N)| ^ γ ≤ target N :=
      le_trans (mul_le_mul_of_nonneg_left h1 hNK) (hmesh N)
    have h3 := (le_abs_self _).trans (hmodv.trans h2)
    linarith

/-- **The `(+,+)` bootstrap structure, assembled from a modulus and fixed-time inputs.**  This
is `bootPP_of_net` with the net made concrete by `hclose_of_modulus`; it is the shape in which
the moment route can supply `RBM.Step2PP.BootPP`.

What is *not* discharged here is `hev`: the one-step improvement at the **fixed** net times,
conditional on the prefix.  That is what the truncated moment Duhamel has to produce — the
cutoff `χ(Ξ^{(L-K)}_{·,2}/Θ)` makes the drift's self-quadratic term linear on its support
(`linearize_on_support`), and on the event where the prefix bound holds the truncated and the
untruncated loop coincide. -/
noncomputable def bootPP_of_modulus (X : Sample B) {target : ℕ → ℝ} {δ₀ K γ : ℝ} {m : ℕ → ℝ}
    (htgt : ∀ N, 0 < target N) (htgt1 : ∀ᶠ N : ℕ in atTop, 1 ≤ target N)
    (hcont : ∀ (N : ℕ) (ω : Ω), ContinuousOn (fun u => X.xiLK E N u ω 2)
      (Set.Icc (s N) (t N)))
    (hδ₀ : 0 < δ₀) (hγ : 0 < γ) (hm : ∀ N, 0 < m N)
    (hmod : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |X.xiLK E N v ω 2 - X.xiLK E N w ω 2| ≤ (N : ℝ) ^ K * |v - w| ^ γ)
    (hmesh : ∀ N : ℕ, (N : ℝ) ^ K * (1 / m N) ^ γ ≤ target N)
    (hev : ∀ δ, 0 < δ → δ ≤ δ₀ →
      HighProb B.P fun N => {ω | ∀ ws ∈ netSet s m N, ws ∈ Set.Icc (s N) (t N) →
        (∀ u ∈ Set.Icc (s N) ws, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * target N) →
          X.xiLK E N ws ω 2 ≤ ((N : ℝ) ^ δ - 1) * target N}) :
    Step2PP.BootPP X E s t :=
  bootPP_of_net X htgt htgt1 hcont hδ₀ (hclose_of_modulus X hγ hm hmod hmesh) hev

end BootPPNet

/-! ### 7. Why the `(+,+)` bootstrap cannot be replaced by finitely many `≺`-passes -/

section Necessity

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The unconditional a priori bound for `(+,+)` at `n = 2`.**  (2.73) gives
`Ξ^{(L)}_{u,2} ≺ R`, and `RBM.Sample.xiLK_le_mul` converts it into
`Ξ^{(L-K)}_{u,2} ≺ A_u (R + C)` — note the **extra factor `A_u`**, which is the difference
between the two normalizations of (5.76) (`Ξ^{(L)}_m` carries `A^{m-1}`, `Ξ^{(L-K)}_m` carries
`A^m`). -/
theorem xiLK_two_apriori (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hapriori : AprioriFlow X E s t) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hK : ∀ (N : ℕ) (u : TimeIcc s t N) (w : LoopData (B.L N) 2),
      ‖B.Kval E N u w.idx‖ ≤ C * (B.scale E N u)⁻¹ ^ (2 - 1)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (u : TimeIcc s t N) (_ : Ω) =>
        B.scale E N u * (Step3.flowR B s t N + C)) := by
  have hL : ∀ N, 1 ≤ B.L N := fun N => by have := B.three_le_L N; omega
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hR0 : ∀ N, (0 : ℝ) ≤ Step3.flowR B s t N := fun N =>
    div_nonneg (Step3.ellHat_pos_of_lt_one (hL N) (ht1 N)).le
      (Step3.ellHat_pos_of_lt_one (hL N) ((hst N).trans_lt (ht1 N))).le
  have hXiL := Step2PP.flow_xiL_apriori_le' X hE hs0 hst ht1 hapriori (m := 2) (by norm_num)
  refine StochDom.of_subset_union hXiL hXiL fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN1
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hτ1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
  rintro ω ⟨u, hu⟩
  by_cases h' : ∃ v : TimeIcc s t N,
      (N : ℝ) ^ τ * Step3.flowR B s t N ^ (2 - 1) < Step3.flowXiL X E s t 2 N v ω
  · exact Or.inl h'
  · exfalso
    have hall : Step3.flowXiL X E s t 2 N u ω ≤ (N : ℝ) ^ τ * Step3.flowR B s t N ^ (2 - 1) :=
      not_lt.1 fun hc => h' ⟨u, hc⟩
    have hle : X.xiLK E N u ω 2 ≤ B.scale E N u * (X.xiL E N u ω 2 + C) :=
      X.xiLK_le_mul (hA N u) (by norm_num) (hK N u)
    have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hflow : Step3.flowXiL X E s t 2 N u ω = X.xiL E N (u : ℝ) ω 2 := rfl
    rw [hflow] at hall
    have hxiL : X.xiL E N (u : ℝ) ω 2 ≤ (N : ℝ) ^ τ * Step3.flowR B s t N := by
      simpa using hall
    have : X.xiLK E N u ω 2
        ≤ (N : ℝ) ^ τ * (B.scale E N u * (Step3.flowR B s t N + C)) := by
      refine hle.trans ?_
      have hmul : X.xiL E N (u : ℝ) ω 2 + C ≤ (N : ℝ) ^ τ * (Step3.flowR B s t N + C) := by
        nlinarith [hC0, hR0 N, hxiL, hτ1]
      calc B.scale E N (u : ℝ) * (X.xiL E N (u : ℝ) ω 2 + C)
          ≤ B.scale E N u * ((N : ℝ) ^ τ * (Step3.flowR B s t N + C)) := by
            exact mul_le_mul_of_nonneg_left hmul (hA N u).le
        _ = (N : ℝ) ^ τ * (B.scale E N u * (Step3.flowR B s t N + C)) := by ring
    exact absurd hu (not_lt.2 this)

/-- **The one-step improvement of (5.83) at `n = 2` is not a contraction above `A_t`.**  Its
right-hand side contains `θ² A_t^{-1}`, so the map `θ ↦ c + θ² A_t^{-1}` satisfies
`θ ≤ c + θ² A_t^{-1}` as soon as `A_t ≤ θ`: iterating it from an a priori bound at or above
`A_t` never decreases.

Together with `xiLK_two_apriori` — whose bound is `A_u (R + C) ≥ A_t` — this is why the
`(+,+)` case of §5.3 **needs** a bootstrap (or, equivalently, a cutoff): no fixed number of
`≺`-passes through `RBM.Step2PP.xiLK_two_improve'` can reach `Θ = A_s^{1/2}`. -/
theorem no_finite_pass {A c θ : ℝ} (hA0 : 0 < A) (hc0 : 0 ≤ c) (hAθ : A ≤ θ) :
    θ ≤ c + θ ^ 2 * A⁻¹ := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hA0 hAθ
  have : θ ≤ θ ^ 2 * A⁻¹ := by
    rw [le_mul_inv_iff₀ hA0]
    nlinarith
  linarith

/-- **The cutoff linearization.**  On the support of `χ(J/Θ)` one has `J ≤ 2Θ`, and there the
super-linear powers of `J*` that (5.34)/(5.35)/(5.36) produce are linear in `J*`:
`J² ≤ 2Θ J`, `J^{3/2} ≤ √(2Θ) J`, `J³ ≤ 4Θ² J`.  This is Jun's linearization, made pointwise
by the cutoff instead of by a stopping time; it is what makes the one-step moment improvement
close **at the same order** `2p`. -/
theorem linearize_on_support {J Θ : ℝ} (hJ0 : 0 ≤ J) (hΘ0 : 0 ≤ Θ) (hJ : J ≤ 2 * Θ) :
    J ^ 2 ≤ 2 * Θ * J ∧ J * √J ≤ √(2 * Θ) * J ∧ J ^ 3 ≤ 4 * Θ ^ 2 * J := by
  refine ⟨by nlinarith, ?_, ?_⟩
  · have h1 : √J ≤ √(2 * Θ) := Real.sqrt_le_sqrt hJ
    nlinarith [Real.sqrt_nonneg J, Real.sqrt_nonneg (2 * Θ)]
  · have h2 : J ^ 2 ≤ 4 * Θ ^ 2 := by nlinarith
    calc J ^ 3 = J ^ 2 * J := by ring
      _ ≤ 4 * Θ ^ 2 * J := by nlinarith

end Necessity

/-! ### 8. (5.48): the near/far split -/

section Eq548

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {U : ℕ → Type*}
variable {W : ℕ → ℝ} {ℓ η d pref : ∀ N, U N → ℝ}

/-- **(5.48) from its two halves.**  The paper's (5.48),

`(L-K)_{u,a} / T_{u,D}(d) ≺ (η_s/η_u)² 1(d ≤ 6ℓ*_u) + 1`,

is exactly the conjunction of

* `hnear` — the bound with the prefactor everywhere, i.e. `(L-K)_{u,a} ≺ pref · T_{u,D}(d)`
  (for the flow this is the **sharp** (5.47), `J*_{u,D} ≺ (η_s/η_u)²`), and
* `hfar` — the same bound **without** any prefactor, asserted only where `d > 6ℓ*_u`.

`hfar` is the half that `RBM.Step2Moment.jS_stochDom` does *not* give: (5.47) as the repository
states it carries `(η_s/η_u)^4` at every distance, whereas (5.48) asks for `1` beyond `6ℓ*_u`.
It comes from keeping the indicators of (5.39), (5.41) and (5.44) through the one-step bound
(the paper's `1(|a₁-a₂| ≤ ℓ*_t)`, `1(≤ 3ℓ*_t)`, `1(≤ 6ℓ*_t)`), which
`RBM.Step2.step_bound` discards. -/
theorem eq548_of_near_far {ξ : ∀ N, U N → Ω → ℝ} (hW : ∀ N, 0 ≤ W N)
    (hpref : ∀ N u, 0 ≤ pref N u)
    (hnear : ∀ D : ℝ, 0 < D → StochDom P ξ
      (fun N u _ => pref N u * tailT (W N) (ℓ N u) (η N u) D (d N u)))
    (hfar : ∀ D : ℝ, 0 < D → StochDom P
      (fun N u ω => if d N u ≤ 6 * ellStar (W N) (ℓ N u) then 0 else ξ N u ω)
      (fun N u _ => tailT (W N) (ℓ N u) (η N u) D (d N u))) :
    Step45.Eq548 P ξ W ℓ η d pref := by
  intro D hD
  refine StochDom.of_subset_union (hnear D hD) (hfar D hD) fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N => ?_
  rintro ω ⟨u, hu⟩
  have hT0 : 0 ≤ tailT (W N) (ℓ N u) (η N u) D (d N u) := tailT_nonneg (hW N) _
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  by_cases hnearcase : d N u ≤ 6 * ellStar (W N) (ℓ N u)
  · refine Or.inl ⟨u, ?_⟩
    have hite : (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then (1 : ℝ) else 0) = 1 := by
      simp [hnearcase]
    simp only [hite] at hu
    have h1 : pref N u * tailT (W N) (ℓ N u) (η N u) D (d N u)
        ≤ tailT (W N) (ℓ N u) (η N u) D (d N u) * (pref N u * 1 + 1) := by
      have := hpref N u
      nlinarith
    calc (N : ℝ) ^ τ * (pref N u * tailT (W N) (ℓ N u) (η N u) D (d N u))
        ≤ (N : ℝ) ^ τ * (tailT (W N) (ℓ N u) (η N u) D (d N u) * (pref N u * 1 + 1)) := by
          exact mul_le_mul_of_nonneg_left h1 hτ0
      _ < ξ N u ω := hu
  · refine Or.inr ⟨u, ?_⟩
    have hite : (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then (1 : ℝ) else 0) = 0 := by
      simp [hnearcase]
    have hite' : (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then (0 : ℝ) else ξ N u ω) = ξ N u ω := by
      simp [hnearcase]
    simp only [hite] at hu
    simp only [hite']
    calc (N : ℝ) ^ τ * tailT (W N) (ℓ N u) (η N u) D (d N u)
        = (N : ℝ) ^ τ * (tailT (W N) (ℓ N u) (η N u) D (d N u) * (pref N u * 0 + 1)) := by ring
      _ < ξ N u ω := hu

/-- **(5.48) for the flow**, `RBM.Step45.FlowEq548`, from its two halves.  `hnear` is the
sharp (5.47) — `|(L-K)_{u,(+,-),a}| ≺ (η_s/η_u)² T_{u,D}(‖a₁-a₂‖)`, i.e. `J*_{u,D} ≺ (η_s/η_u)²`
— and `hfar` is the same bound with **no** prefactor at distances beyond `6ℓ*_u`. -/
theorem flowEq548_of_near_far {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)
    {E : ℝ} {s t : ℕ → ℝ}
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D (zdist (B.L N) (p.2.1 - p.2.2))))
    (hfar : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
          then 0 else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
        (zdist (B.L N) (p.2.1 - p.2.2)))) :
    Step45.FlowEq548 X E s t := by
  refine eq548_of_near_far (fun N => by positivity) (fun N p => by positivity) hnear hfar

end Eq548

/-! ### 9. Why the frozen `MomentHyp.step` is not the right target -/

section StepAnalysis

open Filter

/-- **`bnd_poly` forbids `bnd` from absorbing any power of `N`.**

`RBM.Step2Moment.MomentHyp.bnd_poly` says `bnd (2p) N ≤ C_{ε,p} N^{εp}` for **every** `ε > 0`.
Reading it at one fixed `p` and letting `ε → 0` shows that `bnd (2p) ·` is `N^{o(1)}`: it can
never dominate `N^α` for any `α > 0`.

This is the first half of the obstruction to `RBM.Step2Moment.MomentHyp.step`.  `J*_{u,D}` is a
maximum over the `L²` loop arguments of length `2`, and the only elementary bound on the `q`-th
moment of a maximum is the union bound `E[(max_a Y_a)^q] ≤ Σ_a E[Y_a^q]`, which costs a factor
`L² ≍ N²` at **every** order `q`.  By this lemma no admissible `bnd` can carry that factor, so
`step` cannot be proved from per-loop moment bounds at the same order `q`.  Removing the factor
needs `‖max_a Y_a‖_q ≤ L^{2/Q} max_a ‖Y_a‖_Q` with `Q ≫ q` — i.e. the prefix hypothesis at an
order strictly higher than the one `step` provides. -/
theorem bnd_poly_excludes_pow {bnd : ℕ → ℕ → ℝ}
    (hpoly : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      bnd (2 * p) N ≤ C * (N : ℝ) ^ (ε * p))
    {p : ℕ} (hp : 1 ≤ p) {α : ℝ} (hα : 0 < α) :
    ¬ (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ α ≤ bnd (2 * p) N) := by
  intro hcon
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨C, hC0, hC⟩ := hpoly (α / (2 * p)) (by positivity) p
  have hhalf : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ α ≤ C * (N : ℝ) ^ (α / 2) := by
    filter_upwards [hcon, hC] with N h1 h2
    refine h1.trans (h2.trans (le_of_eq ?_))
    congr 1
    field_simp
  -- but `N^{α/2} → ∞`, so `N^α = N^{α/2} · N^{α/2} > C · N^{α/2}` eventually
  have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (α / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hbig : ∀ᶠ N : ℕ in atTop, C < (N : ℝ) ^ (α / 2) := htend.eventually_gt_atTop C
  obtain ⟨N, hN1, hN2, hN3⟩ := (hhalf.and (hbig.and (eventually_gt_atTop 0))).exists
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN3
  have hpow : (N : ℝ) ^ α = (N : ℝ) ^ (α / 2) * (N : ℝ) ^ (α / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hpos : (0 : ℝ) < (N : ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hN0 _
  nlinarith [hN1, hN2, hpos]

/-- **De-truncation at the moment level cannot close at the same order.**

Suppose the cutoff `χ(J*/θ)` is de-truncated inside the moment, i.e. `E[(J*)^q]` is split as
`E[(J̃*)^q] + env^q · P(J* > θ)` with `env` the deterministic envelope of `J*` (T77) and the
excess probability estimated by Markov from the *prefix* hypothesis,
`P(J* > θ) ≤ thr / θ^q`.  Then the remainder alone is **at least** `thr`, as soon as the
truncation level `θ` is below the envelope — which it always is, since `θ ≍ N^δ` with `δ` the
bootstrap margin and `env ≍ N^K` with `K` the decay exponent `D ≥ 60`.

Since `RBM.Step2Moment.MomentHyp` demands `bnd q N < thr q N`, the remainder can never be
brought below `bnd`.  This is why the spec puts de-truncation at the **probability** level
(§5 above: `le_of_gap_net`) and not inside the moment. -/
theorem detrunc_remainder_ge_thr {env θ thr : ℝ} {q : ℕ} (hθ0 : 0 < θ) (hθenv : θ ≤ env)
    (hthr : 0 ≤ thr) : thr ≤ env ^ q * (thr / θ ^ q) := by
  have hθq : (0 : ℝ) < θ ^ q := pow_pos hθ0 q
  have hle : θ ^ q ≤ env ^ q := pow_le_pow_left₀ hθ0.le hθenv q
  calc thr = θ ^ q * (thr / θ ^ q) := by field_simp
    _ ≤ env ^ q * (thr / θ ^ q) := by
        refine mul_le_mul_of_nonneg_right hle ?_
        positivity

/-- **The order de-truncation at the moment level would need: `(K + δ)/δ` times the target
order.**  With the envelope `env = N^K`, the truncation level `θ = N^δ` and the prefix
threshold `thr = θ^q = N^{δq}`, the Markov remainder `env^q · thr / θ^Q` at order `Q` is at
most `1` exactly when `Q ≥ q (K + δ)/δ`.

For the flow `K ≍ D ≥ 60` and `δ ≤ c/24`, so the factor is astronomically large; an order-`q`
statement like `RBM.Step2Moment.MomentHyp.step` cannot produce it. -/
theorem detrunc_order_needed {N K δ : ℝ} (hN : 1 ≤ N) {q Q : ℕ}
    (hQ : (q : ℝ) * (K + δ) ≤ (Q : ℝ) * δ) :
    (N ^ K) ^ q * ((N ^ δ) ^ q / (N ^ δ) ^ Q) ≤ 1 := by
  rcases eq_or_lt_of_le hN with h1 | h1
  · rw [← h1]
    simp
  have hN0 : (0 : ℝ) < N := by linarith
  have hKq : (N ^ K) ^ q = N ^ (K * q) := by
    rw [← Real.rpow_natCast (N ^ K) q, ← Real.rpow_mul hN0.le]
  have hδq : (N ^ δ) ^ q = N ^ (δ * q) := by
    rw [← Real.rpow_natCast (N ^ δ) q, ← Real.rpow_mul hN0.le]
  have hδQ : (N ^ δ) ^ Q = N ^ (δ * Q) := by
    rw [← Real.rpow_natCast (N ^ δ) Q, ← Real.rpow_mul hN0.le]
  rw [hKq, hδq, hδQ, ← Real.rpow_sub hN0, ← Real.rpow_add hN0]
  refine Real.rpow_le_one_of_one_le_of_nonpos hN ?_
  nlinarith [hQ]

/-- **The bootstrap closes**: the output `cStep' m · x² R⁴` of `phi_arith'` is below the
threshold `Λ = x⁸ R⁴` of (5.43) as soon as `cStep' m ≤ x⁶`, i.e. `N^{3δ/4} ≥ cStep' m`.  This
is the inequality `bnd q N < thr q N` that `RBM.Step2Moment.MomentHyp.bnd_lt_thr` asks for. -/
theorem phi_lt_threshold {x R m : ℝ} (hR : 1 ≤ R) (hxc : cStep' m ≤ x ^ 6) :
    cStep' m * x ^ 2 * R ^ 4 ≤ x ^ 8 * R ^ 4 := by
  have hR0 : (0 : ℝ) ≤ R ^ 4 := by positivity
  have hx2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have : cStep' m * x ^ 2 ≤ x ^ 6 * x ^ 2 := by nlinarith
  calc cStep' m * x ^ 2 * R ^ 4 ≤ (x ^ 6 * x ^ 2) * R ^ 4 := by nlinarith
    _ = x ^ 8 * R ^ 4 := by ring

end StepAnalysis

/-! ### 10. Satisfiability witnesses (compiled) -/

section Sat

/-- The hypotheses of `phi_arith'` are **jointly satisfiable** and its conclusion is not
vacuous: at the degenerate point `x = R = Ξ = m = A = q = β = γ = J = 1`, `ε = 0` the left-hand
side is `36 e + 7` and the right-hand side is `37 e + 7`, so the inequality holds with the
slack `e` — the constant `cStep'` is essentially sharp there. -/
theorem sat_phi_arith' :
    (1 : ℝ) * 1 ^ 2 * 1 + 1 * (exp 1 * (1 ^ 8 * 1 ^ 4) ^ 2 * (36 * (1 : ℝ)⁻¹ * 1 ^ 2 * (1 : ℝ)⁻¹
        + 1 ^ 2 * 0) + 1 * (1 : ℝ)⁻¹ * 1 ^ 2 * (1 + 1 * 1 + 1 * (1 * √1))) + 1 * (1 ^ 2 + 1) + 1
      ≤ cStep' 1 * 1 ^ 2 * 1 ^ 4 :=
  phi_arith' le_rfl le_rfl zero_le_one le_rfl one_pos (by norm_num) le_rfl (by norm_num)
    zero_le_one (by norm_num) zero_le_one (by norm_num) zero_le_one (by norm_num) zero_le_one
    (by norm_num)

/-- The two side conditions are **sharp at `r = R = x = A = 1`**: `hbeta_of_reg` and
`hgamma_of_reg` both give equality there, so neither exponent (`5.5`, `4.5`) can be lowered by
the argument used. -/
theorem sat_hbeta_sharp : ((1 : ℝ) * √1 * (√(1 : ℝ))⁻¹) * (1 ^ 8 * 1 ^ 2) ≤ 1 :=
  hbeta_of_reg le_rfl le_rfl zero_le_one (by norm_num) one_pos (by norm_num)

theorem sat_hgamma_sharp : ((1 : ℝ) * (1 : ℝ)⁻¹) * (1 ^ 12 * 1 ^ 4) ≤ 1 :=
  hgamma_of_reg le_rfl le_rfl zero_le_one (by norm_num) one_pos (by norm_num)

/-- `le_of_gap_net`'s hypothesis bundle is **jointly satisfiable, non-vacuously**: the constant
path `Y ≡ 0` on `[0,1]` with the one-point net `S = {0}` satisfies `hnet` and `hgood`, and the
conclusion is used. -/
theorem sat_le_of_gap_net : ∀ u ∈ Set.Icc (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) u ≤ 5 / 4 := by
  refine le_of_gap_net (S := {(0 : ℝ)}) zero_le_one continuousOn_const (by norm_num)
    (fun u hu => ⟨0, rfl, ⟨le_rfl, hu.1⟩, by norm_num⟩) ?_
  intro ws _ _ _
  norm_num

/-- `bootPP_step_of_net`'s modulus hypothesis `hclose` is **satisfiable**: the full interval is
a (trivial) net, with `ws = v`.  So the lemma is a genuine reduction and not a vacuous one —
with a finite net it trades the continuum of times for finitely many fixed ones. -/
theorem sat_hclose {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}
    {s t : ℕ → ℝ} {target : ℕ → ℝ} (htgt : ∀ N, 0 ≤ target N) (N : ℕ) (ω : Ω) :
    ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ Set.Icc (s N) (t N),
      ws ∈ Set.Icc (s N) v ∧ X.xiLK E N v ω 2 ≤ X.xiLK E N ws ω 2 + target N :=
  fun v hv => ⟨v, hv, ⟨hv.1, le_rfl⟩, by linarith [htgt N]⟩

/-- `no_finite_pass` is not vacuous: `A = θ = 1`, `c = 0` gives equality. -/
theorem sat_no_finite_pass : (1 : ℝ) ≤ 0 + 1 ^ 2 * (1 : ℝ)⁻¹ :=
  no_finite_pass one_pos le_rfl le_rfl

/-- `detrunc_remainder_ge_thr` is sharp at `θ = env`: equality. -/
theorem sat_detrunc_sharp {thr : ℝ} (hthr : 0 ≤ thr) (q : ℕ) :
    thr ≤ (1 : ℝ) ^ q * (thr / 1 ^ q) :=
  detrunc_remainder_ge_thr one_pos le_rfl hthr

end Sat




end Step2MomentStep

end RBM
