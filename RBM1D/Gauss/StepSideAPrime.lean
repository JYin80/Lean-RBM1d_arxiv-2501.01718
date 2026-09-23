/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.StepSideAPrimeCore
import RBM1D.Hierarchy.Step2MomentStep

/-!
# The one-step arithmetic with room for the weight-support constant (T263, referee (S7))

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.47), **rescaled** so that the a priori level carried by the
soft-max cutoff weight fits.

## Why a second version of the arithmetic

`RBM.Step2MomentStep.phi_arith'` runs the one-step accounting at the a priori level
`Jv ≤ x⁸R⁴ = N^δ R⁴` and **all eight of its side conditions are met at equality** by the
witness `RBM.Step2Bootstrap.sat_StepSide_gt_one`.  Zero margin means that a single constant
factor breaks it.  In the `(A′)` route of the V548 referee report the level really available on
the support of the weight is

`Jv ≤ 4·e·N^{2δ}·R⁴`

(`prefNet`'s level is `N^{2δ}`, the soft maximum costs another `e`, and the widened weight
`χ(J̃/(2Θ′))^{2p}` another `2`), i.e. `Jv ≤ 4e·x^{16}R⁴` in the variable `x = N^{δ/8}`.

This file reruns the arithmetic at

`Jv ≤ cWt · x^{16} · R⁴`,  `cWt = 4e + 2`,

which leaves the genuine slack `2x^{16}R⁴` above the prior bound (`prior_lt_level`).  The
side conditions are rescaled accordingly — `A ≥ cWt²x^{33}R^{10}`, `ε·cWt²x^{33}R^{10} ≤ 1`,
`cWt·β·x^{16}R² ≤ 1`, `cWt^{3/2}·γ·x^{24}R⁴ ≤ 1` — and one **new slot** `κ` is opened for the
cross term of the fixed-`ω` generator identity, with the same budget `κ ≤ x` as the `≺`-loss
`Ξ`.  The output grows by exactly that one slot: `(cStep' m + 1)·x²R⁴`.

## Contents

* §1 `cWt` and its elementary bounds; `prior_lt_level`.
* §2 `phi_arith''` — the arithmetic itself, and `stepRhs''`/`StepSide''`/`stepRhs''_le`,
  `stepRhs''_div_le` packaging it the way `RBM.CutHypTheta.stepRhs` packages `phi_arith'`.
* §3 `phi_lt_threshold''` — the rescaled output is still below the rescaled threshold, so
  the bootstrap still closes (the strengthening is not loose to the point of being empty).
* §4 `sideBundle''_of_A` and `side_conditions_of_reg''` — the rescaled bundle is discharged
  on the flow from (2.72) with a gain, exactly as `RBM.Step2MomentStep.side_conditions_of_reg`
  discharges the old one.  Here the far-field threshold `A ≥ cWt²x^{33}R^{10}` is the single
  bottleneck: it implies both rescaled far-field conditions.
* §5 satisfiability **with margin**: `sat_StepSide''_half` meets every constraint with a
  factor `2` to spare, and `sat_StepSide''_half_strict` records that fact as strict
  inequalities.  (Contrast `RBM.Step2Bootstrap.sat_StepSide_gt_one`, which is tight.)

Nothing in `RBM.Step2MomentStep` or `RBM.CutHypTheta` is changed; every name here is new.
-/

namespace RBM

namespace StepSideAPrime

open Real

/-! ### 1. Elementary bounds for the weight-support constant -/

theorem one_le_cWt : 1 ≤ cWt := by
  have : (1 : ℝ) ≤ exp 1 := one_le_exp (by norm_num)
  unfold cWt; linarith

theorem one_le_sqrt_cWt : 1 ≤ √cWt := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt one_le_cWt

/-- **The prior bound on the support of the weight fits strictly below the new level.**  The
slack is `2·x^{16}R⁴`, which is what `phi_arith'`'s zero-margin level `x⁸R⁴` did not have. -/
theorem prior_lt_level {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    4 * exp 1 * (x ^ 16 * R ^ 4) < cWt * (x ^ 16 * R ^ 4) := by
  have h1 : (1 : ℝ) ≤ x ^ 16 * R ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have : 4 * exp 1 * (x ^ 16 * R ^ 4) + 2 * 1 ≤ 4 * exp 1 * (x ^ 16 * R ^ 4)
      + 2 * (x ^ 16 * R ^ 4) := by linarith
  unfold cWt; nlinarith

/-- The old level `x⁸R⁴` is strictly inside the new one, so nothing is lost. -/
theorem old_level_lt {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    x ^ 8 * R ^ 4 < cWt * (x ^ 16 * R ^ 4) := by
  have hx8 : x ^ 8 ≤ x ^ 16 := pow_le_pow_right₀ hx (by norm_num)
  have h1 : (1 : ℝ) ≤ x ^ 16 * R ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hR4 : (0 : ℝ) < R ^ 4 := by positivity
  have h2 : x ^ 8 * R ^ 4 ≤ x ^ 16 * R ^ 4 := by gcongr
  have he : (1 : ℝ) ≤ exp 1 := one_le_exp (by norm_num)
  unfold cWt; nlinarith

/-! ### 2. The arithmetic -/

section Arith

/-- **The arithmetic of (5.40)–(5.47) at the weight-support level** (referee (S7)).

This is `RBM.Step2MomentStep.phi_arith'` with the level `x⁸R⁴` of (5.43) replaced by
`cWt·x^{16}R⁴` everywhere it occurs — in the hypothesis on `Jv` and in the square of the
level multiplying the `A⁻¹` and `ε` terms of (5.40) — the four far-field side conditions
rescaled accordingly, and one new slot `κ ≤ x` for the cross term of the fixed-`ω`
generator identity (referee (S5)).

The output is `(cStep' m + 1)·x²R⁴`: the seven old terms still cost `cStep' m · x²R⁴`
(each of them pays exactly what it paid before, because every rescaled side condition carries
the matching power of `cWt`), and the new slot costs one more `x²R⁴`. -/
theorem phi_arith'' {x R Ξ m A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (_hΞ0 : 0 ≤ Ξ)
    (hΞ : Ξ ≤ x) (hm0 : 0 < m) (hA : cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε * (cWt ^ 2 * x ^ 33 * R ^ 10) ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ R ^ 2)
    (hβ0 : 0 ≤ β) (hβ : β * (cWt * x ^ 16 * R ^ 2) ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ : γ * (cWt * √cWt * x ^ 24 * R ^ 4) ≤ 1)
    (_hκ0 : 0 ≤ κ) (hκ : κ ≤ x)
    (hJ0 : 0 ≤ Jv) (hJΛ : Jv ≤ cWt * x ^ 16 * R ^ 4) :
    x * R ^ 2 * Ξ + x * R ^ 2 * κ
      + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1
      ≤ (Step2MomentStep.cStep' m + 1) * x ^ 2 * R ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hc0 : 0 < cWt := cWt_pos
  have hc1 : 1 ≤ cWt := one_le_cWt
  have hsc1 : 1 ≤ √cWt := one_le_sqrt_cWt
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hxA : cWt ^ 2 * x ^ 33 * R ^ 10 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hA
  -- `√Jv ≤ √cWt · x⁸ R²`
  have hsq : √Jv ≤ √cWt * x ^ 8 * R ^ 2 := by
    have hsq' : (√cWt * x ^ 8 * R ^ 2) ^ 2 = cWt * x ^ 16 * R ^ 4 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc0.le]; ring
    have := Real.sqrt_le_sqrt hJΛ
    rwa [← hsq', Real.sqrt_sq (by positivity)] at this
  have hsq0 : (0 : ℝ) ≤ √Jv := Real.sqrt_nonneg _
  have hJJ : Jv * √Jv ≤ cWt * √cWt * x ^ 24 * R ^ 6 := by
    calc Jv * √Jv ≤ (cWt * x ^ 16 * R ^ 4) * (√cWt * x ^ 8 * R ^ 2) :=
          mul_le_mul hJΛ hsq hsq0 (by positivity)
      _ = cWt * √cWt * x ^ 24 * R ^ 6 := by ring
  -- the eight terms
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 4 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
      _ ≤ x ^ 2 * R ^ 4 := by gcongr
  -- the new slot: the cross term of the fixed-`ω` generator identity
  have tκ : x * R ^ 2 * κ ≤ x ^ 2 * R ^ 4 := by
    calc x * R ^ 2 * κ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
      _ ≤ x ^ 2 * R ^ 4 := by gcongr
  have t2 : Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
      ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        = 36 * exp 1 * m⁻¹ * (Ξ * (cWt ^ 2 * x ^ 32 * R ^ 10) * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * (cWt ^ 2 * x ^ 32 * R ^ 10) * A⁻¹) := by gcongr
      _ = 36 * exp 1 * m⁻¹ * (cWt ^ 2 * x ^ 33 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by gcongr
  have t3 : Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
      ≤ exp 1 * (x ^ 2 * R ^ 4) := by
    calc Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        = exp 1 * (Ξ * (cWt ^ 2 * x ^ 32 * R ^ 10) * ε) := by ring
      _ ≤ exp 1 * (x * (cWt ^ 2 * x ^ 32 * R ^ 10) * ε) := by gcongr
      _ = exp 1 * (ε * (cWt ^ 2 * x ^ 33 * R ^ 10)) := by ring
      _ ≤ exp 1 * 1 := by gcongr
      _ ≤ exp 1 * (x ^ 2 * R ^ 4) := by gcongr
  have t4 : Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ x * (x * m⁻¹ * R ^ 2 * R ^ 2) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := by ring
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv)) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv))
        ≤ x * (x * m⁻¹ * R ^ 2 * (β * (cWt * x ^ 16 * R ^ 4))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) * (β * (cWt * x ^ 16 * R ^ 2)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := mul_one _
  have t6 : Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv))) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv)))
        ≤ x * (x * m⁻¹ * R ^ 2 * (γ * (cWt * √cWt * x ^ 24 * R ^ 6))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) * (γ * (cWt * √cWt * x ^ 24 * R ^ 4)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := mul_one _
  have t7 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 4) := by nlinarith
  have hsplit : x * R ^ 2 * Ξ + x * R ^ 2 * κ
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
          + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1
      = x * R ^ 2 * Ξ + x * R ^ 2 * κ
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        + Ξ * (x * m⁻¹ * R ^ 2 * q)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv)) + Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv)))
        + x * (R ^ 2 + 1) + 1 := by ring
  rw [hsplit, Step2MomentStep.cStep']
  nlinarith

end Arith

/-! ### 2′. The packaged form -/

section Packaged

/-- The left-hand side of `phi_arith''`, verbatim: the seven terms of (5.39)–(5.44) at the
weight-support level, plus the cross-term slot `κ`. -/
noncomputable def stepRhs'' (m x R Ξ A ε q β γ κ Jv : ℝ) : ℝ :=
  x * R ^ 2 * Ξ + x * R ^ 2 * κ
    + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1

/-- The side conditions of `phi_arith''`, verbatim.  Compared with
`RBM.CutHypTheta.StepSide`: the level is `cWt·x^{16}R⁴` instead of `x⁸R⁴`, the four
far-field conditions carry the matching powers of `cWt`, and the slot `κ` is new. -/
structure StepSide'' (x R Ξ A ε q β γ κ Jv : ℝ) : Prop where
  /-- `R = η_s/η_v ≥ 1` on the window. -/
  R_ge : 1 ≤ R
  /-- (5.35)'s loss is a single `≺`-power. -/
  Ξ_nonneg : 0 ≤ Ξ
  /-- ditto. -/
  Ξ_le : Ξ ≤ x
  /-- the threshold `A_u` of (5.42), rescaled: `cWt²x^{33}R^{10}`. -/
  A_ge : cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A
  /-- the far-field remainder of (5.40). -/
  ε_nonneg : 0 ≤ ε
  /-- ditto, rescaled. -/
  ε_le : ε * (cWt ^ 2 * x ^ 33 * R ^ 10) ≤ 1
  /-- the near-field coefficient `(ℓ_u/ℓ_s)³` of (5.41); unchanged, it carries no level. -/
  q_nonneg : 0 ≤ q
  /-- its cap, `R²` after the (2.73) reduction. -/
  q_le : q ≤ R ^ 2
  /-- the linear far-field coefficient `r^{3/2}A^{-1/2}`. -/
  β_nonneg : 0 ≤ β
  /-- ditto, rescaled: `cWt·β·x^{16}R² ≤ 1`. -/
  β_le : β * (cWt * x ^ 16 * R ^ 2) ≤ 1
  /-- the `3/2`-power far-field coefficient `rA⁻¹`. -/
  γ_nonneg : 0 ≤ γ
  /-- ditto, rescaled: `cWt^{3/2}·γ·x^{24}R⁴ ≤ 1`. -/
  γ_le : γ * (cWt * √cWt * x ^ 24 * R ^ 4) ≤ 1
  /-- **new slot**: the cross term of the fixed-`ω` generator identity (referee (S5)),
  with the same budget as the `≺`-loss. -/
  κ_nonneg : 0 ≤ κ
  /-- ditto. -/
  κ_le : κ ≤ x
  /-- the a priori level on the support of the weight. -/
  Jv_nonneg : 0 ≤ Jv
  /-- ditto: `cWt·x^{16}R⁴`, which by `prior_lt_level` strictly contains `4e·N^{2δ}R⁴`. -/
  Jv_le : Jv ≤ cWt * x ^ 16 * R ^ 4

/-- **`phi_arith''`, packaged.** -/
theorem stepRhs''_le {m x R Ξ A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide'' x R Ξ A ε q β γ κ Jv) :
    stepRhs'' m x R Ξ A ε q β γ κ Jv ≤ (Step2MomentStep.cStep' m + 1) * x ^ 2 * R ^ 4 :=
  phi_arith'' hx H.R_ge H.Ξ_nonneg H.Ξ_le hm H.A_ge H.ε_nonneg H.ε_le H.q_nonneg H.q_le
    H.β_nonneg H.β_le H.γ_nonneg H.γ_le H.κ_nonneg H.κ_le H.Jv_nonneg H.Jv_le

/-- In the blunt normalization `J*/R⁴` the one-step output is `(cStep' m + 1)·x²`. -/
theorem stepRhs''_div_le {m x R Ξ A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide'' x R Ξ A ε q β γ κ Jv) :
    stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4 ≤ (Step2MomentStep.cStep' m + 1) * x ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith [H.R_ge]
  have hR0 : (0 : ℝ) < R ^ 4 := by positivity
  rw [div_le_iff₀ hR0]
  exact stepRhs''_le hx hm H

/-- The one-step right-hand side is at least its own constant term `1`. -/
theorem one_le_stepRhs'' {m x R Ξ A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide'' x R Ξ A ε q β γ κ Jv) : 1 ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith [H.R_ge]
  have hAthr : (0 : ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10 :=
    mul_pos (mul_pos (pow_pos cWt_pos 2) (pow_pos hx0 33)) (pow_pos hR0 10)
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le hAthr H.A_ge
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hJ0 := H.Jv_nonneg
  have hsJ : (0 : ℝ) ≤ √Jv := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) ≤ x * R ^ 2 * Ξ :=
    mul_nonneg (mul_nonneg hx0.le (by positivity)) H.Ξ_nonneg
  have h2 : (0 : ℝ) ≤ x * R ^ 2 * κ :=
    mul_nonneg (mul_nonneg hx0.le (by positivity)) H.κ_nonneg
  have h3 : (0 : ℝ) ≤ Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2
      * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) := by
    have hi : (0 : ℝ) ≤ A⁻¹ := (inv_pos.2 hA0).le
    have hbJ : (0 : ℝ) ≤ β * Jv := mul_nonneg H.β_nonneg hJ0
    have hgJ : (0 : ℝ) ≤ γ * (Jv * √Jv) :=
      mul_nonneg H.γ_nonneg (mul_nonneg hJ0 hsJ)
    have hbr1 : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε :=
      add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hi)
        (mul_nonneg (by positivity) H.ε_nonneg)
    have hc : (0 : ℝ) ≤ exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2
        * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) :=
      mul_nonneg (mul_nonneg (exp_pos 1).le (sq_nonneg _)) hbr1
    have hsum : (0 : ℝ) ≤ q + β * Jv + γ * (Jv * √Jv) := by
      have := H.q_nonneg; linarith
    have hd : (0 : ℝ) ≤ x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hx0.le hmi.le) (by positivity)) hsum
    exact mul_nonneg H.Ξ_nonneg (by linarith)
  have h4 : (0 : ℝ) ≤ x * (R ^ 2 + 1) := mul_nonneg hx0.le (by positivity)
  unfold stepRhs''
  linarith

end Packaged

/-! ### 3. The bootstrap still closes -/

/-- **The rescaled output is below the rescaled threshold.**  `phi_arith''` outputs
`(cStep' m + 1)x²R⁴` and the a priori level of (5.43) is now `cWt·x^{16}R⁴`, so the margin
is `cStep' m + 1 ≤ cWt·x^{14}` — strictly weaker than `phi_lt_threshold`'s
`cStep' m ≤ x⁶`, because the level grew by `cWt·x⁸` while the output grew by `1`. -/
theorem phi_lt_threshold'' {x R m : ℝ} (hR : 1 ≤ R)
    (hxc : Step2MomentStep.cStep' m + 1 ≤ cWt * x ^ 14) :
    (Step2MomentStep.cStep' m + 1) * x ^ 2 * R ^ 4 ≤ cWt * x ^ 16 * R ^ 4 := by
  have hR0 : (0 : ℝ) < R ^ 4 := by positivity
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have : (Step2MomentStep.cStep' m + 1) * x ^ 2 ≤ cWt * x ^ 14 * x ^ 2 := by gcongr
  calc (Step2MomentStep.cStep' m + 1) * x ^ 2 * R ^ 4
      ≤ cWt * x ^ 14 * x ^ 2 * R ^ 4 := by gcongr
    _ = cWt * x ^ 16 * R ^ 4 := by ring

/-! ### 4. The rescaled bundle is satisfiable on the flow -/

section Reg

variable {x R r A : ℝ}

/-- **The rescaled far-field threshold is the single bottleneck.**  From
`A ≥ cWt²x^{33}R^{10}` alone — together with `r² ≤ R` (`RBM.Step2MomentStep.ratio_sq_le`) —
both rescaled far-field side conditions follow:

* `β = r^{3/2}A^{-1/2}` needs `r³cWt²x^{32}R⁴ ≤ A`, and `r³ ≤ R^{3/2}`;
* `γ = rA⁻¹` needs `r·cWt^{3/2}x^{24}R⁴ ≤ A`, and `r ≤ R^{1/2}`.

Both are implied by `A ≥ cWt²x^{33}R^{10}`, with `R^{4.5}` resp. `R^{5.5}` to spare. -/
theorem sideBundle''_of_A (hx : 1 ≤ x) (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R)
    (hA : cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A) :
    (r * √r * (√A)⁻¹) * (cWt * x ^ 16 * R ^ 2) ≤ 1 ∧
      (r * A⁻¹) * (cWt * √cWt * x ^ 24 * R ^ 4) ≤ 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : 0 < cWt := cWt_pos
  have hc1 : 1 ≤ cWt := one_le_cWt
  have hsc1 : 1 ≤ √cWt := one_le_sqrt_cWt
  have hscsq : √cWt ^ 2 = cWt := Real.sq_sqrt hc0.le
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  have hsr : (0 : ℝ) ≤ √r := Real.sqrt_nonneg _
  have hx1 : (1 : ℝ) ≤ x := hx
  constructor
  · -- `β = r^{3/2}A^{-1/2}`
    set β : ℝ := r * √r * (√A)⁻¹ with hβdef
    have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
    have hβsq : β ^ 2 = r ^ 3 * A⁻¹ := by
      rw [hβdef, mul_pow, mul_pow, Real.sq_sqrt hr0, ← Real.sqrt_inv,
        Real.sq_sqrt (by positivity)]
      ring
    have h6 : (r ^ 3) ^ 2 ≤ R ^ 3 := by
      calc (r ^ 3) ^ 2 = (r ^ 2) ^ 3 := by ring
        _ ≤ R ^ 3 := by gcongr
    -- squared target: `r³·cWt²x^{32}R⁴ ≤ A`
    have hkey : r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 4) ≤ A := by
      have hlhs0 : (0 : ℝ) ≤ r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 4) := by positivity
      have hAsq : (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 ≤ A ^ 2 := by
        have h0 : (0 : ℝ) ≤ cWt ^ 2 * x ^ 33 * R ^ 10 := by positivity
        nlinarith
      have hxx : x ^ 64 ≤ x ^ 66 := pow_le_pow_right₀ hx (by norm_num)
      have hcc : cWt ^ 4 ≤ cWt ^ 4 := le_rfl
      have hRR : R ^ 11 ≤ R ^ 20 := pow_le_pow_right₀ hR (by norm_num)
      have hsqle : (r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 4)) ^ 2 ≤ A ^ 2 := by
        calc (r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 4)) ^ 2
            = (r ^ 3) ^ 2 * (cWt ^ 4 * x ^ 64 * R ^ 8) := by ring
          _ ≤ R ^ 3 * (cWt ^ 4 * x ^ 64 * R ^ 8) := by gcongr
          _ = cWt ^ 4 * x ^ 64 * R ^ 11 := by ring
          _ ≤ cWt ^ 4 * x ^ 66 * R ^ 20 := by gcongr
          _ = (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := by ring
          _ ≤ A ^ 2 := hAsq
      nlinarith [hA0.le, hlhs0]
    have hsq : (β * (cWt * x ^ 16 * R ^ 2)) ^ 2 ≤ 1 := by
      have hrw : (β * (cWt * x ^ 16 * R ^ 2)) ^ 2
          = (r ^ 3 * A⁻¹) * (cWt ^ 2 * x ^ 32 * R ^ 4) := by
        rw [mul_pow, hβsq]; ring
      rw [hrw, mul_comm (r ^ 3) A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
      exact hkey
    nlinarith [mul_nonneg hβ0 (by positivity : (0:ℝ) ≤ cWt * x ^ 16 * R ^ 2)]
  · -- `γ = rA⁻¹`
    have hkey : r * (cWt * √cWt * x ^ 24 * R ^ 4) ≤ A := by
      have hlhs0 : (0 : ℝ) ≤ r * (cWt * √cWt * x ^ 24 * R ^ 4) := by positivity
      have hAsq : (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 ≤ A ^ 2 := by
        have h0 : (0 : ℝ) ≤ cWt ^ 2 * x ^ 33 * R ^ 10 := by positivity
        nlinarith
      have hxx : x ^ 48 ≤ x ^ 66 := pow_le_pow_right₀ hx (by norm_num)
      have hRR : R ^ 9 ≤ R ^ 20 := pow_le_pow_right₀ hR (by norm_num)
      have hcc : cWt ^ 3 ≤ cWt ^ 4 := pow_le_pow_right₀ hc1 (by norm_num)
      have hsqle : (r * (cWt * √cWt * x ^ 24 * R ^ 4)) ^ 2 ≤ A ^ 2 := by
        calc (r * (cWt * √cWt * x ^ 24 * R ^ 4)) ^ 2
            = r ^ 2 * (cWt ^ 2 * √cWt ^ 2 * x ^ 48 * R ^ 8) := by ring
          _ = r ^ 2 * (cWt ^ 3 * x ^ 48 * R ^ 8) := by rw [hscsq]; ring
          _ ≤ R * (cWt ^ 3 * x ^ 48 * R ^ 8) := by gcongr
          _ = cWt ^ 3 * x ^ 48 * R ^ 9 := by ring
          _ ≤ cWt ^ 4 * x ^ 66 * R ^ 20 := by gcongr
          _ = (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := by ring
          _ ≤ A ^ 2 := hAsq
      nlinarith [hA0.le, hlhs0]
    have hA0' : 0 < A := lt_of_lt_of_le (by positivity) hA
    rw [mul_comm r A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0']
    exact hkey

/-- **(2.72) with a gain discharges the rescaled far-field threshold.**  (2.72) is
`N^c·R^{30} ≤ A`; the rescaled threshold is `cWt²·x^{33}R^{10}` with `x = N^{δ/8}`, i.e.
`cWt²·N^{33δ/8}R^{10}`.  Since `R^{10} ≤ R^{30}` (twenty powers of `R` to spare) it suffices
that `cWt²·N^{33δ/8} ≤ N^c`, and `33δ/8 ≤ 5δ` for `δ ≥ 0`, so the single hypothesis
`cWt² ≤ N^{c-5δ}` is enough.

That hypothesis is a **largeness condition on `N`**, not a constraint on `δ` alone: see
`eventually_cWt_sq_le` for the fact that it holds for all large `N` as soon as `5δ < c`,
and `five_delta_lt` for the fact that it *forces* `5δ < c` (so it is not slipped in
vacuously). -/
theorem A_ge_of_reg {N c δ : ℝ} (hN : 1 ≤ N) (hR : 1 ≤ R) (hδ0 : 0 ≤ δ)
    (hcW : cWt ^ 2 ≤ N ^ (c - 5 * δ)) (hx : x = N ^ (δ / 8)) (hA : N ^ c * R ^ 30 ≤ A) :
    cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hx33 : x ^ 33 = N ^ (33 * δ / 8) := by
    rw [hx, ← Real.rpow_natCast (N ^ (δ / 8)) 33, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have h5 : N ^ (33 * δ / 8) ≤ N ^ (5 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hsum : N ^ (c - 5 * δ) * N ^ (5 * δ) = N ^ c := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hR1030 : R ^ 10 ≤ R ^ 30 := pow_le_pow_right₀ hR (by norm_num)
  have hstep : cWt ^ 2 * x ^ 33 ≤ N ^ c := by
    rw [hx33]
    calc cWt ^ 2 * N ^ (33 * δ / 8) ≤ N ^ (c - 5 * δ) * N ^ (5 * δ) := by gcongr
      _ = N ^ c := hsum
  calc cWt ^ 2 * x ^ 33 * R ^ 10 ≤ N ^ c * R ^ 30 := by gcongr
    _ ≤ A := hA

/-- The largeness condition of `A_ge_of_reg` holds for all large `N`, as soon as `5δ < c`.
(This is the `∀ᶠ N in atTop` shape the project's quantifier discipline asks for: the
constant `cWt` is absorbed by an arbitrarily small power of `N`, never by a constraint
on `δ` alone.) -/
theorem eventually_cWt_sq_le {c δ : ℝ} (h : 5 * δ < c) :
    ∀ᶠ N : ℝ in Filter.atTop, cWt ^ 2 ≤ N ^ (c - 5 * δ) := by
  have hpos : 0 < c - 5 * δ := by linarith
  exact (_root_.tendsto_rpow_atTop hpos).eventually_ge_atTop (cWt ^ 2)

/-- **The largeness condition is not vacuous, and it is not free either**: for `N > 1` it
already forces `5δ < c`, i.e. it *contains* the `δ`-budget of the rescaled arithmetic
(`phi_arith'`'s budget was `4δ ≤ 2c`).  This is why `A_ge_of_reg` needs no separate
hypothesis `5δ ≤ c`. -/
theorem five_delta_lt {N c δ : ℝ} (hN : 1 < N) (hcW : cWt ^ 2 ≤ N ^ (c - 5 * δ)) :
    5 * δ < c := by
  have hc1 : 1 < cWt ^ 2 := by
    have h1 : (1 : ℝ) < cWt := by
      have : (1 : ℝ) < exp 1 := by
        have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
        linarith
      unfold cWt; linarith
    nlinarith
  have hlt : (1 : ℝ) < N ^ (c - 5 * δ) := lt_of_lt_of_le hc1 hcW
  rcases (Real.one_lt_rpow_iff_of_pos (by linarith)).1 hlt with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · linarith

end Reg

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The whole rescaled side-condition bundle is satisfiable on the flow** — the analogue of
`RBM.Step2MomentStep.side_conditions_of_reg` for `phi_arith''`.  With `x = N^{δ/8}`,
`R = η_s/η_u`, `r = ℓ_u/ℓ_s`:

* `q = r³ ≤ R²` (`RBM.Step2MomentStep.hq_of_ratio`, unchanged — the near field carries no
  level);
* the rescaled far-field threshold `A ≥ cWt²x^{33}R^{10}` from (2.72) (`A_ge_of_reg`);
* `β = r^{3/2}A^{-1/2}` and `γ = rA⁻¹` from that threshold (`sideBundle''_of_A`).

(2.72)'s exponent `30` is **not** touched: the bottleneck moves from `β* = 5.5` to the
far-field threshold's `10`, still far below `30`.  What the rescaling does cost is the
`δ`-budget: `4δ ≤ 2c` becomes `5δ ≤ c`, plus the `N`-largeness `cWt² ≤ N^{c-5δ}`. -/
theorem side_conditions_of_reg'' (hE : |E| < 2) {N : ℕ} {u : ℝ} (_hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hN1 : 1 ≤ (N : ℝ))
    (hcW : cWt ^ 2 ≤ (N : ℝ) ^ (c - 5 * δ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u) :
    (B.ell N u / B.ell N (s N)) ^ 3 ≤ (etaT E (s N) / etaT E u) ^ 2 ∧
      cWt ^ 2 * ((N : ℝ) ^ (δ / 8)) ^ 33 * (etaT E (s N) / etaT E u) ^ 10 ≤ B.scale E N u ∧
      ((B.ell N u / B.ell N (s N)) * √(B.ell N u / B.ell N (s N)) *
          (√(B.scale E N u))⁻¹) *
          (cWt * ((N : ℝ) ^ (δ / 8)) ^ 16 * (etaT E (s N) / etaT E u) ^ 2) ≤ 1 ∧
      ((B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹) *
          (cWt * √cWt * ((N : ℝ) ^ (δ / 8)) ^ 24 * (etaT E (s N) / etaT E u) ^ 4) ≤ 1 := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL hu1
  have hr0 : (0 : ℝ) ≤ B.ell N u / B.ell N (s N) := by positivity
  have hr := Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hsu hu1
  have hηs : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hR1 : (1 : ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith), one_mul]; linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN1 (by linarith)
  have hAge := A_ge_of_reg (x := (N : ℝ) ^ (δ / 8)) (R := etaT E (s N) / etaT E u)
    (A := B.scale E N u) hN1 hR1 hδ0 hcW rfl hA
  obtain ⟨hβ, hγ⟩ := sideBundle''_of_A (x := (N : ℝ) ^ (δ / 8))
    (R := etaT E (s N) / etaT E u) (r := B.ell N u / B.ell N (s N)) hx1 hR1 hr0 hr hAge
  exact ⟨Step2MomentStep.hq_of_ratio hR1 hr0 hr, hAge, hβ, hγ⟩

end Flow

/-! ### 5. Satisfiability **with margin** -/

section Sat

/-- **⭐ The rescaled bundle is jointly satisfiable at every `R ≥ 1` with a factor `2` of
slack in every constraint that has a direction.**

Contrast `RBM.Step2Bootstrap.sat_StepSide_gt_one`, which meets all eight constraints of
`StepSide` **at equality**: that is exactly the zero margin this rescaling was introduced to
remove.  Here `Ξ = x/2`, `A = 2cWt²x^{33}R^{10}`, `ε = (2cWt²x^{33}R^{10})⁻¹`, `q = R²/2`,
`β = (2cWt x^{16}R²)⁻¹`, `γ = (2cWt^{3/2}x^{24}R⁴)⁻¹`, `κ = x/2`,
`Jv = cWt x^{16}R⁴/2` — every one of them strictly inside its constraint
(`sat_StepSide''_half_strict`). -/
theorem sat_StepSide''_half {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    StepSide'' x R (x / 2) (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))
      (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ (R ^ 2 / 2)
      (2 * (cWt * x ^ 16 * R ^ 2))⁻¹ (2 * (cWt * √cWt * x ^ 24 * R ^ 4))⁻¹ (x / 2)
      (cWt * x ^ 16 * R ^ 4 / 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  have hAv : (0 : ℝ) < 2 * (cWt ^ 2 * x ^ 33 * R ^ 10) := by positivity
  have hβv : (0 : ℝ) < 2 * (cWt * x ^ 16 * R ^ 2) := by positivity
  have hγv : (0 : ℝ) < 2 * (cWt * √cWt * x ^ 24 * R ^ 4) := by positivity
  refine
    { R_ge := hR
      Ξ_nonneg := by positivity
      Ξ_le := by linarith
      A_ge := by nlinarith [(by positivity : (0:ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10)]
      ε_nonneg := by positivity
      ε_le := ?_
      q_nonneg := by positivity
      q_le := by nlinarith [(by positivity : (0:ℝ) < R ^ 2)]
      β_nonneg := by positivity
      β_le := ?_
      γ_nonneg := by positivity
      γ_le := ?_
      κ_nonneg := by positivity
      κ_le := by linarith
      Jv_nonneg := by positivity
      Jv_le := by nlinarith [(by positivity : (0:ℝ) < cWt * x ^ 16 * R ^ 4)] }
  · rw [inv_mul_eq_div, div_le_one hAv]; linarith [(by positivity :
      (0:ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10)]
  · rw [inv_mul_eq_div, div_le_one hβv]; linarith [(by positivity :
      (0:ℝ) < cWt * x ^ 16 * R ^ 2)]
  · rw [inv_mul_eq_div, div_le_one hγv]; linarith [(by positivity :
      (0:ℝ) < cWt * √cWt * x ^ 24 * R ^ 4)]

/-- **The margin is real**: at the witness of `sat_StepSide''_half` all eight constraints that
have a direction (`Ξ_le`, `A_ge`, `ε_le`, `q_le`, `β_le`, `γ_le`, `κ_le`, `Jv_le`) are
**strict**, with a factor `2` to spare; the seven inequalities below cover them, the first one
serving both `Ξ_le` and `κ_le` (the two slots carry the same value `x/2`).  The seven
nonnegativity slots are strict too — every witness value is positive — so at `R > 1`
(`sat_StepSide''_two` takes `R = 2`; `RBM.Step2Bootstrap.one_lt_ratR` says `R > 1` is the
generic case strictly inside the window) **no** constraint of `StepSide''` is met at
equality. -/
theorem sat_StepSide''_half_strict {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    x / 2 < x ∧
      cWt ^ 2 * x ^ 33 * R ^ 10 < 2 * (cWt ^ 2 * x ^ 33 * R ^ 10) ∧
      (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ * (cWt ^ 2 * x ^ 33 * R ^ 10) < 1 ∧
      R ^ 2 / 2 < R ^ 2 ∧
      (2 * (cWt * x ^ 16 * R ^ 2))⁻¹ * (cWt * x ^ 16 * R ^ 2) < 1 ∧
      (2 * (cWt * √cWt * x ^ 24 * R ^ 4))⁻¹ * (cWt * √cWt * x ^ 24 * R ^ 4) < 1 ∧
      cWt * x ^ 16 * R ^ 4 / 2 < cWt * x ^ 16 * R ^ 4 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  have hA : (0 : ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10 := by positivity
  have hβ : (0 : ℝ) < cWt * x ^ 16 * R ^ 2 := by positivity
  have hγ : (0 : ℝ) < cWt * √cWt * x ^ 24 * R ^ 4 := by positivity
  have hJ : (0 : ℝ) < cWt * x ^ 16 * R ^ 4 := by positivity
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_, ?_, by linarith⟩
  · rw [inv_mul_eq_div, div_lt_one (by linarith)]; linarith
  · rw [inv_mul_eq_div, div_lt_one (by linarith)]; linarith
  · rw [inv_mul_eq_div, div_lt_one (by linarith)]; linarith

/-- The seven nonnegativity slots are strict at the witness as well: every witness value is
**positive**, so the bundle is not met by collapsing a slot to `0`. -/
theorem sat_StepSide''_half_pos {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    0 < x / 2 ∧ 0 < (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ ∧ 0 < R ^ 2 / 2 ∧
      0 < (2 * (cWt * x ^ 16 * R ^ 2))⁻¹ ∧
      0 < (2 * (cWt * √cWt * x ^ 24 * R ^ 4))⁻¹ ∧
      0 < cWt * x ^ 16 * R ^ 4 / 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
    by positivity⟩

/-- A concrete non-degenerate instance: `x = 1`, `R = 2` (so the window is genuinely
non-collapsed, `R > 1`), with the factor-`2` margin of `sat_StepSide''_half`. -/
theorem sat_StepSide''_two :
    StepSide'' 1 2 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 2 ^ 10))
      (2 * (cWt ^ 2 * (1 : ℝ) ^ 33 * 2 ^ 10))⁻¹ ((2 : ℝ) ^ 2 / 2)
      (2 * (cWt * (1 : ℝ) ^ 16 * 2 ^ 2))⁻¹ (2 * (cWt * √cWt * (1 : ℝ) ^ 24 * 2 ^ 4))⁻¹
      ((1 : ℝ) / 2) (cWt * (1 : ℝ) ^ 16 * 2 ^ 4 / 2) :=
  sat_StepSide''_half le_rfl one_le_two

/-- The one-step output at the margin witness, in the blunt normalization:
`≤ (cStep' m + 1)·x²`. -/
theorem sat_stepRhs''_div_half {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    stepRhs'' m x R (x / 2) (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))
        (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ (R ^ 2 / 2)
        (2 * (cWt * x ^ 16 * R ^ 2))⁻¹ (2 * (cWt * √cWt * x ^ 24 * R ^ 4))⁻¹ (x / 2)
        (cWt * x ^ 16 * R ^ 4 / 2) / R ^ 4
      ≤ (Step2MomentStep.cStep' m + 1) * x ^ 2 :=
  stepRhs''_div_le hx hm (sat_StepSide''_half hx hR)

end Sat

end StepSideAPrime

end RBM

/-!
## Deviations from the paper

**T263a.**  §5.3, the one-step arithmetic between (5.39) and (5.47).

① *Paper location.*  (5.43) fixes the a priori level of the bootstrap as
`J*_{u,D} ≤ (η_s/η_t)⁴` after the `N^δ` loss of `≺`, i.e. `Λ = N^δ R⁴` in the notation of
this file (`x⁸R⁴`, `x = N^{δ/8}`); (5.40)–(5.42) are then run at that level.

② *Is the paper changed?*  **No.**  The paper's stopping time (5.43) is replaced, in the
`(A′)` route, by the soft-max cutoff weight, whose support carries the level
`4e·N^{2δ}R⁴` rather than `N^δR⁴`: one factor `N^δ` because the cutoff level `prefNet` is
`N^{2δ}`, one factor `e` from the soft maximum, one factor `2` from the widened weight
`χ(·/(2Θ′))^{2p}`.  That is a property of the *substitute* for (5.43), not of the paper's
argument; the paper's estimates (5.40)–(5.42) are used verbatim, only at the larger level.
The rescaled side conditions are strictly stronger than the paper's — they ask for more room
in `A_u`, `ε`, `β`, `γ` — and §4 above shows (2.72) still discharges them, with (2.72)'s
exponent `30` untouched.

③ *Lines.*  This file only; nothing in `RBM.Step2MomentStep` or `RBM.CutHypTheta` is edited.

④ *Renumbering?*  **No.**  No paper equation is renumbered.

⑤ *The one new slot.*  `κ` has no counterpart in the paper at all: it is the cross term
`(2√u)⁻¹Σ_q gvar q·(∂_q W)·coordD1(|Ψ|^{2p})` of the fixed-`ω` generator identity
(referee (S1)/(S5)), which exists only because the stopping time was replaced by a weight.
Its budget `κ ≤ x` is the same single `≺`-power as `Ξ`, and it costs exactly one more
`x²R⁴` in the output, whence `cStep' m + 1`.
-/
