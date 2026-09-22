/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeOneStep

/-!
# The **second pass** of route (A′): sharp arithmetic and assembly skeleton (T272)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48), **second pass**, assembled along the repaired route (A′) of
the V548 referee report, §5, step 6.

## What is different from the first pass

`RBM1D/Gauss/APrimeOneStep.lean` (T270) builds the first pass: the functional is normalized
by `T·R⁴` (`RBM.Step2Moment.jSnorm`), the one-step output is `(cStep' m + 1)·x²R⁴`, and the a
priori level fed to the arithmetic is the *blunt* one.  This file builds the second pass, i.e.
the statement `RBM.Step2Bootstrap.weightedMoment_of_stepBoundSharp` consumes.  Three things
move, and only three:

1. **The normalization is `T·R²`** (`RBM.Step2Near47.jSnorm2`), so the one-step right-hand
   side is divided by `R²` and not by `R⁴`.  Every slot therefore has to be paid against
   `x²R²`, which is `R²` *less* room than the first pass had.
2. **The a priori level is the first pass's conclusion**, `N^{2δ}R⁴` on the support of the
   soft-max cutoff weight, i.e. `Jv ≤ cWt·x^{16}R⁴` with `cWt = RBM.StepSideAPrime.cWt`
   — the same level `RBM.StepSideAPrime.StepSide''` carries.  (This is the analogue of
   `RBM.Step2Near47.phi_arith_second_pass` keeping the blunt level `x⁸R⁴` while outputting
   `cSharp m·x²R²`.)
3. **The near field enters integrated**, as `qI` with the budget `2m⁻¹R²`, exactly as in
   `RBM.CutHypTheta.StepSideSharp`; referee §5 step 6 is the statement that in `T·R²` units
   the near-field integral `∫Q̂` is `O(1)`, which is what that budget records.  The cross term
   near×near is the slot `κ ≤ x`, the same slot `RBM.StepSideAPrime.StepSide''` opened.

## ⭐ Where the rescaling bites: the binding condition

T263 found that after rescaling to the weight-support level the bottleneck of the *first*
pass moved from `β* = 5.5` to the far-field threshold `A ≥ cWt²x^{33}R^{10}`, which implied
both far-field conditions with `R^{4.5}` resp. `R^{5.5}` to spare.

Here the two far-field conditions each cost one more power of `R²` (because `J*` is allowed
to be `R²` larger relative to the output, exactly as in `phi_arith_second_pass`):

* `β·(cWt·x^{16}·R⁴) ≤ 1` — `β = r^{3/2}A^{-1/2}` needs `cWt²x^{32}R^{9.5} ≤ A`;
* `γ·(cWt·√cWt·x^{24}·R⁶) ≤ 1` — `γ = rA⁻¹` needs `cWt^{3/2}x^{24}R^{6.5} ≤ A`.

So the threshold `A ≥ cWt²x^{33}R^{10}` is **still** the single binding condition
(`sideBundleSharp''_of_A`), but it is now **nearly saturated by the `β` branch**: half a
power of `R` and one power of `x` of slack, against T263's `R^{4.5}`.  The `γ` branch keeps
`R^{3.5}`.  Nothing else changes: `A_ge_of_reg` (T263) discharges the threshold from (2.72)
verbatim — (2.72)'s exponent `30` is untouched — and the `δ`-budget is the same `5δ < c`.

## The input table

Slot of `stepRhsSharp''` → hypothesis here → supplier:

* `x·R²·Ξ` → `hinit` of `momNormW_le_stepRhsSharp''_div` → **hypothesis**: (5.39) read in
  `T·R²` units, i.e. the first pass's conclusion at the left endpoint of the cell.
  *Supplier*: T271 (`RBM1D/Gauss/APrimeModel.lean`) composed with T269's envelope
  (`RBM1D/Gauss/APrimePrior.lean`).
* drift + QV → `hdrift` → **hypothesis**: (5.40)–(5.42).  *Suppliers*: T269 for the `Q^{bd}`
  envelope, T265 (`RBM1D/Gauss/APrimeDuhamel.lean`) and T267
  (`RBM1D/Gauss/EarlyQVRateEv.lean`) for the cross term, T268
  (`RBM1D/Gauss/APrimeTimeInt.lean`) for the (S6) time integrals.  It is resolved into those
  by `RBM.APrimeOneStep.drift_bound_of_envelopes`, reused verbatim.
* `x·R²·κ` and `x(R²+1)+1` → `hqv` → **hypothesis**: the near×near cross term of referee
  §5 step 6, which in `T·R²` units is `N^{−2δ}(log N)^{1/2}` and so fits in `κ ≤ x`
  (`κ_le_of_crossTerm`).  *Suppliers*: T265 + T267; the bad event is paid for by
  `RBM.APrimeOneStep.integral_le_good_add_bad`, reused verbatim.
* the (G) regularity block → forwarded verbatim → **theorem**, T264
  (`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le`).
* the arithmetic → `stepRhsSharp''_div_le` → **theorem**, this file.
* `p = 0` → discharged internally → **theorem**, T260
  (`RBM.Gauss.integral_weight_pow_zero_le`).

## Contents

* §1 `phi_arith_sharp''` — the sharp arithmetic at the weight-support level, with the slot
  `κ`; `stepRhsSharp''`/`StepSideSharp''` packaging it, `stepRhsSharp''_div_le` (division by
  `R²`), `one_le_stepRhsSharp''`.
* §2 `sideBundleSharp''_of_A`, `side_conditions_sharp''_of_reg` — the threshold is the single
  binding condition and (2.72) discharges it; `beta_margin_sharp`/`gamma_margin_sharp` record
  how much room each branch has left.
* §3 satisfiability **with margin**: `sat_StepSideSharp''_half` and its `_strict`/`_pos`
  companions, plus the concrete `sat_StepSideSharp''_two` at `R = 2 > 1`.
* §4 the skeleton: `driftTermSharp`, `stepRhsSharp''_eq_split`,
  `stepRhsSharp''_div_of_slots`, `momNormW_le_stepRhsSharp''_div`.
* §5 `oneStepSharp_integral_le`, `oneStepSharp_integral_le_sq`.
* §6 `weightedMoment_bound_of_oneStepSharp''`, `weightedMoment_of_stepBoundSharp''`.
* §7 ⚠ the `p = 0` branch, `oneStepSharp_pzero` and
  `weightedMoment_of_stepBoundSharpPos''`.
* §8 the satisfiability witness for the whole skeleton.

Nothing outside this file is edited; `RBM.StepSideAPrime.phi_arith''`,
`RBM.StepSideAPrime.StepSide''`, `RBM.StepSideAPrime.stepRhs''` and everything in
`RBM.APrimeOneStep` are used, not changed.
-/

namespace RBM

namespace APrimeOneStepSharp

open MeasureTheory Filter Set Real
open MomentDuhamel MomentDuhamelCut CutHypTheta StepSideAPrime APrimeOneStep

/-! ### 1. The sharp arithmetic at the weight-support level -/

section Arith

/-- **The second-pass arithmetic of (5.47) at the weight-support level.**

This is `RBM.Step2Near47.phi_arith_second_pass` with the level `x⁸R⁴` of (5.43) replaced by
`cWt·x^{16}R⁴` everywhere it occurs — in the hypothesis on `Jv` and in the square of the
level multiplying the `A⁻¹` and `ε` terms of (5.40) — the far-field side conditions rescaled
accordingly, and one new slot `κ ≤ x` for the near×near cross term of the fixed-`ω` generator
identity (referee (S5), §5 step 6).

Equivalently it is `RBM.StepSideAPrime.phi_arith''` read in the **sharp** normalization: the
output is `(cSharp m + 1)·x²R²` rather than `(cStep' m + 1)·x²R⁴`, the near field enters
integrated as `qI ≤ 2m⁻¹R²` rather than through the coefficient `q ≤ R²`, and the two
far-field conditions each carry one more power of `R²`.

The output is `(cSharp m + 1)·x²R²`: the seven old terms still cost `cSharp m · x²R²` — each
pays exactly what it paid in `phi_arith_second_pass`, because every rescaled side condition
carries the matching power of `cWt` — and the new slot costs one more `x²R²`. -/
theorem phi_arith_sharp'' {x R Ξ m A ε qI β γ κ Jv : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R)
    (_hΞ0 : 0 ≤ Ξ) (hΞ : Ξ ≤ x) (hm0 : 0 < m)
    (hA : cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε * (cWt ^ 2 * x ^ 33 * R ^ 10) ≤ 1)
    (hqI0 : 0 ≤ qI) (hqI : qI ≤ 2 * m⁻¹ * R ^ 2)
    (hβ0 : 0 ≤ β) (hβ : β * (cWt * x ^ 16 * R ^ 4) ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ : γ * (cWt * √cWt * x ^ 24 * R ^ 6) ≤ 1)
    (_hκ0 : 0 ≤ κ) (hκ : κ ≤ x)
    (hJ0 : 0 ≤ Jv) (hJΛ : Jv ≤ cWt * x ^ 16 * R ^ 4) :
    x * R ^ 2 * Ξ + x * R ^ 2 * κ
      + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1
      ≤ (Step2Near47.cSharp m + 1) * x ^ 2 * R ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hc0 : 0 < cWt := cWt_pos
  have hc1 : 1 ≤ cWt := one_le_cWt
  have hsc1 : 1 ≤ √cWt := one_le_sqrt_cWt
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
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
  -- the eight terms, each paid against `x²R²`
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 2 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
  -- the new slot: the near×near cross term of the fixed-`ω` generator identity
  have tκ : x * R ^ 2 * κ ≤ x ^ 2 * R ^ 2 := by
    calc x * R ^ 2 * κ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
  have t2 : Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
      ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        = 36 * exp 1 * m⁻¹ * (Ξ * (cWt ^ 2 * x ^ 32 * R ^ 10) * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * (cWt ^ 2 * x ^ 32 * R ^ 10) * A⁻¹) := by gcongr
      _ = 36 * exp 1 * m⁻¹ * (cWt ^ 2 * x ^ 33 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 2) := by gcongr
  have t3 : Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
      ≤ exp 1 * (x ^ 2 * R ^ 2) := by
    calc Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        = exp 1 * (Ξ * (cWt ^ 2 * x ^ 32 * R ^ 10) * ε) := by ring
      _ ≤ exp 1 * (x * (cWt ^ 2 * x ^ 32 * R ^ 10) * ε) := by gcongr
      _ = exp 1 * (ε * (cWt ^ 2 * x ^ 33 * R ^ 10)) := by ring
      _ ≤ exp 1 * 1 := by gcongr
      _ ≤ exp 1 * (x ^ 2 * R ^ 2) := by gcongr
  have t4 : Ξ * (x * qI) ≤ 2 * m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * qI) ≤ x * (x * (2 * m⁻¹ * R ^ 2)) := by gcongr
      _ = 2 * m⁻¹ * (x ^ 2 * R ^ 2) := by ring
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv)) ≤ m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv))
        ≤ x * (x * m⁻¹ * R ^ 2 * (β * (cWt * x ^ 16 * R ^ 4))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) * (β * (cWt * x ^ 16 * R ^ 4)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 2) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) := mul_one _
  have t6 : Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv))) ≤ m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv)))
        ≤ x * (x * m⁻¹ * R ^ 2 * (γ * (cWt * √cWt * x ^ 24 * R ^ 6))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) * (γ * (cWt * √cWt * x ^ 24 * R ^ 6)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 2) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) := mul_one _
  have t7 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 2) := by nlinarith
  have hsplit : x * R ^ 2 * Ξ + x * R ^ 2 * κ
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
          + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1
      = x * R ^ 2 * Ξ + x * R ^ 2 * κ
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        + Ξ * (x * qI)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv)) + Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv)))
        + x * (R ^ 2 + 1) + 1 := by ring
  rw [hsplit, Step2Near47.cSharp]
  nlinarith

end Arith

/-! ### 1′. The packaged form -/

section Packaged

/-- The left-hand side of `phi_arith_sharp''`, verbatim: the seven terms of (5.39)–(5.44) at
the weight-support level with the near field **integrated**, plus the cross-term slot `κ`.

Compare `RBM.CutHypTheta.stepRhsSharp` (same shape, level `x⁸R⁴`, no `κ`) and
`RBM.StepSideAPrime.stepRhs''` (same level, near field through the coefficient `q`). -/
noncomputable def stepRhsSharp'' (m x R Ξ A ε qI β γ κ Jv : ℝ) : ℝ :=
  x * R ^ 2 * Ξ + x * R ^ 2 * κ
    + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1

/-- The side conditions of `phi_arith_sharp''`, verbatim.

Compared with `RBM.StepSideAPrime.StepSide''` (the first pass at the same level): the near
field is the integrated `qI ≤ 2m⁻¹R²` instead of `q ≤ R²`, and the two far-field conditions
each carry one more power of `R²`.  Compared with `RBM.CutHypTheta.StepSideSharp` (the second
pass at the blunt level): the level is `cWt·x^{16}R⁴` instead of `x⁸R⁴`, the far-field
conditions carry the matching powers of `cWt`, and the slot `κ` is new. -/
structure StepSideSharp'' (m x R Ξ A ε qI β γ κ Jv : ℝ) : Prop where
  /-- `R = η_s/η_v ≥ 1` on the window. -/
  R_ge : 1 ≤ R
  /-- (5.35)'s loss is a single `≺`-power. -/
  Ξ_nonneg : 0 ≤ Ξ
  /-- ditto. -/
  Ξ_le : Ξ ≤ x
  /-- the threshold `A_u` of (5.42), rescaled: `cWt²x^{33}R^{10}`.  **This is the binding
  condition of the sharp pass**: `sideBundleSharp''_of_A` derives both far-field conditions
  from it, and the `β` branch nearly saturates it (`R^{9.5}` against `R^{10}`). -/
  A_ge : cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A
  /-- the far-field remainder of (5.40). -/
  ε_nonneg : 0 ≤ ε
  /-- ditto, rescaled. -/
  ε_le : ε * (cWt ^ 2 * x ^ 33 * R ^ 10) ≤ 1
  /-- the **integrated** near field of (5.44); referee §5 step 6 is the statement that in
  `T·R²` units this integral is `O(1)`, i.e. that this budget is the right one. -/
  qI_nonneg : 0 ≤ qI
  /-- its budget `2m⁻¹R²`, unchanged from `RBM.CutHypTheta.StepSideSharp` — the near field
  carries no level, so the rescaling does not touch it. -/
  qI_le : qI ≤ 2 * m⁻¹ * R ^ 2
  /-- the linear far-field coefficient `r^{3/2}A^{-1/2}`. -/
  β_nonneg : 0 ≤ β
  /-- ditto, rescaled **and** one power of `R²` weaker than the first pass's
  `β·(cWt x^{16}R²) ≤ 1`: `β·(cWt·x^{16}·R⁴) ≤ 1` (`β* = 9.5`). -/
  β_le : β * (cWt * x ^ 16 * R ^ 4) ≤ 1
  /-- the `3/2`-power far-field coefficient `rA⁻¹`. -/
  γ_nonneg : 0 ≤ γ
  /-- ditto, rescaled and one power of `R²` weaker:
  `γ·(cWt^{3/2}·x^{24}·R⁶) ≤ 1` (`β* = 6.5`). -/
  γ_le : γ * (cWt * √cWt * x ^ 24 * R ^ 6) ≤ 1
  /-- **new slot**: the near×near cross term of the fixed-`ω` generator identity (referee
  (S5), §5 step 6), with the same budget as the `≺`-loss. -/
  κ_nonneg : 0 ≤ κ
  /-- ditto. -/
  κ_le : κ ≤ x
  /-- the a priori level on the support of the weight — **the first pass's conclusion**. -/
  Jv_nonneg : 0 ≤ Jv
  /-- ditto: `cWt·x^{16}R⁴`, which by `RBM.StepSideAPrime.prior_lt_level` strictly contains
  `4e·N^{2δ}R⁴`. -/
  Jv_le : Jv ≤ cWt * x ^ 16 * R ^ 4

/-- **`phi_arith_sharp''`, packaged.** -/
theorem stepRhsSharp''_le {m x R Ξ A ε qI β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSideSharp'' m x R Ξ A ε qI β γ κ Jv) :
    stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv ≤ (Step2Near47.cSharp m + 1) * x ^ 2 * R ^ 2 :=
  phi_arith_sharp'' hx H.R_ge H.Ξ_nonneg H.Ξ_le hm H.A_ge H.ε_nonneg H.ε_le H.qI_nonneg
    H.qI_le H.β_nonneg H.β_le H.γ_nonneg H.γ_le H.κ_nonneg H.κ_le H.Jv_nonneg H.Jv_le

/-- **In the sharp normalization `J*/R²`** (`RBM.Step2Near47.jSnorm2`) the second-pass output
is `(cSharp m + 1)·x²` — the same exponent as the first pass, a larger constant, and **no `R`
left**, which is why the interface's control is the constant `Θ ≡ 1`. -/
theorem stepRhsSharp''_div_le {m x R Ξ A ε qI β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSideSharp'' m x R Ξ A ε qI β γ κ Jv) :
    stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2 ≤ (Step2Near47.cSharp m + 1) * x ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith [H.R_ge]
  have hR0 : (0 : ℝ) < R ^ 2 := by positivity
  rw [div_le_iff₀ hR0]
  exact stepRhsSharp''_le hx hm H

/-- The one-step right-hand side is at least its own constant term `1`; in particular it is
nonnegative, so it can be raised to the `2p`-th power monotonically. -/
theorem one_le_stepRhsSharp'' {m x R Ξ A ε qI β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSideSharp'' m x R Ξ A ε qI β γ κ Jv) :
    1 ≤ stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv := by
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
      + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) := by
    have hi : (0 : ℝ) ≤ A⁻¹ := (inv_pos.2 hA0).le
    have hbJ : (0 : ℝ) ≤ β * Jv := mul_nonneg H.β_nonneg hJ0
    have hgJ : (0 : ℝ) ≤ γ * (Jv * √Jv) := mul_nonneg H.γ_nonneg (mul_nonneg hJ0 hsJ)
    have hbr1 : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε :=
      add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hi)
        (mul_nonneg (by positivity) H.ε_nonneg)
    have hc : (0 : ℝ) ≤ exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2
        * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) :=
      mul_nonneg (mul_nonneg (exp_pos 1).le (sq_nonneg _)) hbr1
    have hq : (0 : ℝ) ≤ x * qI := mul_nonneg hx0.le H.qI_nonneg
    have hd : (0 : ℝ) ≤ x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hx0.le hmi.le) (by positivity)) (by linarith)
    exact mul_nonneg H.Ξ_nonneg (by linarith)
  have h4 : (0 : ℝ) ≤ x * (R ^ 2 + 1) := mul_nonneg hx0.le (by positivity)
  unfold stepRhsSharp''
  linarith

/-- **The sharp output is below the level the first pass established.**  The second pass
outputs `(cSharp m + 1)x²R²` while the a priori level it *consumes* is `cWt·x^{16}R⁴`, so no
second bootstrap is needed: the margin `cSharp m + 1 ≤ cWt·x^{14}` is the same one
`RBM.StepSideAPrime.phi_lt_threshold''` asks for, with `R²` to spare on top. -/
theorem phi_lt_threshold_sharp'' {x R m : ℝ} (hR : 1 ≤ R)
    (hxc : Step2Near47.cSharp m + 1 ≤ cWt * x ^ 14) :
    (Step2Near47.cSharp m + 1) * x ^ 2 * R ^ 2 ≤ cWt * x ^ 16 * R ^ 4 := by
  have hc0 : (0 : ℝ) < cWt := cWt_pos
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hcw : (0 : ℝ) ≤ cWt * x ^ 16 := by positivity
  calc (Step2Near47.cSharp m + 1) * x ^ 2 * R ^ 2
      ≤ cWt * x ^ 14 * x ^ 2 * R ^ 2 := by gcongr
    _ = cWt * x ^ 16 * R ^ 2 := by ring
    _ ≤ cWt * x ^ 16 * R ^ 4 := by gcongr

end Packaged

/-! ### 2. The binding condition after the sharp rescaling

T263's `RBM.StepSideAPrime.sideBundle''_of_A` shows that for the **first** pass the far-field
threshold `A ≥ cWt²x^{33}R^{10}` implies both far-field conditions, with `R^{4.5}` resp.
`R^{5.5}` of slack.  The sharp pass costs one more power of `R²` on each, so the slacks drop
to `R^{0.5}` and `R^{3.5}`: the threshold is **still** the single binding condition, but the
`β` branch now nearly saturates it.  `beta_margin_sharp` and `gamma_margin_sharp` record
exactly what each branch needs, so that a future sharpening knows which one to attack. -/

section Reg

variable {x R r A : ℝ}

/-- What the `β` branch of the sharp pass actually needs: `cWt²x^{32}R^{9.5} ≤ A`, in the
squared form `(cWt²x^{32}R^{9})² · R ≤ A²` that avoids half-integer powers.  Against the
threshold `A ≥ cWt²x^{33}R^{10}` that is **half a power of `R` and one power of `x`** of
slack — this is the binding branch. -/
theorem beta_margin_sharp (hx : 1 ≤ x) (hR : 1 ≤ R) :
    (cWt ^ 2 * x ^ 32 * R ^ 9) ^ 2 * R ≤ (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := by
  have hc0 : (0 : ℝ) < cWt := cWt_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hxx : x ^ 64 ≤ x ^ 66 := pow_le_pow_right₀ hx (by norm_num)
  have hRR : R ^ 19 ≤ R ^ 20 := pow_le_pow_right₀ hR (by norm_num)
  calc (cWt ^ 2 * x ^ 32 * R ^ 9) ^ 2 * R = cWt ^ 4 * x ^ 64 * R ^ 19 := by ring
    _ ≤ cWt ^ 4 * x ^ 66 * R ^ 20 := by gcongr
    _ = (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := by ring

/-- What the `γ` branch of the sharp pass needs: `cWt^{3/2}x^{24}R^{6.5} ≤ A`, squared.
Against the threshold that is `R^{3.5}` of slack — comfortably not the bottleneck. -/
theorem gamma_margin_sharp (hx : 1 ≤ x) (hR : 1 ≤ R) :
    (cWt * √cWt * x ^ 24 * R ^ 6) ^ 2 * R ≤ (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := by
  have hc0 : (0 : ℝ) < cWt := cWt_pos
  have hc1 : (1 : ℝ) ≤ cWt := one_le_cWt
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hscsq : √cWt ^ 2 = cWt := Real.sq_sqrt hc0.le
  have hxx : x ^ 48 ≤ x ^ 66 := pow_le_pow_right₀ hx (by norm_num)
  have hRR : R ^ 13 ≤ R ^ 20 := pow_le_pow_right₀ hR (by norm_num)
  have hcc : cWt ^ 3 ≤ cWt ^ 4 := pow_le_pow_right₀ hc1 (by norm_num)
  calc (cWt * √cWt * x ^ 24 * R ^ 6) ^ 2 * R
      = cWt ^ 2 * √cWt ^ 2 * x ^ 48 * R ^ 13 := by ring
    _ = cWt ^ 3 * x ^ 48 * R ^ 13 := by rw [hscsq]; ring
    _ ≤ cWt ^ 4 * x ^ 66 * R ^ 20 := by gcongr
    _ = (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := by ring

/-- **⭐ The rescaled far-field threshold is still the single binding condition.**  From
`A ≥ cWt²x^{33}R^{10}` alone — together with `r² ≤ R` (`RBM.Step2MomentStep.ratio_sq_le`) —
both **sharp** far-field side conditions follow:

* `β = r^{3/2}A^{-1/2}` needs `r³·cWt²x^{32}R⁸ ≤ A`, and `r³ ≤ R^{3/2}`, so
  `cWt²x^{32}R^{9.5} ≤ A` suffices (`beta_margin_sharp`: `R^{0.5}` to spare);
* `γ = rA⁻¹` needs `r·cWt^{3/2}x^{24}R⁶ ≤ A`, and `r ≤ R^{1/2}`, so
  `cWt^{3/2}x^{24}R^{6.5} ≤ A` suffices (`gamma_margin_sharp`: `R^{3.5}` to spare).

The threshold itself is **unchanged** from the first pass (T263), so
`RBM.StepSideAPrime.A_ge_of_reg` discharges it from (2.72) verbatim and (2.72)'s exponent
`30` is untouched. -/
theorem sideBundleSharp''_of_A (hx : 1 ≤ x) (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R)
    (hA : cWt ^ 2 * x ^ 33 * R ^ 10 ≤ A) :
    (r * √r * (√A)⁻¹) * (cWt * x ^ 16 * R ^ 4) ≤ 1 ∧
      (r * A⁻¹) * (cWt * √cWt * x ^ 24 * R ^ 6) ≤ 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : 0 < cWt := cWt_pos
  have hc1 : 1 ≤ cWt := one_le_cWt
  have hscsq : √cWt ^ 2 = cWt := Real.sq_sqrt hc0.le
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  have hsr : (0 : ℝ) ≤ √r := Real.sqrt_nonneg _
  have hAsq : (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 ≤ A ^ 2 := by
    have h0 : (0 : ℝ) ≤ cWt ^ 2 * x ^ 33 * R ^ 10 := by positivity
    nlinarith
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
    -- squared target: `r³·cWt²x^{32}R⁸ ≤ A`
    have hkey : r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 8) ≤ A := by
      have hlhs0 : (0 : ℝ) ≤ r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 8) := by positivity
      have hsqle : (r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 8)) ^ 2 ≤ A ^ 2 := by
        calc (r ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 8)) ^ 2
            = (r ^ 3) ^ 2 * (cWt ^ 2 * x ^ 32 * R ^ 8) ^ 2 := by ring
          _ ≤ R ^ 3 * (cWt ^ 2 * x ^ 32 * R ^ 8) ^ 2 := by gcongr
          _ = (cWt ^ 2 * x ^ 32 * R ^ 9) ^ 2 * R := by ring
          _ ≤ (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := beta_margin_sharp hx hR
          _ ≤ A ^ 2 := hAsq
      nlinarith [hA0.le, hlhs0]
    have hsq : (β * (cWt * x ^ 16 * R ^ 4)) ^ 2 ≤ 1 := by
      have hrw : (β * (cWt * x ^ 16 * R ^ 4)) ^ 2
          = (r ^ 3 * A⁻¹) * (cWt ^ 2 * x ^ 32 * R ^ 8) := by
        rw [mul_pow, hβsq]; ring
      rw [hrw, mul_comm (r ^ 3) A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
      exact hkey
    nlinarith [mul_nonneg hβ0 (by positivity : (0:ℝ) ≤ cWt * x ^ 16 * R ^ 4)]
  · -- `γ = rA⁻¹`
    have hkey : r * (cWt * √cWt * x ^ 24 * R ^ 6) ≤ A := by
      have hlhs0 : (0 : ℝ) ≤ r * (cWt * √cWt * x ^ 24 * R ^ 6) := by positivity
      have hsqle : (r * (cWt * √cWt * x ^ 24 * R ^ 6)) ^ 2 ≤ A ^ 2 := by
        calc (r * (cWt * √cWt * x ^ 24 * R ^ 6)) ^ 2
            = r ^ 2 * (cWt * √cWt * x ^ 24 * R ^ 6) ^ 2 := by ring
          _ ≤ R * (cWt * √cWt * x ^ 24 * R ^ 6) ^ 2 := by gcongr
          _ = (cWt * √cWt * x ^ 24 * R ^ 6) ^ 2 * R := by ring
          _ ≤ (cWt ^ 2 * x ^ 33 * R ^ 10) ^ 2 := gamma_margin_sharp hx hR
          _ ≤ A ^ 2 := hAsq
      nlinarith [hA0.le, hlhs0]
    rw [mul_comm r A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
    exact hkey

end Reg

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The sharp side-condition bundle is satisfiable on the flow** — the analogue of
`RBM.StepSideAPrime.side_conditions_of_reg''` for `phi_arith_sharp''`.  With `x = N^{δ/8}`,
`R = η_s/η_u`, `r = ℓ_u/ℓ_s`:

* the rescaled far-field threshold `A ≥ cWt²x^{33}R^{10}` from (2.72)
  (`RBM.StepSideAPrime.A_ge_of_reg`, **reused unchanged**);
* `β = r^{3/2}A^{-1/2}` and `γ = rA⁻¹` from that threshold (`sideBundleSharp''_of_A`).

The near-field slot does **not** appear here: in the sharp pass it is the *integrated* `qI`,
whose budget `2m⁻¹R²` is supplied by the time integral (T268), not by a ratio bound.  That is
the one structural difference from `side_conditions_of_reg''`, which still has `q = r³ ≤ R²`.

The `δ`-budget is the same as the first pass's — `cWt² ≤ N^{c-5δ}`, which forces `5δ < c`
(`RBM.StepSideAPrime.five_delta_lt`) and holds for all large `N` when it does
(`RBM.StepSideAPrime.eventually_cWt_sq_le`). -/
theorem side_conditions_sharp''_of_reg (hE : |E| < 2) {N : ℕ} {u : ℝ} (_hs0 : 0 ≤ s N)
    (hsu : s N ≤ u) (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hN1 : 1 ≤ (N : ℝ))
    (hcW : cWt ^ 2 ≤ (N : ℝ) ^ (c - 5 * δ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u) :
    cWt ^ 2 * ((N : ℝ) ^ (δ / 8)) ^ 33 * (etaT E (s N) / etaT E u) ^ 10 ≤ B.scale E N u ∧
      ((B.ell N u / B.ell N (s N)) * √(B.ell N u / B.ell N (s N)) *
          (√(B.scale E N u))⁻¹) *
          (cWt * ((N : ℝ) ^ (δ / 8)) ^ 16 * (etaT E (s N) / etaT E u) ^ 4) ≤ 1 ∧
      ((B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹) *
          (cWt * √cWt * ((N : ℝ) ^ (δ / 8)) ^ 24 * (etaT E (s N) / etaT E u) ^ 6) ≤ 1 := by
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
  have hAge := StepSideAPrime.A_ge_of_reg (x := (N : ℝ) ^ (δ / 8))
    (R := etaT E (s N) / etaT E u) (A := B.scale E N u) hN1 hR1 hδ0 hcW rfl hA
  obtain ⟨hβ, hγ⟩ := sideBundleSharp''_of_A (x := (N : ℝ) ^ (δ / 8))
    (R := etaT E (s N) / etaT E u) (r := B.ell N u / B.ell N (s N)) hx1 hR1 hr0 hr hAge
  exact ⟨hAge, hβ, hγ⟩

end Flow

/-! ### 3. Satisfiability of the sharp bundle, **with margin**

Written the way T263 wrote `RBM.StepSideAPrime.sat_StepSide''_half`, and for the same
reason: `RBM.Step2Bootstrap.sat_StepSideSharp_gt_one` meets all of
`RBM.CutHypTheta.StepSideSharp`'s directed constraints **at equality**, and that zero margin
is what the rescaling exists to remove. -/

section Sat

/-- **⭐ The sharp bundle is jointly satisfiable at every `R ≥ 1` with a factor `2` of slack
in every constraint that has a direction.**

`Ξ = x/2`, `A = 2cWt²x^{33}R^{10}`, `ε = (2cWt²x^{33}R^{10})⁻¹`, `qI = m⁻¹R²`,
`β = (2cWt x^{16}R⁴)⁻¹`, `γ = (2cWt^{3/2}x^{24}R⁶)⁻¹`, `κ = x/2`, `Jv = cWt x^{16}R⁴/2`.

Note `qI = m⁻¹R²` against the budget `2m⁻¹R²`: the near-field slot is the one whose budget
carries the spectral constant `m`, so the witness needs `0 < m`. -/
theorem sat_StepSideSharp''_half {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    StepSideSharp'' m x R (x / 2) (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))
      (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ (m⁻¹ * R ^ 2)
      (2 * (cWt * x ^ 16 * R ^ 4))⁻¹ (2 * (cWt * √cWt * x ^ 24 * R ^ 6))⁻¹ (x / 2)
      (cWt * x ^ 16 * R ^ 4 / 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  have hAv : (0 : ℝ) < 2 * (cWt ^ 2 * x ^ 33 * R ^ 10) := by positivity
  have hβv : (0 : ℝ) < 2 * (cWt * x ^ 16 * R ^ 4) := by positivity
  have hγv : (0 : ℝ) < 2 * (cWt * √cWt * x ^ 24 * R ^ 6) := by positivity
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  refine
    { R_ge := hR
      Ξ_nonneg := by positivity
      Ξ_le := by linarith
      A_ge := by nlinarith [(by positivity : (0:ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10)]
      ε_nonneg := by positivity
      ε_le := ?_
      qI_nonneg := by positivity
      qI_le := by nlinarith
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
      (0:ℝ) < cWt * x ^ 16 * R ^ 4)]
  · rw [inv_mul_eq_div, div_le_one hγv]; linarith [(by positivity :
      (0:ℝ) < cWt * √cWt * x ^ 24 * R ^ 6)]

/-- **The margin is real**: at the witness of `sat_StepSideSharp''_half` all eight constraints
that have a direction (`Ξ_le`, `A_ge`, `ε_le`, `qI_le`, `β_le`, `γ_le`, `κ_le`, `Jv_le`) are
**strict**, with a factor `2` to spare; the seven inequalities below cover them, the first one
serving both `Ξ_le` and `κ_le` (the two slots carry the same value `x/2`).

Contrast `RBM.Step2Bootstrap.sat_StepSideSharp_gt_one`, whose docstring records that it meets
its constraints at equality. -/
theorem sat_StepSideSharp''_half_strict {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    x / 2 < x ∧
      cWt ^ 2 * x ^ 33 * R ^ 10 < 2 * (cWt ^ 2 * x ^ 33 * R ^ 10) ∧
      (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ * (cWt ^ 2 * x ^ 33 * R ^ 10) < 1 ∧
      m⁻¹ * R ^ 2 < 2 * m⁻¹ * R ^ 2 ∧
      (2 * (cWt * x ^ 16 * R ^ 4))⁻¹ * (cWt * x ^ 16 * R ^ 4) < 1 ∧
      (2 * (cWt * √cWt * x ^ 24 * R ^ 6))⁻¹ * (cWt * √cWt * x ^ 24 * R ^ 6) < 1 ∧
      cWt * x ^ 16 * R ^ 4 / 2 < cWt * x ^ 16 * R ^ 4 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  have hA : (0 : ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10 := by positivity
  have hβ : (0 : ℝ) < cWt * x ^ 16 * R ^ 4 := by positivity
  have hγ : (0 : ℝ) < cWt * √cWt * x ^ 24 * R ^ 6 := by positivity
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hq : (0 : ℝ) < m⁻¹ * R ^ 2 := by positivity
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_, ?_, by linarith⟩
  · rw [inv_mul_eq_div, div_lt_one (by linarith)]; linarith
  · rw [inv_mul_eq_div, div_lt_one (by linarith)]; linarith
  · rw [inv_mul_eq_div, div_lt_one (by linarith)]; linarith

/-- The seven nonnegativity slots are strict at the witness as well: every witness value is
**positive**, so the bundle is not met by collapsing a slot to `0`. -/
theorem sat_StepSideSharp''_half_pos {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    0 < x / 2 ∧ 0 < (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ ∧ 0 < m⁻¹ * R ^ 2 ∧
      0 < (2 * (cWt * x ^ 16 * R ^ 4))⁻¹ ∧
      0 < (2 * (cWt * √cWt * x ^ 24 * R ^ 6))⁻¹ ∧
      0 < cWt * x ^ 16 * R ^ 4 / 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  exact ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
    by positivity⟩

/-- A concrete non-degenerate instance: `m = 1`, `x = 1`, `R = 2` (so the window is genuinely
non-collapsed, `R > 1`), with the factor-`2` margin of `sat_StepSideSharp''_half`. -/
theorem sat_StepSideSharp''_two :
    StepSideSharp'' 1 1 2 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 2 ^ 10))
      (2 * (cWt ^ 2 * (1 : ℝ) ^ 33 * 2 ^ 10))⁻¹ ((1 : ℝ)⁻¹ * (2 : ℝ) ^ 2)
      (2 * (cWt * (1 : ℝ) ^ 16 * 2 ^ 4))⁻¹ (2 * (cWt * √cWt * (1 : ℝ) ^ 24 * 2 ^ 6))⁻¹
      ((1 : ℝ) / 2) (cWt * (1 : ℝ) ^ 16 * 2 ^ 4 / 2) :=
  sat_StepSideSharp''_half one_pos le_rfl one_le_two

/-- The one-step output at the margin witness, in the **sharp** normalization:
`≤ (cSharp m + 1)·x²`. -/
theorem sat_stepRhsSharp''_div_half {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    stepRhsSharp'' m x R (x / 2) (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))
        (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹ (m⁻¹ * R ^ 2)
        (2 * (cWt * x ^ 16 * R ^ 4))⁻¹ (2 * (cWt * √cWt * x ^ 24 * R ^ 6))⁻¹ (x / 2)
        (cWt * x ^ 16 * R ^ 4 / 2) / R ^ 2
      ≤ (Step2Near47.cSharp m + 1) * x ^ 2 :=
  stepRhsSharp''_div_le hx hm (sat_StepSideSharp''_half hm hx hR)

end Sat

/-! ### 4. The skeleton: (G) plus three slot bounds, in `T·R²` units

Identical in shape to `RBM.APrimeOneStep`'s §3, with two changes: the drift slot carries the
**integrated** near field `qI`, and every slot is divided by `R²` rather than `R⁴`.  The
initial and tail slots are literally `RBM.APrimeOneStep.initTerm` and
`RBM.APrimeOneStep.tailTerm` — those two groups are the same expressions in both passes. -/

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- (5.40)+(5.41)+(5.42) for the second pass: the drift and quadratic-variation slots of
`stepRhsSharp''`, with the near field entering as the integrated `qI`. -/
noncomputable def driftTermSharp (m x R Ξ A ε qI β γ Jv : ℝ) : ℝ :=
  Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
    + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv)))

/-- The three slot groups add up to `stepRhsSharp''` **exactly**: the split is an identity,
not an estimate. -/
theorem stepRhsSharp''_eq_split (m x R Ξ A ε qI β γ κ Jv : ℝ) :
    stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv
      = initTerm x R Ξ + driftTermSharp m x R Ξ A ε qI β γ Jv + tailTerm x R κ := by
  unfold stepRhsSharp'' driftTermSharp initTerm tailTerm
  ring

/-- **⭐⭐ The sharp one-step chain: the three slot bounds close `stepRhsSharp''`.**

`hG` is the conclusion of the weighted Minkowski closure (G),
`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le` — **already a theorem** (T264).

The three named inputs are the slot bounds, in `T·R²` units:

* `hinit` — **(5.39)** read sharply: the initial datum at the left endpoint of the cell, i.e.
  the **first pass's conclusion** there.  *Supplier*: T271 (`RBM1D/Gauss/APrimeModel.lean`)
  composed with T269's envelope (`RBM1D/Gauss/APrimePrior.lean`).
* `hdrift` — **(5.40)+(5.41)+(5.42)**, the time integral of the drift and the integrated near
  field.  *Suppliers*: T268 (`RBM1D/Gauss/APrimeTimeInt.lean`) for the (S6) time integrals,
  T269 for the envelopes.  `RBM.APrimeOneStep.drift_bound_of_envelopes` resolves it into
  those, unchanged.
* `hqv` — **(5.42)** plus the near×near cross-term slot `κ`.  *Suppliers*: T265
  (`RBM1D/Gauss/APrimeDuhamel.lean`) for the (S5) pointwise cross-term bound, T267
  (`RBM1D/Gauss/EarlyQVRateEv.lean`) for the (S3) early-time rate; the bad event is paid for
  by `RBM.APrimeOneStep.integral_le_good_add_bad`.  `RBM.APrimeOneStep.qv_bound_of_envelope`
  resolves it, unchanged.

**The left endpoint may be `0`** (Cowork's ruling D17): (G)'s derivative hypothesis lives on
`Set.Ioo a b` only, so nothing here forces `0 < a`. -/
theorem stepRhsSharp''_div_of_slots {m x R Ξ A ε qI β γ κ Jv : ℝ} {a b : ℝ} {p : ℕ}
    {W : Ω → ℝ} {Y : ℝ → Ω → ℝ} {Adr Bcr g : ℝ → ℝ}
    (hG : momNormW P W p (Y b)
      ≤ momNormW P W p (Y a) + 2 * (∫ r in a..b, (Adr r + Bcr r))
        + √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r))
    (hinit : momNormW P W p (Y a) ≤ initTerm x R Ξ / R ^ 2)
    (hdrift : 2 * (∫ r in a..b, (Adr r + Bcr r))
      ≤ driftTermSharp m x R Ξ A ε qI β γ Jv / R ^ 2)
    (hqv : √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ tailTerm x R κ / R ^ 2) :
    momNormW P W p (Y b) ≤ stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2 := by
  refine hG.trans ?_
  rw [stepRhsSharp''_eq_split, add_div, add_div]
  exact add_le_add (add_le_add hinit hdrift) hqv

/-- **⭐⭐ The sharp one-step chain, in normalized units `J*/R²`, with (G) wired in.** -/
theorem momNormW_le_stepRhsSharp''_div {m x R Ξ A ε qI β γ κ Jv : ℝ}
    {a b : ℝ} (hab : a ≤ b) {p : ℕ} (hp : 1 ≤ p) {W : Ω → ℝ} {Y : ℝ → Ω → ℝ}
    {φ' Adr Bcr g : ℝ → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hcont : ContinuousOn (fun u => ∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P) (Icc a b))
    (hderiv : ∀ u ∈ Ioo a b,
      HasDerivAt (fun r => ∫ ω, W ω * |Y r ω| ^ (2 * p) ∂P) (φ' u) u)
    (hφ'int : IntervalIntegrable φ' volume a b)
    (hA0 : ∀ u ∈ Icc a b, 0 ≤ Adr u) (hB0 : ∀ u ∈ Icc a b, 0 ≤ Bcr u)
    (hg0 : ∀ u ∈ Icc a b, 0 ≤ g u)
    (hABint : IntervalIntegrable (fun r => Adr r + Bcr r) volume a b)
    (hgint : IntervalIntegrable g volume a b)
    (hintψf : ∀ u ∈ Icc a b,
      IntervalIntegrable (fun r => momNormW P W p (Y r) * (Adr r + Bcr r)) volume a u)
    (hbound : ∀ u ∈ Ioo a b, φ' u
      ≤ 2 * (p : ℝ) * (∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P)
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (Adr u + Bcr u)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ)) * g u)
    (hinit : momNormW P W p (Y a) ≤ initTerm x R Ξ / R ^ 2)
    (hdrift : 2 * (∫ r in a..b, (Adr r + Bcr r))
      ≤ driftTermSharp m x R Ξ A ε qI β γ Jv / R ^ 2)
    (hqv : √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ tailTerm x R κ / R ^ 2) :
    momNormW P W p (Y b) ≤ stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2 :=
  stepRhsSharp''_div_of_slots (weightedMinkowski_of_deriv_le hab hp hW0 hcont hderiv hφ'int
    hA0 hB0 hg0 hABint hgint hintψf hbound) hinit hdrift hqv

/-- **The `κ` slot from the near×near cross term of referee §5 step 6.**

Step 6 reads: after normalizing by `T·R²` the near field satisfies `∫Q̂ = O(1)`, and the
cross term near×near is `N^{−2δ}(log N)^{1/2}`.  With `x = N^{δ/8}` the slot's budget is
`κ ≤ x = N^{δ/8}`, so the statement to supply is that the cross term is below `N^{δ/8}`,
which `N^{−2δ}(log N)^{1/2} → 0` makes true for all large `N`.

This lemma is the shape of that hand-off — a **monotonicity step**, nothing more: whatever
bound `cr` a supplier proves, if `cr ≤ x` then `κ = cr` fits.  It is stated so that T265/T267
have a single named target.  *Suppliers*: T265 (`RBM1D/Gauss/APrimeDuhamel.lean`), T267
(`RBM1D/Gauss/EarlyQVRateEv.lean`). -/
theorem kappa_le_of_crossTerm {cr x : ℝ} (hcr0 : 0 ≤ cr) (hcr : cr ≤ x) : 0 ≤ cr ∧ cr ≤ x :=
  ⟨hcr0, hcr⟩

/-- The quantifier shape the `κ` supplier must hit: `∀ p, ∀ᶠ N in atTop, …`, never
`∀ p N, …`.  With `cr N = N^{-2δ}√(log N)` and the budget `x = N^{δ/8}` this is true because
the left side tends to `0` and the right side is `≥ 1`; the lemma below is the abstract
version, so that a supplier only has to produce `cr N → 0`. -/
theorem eventually_kappa_le {δ : ℝ} (hδ : 0 < δ) {cr : ℕ → ℝ}
    (hcr : Filter.Tendsto cr atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, cr N ≤ (N : ℝ) ^ (δ / 8) := by
  have h1 : ∀ᶠ N : ℕ in atTop, cr N ≤ 1 := by
    exact hcr.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h1, eventually_ge_atTop 1] with N hN hN1
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  exact hN.trans (Real.one_le_rpow hNR (by linarith))

end Chain

/-! ### 5. The one-step moment bound `WeightedMoment` consumes -/

section OneStep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The one-step moment bound, in the form
`RBM.Step2Bootstrap.weightedMoment_of_stepBoundSharp` consumes it** (with `''` for the
rescaled level).

`hdom` says the interface functional `cutTrunc θ (Jf ·)` is dominated by the normalized
Duhamel functional `Y`; `hYint` is integrability of the majorant.

⚠ `hdom` is quantified over all `ω` with no good event; that is admissible **only** because
both sides are random — see `RBM.APrimeOneStep.integral_cutTrunc_le_of_momNormW_le`, whose
docstring records the trap, and whose satisfiability witness
`RBM.APrimeOneStep.integral_cutTrunc_le_of_momNormW_le_self` is the identity instantiation. -/
theorem oneStepSharp_integral_le {m x R Ξ A ε qI β γ κ Jv : ℝ}
    {p : ℕ} (hp : 1 ≤ p) {W Jf : Ω → ℝ} {Y : Ω → ℝ} {θ : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hYint : Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hdom : ∀ ω, |cutTrunc θ (Jf ω)| ≤ |Y ω|)
    (hmom : momNormW P W p Y ≤ stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ (stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2) ^ (2 * p) :=
  integral_cutTrunc_le_of_momNormW_le hW0 hp hYint hdom hmom

/-- The same, with the arithmetic of `phi_arith_sharp''` read off: the one-step output is
`((cSharp m + 1)·x²)^{2p}`, which is exactly the per-`p` clause
`RBM.Step2Bootstrap.weightedMoment_bound_of_sq` consumes with `x = N^{δ/8}`. -/
theorem oneStepSharp_integral_le_sq {m x R Ξ A ε qI β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (hside : StepSideSharp'' m x R Ξ A ε qI β γ κ Jv)
    {p : ℕ} (hp : 1 ≤ p) {W Jf : Ω → ℝ} {Y : Ω → ℝ} {θ : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hYint : Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hdom : ∀ ω, |cutTrunc θ (Jf ω)| ≤ |Y ω|)
    (hmom : momNormW P W p Y ≤ stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ ((Step2Near47.cSharp m + 1) * x ^ 2) ^ (2 * p) := by
  have hR2 : (0 : ℝ) < R ^ 2 := by
    have : (0 : ℝ) < R := by linarith [hside.R_ge]
    positivity
  have h0 : (0 : ℝ) ≤ stepRhsSharp'' m x R Ξ A ε qI β γ κ Jv / R ^ 2 :=
    div_nonneg (le_trans zero_le_one (one_le_stepRhsSharp'' hx hm hside)) hR2.le
  exact (oneStepSharp_integral_le hp hW0 hYint hdom hmom).trans
    (pow_le_pow_left₀ h0 (stepRhsSharp''_div_le hx hm hside) _)

end OneStep

/-! ### 6. `WeightedMoment` from the sharp rescaled arithmetic

The `''` counterparts of `RBM.Step2Bootstrap.weightedMoment_bound_of_oneStepSharp` and
`RBM.Step2Bootstrap.weightedMoment_of_stepBoundSharp`.  The constant is
`(RBM.Step2Near47.cSharp m + 1)^{2p}`, which is what `phi_arith_sharp''` actually outputs;
the **loss exponent `N^{δ/2·p}` is unchanged** — that is the interface-level form of "the
second pass costs a constant, not an exponent". -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ}
  {s t mesh : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ} {W : ℝ → ℕ → ℕ → Ω → ℝ}

/-- `RBM.Step2Bootstrap.weightedMoment_bound_of_oneStepSharp` for `StepSideSharp''`. -/
theorem weightedMoment_bound_of_oneStepSharp'' {δ m : ℝ} (hδ0 : 0 ≤ δ) (hm : 0 < m)
    (hΘ : ∀ N, Θ N = 1) (p : ℕ)
    (h : ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N, ∃ R Ξ A ε qI β γ κ Jv : ℝ,
      StepSideSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv ∧
        ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
          ≤ (stepRhsSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv / R ^ 2) ^ (2 * p)) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
      ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
          (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p)) := by
  have hc₀ : (0 : ℝ) < Step2Near47.cSharp m + 1 := by
    linarith [Step2Near47.cSharp_pos hm]
  refine Step2Bootstrap.weightedMoment_bound_of_sq hc₀ hΘ p ?_
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1 k hk
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  obtain ⟨R, Ξ, A, ε, qI, β, γ, κ, Jv, hside, hmom⟩ := hN k hk
  have hR2 : (0 : ℝ) < R ^ 2 := by
    have : (0 : ℝ) < R := by linarith [hside.R_ge]
    positivity
  have h0 : (0 : ℝ) ≤ stepRhsSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv / R ^ 2 :=
    div_nonneg (le_trans zero_le_one (one_le_stepRhsSharp'' hx hm hside)) hR2.le
  exact hmom.trans (pow_le_pow_left₀ h0 (stepRhsSharp''_div_le hx hm hside) _)

/-- `RBM.Step2Bootstrap.weightedMoment_of_stepBoundSharp` for `StepSideSharp''`. -/
theorem weightedMoment_of_stepBoundSharp'' {δ₀ m : ℝ} (hm : 0 < m) (hΘ : ∀ N, Θ N = 1)
    (H : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t mesh N, ∃ R Ξ A ε qI β γ κ Jv : ℝ,
        StepSideSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv ∧
          ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
              (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (stepRhsSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv / R ^ 2) ^ (2 * p)) :
    Step2Bootstrap.WeightedMoment P J s t mesh lev Θ δ₀ W :=
  fun δ hδ0 hδ p => weightedMoment_bound_of_oneStepSharp'' hδ0.le hm hΘ p (H δ hδ0 hδ p)

end Bridge

/-! ### 7. ⚠ The `p = 0` branch

Exactly the trap T230 walked into, and exactly as `RBM.APrimeOneStep` §6 closes it: at
`p = 0` the integrand degenerates to the weight itself, so the pointwise domination `hdom`
becomes `1 ≤ 1` and carries nothing, and `momNormW`'s exponent `1/(2p)` is `1/0`.  The
branch is not a gap — `0 ≤ W ≤ 1` on a probability space already gives `≤ 1 = (·)^0` — and it
is discharged here once and for all by `RBM.Gauss.integral_weight_pow_zero_le` (T260), so a
producer only ever has to argue for `1 ≤ p`, which is what (G) needs anyway. -/

section PZero

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}
  {W : ℝ → ℕ → ℕ → Ω → ℝ}

/-- The `p = 0` clause of the sharp one-step hypothesis, as a theorem. -/
theorem oneStepSharp_pzero {m δ : ℝ} (hm : 0 < m) (hδ0 : 0 < δ) (N k : ℕ) (hN1 : 1 ≤ N)
    (hW0 : ∀ ω, 0 ≤ W δ N k ω) (hW1 : ∀ ω, W δ N k ω ≤ 1)
    (hWm : AEStronglyMeasurable (fun ω => W δ N k ω) P) :
    ∃ R Ξ A ε qI β γ κ Jv : ℝ,
      StepSideSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv ∧
        ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * 0) ∂P
          ≤ (stepRhsSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv / R ^ 2) ^ (2 * 0) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  refine ⟨1, _, _, _, _, _, _, _, _, sat_StepSideSharp''_half hm hx le_rfl, ?_⟩
  have hzero := Gauss.integral_weight_pow_zero_le (P := P) (W := W δ N k)
    (J := fun ω => J N (cutNetPt s mesh N k) ω)
    (θ := (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k)) hW0 hW1 hWm
  refine hzero.trans ?_
  simp

/-- **`WeightedMoment` with the `p = 0` branch discharged**: the producer supplies the sharp
one-step bound only for `1 ≤ p`. -/
theorem weightedMoment_of_stepBoundSharpPos'' {δ₀ m : ℝ} (hm : 0 < m) (hΘ : ∀ N, Θ N = 1)
    (hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω) (hW1 : ∀ δ N k ω, W δ N k ω ≤ 1)
    (hWm : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => W δ N k ω) P)
    (H : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t mesh N, ∃ R Ξ A ε qI β γ κ Jv : ℝ,
        StepSideSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv ∧
          ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
              (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (stepRhsSharp'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ κ Jv / R ^ 2) ^ (2 * p)) :
    Step2Bootstrap.WeightedMoment P J s t mesh lev Θ δ₀ W := by
  refine weightedMoment_of_stepBoundSharp'' hm hΘ ?_
  intro δ hδ0 hδ p
  match p with
  | 0 =>
    filter_upwards [eventually_ge_atTop 1] with N hN1 k _
    exact oneStepSharp_pzero (lev := lev) (J := J) (s := s) (mesh := mesh) hm hδ0 N k hN1
      (hW0 δ N k) (hW1 δ N k) (hWm δ N k)
  | (n + 1) => exact H δ hδ0 hδ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

end PZero

/-! ### 8. Satisfiability: the sharp skeleton is not self-contradictory

The danger a skeleton runs is that one of its named inputs is, read literally, unsatisfiable —
then every theorem downstream is vacuously true and the compiler says nothing.  The witness
below is **non-degenerate**: T264's sharp witness for (G) (`p = 1`, `W ≡ 1`, `Y_u ≡ √u`,
`g ≡ 1` on `[0, 1]`, in which the moment and the quadratic-variation slot are both nonzero
and (G) is attained with equality) run against the **margin** witness
`sat_StepSideSharp''_half` for the side conditions.  The left endpoint of the window is
**exactly `0`** (D17). -/

section SatChain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The sharp drift slot of the margin witness is nonnegative, which is all the degenerate
drift of the (G) witness below needs. -/
theorem sat_driftTermSharp_nonneg :
    0 ≤ driftTermSharp 1 1 1 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))
      (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))⁻¹ ((1 : ℝ)⁻¹ * 1 ^ 2)
      (2 * (cWt * 1 ^ 16 * 1 ^ 4))⁻¹ (2 * (cWt * √cWt * 1 ^ 24 * 1 ^ 6))⁻¹
      (cWt * 1 ^ 16 * 1 ^ 4 / 2) / (1 : ℝ) ^ 2 := by
  have hc0 : (0 : ℝ) < cWt := cWt_pos
  have hsc : (0 : ℝ) < √cWt := Real.sqrt_pos.2 hc0
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  unfold driftTermSharp
  have hJ : (0 : ℝ) ≤ cWt * 1 ^ 16 * 1 ^ 4 / 2 := by positivity
  have hsJ : (0 : ℝ) ≤ √(cWt * 1 ^ 16 * 1 ^ 4 / 2) := Real.sqrt_nonneg _
  positivity

/-- **⭐ The satisfiability witness for the whole sharp skeleton.**

`stepRhsSharp''_div_of_slots` is instantiated at

* T264's **non-degenerate** witness for (G), `RBM.MomentDuhamel.sat_weightedMinkowski_sharp`:
  `p = 1`, `W ≡ 1`, `Y_u ≡ √u` on `[0, 1]`, drift `≡ 0`, quadratic-variation rate `≡ 1`.
  There `E[W|Y_1|²] = 1` and `√((2p−1)∫g) = 1`: **the moment and the quadratic-variation slot
  are both nonzero**, and (G) is attained with equality.
* the **margin** witness `sat_StepSideSharp''_half` at `m = x = R = 1`, which meets all eight
  directed constraints with a factor `2` to spare.

So the three named slot hypotheses `hinit`, `hdrift`, `hqv` hold **simultaneously** on an
instance where nothing has collapsed to `0`. -/
theorem sat_stepRhsSharp''_div_of_slots :
    momNormW P (fun _ => (1 : ℝ)) 1 (fun _ => √(1 : ℝ))
      ≤ stepRhsSharp'' 1 1 1 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))
          (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))⁻¹ ((1 : ℝ)⁻¹ * 1 ^ 2)
          (2 * (cWt * 1 ^ 16 * 1 ^ 4))⁻¹ (2 * (cWt * √cWt * 1 ^ 24 * 1 ^ 6))⁻¹ ((1 : ℝ) / 2)
          (cWt * 1 ^ 16 * 1 ^ 4 / 2) / (1 : ℝ) ^ 2 := by
  refine stepRhsSharp''_div_of_slots (a := 0) (b := 1) (p := 1) (Y := fun u _ => √u)
    (Adr := fun _ => 0) (Bcr := fun _ => 0) (g := fun _ => 1)
    (sat_weightedMinkowski_sharp P) ?_ ?_ ?_
  · simp [momNormW, initTerm]
  · simpa using sat_driftTermSharp_nonneg
  · norm_num [tailTerm]

/-- The witness carried all the way through the sharp arithmetic: the one-step output of the
skeleton is below `(cSharp 1 + 1)·x²` at `x = 1`, i.e. the constant `phi_arith_sharp''`
advertises.  The left-hand side is `1`, not `0`. -/
theorem sat_oneStepSharp_chain :
    momNormW P (fun _ => (1 : ℝ)) 1 (fun _ => √(1 : ℝ))
      ≤ (Step2Near47.cSharp 1 + 1) * (1 : ℝ) ^ 2 :=
  (sat_stepRhsSharp''_div_of_slots (P := P)).trans
    (sat_stepRhsSharp''_div_half one_pos le_rfl le_rfl)

/-- The side conditions of the same witness, for the record: `oneStepSharp_integral_le_sq` is
applicable to it. -/
theorem sat_stepSideSharp'' :
    StepSideSharp'' 1 1 1 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))
      (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))⁻¹ ((1 : ℝ)⁻¹ * 1 ^ 2)
      (2 * (cWt * 1 ^ 16 * 1 ^ 4))⁻¹ (2 * (cWt * √cWt * 1 ^ 24 * 1 ^ 6))⁻¹ ((1 : ℝ) / 2)
      (cWt * 1 ^ 16 * 1 ^ 4 / 2) :=
  sat_StepSideSharp''_half one_pos le_rfl le_rfl

end SatChain

end APrimeOneStepSharp

end RBM

/-!
## Deviations from the paper

**T272a.**  §5.3, the second pass, (5.47).

① *Paper location.*  (5.47) re-reads the one-step right-hand side after the stopping time of
(5.43) has been excluded; the near field then enters as `(η_s/η_t)²1(·) + 1` rather than
through the level `Λ`, and the output is read in the sharp normalization `J*/R²`.
`RBM.Step2Near47.phi_arith_second_pass` is that statement verbatim.

② *Is the paper changed?*  **No**, and for the same reason as `T263a`: in route (A′) the
stopping time (5.43) is replaced by the soft-max cutoff weight, whose support carries the
level `4e·N^{2δ}R⁴ < cWt·x^{16}R⁴` rather than `N^δR⁴`.  The paper's estimates are used at
that larger level; the rescaled side conditions are **strictly stronger** than the paper's,
and §2 above shows (2.72) still discharges them with (2.72)'s exponent `30` untouched.  The
budget is the same `5δ < c` T263 already paid.

③ *What is new relative to `T263a`.*  Two things, both forced by the `T·R²` normalization
(which is the paper's own, at (5.47)):

  * the two far-field conditions each cost one more power of `R²` — `β·(cWt x^{16}R⁴) ≤ 1`
    and `γ·(cWt^{3/2}x^{24}R⁶) ≤ 1`, i.e. `β* = 9.5` and `β* = 6.5` in the paper's counting,
    exactly the same two powers `phi_arith_second_pass` pays over `phi_arith_sharp`.  The
    threshold `cWt²x^{33}R^{10}` is unchanged, so the `β` branch now nearly saturates it
    (`beta_margin_sharp`: `R^{0.5}` of slack, against T263's `R^{4.5}`).  **This is the
    binding condition of the sharp pass.**
  * the near field enters as the integrated `qI ≤ 2m⁻¹R²` rather than the coefficient
    `q ≤ R²`; that is `phi_arith_second_pass`'s shape, not a new deviation.

④ *The slot `κ`.*  As in `T263a`, `κ` has **no counterpart in the paper**: it is the
near×near cross term of the fixed-`ω` generator identity that route (A′) introduces (referee
(S5), §5 step 6).  It is budgeted like the `≺`-loss, `κ ≤ x = N^{δ/8}`, and it costs exactly
one more `x²R²`, so the output is `(cSharp m + 1)·x²R²` rather than `cSharp m·x²R²`.

⑤ *Renumbering?*  **No.**  No paper equation is renumbered, and nothing outside this file is
edited.
-/
