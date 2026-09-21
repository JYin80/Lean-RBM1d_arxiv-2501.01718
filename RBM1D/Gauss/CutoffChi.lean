/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CutoffBounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A concrete `C²` cutoff profile, and the instantiation of T158's hypotheses (T175)

`RBM1D/Gauss/CutoffBounds.lean` (T158) takes the cutoff profile `χ` **abstractly**: every
statement about it carries a `HasDerivAt χ dχ ·` hypothesis and a bound `|dχ| ≤ C_χ`, and
T158 deliberately built no concrete `χ`, so the whole scheme rested on hypotheses that had
never been exhibited.  This file supplies the witness and instantiates them.

## Which construction, and why not Mathlib's

**Mathlib's smooth transitions cannot be used here.**  `Real.smoothTransition` and
`ContDiffBump` are `C^∞`, but Mathlib proves about them only `zero_of_nonpos`,
`one_of_one_le`, `nonneg`, `le_one`, `monotone` and `ContDiff` — **no derivative formula, no
derivative bound, no Lipschitz constant** (checked: `Mathlib/Analysis/SpecialFunctions/
SmoothTransition.lean` and `Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`).  T158's
`abs_threshold_drift_le` and the gap terms need `C_χ` as an actual number, and for
`Real.smoothTransition` the sup of `|χ'|` is
`sup_{0<t<1} (t^{-2} + (1-t)^{-2}) e^{-1/t-1/(1-t)} / (e^{-1/t}+e^{-1/(1-t)})²`, which is not
a closed form; making it explicit — let alone the second derivative — is a project of its own.
Inventing a constant for it would be a fake proof, so we do not.

Instead we use the **quintic Hermite cutoff**, which is exactly `C²` (all that T158 and the
generator `𝓛 = ½ ∑ S_{ij} ∂_{ij}∂_{ji}` need) and whose derivative bounds are rational
numbers.  Writing it in the truncated-power basis makes the `C²` gluing a *theorem* rather
than a case analysis: with `u = (x-1)_+`, `v = (x-2)_+` and
`P(t) = 6t⁵ - 15t⁴ + 10t³`, `Q(s) = 6s⁵ + 15s⁴ + 10s³`,

`cutChi x = 1 - P(u) + Q(v)`,

and the algebraic identity `P(s+1) = 1 + Q(s)` is what makes it vanish identically on
`[2, ∞)`.  Since `(·)_+^k` is `C^{k-1}` and all exponents are `≥ 3`, the profile is `C²`
with no gluing conditions to check by hand (`hasDerivAt_maxPow`).

## The profile and its constants

* `RBM.Cutoff.cutChi`, `cutChiD`, `cutChiDD` — `χ`, `χ'`, `χ''`.
* `cutChi_eq_one` : `χ = 1` on `(-∞, 1]` (in particular on `[0,1]`), `cutChi_eq_zero` :
  `χ = 0` on `[2, ∞)`, `cutChi_antitone`, `cutChi_nonneg`, `cutChi_le_one`.
* `hasDerivAt_cutChi`, `hasDerivAt_cutChiD`, `contDiff_cutChi` (`ContDiff ℝ 2`).
* **`abs_cutChiD_le` : `|χ'| ≤ 15/8`** — attained at `x = 3/2` (`cutChiD_three_halves`),
  so this constant is *sharp*.
* **`abs_cutChiDD_le` : `|χ''| ≤ 15`** — from `|χ''| = 60·|(x-1)(x-2)|·|2x-3| ≤ 60·¼·1`.
  Not optimal (the true sup is `10/√3 ≈ 5.7735`); per `CLAUDE.md` constants are not optimized.
* `cutChiD_eq_zero_left` / `cutChiD_eq_zero_right` : `χ'` is supported in `[1,2]`, which is
  exactly T158's "gap" `J_u/Θ_u ∈ [1,2]`.

## What of T158 is now instantiated

* `RBM.Cutoff.hasDerivAt_cutComp` — its `hχ` hypothesis is discharged by `hasDerivAt_cutChi`;
  the χ-free consequence is `hasDerivAt_cutComp_cutChi`.
* `RBM.Cutoff.abs_threshold_drift_le` — its `hdχ` hypothesis is discharged by `abs_cutChiD_le`
  with `C_χ = 15/8`; the χ-free consequence is `abs_threshold_drift_cutChi_le`, giving the
  **numerical** drift bound `15 m / η_u`.

These two are the *only* statements of `CutoffBounds.lean` that quantify over `χ`; everything
else there (`smoothMax`, `cutWeight`, `tailT`, the threshold derivative) is about `J`, `T` and
`Θ` and needs no cutoff profile.  So after this file **no hypothesis about `χ` remains open**
in the T158 deliverable.  What remains open in the cutoff *scheme* is what T158 already listed
as out of scope: the de-truncation step (probability level) and the assembly T132b/T132c.

## Satisfiability

`cutChi_spec` bundles the whole hypothesis package that T158 imposes on `χ` and proves it
inhabited, so the instantiated statements are not simultaneously unsatisfiable.  Two numerical
self-checks (`cutChi_three_halves`, `cutChiD_three_halves`, and the `example` after
`abs_threshold_drift_cutChi_le`) pin the profile and the constant `15/8` to concrete values:
a mis-copied coefficient would fail to compile here rather than silently weaken the estimate.

## Deviations

None from the paper: the paper uses a stopping time and no cutoff profile at all, so `χ` is a
Lean-side device (as `CutoffBounds.lean` already records).  The choice of the quintic profile
and the constants `15/8`, `15` are ours and are not optimized.
-/

namespace RBM
namespace Cutoff

open Set

/-! ### Truncated powers

`(·)_+^{n+2}` is `C¹` with derivative `(n+2)(·)_+^{n+1}`; iterating twice is what makes the
spline below `C²` without any hand gluing. -/

/-- **The truncated power is differentiable.**  `t ↦ (max t 0)^{n+2}` has derivative
`(n+2)(max t 0)^{n+1}` at every real `t`, including at the break point `t = 0` (where the
two one-sided derivatives are both `0` because the exponent is `≥ 2`). -/
theorem hasDerivAt_maxPow (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ (n + 2)) (((n : ℝ) + 2) * max t 0 ^ (n + 1)) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun s : ℝ => max s 0 ^ (n + 2)) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [max_eq_right (le_of_lt hs)]
      simp
    have h0 : max t 0 = 0 := max_eq_right ht.le
    have := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
    convert this using 1
    rw [h0]
    simp
  · subst ht
    have hR : HasDerivWithinAt (fun s : ℝ => max s 0 ^ (n + 2)) 0 (Ici (0 : ℝ)) 0 := by
      have hp : HasDerivWithinAt (fun s : ℝ => s ^ (n + 2))
          (((n : ℝ) + 2) * (0 : ℝ) ^ (n + 1)) (Ici (0 : ℝ)) 0 := by
        have := (hasDerivAt_pow (n + 2) (0 : ℝ)).hasDerivWithinAt (s := Ici (0 : ℝ))
        simpa using this
      have hz : ((n : ℝ) + 2) * (0 : ℝ) ^ (n + 1) = 0 := by simp
      rw [hz] at hp
      refine hp.congr (fun s hs => ?_) (by simp)
      rw [max_eq_left hs]
    have hL : HasDerivWithinAt (fun s : ℝ => max s 0 ^ (n + 2)) 0 (Iic (0 : ℝ)) 0 := by
      have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Iic (0 : ℝ)) 0 :=
        (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt
      refine hc.congr (fun s hs => ?_) (by simp)
      rw [max_eq_right hs]
      simp
    have := hL.union hR
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    simpa using this
  · have hev : (fun s : ℝ => max s 0 ^ (n + 2)) =ᶠ[nhds t] fun s => s ^ (n + 2) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left hs.le]
    have := (hasDerivAt_pow (n + 2) t).congr_of_eventuallyEq hev
    convert this using 1
    rw [max_eq_left ht.le]
    push_cast
    ring_nf

/-- The shifted truncated power `s ↦ (s - a)_+^{n+2}`. -/
theorem hasDerivAt_maxPow_shift (n : ℕ) (a x : ℝ) :
    HasDerivAt (fun s : ℝ => max (s - a) 0 ^ (n + 2))
      (((n : ℝ) + 2) * max (x - a) 0 ^ (n + 1)) x :=
  HasDerivAt.comp_sub_const x a (hasDerivAt_maxPow n (x - a))

/-! ### The cutoff profile -/

/-- **The concrete `C²` cutoff.**  `cutChi = 1` on `(-∞,1]`, `= 0` on `[2,∞)`, and on the gap
`[1,2]` it is `1 - P(x-1)` for the quintic Hermite profile `P(t) = 6t⁵ - 15t⁴ + 10t³`.  It is
written in the truncated-power basis `(x-1)_+`, `(x-2)_+` so that `C²` smoothness is inherited
from `hasDerivAt_maxPow` rather than checked at the break points. -/
noncomputable def cutChi (x : ℝ) : ℝ :=
  1 - (6 * max (x - 1) 0 ^ 5 - 15 * max (x - 1) 0 ^ 4 + 10 * max (x - 1) 0 ^ 3)
    + (6 * max (x - 2) 0 ^ 5 + 15 * max (x - 2) 0 ^ 4 + 10 * max (x - 2) 0 ^ 3)

/-- The derivative `χ'` of `cutChi`; see `hasDerivAt_cutChi`. -/
noncomputable def cutChiD (x : ℝ) : ℝ :=
  -(30 * max (x - 1) 0 ^ 4 - 60 * max (x - 1) 0 ^ 3 + 30 * max (x - 1) 0 ^ 2)
    + (30 * max (x - 2) 0 ^ 4 + 60 * max (x - 2) 0 ^ 3 + 30 * max (x - 2) 0 ^ 2)

/-- The second derivative `χ''` of `cutChi`; see `hasDerivAt_cutChiD`. -/
noncomputable def cutChiDD (x : ℝ) : ℝ :=
  -(120 * max (x - 1) 0 ^ 3 - 180 * max (x - 1) 0 ^ 2 + 60 * max (x - 1) 0)
    + (120 * max (x - 2) 0 ^ 3 + 180 * max (x - 2) 0 ^ 2 + 60 * max (x - 2) 0)

theorem hasDerivAt_cutChi (x : ℝ) : HasDerivAt cutChi (cutChiD x) x := by
  have h13 := hasDerivAt_maxPow_shift 1 1 x
  have h14 := hasDerivAt_maxPow_shift 2 1 x
  have h15 := hasDerivAt_maxPow_shift 3 1 x
  have h23 := hasDerivAt_maxPow_shift 1 2 x
  have h24 := hasDerivAt_maxPow_shift 2 2 x
  have h25 := hasDerivAt_maxPow_shift 3 2 x
  norm_num at h13 h14 h15 h23 h24 h25
  have key := (((hasDerivAt_const x (1 : ℝ)).sub
      (((h15.const_mul (6 : ℝ)).sub (h14.const_mul (15 : ℝ))).add (h13.const_mul (10 : ℝ)))).add
      (((h25.const_mul (6 : ℝ)).add (h24.const_mul (15 : ℝ))).add (h23.const_mul (10 : ℝ))))
  unfold cutChi
  convert key using 1
  unfold cutChiD
  ring

theorem hasDerivAt_cutChiD (x : ℝ) : HasDerivAt cutChiD (cutChiDD x) x := by
  have h12 := hasDerivAt_maxPow_shift 0 1 x
  have h13 := hasDerivAt_maxPow_shift 1 1 x
  have h14 := hasDerivAt_maxPow_shift 2 1 x
  have h22 := hasDerivAt_maxPow_shift 0 2 x
  have h23 := hasDerivAt_maxPow_shift 1 2 x
  have h24 := hasDerivAt_maxPow_shift 2 2 x
  norm_num at h12 h13 h14 h22 h23 h24
  have key := ((((h14.const_mul (30 : ℝ)).sub (h13.const_mul (60 : ℝ))).add
      (h12.const_mul (30 : ℝ))).neg).add
      (((h24.const_mul (30 : ℝ)).add (h23.const_mul (60 : ℝ))).add (h22.const_mul (30 : ℝ)))
  unfold cutChiD
  convert key using 1
  unfold cutChiDD
  ring

/-! ### Values: `1` below the gap, `0` above it -/

/-- `χ = 1` on `(-∞, 1]`, in particular on the `[0,1]` required by the cutoff scheme. -/
theorem cutChi_eq_one {x : ℝ} (hx : x ≤ 1) : cutChi x = 1 := by
  have h1 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  have h2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  simp [cutChi, h1, h2]

/-- `χ = 0` on `[2, ∞)`.  This is the identity `P(s+1) = 1 + Q(s)` between the two quintics. -/
theorem cutChi_eq_zero {x : ℝ} (hx : 2 ≤ x) : cutChi x = 0 := by
  have h1 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  have h2 : max (x - 2) 0 = x - 2 := max_eq_left (by linarith)
  simp only [cutChi, h1, h2]
  ring

/-- On the gap `[1,2]` the profile is the quintic Hermite step. -/
theorem cutChi_gap {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    cutChi x = 1 - (6 * (x - 1) ^ 5 - 15 * (x - 1) ^ 4 + 10 * (x - 1) ^ 3) := by
  have e1 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  have e2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  simp only [cutChi, e1, e2]
  norm_num

theorem cutChiD_eq_zero_left {x : ℝ} (hx : x ≤ 1) : cutChiD x = 0 := by
  have h1 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  have h2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  simp [cutChiD, h1, h2]

theorem cutChiD_eq_zero_right {x : ℝ} (hx : 2 ≤ x) : cutChiD x = 0 := by
  have h1 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  have h2 : max (x - 2) 0 = x - 2 := max_eq_left (by linarith)
  simp only [cutChiD, h1, h2]
  ring

/-- `χ' = -30 (x-1)²(x-2)²` on the gap; in particular `χ'` is supported in `[1,2]`, which is
exactly the gap `J_u/Θ_u ∈ [1,2]` on which `abs_threshold_drift_le` is stated. -/
theorem cutChiD_gap {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    cutChiD x = -(30 * (x - 1) ^ 2 * (x - 2) ^ 2) := by
  have e1 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  have e2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  simp only [cutChiD, e1, e2]
  norm_num
  ring

theorem cutChiDD_eq_zero_left {x : ℝ} (hx : x ≤ 1) : cutChiDD x = 0 := by
  have h1 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  have h2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  simp [cutChiDD, h1, h2]

theorem cutChiDD_eq_zero_right {x : ℝ} (hx : 2 ≤ x) : cutChiDD x = 0 := by
  have h1 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  have h2 : max (x - 2) 0 = x - 2 := max_eq_left (by linarith)
  simp only [cutChiDD, h1, h2]
  ring

/-- `χ'' = -60 (x-1)(2x-3)(x-2)` on the gap. -/
theorem cutChiDD_gap {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    cutChiDD x = -(60 * (x - 1) * (2 * x - 3) * (x - 2)) := by
  have e1 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  have e2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  simp only [cutChiDD, e1, e2]
  norm_num
  ring

/-! ### The explicit constants -/

/-- **`C_χ = 15/8`.**  The bound on `|χ'|` that `abs_threshold_drift_le` consumes.  It is
attained at `x = 3/2` (`cutChiD_three_halves`), hence sharp. -/
theorem abs_cutChiD_le (x : ℝ) : |cutChiD x| ≤ 15 / 8 := by
  rcases le_or_gt x 1 with h1 | h1
  · rw [cutChiD_eq_zero_left h1]; norm_num
  rcases le_or_gt 2 x with h2 | h2
  · rw [cutChiD_eq_zero_right h2]; norm_num
  have hp1 : (x - 1) * (x - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hp2 : -(1 / 4 : ℝ) ≤ (x - 1) * (x - 2) := by nlinarith [sq_nonneg (x - 3 / 2)]
  rw [cutChiD_gap h1.le h2.le, abs_le]
  constructor <;> nlinarith [sq_nonneg ((x - 1) * (x - 2))]

/-- `χ` is non-increasing: `χ' ≤ 0` everywhere. -/
theorem cutChiD_nonpos (x : ℝ) : cutChiD x ≤ 0 := by
  rcases le_or_gt x 1 with h1 | h1
  · rw [cutChiD_eq_zero_left h1]
  rcases le_or_gt 2 x with h2 | h2
  · rw [cutChiD_eq_zero_right h2]
  rw [cutChiD_gap h1.le h2.le]
  nlinarith [sq_nonneg ((x - 1) * (x - 2))]

/-- **`|χ''| ≤ 15`.**  From `|χ''| = 60·|(x-1)(x-2)|·|2x-3| ≤ 60·(1/4)·1` on the gap.  Not
optimal — the true supremum is `10/√3 ≈ 5.7735` — but explicit, which is what the second-order
(generator) terms need. -/
theorem abs_cutChiDD_le (x : ℝ) : |cutChiDD x| ≤ 15 := by
  rcases le_or_gt x 1 with h1 | h1
  · rw [cutChiDD_eq_zero_left h1]; norm_num
  rcases le_or_gt 2 x with h2 | h2
  · rw [cutChiDD_eq_zero_right h2]; norm_num
  have hp1 : (x - 1) * (x - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hp2 : -(1 / 4 : ℝ) ≤ (x - 1) * (x - 2) := by nlinarith [sq_nonneg (x - 3 / 2)]
  have hq1 : -(1 : ℝ) ≤ 2 * x - 3 := by linarith
  have hq2 : 2 * x - 3 ≤ 1 := by linarith
  rw [cutChiDD_gap h1.le h2.le, abs_le]
  constructor
  · nlinarith [mul_nonneg (neg_nonneg.2 hp1) (by linarith : (0 : ℝ) ≤ 1 - (2 * x - 3))]
  · nlinarith [mul_nonneg (neg_nonneg.2 hp1) (by linarith : (0 : ℝ) ≤ 1 + (2 * x - 3))]

/-! ### Monotonicity, range, and `C²` -/

theorem differentiable_cutChi : Differentiable ℝ cutChi :=
  fun x => (hasDerivAt_cutChi x).differentiableAt

theorem deriv_cutChi (x : ℝ) : deriv cutChi x = cutChiD x := (hasDerivAt_cutChi x).deriv

theorem deriv_cutChiD (x : ℝ) : deriv cutChiD x = cutChiDD x := (hasDerivAt_cutChiD x).deriv

theorem cutChi_antitone : Antitone cutChi :=
  antitone_of_deriv_nonpos differentiable_cutChi
    (fun x => by rw [deriv_cutChi]; exact cutChiD_nonpos x)

theorem cutChi_le_one (x : ℝ) : cutChi x ≤ 1 := by
  rcases le_or_gt x 1 with h | h
  · rw [cutChi_eq_one h]
  · have := cutChi_antitone h.le
    rwa [cutChi_eq_one le_rfl] at this

theorem cutChi_nonneg (x : ℝ) : 0 ≤ cutChi x := by
  rcases le_or_gt 2 x with h | h
  · rw [cutChi_eq_zero h]
  · have := cutChi_antitone h.le
    rwa [cutChi_eq_zero le_rfl] at this

theorem continuous_cutChiDD : Continuous cutChiDD := by
  unfold cutChiDD
  fun_prop

/-- **`χ` is `C²`** — the literal form of the smoothness the cutoff scheme asks for. -/
theorem contDiff_cutChi : ContDiff ℝ 2 cutChi := by
  have hd : deriv cutChi = cutChiD := funext deriv_cutChi
  have hdd : deriv cutChiD = cutChiDD := funext deriv_cutChiD
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨differentiable_cutChi, by simp, ?_⟩
  rw [hd, contDiff_one_iff_deriv]
  exact ⟨fun x => (hasDerivAt_cutChiD x).differentiableAt, by rw [hdd]; exact continuous_cutChiDD⟩

/-! ### Numerical self-checks

Pin the profile and the constant `15/8` to concrete values: a mis-copied coefficient in
`cutChi` / `cutChiD` / `cutChiDD` would make these fail to compile instead of silently
producing a weaker estimate. -/

theorem cutChi_three_halves : cutChi (3 / 2) = 1 / 2 := by
  rw [cutChi_gap (by norm_num) (by norm_num)]; norm_num

/-- The bound `15/8` of `abs_cutChiD_le` is **attained**, so it cannot be improved. -/
theorem cutChiD_three_halves : cutChiD (3 / 2) = -(15 / 8) := by
  rw [cutChiD_gap (by norm_num) (by norm_num)]; norm_num

theorem cutChiDD_three_halves : cutChiDD (3 / 2) = 0 := by
  rw [cutChiDD_gap (by norm_num) (by norm_num)]; norm_num

example : cutChi 0 = 1 := cutChi_eq_one (by norm_num)
example : cutChi 1 = 1 := cutChi_eq_one le_rfl
example : cutChi 2 = 0 := cutChi_eq_zero le_rfl
example : cutChi 3 = 0 := cutChi_eq_zero (by norm_num)

/-- `χ''` is genuinely nonzero somewhere in the gap, so `abs_cutChiDD_le` is not a statement
about the zero function. -/
example : cutChiDD (5 / 4) = -(45 / 8) := by
  rw [cutChiDD_gap (by norm_num) (by norm_num)]; norm_num

/-! ### Instantiating T158

`hasDerivAt_cutComp` and `abs_threshold_drift_le` are the only two statements of
`Gauss/CutoffBounds.lean` that quantify over the cutoff profile.  Both are discharged here. -/

/-- **T158's `hasDerivAt_cutComp` with no hypothesis on `χ`.**  The chain rule for
`u ↦ χ(J_u/Θ_u)` with the concrete profile: the first summand is the `∂_u J` drift, the second
is the term carried by the time dependence of the threshold. -/
theorem hasDerivAt_cutComp_cutChi {J Θ : ℝ → ℝ} {J' Θ' u : ℝ}
    (hJ : HasDerivAt J J' u) (hΘ : HasDerivAt Θ Θ' u) (hΘ0 : Θ u ≠ 0) :
    HasDerivAt (fun v => cutChi (J v / Θ v))
      (cutChiD (J u / Θ u) * (J' / Θ u)
        - cutChiD (J u / Θ u) * (J u / Θ u) * (Θ' / Θ u)) u :=
  hasDerivAt_cutComp hJ hΘ hΘ0 (hasDerivAt_cutChi (J u / Θ u))

/-- **T158's `abs_threshold_drift_le` with no hypothesis on `χ`.**  With `C_χ = 15/8` the
threshold-drift term `χ'(J_u/Θ_u)·(J_u/Θ_u)·Θ̇_u/Θ_u` is bounded by the **number** `15 m/η_u`
— the same order `η_u^{-1}` as the other drift terms, hence harmless. -/
theorem abs_threshold_drift_cutChi_le {q η m : ℝ} (hq0 : 0 ≤ q) (hq2 : q ≤ 2) (hm : 0 ≤ m)
    (hη : 0 < η) : |cutChiD q * q * (4 * m / η)| ≤ 15 * m / η := by
  have h := abs_threshold_drift_le (m := m) (dχ := cutChiD q) (Cχ := 15 / 8) (q := q) (η := η)
    (abs_cutChiD_le q) hq0 hq2 hm hη
  calc |cutChiD q * q * (4 * m / η)| ≤ 8 * (15 / 8) * m / η := h
    _ = 15 * m / η := by ring

/-- **Satisfiability check.**  The instantiated bound is not vacuous: at the worst point of the
gap the left-hand side is genuinely nonzero and the inequality holds with room to spare. -/
example : |cutChiD (3 / 2) * (3 / 2) * (4 * 1 / 1)| = 45 / 4 ∧ (45 / 4 : ℝ) ≤ 15 * 1 / 1 := by
  rw [cutChiD_three_halves]
  norm_num

/-- **The hypothesis package T158 imposes on `χ`, proved inhabited.**  Every condition the
cutoff scheme asks of the profile holds simultaneously for `cutChi`, so the instantiated
statements of `CutoffBounds.lean` are jointly satisfiable — the defect this ticket was opened
to close. -/
theorem cutChi_spec :
    (∀ x : ℝ, x ≤ 1 → cutChi x = 1) ∧
    (∀ x : ℝ, 2 ≤ x → cutChi x = 0) ∧
    (∀ x : ℝ, 0 ≤ cutChi x ∧ cutChi x ≤ 1) ∧
    Antitone cutChi ∧
    ContDiff ℝ 2 cutChi ∧
    (∀ x : ℝ, HasDerivAt cutChi (cutChiD x) x) ∧
    (∀ x : ℝ, HasDerivAt cutChiD (cutChiDD x) x) ∧
    (∀ x : ℝ, |cutChiD x| ≤ 15 / 8) ∧
    (∀ x : ℝ, |cutChiDD x| ≤ 15) :=
  ⟨fun _ hx => cutChi_eq_one hx, fun _ hx => cutChi_eq_zero hx,
    fun x => ⟨cutChi_nonneg x, cutChi_le_one x⟩, cutChi_antitone, contDiff_cutChi,
    hasDerivAt_cutChi, hasDerivAt_cutChiD, abs_cutChiD_le, abs_cutChiDD_le⟩

end Cutoff
end RBM
