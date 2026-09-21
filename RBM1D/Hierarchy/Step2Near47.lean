/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelCut

/-!
# The sharp (5.47): `J*_{u,D} ≺ (η_s/η_u)²` (T207)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.41), (5.44)–(5.48).

## The question this file answers

`RBM.Step2MomentStep.flowEq548_of_near_far` (T132c) and
`RBM.Step2MomentStep.flowEq548_of_near_farInputs` (T198) both ask for a near half

`|(L-K)_{u,(+,-),a}| ≺ (η_s/η_u)² · T_{u,D}(‖a₁-a₂‖)`,

which is the paper's (5.47) `J*_{τ,D} ≺ (η_s/η_t)²` and its consequence (5.48).  What the
repository produces is `RBM.Step2Moment.jS_stochDom` / `RBM.MomentDuhamelCut.jS_stochDom_cut`:

`J*_{u,D} ≺ (η_s/η_u)⁴`.

**Where the two powers are.**  They are not lost in an estimate.  `(η_s/η_u)⁴` is the paper's
*a priori* aim (5.29) and the level of the stopping time (5.43),
`T = min{u : J*_{u,D} ≥ (η_s/η_t)⁴}`, and the repository's whole Step 2 is normalized to it:
`RBM.Step2Moment.jSnorm = J*/(η_s/η_u)⁴`, hence `RBM.Step2Moment.MomentHyp`'s threshold, hence
`RBM.MomentDuhamelCut.MomentHypCut.cut`.  Proving `J* ≺ (η_s/η_u)⁴` is exactly the paper's
"hence `P(T ≤ t)` is negligible"; the paper's (5.47) is the *second, sharper reading* of the
same one-step bound, and the repository never takes it.

Inside the one-step arithmetic `RBM.Step2MomentStep.phi_arith'` the output is
`cStep' m · x² R⁴` and **exactly one of its seven summands is genuinely `R⁴`**: the near-field
term of (5.41), `Ξ · (x m⁻¹ R² q)` with `q = (ℓ_u/ℓ_s)³ ≤ R²` (its `t4`).  There the two
`u`-dependent factors `(η_u/η_t)²` and `(ℓ_u/ℓ_s)³` are bounded **separately**, each at its own
supremum — T174's warning, which T132c's `RBM.Step2MomentStep.integral_nearInt_le` implements
for the *quadratic variation* integrand of (5.44) but **not** for the *drift* integrand of
(5.41).  Done jointly (§1 below) that term is `2 m⁻¹ R²`, and then every summand is `R²`.

## What is proved here

* §1 `driftNearInt`, `integral_driftNearInt_le` —
  `∫_s^v η_u^{-1}(η_u/η_v)²(η_s/η_u)^{3/2} du ≤ 2 (Im m)^{-1}(η_s/η_v)²`, the missing
  "multiply first, then integrate".
* §1 `sup_mul_len_driftNearInt_eq`, `crude_exceeds_budget` — sup × length is **not** enough
  here: it gives `R^{5/2}`, strictly over budget once `R > 4`.  The genuine antiderivative
  `∫(1-u)^{-1/2}` is what buys the last half power.
* §2 `phi_arith_sharp` — the one-step arithmetic with output `cSharp m · x² **R²**`, where
  `cSharp m = cStep' m + m⁻¹`, under the **same side conditions** as `phi_arith'`.
* §2 `phi_lt_threshold_sharp`, `phi_arith_sharp_flow`, `sharp_side_conditions_of_reg` — the
  bootstrap closes at the sharp threshold `Λ = x⁸R²`; the near-field hypothesis is met by the
  integral of §1 itself; the exponent table does not move.
* §2/§2″ `phi_arith_second_pass`, `margin_of_reg`, `second_pass_side_conditions_of_reg` — the
  `R²` output already follows from the **blunt** a priori level `J* ≤ x⁸R⁴` that the
  repository has established, i.e. **no new bootstrap is needed**; its side conditions
  (`β* = 9.5`, `β* = 6.5`) come from (2.72) with a gain under the *same* `4δ ≤ 2c`.
* §3 `jSnorm2`, `MomentHypCutSharp`, `jS_stochDom_sharp` — (5.47) sharp,
  `J*_{u,D} ≺ (η_s/η_u)²`.
* §3 `jS_stochDom_of_sharp` — the sharp bound implies the `⁴` one verbatim, so nothing
  downstream is lost.
* §4 `hnear_of_jS`, `hnear_sharp`, `flowEq548_of_sharp_farInputs`, `aprioriDecay_of_sharp` —
  the `hnear` slot of (5.48), discharged; and (2.76) from the same bundle.
* §5 satisfiability witnesses.

## What is **not** proved here

`MomentHypCutSharp.cut` is a *hypothesis*, exactly as `RBM.MomentDuhamelCut.MomentHypCut.cut`
is: the truncated one-step moment bound is a statement about the Gaussian layer's Duhamel
expansion and cannot be derived from the `⁴` version.  What §2 proves is that the sharp
version needs **no more** than the blunt one: the side conditions of `phi_arith_sharp` are
literally those of `phi_arith'`, so `RBM.Step2MomentStep.hbeta_of_reg` and `hgamma_of_reg`
(`β* = 5.5`, `β* = 4.5`) discharge them unchanged, and the near-field row improves from
`β* = 4` with zero margin to `β* = 2`.

There is a further refinement this file stops short of.  `phi_arith_second_pass` shows the
sharp output needs only the *blunt* prefix `J* ≤ x⁸R⁴`, so the right interface would be a
`CutHyp` whose **truncation level** is read off the blunt bound and whose **conclusion** is
about `jSnorm2` — no second bootstrap at all.  `RBM.MomentDuhamelCut.CutHyp` cannot express
it, because its `Θ : ℕ → ℝ` has no `u`-dependence while the blunt level `N^{2δ}(η_s/η_u)²`
(read in `jSnorm2` units) does.  Generalizing `Θ` to `ℕ → ℝ → ℝ` would remove the last piece
of assumption here; `MomentHypCutSharp` is the version expressible against the frozen
interface today, and it is *stronger* than what §2 shows is needed (`jSnorm_le_jSnorm2`).

## Deviations from the paper (to report)

* `T207a`.  (5.47) is stated in the paper at the stopping time, `J*_{τ,D} ≺ (η_s/η_t)²`, for
  the window `[s,t]`; here it is `J*_{u,D} ≺ (η_s/η_u)²` uniformly in `u ∈ [s,t]`, which is
  the paper's own reading ("This statement holds for any `t ≥ s`", just before (5.45))
  applied to the sub-window `[s,u]`.  Since `η` is decreasing, `(η_s/η_u)² ≤ (η_s/η_t)²`, so
  the Lean statement is the stronger one, and it is the one `RBM.Step45.FlowEq548` consumes.
  No renumbering.
* `T207b`.  The near-field coefficient of (5.41) is `(ℓ_u/ℓ_s)³` here, not the paper's
  `(ℓ_u/ℓ_s)²`: this is the `(2.73)`-reduced shape 2 of (5.35) that T155's
  `RBM.Lemma57.eG_le_reduced` actually proves (already recorded by T132c as paper-delta #130).
  The sharpening of this file is insensitive to it — §1 integrates `(ℓ_u/ℓ_s)³` and still
  lands on `R²`.  No renumbering.
-/

namespace RBM

namespace Step2Near47

open Real Filter MeasureTheory intervalIntegral

/-! ### 1. (5.41)'s near field, integrated jointly -/

section Near

variable {E : ℝ}

/-- The near-field integrand of the **drift** term of (5.41), with the loop-length ratio
`ℓ_u/ℓ_s` already replaced by its bound `√(η_s/η_u)` (`RBM.Step3.ellHat_le_sqrt_mul`) and the
reduced shape's cube in place of the paper's square (`T207b`):

`η_u^{-1} (η_u/η_v)² (η_s/η_u)^{3/2}`.

Compare `RBM.Step2MomentStep.nearInt`, which is the same object for the **quadratic
variation** of (5.44) (exponents `4` and `5/2` instead of `2` and `3/2`). -/
noncomputable def driftNearInt (E s v u : ℝ) : ℝ :=
  (etaT E u)⁻¹ * (etaT E u / etaT E v) ^ 2 * √(etaT E s / etaT E u) ^ 3

/-- The integrand collapses to `η_s^{3/2} η_v^{-2} η_u^{-1/2}`, i.e. a constant times
`(1-u)^{-1/2}`.  Note the sign of the exponent: unlike `RBM.Step2MomentStep.nearInt`, which is
*increasing* in `η_u` and is therefore handled by "sup × length", this one is *decreasing*, so
sup × length overshoots (`sup_mul_len_driftNearInt_eq`) and a genuine antiderivative is
needed. -/
theorem driftNearInt_eq (hE : |E| < 2) {s v u : ℝ} (hs1 : s < 1) (hu1 : u < 1) (hv1 : v < 1) :
    driftNearInt E s v u
      = √(etaT E s) ^ 3 * (etaT E v ^ 2 * √((mE E).im))⁻¹ * (√(1 - u))⁻¹ := by
  have hm := mE_im_pos hE
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hb : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hp0 : 0 < √(1 - u) := Real.sqrt_pos.2 h1u
  have hq0 : 0 < √((mE E).im) := Real.sqrt_pos.2 hm
  have hsu : √(etaT E u) = √(1 - u) * √((mE E).im) := by
    rw [Step2.etaT_eq, Real.sqrt_mul h1u.le]
  have hbu : etaT E u = √(1 - u) ^ 2 * √((mE E).im) ^ 2 := by
    rw [Real.sq_sqrt h1u.le, Real.sq_sqrt hm.le, Step2.etaT_eq]
  have hdiv : √(etaT E s / etaT E u) = √(etaT E s) / √(etaT E u) := Real.sqrt_div ha.le _
  rw [driftNearInt, hdiv, hsu, div_pow, div_pow]
  rw [hbu]
  have hne1 : √(1 - u) ≠ 0 := hp0.ne'
  have hne2 : √((mE E).im) ≠ 0 := hq0.ne'
  have hne3 : etaT E v ≠ 0 := hc.ne'
  field_simp

/-- `∫_s^v (1-u)^{-1/2} du = 2√(1-s) - 2√(1-v)`. -/
theorem integral_inv_sqrt_one_sub {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) :
    (∫ u in s..v, (√(1 - u))⁻¹) = 2 * √(1 - s) - 2 * √(1 - v) := by
  have hderiv : ∀ u ∈ Set.uIcc s v, HasDerivAt (fun y => -2 * √(1 - y)) ((√(1 - u))⁻¹) u := by
    intro u hu
    rw [Set.uIcc_of_le hsv] at hu
    have hu1 : (0 : ℝ) < 1 - u := by linarith [hu.2]
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => √(1 - y)) (1 / (2 * √(1 - u)) * (-1)) u :=
      (Real.hasDerivAt_sqrt hu1.ne').comp u h1
    have h3 := h2.const_mul (-2 : ℝ)
    convert h3 using 1
    have hs0 : 0 < √(1 - u) := Real.sqrt_pos.2 hu1
    field_simp
  have hint : IntervalIntegrable (fun u => (√(1 - u))⁻¹) volume s v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hsv]
    intro u hu
    have hu1 : (0 : ℝ) < 1 - u := by linarith [hu.2]
    have hcw : ContinuousWithinAt (fun u : ℝ => √(1 - u)) (Set.Icc s v) u := by fun_prop
    exact hcw.inv₀ (Real.sqrt_pos.2 hu1).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- **(5.41)'s near-field drift term, integrated jointly**:

`∫_s^v η_u^{-1}(η_u/η_v)²(η_s/η_u)^{3/2} du ≤ 2 (Im m_E)^{-1} (η_s/η_v)²`.

This is the missing half of T174's second recommendation.  Its consequence is the whole
point of the file: with this in place, every summand of the one-step bound is `R²`, and
`RBM.Step2MomentStep.phi_arith'`'s only genuinely `R⁴` term disappears. -/
theorem integral_driftNearInt_le (hE : |E| < 2) {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) :
    (∫ u in s..v, driftNearInt E s v u) ≤ 2 * ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 2 := by
  have hm := mE_im_pos hE
  have hs1 : s < 1 := hsv.trans_lt hv1
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have h1v : (0 : ℝ) < 1 - v := by linarith
  set c : ℝ := √(etaT E s) ^ 3 * (etaT E v ^ 2 * √((mE E).im))⁻¹ with hcdef
  have hc0 : 0 < c := by
    have h1 : 0 < √(etaT E s) := Real.sqrt_pos.2 ha
    have h2 : 0 < √((mE E).im) := Real.sqrt_pos.2 hm
    rw [hcdef]; positivity
  have hcongr : (∫ u in s..v, driftNearInt E s v u) = ∫ u in s..v, c * (√(1 - u))⁻¹ := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hsv] at hu
    exact driftNearInt_eq hE hs1 (lt_of_le_of_lt hu.2 hv1) hv1
  rw [hcongr, intervalIntegral.integral_const_mul, integral_inv_sqrt_one_sub hsv hv1]
  have hstep : c * (2 * √(1 - s) - 2 * √(1 - v)) ≤ c * (2 * √(1 - s)) := by
    have : (0 : ℝ) ≤ √(1 - v) := Real.sqrt_nonneg _
    nlinarith
  refine hstep.trans (le_of_eq ?_)
  -- `c · 2√(1-s) = 2 m⁻¹ (η_s/η_v)²`, in the variables `p = √(1-s)`, `q = √(Im m)`
  obtain ⟨p, hp0, hp⟩ : ∃ p : ℝ, 0 < p ∧ p ^ 2 = 1 - s :=
    ⟨√(1 - s), Real.sqrt_pos.2 h1s, Real.sq_sqrt h1s.le⟩
  obtain ⟨q, hq0, hq⟩ : ∃ q : ℝ, 0 < q ∧ q ^ 2 = (mE E).im :=
    ⟨√((mE E).im), Real.sqrt_pos.2 hm, Real.sq_sqrt hm.le⟩
  have hps : √(1 - s) = p := by rw [← hp, Real.sqrt_sq hp0.le]
  have hqs : √((mE E).im) = q := by rw [← hq, Real.sqrt_sq hq0.le]
  have hsa : √(etaT E s) = p * q := by
    rw [Step2.etaT_eq, ← hp, ← hq, ← mul_pow, Real.sqrt_sq (by positivity)]
  have hes : etaT E s = p ^ 2 * q ^ 2 := by rw [Step2.etaT_eq, hp, hq]
  have hne3 : etaT E v ≠ 0 := hc.ne'
  rw [hcdef, hsa, hps, hqs, hes, ← hq]
  field_simp

/-- **Sup × length is not enough here.**  `driftNearInt` attains its maximum at the *right*
endpoint `u = v` (it decreases in `η_u`), and there it is `η_v^{-1}(η_s/η_v)^{3/2}`.  Times
the length of the window, `1 - s = η_s / Im m`, that is exactly

`(Im m)^{-1} (η_s/η_v)² · √(η_s/η_v)`,

i.e. the budget `2 (Im m)^{-1}(η_s/η_v)²` of `integral_driftNearInt_le` times **`√R/2`**.

This is why the recipe that works for `RBM.Step2MomentStep.nearInt` — whose integrand
*increases* in `η_u`, so that its supremum sits at `u = s` — does not transfer, and why the
honest antiderivative `integral_inv_sqrt_one_sub` is needed to buy the last half power. -/
theorem sup_mul_len_driftNearInt_eq (hE : |E| < 2) {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) :
    driftNearInt E s v v * (1 - s)
      = ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 2 * √(etaT E s / etaT E v) := by
  have hm := mE_im_pos hE
  have hs1 : s < 1 := hsv.trans_lt hv1
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hR0 : (0 : ℝ) < etaT E s / etaT E v := div_pos ha hc
  have hR3 : √(etaT E s / etaT E v) ^ 3
      = etaT E s / etaT E v * √(etaT E s / etaT E v) := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, Real.sq_sqrt hR0.le]
  have h1s : (1 : ℝ) - s = etaT E s / (mE E).im := by
    rw [Step2.etaT_eq]; field_simp
  rw [driftNearInt, hR3, h1s]
  rw [div_self hc.ne']
  field_simp

end Near

/-! ### 2. The one-step arithmetic at the sharp threshold -/

section Arith

/-- The constant of `phi_arith_sharp`.  It is `RBM.Step2MomentStep.cStep' m + m⁻¹`: the near
field is now integrated (`integral_driftNearInt_le`), which costs the factor `2` instead of
the factor `1` the separated bound carried. -/
noncomputable def cSharp (m : ℝ) : ℝ := 4 + exp 1 + (36 * exp 1 + 4) * m⁻¹

theorem cSharp_pos {m : ℝ} (hm : 0 < m) : 0 < cSharp m := by
  have : 0 < exp 1 := exp_pos 1
  have : 0 < m⁻¹ := inv_pos.2 hm
  unfold cSharp; positivity

theorem cSharp_eq (m : ℝ) : cSharp m = Step2MomentStep.cStep' m + m⁻¹ := by
  unfold cSharp Step2MomentStep.cStep'; ring

/-- **The arithmetic of (5.40)–(5.47) at the sharp threshold.**

This is `RBM.Step2MomentStep.phi_arith'` with exactly two changes:

* the near-field summand of (5.41) is the **integrated** quantity `qI`, with
  `qI ≤ 2 m⁻¹ R²` from `integral_driftNearInt_le`, in place of the separated
  `m⁻¹ R² q` with `q ≤ R²` — this is the change that removes the two powers;
* the a priori level of `J*` is `Λ = x⁸ R²`, not `x⁸ R⁴`.

Everything else is identical, **including the side conditions** `hA`, `hε`, `hβ`, `hγ`: the
exponent table of T174 does not move, so `RBM.Step2MomentStep.hbeta_of_reg` (`β* = 5.5`) and
`RBM.Step2MomentStep.hgamma_of_reg` (`β* = 4.5`) discharge `hβ` and `hγ` verbatim
(`sharp_side_conditions_of_reg`).  The conclusion is `cSharp m · x² **R²**`, strictly below
`Λ = x⁸ R²` once `cSharp m ≤ x⁶` (`phi_lt_threshold_sharp`). -/
theorem phi_arith_sharp {x R Ξ m A ε qI β γ J : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (_hΞ0 : 0 ≤ Ξ)
    (hΞ : Ξ ≤ x) (hm0 : 0 < m) (hA : x ^ 17 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε * x ^ 17 * R ^ 10 ≤ 1) (hqI0 : 0 ≤ qI) (hqI : qI ≤ 2 * m⁻¹ * R ^ 2)
    (hβ0 : 0 ≤ β) (hβ : β * (x ^ 8 * R ^ 2) ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ : γ * (x ^ 12 * R ^ 4) ≤ 1)
    (hJ0 : 0 ≤ J) (hJΛ : J ≤ x ^ 8 * R ^ 2) :
    x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * qI + x * m⁻¹ * R ^ 2 * (β * J + γ * (J * √J))) + x * (R ^ 2 + 1) + 1
      ≤ cSharp m * x ^ 2 * R ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hR610 : R ^ 6 ≤ R ^ 10 := pow_le_pow_right₀ hR (by norm_num)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hA6 : x ^ 17 * R ^ 6 ≤ A := by
    refine le_trans ?_ hA; gcongr
  have hxA : x ^ 17 * R ^ 6 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hA6
  -- `√J ≤ x⁴ R`
  have hsq : √J ≤ x ^ 4 * R := by
    have hsq' : (x ^ 4 * R) ^ 2 = x ^ 8 * R ^ 2 := by ring
    have := Real.sqrt_le_sqrt hJΛ
    rwa [← hsq', Real.sqrt_sq (by positivity)] at this
  have hsq0 : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hJJ : J * √J ≤ x ^ 12 * R ^ 3 := by
    calc J * √J ≤ (x ^ 8 * R ^ 2) * (x ^ 4 * R) :=
          mul_le_mul hJΛ hsq hsq0 (by positivity)
      _ = x ^ 12 * R ^ 3 := by ring
  -- the seven terms
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 2 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
  have t2 : Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
      ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        = 36 * exp 1 * m⁻¹ * (Ξ * x ^ 16 * R ^ 6 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * x ^ 16 * R ^ 6 * A⁻¹) := by gcongr
      _ = 36 * exp 1 * m⁻¹ * (x ^ 17 * R ^ 6 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 2) := by gcongr
  have t3 : Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (R ^ 2 * ε)) ≤ exp 1 * (x ^ 2 * R ^ 2) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (R ^ 2 * ε))
        = exp 1 * (Ξ * x ^ 16 * R ^ 6 * ε) := by ring
      _ ≤ exp 1 * (x * x ^ 16 * R ^ 6 * ε) := by gcongr
      _ = exp 1 * (ε * x ^ 17 * R ^ 6) := by ring
      _ ≤ exp 1 * (ε * x ^ 17 * R ^ 10) := by gcongr
      _ ≤ exp 1 * 1 := by gcongr
      _ ≤ exp 1 * (x ^ 2 * R ^ 2) := by gcongr
  -- the near field: **integrated**, `qI ≤ 2 m⁻¹ R²`; this is the whole sharpening
  have t4 : Ξ * (x * qI) ≤ 2 * m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * qI) ≤ x * (x * (2 * m⁻¹ * R ^ 2)) := by gcongr
      _ = 2 * m⁻¹ * (x ^ 2 * R ^ 2) := by ring
  -- the leading far-field term: `β J*`, `β* = 5.5`, side condition unchanged
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (β * J)) ≤ m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (β * J))
        ≤ x * (x * m⁻¹ * R ^ 2 * (β * (x ^ 8 * R ^ 2))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) * (β * (x ^ 8 * R ^ 2)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 2) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) := mul_one _
  -- the subleading far-field term: `γ (J*)^{3/2}`, `β* = 4.5`, side condition unchanged
  have t6 : Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J))) ≤ m⁻¹ * (x ^ 2 * R ^ 2) := by
    have hγR : γ * (x ^ 12 * R ^ 3) ≤ 1 := by
      refine le_trans ?_ hγ
      have h34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
      have : (0 : ℝ) ≤ γ * x ^ 12 := by positivity
      nlinarith
    calc Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J)))
        ≤ x * (x * m⁻¹ * R ^ 2 * (γ * (x ^ 12 * R ^ 3))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) * (γ * (x ^ 12 * R ^ 3)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 2) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) := mul_one _
  have t7 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 2) := by nlinarith
  have hsplit : x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 *
        (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * qI + x * m⁻¹ * R ^ 2 * (β * J + γ * (J * √J))) + x * (R ^ 2 + 1) + 1
      = x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (x ^ 8 * R ^ 2) ^ 2 * (R ^ 2 * ε)) + Ξ * (x * qI)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * J)) + Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J)))
        + x * (R ^ 2 + 1) + 1 := by ring
  rw [hsplit, cSharp]
  nlinarith

/-- **The bootstrap closes at the sharp threshold**: the output `cSharp m · x² R²` of
`phi_arith_sharp` is below `Λ = x⁸ R²` as soon as `cSharp m ≤ x⁶`, i.e. `N^{3δ/4} ≥ cSharp m`
— the same margin `RBM.Step2MomentStep.phi_lt_threshold` gives at the blunt threshold, with
`cSharp m = cStep' m + m⁻¹` in place of `cStep' m`. -/
theorem phi_lt_threshold_sharp {x R m : ℝ} (hR : 1 ≤ R) (hxc : cSharp m ≤ x ^ 6) :
    cSharp m * x ^ 2 * R ^ 2 ≤ x ^ 8 * R ^ 2 := by
  have hR0 : (0 : ℝ) ≤ R ^ 2 := by positivity
  have hx2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have h : cSharp m * x ^ 2 ≤ x ^ 6 * x ^ 2 := by nlinarith
  calc cSharp m * x ^ 2 * R ^ 2 ≤ (x ^ 6 * x ^ 2) * R ^ 2 := by nlinarith
    _ = x ^ 8 * R ^ 2 := by ring

/-- **The near field of (5.41) feeds `phi_arith_sharp` with no slack.**  Instantiating
`phi_arith_sharp` on the flow — `R = η_s/η_v`, `m = Im m_E`, and `qI` the *actual* integral
`∫_s^v η_u^{-1}(η_u/η_v)²(η_s/η_u)^{3/2} du` — its near-field hypothesis is discharged by
`integral_driftNearInt_le` and nothing else.

This is the bridge that makes the sharpening real rather than a change of notation: the `R²`
on the right is produced by the integral of §1, not assumed. -/
theorem phi_arith_sharp_flow {E : ℝ} (hE : |E| < 2) {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1)
    {x Ξ A ε β γ J : ℝ} (hx : 1 ≤ x) (hΞ0 : 0 ≤ Ξ) (hΞ : Ξ ≤ x)
    (hA : x ^ 17 * (etaT E s / etaT E v) ^ 10 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε * x ^ 17 * (etaT E s / etaT E v) ^ 10 ≤ 1)
    (hβ0 : 0 ≤ β) (hβ : β * (x ^ 8 * (etaT E s / etaT E v) ^ 2) ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ : γ * (x ^ 12 * (etaT E s / etaT E v) ^ 4) ≤ 1)
    (hJ0 : 0 ≤ J) (hJΛ : J ≤ x ^ 8 * (etaT E s / etaT E v) ^ 2) :
    x * (etaT E s / etaT E v) ^ 2 * Ξ
      + Ξ * (exp 1 * (x ^ 8 * (etaT E s / etaT E v) ^ 2) ^ 2 *
            (36 * ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 2 * A⁻¹
              + (etaT E s / etaT E v) ^ 2 * ε)
          + x * (∫ u in s..v, driftNearInt E s v u)
          + x * ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 2 * (β * J + γ * (J * √J)))
      + x * ((etaT E s / etaT E v) ^ 2 + 1) + 1
      ≤ cSharp ((mE E).im) * x ^ 2 * (etaT E s / etaT E v) ^ 2 := by
  have hm := mE_im_pos hE
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hR1 : (1 : ℝ) ≤ etaT E s / etaT E v := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith), one_mul]; linarith
  have hqI0 : (0 : ℝ) ≤ ∫ u in s..v, driftNearInt E s v u := by
    refine intervalIntegral.integral_nonneg hsv fun u hu => ?_
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 hv1
    have := Step2.etaT_pos' hE hu1
    have := Step2.etaT_pos' hE hv1
    unfold driftNearInt; positivity
  exact phi_arith_sharp hx hR1 hΞ0 hΞ hm hA hε0 hε hqI0
    (integral_driftNearInt_le hE hsv hv1) hβ0 hβ hγ0 hγ hJ0 hJΛ

/-- **The second pass**: the sharp output `cSharp m · x² R²` already follows from the *blunt*
a priori level `J* ≤ Λ = x⁸ R⁴` — the one the repository has established
(`RBM.MomentDuhamelCut.jS_stochDom_cut`).  This is exactly the paper's move at (5.47): the
stopping time having been excluded, the one-step right-hand side is re-read and it is
`(η_s/η_t)² 1(·) + 1`, not `Λ`.  **No bootstrap is needed for it.**

Relative to `phi_arith_sharp` only the two far-field side conditions move, and only because
`J*` is now allowed to be `R²` larger: `hβ` from `β x⁸R² ≤ 1` (`β* = 5.5`) to `β x⁸R⁴ ≤ 1`
(`β* = 9.5`), `hγ` from `γ x¹²R⁴ ≤ 1` (`β* = 4.5`) to `γ x¹²R⁶ ≤ 1` (`β* = 6.5`).  Both are
still far below 30, and `second_pass_side_conditions_of_reg` discharges them from (2.72) with
a gain under **the same** `4δ ≤ 2c` as T132c. -/
theorem phi_arith_second_pass {x R Ξ m A ε qI β γ J : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R)
    (_hΞ0 : 0 ≤ Ξ) (hΞ : Ξ ≤ x) (hm0 : 0 < m) (hA : x ^ 17 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε * x ^ 17 * R ^ 10 ≤ 1) (hqI0 : 0 ≤ qI) (hqI : qI ≤ 2 * m⁻¹ * R ^ 2)
    (hβ0 : 0 ≤ β) (hβ : β * (x ^ 8 * R ^ 4) ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ : γ * (x ^ 12 * R ^ 6) ≤ 1)
    (hJ0 : 0 ≤ J) (hJΛ : J ≤ x ^ 8 * R ^ 4) :
    x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * qI + x * m⁻¹ * R ^ 2 * (β * J + γ * (J * √J))) + x * (R ^ 2 + 1) + 1
      ≤ cSharp m * x ^ 2 * R ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hxA : x ^ 17 * R ^ 10 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hA
  have hsq : √J ≤ x ^ 4 * R ^ 2 := by
    have hsq' : (x ^ 4 * R ^ 2) ^ 2 = x ^ 8 * R ^ 4 := by ring
    have := Real.sqrt_le_sqrt hJΛ
    rwa [← hsq', Real.sqrt_sq (by positivity)] at this
  have hsq0 : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hJJ : J * √J ≤ x ^ 12 * R ^ 6 := by
    calc J * √J ≤ (x ^ 8 * R ^ 4) * (x ^ 4 * R ^ 2) :=
          mul_le_mul hJΛ hsq hsq0 (by positivity)
      _ = x ^ 12 * R ^ 6 := by ring
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 2 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
  have t2 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
      ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        = 36 * exp 1 * m⁻¹ * (Ξ * x ^ 16 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * x ^ 16 * R ^ 10 * A⁻¹) := by gcongr
      _ = 36 * exp 1 * m⁻¹ * (x ^ 17 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 2) := by gcongr
  have t3 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) ≤ exp 1 * (x ^ 2 * R ^ 2) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        = exp 1 * (Ξ * x ^ 16 * R ^ 10 * ε) := by ring
      _ ≤ exp 1 * (x * x ^ 16 * R ^ 10 * ε) := by gcongr
      _ = exp 1 * (ε * x ^ 17 * R ^ 10) := by ring
      _ ≤ exp 1 * 1 := by gcongr
      _ ≤ exp 1 * (x ^ 2 * R ^ 2) := by gcongr
  have t4 : Ξ * (x * qI) ≤ 2 * m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * qI) ≤ x * (x * (2 * m⁻¹ * R ^ 2)) := by gcongr
      _ = 2 * m⁻¹ * (x ^ 2 * R ^ 2) := by ring
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (β * J)) ≤ m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (β * J))
        ≤ x * (x * m⁻¹ * R ^ 2 * (β * (x ^ 8 * R ^ 4))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) * (β * (x ^ 8 * R ^ 4)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 2) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) := mul_one _
  have t6 : Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J))) ≤ m⁻¹ * (x ^ 2 * R ^ 2) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J)))
        ≤ x * (x * m⁻¹ * R ^ 2 * (γ * (x ^ 12 * R ^ 6))) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) * (γ * (x ^ 12 * R ^ 6)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 2) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 2) := mul_one _
  have t7 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 2) := by nlinarith
  have hsplit : x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 *
        (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * qI + x * m⁻¹ * R ^ 2 * (β * J + γ * (J * √J))) + x * (R ^ 2 + 1) + 1
      = x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) + Ξ * (x * qI)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * J)) + Ξ * (x * m⁻¹ * R ^ 2 * (γ * (J * √J)))
        + x * (R ^ 2 + 1) + 1 := by ring
  rw [hsplit, cSharp]
  nlinarith

end Arith

/-! ### 2″. The second pass costs nothing in the exponent budget -/

section SecondPassExponents

variable {x R r A : ℝ}

/-- A uniform margin: under (2.72) with a gain (`N^c R^{30} ≤ A`) and `x = N^{δ/8}` with
`4δ ≤ 2c`, **every** monomial `x^j R^k` with `j ≤ 32` and `k ≤ 60` is below `A²`.  T132c's
`RBM.Step2MomentStep.beta_star_margin` is the case `(j,k) = (32,11)`; the second pass needs
`(32,19)` and `(24,13)`, both still inside the same budget. -/
theorem margin_of_reg {N c δ : ℝ} (hN : 1 ≤ N) (hR : 1 ≤ R) (hδ0 : 0 ≤ δ)
    (hδ : 4 * δ ≤ 2 * c) (hx : x = N ^ (δ / 8)) (hA0 : 0 < A) (hA : N ^ c * R ^ 30 ≤ A)
    {j k : ℕ} (hj : j ≤ 32) (hk : k ≤ 60) : x ^ j * R ^ k ≤ A ^ 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact Real.one_le_rpow hN (by linarith)
  have h1 : x ^ j * R ^ k ≤ x ^ 32 * R ^ 60 :=
    mul_le_mul (pow_le_pow_right₀ hx1 hj) (pow_le_pow_right₀ hR hk) (by positivity)
      (by positivity)
  have hx32 : x ^ 32 = N ^ (4 * δ) := by
    rw [hx, ← Real.rpow_natCast (N ^ (δ / 8)) 32, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hNc2 : (N ^ c) ^ 2 = N ^ (2 * c) := by
    rw [← Real.rpow_natCast (N ^ c) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have h2c : N ^ (4 * δ) ≤ N ^ (2 * c) := Real.rpow_le_rpow_of_exponent_le hN hδ
  have hAsq : (N ^ c * R ^ 30) ^ 2 ≤ A ^ 2 := by
    have h0 : (0 : ℝ) ≤ N ^ c * R ^ 30 := by positivity
    nlinarith
  refine h1.trans ?_
  calc x ^ 32 * R ^ 60 = N ^ (4 * δ) * R ^ 60 := by rw [hx32]
    _ ≤ N ^ (2 * c) * R ^ 60 := by gcongr
    _ = (N ^ c * R ^ 30) ^ 2 := by rw [mul_pow, hNc2]; ring
    _ ≤ A ^ 2 := hAsq

/-- **`β* = 9.5`** for the second pass: `β = r^{3/2}A^{-1/2}` with `β x⁸ R⁴ ≤ 1`, i.e.
`r³ x^{16} R⁸ ≤ A`; squaring and using `r⁶ ≤ R³` this needs `A² ≥ x^{32} R^{19}`. -/
theorem hbeta_second_of_reg (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R) (hA0 : 0 < A)
    (hA : x ^ 32 * R ^ 19 ≤ A ^ 2) : (r * √r * (√A)⁻¹) * (x ^ 8 * R ^ 4) ≤ 1 := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  set β : ℝ := r * √r * (√A)⁻¹ with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hβsq : β ^ 2 = r ^ 3 * A⁻¹ := by
    rw [hβdef, mul_pow, mul_pow, Real.sq_sqrt hr0, ← Real.sqrt_inv,
      Real.sq_sqrt (by positivity)]
    ring
  have h6 : (r ^ 3) ^ 2 ≤ R ^ 3 := by
    calc (r ^ 3) ^ 2 = (r ^ 2) ^ 3 := by ring
      _ ≤ R ^ 3 := by gcongr
  have hkey : r ^ 3 * (x ^ 16 * R ^ 8) ≤ A := by
    have hx0 : (0 : ℝ) ≤ x ^ 16 := by positivity
    have hlhs0 : (0 : ℝ) ≤ r ^ 3 * (x ^ 16 * R ^ 8) := by positivity
    have hsqle : (r ^ 3 * (x ^ 16 * R ^ 8)) ^ 2 ≤ A ^ 2 := by
      calc (r ^ 3 * (x ^ 16 * R ^ 8)) ^ 2 = (r ^ 3) ^ 2 * (x ^ 32 * R ^ 16) := by ring
        _ ≤ R ^ 3 * (x ^ 32 * R ^ 16) := by gcongr
        _ = x ^ 32 * R ^ 19 := by ring
        _ ≤ A ^ 2 := hA
    nlinarith [hA0.le, hlhs0]
  have hsq : (β * (x ^ 8 * R ^ 4)) ^ 2 ≤ 1 := by
    have heq : (β * (x ^ 8 * R ^ 4)) ^ 2 = (r ^ 3 * A⁻¹) * (x ^ 16 * R ^ 8) := by
      rw [mul_pow, hβsq]; ring
    rw [heq, mul_comm (r ^ 3) A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
    exact hkey
  nlinarith [mul_nonneg hβ0 (by positivity : (0 : ℝ) ≤ x ^ 8 * R ^ 4)]

/-- **`β* = 6.5`** for the second pass: `γ = r A^{-1}` with `γ x¹² R⁶ ≤ 1`, i.e.
`r x¹² R⁶ ≤ A`; squaring and using `r² ≤ R` this needs `A² ≥ x^{24} R^{13}`. -/
theorem hgamma_second_of_reg (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R) (hA0 : 0 < A)
    (hA : x ^ 24 * R ^ 13 ≤ A ^ 2) : (r * A⁻¹) * (x ^ 12 * R ^ 6) ≤ 1 := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hkey : r * (x ^ 12 * R ^ 6) ≤ A := by
    have hlhs0 : (0 : ℝ) ≤ r * (x ^ 12 * R ^ 6) := by positivity
    have hsqle : (r * (x ^ 12 * R ^ 6)) ^ 2 ≤ A ^ 2 := by
      calc (r * (x ^ 12 * R ^ 6)) ^ 2 = r ^ 2 * (x ^ 24 * R ^ 12) := by ring
        _ ≤ R * (x ^ 24 * R ^ 12) := by gcongr
        _ = x ^ 24 * R ^ 13 := by ring
        _ ≤ A ^ 2 := hA
    nlinarith [hA0.le, hlhs0]
  rw [mul_comm r A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
  exact hkey

end SecondPassExponents

/-! ### 2′. The exponent table does not move -/

section Exponents

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s : ℕ → ℝ}

/-- **The sharpening is free in the exponent budget.**  The two side conditions of
`phi_arith_sharp` that carry exponents are *literally* those of
`RBM.Step2MomentStep.phi_arith'`, so `RBM.Step2MomentStep.side_conditions_of_reg` discharges
them unchanged: the bottleneck stays `β* = 5.5 < 30` and (2.72)'s exponent is untouched.

The near-field row is the only one that changes, and it changes **downwards**: T132c's
`q ≤ R²` (its `β* = 4`, with zero margin) becomes `qI ≤ 2 m⁻¹ R²`
(`integral_driftNearInt_le`, `β* = 2`). -/
theorem sharp_side_conditions_of_reg (hE : |E| < 2) {N : ℕ} {u : ℝ} (hs0 : 0 ≤ s N)
    (hsu : s N ≤ u) (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    (hN1 : 1 ≤ (N : ℝ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u) :
    ((B.ell N u / B.ell N (s N)) * √(B.ell N u / B.ell N (s N)) *
          (√(B.scale E N u))⁻¹) *
          (((N : ℝ) ^ (δ / 8)) ^ 8 * (etaT E (s N) / etaT E u) ^ 2) ≤ 1 ∧
      ((B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹) *
          (((N : ℝ) ^ (δ / 8)) ^ 12 * (etaT E (s N) / etaT E u) ^ 4) ≤ 1 :=
  ⟨(Step2MomentStep.side_conditions_of_reg hE hs0 hsu hu1 hδ0 hδ hN1 hA).2.1,
    (Step2MomentStep.side_conditions_of_reg hE hs0 hsu hu1 hδ0 hδ hN1 hA).2.2⟩

/-- **The second pass is free too.**  The two side conditions of `phi_arith_second_pass`
(`β* = 9.5`, `β* = 6.5`) are discharged on the flow from (2.72) with a gain under exactly the
same margin `4δ ≤ 2c` that T132c already assumes — `margin_of_reg` covers every exponent up to
`x^{32} R^{60}`, and the second pass only reaches `x^{32} R^{19}`.

Consequence: **reading (5.47) at `(η_s/η_u)²` instead of `(η_s/η_u)⁴` costs nothing at all in
the exponent budget of Theorem 2.21.** -/
theorem second_pass_side_conditions_of_reg (hE : |E| < 2) {N : ℕ} {u : ℝ} (hs0 : 0 ≤ s N)
    (hsu : s N ≤ u) (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    (hN1 : 1 ≤ (N : ℝ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u) :
    ((B.ell N u / B.ell N (s N)) * √(B.ell N u / B.ell N (s N)) *
          (√(B.scale E N u))⁻¹) *
          (((N : ℝ) ^ (δ / 8)) ^ 8 * (etaT E (s N) / etaT E u) ^ 4) ≤ 1 ∧
      ((B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹) *
          (((N : ℝ) ^ (δ / 8)) ^ 12 * (etaT E (s N) / etaT E u) ^ 6) ≤ 1 := by
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
  have hA0 : 0 < B.scale E N u := B.scale_pos' hE N (hs0.trans hsu) hu1
  have h19 := margin_of_reg (x := (N : ℝ) ^ (δ / 8)) (R := etaT E (s N) / etaT E u)
    (A := B.scale E N u) hN1 hR1 hδ0 hδ rfl hA0 hA (j := 32) (k := 19)
    (by norm_num) (by norm_num)
  have h13 := margin_of_reg (x := (N : ℝ) ^ (δ / 8)) (R := etaT E (s N) / etaT E u)
    (A := B.scale E N u) hN1 hR1 hδ0 hδ rfl hA0 hA (j := 24) (k := 13)
    (by norm_num) (by norm_num)
  exact ⟨hbeta_second_of_reg hR1 hr0 hr hA0 h19, hgamma_second_of_reg hR1 hr0 hr hA0 h13⟩

end Exponents

/-! ### 3. (5.47) sharp: `J*_{u,D} ≺ (η_s/η_u)²` -/

section Sharp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- `J*_{u,D}` normalized by the **sharp** weight `(η_s/η_u)²` of (5.47), the analogue of
`RBM.Step2Moment.jSnorm` (which uses the a priori weight `(η_s/η_u)⁴` of (5.29)/(5.43)). -/
noncomputable def jSnorm2 (X : Sample B) (E D : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  Step2.jS X E D N u ω / Step2Moment.ratR E s N u ^ 2

variable (X : Sample B) {D : ℝ}

/-- At the left endpoint the two normalizations coincide, because `R_{s} = 1`. -/
theorem ratR_left (hE : |E| < 2) {N : ℕ} (hs1 : s N < 1) : Step2Moment.ratR E s N (s N) = 1 :=
  div_self (Step2.etaT_pos' hE hs1).ne'

/-- **The initial condition is not strengthened.**  At `u = s_N` the sharp normalization is
`J*_{s,D}` itself, exactly as `RBM.Step2Moment.jSnorm` is: so `MomentHypCutSharp.init` is
literally `RBM.MomentDuhamelCut.MomentHypCut.init`, i.e. (2.68)/(2.69), unchanged. -/
theorem jSnorm2_left (hE : |E| < 2) {N : ℕ} (hs1 : s N < 1) (ω : Ω) :
    jSnorm2 X E D s N (s N) ω = Step2Moment.jSnorm X E D s N (s N) ω := by
  rw [jSnorm2, Step2Moment.jSnorm, ratR_left (s := s) hE hs1]
  norm_num

/-- **What the sharp interface really assumes.**  `jSnorm ≤ jSnorm2` (since `R ≥ 1`), so a
`CutHyp` on `jSnorm2` at level `1` is a *strictly stronger* hypothesis than T197's one on
`jSnorm` — the sharpening is an assumption about the one-step moment bound, not a free
consequence.  §2 is what makes it a *legitimate* assumption: the arithmetic closes at the
sharp threshold with the same exponent budget. -/
theorem jSnorm_le_jSnorm2 (hE : |E| < 2) {N : ℕ} (hs1 : s N < 1) {u : ℝ} (hu1 : u < 1)
    (hsu : s N ≤ u) (ω : Ω) :
    Step2Moment.jSnorm X E D s N u ω ≤ jSnorm2 X E D s N u ω := by
  have hR0 : 0 < Step2Moment.ratR E s N u := Step2Moment.ratR_pos hE hs1 hu1
  have hR1 : (1 : ℝ) ≤ Step2Moment.ratR E s N u := by
    rw [Step2Moment.ratR, Step2.etaT_ratio hE, le_div_iff₀ (by linarith), one_mul]
    linarith
  have hJ0 : 0 ≤ Step2.jS X E D N u ω := by
    linarith [Step2Moment.one_le_jS X (E := E) (D := D) N u ω]
  have hp2 : 0 < Step2Moment.ratR E s N u ^ 2 := pow_pos hR0 2
  have h24 : Step2Moment.ratR E s N u ^ 2 ≤ Step2Moment.ratR E s N u ^ 4 :=
    pow_le_pow_right₀ hR1 (by norm_num)
  rw [Step2Moment.jSnorm, jSnorm2, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hp2 h24) hJ0

/-- **The sharp replacement for `RBM.MomentDuhamelCut.MomentHypCut`.**

Identical to it field for field, with `RBM.Step2Moment.jSnorm` (weight `(η_s/η_u)⁴`) replaced
by `jSnorm2` (weight `(η_s/η_u)²`).  `init` is *the same statement* — `jSnorm2_left`. -/
structure MomentHypCutSharp (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- The truncated moment Duhamel for the sharply normalized `J*_{u,D}`, threshold `1`. -/
  cut : MomentDuhamelCut.CutHyp B.P (fun N u ω => jSnorm2 X E D s N u ω) s t (fun _ => 1)
  /-- **(2.69)**: the initial bound `J*_{s,D} ≺ 1`. -/
  init : StochDom B.P (fun N (_ : Unit) ω => jSnorm2 X E D s N (s N) ω)
    (fun _ _ _ => (1 : ℝ))

/-- `J*_{u,D}/(η_s/η_u)² ≺ 1`, uniformly in `u ∈ [s, t]`. -/
theorem stochDom_jSnorm2_cut (Hy : MomentHypCutSharp X E s t D) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => jSnorm2 X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  have := B.isProbabilityMeasure
  exact MomentDuhamelCut.stochDom_of_cutHyp Hy.cut
    (Filter.Eventually.of_forall fun _ => le_rfl) Hy.init

/-- **(5.47), sharp**: `J*_{u,D} ≺ (η_s/η_u)²`, uniformly in `u ∈ [s, t]` — the paper's
`J*_{τ,D} ≺ (η_s/η_t)²`, read on every sub-window `[s,u]` (`T207a`). -/
theorem jS_stochDom_sharp (Hy : MomentHypCutSharp X E s t D) (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2) := by
  refine StochDom.of_subset (stochDom_jSnorm2_cut X Hy) fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N (u : ℝ) ^ 2 :=
    pow_pos (Step2Moment.ratR_pos hE hs1 (u.2.2.trans_lt (ht1 N))) 2
  change (N : ℝ) ^ τ * 1 < Step2.jS X E D N (u : ℝ) ω / Step2Moment.ratR E s N (u : ℝ) ^ 2
  rw [mul_one, lt_div_iff₀ hR]
  exact hu

/-- **Nothing downstream is lost.**  The sharp (5.47) implies the blunt one *verbatim* — the
conclusion of `RBM.Step2Moment.jS_stochDom` and `RBM.MomentDuhamelCut.jS_stochDom_cut` — so
every existing consumer (in particular `RBM.Step2Moment.aprioriDecay_of_jS`, i.e. (2.76)) can
be fed from `MomentHypCutSharp` alone. -/
theorem jS_stochDom_of_sharp (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (h : StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2)) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 4) := by
  refine StochDom.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR1 : (1 : ℝ) ≤ etaT E (s N) / etaT E (u : ℝ) := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith [u.2.2.trans_lt (ht1 N)]), one_mul]
    linarith [u.2.1]
  have h24 : (etaT E (s N) / etaT E (u : ℝ)) ^ 2 ≤ (etaT E (s N) / etaT E (u : ℝ)) ^ 4 :=
    pow_le_pow_right₀ hR1 (by norm_num)
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc (N : ℝ) ^ τ * (etaT E (s N) / etaT E (u : ℝ)) ^ 2
      ≤ (N : ℝ) ^ τ * (etaT E (s N) / etaT E (u : ℝ)) ^ 4 := by gcongr
    _ < Step2.jS X E D N (u : ℝ) ω := hu

end Sharp

/-! ### 4. `hnear`: the near half of (5.48) -/

section Hnear

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- **From (5.47) to the near half of (5.48).**  `J*_{u,D} ≺ (η_s/η_u)²` gives
`|(L-K)_{u,(+,-),a}| ≺ (η_s/η_u)² T_{u,D}(‖a₁-a₂‖)` by the definitional content (5.31) of
`J*` (`RBM.Step2.le_jStar_mul`).  This is exactly the `hnear` slot of
`RBM.Step2MomentStep.flowEq548_of_near_far` and
`RBM.Step2MomentStep.flowEq548_of_near_farInputs`. -/
theorem hnear_of_jS
    (hJ : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))) := by
  intro D hD
  have hW0 : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have hJD := (hJ D hD).precomp_param
    (V := fun N => TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) fun N p => p.1
  have hT0 : ∀ N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω),
      0 ≤ Step2.tT B E N D p.1 (zdist (B.L N) (p.2.1 - p.2.2)) :=
    fun N p _ => tailT_nonneg (hW0 N).le _
  have hR0 : ∀ N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω),
      0 ≤ (etaT E (s N) / etaT E p.1) ^ 2 := fun N p _ => by positivity
  have hmul := StochDom.mul hT0 hR0 hJD (StochDom.refl hT0)
  refine StochDom.of_le_left (fun N p ω => ?_) hmul
  simp only [Pi.mul_apply]
  have h := Step2.le_jStar_mul (f := fun b => ‖Step2.lk X E N p.1 ω b‖) (ℓu := B.ell N p.1)
    (ηu := etaT E p.1) (D := D) (hW0 N) ![p.2.1, p.2.2]
  rw [Step2.norm_lk_eq] at h
  simpa [Step2.jS, Step2.tT] using h

/-- **`hnear`, from the sharp interface.** -/
theorem hnear_sharp (Hy : ∀ D : ℝ, 0 < D → MomentHypCutSharp X E s t D) (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))) :=
  hnear_of_jS X fun D hD => jS_stochDom_sharp X (Hy D hD) hE hst ht1

/-- **(5.48) with both halves in place.**  `RBM.Step45.FlowEq548` from `MomentHypCutSharp`
(the near half, this file) and T198's `FarInputs` (the far half). -/
theorem flowEq548_of_sharp_farInputs (Hy : ∀ D : ℝ, 0 < D → MomentHypCutSharp X E s t D)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {Mi Mn Mf Mm : ℝ → ℕ → ℝ}
    (hMi : ∀ D' N, 0 ≤ Mi D' N) (hMn : ∀ D' N, 0 ≤ Mn D' N) (hMf : ∀ D' N, 0 ≤ Mf D' N)
    (hMm : ∀ D' N, 0 ≤ Mm D' N)
    (hpoly : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      Step2MomentStep.cFarStep B E (Mi D') (Mf D') (Mm D') N ≤ (N : ℝ) ^ τ)
    (hHP : ∀ D' : ℝ, HighProb B.P
      (fun N => {ω | Step2MomentStep.FarInputs X E s t D' (Mi D') (Mn D') (Mf D') (Mm D')
        N ω}))
    (hres : ∀ D : ℝ, 0 < D → ∃ D' : ℝ, D ≤ D' ∧ ∀ᶠ N : ℕ in atTop,
      exp 1 ≤ (B.W N : ℝ) ∧
        Step2MomentStep.FarResidue B E s t D D' (Mi D') (Mn D') (Mf D') N) :
    Step45.FlowEq548 X E s t :=
  Step2MomentStep.flowEq548_of_near_farInputs X hE hs0 hst ht1 hMi hMn hMf hMm hpoly hHP hres
    (hnear_sharp X Hy hE hst ht1)

/-- **(2.76) from the same interface.**  `RBM.Step2Moment.aprioriDecay_of_jS` fed by
`jS_stochDom_of_sharp`: one hypothesis bundle, both the a priori decay and `hnear`. -/
theorem aprioriDecay_of_sharp (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCutSharp X E s t D)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  Step2Moment.aprioriDecay_of_jS X hE hs0 hst ht1 hc0 hreg
    fun D hD => jS_stochDom_of_sharp X hE hst ht1 (jS_stochDom_sharp X (Hy D hD) hE hst ht1)

end Hnear

/-! ### 5. Satisfiability witnesses (compiled) -/

section Sat

/-- The hypotheses of `phi_arith_sharp` are **jointly satisfiable** and its conclusion is not
vacuous: take `x = R = Ξ = m = A = 1`, `ε = qI = β = γ = J = 0`.  (The degenerate window
`η_s = η_t`, i.e. `R = 1`, is included.) -/
theorem sat_phi_arith_sharp :
    (1 : ℝ) * 1 ^ 2 * 1 + 1 * (exp 1 * (1 ^ 8 * 1 ^ 2) ^ 2 * (36 * (1 : ℝ)⁻¹ * 1 ^ 2 * 1⁻¹
        + 1 ^ 2 * 0) + 1 * 0 + 1 * (1 : ℝ)⁻¹ * 1 ^ 2 * (0 * 0 + 0 * (0 * √0)))
      + 1 * (1 ^ 2 + 1) + 1 ≤ cSharp 1 * 1 ^ 2 * 1 ^ 2 :=
  phi_arith_sharp le_rfl le_rfl zero_le_one le_rfl one_pos (by norm_num) le_rfl (by norm_num)
    le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num)

/-- The hypotheses of `phi_arith_second_pass` are **jointly satisfiable** and its conclusion
is not vacuous, at the same degenerate point as `sat_phi_arith_sharp`. -/
theorem sat_phi_arith_second_pass :
    (1 : ℝ) * 1 ^ 2 * 1 + 1 * (exp 1 * (1 ^ 8 * 1 ^ 4) ^ 2 * (36 * (1 : ℝ)⁻¹ * 1 ^ 2 * 1⁻¹
        + 1 ^ 2 * 0) + 1 * 0 + 1 * (1 : ℝ)⁻¹ * 1 ^ 2 * (0 * 0 + 0 * (0 * √0)))
      + 1 * (1 ^ 2 + 1) + 1 ≤ cSharp 1 * 1 ^ 2 * 1 ^ 2 :=
  phi_arith_second_pass le_rfl le_rfl zero_le_one le_rfl one_pos (by norm_num) le_rfl
    (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    (by norm_num)

/-- **The near-field hypothesis of `phi_arith_sharp` is met by the real integral, not by
fiat**: `phi_arith_sharp_flow` takes `qI` to be `∫_s^v driftNearInt` itself.  Here is the
degenerate end of that: at `s = v` the integral is `0` and the bound still holds, so the
hypothesis bundle is non-empty at the window's collapse as well. -/
theorem sat_hqI_flow {E : ℝ} (hE : |E| < 2) {s : ℝ} (hs1 : s < 1) :
    (∫ u in s..s, driftNearInt E s s u) ≤ 2 * ((mE E).im)⁻¹ * (etaT E s / etaT E s) ^ 2 :=
  integral_driftNearInt_le hE le_rfl hs1

/-- **The two far-field side conditions are sharp at `r = R = x = A = 1`** — unchanged from
T132c, which is the point: the sharpening did not spend any of their margin. -/
theorem sat_hbeta_sharp : ((1 : ℝ) * √1 * (√(1 : ℝ))⁻¹) * (1 ^ 8 * 1 ^ 2) ≤ 1 := by
  rw [Real.sqrt_one]; norm_num

theorem sat_hgamma_sharp : ((1 : ℝ) * (1 : ℝ)⁻¹) * (1 ^ 12 * 1 ^ 4) ≤ 1 := by norm_num

/-- The near-field integrand is **strictly positive**, so `integral_driftNearInt_le` is not
met by a vanishing integrand. -/
theorem driftNearInt_pos {E : ℝ} (hE : |E| < 2) {s v u : ℝ} (hs1 : s < 1) (hu1 : u < 1)
    (hv1 : v < 1) : 0 < driftNearInt E s v u := by
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hb : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hs : 0 < √(etaT E s / etaT E u) := Real.sqrt_pos.2 (div_pos ha hb)
  unfold driftNearInt; positivity

/-- **The separated route is provably over budget.**  `sup_mul_len_driftNearInt_eq` says the
separated bound for (5.41)'s near field is `(Im m)^{-1} R² √R`; `integral_driftNearInt_le` says
the joint one is at most `2 (Im m)^{-1} R²`.  As soon as `R = η_s/η_v > 4` the former is
**strictly larger** — so the two powers T132c's `phi_arith'` pays are not an artifact of the
bookkeeping here, they are really spent. -/
theorem crude_exceeds_budget {E : ℝ} (hE : |E| < 2) {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1)
    (hR4 : 4 < etaT E s / etaT E v) :
    2 * ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 2 < driftNearInt E s v v * (1 - s) := by
  have hm := mE_im_pos hE
  have hs1 : s < 1 := hsv.trans_lt hv1
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hR0 : (0 : ℝ) < etaT E s / etaT E v := div_pos ha hc
  have h2 : (2 : ℝ) < √(etaT E s / etaT E v) := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num
    calc (2 : ℝ) = √(4 : ℝ) := h4.symm
      _ < √(etaT E s / etaT E v) := Real.sqrt_lt_sqrt (by norm_num) hR4
  rw [sup_mul_len_driftNearInt_eq hE hsv hv1]
  have hpos : (0 : ℝ) < ((mE E).im)⁻¹ * (etaT E s / etaT E v) ^ 2 := by positivity
  nlinarith

/-- **The sharpening is a strict gain wherever the window is non-degenerate**: for `R > 1` the
sharp majorant `R²` is strictly below the blunt `R⁴`.  (At `R = 1`, i.e. `s = t`, they agree —
which is why `jSnorm2_left` shows the initial condition is untouched.) -/
theorem sharp_lt_blunt {R : ℝ} (hR : 1 < R) : R ^ 2 < R ^ 4 := by
  have h0 : (0 : ℝ) < R := by linarith
  nlinarith [sq_nonneg R, sq_nonneg (R - 1)]

/-- The interface-level witness for `MomentHypCutSharp.cut`: `RBM.MomentDuhamelCut.CutHyp` is
parametric in the functional, so T197's witness `RBM.MomentDuhamelCut.satCutHyp` — a complete
instance at the critical scaling `J ≡ Θ`, with `mesh_fine` at equality — applies to the sharp
normalization verbatim.  (A witness at the level of an actual Gaussian `Sample` is the same
open problem as for `RBM.MomentDuhamelCut.MomentHypCut`; see the file header.) -/
theorem sat_cutHyp_sharp_shape {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    Nonempty (MomentDuhamelCut.CutHyp P (fun _ _ (_ : Ω) => (1 : ℝ)) (fun _ => 0)
      (fun _ => 1) (fun _ => 1)) :=
  ⟨MomentDuhamelCut.satCutHyp P⟩

end Sat

end Step2Near47

end RBM

