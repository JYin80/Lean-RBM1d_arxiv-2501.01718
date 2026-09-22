/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.FDeriv.Norm
import RBM1D.Gauss.APrimeTestFun

/-!
# The `BddC2C` instance for the loop ratio of route (A′) (T255)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.47) — the analytic side of Step 2's first bootstrap pass.

`RBM1D/Gauss/APrimeTestFun.lean` (T250) reduced the `RBM.Gauss.TestFun` hypothesis of route
(A′) to one `RBM.Gauss.BddC2C` for the polynomial `∑_i ρ_i^{2r}` built from the ratios of
(5.29),

  `ρ_{(j,a)}(M) = ‖(L − K)_{u_j,(+,−),a}(M)‖ / (Θ_N · T_{u_j,D}(a))`,

and recorded that the model-level instance was missing.  This file supplies it.

## ⚠ `BddC2C ρ` is false; `BddC2C (ρ^{2r})` is what is needed and true

The ticket asked for `BddC2C (ρ i)` followed by `RBM.Gauss.bddC2C_pow_real`.  That first step
is **refutable**: `z ↦ ‖z‖` is not differentiable at the origin
(`RBM.Gauss.not_bddC2C_norm_div`), and the origin is attained — it is `L = K`, the very
configuration at which T250 refuted the multiplicative derivative bound
(`RBM.Gauss.not_coordD1_le_mul_norm`).  Nothing is lost: `RBM.Gauss.testFun_softW_mul`
consumes `BddC2C (fun M => ∑ i ∈ S, ρ i M ^ (2r))` and never `BddC2C (ρ i)`, and the *even*
power is smooth because `‖z‖^{2r} = (z.re² + z.im²)^r` is a polynomial in `(Re z, Im z)`.

## Main results

* `RBM.Gauss.bddC2C_normSq`, `RBM.Gauss.bddC2C_norm_pow` — `‖F‖²` and `‖F‖^{2r}` are `C²`
  with explicit constants whenever `F` is.
* `RBM.Gauss.bddC2C_div_const`, `RBM.Gauss.bddC2C_ratio_pow_of_le` — **甲**: the ratio to the
  `2r`-th power, with constants depending on the denominator only through a **floor** `T₀`,
  so a whole family shares them.
* `RBM.Gauss.not_bddC2C_norm_div` — the compiled refutation of the un-powered shape.
* `RBM.Gauss.norm_fderiv_normSq_le`, `RBM.Gauss.norm_fderiv_ratio_pow_le`,
  `RBM.Gauss.norm_fderiv_sum_ratio_pow_le` — **the sharp gradient, free of `card S`**:
  `‖D(∑_i ρ_i^{2r})‖ ≤ 2r · card^{1/(2r)} · (∑_i ρ_i^{2r})^{1−1/(2r)} · (b₁/T₀)`.  The
  `RBM.Gauss.BddC2C` constant of the same polynomial carries a full factor `card S`; this is
  the model-side input of `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` at `Λ = 0`, and it
  is the entire gain of the soft maximum over the product weight of §4.
* `RBM.Gauss.testFun_softW_ratio`, `RBM.Gauss.testFun_softW_lkRatio` — the
  `RBM.Gauss.TestFun` of route (A′) on the model's ratios, with the tail function `T_{u,D}`
  of (5.27) in the denominator and the floor `Θ_N · W^{-D}` of `RBM.rpow_neg_le_tailT`.
* `RBM.Gauss.hasDerivAt_integral_softW_lkRatio` — step 4 of the (A′) chain: the generator
  identity `RBM.Gauss.hasDerivAt_integral_Phi` applied to the (A′) integrand, on the full
  measure.
* `RBM.Gauss.sat_testFun_softW_lkRatio` — a compiled satisfiability witness with a genuine
  two-edge `(+,−)` loop as numerator.

## What the constants depend on

`b₀ = card(Idx) · Bⁿ + Kb`, `b₁ = card(Idx) · n Bⁿ`, `b₂ = card(Idx) · n² Bⁿ` with
`B = 2(1 + η_u⁻¹)³` (`RBM.Gauss.bddC2C_loopObs`), and `T₀ = Θ_N · W^{-D}`.  All are finite,
explicit, and independent of the quantity being estimated.
-/

namespace RBM

open Cutoff MomentDuhamelCut

open scoped Matrix.Norms.L2Operator

namespace Gauss

open Matrix Step2Bootstrap

section Ratio

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `‖F‖²` is `C²` with explicit constants whenever `F` is. -/
theorem bddC2C_normSq {F : E → ℂ} {b₀ b₁ b₂ : ℝ} (hF : BddC2C F b₀ b₁ b₂) :
    BddC2C (fun M => ‖F M‖ ^ 2) (b₀ ^ 2) (4 * (b₀ * b₁)) (4 * (b₀ * b₂) + 4 * (b₁ * b₁)) := by
  have hreN : ‖Complex.reCLM‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  have himN : ‖Complex.imCLM‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm z
  have hre : BddC2C (fun M => (F M).re) b₀ b₁ b₂ :=
    (bddC2C_clm_comp Complex.reCLM hF).mono
      (mul_le_of_le_one_left hF.nonneg₀ hreN) (mul_le_of_le_one_left hF.nonneg₁ hreN)
      (mul_le_of_le_one_left hF.nonneg₂ hreN)
  have him : BddC2C (fun M => (F M).im) b₀ b₁ b₂ :=
    (bddC2C_clm_comp Complex.imCLM hF).mono
      (mul_le_of_le_one_left hF.nonneg₀ himN) (mul_le_of_le_one_left hF.nonneg₁ himN)
      (mul_le_of_le_one_left hF.nonneg₂ himN)
  have hsq := bddC2C_add (bddC2C_mul_real hre hre) (bddC2C_mul_real him him)
  have hfun : (fun M => ‖F M‖ ^ 2)
      = fun M => (F M).re * (F M).re + (F M).im * (F M).im := by
    funext M
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hfun]
  refine ⟨hsq.contDiff, ?_, ?_, ?_⟩
  · intro M
    have h := hF.bdd₀ M
    have : ‖F M‖ ^ 2 ≤ b₀ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg (F M)) h 2
      simpa using this
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at this
    exact this
  · intro M
    refine (hsq.bdd₁ M).trans (le_of_eq ?_); ring
  · intro M
    refine (hsq.bdd₂ M).trans (le_of_eq ?_); ring

/-- Multiplying by a non-negative constant scales all three constants. -/
theorem bddC2C_const_mul_real {F : E → ℝ} {a₀ a₁ a₂ c : ℝ} (hc : 0 ≤ c)
    (hF : BddC2C F a₀ a₁ a₂) :
    BddC2C (fun M => c * F M) (c * a₀) (c * a₁) (c * a₂) := by
  have h := bddC2C_mul_real (bddC2C_const (E := E) (c : ℝ)) hF
  refine h.mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_) <;>
    (rw [Real.norm_eq_abs, abs_of_nonneg hc]; try ring)

/-- **⭐ The `2r`-th power of the loop ratio `ρ = ‖F‖ / T` is `C²` with explicit constants.**

⚠ `BddC2C (fun M => ‖F M‖ / T)` itself is *false* whenever `F` has a zero with a non-zero
differential (`RBM.Gauss.not_bddC2C_norm_div`), and `F = (L-K)` does: `L = K` is in the
domain.  The even power is what route (A′) needs — `RBM.Gauss.testFun_softW_mul` consumes
`BddC2C (fun M => ∑ i, ρ i M ^ (2r))`, never `BddC2C (ρ i)` — and it is smooth because
`‖z‖^{2r} = (z.re² + z.im²)^r` is a polynomial in `(Re z, Im z)`. -/
theorem bddC2C_ratio_pow {F : E → ℂ} {b₀ b₁ b₂ T : ℝ} (hT : T ≠ 0)
    (hF : BddC2C F b₀ b₁ b₂) (r : ℕ) :
    BddC2C (fun M => (‖F M‖ / T) ^ (2 * r))
      ((b₀ ^ 2 / T ^ 2) ^ r)
      ((r : ℝ) * (b₀ ^ 2 / T ^ 2) ^ (r - 1) * (4 * (b₀ * b₁) / T ^ 2))
      (((r : ℝ) * ((r : ℝ) - 1) * (b₀ ^ 2 / T ^ 2) ^ (r - 2)) *
          ((4 * (b₀ * b₁) / T ^ 2) * (4 * (b₀ * b₁) / T ^ 2))
        + ((r : ℝ) * (b₀ ^ 2 / T ^ 2) ^ (r - 1)) *
          ((4 * (b₀ * b₂) + 4 * (b₁ * b₁)) / T ^ 2)) := by
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hinv : (0 : ℝ) ≤ (T ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hT2)
  have hG : BddC2C (fun M => ‖F M‖ ^ 2 / T ^ 2)
      (b₀ ^ 2 / T ^ 2) (4 * (b₀ * b₁) / T ^ 2)
      ((4 * (b₀ * b₂) + 4 * (b₁ * b₁)) / T ^ 2) := by
    have h := bddC2C_const_mul_real hinv (bddC2C_normSq hF)
    have hfun : (fun M => ‖F M‖ ^ 2 / T ^ 2) = fun M => (T ^ 2)⁻¹ * ‖F M‖ ^ 2 := by
      funext M; rw [div_eq_inv_mul]
    rw [hfun]
    exact h.mono (le_of_eq (by rw [div_eq_inv_mul])) (le_of_eq (by rw [div_eq_inv_mul]))
      (le_of_eq (by rw [div_eq_inv_mul]))
  have hpow := bddC2C_pow_real hG r
  have hfun : (fun M => (‖F M‖ / T) ^ (2 * r)) = fun M => (‖F M‖ ^ 2 / T ^ 2) ^ r := by
    funext M; rw [pow_mul, div_pow]
  rw [hfun]
  exact hpow

/-- The even power of a norm, with no denominator: the `T = 1` case of
`RBM.Gauss.bddC2C_ratio_pow`. -/
theorem bddC2C_norm_pow {F : E → ℂ} {b₀ b₁ b₂ : ℝ} (hF : BddC2C F b₀ b₁ b₂) (r : ℕ) :
    BddC2C (fun M => ‖F M‖ ^ (2 * r))
      ((b₀ ^ 2) ^ r)
      ((r : ℝ) * (b₀ ^ 2) ^ (r - 1) * (4 * (b₀ * b₁)))
      (((r : ℝ) * ((r : ℝ) - 1) * (b₀ ^ 2) ^ (r - 2)) * ((4 * (b₀ * b₁)) * (4 * (b₀ * b₁)))
        + ((r : ℝ) * (b₀ ^ 2) ^ (r - 1)) * (4 * (b₀ * b₂) + 4 * (b₁ * b₁))) := by
  have hpow := bddC2C_pow_real (bddC2C_normSq hF) r
  have hfun : (fun M => ‖F M‖ ^ (2 * r)) = fun M => (‖F M‖ ^ 2) ^ r := by
    funext M; rw [pow_mul]
  rw [hfun]
  exact hpow

/-- Dividing a `ℂ`-valued functional by a real constant bounded below by `T₀ > 0`: all three
constants are divided by the **floor** `T₀`, which is what makes them uniform over a family of
denominators. -/
theorem bddC2C_div_const {F : E → ℂ} {b₀ b₁ b₂ T T₀ : ℝ} (hT₀ : 0 < T₀) (hT : T₀ ≤ T)
    (hF : BddC2C F b₀ b₁ b₂) :
    BddC2C (fun M => F M / (T : ℂ)) (b₀ / T₀) (b₁ / T₀) (b₂ / T₀) := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT₀ hT
  have hnorm : ‖ContinuousLinearMap.mul ℝ ℂ ((T : ℂ)⁻¹)‖ ≤ T₀⁻¹ := by
    refine (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ _).trans ?_
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
    simpa [one_div] using one_div_le_one_div_of_le hT₀ hT
  have h := bddC2C_clm_comp (ContinuousLinearMap.mul ℝ ℂ ((T : ℂ)⁻¹)) hF
  have hfun : (fun M => F M / (T : ℂ))
      = fun M => ContinuousLinearMap.mul ℝ ℂ ((T : ℂ)⁻¹) (F M) := by
    funext M; simp [div_eq_inv_mul]
  rw [hfun]
  refine h.mono ?_ ?_ ?_ <;>
    rw [div_eq_inv_mul] <;>
    exact mul_le_mul_of_nonneg_right hnorm (by
      first
        | exact hF.nonneg₀
        | exact hF.nonneg₁
        | exact hF.nonneg₂)

/-- **⭐ 甲: the `BddC2C` instance for the `2r`-th power of the loop ratio, with constants
uniform over the family.**  `ρ M = ‖F M‖ / T`, and the constants involve only the **floor**
`T₀ ≤ T` of the denominator, so a whole family of ratios shares them. -/
theorem bddC2C_ratio_pow_of_le {F : E → ℂ} {b₀ b₁ b₂ T T₀ : ℝ} (hT₀ : 0 < T₀) (hT : T₀ ≤ T)
    (hF : BddC2C F b₀ b₁ b₂) (r : ℕ) :
    BddC2C (fun M => (‖F M‖ / T) ^ (2 * r))
      (((b₀ / T₀) ^ 2) ^ r)
      ((r : ℝ) * ((b₀ / T₀) ^ 2) ^ (r - 1) * (4 * ((b₀ / T₀) * (b₁ / T₀))))
      (((r : ℝ) * ((r : ℝ) - 1) * ((b₀ / T₀) ^ 2) ^ (r - 2)) *
          ((4 * ((b₀ / T₀) * (b₁ / T₀))) * (4 * ((b₀ / T₀) * (b₁ / T₀))))
        + ((r : ℝ) * ((b₀ / T₀) ^ 2) ^ (r - 1)) *
          (4 * ((b₀ / T₀) * (b₂ / T₀)) + 4 * ((b₁ / T₀) * (b₁ / T₀)))) := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT₀ hT
  have hG := bddC2C_div_const hT₀ hT hF
  have hfun : (fun M => (‖F M‖ / T) ^ (2 * r)) = fun M => ‖F M / (T : ℂ)‖ ^ (2 * r) := by
    funext M
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
  rw [hfun]
  exact bddC2C_norm_pow hG r

/-- A finite sum of functionals sharing one triple of constants. -/
theorem bddC2C_sum_of_uniform {ι : Type*} (S : Finset ι) {f : ι → E → ℝ} {c₀ c₁ c₂ : ℝ}
    (h : ∀ i ∈ S, BddC2C (f i) c₀ c₁ c₂) :
    BddC2C (fun M => ∑ i ∈ S, f i M)
      ((S.card : ℝ) * c₀) ((S.card : ℝ) * c₁) ((S.card : ℝ) * c₂) := by
  have hsum := bddC2C_sum S (f := f) (c₀ := fun _ => c₀) (c₁ := fun _ => c₁)
    (c₂ := fun _ => c₂) h
  refine hsum.mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_) <;>
    rw [Finset.sum_const, nsmul_eq_mul]

end Ratio

/-! ### The refutation: the ratio itself is not `C¹` -/

section Refute

/-- **⚠ `BddC2C ρ` for the *un-powered* ratio `ρ = ‖F‖ / T` is refutable.**  Already for
`F = id` on `ℂ` the map `z ↦ ‖z‖ / T` fails to be differentiable at the origin, so no triple
of constants works.  For the loop ratio the origin is attained — it is `L = K`, the very
configuration `RBM.Gauss.not_coordD1_le_mul_norm` uses.  This is why T255 supplies
`BddC2C (fun M => ρ M ^ (2r))` directly instead of `BddC2C ρ` followed by
`RBM.Gauss.bddC2C_pow_real`: the even power is a polynomial in `(Re, Im)` and is smooth,
while the ratio is not. `RBM.Gauss.testFun_softW_mul` consumes only the former. -/
theorem not_bddC2C_norm_div {T : ℝ} (hT : T ≠ 0) (a₀ a₁ a₂ : ℝ) :
    ¬ BddC2C (fun z : ℂ => ‖z‖ / T) a₀ a₁ a₂ := by
  intro h
  refine not_differentiableAt_norm_zero (E := ℂ) ?_
  have hd : DifferentiableAt ℝ (fun z : ℂ => ‖z‖ / T) 0 := h.differentiable 0
  have := hd.mul_const T
  simpa [div_mul_cancel₀, hT] using this

end Refute


/-! ### The sharp gradient: no cardinality factor

The `RBM.Gauss.BddC2C` constant of the polynomial `Y = ∑_i ρ_i^{2r}` carries a factor
`card S` (`RBM.Gauss.bddC2C_sum_of_uniform`), which is exactly the loss route (A′) introduces
the soft maximum to avoid.  The bounds below are the sharp, pointwise ones: the gradient of
`Y` is controlled by `Y` itself with only `card^{1/(2r)}`, which
`RBM.Step2Bootstrap.rpow_card_le_exp_one` calibrates to `e` at `2r ≍ log N`.  They are the
model-side input of `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` (`Λ = 0`).
-/

section Sharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise gradient of `‖F‖²`: `2‖F M‖·b₁`, **linear in `‖F M‖`**, where
`RBM.Gauss.bddC2C_normSq` only gives the uniform `4 b₀ b₁`. -/
theorem norm_fderiv_normSq_le {F : E → ℂ} {b₀ b₁ b₂ : ℝ} (hF : BddC2C F b₀ b₁ b₂) (M : E) :
    ‖fderiv ℝ (fun M => ‖F M‖ ^ 2) M‖ ≤ 2 * ‖F M‖ * b₁ := by
  have hd : HasFDerivAt F (fderiv ℝ F M) M := (hF.differentiable M).hasFDerivAt
  have h := hd.norm_sq
  rw [h.fderiv]
  have h2 : ((2 : ℕ) • ((innerSL ℝ (F M)).comp (fderiv ℝ F M)))
      = (2 : ℝ) • ((innerSL ℝ (F M)).comp (fderiv ℝ F M)) := by
    rw [two_smul, two_smul]
  rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hcomp : ‖(innerSL ℝ (F M)).comp (fderiv ℝ F M)‖ ≤ ‖F M‖ * b₁ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul (le_of_eq (innerSL_apply_norm ℝ (F M))) (hF.bdd₁ M)
      (norm_nonneg _) (norm_nonneg _)
  calc (2 : ℝ) * ‖(innerSL ℝ (F M)).comp (fderiv ℝ F M)‖
      ≤ (2 : ℝ) * (‖F M‖ * b₁) := mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = 2 * ‖F M‖ * b₁ := by ring

/-- **⭐ The sharp per-index gradient**: `‖D(ρ^{2r})(M)‖ ≤ 2r · ρ(M)^{2r-1} · (b₁/T₀)`, i.e.
the affine hypothesis of `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` holds with
`Λ = 0` and `K = (b₁/T₀)`, with the formal derivative `ρ'` read off the polynomial. -/
theorem norm_fderiv_ratio_pow_le {F : E → ℂ} {b₀ b₁ b₂ T T₀ : ℝ} (hT₀ : 0 < T₀) (hT : T₀ ≤ T)
    (hF : BddC2C F b₀ b₁ b₂) {r : ℕ} (hr : 1 ≤ r) (M : E) :
    ‖fderiv ℝ (fun M => (‖F M‖ / T) ^ (2 * r)) M‖
      ≤ ((2 * r : ℕ) : ℝ) * (‖F M‖ / T) ^ (2 * r - 1) * (b₁ / T₀) := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT₀ hT
  have hG := bddC2C_div_const hT₀ hT hF
  have hGn : ∀ M : E, ‖F M / (T : ℂ)‖ = ‖F M‖ / T := fun M => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
  have hfun : (fun M => (‖F M‖ / T) ^ (2 * r))
      = fun M => (‖F M / (T : ℂ)‖ ^ 2) ^ r := by
    funext M; rw [hGn M, pow_mul]
  rw [hfun]
  have hd : HasFDerivAt (fun M => ‖F M / (T : ℂ)‖ ^ 2)
      (fderiv ℝ (fun M => ‖F M / (T : ℂ)‖ ^ 2) M) M :=
    ((bddC2C_normSq hG).differentiable M).hasFDerivAt
  have hp := hd.pow r
  rw [hp.fderiv]
  have hbase : ‖fderiv ℝ (fun M => ‖F M / (T : ℂ)‖ ^ 2) M‖ ≤ 2 * (‖F M‖ / T) * (b₁ / T₀) := by
    have := norm_fderiv_normSq_le hG M
    rwa [hGn M] at this
  have hx0 : (0 : ℝ) ≤ ‖F M‖ / T := div_nonneg (norm_nonneg _) hTpos.le
  have hsm : (r • (‖F M / (T : ℂ)‖ ^ 2) ^ (r - 1) : ℝ)
      = (r : ℝ) * ((‖F M‖ / T) ^ 2) ^ (r - 1) := by
    rw [hGn M, nsmul_eq_mul]
  rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexp : ((‖F M‖ / T) ^ 2) ^ (r - 1) * (‖F M‖ / T) = (‖F M‖ / T) ^ (2 * r - 1) := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  calc (r : ℝ) * ((‖F M‖ / T) ^ 2) ^ (r - 1) *
        ‖fderiv ℝ (fun M => ‖F M / (T : ℂ)‖ ^ 2) M‖
      ≤ (r : ℝ) * ((‖F M‖ / T) ^ 2) ^ (r - 1) * (2 * (‖F M‖ / T) * (b₁ / T₀)) := by
        refine mul_le_mul_of_nonneg_left hbase ?_
        positivity
    _ = ((2 * r : ℕ) : ℝ) * (((‖F M‖ / T) ^ 2) ^ (r - 1) * (‖F M‖ / T)) * (b₁ / T₀) := by
        push_cast; ring
    _ = ((2 * r : ℕ) : ℝ) * (‖F M‖ / T) ^ (2 * r - 1) * (b₁ / T₀) := by rw [hexp]

/-- **⭐⭐ The cardinality-free gradient of the weight's argument.**  `Y = ∑_i ρ_i^{2r}` with
`ρ_i = ‖F_i‖ / T_i` satisfies

  `‖DY(M)‖ ≤ 2r · card(S)^{1/(2r)} · Y(M)^{1 − 1/(2r)} · (b₁/T₀)`,

i.e. the additive constant of the affine bound is paid only `card^{1/(2r)}` times — which
`RBM.Step2Bootstrap.rpow_card_le_exp_one` turns into `e` at `2r ≍ log N`.  Compare
`RBM.Gauss.bddC2C_sum_of_uniform`, whose (uniform, `Y`-free) constant carries a full factor
`card S`: **this is the entire gain of the soft maximum over the product weight**, now
available on the model's ratios. -/
theorem norm_fderiv_sum_ratio_pow_le {ι : Type*} (S : Finset ι) {F : ι → E → ℂ} {T : ι → ℝ}
    {b₀ b₁ b₂ T₀ : ℝ} (hT₀ : 0 < T₀) (hb₁ : 0 ≤ b₁) (hT : ∀ i ∈ S, T₀ ≤ T i)
    (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂) {r : ℕ} (hr : 1 ≤ r) (M : E) :
    ‖fderiv ℝ (fun M => ∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r)) M‖
      ≤ ((2 * r : ℕ) : ℝ) * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) *
          (∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r)) ^ (1 - (1 : ℝ) / (2 * (r : ℝ))))
        * (b₁ / T₀) := by
  have hb : (0 : ℝ) ≤ b₁ / T₀ := div_nonneg hb₁ hT₀.le
  have hdi : ∀ i ∈ S, HasFDerivAt (fun M => (‖F i M‖ / T i) ^ (2 * r))
      (fderiv ℝ (fun M => (‖F i M‖ / T i) ^ (2 * r)) M) M := fun i hi =>
    ((bddC2C_ratio_pow_of_le hT₀ (hT i hi) (hF i hi) r).differentiable M).hasFDerivAt
  have hs : HasFDerivAt (fun M => ∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r))
      (∑ i ∈ S, fderiv ℝ (fun M => (‖F i M‖ / T i) ^ (2 * r)) M) M := by
    exact HasFDerivAt.fun_sum hdi
  rw [hs.fderiv]
  have hstep : ‖∑ i ∈ S, fderiv ℝ (fun M => (‖F i M‖ / T i) ^ (2 * r)) M‖
      ≤ ∑ i ∈ S, ((2 * r : ℕ) : ℝ) * (‖F i M‖ / T i) ^ (2 * r - 1) * (b₁ / T₀) :=
    (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i hi =>
        norm_fderiv_ratio_pow_le hT₀ (hT i hi) (hF i hi) hr M)
  refine hstep.trans ?_
  have habs : ∀ i ∈ S, (‖F i M‖ / T i) ^ (2 * r - 1) = |‖F i M‖ / T i| ^ (2 * r - 1) := by
    intro i hi
    have hTi : (0 : ℝ) < T i := lt_of_lt_of_le hT₀ (hT i hi)
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hTi.le)]
  have hrw : ∑ i ∈ S, ((2 * r : ℕ) : ℝ) * (‖F i M‖ / T i) ^ (2 * r - 1) * (b₁ / T₀)
      = ((2 * r : ℕ) : ℝ) * (∑ i ∈ S, |‖F i M‖ / T i| ^ (2 * r - 1)) * (b₁ / T₀) := by
    have h1 : ∀ i ∈ S, ((2 * r : ℕ) : ℝ) * (‖F i M‖ / T i) ^ (2 * r - 1) * (b₁ / T₀)
        = ((2 * r : ℕ) : ℝ) * |‖F i M‖ / T i| ^ (2 * r - 1) * (b₁ / T₀) :=
      fun i hi => by rw [habs i hi]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hrw]
  have hhold := sum_abs_pow_pred_le (S := S) (ρ := fun i => ‖F i M‖ / T i) hr
  have hcast : (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhold hcast) hb

end Sharp

/-! ### The assembly: `TestFun` for the soft-max weight built from the ratios -/

section Assembly

variable {d : Dims} {N : ℕ}

/-- **⭐⭐ 甲, in the shape route (A′) consumes it.**  From a `RBM.Gauss.BddC2C` for each
numerator and a common positive floor `T₀` for the denominators, the soft-max weight built
from the ratios `ρ i = ‖F i‖ / T i` times any `C²` moment factor is a
`RBM.Gauss.TestFun` — the hypothesis of `RBM.Gauss.hasDerivAt_integral_Phi`. -/
theorem testFun_softW_ratio {ι : Type*} {S : Finset ι}
    {F : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {T : ι → ℝ}
    {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {r : ℕ} {Θ b₀ b₁ b₂ T₀ c₀ c₁ c₂ : ℝ}
    (hr : 1 ≤ r) (hΘ : 0 < Θ) (hT₀ : 0 < T₀) (hT : ∀ i ∈ S, T₀ ≤ T i)
    (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂) (hΨ : BddC2C Ψ c₀ c₁ c₂) :
    TestFun d N (fun M => ((softW r S (fun i => ‖F i M‖ / T i) Θ : ℝ) : ℂ) * Ψ M) :=
  testFun_softW_mul hr hΘ
    (bddC2C_sum_of_uniform S (f := fun i M => (‖F i M‖ / T i) ^ (2 * r))
      (fun i hi => bddC2C_ratio_pow_of_le hT₀ (hT i hi) (hF i hi) r)) hΨ

/-! ### The model-level numerator `L − K` -/

/-- `L_{σ,a} − K` is `C²` with explicit constants: the loop's own, with `‖K‖` added to the
value bound.  `K` is `H`-independent, so it costs nothing at first or second order. -/
theorem bddC2C_loopObs_sub {z : ℂ} {η B : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (hBa : η⁻¹ ≤ B) (hBb : η⁻¹ * η⁻¹ ≤ B) (hBc : 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ B)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (K : ℂ) :
    BddC2C (fun M => loopObs d N z I M - K)
      ((Fintype.card (d.Idx N) : ℝ) * B ^ I.a.length + ‖K‖)
      ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length) + 0)
      ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2 * B ^ I.a.length) + 0) := by
  have hfun : (fun M => loopObs d N z I M - K)
      = fun M => loopObs d N z I M + (-K : ℂ) := by funext M; rw [sub_eq_add_neg]
  rw [hfun]
  have h := bddC2C_add (bddC2C_loopObs hz hη hzη hBa hBb hBc hwf)
    (bddC2C_const (E := Matrix (d.Idx N) (d.Idx N) ℂ) (-K : ℂ))
  simpa using h

/-- **⭐⭐ The model-level instance of 甲**, at the shape of (5.29): the index set carries a
loop index `I i` and a distance `ℓ i`, the numerator is `(L − K)_{u,σ,a}` and the denominator
is `Θ_N · T_{u,D}(ℓ i)` of (5.27).  The floor of the denominator is `Θ_N · W^{-D}`
(`RBM.rpow_neg_le_tailT`), so the constants depend on the model only through

  `η_u⁻¹` (through `B = 2(1 + η_u⁻¹)³`),  `W^D`,  `Θ_N⁻¹`,  the matrix dimension, and `n`.

No constant is infinite and none depends on the quantity being estimated. -/
theorem testFun_softW_lkRatio {ι : Type*} {S : Finset ι} {z : ℂ}
    {η Θ ΘN W ℓu ηu D Kb : ℝ} {r n : ℕ}
    (hr : 1 ≤ r) (hΘ : 0 < Θ) (hΘN : 0 < ΘN) (hW : 0 < W)
    (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    {I : ι → LoopIdx (ZMod (d.L N))} (hwf : ∀ i ∈ S, (I i).WF)
    (hlen : ∀ i ∈ S, (I i).a.length = n)
    {K : ι → ℂ} (hK : ∀ i ∈ S, ‖K i‖ ≤ Kb) {ℓ : ι → ℝ}
    {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c₀ c₁ c₂ : ℝ} (hΨ : BddC2C Ψ c₀ c₁ c₂) :
    TestFun d N (fun M => ((softW r S (fun i =>
        ‖loopObs d N z (I i) M - K i‖ / (ΘN * tailT W ℓu ηu D (ℓ i))) Θ : ℝ) : ℂ) * Ψ M) := by
  set B : ℝ := 2 * (1 + η⁻¹) ^ 3 with hB
  obtain ⟨hB1, hB2, hB3⟩ := le_two_mul_one_add_inv_cube hη
  have hT₀ : (0 : ℝ) < ΘN * W ^ (-D) := mul_pos hΘN (Real.rpow_pos_of_pos hW _)
  refine testFun_softW_ratio (b₀ := (Fintype.card (d.Idx N) : ℝ) * B ^ n + Kb)
    (b₁ := (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) * B ^ n))
    (b₂ := (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * B ^ n))
    (T₀ := ΘN * W ^ (-D)) hr hΘ hT₀ (fun i hi => ?_) (fun i hi => ?_) hΨ
  · exact mul_le_mul_of_nonneg_left (rpow_neg_le_tailT (ℓ i)) hΘN.le
  · have h := bddC2C_loopObs_sub hz hη hzη hB1 hB2 hB3 (hwf i hi) (K i)
    rw [hlen i hi] at h
    exact h.mono (by linarith [hK i hi]) (by linarith) (by linarith)

/-- **Step 4 of the route-(A′) chain, compiled: the generator identity for the (A′)
integrand.**  With the `TestFun` of `RBM.Gauss.testFun_softW_lkRatio` in hand,
`RBM.Gauss.hasDerivAt_integral_Phi` applies on the **full** measure — no prefix event, no
bad-event remainder.  This is the shape Stein's identity can be applied to, and it is what
route (A′) exists to obtain. -/
theorem hasDerivAt_integral_softW_lkRatio (hst : MatrixStein d) {ι : Type*} {S : Finset ι}
    {z : ℂ} {η Θ ΘN W ℓu ηu D Kb : ℝ} {r n : ℕ}
    (hr : 1 ≤ r) (hΘ : 0 < Θ) (hΘN : 0 < ΘN) (hW : 0 < W)
    (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    {I : ι → LoopIdx (ZMod (d.L N))} (hwf : ∀ i ∈ S, (I i).WF)
    (hlen : ∀ i ∈ S, (I i).a.length = n)
    {K : ι → ℂ} (hK : ∀ i ∈ S, ‖K i‖ ≤ Kb) {ℓ : ι → ℝ}
    {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c₀ c₁ c₂ : ℝ} (hΨ : BddC2C Ψ c₀ c₁ c₂)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, (fun M => ((softW r S (fun i =>
          ‖loopObs d N z (I i) M - K i‖ / (ΘN * tailT W ℓu ηu D (ℓ i))) Θ : ℝ) : ℂ) * Ψ M)
        (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
        ∫ ω, coordD2 d N (fun M => ((softW r S (fun i =>
            ‖loopObs d N z (I i) M - K i‖ / (ΘN * tailT W ℓu ηu D (ℓ i))) Θ : ℝ) : ℂ) * Ψ M)
          (Hflow d N u ω) q ∂(P d)) u :=
  hasDerivAt_integral_Phi hst
    (testFun_softW_lkRatio hr hΘ hΘN hW hz hη hzη hwf hlen hK hΨ) hu

end Assembly

/-! ### A compiled satisfiability witness -/

section Sat

/-- Every hypothesis of `RBM.Gauss.testFun_softW_lkRatio` is simultaneously satisfiable, with a
**genuine** two-edge loop `σ = (+,−)` as the numerator (the `(+,−)` of (5.17)), the tail
function `T_{u,D}` of (5.27) as the denominator, and the moment factor `Ψ ≡ 1`.  None of the
constants is `∞` and none depends on the estimated quantity: `η_u = 1`, `W = 2`, `D = 1`,
`Θ_N = 1`, so the denominator floor is `1/2 > 0`. -/
theorem sat_testFun_softW_lkRatio (d : Dims) (N : ℕ) (a₁ a₂ : ZMod (d.L N)) :
    TestFun d N (fun M => ((softW 1 ({0} : Finset (Fin 1)) (fun _ =>
        ‖loopObs d N Complex.I ⟨[true, false], [a₁, a₂]⟩ M - 0‖ /
          (1 * tailT 2 1 1 1 0)) 1 : ℝ) : ℂ) * (1 : ℂ)) := by
  have hz : (Complex.I : ℂ).im ≠ 0 := by simp
  have hzη : (1 : ℝ) ≤ |(Complex.I : ℂ).im| := by simp
  refine testFun_softW_lkRatio (n := 2) (Kb := 0)
    (I := fun _ : Fin 1 => (⟨[true, false], [a₁, a₂]⟩ : LoopIdx (ZMod (d.L N))))
    (K := fun _ : Fin 1 => (0 : ℂ)) (ℓ := fun _ : Fin 1 => (0 : ℝ))
    le_rfl one_pos one_pos two_pos hz one_pos hzη
    (fun _ _ => by simp [LoopIdx.WF]) (fun _ _ => rfl) (fun _ _ => by simp)
    (bddC2C_const (E := Matrix (d.Idx N) (d.Idx N) ℂ) (1 : ℂ))

end Sat

end Gauss

end RBM

/-!
## Deviations from the paper

**T255a** (§5.3, (5.29) and the display after (5.44); Stein/generator in §5.2).

1. *The ratio of (5.29) enters only through its `2r`-th power.*  The paper writes the
   soft maximum `J̃ = (∑_i ρ_i^{2r})^{1/(2r)}` of the ratios `ρ_i = ‖(L−K)‖/(Θ_N T_{u,D})`,
   and the smoothness that route (A′) needs is smoothness of `J̃` in the matrix entries.  The
   Lean statements are therefore about `∑_i ρ_i^{2r}`, never about an individual `ρ_i`:
   `ρ_i` itself is *not* differentiable where `L = K` (`RBM.Gauss.not_bddC2C_norm_div`), while
   the sum is a polynomial in `(Re, Im)` of the loop values.  No change to the paper is
   proposed; this only fixes which object carries the regularity.  Affected: the sentence
   introducing (5.29).  No renumbering.
2. *The denominator is replaced by its floor in the constants.*  The paper's `T_{u,D}(ℓ)` of
   (5.27) is `ℓ`-dependent; the `RBM.Gauss.BddC2C` constants here use only
   `T_{u,D}(ℓ) ≥ W^{-D}` (`RBM.rpow_neg_le_tailT`), which is what makes one triple of
   constants serve the whole net.  This is a weakening in our favour and costs the exponent
   `W^{D}` that the paper already pays at that step.  No change to the paper.  No
   renumbering.
3. *The gradient estimate is affine with `Λ = 0`, as in T250a.*  The sharp bound proved here,
   `‖D(∑_i ρ_i^{2r})‖ ≤ 2r·card^{1/(2r)}·(∑_i ρ_i^{2r})^{1−1/(2r)}·(b₁/T₀)`, is the model-side
   instance of `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` with `Λ = 0`; the paper's
   display after (5.44) is unaffected, since `card^{1/(2r)} ≤ e` at `2r ≍ log N`
   (`RBM.Step2Bootstrap.rpow_card_le_exp_one`).  No renumbering.
-/
