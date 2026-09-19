/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.SymbolBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The infinite-volume kernel and the contour shift (B.2), (B.4), (B.5)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Appendix B, p. 89-90.

With `D_ξ(z) = 1 - ξ Ŝ(z)`, `Ŝ(z) = (1 + 2 cos z)/3` and `κ = |1 - ξ|^{1/2}`:

* (B.2) `K_{ξ,∞}(u) = (2π)⁻¹ ∫_{-π}^{π} e^{ipu} / D_ξ(p) dp`, `u ∈ ℤ`;
* (B.4) for `|η| ≤ c₀ κ`, `|D_ξ(p + iη)| ≥ c (κ² + p²)`;
* (B.5) shifting the contour by `i c₀ κ sgn(u)`, `|K_{ξ,∞}(u)| ≤ (C/κ) e^{-c κ |u|}`.

The constants are explicit: `c₀ = 1/(16π²)`, `c = 1/(12π²)` in (B.4), `C = 6π²` in (B.5).
(B.4) is proved for `p ∈ [-π, π]`, where `|p|_* = |p|`; that is the range of (B.2).

## The argument

(B.4): `D_ξ(p + iη) - D_ξ(p) = -(2ξ/3)(cos(p + iη) - cos p)`, and
`|cos(p + iη) - cos p| ≤ (cosh η - 1) + |sin p| |sinh η| ≤ η² + 2|p||η|` for `|η| ≤ 1`.
With `|η| ≤ c₀κ` this is at most `2c₀(κ² + p²)`, which the lower bound
`(κ² + p²)/(6π²)` of (B.3) (`RBM.le_norm_one_sub_mul_real`) absorbs.

(B.5): the integrand is `2π`-periodic in `p` (as `u ∈ ℤ`) and holomorphic where `D_ξ ≠ 0`,
so by Cauchy's theorem on the rectangle `[-π, π] × [0, η]` the two vertical sides cancel and
the integral over `ℝ` equals the one over `ℝ + iη`.  There `|e^{i(p+iη)u}| = e^{-ηu}`, and
`∫_{-π}^{π} dp/(κ² + p²) ≤ π/κ` (arctan).

## Main results

* `RBM.Kinf` : (B.2)
* `RBM.norm_cos_add_mul_I_sub_le` : `|cos(x + iy) - cos x| ≤ y² + 2|x||y|`
* `RBM.le_norm_Dxi` : (B.4)
* `RBM.integral_kernelFun_shift` : the contour shift
* `RBM.norm_Kinf_le`, `RBM.norm_Kinf_le_exists` : (B.5)
-/

namespace RBM

open Real

/-- The constant `c₀` of (B.4). -/
noncomputable def cZero : ℝ := 1 / (16 * π ^ 2)

theorem cZero_pos : 0 < cZero := by unfold cZero; positivity

/-- `D_ξ(z) = 1 - ξ (1 + 2 cos z)/3`, the multiplier of Appendix B at complex momentum. -/
noncomputable def Dxi (ξ z : ℂ) : ℂ := 1 - ξ * ((1 + 2 * Complex.cos z) / 3)

/-- The integrand of (B.2), `e^{izu} / D_ξ(z)`. -/
noncomputable def kernelFun (ξ : ℂ) (u : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * u) / Dxi ξ z

/-- **(B.2)**: the infinite-volume kernel `K_{ξ,∞}(u) = (2π)⁻¹ ∫_{-π}^{π} e^{ipu}/D_ξ(p) dp`. -/
noncomputable def Kinf (ξ : ℂ) (u : ℤ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ p : ℝ in (-π)..π, kernelFun ξ u p

section Elementary

theorem cosh_sub_one_le {y : ℝ} (hy : |y| ≤ 1) : cosh y - 1 ≤ y ^ 2 := by
  have h1 := cosh_le_exp_half_sq y
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [sq_abs y, abs_nonneg y]
  have h2 : |y ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; linarith
  have h3 := abs_exp_sub_one_le h2
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 2 / 2)] at h3
  have h4 := le_abs_self (exp (y ^ 2 / 2) - 1)
  linarith

theorem abs_sinh_le {y : ℝ} (hy : |y| ≤ 1) : |sinh y| ≤ 2 * |y| := by
  rw [sinh_eq]
  have h1 := abs_exp_sub_one_le hy
  have h2 := abs_exp_sub_one_le (x := -y) (by rwa [abs_neg])
  rw [abs_neg] at h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

/-- `|cos(x + iy) - cos x| ≤ y² + 2|x||y|` for `|y| ≤ 1`. -/
theorem norm_cos_add_mul_I_sub_le (x y : ℝ) (hy : |y| ≤ 1) :
    ‖Complex.cos (x + y * Complex.I) - Complex.cos x‖ ≤ y ^ 2 + 2 * |x| * |y| := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  have e : ((cos x : ℝ) : ℂ) * ((cosh y : ℝ) : ℂ) - ((sin x : ℝ) : ℂ) * ((sinh y : ℝ) : ℂ)
      * Complex.I - ((cos x : ℝ) : ℂ)
      = ((cos x * (cosh y - 1) : ℝ) : ℂ) - ((sin x * sinh y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e]
  have hc : |cosh y - 1| ≤ y ^ 2 := by
    rw [abs_of_nonneg (by linarith [one_le_cosh y])]; exact cosh_sub_one_le hy
  calc ‖((cos x * (cosh y - 1) : ℝ) : ℂ) - ((sin x * sinh y : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((cos x * (cosh y - 1) : ℝ) : ℂ)‖ + ‖((sin x * sinh y : ℝ) : ℂ) * Complex.I‖ :=
        norm_sub_le _ _
    _ = |cos x| * |cosh y - 1| + |sin x| * |sinh y| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ 1 * y ^ 2 + |x| * (2 * |y|) :=
        add_le_add (mul_le_mul (abs_cos_le_one x) hc (abs_nonneg _) zero_le_one)
          (mul_le_mul abs_sin_le_abs (abs_sinh_le hy) (abs_nonneg _) (abs_nonneg _))
    _ = y ^ 2 + 2 * |x| * |y| := by ring

/-- `∫_{-π}^{π} dp / (κ² + p²) ≤ π/κ`. -/
theorem integral_inv_sq_add_sq_le {κ : ℝ} (hκ : 0 < κ) :
    ∫ x in (-π)..π, (κ ^ 2 + x ^ 2)⁻¹ ≤ π / κ := by
  have e : ∀ x : ℝ, (κ ^ 2 + x ^ 2)⁻¹ = κ⁻¹ ^ 2 * (1 + (x / κ) ^ 2)⁻¹ := by
    intro x; field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (ne_of_gt hκ)]
  simp only [smul_eq_mul]
  rw [integral_inv_one_add_sq, neg_div, arctan_neg]
  have h := arctan_lt_pi_div_two (π / κ)
  have : κ⁻¹ ^ 2 * (κ * (arctan (π / κ) - -arctan (π / κ))) = 2 * arctan (π / κ) / κ := by
    field_simp; ring
  rw [this, div_le_div_iff_of_pos_right hκ]
  linarith

end Elementary

variable {ξ : ℂ}

/-- `κ² = |1 - ξ|` with `κ = √|1 - ξ|`. -/
theorem sq_sqrt_norm_one_sub (ξ : ℂ) : √‖1 - ξ‖ ^ 2 = ‖1 - ξ‖ := Real.sq_sqrt (norm_nonneg _)

theorem sqrt_norm_one_sub_pos (hξ : ‖ξ‖ < 1) : 0 < √‖1 - ξ‖ := by
  refine Real.sqrt_pos.2 (norm_pos_iff.2 (sub_ne_zero.2 ?_))
  rintro rfl
  simp at hξ

/-- **(B.4)**: for `p ∈ [-π, π]` and `|η| ≤ c₀ κ`, `(κ² + p²)/(12π²) ≤ |D_ξ(p + iη)|`. -/
theorem le_norm_Dxi (hξ : ‖ξ‖ < 1) {x y : ℝ} (hx : |x| ≤ π)
    (hy : |y| ≤ cZero * √‖1 - ξ‖) :
    (‖1 - ξ‖ + x ^ 2) / (12 * π ^ 2) ≤ ‖Dxi ξ (x + y * Complex.I)‖ := by
  set κ := √‖1 - ξ‖ with hκdef
  have hκ2 : κ ^ 2 = ‖1 - ξ‖ := sq_sqrt_norm_one_sub ξ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hpi : 3 < π := pi_gt_three
  have hw : ‖1 - ξ‖ < 2 := by
    calc ‖1 - ξ‖ ≤ ‖(1 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
      _ < 2 := by rw [norm_one]; linarith
  have hκ2' : κ ≤ 2 := by nlinarith
  have hc0 : cZero ≤ 1 / 144 := by
    unfold cZero; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hc00 : 0 ≤ cZero := cZero_pos.le
  have hy1 : |y| ≤ 1 := by nlinarith
  -- (B.3) at the real point
  have hS := cos_symbol_bounds hx
  have hreal : Dxi ξ x = 1 - ξ * (((1 + 2 * cos x) / 3 : ℝ) : ℂ) := by
    simp only [Dxi, ← Complex.ofReal_cos]; push_cast; ring
  have h0 : (‖1 - ξ‖ + x ^ 2) / (6 * π ^ 2) ≤ ‖Dxi ξ x‖ := by
    rw [hreal]; exact le_norm_one_sub_mul_real hξ hS.1 hS.2.1 hS.2.2.1
  -- the perturbation
  have hdiff : Dxi ξ (x + y * Complex.I)
      = Dxi ξ x - ξ * (2 / 3) * (Complex.cos (x + y * Complex.I) - Complex.cos x) := by
    unfold Dxi; ring
  have hcos := norm_cos_add_mul_I_sub_le x y hy1
  have hpert : ‖ξ * (2 / 3) * (Complex.cos (x + y * Complex.I) - Complex.cos x)‖
      ≤ 2 / 3 * (y ^ 2 + 2 * |x| * |y|) := by
    rw [norm_mul, norm_mul]
    have h23 : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by norm_num
    rw [h23]
    have := mul_le_mul_of_nonneg_left hcos (by norm_num : (0 : ℝ) ≤ 2 / 3)
    nlinarith [norm_nonneg ξ, norm_nonneg (Complex.cos (x + y * Complex.I) - Complex.cos x)]
  -- `y² + 2|x||y| ≤ 2 c₀ (κ² + x²)`
  have hyy : y ^ 2 ≤ cZero * κ ^ 2 := by
    have : y ^ 2 ≤ (cZero * κ) ^ 2 := by
      rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
    nlinarith
  have hxy : 2 * |x| * |y| ≤ cZero * (κ ^ 2 + x ^ 2) := by
    have h1 : 2 * |x| * |y| ≤ 2 * |x| * (cZero * κ) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    nlinarith [sq_nonneg (|x| - κ), sq_abs x, abs_nonneg x]
  have htri := norm_sub_norm_le (Dxi ξ x)
    (ξ * (2 / 3) * (Complex.cos (x + y * Complex.I) - Complex.cos x))
  rw [← hdiff] at htri
  have hcz : 2 / 3 * (2 * cZero) = 1 / (12 * π ^ 2) := by unfold cZero; field_simp; ring
  have key : 2 / 3 * (y ^ 2 + 2 * |x| * |y|) ≤ (‖1 - ξ‖ + x ^ 2) / (12 * π ^ 2) := by
    rw [← hκ2]
    calc 2 / 3 * (y ^ 2 + 2 * |x| * |y|) ≤ 2 / 3 * (2 * cZero * (κ ^ 2 + x ^ 2)) := by
          nlinarith
      _ = (κ ^ 2 + x ^ 2) / (12 * π ^ 2) := by rw [← mul_assoc, hcz]; ring
  have e2 : (‖1 - ξ‖ + x ^ 2) / (6 * π ^ 2)
      = 2 * ((‖1 - ξ‖ + x ^ 2) / (12 * π ^ 2)) := by field_simp; ring
  linarith

theorem Dxi_ne_zero (hξ : ‖ξ‖ < 1) {z : ℂ} (hre : |z.re| ≤ π)
    (him : |z.im| ≤ cZero * √‖1 - ξ‖) : Dxi ξ z ≠ 0 := by
  have h := le_norm_Dxi hξ hre him
  rw [Complex.re_add_im] at h
  have hpos : 0 < (‖1 - ξ‖ + z.re ^ 2) / (12 * π ^ 2) := by
    have := sqrt_norm_one_sub_pos hξ
    have h1 : 0 < ‖1 - ξ‖ := by rw [← sq_sqrt_norm_one_sub ξ]; positivity
    positivity
  intro h0
  rw [h0, norm_zero] at h
  linarith

theorem kernelFun_add_two_pi (u : ℤ) (z : ℂ) :
    kernelFun ξ u (z + 2 * π) = kernelFun ξ u z := by
  unfold kernelFun Dxi
  rw [Complex.cos_add_two_pi]
  congr 1
  rw [show Complex.I * (z + 2 * π) * u = Complex.I * z * u + u * (2 * π * Complex.I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem differentiableAt_kernelFun (u : ℤ) {z : ℂ} (hD : Dxi ξ z ≠ 0) :
    DifferentiableAt ℂ (kernelFun ξ u) z := by
  unfold kernelFun
  refine DifferentiableAt.div ?_ ?_ hD
  · fun_prop
  · unfold Dxi; fun_prop

/-- **The contour shift**: for `|η| ≤ c₀ κ`,
`∫_{-π}^{π} e^{ipu}/D_ξ(p) dp = ∫_{-π}^{π} e^{i(p+iη)u}/D_ξ(p+iη) dp`. -/
theorem integral_kernelFun_shift (hξ : ‖ξ‖ < 1) {η : ℝ} (hη : |η| ≤ cZero * √‖1 - ξ‖)
    (u : ℤ) :
    ∫ x : ℝ in (-π)..π, kernelFun ξ u x
      = ∫ x : ℝ in (-π)..π, kernelFun ξ u (x + η * Complex.I) := by
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (kernelFun ξ u)
    ((-π : ℝ) : ℂ) ((π : ℂ) + η * Complex.I) ?_
  · simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, zero_mul, add_zero, zero_add, Complex.ofReal_zero] at H
    have hv : ∫ y : ℝ in (0 : ℝ)..η, kernelFun ξ u (π + y * Complex.I)
        = ∫ y : ℝ in (0 : ℝ)..η, kernelFun ξ u ((-π : ℝ) + y * Complex.I) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [← kernelFun_add_two_pi u ((-π : ℝ) + y * Complex.I)]
      congr 1
      push_cast; ring
    rw [hv] at H
    simp only [Complex.ofReal_neg] at H ⊢
    linear_combination H
  · intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨h1, h2⟩ := hz
    simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at h1 h2
    have hre : |z.re| ≤ π := by
      rw [Set.uIcc_of_le (by linarith [pi_pos])] at h1
      exact abs_le.2 ⟨h1.1, h1.2⟩
    have him : |z.im| ≤ cZero * √‖1 - ξ‖ := by
      have := Set.abs_sub_left_of_mem_uIcc h2
      simp only [sub_zero] at this
      linarith
    exact (differentiableAt_kernelFun u (Dxi_ne_zero hξ hre him)).differentiableWithinAt

/-- The shifted integrand: `|e^{i(p+iη)u}/D_ξ(p+iη)| ≤ e^{-ηu} · 12π²/(κ² + p²)`. -/
theorem norm_kernelFun_shift_le (hξ : ‖ξ‖ < 1) {x η : ℝ} (hx : |x| ≤ π)
    (hη : |η| ≤ cZero * √‖1 - ξ‖) (u : ℤ) :
    ‖kernelFun ξ u (x + η * Complex.I)‖
      ≤ exp (-(η * u)) * (12 * π ^ 2 * (‖1 - ξ‖ + x ^ 2)⁻¹) := by
  have hD := le_norm_Dxi hξ hx hη
  have hpos : 0 < (‖1 - ξ‖ + x ^ 2) / (12 * π ^ 2) := by
    have := sqrt_norm_one_sub_pos hξ
    have h1 : 0 < ‖1 - ξ‖ := by rw [← sq_sqrt_norm_one_sub ξ]; positivity
    positivity
  unfold kernelFun
  rw [norm_div, Complex.norm_exp]
  have hre : (Complex.I * (x + η * Complex.I) * u).re = -(η * u) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, div_eq_mul_inv]
  gcongr
  calc ‖Dxi ξ (x + η * Complex.I)‖⁻¹ ≤ ((‖1 - ξ‖ + x ^ 2) / (12 * π ^ 2))⁻¹ := inv_anti₀ hpos hD
    _ = 12 * π ^ 2 * (‖1 - ξ‖ + x ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- **(B.5)**: `|K_{ξ,∞}(u)| ≤ (6π²/κ) e^{-c₀ κ |u|}`, `κ = |1 - ξ|^{1/2}`. -/
theorem norm_Kinf_le (hξ : ‖ξ‖ < 1) (u : ℤ) :
    ‖Kinf ξ u‖ ≤ 6 * π ^ 2 / √‖1 - ξ‖ * exp (-(cZero * √‖1 - ξ‖ * |(u : ℝ)|)) := by
  set κ := √‖1 - ξ‖ with hκdef
  have hκ : 0 < κ := sqrt_norm_one_sub_pos hξ
  have hκ2 : κ ^ 2 = ‖1 - ξ‖ := sq_sqrt_norm_one_sub ξ
  -- shift by `η = c₀ κ sgn(u)`
  set η : ℝ := if 0 ≤ u then cZero * κ else -(cZero * κ) with hηdef
  have hη : |η| ≤ cZero * κ := by
    have : 0 ≤ cZero * κ := mul_nonneg cZero_pos.le hκ.le
    rw [hηdef]; split_ifs <;> simp [abs_of_nonneg this]
  have hηu : η * u = cZero * κ * |(u : ℝ)| := by
    rw [hηdef]
    split_ifs with hu
    · rw [abs_of_nonneg (by exact_mod_cast hu)]
    · rw [abs_of_neg (by exact_mod_cast (not_le.1 hu))]; ring
  set E := exp (-(cZero * κ * |(u : ℝ)|)) with hE
  let g : ℝ → ℝ := fun x => E * (12 * π ^ 2 * (κ ^ 2 + x ^ 2)⁻¹)
  have hg : Continuous g := by
    refine continuous_const.mul (continuous_const.mul ?_)
    exact (continuous_const.add (continuous_pow 2)).inv₀ fun x =>
      (add_pos_of_pos_of_nonneg (pow_pos hκ 2) (sq_nonneg x)).ne'
  have hint : ‖∫ x : ℝ in (-π)..π, kernelFun ξ u (x + η * Complex.I)‖
      ≤ ∫ x in (-π)..π, g x := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith [pi_pos])
      (Filter.Eventually.of_forall fun x hx => ?_) (hg.intervalIntegrable _ _)
    have hx' : |x| ≤ π := abs_le.2 ⟨hx.1.le, hx.2⟩
    have := norm_kernelFun_shift_le hξ hx' hη u
    rw [hηu, ← hκ2] at this
    exact this
  have hgint : ∫ x in (-π)..π, g x = E * (12 * π ^ 2) * ∫ x in (-π)..π, (κ ^ 2 + x ^ 2)⁻¹ := by
    simp only [g, ← mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  have harc := integral_inv_sq_add_sq_le hκ
  have hE0 : 0 ≤ E := (exp_pos _).le
  rw [Kinf, integral_kernelFun_shift hξ hη u, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc (2 * π)⁻¹ * ‖∫ x : ℝ in (-π)..π, kernelFun ξ u (x + η * Complex.I)‖
      ≤ (2 * π)⁻¹ * (E * (12 * π ^ 2) * (π / κ)) := by
        gcongr
        calc _ ≤ ∫ x in (-π)..π, g x := hint
          _ = E * (12 * π ^ 2) * ∫ x in (-π)..π, (κ ^ 2 + x ^ 2)⁻¹ := hgint
          _ ≤ E * (12 * π ^ 2) * (π / κ) := by gcongr
    _ = 6 * π ^ 2 / κ * E := by field_simp; ring

/-- **(B.5)** in the form of the paper: `|K_{ξ,∞}(u)| ≤ (C/κ) e^{-cκ|u|}` with constants
independent of `ξ` and `u`. -/
theorem norm_Kinf_le_exists :
    ∃ C > 0, ∃ c > 0, ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ u : ℤ,
      ‖Kinf ξ u‖ ≤ C / √‖1 - ξ‖ * exp (-(c * √‖1 - ξ‖ * |(u : ℝ)|)) :=
  ⟨6 * π ^ 2, by positivity, cZero, cZero_pos, fun _ hξ u => norm_Kinf_le hξ u⟩

end RBM
