/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian integration by parts (Stein's identity)

The analytic foundation of the *moment route* for the stochastic layer: see the project
note `claude/moment-route-plan.md`.  Realizing the flow of (2.34) as `H_u = sqrt(u) * X`
with `X` a fixed Gaussian band matrix, the generator identity

  `d/du E[Phi(H_u)] = (1/2) sum_ij S_ij E[d_ij d_ji Phi(H_u)]`

is what replaces Ito's formula, and *this* file is what makes that identity true: the only
probabilistic input is that a centred Gaussian density satisfies `p' = -(x/v) p`, so that
one integration by parts on the line turns a factor of `x` into a derivative.

Mathlib has `gaussianPDFReal` with an explicit formula but no integration-by-parts lemma,
so we prove it here.

## Main results

* `RBM.hasDerivAt_gaussianPDFReal_zero` : `p' = -(x/v) p`
* `RBM.integral_mul_gaussianPDF` : Stein's identity, density form
* `RBM.integral_mul_gaussianReal` : Stein's identity, `E[X f(X)] = v E[f'(X)]`

## Note on hypotheses

Integrability is taken as an explicit hypothesis rather than derived from growth
conditions.  In every application here the integrand is a polynomial in entries of
`G = (H - z)^{-1}` with `Im z >= eta > 0`, so `‖G‖ <= eta⁻¹` holds on the *whole* space and
every derivative is bounded globally by `k! eta^{-(k+1)}`; integrability against a Gaussian
is then immediate.  Keeping it as a hypothesis makes this file reusable and keeps the
domination argument where it belongs.
-/

namespace RBM

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {var : ℝ≥0}

/-- The centred Gaussian density solves the first-order ODE `p' = -(x/v) p`.  This single
fact is the whole probabilistic content of the moment route. -/
theorem hasDerivAt_gaussianPDFReal_zero (hv : (var : ℝ) ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 var) (-(x / (var : ℝ)) * gaussianPDFReal 0 var x) x := by
  have key : gaussianPDFReal 0 var
      = fun y : ℝ => (Real.sqrt (2 * π * (var : ℝ)))⁻¹ * Real.exp (-(y ^ 2) / (2 * (var : ℝ))) := by
    funext y
    simp [gaussianPDFReal]
  have hp : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * (var : ℝ)))
      (-(2 * x) / (2 * (var : ℝ))) x := by
    simpa using ((hasDerivAt_pow 2 x).neg).div_const (2 * (var : ℝ))
  have hc := (hp.exp).const_mul ((Real.sqrt (2 * π * (var : ℝ)))⁻¹)
  rw [key]
  convert hc using 1
  simp only
  field_simp
  try ring

/-- **Stein's identity**, density form:
`∫ x f(x) p(x) dx = v ∫ f'(x) p(x) dx`.

One integration by parts on `(-∞, ∞)`; the boundary terms vanish because the total
function is integrable. -/
theorem integral_mul_gaussianPDF (hv : (var : ℝ) ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h1 : Integrable fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x))
    (h2 : Integrable fun x : ℝ => f' x * gaussianPDFReal 0 var x)
    (h3 : Integrable fun x : ℝ => f x * gaussianPDFReal 0 var x) :
    ∫ x : ℝ, x * f x * gaussianPDFReal 0 var x
      = (var : ℝ) * ∫ x : ℝ, f' x * gaussianPDFReal 0 var x := by
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 var) (u' := f')
    (v' := fun x : ℝ => -(x / (var : ℝ)) * gaussianPDFReal 0 var x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal_zero hv x) h1 h2 h3
  have hL : (fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x))
      = fun x : ℝ => (-(1 / (var : ℝ))) * (x * f x * gaussianPDFReal 0 var x) := by
    funext x
    field_simp
    try ring
  rw [hL, integral_const_mul] at key
  field_simp at key
  linarith

/-- **Stein's identity** for the Gaussian measure: `E[X f(X)] = v E[f'(X)]`. -/
theorem integral_mul_gaussianReal (hv : var ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h1 : Integrable fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x))
    (h2 : Integrable fun x : ℝ => f' x * gaussianPDFReal 0 var x)
    (h3 : Integrable fun x : ℝ => f x * gaussianPDFReal 0 var x) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var) = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  have hv' : (var : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h := integral_mul_gaussianPDF hv' hf h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (f := fun x : ℝ => x * f x) hv,
    integral_gaussianReal_eq_integral_smul (f := f') hv]
  simp only [smul_eq_mul]
  rw [show (fun x : ℝ => gaussianPDFReal 0 var x * (x * f x))
        = fun x : ℝ => x * f x * gaussianPDFReal 0 var x from by funext x; ring,
    show (fun x : ℝ => gaussianPDFReal 0 var x * f' x)
        = fun x : ℝ => f' x * gaussianPDFReal 0 var x from by funext x; ring]
  exact h

/-! ### Integrability, so that the hypotheses become "continuous and bounded"

`MatrixStein` (T71, `RBM1D/Gauss/Generator.lean`) supplies its test functions as *continuous
and globally bounded*, not as integrable.  These three lemmas make the conversion, and the
only non-formal ingredient is the first absolute moment of a Gaussian. -/

/-- The first absolute moment of a centred Gaussian is finite. -/
theorem integrable_id_mul_gaussianPDFReal (hv : 0 < (var : ℝ)) :
    Integrable fun x : ℝ => x * gaussianPDFReal 0 var x := by
  have hb : (0 : ℝ) < 1 / (2 * (var : ℝ)) := by positivity
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)).const_mul
      ((Real.sqrt (2 * π * (var : ℝ)))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_one, gaussianPDFReal]
  rw [show -(1 / (2 * (var : ℝ))) * x ^ 2 = -(x - 0) ^ 2 / (2 * (var : ℝ)) by ring]
  ring

/-- A bounded measurable function times the Gaussian density is integrable. -/
theorem integrable_bdd_mul_gaussianPDFReal {f : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f MeasureTheory.volume) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable fun x : ℝ => f x * gaussianPDFReal 0 var x :=
  (integrable_gaussianPDFReal 0 var).bdd_mul hf (Filter.Eventually.of_forall hC)

/-- The third integrability hypothesis of `integral_mul_gaussianPDF`, from boundedness. -/
theorem integrable_bdd_mul_deriv_gaussianPDFReal (hv : 0 < (var : ℝ)) {f : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f MeasureTheory.volume) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x) := by
  have h := ((integrable_id_mul_gaussianPDFReal hv).bdd_mul hf
    (Filter.Eventually.of_forall hC)).const_mul (-(1 / (var : ℝ)))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  field_simp
  try ring

/-- **Stein's identity with the hypotheses `MatrixStein` actually supplies**: `f` is
differentiable with continuous derivative, and both `f` and `f'` are globally bounded. -/
theorem integral_mul_gaussianReal_of_bdd (hv : var ≠ 0) {f f' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var) = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  have hv' : (0 : ℝ) < (var : ℝ) :=
    lt_of_le_of_ne var.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  have hd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : AEStronglyMeasurable f MeasureTheory.volume :=
    hd.continuous.aestronglyMeasurable
  have hf'm : AEStronglyMeasurable f' MeasureTheory.volume := hf'c.aestronglyMeasurable
  exact integral_mul_gaussianReal hv hf
    (integrable_bdd_mul_deriv_gaussianPDFReal hv' hfm hb)
    (integrable_bdd_mul_gaussianPDFReal hf'm hb')
    (integrable_bdd_mul_gaussianPDFReal hfm hb)

/-! ### The complex-valued one-dimensional Stein identity

`MatrixStein` (T71, `RBM1D/Gauss/Generator.lean`) consumes `ℂ`-valued test functions.
Splitting into real and imaginary parts turns that into two applications of
`integral_mul_gaussianReal_of_bdd`; no new probability enters here. -/

/-- A bounded continuous function is integrable against a Gaussian, which is a probability
measure. -/
theorem integrable_of_bdd_gaussianReal {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} {C : ℝ} (hg : Continuous g) (hb : ∀ x, ‖g x‖ ≤ C) :
    Integrable g (gaussianReal 0 var) :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- The identity has a finite first absolute moment under a Gaussian. -/
theorem integrable_id_gaussianReal :
    Integrable (fun x : ℝ => x) (gaussianReal 0 var) := by
  have h : MemLp id 1 (gaussianReal (0 : ℝ) var) := by
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := var) 1
  exact memLp_one_iff_integrable.mp h

/-- `x · g x` is integrable against a Gaussian whenever `g` is continuous and bounded. -/
theorem integrable_ofReal_mul_gaussianReal {g : ℝ → ℂ} {C : ℝ}
    (hg : Continuous g) (hb : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x : ℝ => (x : ℂ) * g x) (gaussianReal 0 var) := by
  have h := (integrable_id_gaussianReal (var := var)).ofReal.bdd_mul
    hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa [mul_comm] using h

/-- **Stein's identity, `ℂ`-valued.**  This is exactly the shape `MatrixStein` asks for in a
single coordinate: `E[X f(X)] = v · E[f'(X)]` for a bounded `C¹` function `f : ℝ → ℂ`. -/
theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hre : ∀ x, HasDerivAt (fun y => (f y).re) (f' x).re x := fun x => by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simp only [Function.comp_def, Complex.reCLM_apply] at h
    exact h
  have him : ∀ x, HasDerivAt (fun y => (f y).im) (f' x).im x := fun x => by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simp only [Function.comp_def, Complex.imCLM_apply] at h
    exact h
  have hbre : ∀ x, ‖(f x).re‖ ≤ C := fun x =>
    le_trans (by simpa using Complex.abs_re_le_norm (f x)) (hb x)
  have hbim : ∀ x, ‖(f x).im‖ ≤ C := fun x =>
    le_trans (by simpa using Complex.abs_im_le_norm (f x)) (hb x)
  have hb're : ∀ x, ‖(f' x).re‖ ≤ C := fun x =>
    le_trans (by simpa using Complex.abs_re_le_norm (f' x)) (hb' x)
  have hb'im : ∀ x, ‖(f' x).im‖ ≤ C := fun x =>
    le_trans (by simpa using Complex.abs_im_le_norm (f' x)) (hb' x)
  have Hre := integral_mul_gaussianReal_of_bdd hv hre
    (Complex.continuous_re.comp hf'c) hbre hb're
  have Him := integral_mul_gaussianReal_of_bdd hv him
    (Complex.continuous_im.comp hf'c) hbim hb'im
  have hIl : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var) :=
    integrable_ofReal_mul_gaussianReal hfc hb
  have hIr : Integrable f' (gaussianReal 0 var) := integrable_of_bdd_gaussianReal hf'c hb'
  have hLre : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, x * (f x).re ∂(gaussianReal 0 var) := by
    simpa using (Complex.reCLM.integral_comp_comm hIl).symm
  have hLim : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, x * (f x).im ∂(gaussianReal 0 var) := by
    simpa using (Complex.imCLM.integral_comp_comm hIl).symm
  have hFre : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, (f' x).re ∂(gaussianReal 0 var) := by
    simpa using (Complex.reCLM.integral_comp_comm hIr).symm
  have hFim : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, (f' x).im ∂(gaussianReal 0 var) := by
    simpa using (Complex.imCLM.integral_comp_comm hIr).symm
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hLre, hFre]
    exact Hre
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hLim, hFim]
    exact Him


end RBM
