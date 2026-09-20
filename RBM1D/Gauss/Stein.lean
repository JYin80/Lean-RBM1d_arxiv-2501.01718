/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

end RBM
