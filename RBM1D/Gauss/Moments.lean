/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Stein

/-!
# Moments of a centred real Gaussian

The even moments, from the one-dimensional Stein identity of `Gauss/Stein.lean`:
taking `f x = x^{2p+1}` in `E[X f(X)] = v E[f'(X)]` gives the recursion

  `E[X^{2p+2}] = (2p+1) · v · E[X^{2p}]`,

hence `E[X^{2p}] = (2p-1)!! · v^p`.  This is the deterministic input of the large deviation
estimates of T81/T82: conditionally on the other coordinates, the linear form
`∑_k H_{ik} X_k` is a centred Gaussian, and its moments are read off from this formula.

## Main statements

* `RBM.integrable_pow_gaussianReal` : all polynomial moments exist
* `RBM.integral_pow_gaussianReal_succ` : the Stein recursion
* `RBM.integral_pow_gaussianReal` : `E[X^{2p}] = (∏_{i<p} (2i+1)) v^p`, valid also at `v = 0`
-/

namespace RBM

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

section Moments

/-- Every polynomial is integrable against a real Gaussian. -/
theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Transfer integrability from the Gaussian measure to the density form used by
`RBM.integral_mul_gaussianReal`. -/
theorem integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

/-- **The Stein recursion for the even moments**: `E[X^{2p+2}] = (2p+1) v E[X^{2p}]`. -/
theorem integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv
      ((integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv (integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- **The even moments of a centred real Gaussian**: `E[X^{2p}] = (2p-1)!!·v^p`, with the
double factorial written as `∏_{i<p} (2i+1)`. -/
theorem integral_pow_gaussianReal (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v)
      = (∏ i ∈ range p, (2 * (i : ℝ) + 1)) * (v : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, integral_pow_gaussianReal_succ, ih,
      prod_range_succ]
    ring

end Moments

end RBM
