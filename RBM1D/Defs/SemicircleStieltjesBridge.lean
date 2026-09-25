/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleFlowResolvent

/-!
# The semicircle density Stieltjes transform on the flow line

The paper defines the transform with kernel `(x-z)⁻¹` immediately before
(2.1). This module identifies that density integral with the algebraic
`RBM.msc` at `z = i(1-u)/√u`, for `0 < u ≤ 1/2`. The parameter `u=0` is
excluded because this finite spectral parameter is undefined there.
-/

namespace RBM

open Complex MeasureTheory

/-- In the upper half-plane, a root of `m(m+z)=-1` with positive imaginary
part is the selected algebraic root `msc z`. -/
theorem eq_msc_of_mul_im_pos {z m : ℂ} (hz : 0 < z.im)
    (hm : m * (m + z) = -1) (hmi : 0 < m.im) : m = msc z := by
  have hmsc := msc_mul z
  have hfact : (m - msc z) * (m + msc z + z) = 0 := by
    linear_combination hm - hmsc
  rcases mul_eq_zero.mp hfact with h | h
  · exact sub_eq_zero.mp h
  · have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im] at hi
    have hpos := msc_im_pos hz
    linarith

/-- The algebraic semicircle transform along the positive flow line is
`i√u`. -/
theorem msc_flow_value (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    msc (Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)) =
      Complex.I * ((Real.sqrt u : ℝ) : ℂ) := by
  have ha : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have ha2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hb : 0 < 1-u := by linarith
  have hr : Real.sqrt u * (Real.sqrt u + (1-u)/Real.sqrt u) = 1 := by
    field_simp
    nlinarith
  have hz : 0 < (Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)).im := by
    simpa using div_pos hb ha
  have him : 0 < (Complex.I * ((Real.sqrt u : ℝ) : ℂ)).im := by
    simpa using ha
  symm
  apply eq_msc_of_mul_im_pos hz ?_ him
  calc
    (Complex.I * ((Real.sqrt u : ℝ) : ℂ)) *
       (Complex.I * ((Real.sqrt u : ℝ) : ℂ) +
        Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))
      = - ((Real.sqrt u : ℂ) * ((Real.sqrt u : ℂ) +
          (((1-u)/Real.sqrt u : ℝ) : ℂ))) := by
        rw [show (Complex.I * (Real.sqrt u : ℂ)) *
           (Complex.I * (Real.sqrt u : ℂ) +
            Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)) =
              (Complex.I * Complex.I) *
              ((Real.sqrt u : ℂ) * ((Real.sqrt u : ℂ) +
                (((1-u)/Real.sqrt u : ℝ) : ℂ))) by ring]
        rw [Complex.I_mul_I]
        ring
    _ = -1 := by
      norm_cast
      rw [hr]
      norm_num

/-- Pointwise scaling from the ordinary Stieltjes kernel to T873's flow
kernel. -/
theorem semicircleMeasure_stieltjes_flow_kernel_scale (u x : ℝ) (hu : 0 < u) :
    (((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))⁻¹) =
      ((Real.sqrt u : ℝ) : ℂ) *
        ((((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹) := by
  have ha : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have haC : (((Real.sqrt u : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hden : (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)) =
      ((Real.sqrt u : ℝ) : ℂ) *
        ((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)) := by
    push_cast
    field_simp
  rw [hden, mul_inv_rev]
  calc
    (((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))⁻¹)
      = (((Real.sqrt u : ℝ) : ℂ) * (((Real.sqrt u : ℝ) : ℂ)⁻¹)) *
         (((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))⁻¹) := by
           rw [mul_inv_cancel₀ haC, one_mul]
    _ = _ := by ring

/-- The ordinary `(x-z)⁻¹` kernel is integrable against the semicircle
density measure at the flow spectral parameter. -/
theorem semicircleMeasure_stieltjes_flow_integrable (u : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    Integrable (fun x : ℝ =>
      (((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))⁻¹))
      semicircleMeasure := by
  have h := semicircleFlowResolvent_integrable u hu1
  have hscale (x : ℝ) := semicircleMeasure_stieltjes_flow_kernel_scale u x hu
  have hmul := h.const_mul ((Real.sqrt u : ℝ) : ℂ)
  convert hmul using 1
  funext x
  exact hscale x

/-- The paper-sign semicircle Stieltjes integral equals the algebraic `msc`
on the flow line `z = i(1-u)/√u`, for `0 < u ≤ 1/2`. -/
theorem semicircleMeasure_stieltjes_flow (u : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    (∫ x : ℝ,
      (((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))⁻¹)
        ∂semicircleMeasure) =
      msc (Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)) := by
  calc
    (∫ x : ℝ,
      (((x : ℂ) - Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ))⁻¹)
        ∂semicircleMeasure)
      = ∫ x : ℝ, ((Real.sqrt u : ℝ) : ℂ) *
          ((((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹)
            ∂semicircleMeasure := by
              congr 1
              funext x
              exact semicircleMeasure_stieltjes_flow_kernel_scale u x hu
    _ = ((Real.sqrt u : ℝ) : ℂ) * Complex.I := by
      rw [integral_const_mul, semicircleFlowResolvent_integral u hu.le hu1]
    _ = msc (Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)) := by
      rw [msc_flow_value u hu hu1]
      ring

/-- The `u=1/2` flow resolvent kernel is nonconstant (its values at zero and
one differ). -/
theorem semicircleStieltjesFlow_half_nonconstant :
    ((((Real.sqrt (1 / 2 : ℝ) * (0 : ℝ) : ℝ) : ℂ) -
      Complex.I * ((1 - (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹) ≠
    ((((Real.sqrt (1 / 2 : ℝ) * (1 : ℝ) : ℝ) : ℂ) -
      Complex.I * ((1 - (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹) :=
  semicircleFlowResolvent_half_nonconstant

#print axioms eq_msc_of_mul_im_pos
#print axioms msc_flow_value
#print axioms semicircleMeasure_stieltjes_flow_kernel_scale
#print axioms semicircleMeasure_stieltjes_flow_integrable
#print axioms semicircleMeasure_stieltjes_flow
#print axioms semicircleStieltjesFlow_half_nonconstant

end RBM
