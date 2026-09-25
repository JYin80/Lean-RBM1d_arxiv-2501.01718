/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleStieltjesBridge

/-!
# The semicircle density Stieltjes transform on the positive imaginary axis

The paper defines its transform with the kernel `(x-z)⁻¹` immediately before
(2.1). Here `z=i y` for every `y>0`, using the explicit density measure.
-/

namespace RBM
open MeasureTheory Real Complex

private noncomputable def kern (u x : ℝ) : ℂ :=
  ((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)

private theorem kern_re (u x : ℝ) : (kern u x).re = Real.sqrt u * x := by
  simp [kern]
private theorem kern_im (u x : ℝ) : (kern u x).im = -(1-u) := by
  simp [kern]
private theorem kern_normSq (u x : ℝ) (hu : 0 ≤ u) :
    Complex.normSq (kern u x) = u*x^2 + (1-u)^2 := by
  rw [Complex.normSq_apply, kern_re, kern_im]
  calc
    _ = (Real.sqrt u)^2 * x^2 + (1-u)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hu]

private theorem kern_inv_re (u x : ℝ) (hu : 0 ≤ u) :
    ((kern u x)⁻¹).re = Real.sqrt u * x / (u*x^2+(1-u)^2) := by
  rw [Complex.inv_re, kern_re, kern_normSq u x hu]
private theorem kern_inv_im (u x : ℝ) (hu : 0 ≤ u) :
    ((kern u x)⁻¹).im = (1-u) / (u*x^2+(1-u)^2) := by
  rw [Complex.inv_im, kern_im, kern_normSq u x hu]
  ring

private theorem kern_norm_gap (u x : ℝ) (hu : u ≤ 1) :
    1-u ≤ ‖kern u x‖ := by
  have hb : 0 ≤ 1-u := by linarith
  have h := Complex.abs_im_le_norm (kern u x)
  rw [kern_im, abs_neg, abs_of_nonneg hb] at h
  exact h

private theorem kern_inv_norm_bound (u x : ℝ) (hu : u < 1) :
    ‖(kern u x)⁻¹‖ ≤ (1-u)⁻¹ := by
  have hb : 0 < 1-u := by linarith
  have hn := kern_norm_gap u x (le_of_lt hu)
  rw [norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le hb hn) hb).2 hn

private theorem kern_inv_integrable (u : ℝ) (hu : u < 1) :
    Integrable (fun x : ℝ => (kern u x)⁻¹) semicircleMeasure := by
  have hb : 0 < 1-u := by linarith
  have hne (x : ℝ) : kern u x ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [kern_im] at him
    simp at him
    linarith
  have hcont : Continuous (fun x : ℝ => (kern u x)⁻¹) := by
    have hk : Continuous (fun x : ℝ => kern u x) := by
      unfold kern
      fun_prop
    exact hk.inv₀ hne
  apply Integrable.of_bound hcont.aestronglyMeasurable ((1-u)⁻¹)
  filter_upwards [] with x
  exact kern_inv_norm_bound u x hu

private theorem real_part_integral_zero (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    (∫ x : ℝ, Real.sqrt u * x / (u*x^2+(1-u)^2) ∂semicircleMeasure) = 0 := by
  let f : ℝ → ℝ := fun x => Real.sqrt u * x / (u*x^2+(1-u)^2)
  have hi : Integrable f semicircleMeasure := by
    convert (kern_inv_integrable u hu1).re using 1
    funext x
    exact (kern_inv_re u x hu).symm
  have hmap := integral_map (μ := semicircleMeasure) (φ := fun x : ℝ => -x)
    measurable_neg.aemeasurable (by
      simpa only [semicircleMeasure_map_neg] using hi.aestronglyMeasurable)
  rw [semicircleMeasure_map_neg] at hmap
  have hfneg (x : ℝ) : f (-x) = -f x := by
    dsimp [f]
    rw [neg_sq]
    ring
  simp_rw [hfneg, integral_neg] at hmap
  linarith

/-- The density integral of the full complex flow kernel is `i` throughout
`0<u<1`. This reconstructs its odd real and Poisson imaginary parts. -/
theorem semicircleFlowResolvent_integral_full (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (∫ x : ℝ,
      (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹
        ∂semicircleMeasure) = Complex.I := by
  have hrei : (∫ x : ℝ, ((kern u x)⁻¹).re ∂semicircleMeasure) = 0 := by
    simp_rw [kern_inv_re u _ hu0.le]
    exact real_part_integral_zero u hu0.le hu1
  have himi : (∫ x : ℝ, ((kern u x)⁻¹).im ∂semicircleMeasure) = 1 := by
    simp_rw [kern_inv_im u _ hu0.le]
    exact semicircleMeasure_flow_poisson u hu0 hu1
  have h := integral_re_add_im (kern_inv_integrable u hu1)
  change ((∫ x : ℝ, ((kern u x)⁻¹).re ∂semicircleMeasure : ℝ) : ℂ) +
      ((∫ x : ℝ, ((kern u x)⁻¹).im ∂semicircleMeasure : ℝ) : ℂ) * Complex.I =
      ∫ x : ℝ, (kern u x)⁻¹ ∂semicircleMeasure at h
  rw [hrei, himi] at h
  simpa [kern] using h.symm

/-- The exact quadratic parameter for an arbitrary height `y>0`. -/
noncomputable def semicircleImagRadius (y : ℝ) : ℝ :=
  (Real.sqrt (y^2+4)-y)/2

/-- The radius is positive, strictly below one, and solves the quadratic. -/
theorem semicircleImagRadius_spec (y : ℝ) (hy : 0 < y) :
    0 < semicircleImagRadius y ∧ semicircleImagRadius y < 1 ∧
    (semicircleImagRadius y)^2 + y*semicircleImagRadius y = 1 := by
  have hs0 : 0 ≤ y^2+4 := by positivity
  have hs2 : (Real.sqrt (y^2+4))^2 = y^2+4 := Real.sq_sqrt hs0
  have hsnon : 0 ≤ Real.sqrt (y^2+4) := Real.sqrt_nonneg _
  have hsy : y < Real.sqrt (y^2+4) := by nlinarith
  have hsup : Real.sqrt (y^2+4) < y+2 := by nlinarith
  dsimp [semicircleImagRadius]
  constructor; · linarith
  constructor; · linarith
  nlinarith

/-- The flow parameter `u=r²` lies in `(0,1)` and gives `y=(1-u)/√u`. -/
theorem semicircleImagRadius_flow_parameter (y : ℝ) (hy : 0 < y) :
    let u := (semicircleImagRadius y)^2
    0 < u ∧ u < 1 ∧ (1-u)/Real.sqrt u = y := by
  obtain ⟨hr0,hr1,hrq⟩ := semicircleImagRadius_spec y hy
  dsimp
  have hu0 : 0 < (semicircleImagRadius y)^2 := sq_pos_of_pos hr0
  have hu1 : (semicircleImagRadius y)^2 < 1 := by nlinarith
  have hsqrt : Real.sqrt ((semicircleImagRadius y)^2) =
      semicircleImagRadius y :=
    (Real.sqrt_sq_eq_abs _).trans (abs_of_pos hr0)
  refine ⟨hu0, hu1, ?_⟩
  rw [hsqrt]
  field_simp
  nlinarith

/-- The algebraic `msc(i y)` is the positive imaginary quadratic root. -/
theorem msc_imaginary_axis_value (y : ℝ) (hy : 0 < y) :
    msc (Complex.I * (y : ℂ)) =
      Complex.I * (semicircleImagRadius y : ℂ) := by
  obtain ⟨hr0, -, hrq⟩ := semicircleImagRadius_spec y hy
  have hz : 0 < (Complex.I * (y : ℂ)).im := by simpa using hy
  have hmim : 0 < (Complex.I * (semicircleImagRadius y : ℂ)).im := by
    simpa using hr0
  symm
  apply eq_msc_of_mul_im_pos hz ?_ hmim
  calc
    (Complex.I * (semicircleImagRadius y : ℂ)) *
        (Complex.I * (semicircleImagRadius y : ℂ) + Complex.I * (y : ℂ)) =
      - ((semicircleImagRadius y : ℂ) *
          ((semicircleImagRadius y : ℂ) + (y : ℂ))) := by
            rw [show (Complex.I * (semicircleImagRadius y : ℂ)) *
                (Complex.I * (semicircleImagRadius y : ℂ) + Complex.I * (y : ℂ)) =
                (Complex.I * Complex.I) *
                ((semicircleImagRadius y : ℂ) *
                  ((semicircleImagRadius y : ℂ) + (y : ℂ))) by ring]
            rw [Complex.I_mul_I]
            ring
    _ = -1 := by
      have hreal : semicircleImagRadius y *
          (semicircleImagRadius y + y) = 1 := by nlinarith [hrq]
      calc
        _ = - ((semicircleImagRadius y *
            (semicircleImagRadius y + y) : ℝ) : ℂ) := by push_cast; ring
        _ = -1 := by rw [hreal]; norm_num

/-- The denominator of the paper-sign kernel has norm at least `y>0`. -/
theorem semicircleMeasure_stieltjes_imagAxis_denominator_gap
    (y x : ℝ) (hy : 0 < y) :
    y ≤ ‖(x : ℂ) - Complex.I * (y : ℂ)‖ := by
  have h := Complex.abs_im_le_norm ((x : ℂ) - Complex.I * (y : ℂ))
  simpa [abs_of_pos hy] using h

/-- The paper-sign `(x-i y)⁻¹` kernel is integrable for every `y>0`. -/
theorem semicircleMeasure_stieltjes_imagAxis_integrable (y : ℝ) (hy : 0 < y) :
    Integrable (fun x : ℝ => ((x : ℂ) - Complex.I * (y : ℂ))⁻¹)
      semicircleMeasure := by
  let u := (semicircleImagRadius y)^2
  obtain ⟨hu0, hu1, hparam⟩ := semicircleImagRadius_flow_parameter y hy
  have hflow := (kern_inv_integrable u hu1).const_mul
    ((Real.sqrt u : ℝ) : ℂ)
  convert hflow using 1
  funext x
  rw [← hparam]
  exact semicircleMeasure_stieltjes_flow_kernel_scale u x hu0

/-- The explicit semicircle density Stieltjes integral equals the algebraic
`msc(i y)` for every positive imaginary height, with the paper's sign. -/
theorem semicircleMeasure_stieltjes_imagAxis (y : ℝ) (hy : 0 < y) :
    (∫ x : ℝ, ((x : ℂ) - Complex.I * (y : ℂ))⁻¹ ∂semicircleMeasure) =
      msc (Complex.I * (y : ℂ)) := by
  let u := (semicircleImagRadius y)^2
  obtain ⟨hu0, hu1, hparam⟩ := semicircleImagRadius_flow_parameter y hy
  have hroot : Real.sqrt u = semicircleImagRadius y := by
    exact (Real.sqrt_sq_eq_abs _).trans
      (abs_of_pos (semicircleImagRadius_spec y hy).1)
  calc
    (∫ x : ℝ, ((x : ℂ) - Complex.I * (y : ℂ))⁻¹ ∂semicircleMeasure)
      = ∫ x : ℝ, ((Real.sqrt u : ℝ) : ℂ) *
          ((((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹)
          ∂semicircleMeasure := by
            congr 1
            funext x
            rw [← hparam]
            exact semicircleMeasure_stieltjes_flow_kernel_scale u x hu0
    _ = ((Real.sqrt u : ℝ) : ℂ) * Complex.I := by
      rw [integral_const_mul, semicircleFlowResolvent_integral_full u hu0 hu1]
    _ = msc (Complex.I * (y : ℂ)) := by
      rw [msc_imaginary_axis_value y hy, hroot]
      ring

/-- At `y=1/2`, the flow parameter exceeds `1/2`; this is outside the
narrow T890 theorem. -/
theorem semicircleImagRadius_half_parameter_gt_half :
    (1/2 : ℝ) < (semicircleImagRadius (1/2))^2 := by
  obtain ⟨hr0, hr1, hrq⟩ := semicircleImagRadius_spec (1/2) (by norm_num)
  have hs : Real.sqrt (1/2 : ℝ) < semicircleImagRadius (1/2) := by
    have hroot0 : 0 ≤ Real.sqrt (1/2 : ℝ) := Real.sqrt_nonneg _
    have hroot2 : Real.sqrt (1/2 : ℝ)^2 = 1/2 := by
      rw [Real.sq_sqrt (by norm_num)]
    nlinarith
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1/2 by norm_num)]

/-- A pointwise witness that the ordinary kernel at `y=1/2` is nonconstant. -/
theorem semicircleMeasure_stieltjes_imagAxis_half_nonconstant :
    ((((0:ℝ) : ℂ) - Complex.I * ((1/2:ℝ) : ℂ))⁻¹) ≠
      ((((1:ℝ) : ℂ) - Complex.I * ((1/2:ℝ) : ℂ))⁻¹) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.inv_re, Complex.normSq_apply] at hre

/-- A concrete positive height beyond the range of the earlier flow bridge. -/
theorem semicircleMeasure_stieltjes_imagAxis_half :
    (∫ x : ℝ, ((x : ℂ) - Complex.I * ((1/2 : ℝ) : ℂ))⁻¹
      ∂semicircleMeasure) =
      msc (Complex.I * ((1/2 : ℝ) : ℂ)) :=
  semicircleMeasure_stieltjes_imagAxis (1/2) (by norm_num)

#print axioms semicircleFlowResolvent_integral_full
#print axioms semicircleImagRadius
#print axioms semicircleImagRadius_spec
#print axioms semicircleImagRadius_flow_parameter
#print axioms msc_imaginary_axis_value
#print axioms semicircleMeasure_stieltjes_imagAxis_denominator_gap
#print axioms semicircleMeasure_stieltjes_imagAxis_integrable
#print axioms semicircleMeasure_stieltjes_imagAxis
#print axioms semicircleImagRadius_half_parameter_gt_half
#print axioms semicircleMeasure_stieltjes_imagAxis_half_nonconstant
#print axioms semicircleMeasure_stieltjes_imagAxis_half

end RBM
