/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicirclePoissonIntegral

/-!
# The semicircle density resolvent on the flow line

The paper defines its Stieltjes transform using `(x - z)⁻¹` immediately before
(2.1). This file evaluates the corresponding density integral on the flow line;
it does not identify that integral with the algebraic `RBM.msc`.
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

private theorem kern_integral_zero :
    (∫ x : ℝ, (kern 0 x)⁻¹ ∂semicircleMeasure) = Complex.I := by
  have hpoint (x : ℝ) : (kern 0 x)⁻¹ = Complex.I := by
    simp [kern]
  simp_rw [hpoint]
  simp

private theorem kern_integral (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    (∫ x : ℝ, (kern u x)⁻¹ ∂semicircleMeasure) = Complex.I := by
  by_cases hzero : u = 0
  · subst u
    exact kern_integral_zero
  have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
  have hlt : u < 1 := lt_of_le_of_lt hu1 (by norm_num)
  have hrei : (∫ x : ℝ, ((kern u x)⁻¹).re ∂semicircleMeasure) = 0 := by
    simp_rw [kern_inv_re u _ hu0]
    exact real_part_integral_zero u hu0 hlt
  have himi : (∫ x : ℝ, ((kern u x)⁻¹).im ∂semicircleMeasure) = 1 := by
    simp_rw [kern_inv_im u _ hu0]
    exact semicircleMeasure_flow_poisson u hu hlt
  have h := integral_re_add_im (kern_inv_integrable u hlt)
  change ((∫ x : ℝ, ((kern u x)⁻¹).re ∂semicircleMeasure : ℝ) : ℂ) +
      ((∫ x : ℝ, ((kern u x)⁻¹).im ∂semicircleMeasure : ℝ) : ℂ) * Complex.I =
      ∫ x : ℝ, (kern u x)⁻¹ ∂semicircleMeasure at h
  rw [hrei, himi] at h
  simpa using h.symm

private theorem kern_half_zero : (kern (1 / 2) 0)⁻¹ = 2 * Complex.I := by
  norm_num [kern]

private theorem kern_half_nonconstant :
    (kern (1 / 2) 0)⁻¹ ≠ (kern (1 / 2) 1)⁻¹ := by
  intro h
  have hre := congrArg Complex.re h
  rw [kern_inv_re (1 / 2) 0 (by norm_num),
      kern_inv_re (1 / 2) 1 (by norm_num)] at hre
  have hpos : 0 < Real.sqrt (1 / 2 : ℝ) /
      ((1 / 2 : ℝ) * 1 ^ 2 + (1 - 1 / 2) ^ 2) := by
    positivity
  simp only [mul_zero, zero_div, mul_one] at hre
  exact (ne_of_gt hpos) hre.symm

/-- The denominator has a gap of at least `1-u` along the flow line. -/
theorem semicircleFlowResolvent_denominator_gap (u x : ℝ) (hu : u ≤ 1 / 2) :
    1-u ≤ ‖((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)‖ := by
  exact kern_norm_gap u x (by linarith : u ≤ 1)

/-- The complex density resolvent kernel is integrable for `u ∈ [0,1 / 2]`. -/
theorem semicircleFlowResolvent_integrable (u : ℝ) (hu : u ≤ 1 / 2) :
    Integrable (fun x : ℝ =>
      (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹)
      semicircleMeasure :=
  kern_inv_integrable u (by linarith)

/-- The endpoint `u=0` is a constant integral. -/
theorem semicircleFlowResolvent_zero :
    (∫ x : ℝ,
      (((Real.sqrt (0:ℝ) * x : ℝ) : ℂ) - Complex.I * ((1-(0:ℝ) : ℝ) : ℂ))⁻¹
      ∂semicircleMeasure) = Complex.I :=
  kern_integral_zero

/-- The endpoint `u=1 / 2` is a nonconstant density integral. -/
theorem semicircleFlowResolvent_half :
    (∫ x : ℝ,
      (((Real.sqrt (1 / 2:ℝ) * x : ℝ) : ℂ) - Complex.I * ((1-(1 / 2:ℝ) : ℝ) : ℂ))⁻¹
      ∂semicircleMeasure) = Complex.I :=
  kern_integral (1 / 2) (by norm_num) (by norm_num)

/-- The actual pointwise kernel at `u=1 / 2`, `x=0` equals `2i`. -/
theorem semicircleFlowResolvent_half_at_zero :
    ((((Real.sqrt (1 / 2:ℝ) * (0:ℝ) : ℝ) : ℂ) -
      Complex.I * ((1-(1 / 2:ℝ) : ℝ) : ℂ))⁻¹) = 2 * Complex.I :=
  kern_half_zero

/-- At `u=1/2`, the values at `x=0` and `x=1` are distinct. -/
theorem semicircleFlowResolvent_half_nonconstant :
    ((((Real.sqrt (1 / 2 : ℝ) * (0 : ℝ) : ℝ) : ℂ) -
      Complex.I * ((1 - (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹) ≠
    ((((Real.sqrt (1 / 2 : ℝ) * (1 : ℝ) : ℝ) : ℂ) -
      Complex.I * ((1 - (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹) :=
  kern_half_nonconstant

/-- The semicircle density integral of the `(x-z)⁻¹` resolvent on the flow line. -/
theorem semicircleFlowResolvent_integral (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    (∫ x : ℝ,
      (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹
      ∂semicircleMeasure) = Complex.I := by
  by_cases hzero : u = 0
  · subst u
    exact semicircleFlowResolvent_zero
  by_cases hhalf : u = 1 / 2
  · subst u
    exact semicircleFlowResolvent_half
  exact kern_integral u hu0 hu1

#print axioms semicircleFlowResolvent_denominator_gap
#print axioms semicircleFlowResolvent_integrable
#print axioms semicircleFlowResolvent_zero
#print axioms semicircleFlowResolvent_half
#print axioms semicircleFlowResolvent_half_at_zero
#print axioms semicircleFlowResolvent_half_nonconstant
#print axioms semicircleFlowResolvent_integral

end RBM
