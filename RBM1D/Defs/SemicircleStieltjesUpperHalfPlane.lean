/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleStieltjesBridge
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
# The semicircle Stieltjes transform on the upper half-plane

The paper defines `m_sc(z)` by the density integral with kernel `(x-z)⁻¹`
immediately before (2.1). The density computation on the flow line, followed
by the identity theorem for the resolvent transform, identifies that integral
with the algebraically defined `RBM.msc` throughout the upper half-plane.
-/

namespace RBM

open MeasureTheory Complex Set

private def upperHalfPlane : Set ℂ := {z | 0 < z.im}

private noncomputable def semicircleStieltjesIntegral (z : ℂ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂semicircleMeasure

private noncomputable def semicircleFlowPoint (u : ℝ) : ℂ :=
  Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)

private noncomputable def semicircleStieltjesPolynomial (z : ℂ) : ℂ :=
  semicircleStieltjesIntegral z * (semicircleStieltjesIntegral z + z) + 1

private theorem semicircleStieltjesIntegral_eq_resolventTransform (z : ℂ) :
    semicircleStieltjesIntegral z = resolventTransform semicircleMeasure z := by
  unfold semicircleStieltjesIntegral resolventTransform resolvent
  simp only [Ring.inverse_eq_inv]
  congr 1

private theorem upperHalfPlane_disjoint_support {z : ℂ} (hz : z ∈ upperHalfPlane) :
    z ∉ (algebraMap ℝ ℂ '' semicircleMeasure.support) := by
  rintro ⟨x, -, rfl⟩
  simp [upperHalfPlane] at hz

/-- The paper-sign semicircle Stieltjes kernel is integrable for `Im z>0`. -/
theorem semicircleMeasure_stieltjes_integrable {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) semicircleMeasure := by
  have hz' : z ∈ upperHalfPlane := hz
  convert MeasureTheory.integrable_resolvent (μ := semicircleMeasure)
    (upperHalfPlane_disjoint_support hz') using 1
  funext x
  simp [resolvent, Ring.inverse_eq_inv]

private theorem semicircleStieltjesIntegral_analytic :
    AnalyticOnNhd ℂ semicircleStieltjesIntegral upperHalfPlane := by
  have hsub : upperHalfPlane ⊆
      (algebraMap ℝ ℂ '' semicircleMeasure.support)ᶜ := by
    intro z hz
    exact Set.mem_compl (upperHalfPlane_disjoint_support hz)
  have h := (MeasureTheory.analyticOn_resolventTransform
    (μ := semicircleMeasure)).mono hsub
  rw [show semicircleStieltjesIntegral =
    resolventTransform semicircleMeasure from funext
      semicircleStieltjesIntegral_eq_resolventTransform]
  exact h.differentiableOn.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im)

private theorem semicircleStieltjesPolynomial_analytic :
    AnalyticOnNhd ℂ semicircleStieltjesPolynomial upperHalfPlane := by
  unfold semicircleStieltjesPolynomial
  exact (semicircleStieltjesIntegral_analytic.mul
    (semicircleStieltjesIntegral_analytic.add analyticOnNhd_id)).add
      analyticOnNhd_const

private theorem semicircleFlowPoint_continuousAt_half :
    ContinuousAt semicircleFlowPoint (1/2 : ℝ) := by
  unfold semicircleFlowPoint
  fun_prop (disch := norm_num)

private theorem semicircleFlowPoint_ne_half {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (1 / 2)) :
    semicircleFlowPoint u ≠ semicircleFlowPoint (1 / 2 : ℝ) := by
  intro heq
  have hm := congrArg msc heq
  have hmu := msc_flow_value u hu.1 hu.2.le
  have hmh := msc_flow_value (1/2 : ℝ) (by norm_num) (by norm_num)
  change msc (Complex.I * (((1-u)/Real.sqrt u : ℝ) : ℂ)) =
    msc (Complex.I * (((1-(1/2:ℝ))/Real.sqrt (1/2:ℝ) : ℝ) : ℂ)) at hm
  rw [hmu, hmh] at hm
  have hs := congrArg Complex.im hm
  have hs' : Real.sqrt u = Real.sqrt (1/2:ℝ) := by
    simpa only [Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero, zero_add] using hs
  have huEq : u = (1 / 2 : ℝ) := by
    calc
      u = (Real.sqrt u)^2 := (Real.sq_sqrt hu.1.le).symm
      _ = (Real.sqrt (1/2:ℝ))^2 := by rw [hs']
      _ = (1/2:ℝ) := Real.sq_sqrt (by norm_num)
  exact (ne_of_lt hu.2) huEq

private theorem semicircleStieltjesPolynomial_flow_zero {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (1 / 2)) :
    semicircleStieltjesPolynomial (semicircleFlowPoint u) = 0 := by
  have hbridge := semicircleMeasure_stieltjes_flow u hu.1 hu.2.le
  change semicircleStieltjesIntegral (semicircleFlowPoint u) =
    msc (semicircleFlowPoint u) at hbridge
  unfold semicircleStieltjesPolynomial
  rw [hbridge]
  have h := msc_mul (semicircleFlowPoint u)
  linear_combination h

private theorem semicircleStieltjesPolynomial_flow_accumulation :
    semicircleFlowPoint (1/2 : ℝ) ∈
      closure ({z | semicircleStieltjesPolynomial z = 0} \
        {semicircleFlowPoint (1/2 : ℝ)}) := by
  have hcl : (1/2 : ℝ) ∈ closure (Ioo (0 : ℝ) (1/2)) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1/2)]
    norm_num
  have hImage : semicircleFlowPoint (1/2 : ℝ) ∈
      closure (semicircleFlowPoint '' Ioo (0 : ℝ) (1/2)) :=
    mem_closure_image semicircleFlowPoint_continuousAt_half hcl
  apply (closure_mono ?_) hImage
  rintro z ⟨u, hu, rfl⟩
  exact ⟨semicircleStieltjesPolynomial_flow_zero hu,
    semicircleFlowPoint_ne_half hu⟩

private theorem semicircleFlowPoint_half_mem_upperHalfPlane :
    semicircleFlowPoint (1/2 : ℝ) ∈ upperHalfPlane := by
  change 0 < (Complex.I * (((1-(1/2:ℝ))/Real.sqrt (1/2:ℝ) : ℝ) : ℂ)).im
  norm_num

/-- The paper-sign resolvent kernel separates the interior points zero and
one, and the semicircle measure gives positive mass to `(-1,1)`. -/
theorem semicircleMeasure_stieltjes_nontrivial_witness :
    0 < semicircleMeasure (Ioo (-1 : ℝ) 1) ∧
      ∀ z : ℂ, (((0 : ℝ) : ℂ) - z)⁻¹ ≠ (((1 : ℝ) : ℂ) - z)⁻¹ := by
  constructor
  · exact semicircleMeasure_nontrivial
  · intro z h
    have h' := inv_injective h
    have hfalse : (0 : ℂ) = 1 := by
      have h'' : (0 : ℂ) - z = (1 : ℂ) - z := by simpa using h'
      calc
        (0 : ℂ) = ((0 : ℂ) - z) + z := by ring
        _ = ((1 : ℂ) - z) + z := by rw [h'']
        _ = 1 := by ring
    exact zero_ne_one hfalse

/-- The density Stieltjes transform satisfies the semicircle quadratic
equation throughout the open upper half-plane. -/
theorem semicircleMeasure_stieltjes_mul {z : ℂ} (hz : 0 < z.im) :
    (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂semicircleMeasure) *
      ((∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂semicircleMeasure) + z) = -1 := by
  have hEq : EqOn semicircleStieltjesPolynomial (fun _ : ℂ => 0)
      upperHalfPlane :=
    semicircleStieltjesPolynomial_analytic.eqOn_of_preconnected_of_mem_closure
      analyticOnNhd_const (convex_halfSpace_im_gt 0).isPreconnected
      semicircleFlowPoint_half_mem_upperHalfPlane
      semicircleStieltjesPolynomial_flow_accumulation
  have hp := hEq (show z ∈ upperHalfPlane from hz)
  unfold semicircleStieltjesPolynomial semicircleStieltjesIntegral at hp
  simp only at hp
  linear_combination hp

/-- The density Stieltjes transform has strictly positive imaginary part in
the upper half-plane; the density measure has total mass one. -/
theorem semicircleMeasure_stieltjes_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂semicircleMeasure).im := by
  have hI := semicircleMeasure_stieltjes_integrable hz
  change 0 < RCLike.im (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂semicircleMeasure)
  rw [← integral_im hI]
  have hfpos (x : ℝ) : 0 < (((x : ℂ) - z)⁻¹).im := by
    rw [Complex.inv_im]
    have him : ((x : ℂ) - z).im = -z.im := by simp
    rw [him]
    have hnorm : 0 < Complex.normSq ((x : ℂ) - z) := by
      apply Complex.normSq_pos.mpr
      intro heq
      have heqim := congrArg Complex.im heq
      simp at heqim
      linarith
    simpa only [neg_neg] using (div_pos hz hnorm)
  have hrealint : Integrable (fun x : ℝ => (((x : ℂ) - z)⁻¹).im)
      semicircleMeasure := hI.im
  have hsupport : Function.support (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) =
      Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hfpos x)
  exact (integral_pos_iff_support_of_nonneg (fun x => (hfpos x).le)
    hrealint).2 (by
      rw [hsupport, semicircleMeasure_univ]
      norm_num)

/-- On `Im z>0`, the paper's semicircle density integral with kernel
`(x-z)⁻¹` equals the algebraic root `RBM.msc z`. -/
theorem semicircleMeasure_stieltjes_upperHalfPlane {z : ℂ} (hz : 0 < z.im) :
    (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂semicircleMeasure) = msc z := by
  exact eq_msc_of_mul_im_pos hz (semicircleMeasure_stieltjes_mul hz)
    (semicircleMeasure_stieltjes_im_pos hz)

#print axioms semicircleMeasure_stieltjes_integrable
#print axioms semicircleMeasure_stieltjes_nontrivial_witness
#print axioms semicircleMeasure_stieltjes_mul
#print axioms semicircleMeasure_stieltjes_im_pos
#print axioms semicircleMeasure_stieltjes_upperHalfPlane

end RBM
