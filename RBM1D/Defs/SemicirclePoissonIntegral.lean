/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleDensityMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The semicircle Poisson integral -/

namespace RBM

open MeasureTheory Set Real

private noncomputable def phi (t : ℝ) : ℝ := 2 * t / Real.sqrt (1 + t ^ 2)
private noncomputable def phiDeriv (t : ℝ) : ℝ := 2 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))

private theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity
private theorem sqrt_one_add_sq_pos (t : ℝ) :
    0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (one_add_sq_pos t)

private theorem phi_hasDerivAt (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hnum : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    convert (hasDerivAt_id t).const_mul 2 using 1 <;> simp
  have hden : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2))
      ((2 * t) / (2 * Real.sqrt (1 + t ^ 2))) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt (one_add_sq_pos t))).comp t
      ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2)) using 1
      <;> simp [Function.comp_def, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc]
  have h := hnum.div hden (ne_of_gt (sqrt_one_add_sq_pos t))
  have heq : (2 * Real.sqrt (1 + t ^ 2) -
      2 * t * (2 * t / (2 * Real.sqrt (1 + t ^ 2)))) /
      (Real.sqrt (1 + t ^ 2)) ^ 2 = phiDeriv t := by
    unfold phiDeriv
    have hs : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
      Real.sq_sqrt (le_of_lt (one_add_sq_pos t))
    field_simp
    nlinarith [hs]
  rw [heq] at h
  exact h

private theorem phi_sq (t : ℝ) : phi t ^ 2 = 4 * t ^ 2 / (1 + t ^ 2) := by
  unfold phi
  rw [div_pow, Real.sq_sqrt (le_of_lt (one_add_sq_pos t))]
  ring

private theorem phi_mem_Ioo (t : ℝ) : phi t ∈ Ioo (-2 : ℝ) 2 := by
  have hp := one_add_sq_pos t
  have hs := phi_sq t
  have hlt : phi t ^ 2 < 4 := by
    rw [hs]
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  constructor <;> nlinarith

private theorem phi_strictMono : StrictMono phi := by
  apply strictMono_of_hasDerivAt_pos phi_hasDerivAt
  intro t
  unfold phiDeriv
  positivity

private theorem phi_image_univ : phi '' (Set.univ : Set ℝ) = Ioo (-2 : ℝ) 2 := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨t, -, rfl⟩
    exact phi_mem_Ioo t
  · intro x hx
    have hx4 : 0 < 4 - x ^ 2 := by
      rcases hx with ⟨hl, hr⟩
      nlinarith
    let t := x / Real.sqrt (4 - x ^ 2)
    have ht : 0 < Real.sqrt (4 - x ^ 2) := Real.sqrt_pos.2 hx4
    have htsq : t ^ 2 = x ^ 2 / (4 - x ^ 2) := by
      dsimp [t]
      rw [div_pow, Real.sq_sqrt (le_of_lt hx4)]
    have h1 : 1 + t ^ 2 = 4 / (4 - x ^ 2) := by
      rw [htsq]
      field_simp
      ring
    have hsqrt : Real.sqrt (1 + t ^ 2) = 2 / Real.sqrt (4 - x ^ 2) := by
      have hq : (2 / Real.sqrt (4 - x ^ 2)) ^ 2 = 1 + t ^ 2 := by
        rw [h1, div_pow, Real.sq_sqrt (le_of_lt hx4)]
        field_simp
        norm_num
      have hright : 0 ≤ 2 / Real.sqrt (4 - x ^ 2) := by positivity
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hright).mp
      rw [Real.sq_sqrt (le_of_lt (one_add_sq_pos t)), hq]
    refine ⟨t, trivial, ?_⟩
    unfold phi
    rw [hsqrt]
    dsimp [t]
    field_simp

private theorem phi_sqrt_density (t : ℝ) :
    Real.sqrt (4 - phi t ^ 2) = 2 / Real.sqrt (1 + t ^ 2) := by
  have hsq : 4 - phi t ^ 2 = 4 / (1 + t ^ 2) := by
    rw [phi_sq]
    field_simp
    ring
  have ht := one_add_sq_pos t
  have hs := sqrt_one_add_sq_pos t
  have hp : 0 < 4 - phi t ^ 2 := by rw [hsq]; positivity
  have hr : 0 ≤ 2 / Real.sqrt (1 + t ^ 2) := by positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hr).mp
  rw [Real.sq_sqrt (le_of_lt hp), hsq, div_pow, Real.sq_sqrt (le_of_lt ht)]
  norm_num

private theorem phi_density_jacobian (t : ℝ) :
    phiDeriv t * semicircleDensity (phi t) =
      2 / (Real.pi * (1 + t ^ 2) ^ 2) := by
  rw [semicircleDensity, phi_sqrt_density]
  unfold phiDeriv
  have hs : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (le_of_lt (one_add_sq_pos t))
  have hne : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt (sqrt_one_add_sq_pos t)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith [hs]

private theorem integrable_inv_scaled (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Integrable (fun t : ℝ => (b ^ 2 + (c * t) ^ 2)⁻¹) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hk : c / b ≠ 0 := div_ne_zero (ne_of_gt hc) hb0
  have hfun : (fun t : ℝ => (b ^ 2 + (c * t) ^ 2)⁻¹) =
      fun t => b⁻¹ ^ 2 * (1 + ((c / b) * t) ^ 2)⁻¹ := by
    funext t
    have hd : b ^ 2 + (c * t) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hfun]
  exact (integrable_inv_one_add_mul_sq hk).const_mul _

private theorem integral_inv_scaled (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (∫ t : ℝ, (b ^ 2 + (c * t) ^ 2)⁻¹) = Real.pi / (b * c) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hfun : (fun t : ℝ => (b ^ 2 + (c * t) ^ 2)⁻¹) =
      fun t => b⁻¹ ^ 2 * (1 + ((c / b) * t) ^ 2)⁻¹ := by
    funext t
    have hd : b ^ 2 + (c * t) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hfun, integral_const_mul, integral_univ_inv_one_add_mul_sq]
  rw [abs_of_pos (div_pos hc hb)]
  field_simp

private theorem integral_rational (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    (∫ t : ℝ, ((1 + t ^ 2) * (b ^ 2 + (c * t) ^ 2))⁻¹) =
      Real.pi / (b * (b + c)) := by
  have hc : 0 < c := lt_trans hb hbc
  have hd : c ^ 2 - b ^ 2 ≠ 0 := by nlinarith
  have hfun : (fun t : ℝ => ((1 + t ^ 2) * (b ^ 2 + (c * t) ^ 2))⁻¹) =
      fun t => (c ^ 2 - b ^ 2)⁻¹ *
        (c ^ 2 * (b ^ 2 + (c * t) ^ 2)⁻¹ - (1 + t ^ 2)⁻¹) := by
    funext t
    have h1 : 1 + t ^ 2 ≠ 0 := ne_of_gt (one_add_sq_pos t)
    have h2 : b ^ 2 + (c * t) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hfun, integral_const_mul, integral_sub
    ((integrable_inv_scaled b c hb hc).const_mul _) integrable_inv_one_add_sq,
    integral_const_mul, integral_inv_scaled b c hb hc,
    integral_univ_inv_one_add_sq]
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hsum : b + c ≠ 0 := ne_of_gt (add_pos hb hc)
  field_simp
  ring

private theorem semicircleDensity_eq_zero_of_not_mem_Ioo {x : ℝ}
    (hx : x ∉ Ioo (-2) 2) : semicircleDensity x = 0 := by
  have h : 4 - x ^ 2 ≤ 0 := by
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with hx | hx <;> nlinarith
  simp [semicircleDensity, Real.sqrt_eq_zero_of_nonpos h]

private theorem integral_semicircle_phi (f : ℝ → ℝ) :
    (∫ x, f x ∂semicircleMeasure) =
      ∫ t : ℝ, phiDeriv t * (semicircleDensity (phi t) * f (phi t)) := by
  have hd : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal (semicircleDensity x) < ⊤ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  rw [semicircleMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (semicircleDensity_continuous.measurable.ennreal_ofReal) hd]
  simp only [ENNReal.toReal_ofReal (semicircleDensity_nonneg _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioo (-2 : ℝ) 2) (fun x hx => by
      rw [semicircleDensity_eq_zero_of_not_mem_Ioo hx]
      simp)]
  rw [← phi_image_univ]
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (phi_hasDerivAt x).hasDerivWithinAt)
    (phi_strictMono.injective.injOn)
    (fun x => semicircleDensity x * f x)
  rw [h]
  simp only [Measure.restrict_univ, smul_eq_mul]
  congr 1
  funext t
  rw [abs_of_pos (by unfold phiDeriv; positivity)]

/-- The scalar kernel is integrable against the finite semicircle measure. -/
theorem semicircleMeasure_flow_poisson_integrable (u : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) :
    Integrable (fun x : ℝ => (1 - u) / (u * x ^ 2 + (1 - u) ^ 2))
      semicircleMeasure := by
  have hb : 0 < 1 - u := by linarith
  have hden (x : ℝ) : 0 < u * x ^ 2 + (1 - u) ^ 2 := by positivity
  have hcont : Continuous (fun x : ℝ =>
      (1 - u) / (u * x ^ 2 + (1 - u) ^ 2)) := by
    exact Continuous.div₀ (by fun_prop) (by fun_prop)
      (fun x => ne_of_gt (hden x))
  apply Integrable.of_bound hcont.aestronglyMeasurable (1 / (1 - u))
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hb (hden x))]
  apply (div_le_iff₀ (hden x)).2
  rw [show 1 / (1 - u) * (u * x ^ 2 + (1 - u) ^ 2) =
      (u * x ^ 2 + (1 - u) ^ 2) / (1 - u) by ring]
  apply (le_div_iff₀ hb).2
  nlinarith [mul_nonneg (le_of_lt hu0) (sq_nonneg x)]

/-- The Poisson kernel on the semicircle law at the flow parameter `0 < u < 1`.
This is a density integral, with no appeal to the algebraic transform `msc`. -/
theorem semicircleMeasure_flow_poisson (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (∫ x : ℝ, (1 - u) / (u * x ^ 2 + (1 - u) ^ 2) ∂semicircleMeasure) = 1 := by
  let b : ℝ := 1 - u
  let c : ℝ := 1 + u
  have hb : 0 < b := by dsimp [b]; linarith
  have hbc : b < c := by dsimp [b, c]; linarith
  have hc : 0 < c := lt_trans hb hbc
  have hcsq : c ^ 2 = b ^ 2 + 4 * u := by dsimp [b, c]; ring
  have hsum : b + c = 2 := by dsimp [b, c]; ring
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpoint (t : ℝ) :
      phiDeriv t * (semicircleDensity (phi t) *
        ((1 - u) / (u * phi t ^ 2 + (1 - u) ^ 2))) =
      (2 * b / Real.pi) *
        (((1 + t ^ 2) * (b ^ 2 + (c * t) ^ 2))⁻¹) := by
    have hd : u * phi t ^ 2 + b ^ 2 =
        (b ^ 2 + (c * t) ^ 2) / (1 + t ^ 2) := by
      rw [phi_sq]
      field_simp
      nlinarith [hcsq]
    have hn : b ^ 2 + (c * t) ^ 2 ≠ 0 := by positivity
    have ht : 1 + t ^ 2 ≠ 0 := ne_of_gt (one_add_sq_pos t)
    have hden : u * phi t ^ 2 + b ^ 2 ≠ 0 := by positivity
    rw [← mul_assoc, phi_density_jacobian]
    change (2 / (Real.pi * (1 + t ^ 2) ^ 2)) *
      (b / (u * phi t ^ 2 + b ^ 2)) = _
    rw [hd]
    field_simp
  calc
    _ = ∫ t : ℝ, (2 * b / Real.pi) *
        (((1 + t ^ 2) * (b ^ 2 + (c * t) ^ 2))⁻¹) := by
          rw [integral_semicircle_phi]
          exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (2 * b / Real.pi) * (Real.pi / (b * (b + c))) := by
          rw [integral_const_mul, integral_rational b c hb hbc]
    _ = 1 := by
          rw [hsum]
          field_simp

/-- The endpoint `u = 0` is a separate constant-integrand case. -/
theorem semicircleMeasure_flow_poisson_zero :
    (∫ x : ℝ, (1 - (0 : ℝ)) /
      ((0 : ℝ) * x ^ 2 + (1 - (0 : ℝ)) ^ 2) ∂semicircleMeasure) = 1 := by
  simp

/-- The nondegenerate flow value `u = 1/2` lies in the analytic range. -/
theorem semicircleMeasure_flow_poisson_half :
    (∫ x : ℝ, (1 - (1 / 2 : ℝ)) /
      ((1 / 2 : ℝ) * x ^ 2 + (1 - (1 / 2 : ℝ)) ^ 2)
      ∂semicircleMeasure) = 1 := by
  exact semicircleMeasure_flow_poisson (1 / 2) (by norm_num) (by norm_num)

/-- At `u = 1/2` the integrand is not pointwise constant. -/
theorem semicircleMeasure_flow_poisson_half_nonconstant :
    (1 - (1 / 2 : ℝ)) /
      ((1 / 2 : ℝ) * (0 : ℝ) ^ 2 + (1 - (1 / 2 : ℝ)) ^ 2) ≠
    (1 - (1 / 2 : ℝ)) /
      ((1 / 2 : ℝ) * (1 : ℝ) ^ 2 + (1 - (1 / 2 : ℝ)) ^ 2) := by
  norm_num

#print axioms semicircleMeasure_flow_poisson_integrable
#print axioms semicircleMeasure_flow_poisson
#print axioms semicircleMeasure_flow_poisson_zero
#print axioms semicircleMeasure_flow_poisson_half
#print axioms semicircleMeasure_flow_poisson_half_nonconstant

end RBM
