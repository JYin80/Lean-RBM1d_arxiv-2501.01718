/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

/-!
# Linear forms in the Gaussian coordinates

The coordinates of the model are independent centred Gaussians (`P` is an infinite product), so
a finite real linear combination of them is again a centred Gaussian, with variance the weighted
sum of the coordinate variances.

This is the scalar input of the large deviation estimates: conditionally on the coordinates
outside row `i`, the row sum `∑_{k ≠ i} H_{ik} G^{(i)}_{kj}` is such a linear form.

## Main statements

* `RBM.Gauss.iIndepFun_coord` : the coordinates are independent
* `RBM.Gauss.hasLaw_coord` : each coordinate is `N(0, gvar c)`
* `RBM.Gauss.hasLaw_const_mul_coord` : `a · ω c` is `N(0, a² gvar c)`
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable (d : Dims)

/-- **The coordinates are independent.**  `P` is an infinite product measure. -/
theorem iIndepFun_coord : iIndepFun (fun (c : Coord d) (ω : Ω d) => ω c) (P d) := by
  have := iIndepFun_infinitePi (P := fun c : Coord d => gaussianReal 0 (gvar d c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [P] using this

/-- Each coordinate is a centred Gaussian of variance `gvar d c`. -/
theorem hasLaw_coord (c : Coord d) :
    HasLaw (fun ω : Ω d => ω c) (gaussianReal 0 (gvar d c)) (P d) :=
  ⟨measurable_pi_apply c |>.aemeasurable, P_map_eval d c⟩

/-- A scaled coordinate is a centred Gaussian of variance `a² gvar d c`. -/
theorem hasLaw_const_mul_coord (a : ℝ) (c : Coord d) :
    HasLaw (fun ω : Ω d => a * ω c)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg _) * gvar d c)) (P d) := by
  refine ⟨((measurable_const.mul (measurable_pi_apply c)).aemeasurable), ?_⟩
  have h : (P d).map (fun ω : Ω d => a * ω c)
      = ((P d).map (fun ω : Ω d => ω c)).map (fun x : ℝ => a * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h, P_map_eval d c, gaussianReal_map_const_mul a]
  simp

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι]

/-- **A finite real linear form in an independent Gaussian family is a centred Gaussian**, with
variance `∑ a_i² v_i`.  Induction on the finite set: a scaled variable is independent of the sum
of the others, and Gaussians convolve. -/
theorem map_sum_const_mul_of_indep {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P) (a : ι → ℝ)
    (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω)
      = gaussianReal 0 (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  classical
  have hmul : ∀ i, Measurable (fun ω => a i * X i ω) := fun i => (hmeas i).const_mul _
  have hindep' : iIndepFun (fun i ω => a i * X i ω) P :=
    hindep.comp (fun i => fun x : ℝ => a i * x) fun _ => by fun_prop
  have hlaw' : ∀ i, P.map (fun ω => a i * X i ω)
      = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
    intro i
    have h : P.map (fun ω => a i * X i ω) = (P.map (X i)).map (fun x : ℝ => a i * x) := by
      rw [Measure.map_map (by fun_prop) (hmeas i)]
      rfl
    rw [h, hlaw i, gaussianReal_map_const_mul (a i)]
    simp
  induction s using Finset.induction with
  | empty => simp [Measure.map_const]
  | insert i₀ s hi₀ ih =>
    have hsum : Measurable (fun ω => ∑ i ∈ s, a i * X i ω) :=
      Finset.measurable_sum _ fun i _ => hmul i
    have hindep0 := hindep'.indepFun_finsetSum_of_notMem (fun i => hmul i) hi₀
    have hfun : (∑ j ∈ s, fun ω => a j * X j ω) = fun ω => ∑ i ∈ s, a i * X i ω := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun] at hindep0
    have hadd : (fun ω => ∑ i ∈ insert i₀ s, a i * X i ω)
        = (fun ω => a i₀ * X i₀ ω) + (fun ω => ∑ i ∈ s, a i * X i ω) := by
      funext ω
      simp [Finset.sum_insert hi₀]
    rw [hadd, (hindep0.symm).map_add_eq_map_conv_map (hmul i₀) hsum, ih, hlaw' i₀,
      gaussianReal_conv_gaussianReal, Finset.sum_insert hi₀]
    simp

end General

/-- The family of scaled coordinates is independent. -/
theorem iIndepFun_const_mul_coord (a : Coord d → ℝ) :
    iIndepFun (fun (c : Coord d) (ω : Ω d) => a c * ω c) (P d) :=
  (iIndepFun_coord d).comp (fun c => fun x : ℝ => a c * x) fun _ => by fun_prop

/-- **A finite real linear form in the coordinates is a centred Gaussian**, with variance the
weighted sum `∑ a_c² v_c`. -/
theorem map_sum_const_mul_coord (a : Coord d → ℝ) (s : Finset (Coord d)) :
    (P d).map (fun ω : Ω d => ∑ c ∈ s, a c * ω c)
      = gaussianReal 0 (∑ c ∈ s, NNReal.mk (a c ^ 2) (sq_nonneg _) * gvar d c) :=
  map_sum_const_mul_of_indep (fun c => measurable_pi_apply c) (fun c => P_map_eval d c)
    (iIndepFun_coord d) a s

end RBM.Gauss
