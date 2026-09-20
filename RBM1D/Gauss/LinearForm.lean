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

end RBM.Gauss
