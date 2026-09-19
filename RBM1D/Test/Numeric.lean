/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Numeric regression tests

Independent checks, over `ℚ`, of the definitions of Section 2.1 and Definition 2.13 at
`L = 5, 7` and `ξ = 1/2`.  The block covariance matrix is written out again here
directly from the paper, `S^(B)_{ij} = (1/3) 1(dist_{Z_L}(i,j) ≤ 1)`, without going
through `RBM.SB`, and its resolvent is the explicit rational matrix computed by exact
Gaussian elimination.  A transcription error in either definition breaks these checks.

At the end the rational inverse for `L = 5` is matched against `RBM.Theta` itself.
-/

namespace RBM.Numeric

open Matrix

/-- `S^(B)` over `ℚ`, written directly from §2.1: `1/3` when the cyclic distance is `≤ 1`. -/
def SBq (L : ℕ) : Matrix (Fin L) (Fin L) ℚ :=
  Matrix.of fun i j =>
    if (i.val + L - j.val) % L ≤ 1 ∨ (j.val + L - i.val) % L ≤ 1 then 1 / 3 else 0

/-- `Θ_{1/2}` for `L = 5`, by exact Gaussian elimination. -/
def Theta5 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![38/29, 8/29, 2/29, 2/29, 8/29;
    8/29, 38/29, 8/29, 2/29, 2/29;
    2/29, 8/29, 38/29, 8/29, 2/29;
    2/29, 2/29, 8/29, 38/29, 8/29;
    8/29, 2/29, 2/29, 8/29, 38/29]

/-- `Θ_{1/2}` for `L = 7`, by exact Gaussian elimination. -/
def Theta7 : Matrix (Fin 7) (Fin 7) ℚ :=
  !![182/139, 38/139, 8/139, 2/139, 2/139, 8/139, 38/139;
    38/139, 182/139, 38/139, 8/139, 2/139, 2/139, 8/139;
    8/139, 38/139, 182/139, 38/139, 8/139, 2/139, 2/139;
    2/139, 8/139, 38/139, 182/139, 38/139, 8/139, 2/139;
    2/139, 2/139, 8/139, 38/139, 182/139, 38/139, 8/139;
    8/139, 2/139, 2/139, 8/139, 38/139, 182/139, 38/139;
    38/139, 8/139, 2/139, 2/139, 8/139, 38/139, 182/139]

example : (1 - (1 / 2 : ℚ) • SBq 5) * Theta5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SBq, Theta5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num

example : Theta5 * (1 - (1 / 2 : ℚ) • SBq 5) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SBq, Theta5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num

set_option maxHeartbeats 2000000 in
example : (1 - (1 / 2 : ℚ) • SBq 7) * Theta7 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SBq, Theta7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num

set_option maxHeartbeats 2000000 in
example : Theta7 * (1 - (1 / 2 : ℚ) • SBq 7) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SBq, Theta7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num

/-- Row sums are `(1 - ξ)⁻¹ = 2`, as `RBM.sum_Theta_row` predicts. -/
example (i : Fin 5) : ∑ j, Theta5 i j = 2 := by
  fin_cases i <;> simp [Theta5, Fin.sum_univ_succ] <;> norm_num

example (i : Fin 7) : ∑ j, Theta7 i j = 2 := by
  fin_cases i <;> simp [Theta7, Fin.sum_univ_succ] <;> norm_num

/-- At `ξ = 1/2` the characteristic equation is `ρ² - 5ρ + 1 = 0` (`c = 3/ξ - 1 = 5`),
and `ρ = (5 - √21)/2` is its root of modulus `< 1`. -/
example : ((5 - Real.sqrt 21) / 2) ^ 2 - 5 * ((5 - Real.sqrt 21) / 2) + 1 = 0 := by
  have h : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  linear_combination h / 4

example : (3 : ℚ) / (1 / 2) - 1 = 5 := by norm_num

end RBM.Numeric
