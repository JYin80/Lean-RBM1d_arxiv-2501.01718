/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial meshes for general moving windows

This file contains the project-independent target-mesh core.
-/

namespace RBM.APrimeGeneralMovingMesh

open Filter

/-- A mesh which is positive even at `N = 0` and agrees eventually with
`N^(2K+4)`. -/
noncomputable def polynomialMesh (K : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else (N : ℝ) ^ (2 * K + 4)

@[simp] theorem polynomialMesh_zero (K : ℝ) : polynomialMesh K 0 = 1 := by
  simp [polynomialMesh]

theorem polynomialMesh_eq_of_pos {K : ℝ} {N : ℕ} (hN : 0 < N) :
    polynomialMesh K N = (N : ℝ) ^ (2 * K + 4) := by
  simp [polynomialMesh, hN.ne']

theorem polynomialMesh_pos (K : ℝ) (N : ℕ) : 0 < polynomialMesh K N := by
  by_cases hN : N = 0
  · subst N
    simp
  · rw [polynomialMesh, ite_eq_right hN]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero hN)) _

theorem eventually_polynomialMesh_eq (K : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      polynomialMesh K N = (N : ℝ) ^ (2 * K + 4) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact polynomialMesh_eq_of_pos (by omega)

/-! ## The `K = 2D+7` instance -/

/-- The mesh used at the target general-window modulus exponent. -/
noncomputable def targetMesh (D : ℝ) (N : ℕ) : ℝ :=
  polynomialMesh (2 * D + 7) N

theorem targetMesh_pos (D : ℝ) (N : ℕ) : 0 < targetMesh D N :=
  polynomialMesh_pos (2 * D + 7) N

theorem eventually_targetMesh_eq (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      targetMesh D N = (N : ℝ) ^ (4 * D + 18) := by
  filter_upwards [eventually_polynomialMesh_eq (2 * D + 7)] with N hN
  unfold targetMesh
  rw [hN]
  congr 1
  ring

end RBM.APrimeGeneralMovingMesh
