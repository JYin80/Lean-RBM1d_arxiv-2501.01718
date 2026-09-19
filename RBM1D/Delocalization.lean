/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Delocalization from a bound on the Green's function

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, the spectral part of the
proof of Theorem 2.2, i.e. (2.10).

Let `H` be Hermitian with eigenvalues `λ_l` and orthonormal eigenvectors `ψ_l`, and
`G(z) = (H - z)⁻¹`.  For `η > 0`,
`|ψ_k(x)|² ≤ ∑_l η² |ψ_l(x)|² / ((λ_k - λ_l)² + η²) = η · Im G_xx(λ_k + iη)`.   (2.10)

Consequently a bound `|G_xx(λ_k + iη)| ≤ C` gives `|ψ_k(x)|² ≤ C η`.  In the paper the
bound on `G` comes from the local law (Theorem 2.3) with high probability and
`η = N^{-1+τ}`; here it is a hypothesis, and everything is deterministic.

## Main results

* `RBM.green_eq_spectral`       : `G(z) = U diag((λ - z)⁻¹) U*`
* `RBM.im_green_apply_self`     : `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)`
* `RBM.sq_norm_eigenvector_le_sum`, `RBM.sq_norm_eigenvector_le_im_green` : (2.10)
* `RBM.sq_norm_eigenvector_le_of_norm_green_le` : `|G_xx| ≤ C ⇒ |ψ_k(x)|² ≤ C η`
-/

namespace RBM

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (H - z • 1)⁻¹

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- Spectral decomposition of the Green's function. -/
theorem green_eq_spectral {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) :
    green H z = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hz1 : (z • 1 : Matrix n n ℂ) = U * diagonal (fun _ => z) * star U := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU']
  have hsub : H - z • 1 = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U := by
    rw [hz1]
    conv_lhs => rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - z) * ((hH.eigenvalues l : ℂ) - z)⁻¹)
            = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- Diagonal entries of the Green's function: `G_xx(z) = ∑_l |ψ_l(x)|² / (λ_l - z)`. -/
theorem green_apply_self {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) (x : n) :
    green H z x x
      = ∑ l, (Complex.normSq (hH.eigenvectorBasis l x) : ℂ) / ((hH.eigenvalues l : ℂ) - z) := by
  rw [green_eq_spectral hH hz, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_diagonal, star_apply, IsHermitian.eigenvectorUnitary_apply,
    Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

/-- `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)`. -/
theorem im_green_apply_self (E : ℝ) {η : ℝ} (hη : η ≠ 0) (x : n) :
    (green H (E + η * Complex.I) x x).im
      = ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x)
          / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
  have hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ E + η * Complex.I := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hη this.symm
  rw [green_apply_self hH hz, Complex.im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I))
      = (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have him : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
  have hpos : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, hn, him]
  field_simp

/-- (2.10), first inequality: the `l = k` term of the sum is `|ψ_k(x)|²`. -/
theorem sq_norm_eigenvector_le_sum {η : ℝ} (hη : 0 < η) (k x : n) :
    ‖hH.eigenvectorBasis k x‖ ^ 2
      ≤ ∑ l, η ^ 2 * ‖hH.eigenvectorBasis l x‖ ^ 2
          / ((hH.eigenvalues k - hH.eigenvalues l) ^ 2 + η ^ 2) := by
  have hk : η ^ 2 * ‖hH.eigenvectorBasis k x‖ ^ 2
      / ((hH.eigenvalues k - hH.eigenvalues k) ^ 2 + η ^ 2) = ‖hH.eigenvectorBasis k x‖ ^ 2 := by
    rw [sub_self]
    field_simp
    ring
  rw [← hk]
  refine Finset.single_le_sum (f := fun l => η ^ 2 * ‖hH.eigenvectorBasis l x‖ ^ 2
    / ((hH.eigenvalues k - hH.eigenvalues l) ^ 2 + η ^ 2)) (fun l _ => ?_) (Finset.mem_univ k)
  positivity

/-- (2.10), second step: the sum equals `η Im G_xx(λ_k + iη)`. -/
theorem sum_eq_mul_im_green {η : ℝ} (hη : 0 < η) (k x : n) :
    ∑ l, η ^ 2 * ‖hH.eigenvectorBasis l x‖ ^ 2
        / ((hH.eigenvalues k - hH.eigenvalues l) ^ 2 + η ^ 2)
      = η * (green H (hH.eigenvalues k + η * Complex.I) x x).im := by
  rw [im_green_apply_self hH _ hη.ne', Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.normSq_eq_norm_sq]
  have hpos : 0 < (hH.eigenvalues l - hH.eigenvalues k) ^ 2 + η ^ 2 := by positivity
  rw [show (hH.eigenvalues k - hH.eigenvalues l) ^ 2 = (hH.eigenvalues l - hH.eigenvalues k) ^ 2
    by ring]
  field_simp

/-- **(2.10)**: `|ψ_k(x)|² ≤ η Im G_xx(λ_k + iη)`. -/
theorem sq_norm_eigenvector_le_im_green {η : ℝ} (hη : 0 < η) (k x : n) :
    ‖hH.eigenvectorBasis k x‖ ^ 2
      ≤ η * (green H (hH.eigenvalues k + η * Complex.I) x x).im :=
  (sq_norm_eigenvector_le_sum hH hη k x).trans_eq (sum_eq_mul_im_green hH hη k x)

/-- The deterministic core of Theorem 2.2: a bound `|G_xx(λ_k + iη)| ≤ C` on the Green's
function gives `|ψ_k(x)|² ≤ C η`. -/
theorem sq_norm_eigenvector_le_of_norm_green_le {η C : ℝ} (hη : 0 < η) (k x : n)
    (hG : ‖green H (hH.eigenvalues k + η * Complex.I) x x‖ ≤ C) :
    ‖hH.eigenvectorBasis k x‖ ^ 2 ≤ C * η := by
  refine (sq_norm_eigenvector_le_im_green hH hη k x).trans ?_
  rw [mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  exact (Complex.im_le_norm _).trans hG

end RBM
