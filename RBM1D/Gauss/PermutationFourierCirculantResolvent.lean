/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierUnitaryMatrix
import RBM1D.Gauss.PermutationFourierSwap
import RBM1D.Defs.SemicircleFlowKernelTimeModulus
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# One actual semicircle-quantile Fourier block and its closed-flow resolvent

For the positive-phase normalized Fourier matrix `F` and any permutation `π`, this
file computes the resolvent of `Fᴴ diag(λ_(πj)) F` exactly. The result is a
single deterministic `Fin W` block; it makes no Gaussian or local-law claim.
-/

open Matrix
namespace RBM.Gauss

noncomputable def permutationFourierBlockLambda (W : ℕ) (hW : 1 ≤ W) (π : Equiv.Perm (Fin W))
    (j : Fin W) : ℝ := RBM.semicircleLambda W hW (π j).val (π j).isLt
noncomputable def permutationFourierBlock (W : ℕ) (hW : 1 ≤ W) (π : Equiv.Perm (Fin W)) :
    Matrix (Fin W) (Fin W) ℂ :=
  (permutationFourierMatrix W)ᴴ *
    Matrix.diagonal (fun j => (permutationFourierBlockLambda W hW π j : ℂ)) *
      permutationFourierMatrix W

theorem permutationFourierBlock_hermitian (W : ℕ) (hW : 1 ≤ W)
    (π : Equiv.Perm (Fin W)) : (permutationFourierBlock W hW π).IsHermitian := by
  unfold permutationFourierBlock
  apply Matrix.isHermitian_conjTranspose_mul_mul
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro j
  simp [IsSelfAdjoint]

private theorem inverse_conjugated_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n ℂ) (v : n → ℂ)
    (hleft : Fᴴ * F = 1) (hright : F * Fᴴ = 1)
    (hv : ∀ j, v j ≠ 0) :
    (Fᴴ * Matrix.diagonal v * F)⁻¹ =
      Fᴴ * Matrix.diagonal (fun j => (v j)⁻¹) * F := by
  have hFinv : F⁻¹ = Fᴴ := Matrix.inv_eq_left_inv hleft
  have hFHinv : (Fᴴ)⁻¹ = F := Matrix.inv_eq_left_inv hright
  have hDinv : (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun j => (v j)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp [funext_iff, hv]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hFinv, hFHinv, hDinv, Matrix.mul_assoc]

private theorem flow_denom_ne_zero (u x : ℝ) (hu : u ≤ 1 / 2) :
    (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, add_zero,
    Complex.ofReal_re, Complex.zero_im] at him
  linarith

private theorem conjugated_diag_sub
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n ℂ) (v : n → ℂ) (c z : ℂ) (hF : Fᴴ * F = 1) :
    Fᴴ * Matrix.diagonal (fun j => c * v j - z) * F =
      c • (Fᴴ * Matrix.diagonal v * F) - z • (1 : Matrix n n ℂ) := by
  have hdiag : Matrix.diagonal (fun j => c * v j - z) =
      c • Matrix.diagonal v - z • (1 : Matrix n n ℂ) := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub]
    simp [smul_eq_mul]
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_one, hF]

theorem permutationFourierBlock_resolvent_factor (W : ℕ) (hW : 1 ≤ W)
    (π : Equiv.Perm (Fin W)) (u : ℝ) :
    ((Real.sqrt u : ℂ) • permutationFourierBlock W hW π -
      (Complex.I * ((1-u : ℝ) : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ)) =
    (permutationFourierMatrix W)ᴴ *
      Matrix.diagonal (fun j : Fin W =>
        (((Real.sqrt u * permutationFourierBlockLambda W hW π j : ℝ) : ℂ) -
          Complex.I * ((1-u : ℝ) : ℂ))) * permutationFourierMatrix W := by
  symm
  convert conjugated_diag_sub (permutationFourierMatrix W)
    (fun j => (permutationFourierBlockLambda W hW π j : ℂ)) (Real.sqrt u : ℂ)
    (Complex.I * ((1-u : ℝ) : ℂ))
    (permutationFourierMatrix_conjTranspose_mul W hW) using 1
  · congr 1
    funext j
    push_cast
    ring
  · rfl

theorem permutationFourierBlock_resolvent_entry (W : ℕ) (hW : 1 ≤ W)
    (π : Equiv.Perm (Fin W)) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (a b : Fin W) :
    (((Real.sqrt u : ℂ) • permutationFourierBlock W hW π -
      (Complex.I * ((1-u : ℝ) : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹) a b =
      permutationFourierSum W
        (fun k : Fin W => RBM.semicircleFlowKernel u
          (RBM.semicircleLambda W hW k.val k.isLt))
        (permutationFourierCharacter W (b-a)) π := by
  rw [permutationFourierBlock_resolvent_factor]
  rw [inverse_conjugated_diagonal (permutationFourierMatrix W)
    (fun j : Fin W => (((Real.sqrt u * permutationFourierBlockLambda W hW π j : ℝ) : ℂ) -
      Complex.I * ((1-u : ℝ) : ℂ)))
    (permutationFourierMatrix_conjTranspose_mul W hW)
    (permutationFourierMatrix_mul_conjTranspose W hW)]
  · rw [permutationFourierMatrix_diagonal_entry W hW]
    unfold permutationFourierSum
    simp only [RBM.semicircleFlowKernel, permutationFourierBlockLambda]
    rw [div_eq_mul_inv]
    ring
  · intro j
    exact flow_denom_ne_zero u (permutationFourierBlockLambda W hW π j) hu1

theorem permutationFourierBlock_resolvent_diagonal_zero_mode (W : ℕ) (hW : 1 ≤ W)
    (π : Equiv.Perm (Fin W)) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (a : Fin W) :
    (((Real.sqrt u : ℂ) • permutationFourierBlock W hW π -
      (Complex.I * ((1-u : ℝ) : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹) a a =
      permutationFourierSum W
        (fun k : Fin W => RBM.semicircleFlowKernel u
          (RBM.semicircleLambda W hW k.val k.isLt))
        (fun _ => 1) π := by
  letI : NeZero W := ⟨by omega⟩
  rw [permutationFourierBlock_resolvent_entry W hW π u hu0 hu1 a a]
  congr 1
  funext j
  simp [permutationFourierCharacter]

theorem permutationFourierBlock_resolvent_offdiag_mode_ne_zero (W : ℕ) (hW : 1 ≤ W)
    (a b : Fin W) (hab : a ≠ b) : (b-a : Fin W).val ≠ 0 := by
  letI : NeZero W := ⟨by omega⟩
  intro h
  have hz : b-a = (0 : Fin W) := Fin.ext h
  exact hab (sub_eq_zero.mp hz).symm

theorem permutationFourierBlock_resolvent_two_offdiag_nonzero :
    (((Real.sqrt (1/2 : ℝ) : ℂ) • permutationFourierBlock 2 (by norm_num) (Equiv.refl (Fin 2)) -
      (Complex.I * ((1-(1/2 : ℝ) : ℝ) : ℂ)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹) 0 1 ≠ 0 := by
  let lam : Fin 2 → ℝ := fun j => RBM.semicircleLambda 2 (by norm_num) j.val j.isLt
  have hlt : lam 0 < lam 1 := RBM.semicircleQuantileReflection_witness_two.1
  have hden :
      (((Real.sqrt (1/2 : ℝ) * lam 0 : ℝ) : ℂ) -
        Complex.I * ((1-(1/2 : ℝ) : ℝ) : ℂ)) ≠
      (((Real.sqrt (1/2 : ℝ) * lam 1 : ℝ) : ℂ) -
        Complex.I * ((1-(1/2 : ℝ) : ℝ) : ℂ)) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero] at hr
    have hs : 0 < Real.sqrt (1/2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have hg : RBM.semicircleFlowKernel (1/2) (lam 0) ≠
      RBM.semicircleFlowKernel (1/2) (lam 1) := by
    unfold RBM.semicircleFlowKernel
    exact (inv_inj.not.mpr hden)
  have hentry :
      (((Real.sqrt (1/2 : ℝ) : ℂ) • permutationFourierBlock 2 (by norm_num) (Equiv.refl (Fin 2)) -
        (Complex.I * ((1-(1/2 : ℝ) : ℝ) : ℂ)) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹) 0 1 =
        (RBM.semicircleFlowKernel (1/2) (lam 0) -
          RBM.semicircleFlowKernel (1/2) (lam 1)) / 2 := by
    rw [permutationFourierBlock_resolvent_entry 2 (by norm_num) (Equiv.refl (Fin 2))
      (1/2) (by norm_num) (by norm_num)]
    norm_num [permutationFourierSum, Fin.sum_univ_two,
      permutationFourierCharacter_two, lam]
    ring
  rw [hentry]
  exact div_ne_zero (sub_ne_zero.mpr hg) (by norm_num)

#print axioms permutationFourierBlock_hermitian
#print axioms permutationFourierBlock_resolvent_factor
#print axioms permutationFourierBlock_resolvent_entry
#print axioms permutationFourierBlock_resolvent_diagonal_zero_mode
#print axioms permutationFourierBlock_resolvent_offdiag_mode_ne_zero
#print axioms permutationFourierBlock_resolvent_two_offdiag_nonzero
end RBM.Gauss
