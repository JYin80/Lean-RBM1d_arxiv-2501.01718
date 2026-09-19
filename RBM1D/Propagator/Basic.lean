/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Block
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The propagator `Θ_ξ`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.13 and
Lemma 2.14.

Definition 2.13 sets `Θ_ξ = (1 - ξ S^(B))⁻¹` for `ξ : ℂ` with `‖ξ‖ < 1`.  We take
`Ring.inverse` of `1 - ξ • S^(B)` in the ring of matrices equipped with the
`ℓ^∞`-operator norm; `‖S^(B)‖ = 1` then makes `1 - ξ S^(B)` a unit.

## Main results

* `RBM.norm_SB`        : `‖S^(B)‖ = 1` in the `ℓ^∞` operator norm
* `RBM.Theta_mul`, `RBM.mul_Theta` : `Θ_ξ` is a two-sided inverse of `1 - ξ S^(B)`
* `RBM.eq_Theta_of_mul`: uniqueness, the workhorse for the remaining properties
* `RBM.Theta_transpose`: Lemma 2.14 (1), symmetry
* `RBM.Theta_commute_SB`, `RBM.Theta_commute` : Lemma 2.14 (3), commutativity
* `RBM.sum_Theta_row`  : `∑_b (Θ_ξ)_{ab} = (1 - ξ)⁻¹`, used in (3.47)-(3.48)
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

section Norm

variable (L : ℕ) [NeZero L]

theorem nnnorm_sbKernel (u : ZMod L) :
    ‖sbKernel L u‖₊ = if u ∈ sbSupport L then (3 : ℝ≥0)⁻¹ else 0 := by
  rw [sbKernel]
  split_ifs with h
  · have h3 : ‖(3 : ℂ)‖₊ = 3 := by simp
    rw [nnnorm_inv, h3]
  · simp

theorem sum_nnnorm_sbKernel (hL : 3 ≤ L) : ∑ u : ZMod L, ‖sbKernel L u‖₊ = 1 := by
  classical
  simp only [nnnorm_sbKernel]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, card_sbSupport L hL]
  norm_num

theorem sum_nnnorm_SB_row (hL : 3 ≤ L) (a : ZMod L) : ∑ b : ZMod L, ‖SB L a b‖₊ = 1 := by
  have h : ∑ b : ZMod L, ‖SB L a b‖₊ = ∑ u : ZMod L, ‖sbKernel L u‖₊ :=
    Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun b => by rw [SB_apply]; rfl)
  rw [h, sum_nnnorm_sbKernel L hL]

theorem nnnorm_SB (hL : 3 ≤ L) : ‖SB L‖₊ = 1 := by
  rw [Matrix.linfty_opNNNorm_def]
  simp only [sum_nnnorm_SB_row L hL]
  exact Finset.sup_const Finset.univ_nonempty 1

/-- `‖S^(B)‖ = 1` in the `ℓ^∞` operator norm: `S^(B)` is symmetric and stochastic. -/
theorem norm_SB (hL : 3 ≤ L) : ‖SB L‖ = 1 := by
  rw [← coe_nnnorm, nnnorm_SB L hL, NNReal.coe_one]

theorem norm_smul_SB_lt_one (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : ‖ξ • SB L‖ < 1 := by
  rw [norm_smul, norm_SB L hL, mul_one]
  exact hξ

end Norm

section Defs

variable (L : ℕ) [NeZero L]

/-- Definition 2.13: the propagator `Θ_ξ = (1 - ξ S^(B))⁻¹`. -/
noncomputable def Theta (ξ : ℂ) : Matrix (ZMod L) (ZMod L) ℂ :=
  Ring.inverse (1 - ξ • SB L)

theorem isUnit_one_sub_smul_SB (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    IsUnit (1 - ξ • SB L) :=
  ⟨Units.oneSub _ (norm_smul_SB_lt_one L hL hξ), Units.val_oneSub _ _⟩

theorem Theta_mul (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta L ξ * (1 - ξ • SB L) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_sub_smul_SB L hL hξ)

theorem mul_Theta (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (1 - ξ • SB L) * Theta L ξ = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_sub_smul_SB L hL hξ)

/-- Uniqueness of the inverse: any left inverse of `1 - ξ S^(B)` equals `Θ_ξ`.
This is the workhorse used to transfer structural properties of `S^(B)` to `Θ_ξ`. -/
theorem eq_Theta_of_mul (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    {B : Matrix (ZMod L) (ZMod L) ℂ} (h : B * (1 - ξ • SB L) = 1) : B = Theta L ξ := by
  calc B = B * ((1 - ξ • SB L) * Theta L ξ) := by rw [mul_Theta L hL hξ, mul_one]
    _ = (B * (1 - ξ • SB L)) * Theta L ξ := (mul_assoc _ _ _).symm
    _ = Theta L ξ := by rw [h, one_mul]

end Defs

section Structure

variable (L : ℕ) [NeZero L]

/-- Lemma 2.14 (1): `Θ_ξ` is symmetric. -/
theorem Theta_transpose (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (Theta L ξ)ᵀ = Theta L ξ := by
  refine eq_Theta_of_mul L hL hξ ?_
  have hsym : (1 - ξ • SB L)ᵀ = 1 - ξ • SB L := by
    rw [transpose_sub, transpose_one, transpose_smul, SB_transpose]
  calc (Theta L ξ)ᵀ * (1 - ξ • SB L)
      = (Theta L ξ)ᵀ * (1 - ξ • SB L)ᵀ := by rw [hsym]
    _ = ((1 - ξ • SB L) * Theta L ξ)ᵀ := (transpose_mul _ _).symm
    _ = 1 := by rw [mul_Theta L hL hξ, transpose_one]

theorem Theta_isSymm (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : (Theta L ξ).IsSymm :=
  Theta_transpose L hL hξ

/-- Lemma 2.14 (3): `Θ_ξ` commutes with `S^(B)`. -/
theorem Theta_commute_SB (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Commute (Theta L ξ) (SB L) := by
  have hb : Commute (1 - ξ • SB L) (SB L) := by
    unfold Commute SemiconjBy
    simp [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  have key : Theta L ξ * SB L = SB L * Theta L ξ := by
    calc Theta L ξ * SB L
        = Theta L ξ * SB L * ((1 - ξ • SB L) * Theta L ξ) := by
          rw [mul_Theta L hL hξ, mul_one]
      _ = Theta L ξ * ((1 - ξ • SB L) * SB L) * Theta L ξ := by
          rw [hb.eq]; noncomm_ring
      _ = (Theta L ξ * (1 - ξ • SB L)) * SB L * Theta L ξ := by noncomm_ring
      _ = SB L * Theta L ξ := by rw [Theta_mul L hL hξ, one_mul]
  exact key

/-- Lemma 2.14 (3): propagators at different spectral parameters commute. -/
theorem Theta_commute (hL : 3 ≤ L) {ξ ξ' : ℂ} (hξ : ‖ξ‖ < 1) (hξ' : ‖ξ'‖ < 1) :
    Commute (Theta L ξ) (Theta L ξ') := by
  have h1 : Commute (Theta L ξ) (1 - ξ' • SB L) := by
    have := Theta_commute_SB L hL hξ
    unfold Commute SemiconjBy at this ⊢
    simp [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, this]
  have h2 : Theta L ξ * Theta L ξ' = Theta L ξ' * Theta L ξ := by
    calc Theta L ξ * Theta L ξ'
        = Theta L ξ' * (1 - ξ' • SB L) * (Theta L ξ * Theta L ξ') := by
          rw [Theta_mul L hL hξ', one_mul]
      _ = Theta L ξ' * ((1 - ξ' • SB L) * Theta L ξ) * Theta L ξ' := by noncomm_ring
      _ = Theta L ξ' * (Theta L ξ * (1 - ξ' • SB L)) * Theta L ξ' := by rw [h1.eq]
      _ = Theta L ξ' * Theta L ξ * ((1 - ξ' • SB L) * Theta L ξ') := by noncomm_ring
      _ = Theta L ξ' * Theta L ξ := by rw [mul_Theta L hL hξ', mul_one]
  exact h2

end Structure

section RowSum

variable (L : ℕ) [NeZero L]

theorem one_sub_ne_zero {ξ : ℂ} (hξ : ‖ξ‖ < 1) : (1 : ℂ) - ξ ≠ 0 := by
  intro h
  have hone : ξ = 1 := by linear_combination -h
  rw [hone] at hξ
  simp at hξ

/-- `Θ_ξ` applied to the constant vector `1`.  Equivalent to `∑_b (Θ_ξ)_{ab} = (1-ξ)⁻¹`. -/
theorem Theta_mulVec_one (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta L ξ *ᵥ (1 : ZMod L → ℂ) = (1 - ξ)⁻¹ • (1 : ZMod L → ℂ) := by
  have hne : (1 : ℂ) - ξ ≠ 0 := one_sub_ne_zero hξ
  have h1 : (1 - ξ • SB L) *ᵥ (1 : ZMod L → ℂ) = (1 - ξ) • (1 : ZMod L → ℂ) := by
    rw [sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, SB_mulVec_one L hL, sub_smul,
      one_smul]
  calc Theta L ξ *ᵥ (1 : ZMod L → ℂ)
      = (1 - ξ)⁻¹ • (Theta L ξ *ᵥ ((1 - ξ) • (1 : ZMod L → ℂ))) := by
        rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (1 - ξ)⁻¹ • (Theta L ξ *ᵥ ((1 - ξ • SB L) *ᵥ (1 : ZMod L → ℂ))) := by rw [h1]
    _ = (1 - ξ)⁻¹ • ((Theta L ξ * (1 - ξ • SB L)) *ᵥ (1 : ZMod L → ℂ)) := by
        rw [Matrix.mulVec_mulVec]
    _ = (1 - ξ)⁻¹ • (1 : ZMod L → ℂ) := by rw [Theta_mul L hL hξ, Matrix.one_mulVec]

/-- The row sums of the propagator, used in (3.47) and Step 4 of Lemma 3.6. -/
theorem sum_Theta_row (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a : ZMod L) :
    ∑ b : ZMod L, Theta L ξ a b = (1 - ξ)⁻¹ := by
  have h := congrFun (Theta_mulVec_one L hL hξ) a
  simpa [Matrix.mulVec, dotProduct] using h

end RowSum

section Series

variable (L : ℕ) [NeZero L]

/-- Lemma 2.14 (5): the random-walk (Neumann) representation
`Θ_ξ = ∑_{k} ξ^k (S^(B))^k`. -/
theorem Theta_eq_tsum (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta L ξ = ∑' k : ℕ, (ξ • SB L) ^ k := by
  rw [Theta, NormedRing.inverse_one_sub _ (norm_smul_SB_lt_one L hL hξ)]
  rfl

end Series

section Translation

variable (L : ℕ) [NeZero L]

/-- Lemma 2.14 (2): `Θ_ξ` is translation invariant, `(Θ_ξ)_{x y} = (Θ_ξ)_{x+1, y+1}`. -/
theorem Theta_apply_add_right (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b c : ZMod L) :
    Theta L ξ (a + c) (b + c) = Theta L ξ a b := by
  set e : ZMod L ≃ ZMod L := Equiv.addRight c with he
  have hone : ((1 : Matrix (ZMod L) (ZMod L) ℂ)).submatrix e e = 1 :=
    Matrix.submatrix_one_equiv e
  have hSB : (SB L).submatrix e e = SB L := by
    ext i j
    simpa [he] using SB_apply_add_right L i j c
  have hsub : (1 - ξ • SB L).submatrix e e = 1 - ξ • SB L := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul, hSB, hone]
  have hkey : (Theta L ξ).submatrix e e = Theta L ξ := by
    refine eq_Theta_of_mul L hL hξ ?_
    calc (Theta L ξ).submatrix e e * (1 - ξ • SB L)
        = (Theta L ξ).submatrix e e * (1 - ξ • SB L).submatrix e e := by rw [hsub]
      _ = (Theta L ξ * (1 - ξ • SB L)).submatrix e e := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [Theta_mul L hL hξ, hone]
  calc Theta L ξ (a + c) (b + c) = (Theta L ξ).submatrix e e a b := rfl
    _ = Theta L ξ a b := by rw [hkey]

end Translation

end RBM
