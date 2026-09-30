/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GreenSpectralL1
import RBM1D.Green.EntryBound

/-!
# Deterministic spectral tail for the block profile

For the actual block variance profile, eigenbasis completeness bounds the full-spectrum
blockM mass by 2N. A fixed bulk interval then gives a deterministic pole-square tail, and a
bulk-only eigenvector mass bound controls blockM only on that interval.

This file proves deterministic finite-dimensional implications only. It does not assert the
stochastic estimates (2.29) or (2.32), or an unrestricted maximum over eigenvectors.
-/

namespace RBM

open Matrix Finset

/-- Both resolvent signs have the same pole norm for a Hermitian matrix. -/
theorem spectralGsigPole_norm_eq_spectralPole
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (σ : Bool) (α : n) :
    ‖spectralGsigPole hH z σ α‖ = ‖spectralPole hH z α‖ := by
  cases σ
  · change ‖(((hH.eigenvalues α : ℂ) - (starRingEnd ℂ) z)⁻¹)‖ =
      ‖(((hH.eigenvalues α : ℂ) - z)⁻¹)‖
    rw [norm_inv, norm_inv]
    have hconj : ((hH.eigenvalues α : ℂ) - (starRingEnd ℂ) z) =
        star ((hH.eigenvalues α : ℂ) - z) := by simp
    rw [hconj, norm_star]
  · rfl

noncomputable section GreenSpectralAlphaTail

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
variable (hH : Hm.IsHermitian)

local notation "Idx" => (ZMod L × Fin W)

private theorem size_pos : 0 < (L * W : ℝ) := by
  exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)

private theorem profile_column_sum (hL : 3 ≤ L) (y : Idx) :
    ∑ x : Idx, Sblk L W x y = 1 :=
  sum_Sblk_col hL y

omit [NeZero L] [NeZero W] in
private theorem profile_entry_nonneg (x y : Idx) : 0 ≤ Sblk L W x y :=
  Sblk_nonneg x y

omit [NeZero L] [NeZero W] in
private theorem profile_centered_norm_le (y x : Idx) :
    ‖Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹‖ ≤
      Sblk L W x y + (L * W : ℝ)⁻¹ := by
  calc
    ‖Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹‖ ≤
        ‖Svar L W x y‖ + ‖((L * W : ℕ) : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = Sblk L W x y + (L * W : ℝ)⁻¹ := by
      rw [Svar_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (profile_entry_nonneg x y), norm_inv, Complex.norm_natCast]
      simp only [Nat.cast_mul]

private theorem norm_blockM_le_profile_variation
    (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W) (α : Idx) :
    ‖blockM hH a0 α‖ ≤ (L * W : ℝ) *
      ∑ x : Idx, ‖hH.eigenvectorBasis α x‖ ^ 2 *
        (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
  rw [blockM_eq hL hH a0 β α]
  have hterm (x : Idx) :
      ‖((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
          (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹)‖ ≤
        ‖hH.eigenvectorBasis α x‖ ^ 2 *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (profile_centered_norm_le (a0, β) x)
      (sq_nonneg _)
  have hsum := norm_sum_le Finset.univ
    (fun x : Idx => ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
      (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹))
  calc
    ‖((L * W : ℕ) : ℂ) *
        ∑ x : Idx, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
          (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹)‖ =
      (L * W : ℝ) * ‖∑ x : Idx,
        ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
          (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹)‖ := by
            rw [norm_mul, Complex.norm_natCast]
            simp only [Nat.cast_mul]
    _ ≤ (L * W : ℝ) * ∑ x : Idx,
        ‖((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
          (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹)‖ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (L * W : ℝ) * ∑ x : Idx,
        ‖hH.eigenvectorBasis α x‖ ^ 2 *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x _ => hterm x) (by positivity)

private theorem profile_weight_sum (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W) :
    ∑ x : Idx, (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, profile_column_sum hL (a0, β)]
  have hN : (L * W : ℝ) ≠ 0 := ne_of_gt (size_pos (L := L) (W := W))
  have hconst : ∑ _x : Idx, (L * W : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      ZMod.card, Fintype.card_fin, nsmul_eq_mul]
    have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
    simp only [Nat.cast_mul]
    field_simp [hW]
  rw [hconst]
  norm_num

/-- Full-spectrum aggregate of the actual block profile: sum alpha |M_y,alpha| <= 2N. -/
theorem sum_norm_blockM_le (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W) :
    ∑ α : Idx, ‖blockM hH a0 α‖ ≤ 2 * (L * W : ℝ) := by
  have hN : 0 ≤ (L * W : ℝ) := by positivity
  calc
    ∑ α : Idx, ‖blockM hH a0 α‖ ≤
        ∑ α : Idx, (L * W : ℝ) *
          ∑ x : Idx, ‖hH.eigenvectorBasis α x‖ ^ 2 *
            (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) :=
      Finset.sum_le_sum fun α _ => norm_blockM_le_profile_variation hH hL a0 β α
    _ = (L * W : ℝ) *
        ∑ x : Idx, (∑ α : Idx, ‖hH.eigenvectorBasis α x‖ ^ 2) *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_mul]
    _ = (L * W : ℝ) *
        ∑ x : Idx, (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sum_sq_norm_eigenvectorBasis hH x, one_mul]
    _ = 2 * (L * W : ℝ) := by
      rw [profile_weight_sum hL a0 β]
      ring

end GreenSpectralAlphaTail

end RBM

