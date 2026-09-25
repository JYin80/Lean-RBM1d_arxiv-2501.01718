/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GreenSpectralBulkFactor
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

omit [NeZero W] in
private theorem spectral_pole_sq_le_of_distance {z : ℂ} (α : Idx) {δ : ℝ}
    (hδ : 0 < δ) (hne : (hH.eigenvalues α : ℂ) - z ≠ 0)
    (hdist : δ ≤ ‖(hH.eigenvalues α : ℂ) - z‖) :
    ‖spectralPole hH z α‖ ^ 2 ≤ δ⁻¹ ^ 2 := by
  have hnorm : ‖spectralPole hH z α‖ ≤ δ⁻¹ := by
    rw [spectralPole, norm_inv]
    have hdenpos : 0 < ‖(hH.eigenvalues α : ℂ) - z‖ := norm_pos_iff.mpr hne
    exact (inv_le_inv₀ hdenpos hδ).2 hdist
  have hnonneg : 0 ≤ ‖spectralPole hH z α‖ := norm_nonneg _
  have hδinv : 0 ≤ δ⁻¹ := (inv_nonneg.mpr hδ.le)
  nlinarith

omit [NeZero W] in
private theorem spectral_outside_bulk_distance
    {κ E C0 : ℝ} {z : ℂ} (α : Idx)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hzE : |z.re - E| ≤ C0 / (L * W : ℝ))
    (hsmall : C0 / (L * W : ℝ) ≤ κ / 4)
    (hout : ¬ spectralBulkInterval κ (hH.eigenvalues α)) :
    κ / 4 ≤ ‖(hH.eigenvalues α : ℂ) - z‖ := by
  have hE' : -2 + κ ≤ E ∧ E ≤ 2 - κ := by
    have h := abs_le.mp hE
    constructor <;> linarith
  have hout' : ¬ (-2 + κ / 2 ≤ hH.eigenvalues α ∧ hH.eigenvalues α ≤ 2 - κ / 2) := by
    simpa [spectralBulkInterval] using hout
  have hEigE : κ / 2 ≤ |hH.eigenvalues α - E| := by
    rcases not_and_or.mp hout' with hlo | hhi
    · have hlow : hH.eigenvalues α < -2 + κ / 2 := not_le.mp hlo
      rw [abs_of_neg (by linarith [hE'.1, hlow])]
      linarith
    · have hhigh : 2 - κ / 2 < hH.eigenvalues α := not_le.mp hhi
      rw [abs_of_pos (by linarith [hE'.2, hhigh])]
      linarith
  have htriangle : |hH.eigenvalues α - E| ≤
      |hH.eigenvalues α - z.re| + |z.re - E| := by
    have ht := dist_triangle (hH.eigenvalues α) z.re E
    simpa [Real.dist_eq] using ht
  have hre : κ / 4 ≤ |hH.eigenvalues α - z.re| := by
    linarith [hEigE, htriangle, hzE, hsmall]
  have hcomplex : |((hH.eigenvalues α : ℂ) - z).re| ≤
      ‖(hH.eigenvalues α : ℂ) - z‖ := Complex.abs_re_le_norm _
  have hre' : |((hH.eigenvalues α : ℂ) - z).re| =
      |hH.eigenvalues α - z.re| := by simp
  rw [hre'] at hcomplex
  exact hre.trans hcomplex

/-- A separated eigenvalue has pole square at most delta^-2. For the fixed bulk split,
delta = kappa/4 once |Re z-E| <= C0/N and C0/N <= kappa/4. -/
theorem spectral_pole_sq_le_outside_bulk
    {κ E C0 : ℝ} {z : ℂ} (α : Idx)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hzE : |z.re - E| ≤ C0 / (L * W : ℝ))
    (hsmall : C0 / (L * W : ℝ) ≤ κ / 4)
    (hη : 0 < z.im)
    (hout : ¬ spectralBulkInterval κ (hH.eigenvalues α)) :
    ‖spectralPole hH z α‖ ^ 2 ≤ (κ / 4)⁻¹ ^ 2 := by
  have hNoPole : ∀ α' : Idx, (hH.eigenvalues α' : ℂ) ≠ z := by
    intro α' heq
    have him := congrArg Complex.im heq
    simp at him
    linarith
  have _hdenom_ne : (hH.eigenvalues α : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hNoPole α)
  have hdist := spectral_outside_bulk_distance hH α hκ hE hzE hsmall hout
  exact spectral_pole_sq_le_of_distance hH α (by positivity) _hdenom_ne hdist

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The outside-fixed-bulk pole-square tail is bounded by 2N/delta^2, with the paper's
J=[-2+kappa/2,2-kappa/2] and delta=kappa/4. -/
theorem spectral_alpha_outside_bulk_tail_le
    {κ E C0 : ℝ} {z : ℂ} (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hzE : |z.re - E| ≤ C0 / (L * W : ℝ))
    (hsmall : C0 / (L * W : ℝ) ≤ κ / 4) (hη : 0 < z.im) :
    (∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
      ‖spectralPole hH z α‖ ^ 2 * ‖blockM hH a0 α‖ else 0) ≤
      2 * (L * W : ℝ) * (κ / 4)⁻¹ ^ 2 := by
  have hpole (α : Idx) (hout : ¬ spectralBulkInterval κ (hH.eigenvalues α)) :
      ‖spectralPole hH z α‖ ^ 2 ≤ (κ / 4)⁻¹ ^ 2 :=
    spectral_pole_sq_le_outside_bulk hH α hκ hE hzE hsmall hη hout
  have hrestricted :
      ∑ α : Idx, (if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
        ‖blockM hH a0 α‖ else 0) ≤ ∑ α : Idx, ‖blockM hH a0 α‖ :=
    Finset.sum_le_sum (s := Finset.univ) fun α _ => by
      by_cases hout : ¬ spectralBulkInterval κ (hH.eigenvalues α)
      · simp [hout]
      · simp [hout, norm_nonneg]
  calc
    (∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
        ‖spectralPole hH z α‖ ^ 2 * ‖blockM hH a0 α‖ else 0) ≤
      (∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
        (κ / 4)⁻¹ ^ 2 * ‖blockM hH a0 α‖ else 0) :=
      Finset.sum_le_sum (s := Finset.univ) fun α _ => by
        split_ifs with hout
        · rfl
        · exact mul_le_mul_of_nonneg_right (hpole α hout) (norm_nonneg _)
    _ = (κ / 4)⁻¹ ^ 2 *
        (∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
          ‖blockM hH a0 α‖ else 0) := by
      calc
        (∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
            (κ / 4)⁻¹ ^ 2 * ‖blockM hH a0 α‖ else 0) =
          ∑ α : Idx, (κ / 4)⁻¹ ^ 2 *
            (if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
              ‖blockM hH a0 α‖ else 0) := by
          apply Finset.sum_congr rfl
          intro α _
          by_cases hout : ¬ spectralBulkInterval κ (hH.eigenvalues α) <;> simp [hout]
        _ = (κ / 4)⁻¹ ^ 2 *
            ∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
              ‖blockM hH a0 α‖ else 0 := by rw [Finset.mul_sum]
    _ ≤ (κ / 4)⁻¹ ^ 2 * ∑ α : Idx, ‖blockM hH a0 α‖ :=
      mul_le_mul_of_nonneg_left hrestricted (by positivity)
    _ ≤ (κ / 4)⁻¹ ^ 2 * (2 * (L * W : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_norm_blockM_le hH hL a0 β) (by positivity)
    _ = 2 * (L * W : ℝ) * (κ / 4)⁻¹ ^ 2 := by ring

/-- The same outside-bulk pointwise pole-square bound for either resolvent sign. -/
theorem spectral_gsig_pole_sq_le_outside_bulk
    {κ E C0 : ℝ} {z : ℂ} (α : Idx)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hzE : |z.re - E| ≤ C0 / (L * W : ℝ))
    (hsmall : C0 / (L * W : ℝ) ≤ κ / 4)
    (hη : 0 < z.im) (σ : Bool)
    (hout : ¬ spectralBulkInterval κ (hH.eigenvalues α)) :
    ‖spectralGsigPole hH z σ α‖ ^ 2 ≤ (κ / 4)⁻¹ ^ 2 := by
  rw [spectralGsigPole_norm_eq_spectralPole]
  exact spectral_pole_sq_le_outside_bulk hH α hκ hE hzE hsmall hη hout

/-- The outside-bulk alpha tail at the exact Bool-sign pole used by the spectral consumer. -/
theorem spectral_alpha_outside_bulk_tail_le_gsig
    {κ E C0 : ℝ} {z : ℂ} (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hzE : |z.re - E| ≤ C0 / (L * W : ℝ))
    (hsmall : C0 / (L * W : ℝ) ≤ κ / 4) (hη : 0 < z.im)
    (σ : Bool) :
    (∑ α : Idx, if ¬ spectralBulkInterval κ (hH.eigenvalues α) then
      ‖spectralGsigPole hH z σ α‖ ^ 2 * ‖blockM hH a0 α‖ else 0) ≤
      2 * (L * W : ℝ) * (κ / 4)⁻¹ ^ 2 := by
  simpa only [spectralGsigPole_norm_eq_spectralPole] using
    spectral_alpha_outside_bulk_tail_le hH hL a0 β hκ hE hzE hsmall hη

private theorem norm_blockM_le_two_mul_of_bulk_mass
    {D : ℝ} (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W) (α : Idx)
    (hD : 0 ≤ D)
    (hMass : ∀ x : Idx, ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ D / (L * W : ℝ)) :
    ‖blockM hH a0 α‖ ≤ 2 * D := by
  have hweight (x : Idx) : 0 ≤ Sblk L W x (a0, β) + (L * W : ℝ)⁻¹ :=
    add_nonneg (profile_entry_nonneg x (a0, β)) (by positivity)
  have hmass' (x : Idx) :
      ‖hH.eigenvectorBasis α x‖ ^ 2 *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) ≤
        (D / (L * W : ℝ)) *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_right (hMass x) (hweight x)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun x _ => hmass' x
  calc
    ‖blockM hH a0 α‖ ≤ (L * W : ℝ) *
        ∑ x : Idx, ‖hH.eigenvectorBasis α x‖ ^ 2 *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) :=
      norm_blockM_le_profile_variation hH hL a0 β α
    _ ≤ (L * W : ℝ) *
        ∑ x : Idx, (D / (L * W : ℝ)) *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = D * ∑ x : Idx,
        (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hWpos : 0 < (W : ℝ) := by exact_mod_cast NeZero.pos W
      field_simp [ne_of_gt (size_pos (L := L) (W := W)), ne_of_gt hWpos]
    _ = 2 * D := by rw [profile_weight_sum hL a0 β]; ring

/-- Bulk-restricted maximum implication: if every eigenvector with lambda_alpha in J has site
mass at most D/N, then |M_y,alpha| <= 2D for every such alpha and every block site y.
No bound on eigenvectors outside J is asserted. -/
theorem blockM_bulk_restricted_max_le
    {κ D : ℝ} (hL : 3 ≤ L) (hD : 0 ≤ D)
    (hMass : ∀ α : Idx, spectralBulkInterval κ (hH.eigenvalues α) →
      ∀ x : Idx, ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ D / (L * W : ℝ))
    (a0 : ZMod L) (β : Fin W) (α : Idx)
    (hbulk : spectralBulkInterval κ (hH.eigenvalues α)) :
    ‖blockM hH a0 α‖ ≤ 2 * D :=
  norm_blockM_le_two_mul_of_bulk_mass hH hL a0 β α hD (hMass α hbulk)

end GreenSpectralAlphaTail

end RBM

#print axioms RBM.sum_norm_blockM_le
#print axioms RBM.spectral_pole_sq_le_outside_bulk
#print axioms RBM.spectral_alpha_outside_bulk_tail_le
#print axioms RBM.spectralGsigPole_norm_eq_spectralPole
#print axioms RBM.spectral_gsig_pole_sq_le_outside_bulk
#print axioms RBM.spectral_alpha_outside_bulk_tail_le_gsig
#print axioms RBM.blockM_bulk_restricted_max_le
