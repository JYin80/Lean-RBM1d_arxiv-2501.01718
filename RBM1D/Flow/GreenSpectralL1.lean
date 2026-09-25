/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Universality
import RBM1D.Delocalization
import RBM1D.Loop.GLoop

/-!
# The deterministic spectral precursor to (2.31)

For a finite Hermitian matrix and a spectral parameter in the upper half-plane, expand the
diagonal loop in an eigenbasis. The variance-profile factor is exactly `N⁻¹ M_{y,α}` by
`blockM_eq`; the remaining factor at `y` is the genuine weighted spectral sum
`∑_β |p_{σ₂,β}(z)| |ψ_β(y)|²`.

This file proves only that deterministic identity and its triangle bound. It does not assert the
stochastic domination in (2.31) or the probability estimates around it.
-/

namespace RBM

open Matrix Finset

section GreenSpectralL1

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- The eigenvalue coefficient of the resolvent with spectral parameter `w`. -/
noncomputable def spectralPole (w : ℂ) (α : n) : ℂ :=
  ((hH.eigenvalues α : ℂ) - w)⁻¹

/-- The eigenvalue coefficient for `Gsig`: the minus sign uses the conjugate spectral parameter. -/
noncomputable def spectralGsigPole (z : ℂ) (σ : Bool) (α : n) : ℂ :=
  spectralPole hH (if σ then z else (starRingEnd ℂ) z) α

private theorem eigenvalues_ne_of_im_ne {w : ℂ} (hw : w.im ≠ 0) :
    ∀ α, (hH.eigenvalues α : ℂ) ≠ w := by
  intro α h
  have him := congrArg Complex.im h
  simp at him
  exact hw him.symm

/-- Diagonal entries of the squared resolvent, including the square on the spectral pole. -/
theorem green_sq_apply_self {w : ℂ} (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x : n) :
    (green H w ^ 2) x x =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun α => spectralPole hH w α
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hG : green H w = U * diagonal d * star U := by
    simpa [U, d, spectralPole] using green_eq_spectral hH hw
  have hG2 : green H w ^ 2 = U * diagonal (fun α => d α * d α) * star U := by
    rw [hG]
    simp only [pow_two]
    calc
      (U * diagonal d * star U) * (U * diagonal d * star U) =
          U * diagonal d * (star U * U) * diagonal d * star U := by noncomm_ring
      _ = U * diagonal d * 1 * diagonal d * star U := by rw [hUU]
      _ = U * (diagonal d * diagonal d) * star U := by
        simp only [mul_one]
        rw [← Matrix.mul_assoc U (diagonal d) (diagonal d)]
      _ = U * diagonal (fun α => d α * d α) * star U := by
        rw [diagonal_mul_diagonal]
  rw [hG2, mul_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_diagonal, star_apply]
  change ((hH.eigenvectorUnitary : Matrix n n ℂ) x α * (d α * d α) *
      star ((hH.eigenvectorUnitary : Matrix n n ℂ) x α)) = _
  rw [IsHermitian.eigenvectorUnitary_apply, Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def, d]
  ring

/-- Diagonal entries of `Gsig` in the eigenbasis. -/
theorem Gsig_apply_self_spectral (z : ℂ) (hη : 0 < z.im) (σ : Bool) (y : n) :
    Gsig H z σ y y =
      ∑ β, spectralGsigPole hH z σ β *
        (Complex.normSq (hH.eigenvectorBasis β y) : ℂ) := by
  have him : (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
    by_cases hσ : σ
    · simpa [hσ] using (ne_of_gt hη)
    · rw [if_neg hσ]
      have hconj : ((starRingEnd ℂ) z).im = -z.im := by simp
      rw [hconj]
      exact neg_ne_zero.mpr (ne_of_gt hη)
  have heig := eigenvalues_ne_of_im_ne hH him
  rw [Gsig, green_apply_self hH heig y]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [spectralGsigPole, spectralPole, div_eq_mul_inv]
  ring

/-- Diagonal entries of `Gsig²` in the eigenbasis. -/
theorem Gsig_sq_apply_self_spectral (z : ℂ) (hη : 0 < z.im) (σ : Bool) (x : n) :
    (Gsig H z σ ^ 2) x x =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) := by
  have him : (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
    by_cases hσ : σ
    · simpa [hσ] using (ne_of_gt hη)
    · rw [if_neg hσ]
      have hconj : ((starRingEnd ℂ) z).im = -z.im := by simp
      rw [hconj]
      exact neg_ne_zero.mpr (ne_of_gt hη)
  have heig := eigenvalues_ne_of_im_ne hH him
  simpa [Gsig, spectralGsigPole, spectralPole] using
    green_sq_apply_self hH heig x

end GreenSpectralL1

section BlockGreenSpectralL1

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
variable (hH : Hm.IsHermitian)

local notation "Idx" => (ZMod L × Fin W)

omit [NeZero W] in
/-- Exact eigenbasis expansion of the diagonal loop before substituting `blockM_eq`. -/
theorem green_spectral_sum_variance (a0 : ZMod L) (β : Fin W) (z : ℂ)
    (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx, (Gsig Hm z σ₁ ^ 2) x x *
        (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹) *
        Gsig Hm z σ₂ (a0, β) (a0, β)) =
      ∑ α : Idx, ∑ γ : Idx,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ *
          (Complex.normSq (hH.eigenvectorBasis γ (a0, β)) : ℂ) *
          ∑ x : Idx,
            (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) *
              (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹) := by
  let S0 : Idx → ℂ := fun x => Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹
  let A : Idx → Idx → ℂ := fun α x =>
    (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)
  let P : Idx → ℂ := fun α =>
    spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α
  let B : Idx → ℂ := fun γ =>
    spectralGsigPole hH z σ₂ γ *
      (Complex.normSq (hH.eigenvectorBasis γ (a0, β)) : ℂ)
  calc
    (∑ x : Idx, (Gsig Hm z σ₁ ^ 2) x x * S0 x *
        Gsig Hm z σ₂ (a0, β) (a0, β)) =
        ∑ x : Idx, (∑ α : Idx, P α * A α x) * S0 x *
          ∑ γ : Idx, B γ := by
            congr 1
            funext x
            rw [Gsig_sq_apply_self_spectral hH z hη σ₁,
              Gsig_apply_self_spectral hH z hη σ₂]
    _ = ∑ α : Idx, ∑ γ : Idx,
          P α * B γ * ∑ x : Idx, A α x * S0 x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        calc
          _ = ∑ α : Idx, ∑ x : Idx, ∑ γ : Idx,
                P α * A α x * S0 x * B γ := by rw [Finset.sum_comm]
          _ = ∑ α : Idx, ∑ γ : Idx, ∑ x : Idx,
                P α * A α x * S0 x * B γ := by
                  congr 1
                  funext α
                  rw [Finset.sum_comm]
          _ = ∑ α : Idx, ∑ γ : Idx, ∑ x : Idx,
                P α * B γ * (A α x * S0 x) := by
                  refine Finset.sum_congr rfl fun α _ => ?_
                  refine Finset.sum_congr rfl fun γ _ => ?_
                  refine Finset.sum_congr rfl fun x _ => ?_
                  ring
          _ = _ := rfl
  simp [S0, A, P, B, mul_assoc]

/-- The averaged variance-profile factor in the spectral expansion is exactly `N⁻¹ M_{y,α}`. -/
theorem blockM_eq_variance_sum (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W)
    (α : Idx) :
    ((L * W : ℕ) : ℂ)⁻¹ * blockM hH a0 α =
      ∑ x : Idx, (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) *
        (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹) := by
  rw [blockM_eq hL hH a0 β α]
  have hN : ((L * W : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne W))
  field_simp [hN]
  simp_rw [Complex.normSq_eq_norm_sq]

/-- Exact spectral expansion of the diagonal loop, with `N⁻¹ M_{y,α}` substituted from
`blockM_eq`. -/
theorem green_spectral_identity_blockM (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W)
    (z : ℂ) (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx, (Gsig Hm z σ₁ ^ 2) x x *
        (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹) *
        Gsig Hm z σ₂ (a0, β) (a0, β)) =
      ((L * W : ℕ) : ℂ)⁻¹ * ∑ α : Idx, ∑ γ : Idx,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ * blockM hH a0 α *
          (Complex.normSq (hH.eigenvectorBasis γ (a0, β)) : ℂ) := by
  rw [green_spectral_sum_variance hH a0 β z hη σ₁ σ₂]
  simp_rw [← blockM_eq_variance_sum hH hL a0 β]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- Triangle bound for the exact expansion. The `γ`-sum remains weighted by the actual
eigenvector masses at `y`; no uniform eigenvector bound is assumed. -/
theorem norm_green_spectral_identity_blockM_le (hL : 3 ≤ L) (a0 : ZMod L) (β : Fin W)
    (z : ℂ) (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    ‖∑ x : Idx, (Gsig Hm z σ₁ ^ 2) x x *
        (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹) *
        Gsig Hm z σ₂ (a0, β) (a0, β)‖ ≤
      (L * W : ℝ)⁻¹ *
        (∑ α : Idx, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 * ‖blockM hH a0 α‖) *
        (∑ γ : Idx, ‖spectralGsigPole hH z σ₂ γ‖ *
          Complex.normSq (hH.eigenvectorBasis γ (a0, β))) := by
  rw [green_spectral_identity_blockM hH hL a0 β z hη σ₁ σ₂]
  let P : Idx → ℂ := fun α => spectralGsigPole hH z σ₁ α
  let Q : Idx → ℂ := fun γ => spectralGsigPole hH z σ₂ γ
  let M : Idx → ℂ := fun α => blockM hH a0 α
  let w : Idx → ℝ := fun γ => Complex.normSq (hH.eigenvectorBasis γ (a0, β))
  have hNpos : (0 : ℝ) < (L * W : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)
  have hw (γ : Idx) : 0 ≤ w γ := by
    simp only [w, Complex.normSq_eq_norm_sq]
    positivity
  have hnormw (γ : Idx) : ‖(w γ : ℂ)‖ = w γ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw γ)]
  have hterm (α γ : Idx) :
      ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
    calc
      ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ =
          ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
            simp only [norm_mul, hnormw]
            ring
      _ ≤ _ := le_rfl
  have htriangle :
      ‖∑ α : Idx, ∑ γ : Idx,
          P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ∑ α : Idx, ∑ γ : Idx,
          ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
    calc
      ‖∑ α : Idx, ∑ γ : Idx,
          P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
          ∑ α : Idx, ‖∑ γ : Idx,
            P α * P α * Q γ * M α * (w γ : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ α : Idx, ∑ γ : Idx,
            ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
          exact Finset.sum_le_sum fun α _ => norm_sum_le _ _
  have htermSum :
      ∑ α : Idx, ∑ γ : Idx,
          ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ∑ α : Idx, ∑ γ : Idx, ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
    exact Finset.sum_le_sum fun α _ =>
      Finset.sum_le_sum fun γ _ => hterm α γ
  have hfactor :
      ∑ α : Idx, ∑ γ : Idx, ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) =
        (∑ α : Idx, ‖P α‖ ^ 2 * ‖M α‖) *
          (∑ γ : Idx, ‖Q γ‖ * w γ) := by
    calc
      _ = ∑ α : Idx, (‖P α‖ ^ 2 * ‖M α‖) *
            ∑ γ : Idx, ‖Q γ‖ * w γ := by
              refine Finset.sum_congr rfl fun α _ => ?_
              rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  calc
    ‖((L * W : ℕ) : ℂ)⁻¹ * ∑ α : Idx, ∑ γ : Idx,
        P α * P α * Q γ * M α * (w γ : ℂ)‖ =
        (L * W : ℝ)⁻¹ *
          ‖∑ α : Idx, ∑ γ : Idx,
            P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast, Nat.cast_mul]
    _ ≤ (L * W : ℝ)⁻¹ *
          (∑ α : Idx, ∑ γ : Idx,
            ‖P α * P α * Q γ * M α * (w γ : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left htriangle (by positivity)
    _ ≤ (L * W : ℝ)⁻¹ *
          (∑ α : Idx, ∑ γ : Idx,
            ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ)) := by
          exact mul_le_mul_of_nonneg_left htermSum (by positivity)
    _ = ((L * W : ℝ)⁻¹ *
          (∑ α : Idx, ‖P α‖ ^ 2 * ‖M α‖)) *
            (∑ γ : Idx, ‖Q γ‖ * w γ) := by
          rw [hfactor]
          ring

end BlockGreenSpectralL1

end RBM

#print axioms RBM.green_sq_apply_self
#print axioms RBM.Gsig_apply_self_spectral
#print axioms RBM.Gsig_sq_apply_self_spectral
#print axioms RBM.green_spectral_sum_variance
#print axioms RBM.blockM_eq_variance_sum
#print axioms RBM.green_spectral_identity_blockM
#print axioms RBM.norm_green_spectral_identity_blockM_le
