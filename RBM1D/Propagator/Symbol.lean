/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The Fourier representation of `Θ_ξ`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Appendix B, (B.1).

The paper indexes frequencies by `p ∈ T_L = (2π/L) Z_L` and writes the Fourier
symbol of `S^(B)` as `Ŝ(p) = (1 + 2 cos p)/3`.  Here a frequency is `p : ZMod L`,
standing for `2πp/L`, and the plane wave `x ↦ exp(i (2πp/L) x)` is
`x ↦ ZMod.stdAddChar (p * x)`.

## Main definitions

* `RBM.Shat`          : the symbol `Ŝ(p)`
* `RBM.fourierKernel` : `K_{ξ,L}(u) = (1/L) ∑_p exp(ipu) / (1 - ξ Ŝ(p))`

## Main results

* `RBM.Shat_eq_cos`              : `Ŝ(p) = (1 + 2 cos(2πp/L))/3`, the paper's form
* `RBM.SB_mulVec_char`           : plane waves are eigenvectors of `S^(B)` with eigenvalue `Ŝ(p)`
* `RBM.one_sub_mul_Shat_ne_zero` : `1 - ξ Ŝ(p) ≠ 0` for `‖ξ‖ < 1`
* `RBM.Theta_eq_circulant_fourierKernel`, `RBM.Theta_apply_fourier` : (B.1)
-/

namespace RBM

open Matrix Finset

variable (L : ℕ) [NeZero L]

section Symbol

/-- The Fourier symbol of `S^(B)` at frequency `2πp/L`: `Ŝ(p) = (1 + e^{ip} + e^{-ip})/3`. -/
noncomputable def Shat (p : ZMod L) : ℂ :=
  (1 + ZMod.stdAddChar p + ZMod.stdAddChar (-p)) / 3

/-- The symbol in the form written in Appendix B: `Ŝ(p) = (1 + 2 cos p)/3`. -/
theorem Shat_eq_cos (p : ZMod L) :
    Shat L p = (((1 + 2 * Real.cos (2 * Real.pi * p.val / L)) / 3 : ℝ) : ℂ) := by
  have h := Complex.two_cos (2 * Real.pi * p.val / L)
  have e₁ : 2 * (Real.pi : ℂ) * Complex.I * (p.val : ℂ) / (L : ℂ)
      = 2 * Real.pi * p.val / L * Complex.I := by ring
  have e₂ : -(2 * (Real.pi : ℂ) * p.val / L * Complex.I)
      = -(2 * Real.pi * p.val / L) * Complex.I := by ring
  rw [Shat, AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ZMod.toCircle_apply,
    ← Complex.exp_neg, e₁, e₂]
  push_cast
  rw [h]
  ring

theorem Shat_neg (p : ZMod L) : Shat L (-p) = Shat L p := by
  rw [Shat, Shat, neg_neg]
  ring

theorem norm_Shat_le_one (p : ZMod L) : ‖Shat L p‖ ≤ 1 := by
  rw [Shat, norm_div]
  have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [h3, div_le_one (by norm_num)]
  calc ‖1 + ZMod.stdAddChar p + ZMod.stdAddChar (-p)‖
      ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar p‖ + ‖ZMod.stdAddChar (-p)‖ := norm_add₃_le
    _ = 3 := by rw [AddChar.norm_apply, AddChar.norm_apply, norm_one]; norm_num

/-- For `‖ξ‖ < 1` the Fourier multiplier `1 - ξ Ŝ(p)` never vanishes. -/
theorem one_sub_mul_Shat_ne_zero {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : ZMod L) :
    1 - ξ * Shat L p ≠ 0 := by
  intro h
  have h1 : ξ * Shat L p = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖ξ * Shat L p‖ < 1 := by
    rw [norm_mul]
    calc ‖ξ‖ * ‖Shat L p‖ ≤ ‖ξ‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_Shat_le_one L p) (norm_nonneg ξ)
      _ < 1 := by rwa [mul_one]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

end Symbol

section Eigen

/-- `S^(B)` averages over the three nearest neighbours. -/
theorem SB_mulVec_apply (hL : 3 ≤ L) (v : ZMod L → ℂ) (x : ZMod L) :
    (SB L *ᵥ v) x = (v x + v (x - 1) + v (x + 1)) / 3 := by
  have hsplit : ∀ u : ZMod L, sbKernel L u * v (x - u)
      = if u ∈ sbSupport L then (3 : ℂ)⁻¹ * v (x - u) else 0 := by
    intro u
    rw [sbKernel]
    split_ifs <;> ring
  simp only [mulVec, dotProduct, SB_apply]
  rw [← Equiv.sum_comp (Equiv.subLeft x)]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, hsplit]
  rw [Finset.sum_ite_mem, Finset.univ_inter, sum_over_sbSupport L hL]
  simp only [sub_zero, sub_neg_eq_add]
  ring

theorem stdAddChar_mul_add (p u c : ZMod L) :
    ZMod.stdAddChar (p * (u + c)) = ZMod.stdAddChar (p * u) * ZMod.stdAddChar (p * c) := by
  rw [mul_add, AddChar.map_add_eq_mul]

theorem stdAddChar_mul_sub_one (p u : ZMod L) :
    ZMod.stdAddChar (p * (u - 1)) = ZMod.stdAddChar (p * u) * ZMod.stdAddChar (-p) := by
  rw [sub_eq_add_neg, stdAddChar_mul_add, mul_neg, mul_one]

theorem stdAddChar_mul_add_one (p u : ZMod L) :
    ZMod.stdAddChar (p * (u + 1)) = ZMod.stdAddChar (p * u) * ZMod.stdAddChar p := by
  rw [stdAddChar_mul_add, mul_one]

/-- The plane wave `e_p(x) = exp(i (2πp/L) x)` is an eigenvector of `S^(B)` with
eigenvalue `Ŝ(p)`. -/
theorem SB_mulVec_char (hL : 3 ≤ L) (p : ZMod L) :
    SB L *ᵥ (fun x => ZMod.stdAddChar (p * x)) = Shat L p • fun x => ZMod.stdAddChar (p * x) := by
  funext x
  rw [SB_mulVec_apply L hL, stdAddChar_mul_sub_one, stdAddChar_mul_add_one, Pi.smul_apply,
    smul_eq_mul, Shat]
  ring

/-- Orthogonality of characters: `(1/L) ∑_p exp(ipu) = δ_{u,0}`. -/
theorem inv_mul_sum_stdAddChar (u : ZMod L) :
    (L : ℂ)⁻¹ * ∑ p : ZMod L, ZMod.stdAddChar (p * u) = if u = 0 then 1 else 0 := by
  rw [AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar L), ZMod.card]
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  split_ifs <;> simp [hL]

end Eigen

section Fourier

/-- The kernel of (B.1): `K_{ξ,L}(u) = (1/L) ∑_p exp(ipu) / (1 - ξ Ŝ(p))`. -/
noncomputable def fourierKernel (ξ : ℂ) (u : ZMod L) : ℂ :=
  (L : ℂ)⁻¹ * ∑ p : ZMod L, ZMod.stdAddChar (p * u) / (1 - ξ * Shat L p)

/-- The kernel of (B.1) solves `K - ξ S^(B) K = δ_0`. -/
theorem fourierKernel_sub_SB_mulVec (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (u : ZMod L) :
    fourierKernel L ξ u - ξ * (SB L *ᵥ fourierKernel L ξ) u = if u = 0 then 1 else 0 := by
  rw [SB_mulVec_apply L hL, ← inv_mul_sum_stdAddChar L u]
  simp only [fourierKernel, stdAddChar_mul_sub_one, stdAddChar_mul_add_one]
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hD := one_sub_mul_Shat_ne_zero L hξ p
  have key : ZMod.stdAddChar (p * u) / (1 - ξ * Shat L p)
      - ξ * ((ZMod.stdAddChar (p * u) / (1 - ξ * Shat L p)
        + ZMod.stdAddChar (p * u) * ZMod.stdAddChar (-p) / (1 - ξ * Shat L p)
        + ZMod.stdAddChar (p * u) * ZMod.stdAddChar p / (1 - ξ * Shat L p)) / 3)
      = ZMod.stdAddChar (p * u) / (1 - ξ * Shat L p) * (1 - ξ * Shat L p) := by
    rw [Shat]
    ring
  calc _ = (L : ℂ)⁻¹ * (ZMod.stdAddChar (p * u) / (1 - ξ * Shat L p)
      - ξ * ((ZMod.stdAddChar (p * u) / (1 - ξ * Shat L p)
        + ZMod.stdAddChar (p * u) * ZMod.stdAddChar (-p) / (1 - ξ * Shat L p)
        + ZMod.stdAddChar (p * u) * ZMod.stdAddChar p / (1 - ξ * Shat L p)) / 3)) := by ring
    _ = _ := by rw [key, div_mul_cancel₀ _ hD]

/-- **(B.1)**, matrix form: `Θ_ξ` is the circulant matrix generated by the Fourier
kernel `K_{ξ,L}`. -/
theorem Theta_eq_circulant_fourierKernel (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta L ξ = circulant (fourierKernel L ξ) := by
  refine (eq_Theta_of_mul L hL hξ ?_).symm
  have hmul : circulant (fourierKernel L ξ) * SB L
      = circulant (SB L *ᵥ fourierKernel L ξ) := by
    rw [SB, circulant_mul_comm, circulant_mul]
  rw [mul_sub, mul_one, Matrix.mul_smul, hmul, ← circulant_smul, ← circulant_sub,
    ← circulant_single_one ℂ (ZMod L), circulant_inj]
  funext u
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  exact fourierKernel_sub_SB_mulVec L hL hξ u

/-- **(B.1)**: `(Θ_ξ)_{xy} = (1/L) ∑_p exp(ip(x-y)) / (1 - ξ Ŝ(p))`. -/
theorem Theta_apply_fourier (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    Theta L ξ x y
      = (L : ℂ)⁻¹ * ∑ p : ZMod L, ZMod.stdAddChar (p * (x - y)) / (1 - ξ * Shat L p) := by
  rw [Theta_eq_circulant_fourierKernel L hL hξ, circulant_apply, fourierKernel]

end Fourier

end RBM
