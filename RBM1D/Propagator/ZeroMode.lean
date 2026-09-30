/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.DiffComplex
import Mathlib.Tactic.Module

/-!
# Removing the zero mode: `S̃^(B) = (1-ζ) S^(B) + (ζ/L) J`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, end of Section 7.2.

There the variance profile is `S̃^(B)_{xy} = (1-ζ) S^(B)_{xy} + ζ/L`, i.e.
`S̃^(B) = (1-ζ) S^(B) + (ζ/L) J` with `J` the all-ones matrix, and the paper asserts

  `[(1-ξS̃)⁻¹]_{ab} - [(1-ξS̃)⁻¹]_{a'b'} = [(1-ξ(1-ζ)S)⁻¹]_{ab} - [(1-ξ(1-ζ)S)⁻¹]_{a'b'}`,
  `|1-ξ| ∼ |1-ξ(1-ζ)|`.

The first statement holds because `J = 𝟙𝟙ᵀ` only sees the constant mode, on which
`Θ_{ξ(1-ζ)}` acts as the scalar `(1-ξ(1-ζ))⁻¹`.  Hence the Sherman–Morrison correction is a
scalar multiple of `J`: with `T = ξ(1-ζ)`,

  `(1 - ξ S̃)⁻¹ = Θ_T + α J`,   `α = ξζ / (L (1-T)(1-ξ))`   (`RBM.ThetaTilde_eq`).

## Main results

* `RBM.ThetaTilde_eq`           : the Sherman–Morrison formula above
* `RBM.ThetaTilde_sub_ThetaTilde` : the difference identity at the end of Section 7.2
* `RBM.norm_one_sub_mul_le`, `RBM.le_norm_one_sub_mul` :
  one-sided comparisons of `|1-ξ|` and `|1-ξ(1-ζ)|` for `‖ξ‖ ≤ 1`, `0 ≤ ζ ≤ 1`
* `RBM.norm_one_sub_mul_comparable` : `|1-ξ|/2 ≤ |1-ξ(1-ζ)| ≤ 2|1-ξ|` when
  `0 < ζ ≤ 1/2` and `ζ ≤ |1-ξ|`

## Deviations from the paper

* The comparison `|1-ξ| ∼ |1-ξ(1-ζ)|` is false without a smallness condition relating `ζ`
  to `|1-ξ|` (take `ξ = 1`).  We assume `ζ ≤ |1-ξ|`; in the paper's application
  (`ξ ∈ {m², |m|²}`, `Im z = N^{-1+c/3}`, `ζ_U ∼ N^{-1+τ_U}`) this is the requirement
  `ζ_U ≲ η`.  Conversely `|1-ξ(1-ζ)| ≥ ζ` always, so the
  upper comparison genuinely needs `ζ ≲ |1-ξ|`.
* `ξ` may lie on the closed unit disc (`ξ ≠ 1`), since `‖ξ(1-ζ)‖ ≤ 1 - ζ < 1`.
-/

namespace RBM

open Matrix

section Defs

variable (L : ℕ) [NeZero L]

/-- The all-ones matrix `J`. -/
def onesMat : Matrix (ZMod L) (ZMod L) ℂ := Matrix.of fun _ _ => 1

/-- The variance profile of Section 7.2: `S̃^(B) = (1-ζ) S^(B) + (ζ/L) J`. -/
noncomputable def SBTilde (ζ : ℂ) : Matrix (ZMod L) (ZMod L) ℂ :=
  (1 - ζ) • SB L + (ζ / L) • onesMat L

/-- `(1 - ξ S̃^(B))⁻¹`, taken with `Ring.inverse` as for `Θ_ξ`. -/
noncomputable def ThetaTilde (ζ ξ : ℂ) : Matrix (ZMod L) (ZMod L) ℂ :=
  Ring.inverse (1 - ξ • SBTilde L ζ)

/-- The constant zero mode `α = ξζ / (L (1 - ξ(1-ζ)) (1 - ξ))`. -/
noncomputable def zeroMode (ζ ξ : ℂ) : ℂ :=
  ξ * ζ / ((L : ℂ) * (1 - ξ * (1 - ζ)) * (1 - ξ))

omit [NeZero L] in
@[simp] theorem onesMat_apply (a b : ZMod L) : onesMat L a b = 1 := rfl

theorem onesMat_mul_onesMat : onesMat L * onesMat L = (L : ℂ) • onesMat L := by
  ext a b
  simp [Matrix.mul_apply, ZMod.card]

theorem SB_mul_onesMat (hL : 3 ≤ L) : SB L * onesMat L = onesMat L := by
  ext a b
  simp [Matrix.mul_apply, sum_SB_row L hL a]

theorem onesMat_mul_SB (hL : 3 ≤ L) : onesMat L * SB L = onesMat L := by
  ext a b
  have h : ∀ c, SB L c b = SB L b c := fun c => congrFun (congrFun (SB_transpose L) b) c
  simp [Matrix.mul_apply, h, sum_SB_row L hL b]

theorem Theta_mul_onesMat (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta L ξ * onesMat L = (1 - ξ)⁻¹ • onesMat L := by
  ext a b
  simp [Matrix.mul_apply, sum_Theta_row L hL hξ a]

theorem onesMat_mul_Theta (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    onesMat L * Theta L ξ = (1 - ξ)⁻¹ • onesMat L := by
  ext a b
  have h : ∀ c, Theta L ξ c b = Theta L ξ b c := fun c =>
    congrFun (congrFun (Theta_transpose L hL hξ) b) c
  simp [Matrix.mul_apply, h, sum_Theta_row L hL hξ b]

end Defs

section ShermanMorrison

variable (L : ℕ) [NeZero L]

omit [NeZero L] in
theorem one_sub_smul_SBTilde (ζ ξ : ℂ) :
    1 - ξ • SBTilde L ζ = (1 - (ξ * (1 - ζ)) • SB L) - (ξ * ζ / L) • onesMat L := by
  rw [SBTilde, smul_add, smul_smul, smul_smul, mul_div_assoc]
  abel

/-- **Sherman–Morrison for the zero mode**: `(1 - ξS̃^(B))⁻¹ = Θ_{ξ(1-ζ)} + α J`. -/
theorem ThetaTilde_eq (hL : 3 ≤ L) {ζ ξ : ℂ} (hT : ‖ξ * (1 - ζ)‖ < 1) (hξ1 : ξ ≠ 1) :
    ThetaTilde L ζ ξ = Theta L (ξ * (1 - ζ)) + zeroMode L ζ ξ • onesMat L := by
  set T := ξ * (1 - ζ) with hTdef
  set β : ℂ := ξ * ζ / L with hβ
  set α := zeroMode L ζ ξ with hα
  set J := onesMat L with hJ
  set M := 1 - ξ • SBTilde L ζ with hM
  set B := Theta L T + α • J with hB
  have hM' : M = (1 - T • SB L) - β • J := one_sub_smul_SBTilde L ζ ξ
  have hT1 : (1 : ℂ) - T ≠ 0 := one_sub_ne_zero hT
  have hξ1' : (1 : ℂ) - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ1)
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  -- the scalar identity behind Sherman–Morrison
  have hscal : -(β * (1 - T)⁻¹) + α * (1 - T) - α * β * L = 0 := by
    rw [hα, hβ, zeroMode, hTdef]
    field_simp
    ring
  have hJS : J * SB L = J := onesMat_mul_SB L hL
  have hSJ : SB L * J = J := SB_mul_onesMat L hL
  have hΘJ : Theta L T * J = (1 - T)⁻¹ • J := Theta_mul_onesMat L hL hT
  have hJΘ : J * Theta L T = (1 - T)⁻¹ • J := onesMat_mul_Theta L hL hT
  have hJJ : J * J = (L : ℂ) • J := onesMat_mul_onesMat L
  have hBM : B * M = 1 := by
    have e : B * M = Theta L T * (1 - T • SB L) - β • (Theta L T * J)
        + α • (J - T • (J * SB L)) - (α * β) • (J * J) := by
      rw [hB, hM']
      simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul,
        smul_sub, smul_add]
      module
    rw [e, Theta_mul L hL hT, hΘJ, hJS, hJJ]
    have e2 : (1 : Matrix (ZMod L) (ZMod L) ℂ) - β • ((1 - T)⁻¹ • J) + α • (J - T • J)
        - (α * β) • ((L : ℂ) • J)
        = 1 + (-(β * (1 - T)⁻¹) + α * (1 - T) - α * β * L) • J := by module
    rw [e2, hscal, zero_smul, add_zero]
  have hMB : M * B = 1 := by
    have e : M * B = (1 - T • SB L) * Theta L T + α • (J - T • (SB L * J))
        - β • (J * Theta L T) - (β * α) • (J * J) := by
      rw [hB, hM']
      simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul,
        smul_sub]
      module
    rw [e, mul_Theta L hL hT, hJΘ, hSJ, hJJ]
    have e2 : (1 : Matrix (ZMod L) (ZMod L) ℂ) + α • (J - T • J) - β • ((1 - T)⁻¹ • J)
        - (β * α) • ((L : ℂ) • J)
        = 1 + (-(β * (1 - T)⁻¹) + α * (1 - T) - α * β * L) • J := by module
    rw [e2, hscal, zero_smul, add_zero]
  have hu : Ring.inverse M = B := by
    have := Ring.inverse_unit (⟨M, B, hMB, hBM⟩ : (Matrix (ZMod L) (ZMod L) ℂ)ˣ)
    simpa using this
  exact hu

/-- Entrywise form of `ThetaTilde_eq`. -/
theorem ThetaTilde_apply (hL : 3 ≤ L) {ζ ξ : ℂ} (hT : ‖ξ * (1 - ζ)‖ < 1) (hξ1 : ξ ≠ 1)
    (a b : ZMod L) :
    ThetaTilde L ζ ξ a b = Theta L (ξ * (1 - ζ)) a b + zeroMode L ζ ξ := by
  rw [ThetaTilde_eq L hL hT hξ1]
  simp

/-- **End of Section 7.2**: removing the zero mode does not change differences,
`[(1-ξS̃)⁻¹]_{ab} - [(1-ξS̃)⁻¹]_{a'b'} = [(1-ξ(1-ζ)S)⁻¹]_{ab} - [(1-ξ(1-ζ)S)⁻¹]_{a'b'}`. -/
theorem ThetaTilde_sub_ThetaTilde (hL : 3 ≤ L) {ζ ξ : ℂ} (hT : ‖ξ * (1 - ζ)‖ < 1)
    (hξ1 : ξ ≠ 1) (a b a' b' : ZMod L) :
    ThetaTilde L ζ ξ a b - ThetaTilde L ζ ξ a' b'
      = Theta L (ξ * (1 - ζ)) a b - Theta L (ξ * (1 - ζ)) a' b' := by
  rw [ThetaTilde_apply L hL hT hξ1, ThetaTilde_apply L hL hT hξ1]
  ring

end ShermanMorrison

section Comparison

variable {ξ : ℂ} {ζ : ℝ}

theorem norm_mul_one_sub_lt_one (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ‖ξ * (1 - (ζ : ℂ))‖ < 1 := by
  have h : (1 - (ζ : ℂ)) = ((1 - ζ : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, h, Complex.norm_of_nonneg (by linarith)]
  nlinarith [norm_nonneg ξ]

/-- Upper comparison: `|1 - ξ(1-ζ)| ≤ |1-ξ| + ζ`. -/
theorem norm_one_sub_mul_le (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 ≤ ζ) :
    ‖1 - ξ * (1 - (ζ : ℂ))‖ ≤ ‖1 - ξ‖ + ζ := by
  have e : 1 - ξ * (1 - (ζ : ℂ)) = (1 - ξ) + ξ * (ζ : ℂ) := by ring
  rw [e]
  calc ‖(1 - ξ) + ξ * (ζ : ℂ)‖ ≤ ‖1 - ξ‖ + ‖ξ * (ζ : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖1 - ξ‖ + ζ := by
      rw [norm_mul, Complex.norm_of_nonneg hζ0]
      nlinarith [norm_nonneg ξ]

theorem re_le_one_of_norm_le_one (hξ : ‖ξ‖ ≤ 1) : ξ.re ≤ 1 :=
  (Complex.re_le_norm ξ).trans hξ

theorem normSq_one_sub_mul (ζ : ℝ) :
    ‖1 - ξ * (1 - (ζ : ℂ))‖ ^ 2
      = (1 - ξ.re * (1 - ζ)) ^ 2 + (ξ.im * (1 - ζ)) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Lower comparison: `(1-ζ)|1-ξ| ≤ |1 - ξ(1-ζ)|` for `‖ξ‖ ≤ 1`, `0 ≤ ζ ≤ 1`.
No smallness of `ζ` relative to `|1-ξ|` is needed in this direction. -/
theorem le_norm_one_sub_mul (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    (1 - ζ) * ‖1 - ξ‖ ≤ ‖1 - ξ * (1 - (ζ : ℂ))‖ := by
  have hx := re_le_one_of_norm_le_one hξ
  have h2 : ((1 - ζ) * ‖1 - ξ‖) ^ 2 ≤ ‖1 - ξ * (1 - (ζ : ℂ))‖ ^ 2 := by
    rw [normSq_one_sub_mul, mul_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    have hk : 0 ≤ 2 - ζ - 2 * ξ.re * (1 - ζ) := by nlinarith
    nlinarith [mul_nonneg hζ0 hk]
  exact (pow_le_pow_iff_left₀ (mul_nonneg (by linarith) (norm_nonneg _)) (norm_nonneg _)
    two_ne_zero).1 h2

/-- **End of Section 7.2**: `|1-ξ| ∼ |1-ξ(1-ζ)|`, precisely
`|1-ξ|/2 ≤ |1-ξ(1-ζ)| ≤ 2|1-ξ|` for `‖ξ‖ ≤ 1`, `0 ≤ ζ ≤ 1/2`, `ζ ≤ |1-ξ|`. -/
theorem norm_one_sub_mul_comparable (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1 / 2)
    (hζξ : ζ ≤ ‖1 - ξ‖) :
    ‖1 - ξ‖ / 2 ≤ ‖1 - ξ * (1 - (ζ : ℂ))‖ ∧ ‖1 - ξ * (1 - (ζ : ℂ))‖ ≤ 2 * ‖1 - ξ‖ := by
  refine ⟨?_, ?_⟩
  · have h := le_norm_one_sub_mul hξ hζ0 (by linarith)
    nlinarith [norm_nonneg (1 - ξ)]
  · have h := norm_one_sub_mul_le hξ hζ0
    linarith

theorem sqrt_le_two_mul_sqrt {a b : ℝ} (h : a ≤ 4 * b) :
    Real.sqrt a ≤ 2 * Real.sqrt b := by
  calc Real.sqrt a ≤ Real.sqrt (4 * b) := Real.sqrt_le_sqrt h
    _ = 2 * Real.sqrt b := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

/-- Comparable `|1-ξ|` give comparable `ℓ̂`: if `|1-ξ| ≤ 4|1-ξ'|` then `ℓ̂(ξ') ≤ 2ℓ̂(ξ)`. -/
theorem ellHat_le_two_mul (L : ℕ) {ξ ξ' : ℂ} (h0 : 0 < ‖1 - ξ‖) (h0' : 0 < ‖1 - ξ'‖)
    (h : ‖1 - ξ‖ ≤ 4 * ‖1 - ξ'‖) : ellHat L ξ' ≤ 2 * ellHat L ξ := by
  have hs := sqrt_le_two_mul_sqrt h
  have ha := Real.sqrt_pos.2 h0
  have hb := Real.sqrt_pos.2 h0'
  have hinv : 1 / Real.sqrt ‖1 - ξ'‖ ≤ 2 * (1 / Real.sqrt ‖1 - ξ‖) := by
    rw [mul_one_div, div_le_div_iff₀ hb ha]
    linarith
  unfold ellHat
  rcases le_total (1 / Real.sqrt ‖1 - ξ‖) (L : ℝ) with hc | hc
  · rw [min_eq_left hc]
    exact (min_le_left _ _).trans hinv
  · rw [min_eq_right hc]
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    exact (min_le_right _ _).trans (by linarith)

end Comparison

section Transfer

variable {L : ℕ} [NeZero L] {ξ : ℂ} {ζ : ℝ}

omit [NeZero L] in
/-- The standing facts behind the transfer: with `T = ξ(1-ζ)`, `‖T‖ < 1`, `ξ ≠ 1`,
`|1-ξ|/2 ≤ |1-T|`, and `ℓ̂(T) ≤ 2ℓ̂(ξ)`, `ℓ̂(ξ) ≤ 2ℓ̂(T)`. -/
theorem zeroMode_setup (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1 / 2)
    (hζξ : ζ ≤ ‖1 - ξ‖) :
    ‖ξ * (1 - (ζ : ℂ))‖ < 1 ∧ ξ ≠ 1 ∧ 0 < ‖1 - ξ‖ ∧
      ‖1 - ξ‖ / 2 ≤ ‖1 - ξ * (1 - (ζ : ℂ))‖ ∧
      ellHat L (ξ * (1 - (ζ : ℂ))) ≤ 2 * ellHat L ξ ∧
      ellHat L ξ ≤ 2 * ellHat L (ξ * (1 - (ζ : ℂ))) := by
  have hT := norm_mul_one_sub_lt_one hξ hζ0 (by linarith)
  have ha : 0 < ‖1 - ξ‖ := lt_of_lt_of_le hζ0 hζξ
  have hξ1 : ξ ≠ 1 := by
    rintro rfl
    simp at ha
  obtain ⟨hlo, hhi⟩ := norm_one_sub_mul_comparable hξ hζ0.le hζ1 hζξ
  have haT : 0 < ‖1 - ξ * (1 - (ζ : ℂ))‖ := by linarith
  refine ⟨hT, hξ1, ha, hlo, ?_, ?_⟩
  · exact ellHat_le_two_mul L ha haT (by linarith)
  · exact ellHat_le_two_mul L haT ha (by linarith)

end Transfer

end RBM
