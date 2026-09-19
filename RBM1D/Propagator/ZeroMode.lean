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
*Delocalization of One-Dimensional Random Band Matrices*, end of Section 7.2 (p. 84).

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
* `RBM.ThetaTilde_sub_ThetaTilde` : the difference identity of p. 84
* `RBM.norm_one_sub_mul_le`, `RBM.le_norm_one_sub_mul`, `RBM.norm_one_sub_mul_ge_zeta` :
  one-sided comparisons of `|1-ξ|` and `|1-ξ(1-ζ)|` for `‖ξ‖ ≤ 1`, `0 ≤ ζ ≤ 1`
* `RBM.norm_one_sub_mul_comparable` : `|1-ξ|/2 ≤ |1-ξ(1-ζ)| ≤ 2|1-ξ|` when
  `0 < ζ ≤ 1/2` and `ζ ≤ |1-ξ|`
* `RBM.norm_ThetaTilde_sub_zeroMode_le` : (2.52) for `S̃^(B)`, up to the constant zero mode
* `RBM.norm_ThetaTilde_sub_shift_le`, `RBM.norm_ThetaTilde_second_diff_le` :
  (2.53) and (2.54) for `S̃^(B)` (the zero mode cancels)

## Deviations from the paper

* The comparison `|1-ξ| ∼ |1-ξ(1-ζ)|` is false without a smallness condition relating `ζ`
  to `|1-ξ|` (take `ξ = 1`).  We assume `ζ ≤ |1-ξ|`; in the paper's application
  (`ξ ∈ {m², |m|²}`, `Im z = N^{-1+c/3}`, `ζ_U ∼ N^{-1+τ_U}`) this is the requirement
  `ζ_U ≲ η`.  Conversely `|1-ξ(1-ζ)| ≥ ζ` always (`norm_one_sub_mul_ge_zeta`), so the
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

/-- **End of Section 7.2 (p. 84)**: removing the zero mode does not change differences,
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

/-- `|1 - ξ(1-ζ)| ≥ ζ` for `‖ξ‖ ≤ 1`, `0 ≤ ζ ≤ 1`.  Together with `norm_one_sub_mul_le` this
shows that `|1-ξ| ∼ |1-ξ(1-ζ)|` holds iff `ζ ≲ |1-ξ|`. -/
theorem norm_one_sub_mul_ge_zeta (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ζ ≤ ‖1 - ξ * (1 - (ζ : ℂ))‖ := by
  have hx := re_le_one_of_norm_le_one hξ
  have h2 : ζ ^ 2 ≤ ‖1 - ξ * (1 - (ζ : ℂ))‖ ^ 2 := by
    rw [normSq_one_sub_mul]
    have hk : ζ ≤ 1 - ξ.re * (1 - ζ) := by nlinarith
    nlinarith [sq_nonneg (ξ.im * (1 - ζ))]
  exact (pow_le_pow_iff_left₀ hζ0 (norm_nonneg _) two_ne_zero).1 h2

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

/-- **(2.52) for `S̃^(B)`**, up to the constant zero mode `α = zeroMode L ζ ξ`:
`|[(1-ξS̃)⁻¹]_{xy} - α| ≤ C e^{-c‖x-y‖/ℓ̂(ξ)} / (|1-ξ| ℓ̂(ξ))`,
for `‖ξ‖ ≤ 1`, `0 < ζ ≤ 1/2`, `ζ ≤ |1-ξ|`. -/
theorem norm_ThetaTilde_sub_zeroMode_le (hL : 3 ≤ L) (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 < ζ)
    (hζ1 : ζ ≤ 1 / 2) (hζξ : ζ ≤ ‖1 - ξ‖) (x y : ZMod L) :
    ‖ThetaTilde L ζ ξ x y - zeroMode L ζ ξ‖ ≤
      4 * cTwo52 * Real.exp (-(cZero / 2 * zdist L (x - y) / ellHat L ξ))
        / (‖1 - ξ‖ * ellHat L ξ) := by
  obtain ⟨hT, hξ1, ha, hlo, hℓ1, hℓ2⟩ :=
    zeroMode_setup (L := L) hξ hζ0 hζ1 hζξ
  set T : ℂ := ξ * (1 - (ζ : ℂ)) with hTdef
  rw [ThetaTilde_apply L hL hT hξ1, add_sub_cancel_right]
  have h := norm_Theta_apply_le_complex hL hT x y
  have hℓT : 1 / 2 ≤ ellHat L T := half_le_ellHat L hL hT
  have hℓTpos : 0 < ellHat L T := by linarith
  have hℓpos : 0 < ellHat L ξ := by linarith
  set d : ℝ := (zdist L (x - y) : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hc := cZero_pos
  have hC := cTwo52_pos
  -- the exponential: `ℓ̂(T) ≤ 2ℓ̂(ξ)`
  have hexp : Real.exp (-(cZero * d / ellHat L T))
      ≤ Real.exp (-(cZero / 2 * d / ellHat L ξ)) := by
    apply Real.exp_le_exp.2
    have : cZero / 2 * d / ellHat L ξ ≤ cZero * d / ellHat L T := by
      rw [div_le_div_iff₀ hℓpos hℓTpos]
      nlinarith [mul_nonneg hc.le hd0]
    linarith
  -- the prefactor: `|1-T| ℓ̂(T) ≥ |1-ξ| ℓ̂(ξ) / 4`
  have hden : ‖1 - ξ‖ * ellHat L ξ / 4 ≤ ‖1 - T‖ * ellHat L T := by
    nlinarith [mul_le_mul hlo (show ellHat L ξ / 2 ≤ ellHat L T by linarith)
      (by linarith) (norm_nonneg (1 - T))]
  have hden0 : 0 < ‖1 - ξ‖ * ellHat L ξ / 4 := by positivity
  refine h.trans ?_
  calc cTwo52 * Real.exp (-(cZero * d / ellHat L T)) / (‖1 - T‖ * ellHat L T)
      ≤ cTwo52 * Real.exp (-(cZero / 2 * d / ellHat L ξ)) / (‖1 - ξ‖ * ellHat L ξ / 4) := by
        apply div_le_div₀ (by positivity) (by gcongr) hden0 hden
    _ = 4 * cTwo52 * Real.exp (-(cZero / 2 * d / ellHat L ξ)) / (‖1 - ξ‖ * ellHat L ξ) := by
        field_simp

/-- **(2.53) for `S̃^(B)`**: the zero mode cancels in the difference, so
`|[(1-ξS̃)⁻¹]_{x,y} - [(1-ξS̃)⁻¹]_{x,y+1}| ≤ C / (ℓ̂(ξ) |1-ξ|^{1/2})`. -/
theorem norm_ThetaTilde_sub_shift_le (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ ≤ 1) (hζ0 : 0 < ζ)
    (hζ1 : ζ ≤ 1 / 2) (hζξ : ζ ≤ ‖1 - ξ‖) (x y : ZMod L) :
    ‖ThetaTilde L ζ ξ x y - ThetaTilde L ζ ξ x (y + 1)‖
      ≤ 576 / (ellHat L ξ * Real.sqrt ‖1 - ξ‖) := by
  obtain ⟨hT, hξ1, ha, hlo, hℓ1, hℓ2⟩ :=
    zeroMode_setup (L := L) hξ hζ0 hζ1 hζξ
  set T : ℂ := ξ * (1 - (ζ : ℂ)) with hTdef
  have hT0 : T ≠ 0 := by
    have : (1 : ℂ) - (ζ : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      have : (ζ : ℝ) = 1 := by exact_mod_cast h.symm
      linarith
    exact mul_ne_zero hξ0 this
  rw [ThetaTilde_sub_ThetaTilde L hL hT hξ1]
  have h := norm_Theta_sub_shift_le_complex L hL hT0 hT x y
  have hℓT : 1 / 2 ≤ ellHat L T := half_le_ellHat L hL hT
  have hℓpos : 0 < ellHat L ξ := by linarith
  have hs : Real.sqrt ‖1 - ξ‖ ≤ 2 * Real.sqrt ‖1 - T‖ :=
    sqrt_le_two_mul_sqrt (by linarith)
  have hsa : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.2 ha
  have hden : ellHat L ξ * Real.sqrt ‖1 - ξ‖ / 4 ≤ ellHat L T * Real.sqrt ‖1 - T‖ := by
    nlinarith [mul_le_mul hℓ2 hs hsa.le (by linarith)]
  have hden0 : 0 < ellHat L ξ * Real.sqrt ‖1 - ξ‖ / 4 := by positivity
  refine h.trans ?_
  calc (144 : ℝ) / (ellHat L T * Real.sqrt ‖1 - T‖)
      ≤ 144 / (ellHat L ξ * Real.sqrt ‖1 - ξ‖ / 4) :=
        div_le_div_of_nonneg_left (by norm_num) hden0 hden
    _ = 576 / (ellHat L ξ * Real.sqrt ‖1 - ξ‖) := by field_simp; norm_num

/-- **(2.54) for `S̃^(B)`**: the zero mode cancels in the second difference, so
`|2Θ̃_{x,y} - Θ̃_{x,y+1} - Θ̃_{x,y-1}| ≤ 1728 / (‖x-y‖ + 1)` for `x ≠ y`. -/
theorem norm_ThetaTilde_second_diff_le (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ ≤ 1)
    (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1 / 2) (hζξ : ζ ≤ ‖1 - ξ‖) {x y : ZMod L} (hxy : x ≠ y) :
    ‖2 * ThetaTilde L ζ ξ x y - ThetaTilde L ζ ξ x (y + 1) - ThetaTilde L ζ ξ x (y - 1)‖
      ≤ 1728 / ((zdist L (x - y) : ℝ) + 1) := by
  obtain ⟨hT, hξ1, -, -, -, -⟩ := zeroMode_setup (L := L) hξ hζ0 hζ1 hζξ
  have hT0 : ξ * (1 - (ζ : ℂ)) ≠ 0 := by
    have : (1 : ℂ) - (ζ : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      have : (ζ : ℝ) = 1 := by exact_mod_cast h.symm
      linarith
    exact mul_ne_zero hξ0 this
  have e : 2 * ThetaTilde L ζ ξ x y - ThetaTilde L ζ ξ x (y + 1) - ThetaTilde L ζ ξ x (y - 1)
      = 2 * Theta L (ξ * (1 - ζ)) x y - Theta L (ξ * (1 - ζ)) x (y + 1)
        - Theta L (ξ * (1 - ζ)) x (y - 1) := by
    simp only [ThetaTilde_apply L hL hT hξ1]
    ring
  rw [e]
  exact norm_Theta_second_diff_le_inv_dist_complex L hL hT0 hT hxy

end Transfer

end RBM
