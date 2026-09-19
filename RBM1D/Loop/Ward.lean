/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Example3
import RBM1D.Defs.Semicircle

/-!
# Ward's identity for `K`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.6, (3.13):
for `σ₁ = +` and `σₙ = -`,
`∑_{aₙ} K_{t,σ,a} = (K_{t,σ⁺,a/aₙ} - K_{t,σ⁻,a/aₙ}) / (2 W i η_t)`,
where `σ^± = (±, σ₂, …, σ_{n-1})`, `a/aₙ = (a₁, …, a_{n-1})` and `η_t = (1 - t) Im m`.

Here `m = m^{(E)}` and `m(σ)` is `RBM.mSigma E`, so `|m| = 1` (`RBM.norm_mE`).  This file
proves **Step 1** of the paper's proof: the identity for the explicit `2`- and `3`-loops
(Example 2.15 and Example 2.16), with `K_{t,±,a} = m(±)` for `n = 1` (Definition 2.12).

The key matrix identity at `n = 3` is `m A - m̄ B = (m - m̄) A B` for
`A = Θ_{t m q}`, `B = Θ_{t m̄ q}` (`RBM.mul_Theta_sub_mul_Theta`): the `S^(B)` terms of
`m B⁻¹ - m̄ A⁻¹` cancel because `m · t m̄ q = m̄ · t m q`.

Steps 2–5 (general `n`: the difference of the two sides satisfies the homogeneous linear
equation (3.18) with zero initial value, then uniqueness) are not done yet.

## Main results

* `RBM.etaT`               : `η_t = (1 - t) Im m^{(E)}`, the imaginary part of `z_t` (2.35)
* `RBM.ward_two`           : (3.13) at `n = 2`, i.e. (3.16)
* `RBM.mul_Theta_sub_mul_Theta` : `m A - m̄ B = (m - m̄) A B`
* `RBM.ward_three`         : (3.13) at `n = 3`
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

/-- `η_t = Im z_t^{(E)} = (1 - t) Im m^{(E)}` (2.35). -/
noncomputable def etaT (E t : ℝ) : ℝ := (1 - t) * (mE E).im

theorem etaT_eq_zt_im (E t : ℝ) : etaT E t = (zt E t).im := by
  rw [etaT, zt_im]

section Unit

variable {E : ℝ}

theorem mSigma_true (E : ℝ) : mSigma E true = mE E := rfl

theorem mSigma_false (E : ℝ) : mSigma E false = (starRingEnd ℂ) (mE E) := rfl

/-- `m m̄ = |m|² = 1`. -/
theorem mE_mul_conj (hE : |E| ≤ 2) : mE E * (starRingEnd ℂ) (mE E) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE]
  norm_num

/-- `m - m̄ = 2 i Im m`. -/
theorem mE_sub_conj (E : ℝ) : mE E - (starRingEnd ℂ) (mE E) = 2 * Complex.I * (mE E).im := by
  apply Complex.ext
  · simp
  · simp
    ring

/-- The right-hand side of (3.13) has the denominator `2 W i η_t`; with `m - m̄ = 2 i Im m`
it reduces to `W (1 - t)`. -/
theorem sub_div_two_W_I_etaT (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) (c : ℂ) :
    c * (mE E - (starRingEnd ℂ) (mE E)) / (2 * W * Complex.I * etaT E t)
      = c / ((W : ℂ) * (1 - t)) := by
  have hIm : ((mE E).im : ℂ) ≠ 0 := by exact_mod_cast (mE_im_pos hE).ne'
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  rw [mE_sub_conj, etaT]
  push_cast
  field_simp

end Unit

section Two

variable {E : ℝ}

/-- **(3.13) at `n = 2`**, i.e. (3.16):
`∑_{a₂} K_{t,(+,-),(a₁,a₂)} = W⁻¹ (1 - t)⁻¹ = (m(+) - m(-)) / (2 W i η_t)`. -/
theorem ward_two (hL : 3 ≤ L) (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a₁ : ZMod L) :
    ∑ a₂ : ZMod L, kTwo L W (mSigma E) t true false a₁ a₂
      = (mSigma E true - mSigma E false) / (2 * W * Complex.I * etaT E t) := by
  have hmm : mSigma E true * mSigma E false = 1 := mE_mul_conj hE.le
  have ht : ‖((t : ℂ) * 1)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]
    exact ht1
  simp only [kTwo, hmm, ← Finset.mul_sum]
  rw [sum_Theta_row L hL ht, mSigma_true, mSigma_false,
    show mE E - (starRingEnd ℂ) (mE E) = 1 * (mE E - (starRingEnd ℂ) (mE E)) by ring,
    sub_div_two_W_I_etaT W hE ht1]
  field_simp

end Two

section Three

variable {E : ℝ}

/-- The matrix identity behind (3.13) at `n = 3`: for `A = Θ_{ξ₁}`, `B = Θ_{ξ₂}` with
`m ξ₂ = m' ξ₁`, `m A - m' B = (m - m') A B`. -/
theorem mul_Theta_sub_mul_Theta (hL : 3 ≤ L) {m m' ξ₁ ξ₂ : ℂ} (h₁ : ‖ξ₁‖ < 1) (h₂ : ‖ξ₂‖ < 1)
    (h : m * ξ₂ = m' * ξ₁) :
    m • Theta L ξ₁ - m' • Theta L ξ₂ = (m - m') • (Theta L ξ₁ * Theta L ξ₂) := by
  have hA : Theta L ξ₁ * (1 - ξ₁ • SB L) = 1 := Theta_mul L hL h₁
  have hB : (1 - ξ₂ • SB L) * Theta L ξ₂ = 1 := mul_Theta L hL h₂
  have key : m • (1 - ξ₂ • SB L) - m' • (1 - ξ₁ • SB L) = (m - m') • (1 : Matrix _ _ ℂ) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, h, sub_smul]
    abel
  calc m • Theta L ξ₁ - m' • Theta L ξ₂
      = Theta L ξ₁ * (m • (1 - ξ₂ • SB L) - m' • (1 - ξ₁ • SB L)) * Theta L ξ₂ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.smul_mul, Matrix.mul_assoc, hB, hA, Matrix.mul_one, Matrix.one_mul]
    _ = (m - m') • (Theta L ξ₁ * Theta L ξ₂) := by
        rw [key, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **(3.13) at `n = 3`**: for `σ = (+, σ₂, -)`,
`∑_{a₃} K_{t,σ,(a₁,a₂,a₃)} = (K_{t,(+,σ₂),(a₁,a₂)} - K_{t,(-,σ₂),(a₁,a₂)}) / (2 W i η_t)`. -/
theorem ward_three (hL : 3 ≤ L) (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₂ : Bool) (a₁ a₂ : ZMod L) :
    ∑ a₃ : ZMod L, kThree W (mSigma E) t true σ₂ false a₁ a₂ a₃
      = (kTwo L W (mSigma E) t true σ₂ a₁ a₂ - kTwo L W (mSigma E) t false σ₂ a₁ a₂)
          / (2 * W * Complex.I * etaT E t) := by
  set m := mE E with hm
  set q := mSigma E σ₂
  have hmm : m * (starRingEnd ℂ) m = 1 := mE_mul_conj hE.le
  have hq : ‖q‖ = 1 := norm_mSigma hE.le σ₂
  have hnm : ‖m‖ = 1 := norm_mE hE.le
  have hnm' : ‖(starRingEnd ℂ) m‖ = 1 := by rw [Complex.norm_conj, hnm]
  have htn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  have h₁ : ‖(t : ℂ) * (m * q)‖ < 1 := by rw [norm_mul, norm_mul, htn, hnm, hq]; linarith
  have h₂ : ‖(t : ℂ) * ((starRingEnd ℂ) m * q)‖ < 1 := by
    rw [norm_mul, norm_mul, htn, hnm', hq]; linarith
  have h₃ : ‖(t : ℂ) * ((starRingEnd ℂ) m * m)‖ < 1 := by
    rw [mul_comm ((starRingEnd ℂ) m), hmm, mul_one, htn]; exact ht1
  have h₂' : ‖(t : ℂ) * (q * (starRingEnd ℂ) m)‖ < 1 := by rwa [mul_comm q]
  -- the column sum of `Θ_{t m̄ m}` is `(1 - t)⁻¹`
  have hcol : ∀ b : ZMod L, ∑ a₃ : ZMod L, thetaEdge L (mSigma E) t false true a₃ b
      = (1 - (t : ℂ))⁻¹ := by
    intro b
    have hsym := Theta_transpose L hL h₃
    simp only [thetaEdge, mSigma_true, mSigma_false, ← hm]
    rw [← hsym]
    simp only [Matrix.transpose_apply]
    rw [sum_Theta_row L hL h₃, mul_comm ((starRingEnd ℂ) m), hmm, mul_one]
  -- the left-hand side
  have hlhs : ∑ a₃ : ZMod L, kThree W (mSigma E) t true σ₂ false a₁ a₂ a₃
      = (W : ℂ)⁻¹ ^ 2 * q * (1 - (t : ℂ))⁻¹ *
          (thetaEdge L (mSigma E) t true σ₂ * thetaEdge L (mSigma E) t σ₂ false) a₁ a₂ := by
    simp only [kThree, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [← Finset.mul_sum, hcol b]
    have hsymB : thetaEdge L (mSigma E) t σ₂ false a₂ b
        = thetaEdge L (mSigma E) t σ₂ false b a₂ := by
      have := Theta_transpose L hL h₂'
      simp only [thetaEdge, mSigma_false, ← hm]
      exact congrFun (congrFun this b) a₂
    rw [hsymB, mSigma_true, mSigma_false, ← hm]
    have : m * q * (starRingEnd ℂ) m = q := by
      rw [mul_comm m q, mul_assoc, hmm, mul_one]
    rw [this]
    ring
  -- the matrix identity
  have hmat := mul_Theta_sub_mul_Theta L hL h₁ h₂ (m := m) (m' := (starRingEnd ℂ) m)
    (by ring)
  have hent := congrFun (congrFun hmat a₁) a₂
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hent
  have hAB : (thetaEdge L (mSigma E) t true σ₂ * thetaEdge L (mSigma E) t σ₂ false) a₁ a₂
      = (Theta L ((t : ℂ) * (m * q)) * Theta L ((t : ℂ) * ((starRingEnd ℂ) m * q))) a₁ a₂ := by
    simp only [thetaEdge, mSigma_true, mSigma_false, ← hm]
    rw [mul_comm q ((starRingEnd ℂ) m)]
  rw [hlhs, hAB]
  simp only [kTwo, mSigma_true, mSigma_false, ← hm]
  rw [show (W : ℂ)⁻¹ * (m * q) * Theta L ((t : ℂ) * (m * q)) a₁ a₂
        - (W : ℂ)⁻¹ * ((starRingEnd ℂ) m * q) * Theta L ((t : ℂ) * ((starRingEnd ℂ) m * q)) a₁ a₂
        = (W : ℂ)⁻¹ * q * (m * Theta L ((t : ℂ) * (m * q)) a₁ a₂
          - (starRingEnd ℂ) m * Theta L ((t : ℂ) * ((starRingEnd ℂ) m * q)) a₁ a₂) by ring,
    hent, show (W : ℂ)⁻¹ * q * ((m - (starRingEnd ℂ) m) *
        (Theta L ((t : ℂ) * (m * q)) * Theta L ((t : ℂ) * ((starRingEnd ℂ) m * q))) a₁ a₂)
      = (W : ℂ)⁻¹ * q *
        (Theta L ((t : ℂ) * (m * q)) * Theta L ((t : ℂ) * ((starRingEnd ℂ) m * q))) a₁ a₂
          * (m - (starRingEnd ℂ) m) by ring,
    hm, sub_div_two_W_I_etaT W hE ht1]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  field_simp

end Three

end RBM
