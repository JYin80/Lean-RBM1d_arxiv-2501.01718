/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Example3
import RBM1D.Loop.Unique
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
equation (3.18) with zero initial value, then Grönwall) are done at `n = 2` for a general
solution (`RBM.ward_two_of_isPrimitive`); `n ≥ 3` is not done yet.

## Main results

* `RBM.etaT`               : `η_t = (1 - t) Im m^{(E)}`, the imaginary part of `z_t` (2.35)
* `RBM.ward_two`           : (3.13) at `n = 2`, i.e. (3.16)
* `RBM.mul_Theta_sub_mul_Theta` : `m A - m̄ B = (m - m̄) A B`
* `RBM.ward_three`         : (3.13) at `n = 3`
* `RBM.ward_two_of_isPrimitive` : (3.13) at `n = 2` for **any** solution of Definition 2.12
  (with bounded `2`-loops), by the Grönwall argument of Step 2
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

section GeneralTwo

/-!
### (3.13) at `n = 2` for a general solution

The same Grönwall argument that will close the induction (Step 2 of the paper), at `n = 2`.
With `c_t = (W (1 - t))⁻¹` and `D_t(a₁) = ∑_{a₂} K_{t,(+,-),(a₁,a₂)} - c_t`, the primitive
equation (2.55) and `∑_b S_{ab} = 1` give
`∂_t D(a₁) = W ∑_{a,b} K_{(a₁,a)} S_{ab} D(b) + W c_t D(a₁)`, because `∂_t c_t = W c_t²`;
and `D_0 = 0`.
-/

variable {E : ℝ}

/-- `c_t = (W (1 - t))⁻¹`, the common value of the two sides of (3.16). -/
noncomputable def wardC (W : ℕ) (t : ℝ) : ℂ := ((W : ℂ) * (1 - t))⁻¹

theorem hasDerivAt_wardC (W : ℕ) [NeZero W] {t : ℝ} (ht1 : t < 1) :
    HasDerivAt (wardC W) (W * wardC W t ^ 2) t := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  have h1 : HasDerivAt (fun s : ℝ => (W : ℂ) * (1 - (s : ℂ))) (-(W : ℂ)) t := by
    have := ((hasDerivAt_id t).ofReal_comp.const_sub 1).const_mul (W : ℂ)
    simpa using this
  have h2 := h1.inv (mul_ne_zero hW ht)
  refine h2.congr_deriv ?_
  simp only [wardC]
  field_simp

/-- **(3.13) at `n = 2`** for any solution of Definition 2.12 with `m = m^{(E)}`, on `[0, T₀]`
with `T₀ < 1`, whose `2`-loops stay bounded:
`∑_{a₂} K_{t,(+,-),(a₁,a₂)} = (K_{t,+,a₁} - K_{t,-,a₁}) / (2 W i η_t)`. -/
theorem ward_two_of_isPrimitive (hL : 3 ≤ L) (W : ℕ) [NeZero W] (hE : |E| < 2) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W (mSigma E) T K) {T₀ R : ℝ}
    (hT₀ : T₀ < 1) (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ a₁ : ZMod L,
      ∑ a₂ : ZMod L, K t ⟨[true, false], [a₁, a₂]⟩
        = (K t ⟨[true], [a₁]⟩ - K t ⟨[false], [a₁]⟩) / (2 * W * Complex.I * etaT E t) := by
  let I : ZMod L → ZMod L → LoopIdx (ZMod L) := fun x y => ⟨[true, false], [x, y]⟩
  have hIWF : ∀ x y, (I x y).WF := fun _ _ => rfl
  have hIlen : ∀ x y, (I x y).length = 2 := fun _ _ => rfl
  let D : ℝ → ZMod L → ℂ := fun t x => ∑ y : ZMod L, K t (I x y) - wardC W t
  let D' : ℝ → ZMod L → ℂ := fun t x =>
    (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L, K t (I x a) * SB L a b * D t b + W * wardC W t * D t x
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    refine hasDerivAt_pi.2 fun x => ?_
    have hsum : HasDerivAt (fun s => ∑ y : ZMod L, K s (I x y))
        (∑ y : ZMod L, primRhs L W (K t) (I x y)) t :=
      HasDerivAt.fun_sum fun y _ => hK.1 t (hT ht) (I x y) (hIWF x y) (hIlen x y).ge
    refine (hsum.sub (hasDerivAt_wardC W ht1)).congr_deriv ?_
    -- the value of the derivative
    have hrow : ∀ b : ZMod L, ∑ y : ZMod L, K t (I b y) = D t b + wardC W t := by
      intro b
      simp only [D]
      ring
    have hprim : ∀ y, primRhs L W (K t) (I x y)
        = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L, K t (I x a) * SB L a b * K t (I b y) :=
      fun y => primRhs_two L W (K t) true false x y
    have hsplit : ∀ a, ∑ b : ZMod L, K t (I x a) * SB L a b * (D t b + wardC W t)
        = ∑ b : ZMod L, K t (I x a) * SB L a b * D t b + K t (I x a) * wardC W t := by
      intro a
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_SB_row L hL a]
      ring
    calc ∑ y : ZMod L, primRhs L W (K t) (I x y) - W * wardC W t ^ 2
        = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
            K t (I x a) * SB L a b * (∑ y : ZMod L, K t (I b y)) - W * wardC W t ^ 2 := by
          simp only [hprim, ← Finset.mul_sum]
          congr 2
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
            K t (I x a) * SB L a b * (D t b + wardC W t) - W * wardC W t ^ 2 := by
          simp only [hrow]
      _ = D' t x := by
          simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, hrow x, D']
          ring
  -- the bound
  set C : ℝ := W * ∑ _a : ZMod L, ∑ _b : ZMod L, R + (1 - T₀)⁻¹ with hC
  have hT₀' : 0 < 1 - T₀ := by linarith
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hc : ‖(W : ℂ) * wardC W t‖ ≤ (1 - T₀)⁻¹ := by
      have hW0 : (0 : ℝ) < W := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne W))
      rw [wardC, mul_inv, ← mul_assoc, mul_inv_cancel₀ hW, one_mul, norm_inv]
      have : ‖(1 : ℂ) - t‖ = 1 - t := by
        rw [show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg h1t.le]
      rw [this]
      exact inv_anti₀ hT₀' (by linarith [ht.2])
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg _))).2 fun x => ?_
    have hterm : ∀ a b : ZMod L, ‖K t (I x a) * SB L a b * D t b‖ ≤ R * ‖D t‖ := by
      intro a b
      rw [norm_mul, norm_mul]
      have hK' := hR t ht' (I x a) (hIWF x a) (hIlen x a)
      have hS := norm_SB_apply_le L hL a b
      have hDb := norm_le_pi_norm (D t) b
      calc ‖K t (I x a)‖ * ‖SB L a b‖ * ‖D t b‖ ≤ R * 1 * ‖D t‖ := by
            gcongr
        _ = R * ‖D t‖ := by ring
    calc ‖D' t x‖ ≤ ‖(W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L, K t (I x a) * SB L a b * D t b‖
          + ‖(W : ℂ) * wardC W t * D t x‖ := norm_add_le _ _
      _ ≤ W * ∑ _a : ZMod L, ∑ _b : ZMod L, R * ‖D t‖ + (1 - T₀)⁻¹ * ‖D t‖ := by
          gcongr
          · rw [norm_mul, Complex.norm_natCast]
            gcongr
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
            exact hterm a b
          · rw [norm_mul]
            exact mul_le_mul hc (norm_le_pi_norm (D t) x) (norm_nonneg _) (by positivity)
      _ = C * ‖D t‖ := by
          simp only [hC, add_mul, Finset.sum_mul, mul_assoc]
  -- the initial value
  have h0 : D 0 = 0 := by
    funext x
    simp only [D, Pi.zero_apply]
    have hinit : ∀ y, K 0 (I x y) = kTwo L W (mSigma E) 0 true false x y := fun y => by
      rw [hK.2.1 _ (hIWF x y) (hIlen x y).ge, kTwo_zero]
    simp only [hinit, kTwo, Complex.ofReal_zero, Theta_zero, mE_mul_conj hE.le,
      mSigma_true, mSigma_false, mul_one, ← Finset.mul_sum, Matrix.one_apply,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, wardC, sub_zero]
    ring
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt) h0 hbound
  intro t ht x
  have hDx := congrFun (hzero t ht) x
  simp only [D, Pi.zero_apply, sub_eq_zero] at hDx
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
  rw [hDx, hK.2.2 t (hT ht) true x, hK.2.2 t (hT ht) false x, mSigma_true, mSigma_false,
    show mE E - (starRingEnd ℂ) (mE E) = 1 * (mE E - (starRingEnd ℂ) (mE E)) by ring,
    sub_div_two_W_I_etaT W hE ht1, wardC]
  ring

end GeneralTwo

end RBM
