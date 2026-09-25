/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57

/-!
# Lemma 5.7, (5.36) in the proof-exponent shape

`RBM.Lemma57.ee_le_paper` (`Hierarchy/Lemma57.lean`) states (5.36) with the far-field bracket
`(cFar2 + 72) · (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} · (J*)³` merged into a single term.  Pilot
`docs/claude-team/pilot-P4P5-paper.md` §9 (B) explains why this displayed shape does not close
downstream: the merge step loses precision that the underlying proof — (5.71)+(5.72), i.e. the
abstract master `RBM.Lemma57.ee_le` — never needed to give up.

This file records the **unmerged**, sharper shape as `ee_le_reduced`, with exactly
`ee_le_paper`'s hypotheses, and proves that it implies `ee_le_paper`'s displayed shape
(`ee_le_paper_of_reduced`), confirming `ee_le_reduced` is the sharper statement.
-/

namespace RBM
namespace Lemma57

open Real Finset

variable (L : ℕ) [NeZero L]
variable {W ℓu ℓs ηu D J : ℝ}

/-- **(5.36)** in the shape actually given by the proof, (5.71)+(5.72): same hypotheses as
`ee_le_paper`, but the far-field bracket `cFar2 · (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} · J²` and
`72 · J³ · A_u^{-1}` are kept **apart**, rather than merged into a single `J³` term. This is
`ee_le` with `μ := ℓ_u/ℓ_s · √(ℓ_u/ℓ_s) · ((√(W ℓ_u η_u))⁻¹ · (W ℓ_u η_u)⁻¹)`, the same `μ`
`ee_le_paper` uses, followed only by the identity `(W ℓ_u η_u) · μ = ℓ_u/ℓ_s · √(ℓ_u/ℓ_s) ·
(√(W ℓ_u η_u))⁻¹` — not by `ee_le_paper`'s subsequent merge step. -/
theorem ee_le_reduced (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ W * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs) (a₁ a₂ : ZMod L)
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {ρ EE : ℝ} (hρ : 0 ≤ ρ)
    (hL6 : ∀ b, 0 ≤ L6 b) (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, L6 b ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹)
    (h564 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L6 b ≤ ρ)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h566 : ∀ b, L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ *
      (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)))
    (h572 : ∀ b, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT W ℓu ηu D (zdist L (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter
        (fun b : ZMod L => ¬ ((zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ))), L6 b) ≤
      ((2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W *
          (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)))
        + J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2)
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + cFar2 W ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹) * J ^ 2
        + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + (W * L * ρ + 2 * W * L * W ^ (-D) * J ^ 3 *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hA0 : (0 : ℝ) < W * ℓu * ηu := by linarith
  have hsA : (0 : ℝ) < √(W * ℓu * ηu) := Real.sqrt_pos.2 hA0
  have hμ : (0 : ℝ) ≤ ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹) := by
    positivity
  have hmain := ee_le L hW hℓu hℓs hηu hJ a₁ a₂ hμ hρ hL6 hGsq h273 h564 h42sq h566 h572
    hsym hEE
  refine hmain.trans (le_of_eq ?_)
  have hAμ : W * ℓu * ηu *
      (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹))
      = ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ := by
    field_simp
  rw [hAμ]
  ring

/-- Sanity check that `ee_le_reduced` is the sharper statement: `ee_le_paper`'s displayed,
merged bracket dominates `ee_le_reduced`'s unmerged one, pointwise, under the same
normalization hypotheses `ee_le_paper` needs to run its own merge step. -/
theorem ee_le_paper_of_reduced (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    (hJ : 1 ≤ J) (hA : 1 ≤ W * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (a₁ a₂ : ZMod L) (ρ : ℝ) :
    ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + cFar2 W ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹) * J ^ 2
        + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + (W * L * ρ + 2 * W * L * W ^ (-D) * J ^ 3 *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2)
    ≤
    ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + (cFar2 W ℓu + 72) * (ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹) * J ^ 3)
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + (W * L * ρ + 2 * W * L * W ^ (-D) * J ^ 3 *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hA0 : (0 : ℝ) < W * ℓu * ηu := by linarith
  have hsA : (0 : ℝ) < √(W * ℓu * ηu) := Real.sqrt_pos.2 hA0
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hTsq : (0 : ℝ) ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by positivity
  have hcF : 0 ≤ cFar2 W ℓu := cFar2_nonneg hW hℓ
  have hη0 : (0 : ℝ) < ηu⁻¹ := by positivity
  set ν : ℝ := ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ with hν
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hone : (1 : ℝ) ≤ ℓu / ℓs * √(ℓu / ℓs) := by
    have h1 : (1 : ℝ) ≤ √(ℓu / ℓs) := Real.one_le_sqrt.2 hr
    nlinarith
  have hinvA : (W * ℓu * ηu)⁻¹ ≤ ν := by
    have hsq : √(W * ℓu * ηu) ≤ W * ℓu * ηu := by
      nlinarith [Real.sq_sqrt hA0.le, Real.one_le_sqrt.2 hA, Real.sqrt_nonneg (W * ℓu * ηu)]
    have h1 : (W * ℓu * ηu)⁻¹ ≤ (√(W * ℓu * ηu))⁻¹ := inv_anti₀ hsA hsq
    have h2 : (√(W * ℓu * ηu))⁻¹ ≤ ν := by
      rw [hν]
      have := mul_le_mul_of_nonneg_right hone (le_of_lt (inv_pos.2 hsA))
      linarith [this]
    linarith
  have hJ23 : J ^ 2 ≤ J ^ 3 := pow_le_pow_right₀ hJ (by norm_num)
  have hbr : cFar2 W ℓu * (ν * J ^ 2) + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹
      ≤ (cFar2 W ℓu + 72) * ν * J ^ 3 := by
    have t1 : cFar2 W ℓu * (ν * J ^ 2) ≤ cFar2 W ℓu * (ν * J ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ23 hν0) hcF
    have t2 : 72 * J ^ 3 * (W * ℓu * ηu)⁻¹ ≤ 72 * J ^ 3 * ν :=
      mul_le_mul_of_nonneg_left hinvA (by positivity)
    linarith
  set IND : ℝ := cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
    (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0) with hIND
  have hbr' : IND + cFar2 W ℓu * (ν * J ^ 2) + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹
      ≤ IND + (cFar2 W ℓu + 72) * ν * J ^ 3 := by linarith
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbr' hη0.le) hTsq
  linarith [hstep]

end Lemma57
end RBM
