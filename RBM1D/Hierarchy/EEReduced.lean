/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEDef

/-!
# T1493: (5.36) for `EEpath`, in the proof-exponent shape

`RBM.EEDef.ee_le_paper_EEpath_sym` (`Hierarchy/EEDef.lean`) states (5.36) for the pinned
`RBM.MomentDuhamel.EEpath`, but its far-field bracket `(cFar2 + 72) · (ℓ_u/ℓ_s)^{3/2}
A_u^{-1/2} · (2J*)³` is **merged** into a single term, exactly as `RBM.Lemma57.ee_le_paper_sym`
merges it.  T1491 (`RBM1D/Hierarchy/Lemma57Reduced.lean`) already recorded the unmerged shape
for the abstract, non-`sym` master `RBM.Lemma57.ee_le`, as `RBM.Lemma57.ee_le_reduced`.

This file does the same for the two `sym` layers this ticket is asked to touch:

* `RBM.Lemma57.ee_le_reduced_sym` — the abstract twin of `ee_le_reduced`, built from
  `RBM.Lemma57.ee_le_sym` (T190's version without `h566`/`hsym`) instead of from `ee_le`,
  by the same one-step un-merge (`ee_le_paper_sym`'s proof, stopped before its final
  `cFar2·J²·ν + 72·J³·A⁻¹ ≤ (cFar2+72)·ν·J³` bound).
* `RBM.EEDef.ee_le_reduced_EEpath_sym` — the named instance on the pinned `EEpath`, target
  **M5** of `docs/reports/T1488-prove.md` §3.  Same hypotheses as
  `RBM.EEDef.ee_le_EEpath_sym` plus `hμbd` (exactly as in `ee_le_paper_EEpath_sym`); the
  conclusion keeps the `J²` term and the `J³·A⁻¹` term separate, as (5.71)+(5.72) do.
-/

namespace RBM
namespace Lemma57

open Real Finset

variable (L : ℕ) [NeZero L]
variable {W ℓu ℓs ηu D J : ℝ}

/-- **(5.36), `sym` layer (T190, no `h566`/`hsym`), in the proof-exponent shape.**  Same
hypotheses as `ee_le_paper_sym`, but the far-field bracket `cFar2 · (ℓ_u/ℓ_s)^{3/2}
A_u^{-1/2} · J²` and `72 · J³ · A_u^{-1}` are kept apart, rather than merged into a single
`J³` term — exactly `RBM.Lemma57.ee_le_reduced`'s relation to `ee_le`, one level up the
`sym` ladder. This is `ee_le_sym` with the concrete `μ := ℓ_u/ℓ_s · √(ℓ_u/ℓ_s) ·
((√(W ℓ_u η_u))⁻¹ · (W ℓ_u η_u)⁻¹)`, followed only by the identity
`(W ℓ_u η_u) · μ = ℓ_u/ℓ_s · √(ℓ_u/ℓ_s) · (√(W ℓ_u η_u))⁻¹`, not by `ee_le_paper_sym`'s
subsequent merge step. -/
theorem ee_le_reduced_sym (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    (hJ : 1 ≤ J) (hA : 1 ≤ W * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs) (a₁ a₂ : ZMod L)
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {ρ EE : ℝ} (hρ : 0 ≤ ρ)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, L6 b ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹)
    (h564 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L6 b ≤ ρ)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (hnear₁ : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ *
        (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)))
    (hnear₂ : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu →
      L6 b ≤ Gsq a₂ a₁ * Gsq b a₁ *
        (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)))
    (hfarb : ∀ b, 4 * ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ) →
      ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      ellStar W ℓu < (zdist L (a₂ - b) : ℝ) →
      L6 b ≤ J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
        (tailT W ℓu ηu D (zdist L (a₁ - b)) * tailT W ℓu ηu D (zdist L (a₂ - b))))
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + cFar2 W ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹) * J ^ 2
        + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + (W * L * ρ + 2 * W * L * W ^ (-D) * J ^ 3 *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hA0 : (0 : ℝ) < W * ℓu * ηu := by linarith
  have hsA : (0 : ℝ) < √(W * ℓu * ηu) := Real.sqrt_pos.2 hA0
  have hμ : (0 : ℝ) ≤ ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹) := by
    positivity
  have hmain := ee_le_sym L hW hℓu hℓs hηu hJ a₁ a₂ hμ hρ hGsq h273 h564 h42sq
    hnear₁ hnear₂ hfarb hEE
  refine hmain.trans (le_of_eq ?_)
  have hAμ : W * ℓu * ηu *
      (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹))
      = ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ := by
    field_simp
  rw [hAμ]
  ring

end Lemma57

namespace EEDef

open Matrix Finset Gauss EEBridge MomentDuhamel

section SixSym

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
variable (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)

/-- **(5.36) for `RBM.MomentDuhamel.EEpath`, in the proof-exponent shape** — target **M5**
of `docs/reports/T1488-prove.md` §3.  Same hypotheses as `RBM.EEDef.ee_le_EEpath_sym` plus
`hA`, `hr`, `hμbd`, exactly as in `RBM.EEDef.ee_le_paper_EEpath_sym`; the conclusion keeps
the `J²` term `cFar2·(2J)²·r^{3/2}A_u^{-1/2}` and the `J³` term `72·(2J)³·A_u⁻¹` separate,
which is (5.71)+(5.72) rather than the displayed, merged (5.36). -/
theorem ee_le_reduced_EEpath_sym (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (c : LoopArg (B.L N) ((0 + 2) + (0 + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (B.W N : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (hμbd : 2 * √Smax ≤ ℓu / ℓs * √(ℓu / ℓs) *
      ((√((B.W N : ℝ) * ℓu * ηu))⁻¹ * ((B.W N : ℝ) * ℓu * ηu)⁻¹))
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (lab₁ c - b) : ℝ) → eeL6 X E N u ω σ c b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
              then 1 else 0)
          + Lemma57.cFar2 (B.W N : ℝ) ℓu
            * (ℓu / ℓs * √(ℓu / ℓs) * (√((B.W N : ℝ) * ℓu * ηu))⁻¹) * (2 * J) ^ 2
          + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2) := by
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hJ2 : (1 : ℝ) ≤ 2 * J := by linarith
  have h42sq' : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ 2 * J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
    intro x y hxy
    have h := h42sq x y hxy
    have hT : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
      tailT_nonneg hW0.le _
    nlinarith
  exact Lemma57.ee_le_reduced_sym (B.L N) hW hℓu hℓs hηu hJ2 hA hr (lab₁ c) (lab₂ c) hρ hGsq0
    h273 h564 h42sq'
    (fun b _ => (eeL6_two_le_near₁ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2
        hrow hSmax).trans
      (mul_le_mul_of_nonneg_left hμbd (mul_nonneg (hGsq0 _ _) (hGsq0 _ _))))
    (fun b _ => (eeL6_two_le_near₂ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2
        hrow hSmax).trans
      (mul_le_mul_of_nonneg_left hμbd (mul_nonneg (hGsq0 _ _) (hGsq0 _ _))))
    (fun b hfar hb1 hb2 => eeL6_two_le_far X E N u ω σ c b (by linarith) hJ hc0 hc1
      hGm0 hGm hGsq0 hGsq2 hrow h42sq hfar hb1 hb2)
    (norm_EEpath_le_W_sum X E u ω σ c)

end SixSym

end EEDef
end RBM
