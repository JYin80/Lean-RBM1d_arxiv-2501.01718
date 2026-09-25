/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEDef
import RBM1D.Gauss.EEOffDiag

/-!
# M7b: (5.36) off the diagonal `a' ≠ a` (the bound), T1498

Target **M7b** of `docs/reports/T1488-prove.md` §3: the (5.36)-shape bound for
`RBM.MomentDuhamel.EEpath` at the doubled, *mismatched* argument `Fin.append a a'`
(`a ≠ a'` allowed), needed because the `U ⊗ U` kernel of (5.42) mixes labels
(`docs/paper-deltas.md` #113 ①).  Current Lean (`RBM.EEDef.ee_le_EEpath_sym`, T156/T167)
only covers the matched case `a' = a` (hypotheses `hc0`/`hc1`).

## Route (T1488 §3, M7b)

Write `R(c)` for the right side of `RBM.EEDef.ee_le_EEpath_sym` at a doubled argument `c`.
Given a common displacement bound `hdisp : ∀ i, zdist (a i - a' i) ≤ C * ellStar Wr ℓu`
(`C ≥ 0`):

* `zdist_add_le` (twice, plus the elementary fact that `zdist` is invariant under negation,
  proved here as `RBM.zdist_neg`) gives `dist ≤ dist' + 2 C · ellStar Wr ℓu`, where
  `dist = zdist (a 0 - a 1)`, `dist' = zdist (a' 0 - a' 1)`.
* `RBM.tailT_antitone` and `RBM.tailT_sub_le` (at the loss constant `2 * C` — Step 0 of the
  ticket confirms `tailT_sub_le` gives, at constant `C₀`, the loss `exp (√C₀ * (log W)^{3/4})`,
  so at `C₀ := 2 * C` the loss is `exp (√(2*C) * (log W)^{3/4})`, exactly the ticket's shape)
  give `tailT dist' ≤ exp (√(2*C) * (log W)^{3/4}) · tailT dist`.
* The same displacement bound widens the near-region indicator: both
  `1 (dist ≤ 4 ℓ*_u)` and `1 (dist' ≤ 4 ℓ*_u)` are `≤ 1 (dist ≤ (4 + 2C) ℓ*_u)`.
* `R(a, a) ≤ x + y`, `R(a', a') ≤ e^{2λ} x + y` (`x, y ≥ 0`, `λ := √(2C) (log W)^{3/4}`), so
  `(x + y)(e^{2λ} x + y) ≤ e^{2λ} (x + y)^2`.
* `RBM.Gauss.norm_EEpath_offDiag_sq_le` (T1494, M7a) gives
  `‖EEpath (Fin.append a a')‖² ≤ R(a,a) · R(a',a')`, hence `‖EEpath (Fin.append a a')‖ ≤ e^λ (x+y)`.

## Main declaration

* `RBM.Gauss.norm_EEpath_offDiag_le` — the M7b bound, exactly as stated in the ticket.
-/

namespace RBM

/-! ### An elementary fact about `zdist` used by the displacement bound -/

variable {L : ℕ} [NeZero L]

/-- The displacement triangle inequality for the two endpoints of a doubled `2`-label loop
argument: `zdist (a 0 - a 1) ≤ zdist (a 0 - a' 0) + zdist (a' 0 - a' 1) + zdist (a 1 - a' 1)`. -/
theorem zdist_sub_le_disp_add (a a' : LoopArg L (0 + 2)) :
    zdist L (a 0 - a 1) ≤
      zdist L (a 0 - a' 0) + zdist L (a' 0 - a' 1) + zdist L (a 1 - a' 1) := by
  have e1 : zdist L (a 0 - a 1) ≤ zdist L (a 0 - a' 0) + zdist L (a' 0 - a 1) := by
    have h := zdist_add_le L (a 0 - a' 0) (a' 0 - a 1)
    have heq : (a 0 - a' 0) + (a' 0 - a 1) = a 0 - a 1 := by ring
    rwa [heq] at h
  have e2 : zdist L (a' 0 - a 1) ≤ zdist L (a' 0 - a' 1) + zdist L (a' 1 - a 1) := by
    have h := zdist_add_le L (a' 0 - a' 1) (a' 1 - a 1)
    have heq : (a' 0 - a' 1) + (a' 1 - a 1) = a' 0 - a 1 := by ring
    rwa [heq] at h
  have e3 : zdist L (a' 1 - a 1) = zdist L (a 1 - a' 1) := by
    rw [show a' 1 - a 1 = -(a 1 - a' 1) by ring, zdist_neg]
  omega

end RBM

namespace RBM
namespace Gauss

open EEBridge MomentDuhamel Real

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `ellStar` is nonnegative once `1 ≤ W` and `0 < ℓu`. -/
private theorem ellStar_nonneg' {W ℓu : ℝ} (hW : 1 ≤ W) (hℓu : 0 < ℓu) :
    0 ≤ ellStar W ℓu := by
  have hl : 0 ≤ Real.log W := Real.log_nonneg hW
  unfold ellStar
  exact mul_nonneg (Real.rpow_nonneg hl _) hℓu.le

/-- A generic real-number combination lemma, isolated from the `RBM1D`-specific data:
if `v² ≤ (x + y) * (L2 * x + y)` with `x, y ≥ 0`, `1 ≤ L2`, and `v ≥ 0`, then
`v ≤ √L2 * (x + y)`. Used with `v = ‖EEpath (Fin.append a a')‖`. -/
private theorem le_sqrt_mul_add_of_sq_le_mul {v x y L2 : ℝ} (_hv0 : 0 ≤ v) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) (hL2 : 1 ≤ L2) (h : v ^ 2 ≤ (x + y) * (L2 * x + y)) :
    v ≤ √L2 * (x + y) := by
  have hxy0 : 0 ≤ x + y := by linarith
  have hL20 : 0 ≤ L2 := by linarith
  have hstep : (x + y) * (L2 * x + y) ≤ L2 * (x + y) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ L2 - 1) hy0) hxy0]
  have hsq : v ^ 2 ≤ L2 * (x + y) ^ 2 := h.trans hstep
  have ht0 : 0 ≤ √L2 * (x + y) := mul_nonneg (Real.sqrt_nonneg _) hxy0
  have hsq' : v ^ 2 ≤ (√L2 * (x + y)) ^ 2 := by
    have : (√L2 * (x + y)) ^ 2 = L2 * (x + y) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hL20]
    rw [this]; exact hsq
  nlinarith [sq_nonneg (v - √L2 * (x + y)), sq_nonneg (v + √L2 * (x + y))]

/-- **M7b**, `RBM.Gauss.norm_EEpath_offDiag_le`: (5.36) for `RBM.MomentDuhamel.EEpath` at the
doubled, mismatched argument `Fin.append a a'`. Same hypotheses as `RBM.EEDef.ee_le_EEpath_sym`
except `hc0`/`hc1` (dropped: they only hold at `a' = a`), plus `h273`/`h564` supplied at
*both* `c := Fin.append a a` and `c := Fin.append a' a'` with one common `ρ`, plus a
displacement bound `hdisp` at a common constant `C ≥ 0`. The conclusion carries the loss
factor `exp (√(2*C) * (log Wr)^{3/4})` from `RBM.tailT_sub_le`, and the near-region indicator
is widened from `dist ≤ 4 ℓ*_u` to `dist ≤ (4 + 2*C) ℓ*_u`. -/
theorem norm_EEpath_offDiag_le (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a a' : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
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
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h273' : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a' a') b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (a 0 - b) : ℝ) → EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ ρ)
    (h564' : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (a' 0 - b) : ℝ) → EEDef.eeL6 X E N u ω σ (Fin.append a' a') b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    {C : ℝ} (hC : 0 ≤ C)
    (hdisp : ∀ i, (zdist (B.L N) (a i - a' i) : ℝ) ≤ C * ellStar (B.W N : ℝ) ℓu) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a')‖
      ≤ Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) *
        (ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
              (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ (4 + 2 * C) * ellStar (B.W N : ℝ) ℓu
                then 1 else 0)
            + Lemma57.cFar2 (B.W N : ℝ) ℓu
              * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
            + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1)) ^ 2
          + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
            + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
              * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1)) ^ 2)) := by
  classical
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := EEDef.one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓu0 : (0 : ℝ) < ℓu := by linarith
  have hEStar0 : 0 ≤ ellStar (B.W N : ℝ) ℓu := ellStar_nonneg' hW hℓu0
  -- (1) the displacement bound `dist ≤ dist' + 2 C ellStar`
  have hdisp0 : (zdist (B.L N) (a 0 - a' 0) : ℝ) ≤ C * ellStar (B.W N : ℝ) ℓu := hdisp 0
  have hdisp1 : (zdist (B.L N) (a 1 - a' 1) : ℝ) ≤ C * ellStar (B.W N : ℝ) ℓu := hdisp 1
  have hnat : zdist (B.L N) (a 0 - a 1) ≤
      zdist (B.L N) (a 0 - a' 0) + zdist (B.L N) (a' 0 - a' 1) + zdist (B.L N) (a 1 - a' 1) :=
    zdist_sub_le_disp_add a a'
  have hreal : (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
      (zdist (B.L N) (a 0 - a' 0) : ℝ) + (zdist (B.L N) (a' 0 - a' 1) : ℝ)
        + (zdist (B.L N) (a 1 - a' 1) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this; linarith
  have hdd' : (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
      (zdist (B.L N) (a' 0 - a' 1) : ℝ) + 2 * C * ellStar (B.W N : ℝ) ℓu := by linarith
  -- (2) the tail bound: `tailT dist' ≤ exp(√(2C)(log Wr)^{3/4}) * tailT dist`
  have hCC : (0 : ℝ) ≤ 2 * C := by linarith
  have htail : tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ) ≤
      Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ) := by
    have hanti : tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ) ≤
        tailT (B.W N : ℝ) ℓu ηu D
          ((zdist (B.L N) (a 0 - a 1) : ℝ) - 2 * C * ellStar (B.W N : ℝ) ℓu) :=
      tailT_antitone (W := (B.W N : ℝ)) (ηu := ηu) (D := D) hℓu0 (by linarith)
    exact hanti.trans (tailT_sub_le hW hℓu0 hCC (zdist (B.L N) (a 0 - a 1) : ℝ))
  have hT'0 : 0 ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ) :=
    tailT_nonneg hW0.le _
  have hT0 : 0 ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ) :=
    tailT_nonneg hW0.le _
  have hloss1 : (1 : ℝ) ≤ Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) :=
    Real.one_le_exp (by positivity)
  have hL2 : (1 : ℝ) ≤
      (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 := by
    nlinarith
  have htailsq : tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ) ^ 2 ≤
      (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ) ^ 2 := by
    have hET0 : (0:ℝ) ≤ Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3/4:ℝ))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ) := by positivity
    have hsqstep := mul_le_mul htail htail hT'0 hET0
    have e1 : tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ) ^ 2
        = tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ)
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1) : ℝ) := by ring
    have e2 : (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ) ^ 2
        = (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3/4:ℝ))
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ))
          * (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3/4:ℝ))
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1) : ℝ)) := by ring
    rw [e1, e2]; exact hsqstep
  -- (3) the widened indicator dominates both original ones
  have hind_a : (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
        then (1 : ℝ) else 0) ≤
      (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ (4 + 2 * C) * ellStar (B.W N : ℝ) ℓu
        then (1 : ℝ) else 0) := by
    split_ifs with h1 h2
    · linarith
    · exfalso; apply h2; nlinarith
    · linarith
    · linarith
  have hind_a' : (if (zdist (B.L N) (a' 0 - a' 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
        then (1 : ℝ) else 0) ≤
      (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ (4 + 2 * C) * ellStar (B.W N : ℝ) ℓu
        then (1 : ℝ) else 0) := by
    split_ifs with h1 h2
    · linarith
    · exfalso; apply h2; nlinarith
    · linarith
    · linarith
  -- (4) the two applications of `ee_le_EEpath_sym`
  have hRa := EEDef.ee_le_EEpath_sym X E u ω σ (Fin.append a a) hℓu hℓs hηu hJ
    (by simp) (by simp)
    hρ hGm0 hGm hGsq0 hGsq2 hrow hSmax h273 h564 h42sq
  have hRa' := EEDef.ee_le_EEpath_sym X E u ω σ (Fin.append a' a') hℓu hℓs hηu hJ
    (by simp) (by simp)
    hρ hGm0 hGm hGsq0 hGsq2 hrow hSmax h273' h564' h42sq
  simp only [EEDef.lab₁, EEDef.lab₂, EEBridge.leftArg_append] at hRa hRa'
  -- (5) the two bounds `R(a,a) ≤ x + y`, `R(a',a') ≤ L2 * x + y`
  have hcN0 : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) ℓu := Lemma57.cNear2_nonneg hW hℓu0
  have hcF0 : 0 ≤ Lemma57.cFar2 (B.W N : ℝ) ℓu := Lemma57.cFar2_nonneg hW hℓu0
  have hr50 : 0 ≤ (ℓu / ℓs) ^ 5 := by positivity
  have hSmax0 : 0 ≤ √Smax := Real.sqrt_nonneg _
  have hJ0 : 0 ≤ J := by linarith
  have hηu0 : 0 ≤ ηu⁻¹ := by positivity
  have hWD0 : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hLr0 : 0 ≤ (B.L N : ℝ) := by positivity
  set T : ℝ := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1)) with hTdef
  set T' : ℝ := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a' 0 - a' 1)) with hT'def
  set indw : ℝ := (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ (4 + 2 * C) * ellStar (B.W N : ℝ) ℓu
        then (1:ℝ) else 0) with hindwdef
  set ind_a : ℝ := (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
        then (1:ℝ) else 0) with hindadef
  set ind_a' : ℝ := (if (zdist (B.L N) (a' 0 - a' 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
        then (1:ℝ) else 0) with hindadef'
  set Kw : ℝ := ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * indw
        + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
      + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 with hKwdef
  set Ka : ℝ := ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * ind_a
        + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
      + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 with hKadef
  set Ka' : ℝ := ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * ind_a'
        + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
      + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 with hKa'def
  set x : ℝ := Kw * T ^ 2 with hxdef
  set y : ℝ := (B.W N : ℝ) * (B.L N : ℝ) * ρ with hydef
  have hKw0 : 0 ≤ Kw := by
    rw [hKwdef]
    have hi : 0 ≤ indw := by rw [hindwdef]; split_ifs <;> norm_num
    have h1 : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * indw :=
      mul_nonneg (mul_nonneg hcN0 hr50) hi
    have h2 : 0 ≤ Lemma57.cFar2 (B.W N : ℝ) ℓu
        * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax))) := by positivity
    have h3 : (0:ℝ) ≤ 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹ := by positivity
    have h4 : (0:ℝ) ≤ 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 := by
      positivity
    have h5 : 0 ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * indw
        + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹) := mul_nonneg hηu0 (by linarith)
    linarith
  have hx0 : 0 ≤ x := by rw [hxdef]; exact mul_nonneg hKw0 (sq_nonneg _)
  have hy0 : 0 ≤ y := by rw [hydef]; positivity
  have hT20 : 0 ≤ T ^ 2 := sq_nonneg _
  have hT'20 : 0 ≤ T' ^ 2 := sq_nonneg _
  have hKa_le : Ka ≤ Kw := by
    rw [hKadef, hKwdef]
    have hstep : Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * ind_a ≤
        Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * indw :=
      mul_le_mul_of_nonneg_left hind_a (mul_nonneg hcN0 hr50)
    have hstep2 := mul_le_mul_of_nonneg_left hstep hηu0
    linarith
  have hKa'_le : Ka' ≤ Kw := by
    rw [hKa'def, hKwdef]
    have hstep : Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * ind_a' ≤
        Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * indw :=
      mul_le_mul_of_nonneg_left hind_a' (mul_nonneg hcN0 hr50)
    have hstep2 := mul_le_mul_of_nonneg_left hstep hηu0
    linarith
  have hRa_eq : ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * ind_a
          + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
          + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹) * T ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 * T ^ 2)
      = Ka * T ^ 2 + y := by rw [hKadef, hydef]; ring
  have hRa'_eq : ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * ind_a'
          + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
          + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹) * T' ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 * T' ^ 2)
      = Ka' * T' ^ 2 + y := by rw [hKa'def, hydef]; ring
  rw [hRa_eq] at hRa
  rw [hRa'_eq] at hRa'
  have hRa2 : ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a)‖ ≤ x + y := by
    have h1 : Ka * T ^ 2 ≤ Kw * T ^ 2 := mul_le_mul_of_nonneg_right hKa_le hT20
    rw [hxdef]; linarith
  have hL2Kw0 : 0 ≤ (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * Kw :=
    mul_nonneg (sq_nonneg _) hKw0
  have hRa'2 : ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a' a')‖ ≤
      (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * x + y := by
    have h1 : Ka' * T' ^ 2 ≤ Kw * T' ^ 2 := mul_le_mul_of_nonneg_right hKa'_le hT'20
    have h2 : Kw * T' ^ 2 ≤ Kw *
        ((Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * T ^ 2) :=
      mul_le_mul_of_nonneg_left htailsq hKw0
    rw [hxdef]
    have h3 : Kw * ((Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * T ^ 2)
        = (Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * (Kw * T ^ 2) := by ring
    rw [h3] at h2
    linarith
  -- (6) Cauchy–Schwarz (M7a) and the final combination
  have hcs := norm_EEpath_offDiag_sq_le X E N u ω σ a a'
  have hmul : ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a')‖ ^ 2 ≤
      (x + y) * ((Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * x + y) := by
    have h1 : (0:ℝ) ≤ ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a)‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a' a')‖ := norm_nonneg _
    calc ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a')‖ ^ 2
        ≤ ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a)‖
          * ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a' a')‖ := hcs
      _ ≤ (x + y) * ((Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 * x + y) :=
          mul_le_mul hRa2 hRa'2 h2 (by linarith)
  have hfinal := le_sqrt_mul_add_of_sq_le_mul (norm_nonneg _) hx0 hy0 hL2 hmul
  rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.exp (√(2 * C) * Real.log (B.W N : ℝ) ^ (3/4:ℝ)))]
    at hfinal
  have hxy_eq : x + y = ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 * indw
        + Lemma57.cFar2 (B.W N : ℝ) ℓu * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹) * T ^ 2
      + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
        + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3 * T ^ 2) := by
    rw [hxdef, hydef, hKwdef]; ring
  rwa [hxy_eq] at hfinal

end Gauss
end RBM
