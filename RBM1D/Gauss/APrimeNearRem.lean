/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVEndpoint

/-!
# T280g: the near field remainder in (5.64)

The `h564` remainder is needed only in the near branch of (5.36).  This file
records the near restricted version with the remainder scaled by the local
tail, so the evolved QV estimate has no spatially constant residual.
-/

namespace RBM
namespace Lemma57

variable {W ℓu ℓs ηu D J : ℝ}

/-- The near field form of (5.36), with (5.64) restricted to its actual use. -/
theorem ee_le_sym' (L : ℕ) [NeZero L]
    (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hJ : 1 ≤ J) (a₁ a₂ : ZMod L)
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ}
    {μ ε EE : ℝ} (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, L6 b ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 *
      (W * ℓu * ηu)⁻¹)
    (h564' : (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu →
      ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) →
        L6 b ≤ ε * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 / (W * L))
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (hnear₁ : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ)
    (hnear₂ : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu →
      L6 b ≤ Gsq a₂ a₁ * Gsq b a₁ * μ)
    (hfarb : ∀ b, 4 * ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ) →
      ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      ellStar W ℓu < (zdist L (a₂ - b) : ℝ) →
      L6 b ≤ J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
        (tailT W ℓu ηu D (zdist L (a₁ - b)) *
          tailT W ℓu ηu D (zdist L (a₂ - b))))
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + ηu * ε *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ))
        + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + 2 * W * L * W ^ (-D) * J ^ 3 *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : 0 ≤ J := by linarith
  have hcN : 0 ≤ cNear2 W ℓu := cNear2_nonneg hW hℓ
  have hcF : 0 ≤ cFar2 W ℓu := cFar2_nonneg hW hℓ
  have hA0 : 0 < W * ℓu * ηu := by positivity
  have hrem : 0 ≤ 2 * W * L * W ^ (-D) * J ^ 3 *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
    have : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    positivity
  have hfarterm : 0 ≤ ηu⁻¹ *
      (cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ)) +
        72 * J ^ 3 * (W * ℓu * ηu)⁻¹) *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by positivity
  split_ifs with hd
  · have hρ : 0 ≤ ε * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 / (W * L) := by
      positivity
    have h := ee_near_le (D := D) L hW hℓu hℓs hηu hd hρ h273 (h564' hd) hEE
    have hWL : W * L ≠ (0 : ℝ) := ne_of_gt (mul_pos hW0 hL0)
    have hcancel : W * L *
        (ε * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 / (W * L)) =
        ε * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
      field_simp
    rw [hcancel] at h
    have hcoeff : ηu⁻¹ *
        (cNear2 W ℓu * (ℓu / ℓs) ^ 5 + ηu * ε +
          cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ)) +
          72 * J ^ 3 * (W * ℓu * ηu)⁻¹) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 =
        ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5) *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 +
        ε * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 +
        ηu⁻¹ * (cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ)) +
          72 * J ^ 3 * (W * ℓu * ηu)⁻¹) *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
      field_simp
      ring
    simp only [mul_one]
    rw [hcoeff]
    nlinarith [h, hfarterm, hrem]
  · rw [not_le] at hd
    have h := ee_far_le_sym L hW hℓu hηu hJ hd.le hμ hGsq h42sq
      hnear₁ hnear₂ hfarb hEE
    nlinarith [h]

end Lemma57

namespace EEDef
open Matrix Finset Gauss EEBridge MomentDuhamel
variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- Under the explicit logarithmic threshold, the `ℓ**` separation leaves a
half-`ℓ*` margin after moving a near pair by at most `4ℓ*`. -/
theorem ellStarStar_ge_nine_halves_ellStar {W ℓu : ℝ}
    (hlog : 4 ≤ Real.log W) (hℓu : 0 ≤ ℓu) :
    (9 / 2 : ℝ) * ellStar W ℓu ≤ Lemma57.ellStarStar W ℓu := by
  let x : ℝ := Real.log W
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : (8 : ℝ) ≤ x ^ (3 / 2 : ℝ) := by
    calc
      (8 : ℝ) = (4 : ℝ) ^ (3 / 2 : ℝ) := by norm_num
      _ ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
  have hy0 : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hsq : x ^ (3 : ℝ) = (x ^ (3 / 2 : ℝ)) ^ 2 := by
    calc
      x ^ (3 : ℝ) = x ^ ((3 / 2 : ℝ) * 2) := by norm_num
      _ = (x ^ (3 / 2 : ℝ)) ^ 2 := by
        simpa using (Real.rpow_mul hx (3 / 2 : ℝ) 2)
  have hnum : (9 / 2 : ℝ) * x ^ (3 / 2 : ℝ) ≤ x ^ (3 : ℝ) := by
    rw [hsq]
    have hm : 0 ≤ x ^ (3 / 2 : ℝ) * (x ^ (3 / 2 : ℝ) - 9 / 2) :=
      mul_nonneg hy0 (by linarith)
    nlinarith
  unfold ellStar Lemma57.ellStarStar
  calc
    (9 / 2 : ℝ) * (Real.log W ^ (3 / 2 : ℝ) * ℓu)
        = ((9 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) * ℓu := by ring
    _ ≤ x ^ (3 : ℝ) * ℓu := mul_le_mul_of_nonneg_right hnum hℓu

/-- A near pair with the glue label beyond `ℓ**` gains two tails at the
remaining separation `F = ℓ** - 4ℓ*`. -/
theorem eeL6_le_nearFar (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {ℓu ηu D J Gbar : ℝ}
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ}
    (hℓu : 0 < ℓu) (hJ : 1 ≤ J)
    (hlog : 4 ≤ Real.log (B.W N : ℝ))
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hnear : (zdist (B.L N) (leftArg c 0 - leftArg c 1) : ℝ)
      ≤ 4 * ellStar (B.W N : ℝ) ℓu)
    (hb : Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (leftArg c 0 - b) : ℝ))
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (hGbar12 : Gsq (leftArg c 0) (leftArg c 1) ≤ Gbar)
    (hGbar21 : Gsq (leftArg c 1) (leftArg c 0) ≤ Gbar) :
    eeL6 X E N u ω σ c b ≤
      2 * Gbar * J ^ 2 *
        tailT (B.W N : ℝ) ℓu ηu D
          (Lemma57.ellStarStar (B.W N : ℝ) ℓu -
            4 * ellStar (B.W N : ℝ) ℓu) ^ 2 := by
  classical
  let W : ℝ := B.W N
  let F : ℝ := Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu
  let T : ℝ := tailT W ℓu ηu D F
  let K : ℝ := J * T
  have hW : 1 ≤ W := by
    dsimp [W]
    exact one_le_W B N
  have hW0 : 0 ≤ W := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hstar0 : 0 ≤ ellStar W ℓu := by
    unfold ellStar
    have := Real.log_nonneg hW
    positivity
  have hmargin : (9 / 2 : ℝ) * ellStar W ℓu ≤
      Lemma57.ellStarStar W ℓu :=
    ellStarStar_ge_nine_halves_ellStar hlog hℓu.le
  have hFhalf : ellStar W ℓu / 2 ≤ F := by dsimp [F]; linarith
  have htri : (zdist (B.L N) (leftArg c 0 - b) : ℝ) ≤
      (zdist (B.L N) (leftArg c 0 - leftArg c 1) : ℝ) +
        (zdist (B.L N) (leftArg c 1 - b) : ℝ) := by
    have h := zdist_sub_le_add (B.L N) (leftArg c 0) b (leftArg c 1)
    rw [Lemma57.zdist_sub_comm (B.L N) b (leftArg c 1)] at h
    exact h
  have hb1F : F ≤ (zdist (B.L N) (leftArg c 0 - b) : ℝ) := by
    dsimp [F]
    linarith
  have hb2F : F ≤ (zdist (B.L N) (leftArg c 1 - b) : ℝ) := by
    dsimp [F]
    linarith
  have hT0 : 0 ≤ T := tailT_nonneg hW0 F
  have hK0 : 0 ≤ K := mul_nonneg hJ0 hT0
  have htail1 : tailT W ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)) ≤ T :=
    tailT_antitone hℓu hb1F
  have htail2 : tailT W ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)) ≤ T :=
    tailT_antitone hℓu hb2F
  have hB1 : Gsq b (leftArg c 0) ≤ K := by
    have h := h42sq b (leftArg c 0) (by
      rw [Lemma57.zdist_sub_comm]
      linarith)
    rw [Lemma57.zdist_sub_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_left htail1 hJ0)
  have hB2 : Gsq b (leftArg c 1) ≤ K := by
    have h := h42sq b (leftArg c 1) (by
      rw [Lemma57.zdist_sub_comm]
      linarith)
    rw [Lemma57.zdist_sub_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_left htail2 hJ0)
  have hG1 : Gm (leftArg c 0) b * Gm b (leftArg c 0) ≤ K :=
    (hGsq2 _ _).trans ((h42sq _ _ (by linarith)).trans
      (mul_le_mul_of_nonneg_left htail1 hJ0))
  have hG2 : Gm (leftArg c 1) b * Gm b (leftArg c 1) ≤ K :=
    (hGsq2 _ _).trans ((h42sq _ _ (by linarith)).trans
      (mul_le_mul_of_nonneg_left htail2 hJ0))
  have h1 : eeL6k X E N u ω σ c 1 b ≤
      Gm (rightArg c 0) (rightArg c 1) * K *
        Gm (leftArg c 1) (leftArg c 0) * K :=
    eeL6k_two_one_le_glue X E N u ω σ c b hGm0 hK0 hGm
      (fun b' hz => by rw [hc1]; exact (hrow (leftArg c 1) b b' hz).trans hB2)
      (fun p q y hp hq hy => by
        rw [hc0] at hq
        exact (mul_le_mul (hGm (σ 1) (leftArg c 0) b p y hp hy)
          (hGm (!(σ 1)) b (leftArg c 0) y q hy hq)
          (norm_nonneg _) (hGm0 _ _)).trans hG1)
  have h0 : eeL6k X E N u ω σ c 0 b ≤
      Gm (rightArg c 1) (rightArg c 0) * K *
        Gm (leftArg c 0) (leftArg c 1) * K :=
    eeL6k_two_zero_le_glue X E N u ω σ c b hGm0 hK0 hGm
      (fun b' hz => by rw [hc0]; exact (hrow (leftArg c 0) b b' hz).trans hB1)
      (fun p q y hp hq hy => by
        rw [hc1] at hq
        exact (mul_le_mul (hGm (σ 0) (leftArg c 1) b p y hp hy)
          (hGm (!(σ 0)) b (leftArg c 1) y q hy hq)
          (norm_nonneg _) (hGm0 _ _)).trans hG2)
  have hpair1 : Gm (leftArg c 0) (leftArg c 1) *
      Gm (leftArg c 1) (leftArg c 0) ≤ Gbar :=
    (hGsq2 _ _).trans hGbar12
  have hpair0 : Gm (leftArg c 1) (leftArg c 0) *
      Gm (leftArg c 0) (leftArg c 1) ≤ Gbar :=
    (hGsq2 _ _).trans hGbar21
  have hs1 : eeL6k X E N u ω σ c 1 b ≤ Gbar * K ^ 2 := by
    refine h1.trans ?_
    rw [hc0, hc1]
    calc
      Gm (leftArg c 0) (leftArg c 1) * K *
          Gm (leftArg c 1) (leftArg c 0) * K =
          (Gm (leftArg c 0) (leftArg c 1) *
            Gm (leftArg c 1) (leftArg c 0)) * K ^ 2 := by ring
      _ ≤ Gbar * K ^ 2 := mul_le_mul_of_nonneg_right hpair1 (sq_nonneg K)
  have hs0 : eeL6k X E N u ω σ c 0 b ≤ Gbar * K ^ 2 := by
    refine h0.trans ?_
    rw [hc1, hc0]
    calc
      Gm (leftArg c 1) (leftArg c 0) * K *
          Gm (leftArg c 0) (leftArg c 1) * K =
          (Gm (leftArg c 1) (leftArg c 0) *
            Gm (leftArg c 0) (leftArg c 1)) * K ^ 2 := by ring
      _ ≤ Gbar * K ^ 2 := mul_le_mul_of_nonneg_right hpair0 (sq_nonneg K)
  rw [eeL6_two_eq]
  calc
    eeL6k X E N u ω σ c 0 b + eeL6k X E N u ω σ c 1 b
        ≤ Gbar * K ^ 2 + Gbar * K ^ 2 := add_le_add hs0 hs1
    _ = 2 * Gbar * J ^ 2 * T ^ 2 := by dsimp [K]; ring

/-- The numerical near remainder produced by two far tails. -/
noncomputable def nearEpsilon (W L ℓu ηu D J : ℝ) : ℝ :=
  W * L * (2 * ηu⁻¹ ^ 2 * J ^ 2 *
      tailT W ℓu ηu D
        (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) ^ 2) *
    (W * ℓu * ηu) ^ 4 * Real.exp (4 * Real.log W ^ (3 / 4 : ℝ))

/-- The near-pair tail lower bound converts the two-tail estimate into the
`h564'` normalization consumed by `ee_le_sym'`. -/
theorem nearRem_of_nearFar {W L ℓu ηu D J d Z : ℝ}
    (hW : 1 ≤ W) (hL : 0 < L) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (_hJ : 0 ≤ J) (hd : d ≤ 4 * ellStar W ℓu)
    (hZ : Z ≤ 2 * ηu⁻¹ ^ 2 * J ^ 2 *
      tailT W ℓu ηu D
        (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) ^ 2) :
    Z ≤ nearEpsilon W L ℓu ηu D J * tailT W ℓu ηu D d ^ 2 /
      (W * L) := by
  let A : ℝ := W * ℓu * ηu
  let TF : ℝ := tailT W ℓu ηu D
    (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu)
  let Td : ℝ := tailT W ℓu ηu D d
  have hA : 0 < A := by dsimp [A]; positivity
  have hWL : W * L ≠ 0 := ne_of_gt (mul_pos (by linarith) hL)
  have hTF : 0 ≤ TF := tailT_nonneg (by linarith : 0 ≤ W) _
  have hTd : 0 ≤ Td := tailT_nonneg (by linarith : 0 ≤ W) _
  have hcoef : 0 ≤ 2 * ηu⁻¹ ^ 2 * J ^ 2 * TF ^ 2 := by positivity
  have hscale := Lemma57.inv_four_le_tailT_sq
    (ηu := ηu) (D := D) hW hℓu hd
  have hAeq : A ^ 4 * (((A ^ 2)⁻¹) ^ 2) = 1 := by
    field_simp
  have hgain : 1 ≤ A ^ 4 * Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) * Td ^ 2 := by
    calc
      1 = A ^ 4 * (((A ^ 2)⁻¹) ^ 2) := hAeq.symm
      _ ≤ A ^ 4 * (Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) * Td ^ 2) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hgain hcoef
  calc
    Z ≤ 2 * ηu⁻¹ ^ 2 * J ^ 2 * TF ^ 2 := hZ
    _ = (2 * ηu⁻¹ ^ 2 * J ^ 2 * TF ^ 2) * 1 := by ring
    _ ≤ (2 * ηu⁻¹ ^ 2 * J ^ 2 * TF ^ 2) *
        (A ^ 4 * Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) * Td ^ 2) := hmul
    _ = nearEpsilon W L ℓu ηu D J * Td ^ 2 / (W * L) := by
      dsimp [nearEpsilon, A, TF, Td]
      field_simp

/-- The `ℓ**−4ℓ*` separation beats the floor power when the usual
logarithmic window holds. -/
theorem exp_nearFar_le_floor {W ℓu D : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓu : 0 < ℓu) (hD : 0 ≤ D)
    (hlog4 : 4 ≤ Real.log W)
    (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    Real.exp (-(Real.sqrt ((Lemma57.ellStarStar W ℓu -
      4 * ellStar W ℓu) / ℓu))) ≤ W ^ (-D) := by
  let x : ℝ := Real.log W
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hW0 : 0 < W := (Real.exp_pos 1).trans_le hW
  have hy : (8 : ℝ) ≤ x ^ (3 / 2 : ℝ) := by
    calc
      (8 : ℝ) = (4 : ℝ) ^ (3 / 2 : ℝ) := by norm_num
      _ ≤ x ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hlog4 (by norm_num)
  have hy0 : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hsq : x ^ (3 : ℝ) = (x ^ (3 / 2 : ℝ)) ^ 2 := by
    calc
      x ^ (3 : ℝ) = x ^ ((3 / 2 : ℝ) * 2) := by norm_num
      _ = (x ^ (3 / 2 : ℝ)) ^ 2 := by
        simpa using (Real.rpow_mul hx (3 / 2 : ℝ) 2)
  have hhalf : x ^ (3 : ℝ) / 2 ≤
      x ^ (3 : ℝ) - 4 * x ^ (3 / 2 : ℝ) := by
    rw [hsq]
    have hm : 0 ≤ x ^ (3 / 2 : ℝ) * (x ^ (3 / 2 : ℝ) - 8) :=
      mul_nonneg hy0 (by linarith)
    nlinarith
  have hFdiv : x ^ (3 : ℝ) / 2 ≤
      (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) / ℓu := by
    have hEq : (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) / ℓu =
        x ^ (3 : ℝ) - 4 * x ^ (3 / 2 : ℝ) := by
      dsimp [Lemma57.ellStarStar, ellStar, x]
      field_simp
    rw [hEq]
    exact hhalf
  have hDsq : (D * x) ^ 2 ≤ x ^ (3 : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hlog (sq_nonneg x)
    change (4 * D) ^ 2 * x ^ 2 ≤ x * x ^ 2 at hm
    have hp : x ^ (3 : ℝ) = x ^ 3 := by norm_num
    rw [hp]
    nlinarith only [hm, pow_nonneg hx 3]
  have hFx : 0 ≤ (Lemma57.ellStarStar W ℓu -
      4 * ellStar W ℓu) / ℓu := by
    have : 0 ≤ x ^ (3 : ℝ) := Real.rpow_nonneg hx _
    linarith
  have hroot : D * x ≤ Real.sqrt ((Lemma57.ellStarStar W ℓu -
      4 * ellStar W ℓu) / ℓu) :=
    (Real.le_sqrt (mul_nonneg hD hx) hFx).2 (by linarith)
  rw [Real.rpow_def_of_pos hW0]
  exact Real.exp_le_exp.2 (by dsimp [x] at hroot ⊢; nlinarith)

/-- The explicit epsilon is inverse-bandwidth small in the §18 window. -/
theorem nearEpsilon_le_inv {W L ℓu ηu D J N k : ℝ}
    (hW : Real.exp 1 ≤ W) (_hL : 0 < L) (hℓu : 0 < ℓu)
    (hηu : 0 < ηu) (hN : 1 ≤ N) (hk : 0 ≤ k)
    (hJ0 : 0 ≤ J) (hD : 2 * k + 14 ≤ D)
    (hη : N⁻¹ ≤ ηu) (hA : 1 ≤ W * ℓu * ηu)
    (hAN : W * ℓu * ηu ≤ N) (hWL : W * L ≤ N)
    (hNW : N ≤ W ^ 2) (hJN : J ≤ N ^ k)
    (hlog4 : 4 ≤ Real.log W)
    (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    nearEpsilon W L ℓu ηu D J ≤ W⁻¹ := by
  let A : ℝ := W * ℓu * ηu
  let F : ℝ := Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu
  let TF : ℝ := tailT W ℓu ηu D F
  let q : ℝ := W ^ (-D)
  let x : ℝ := Real.log W
  have hW0 : 0 < W := (Real.exp_pos 1).trans_le hW
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hN0 : 0 < N := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hA0 : 0 < A := by dsimp [A]; linarith
  have hq0 : 0 ≤ q := Real.rpow_nonneg hW0.le _
  have hTF0 : 0 ≤ TF := tailT_nonneg hW0.le _
  have hExp := exp_nearFar_le_floor hW hℓu hD0 hlog4 hlog
  have hAinv : ((A ^ 2)⁻¹) ≤ 1 := by
    have hAsq : 1 ≤ A ^ 2 := by nlinarith
    exact (inv_le_one₀ (by positivity : 0 < A ^ 2)).2 hAsq
  have hTF : TF ≤ 2 * q := by
    have hExp0 : 0 ≤ Real.exp (-Real.sqrt (F / ℓu)) := (Real.exp_pos _).le
    have hp := mul_le_mul hAinv hExp hExp0 (by positivity : 0 ≤ (1 : ℝ))
    dsimp [TF, tailT, q, F, A] at hp ⊢
    nlinarith
  have hTF2 : TF ^ 2 ≤ 4 * q ^ 2 := by
    nlinarith [sq_nonneg (TF - 2 * q)]
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hpow : x ^ (3 / 4 : ℝ) ≤ x := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : ℝ) ≤ 1))
  have hExp4 : Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) ≤ W ^ 4 := by
    have hm := Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4))
    have heq : Real.exp (4 * x) = W ^ 4 := by
      rw [show W ^ 4 = W ^ (4 : ℝ) by norm_cast, Real.rpow_def_of_pos hW0]
      congr 1
      ring
    simpa only [x, heq] using hm
  have hηinv : ηu⁻¹ ≤ N := by
    have hNinv : 0 < N⁻¹ := inv_pos.mpr hN0
    have h := inv_anti₀ hNinv hη
    simpa using h
  have hη2 : ηu⁻¹ ^ 2 ≤ W ^ 4 := by
    calc
      ηu⁻¹ ^ 2 ≤ N ^ 2 := by gcongr
      _ ≤ (W ^ 2) ^ 2 := by gcongr
      _ = W ^ 4 := by ring
  have hA4 : A ^ 4 ≤ W ^ 8 := by
    calc
      A ^ 4 ≤ N ^ 4 := by gcongr
      _ ≤ (W ^ 2) ^ 4 := by gcongr
      _ = W ^ 8 := by ring
  have hJ2 : J ^ 2 ≤ W ^ (4 * k) := by
    have hNpow : N ^ k ≤ (W ^ 2) ^ k :=
      Real.rpow_le_rpow (by positivity) hNW hk
    have hWp : (W ^ 2) ^ k = W ^ (2 * k) := by
      rw [show W ^ 2 = W ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hW0.le]
    have hJp : J ≤ W ^ (2 * k) := hJN.trans (hNpow.trans_eq hWp)
    calc
      J ^ 2 ≤ (W ^ (2 * k)) ^ 2 := by gcongr
      _ = W ^ (4 * k) := by
        calc
          (W ^ (2 * k)) ^ 2 = (W ^ (2 * k)) ^ (2 : ℝ) := by norm_cast
          _ = W ^ ((2 * k) * 2) := (Real.rpow_mul hW0.le _ _).symm
          _ = W ^ (4 * k) := by congr 1; ring
  have hWL2 : W * L ≤ W ^ 2 := hWL.trans hNW
  have hraw : nearEpsilon W L ℓu ηu D J ≤
      W ^ 2 * (2 * W ^ 4 * W ^ (4 * k) * (4 * q ^ 2)) *
        W ^ 8 * W ^ 4 := by
    dsimp [nearEpsilon, TF, q, A] at hTF2 ⊢
    gcongr
  have hpoweq : W ^ 2 * (2 * W ^ 4 * W ^ (4 * k) * (4 * q ^ 2)) *
        W ^ 8 * W ^ 4 = 8 * W ^ (18 + 4 * k - 2 * D) := by
    dsimp [q]
    rw [show (W ^ (-D)) ^ 2 = W ^ (-2 * D) by
      rw [show -2 * D = -D * 2 by ring, Real.rpow_mul hW0.le]
      norm_cast]
    have hbase : W ^ (18 + 4 * k - 2 * D) =
        W ^ 2 * W ^ 4 * W ^ (4 * k) * W ^ (-2 * D) * W ^ 8 * W ^ 4 := by
      calc
        W ^ (18 + 4 * k - 2 * D) =
            W ^ ((2 : ℝ) + 4 + 4 * k + (-2 * D) + 8 + 4) := by congr 1; ring
        _ = W ^ 2 * W ^ 4 * W ^ (4 * k) * W ^ (-2 * D) * W ^ 8 * W ^ 4 := by
          repeat rw [Real.rpow_add hW0]
          norm_cast
    rw [hbase]
    ring
  have hexp : 18 + 4 * k - 2 * D ≤ -10 := by linarith
  have hlow : W ^ (18 + 4 * k - 2 * D) ≤ W ^ (-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hexp
  have hW2 : 2 ≤ W := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact htwo.trans hW
  have hW3 : (8 : ℝ) ≤ W ^ 3 := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ W ^ 3 := by gcongr
  have hlast : 8 * W ^ (-10 : ℝ) ≤ W⁻¹ := by
    have hm := mul_le_mul_of_nonneg_right hW3
      (Real.rpow_nonneg hW0.le (-10 : ℝ))
    have hp : W ^ 3 * W ^ (-10 : ℝ) = W ^ (-7 : ℝ) := by
      calc
        W ^ 3 * W ^ (-10 : ℝ) = W ^ (3 : ℝ) * W ^ (-10 : ℝ) := by norm_cast
        _ = W ^ ((3 : ℝ) + (-10)) := (Real.rpow_add hW0 _ _).symm
        _ = W ^ (-7 : ℝ) := by norm_num
    rw [hp] at hm
    exact hm.trans (by
      simpa only [Real.rpow_neg_one] using
        (Real.rpow_le_rpow_of_exponent_le hW1
          (by norm_num : (-7 : ℝ) ≤ -1)))
  calc
    nearEpsilon W L ℓu ηu D J ≤
        W ^ 2 * (2 * W ^ 4 * W ^ (4 * k) * (4 * q ^ 2)) * W ^ 8 * W ^ 4 := hraw
    _ = 8 * W ^ (18 + 4 * k - 2 * D) := hpoweq
    _ ≤ 8 * W ^ (-10 : ℝ) := by gcongr
    _ ≤ W⁻¹ := hlast

/-- A positive-width, positive-distance, positive-remainder window satisfying
all quantitative premises of `nearEpsilon_le_inv` simultaneously. -/
theorem nearEpsilon_window_witness :
    ∃ W L ℓu ηu D J N k : ℝ,
      Real.exp 1 ≤ W ∧ 1 < L ∧ 0 < ℓu ∧ 0 < ηu ∧
      1 ≤ N ∧ 0 ≤ k ∧ 0 < J ∧ 2 * k + 14 ≤ D ∧
      N⁻¹ ≤ ηu ∧ 1 ≤ W * ℓu * ηu ∧
      W * ℓu * ηu ≤ N ∧ W * L ≤ N ∧ N ≤ W ^ 2 ∧
      J ≤ N ^ k ∧ 4 ≤ Real.log W ∧
      (4 * D) ^ 2 ≤ Real.log W := by
  let W : ℝ := Real.exp 4096
  have hW0 : 0 < W := by dsimp [W]; positivity
  have hW1 : 1 ≤ W := by dsimp [W]; exact Real.one_le_exp (by norm_num)
  have hWexp : Real.exp 1 ≤ W := by
    dsimp [W]
    exact Real.exp_le_exp.2 (by norm_num)
  have hWsq : W ≤ W ^ 2 := by nlinarith
  have hη : (W ^ 2)⁻¹ ≤ W⁻¹ := by
    exact inv_anti₀ hW0 hWsq
  have hA : W * 1 * W⁻¹ = 1 := by field_simp
  refine ⟨W, W, 1, W⁻¹, 14, 1, W ^ 2, 0,
    hWexp, by dsimp [W]; nlinarith [Real.add_one_le_exp (4096 : ℝ)],
    by norm_num, inv_pos.mpr hW0, by nlinarith [sq_nonneg W],
    by norm_num, by norm_num, by norm_num,
    hη, ?_, ?_, by nlinarith, le_rfl, ?_, ?_, ?_⟩
  · rw [hA]
  · rw [hA]
    nlinarith [sq_nonneg W]
  · simp
  · dsimp [W]
    norm_num [Real.log_exp]
  · dsimp [W]
    norm_num [Real.log_exp]

/-- With `D ≥ 1`, the endpoint logarithmic hypothesis supplies the explicit
threshold required by the near/far `b` producer. -/
theorem four_le_log_of_one_le_D {W D : ℝ}
    (hD : 1 ≤ D) (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    4 ≤ Real.log W := by nlinarith

theorem sixteen_le_log_of_one_le_D {W D : ℝ}
    (hD : 1 ≤ D) (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    16 ≤ Real.log W := by nlinarith

/-- The model-level near-restricted `(5.64)` input, with the `Gsq` bound at
the resolvent scale supplied by the block-level (G\) witnesses. -/
theorem eeL6_near_remainder (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω) (σ : Fin 2 → Bool)
    {ℓu ηu D J : ℝ} (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hJ : 1 ≤ J) (hlog4 : 4 ≤ Real.log (B.W N : ℝ))
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D
        (zdist (B.L N) (x - y)))
    (hGsq_eta : ∀ x y, Gsq x y ≤ ηu⁻¹ ^ 2)
    (c : LoopArg (B.L N) 2) :
    (zdist (B.L N) (c 0 - c 1) : ℝ) ≤
      4 * ellStar (B.W N : ℝ) ℓu →
      ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu <
        (zdist (B.L N) (c 0 - b) : ℝ) →
        eeL6 X E N u ω σ (Fin.append c c) b ≤
          nearEpsilon (B.W N : ℝ) (B.L N : ℝ) ℓu ηu D J *
            tailT (B.W N : ℝ) ℓu ηu D
              (zdist (B.L N) (c 0 - c 1)) ^ 2 /
            ((B.W N : ℝ) * (B.L N : ℝ)) := by
  intro hnear b hb
  have hc0 : rightArg (Fin.append c c) 0 = leftArg (Fin.append c c) 0 := by
    rw [leftArg_append, rightArg_append]
  have hc1 : rightArg (Fin.append c c) 1 = leftArg (Fin.append c c) 1 := by
    rw [leftArg_append, rightArg_append]
  have hcore : eeL6 X E N u ω σ (Fin.append c c) b ≤
      2 * ηu⁻¹ ^ 2 * J ^ 2 *
        tailT (B.W N : ℝ) ℓu ηu D
          (Lemma57.ellStarStar (B.W N : ℝ) ℓu -
            4 * ellStar (B.W N : ℝ) ℓu) ^ 2 := by
    exact eeL6_le_nearFar X E N u ω σ (Fin.append c c) b
      hℓu hJ hlog4 hc0 hc1
      (by simpa only [leftArg_append] using hnear)
      (by simpa only [leftArg_append] using hb)
      hGm0 hGm hGsq2 hrow h42sq
      (hGsq_eta _ _) (hGsq_eta _ _)
  exact nearRem_of_nearFar
    (W := (B.W N : ℝ)) (L := (B.L N : ℝ))
    (D := D) (J := J) (d := (zdist (B.L N) (c 0 - c 1) : ℝ))
    (EEDef.one_le_W B N)
    (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (B.three_le_L N)))
    hℓu hηu (by linarith) hnear hcore

/-- The endpoint logarithmic window simultaneously supplies the explicit
`log W ≥ 4` input to the near remainder producer and to the epsilon estimate.
This is the §18 interface between parts (c), (d), and the primed endpoint. -/
theorem nearPackage_of_endpoint_hlog (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω) (σ : Fin 2 → Bool)
    {ℓu ηu D J k : ℝ}
    (hW : Real.exp 1 ≤ (B.W N : ℝ))
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hD1 : 1 ≤ D) (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    (hN : 1 ≤ (N : ℝ)) (hk : 0 ≤ k) (hD : 2 * k + 14 ≤ D)
    (hη : (N : ℝ)⁻¹ ≤ ηu)
    (hA : 1 ≤ (B.W N : ℝ) * ℓu * ηu)
    (hAN : (B.W N : ℝ) * ℓu * ηu ≤ (N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ))
    (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hJN : J ≤ (N : ℝ) ^ k)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D
        (zdist (B.L N) (x - y)))
    (hGsq_eta : ∀ x y, Gsq x y ≤ ηu⁻¹ ^ 2) :
    0 ≤ nearEpsilon (B.W N : ℝ) (B.L N : ℝ) ℓu ηu D J ∧
      (∀ c : LoopArg (B.L N) 2,
        (zdist (B.L N) (c 0 - c 1) : ℝ) ≤
            4 * ellStar (B.W N : ℝ) ℓu →
          ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu <
              (zdist (B.L N) (c 0 - b) : ℝ) →
            eeL6 X E N u ω σ (Fin.append c c) b ≤
              nearEpsilon (B.W N : ℝ) (B.L N : ℝ) ℓu ηu D J *
                tailT (B.W N : ℝ) ℓu ηu D
                  (zdist (B.L N) (c 0 - c 1)) ^ 2 /
                ((B.W N : ℝ) * (B.L N : ℝ))) ∧
      nearEpsilon (B.W N : ℝ) (B.L N : ℝ) ℓu ηu D J ≤
        (B.W N : ℝ)⁻¹ := by
  have hlog16 : 16 ≤ Real.log (B.W N : ℝ) :=
    sixteen_le_log_of_one_le_D hD1 hlog
  have hlog4 : 4 ≤ Real.log (B.W N : ℝ) := by linarith
  have hL : 0 < (B.L N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (B.three_le_L N))
  refine ⟨?_, ?_, ?_⟩
  · unfold nearEpsilon
    positivity
  · intro c
    exact eeL6_near_remainder X E N u ω σ hℓu hηu hJ hlog4
      hGm0 hGm hGsq2 hrow h42sq hGsq_eta c
  · exact nearEpsilon_le_inv hW hL hℓu hηu hN hk (by linarith) hD
      hη hA hAN hWL hNW hJN hlog4 hlog

theorem ee_le_EEpath_sym' (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (c : LoopArg (B.L N) ((0 + 2) + (0 + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ε : ℝ} (hε : 0 ≤ ε)
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
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564' : (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ)
      ≤ 4 * ellStar (B.W N : ℝ) ℓu →
      ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
        < (zdist (B.L N) (lab₁ c - b) : ℝ) →
        eeL6 X E N u ω σ c b ≤
          ε * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2 / ((B.W N : ℝ) * (B.L N : ℝ)))
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
              then 1 else 0)
          + ηu * ε *
            (if (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
              then 1 else 0)
          + Lemma57.cFar2 (B.W N : ℝ) ℓu
            * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
          + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2
        + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2 := by
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hJ2 : (1 : ℝ) ≤ 2 * J := by linarith
  have hμ : (0 : ℝ) ≤ 2 * √Smax := by positivity
  have h42sq' : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ 2 * J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
    intro x y hxy
    have h := h42sq x y hxy
    have hT : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
      tailT_nonneg hW0.le _
    nlinarith
  exact Lemma57.ee_le_sym' (B.L N) hW hℓu hℓs hηu hJ2 (lab₁ c) (lab₂ c) hμ hε hGsq0
    h273 h564' h42sq'
    (fun b _ => eeL6_two_le_near₁ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2 hrow hSmax)
    (fun b _ => eeL6_two_le_near₂ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2 hrow hSmax)
    (fun b hfar hb1 hb2 => eeL6_two_le_far X E N u ω σ c b (by linarith) hJ hc0 hc1
      hGm0 hGm hGsq0 hGsq2 hrow h42sq hfar hb1 hb2)
    (norm_EEpath_le_W_sum X E u ω σ c)

end EEDef

namespace APrimeQVEndpoint
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The diagonal QV envelope with the `(5.64)` remainder supported on the
near field.  The coefficient `2 ε` is the factor from the two-copy QV. -/
noncomputable def diagShape' (B : Band Ω) (N : ℕ)
    (ℓu ℓs ηu D J Smax ε : ℝ)
    (b : LoopArg (B.L N) (0 + 2)) : ℝ :=
  (diagNearRate B N ℓu ℓs ηu + 2 * ε) *
      (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤
          4 * ellStar (B.W N : ℝ) ℓu then 1 else 0) *
      tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2 +
    diagFarRate B N ℓu ηu D J Smax *
      tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2

end APrimeQVEndpoint

namespace EarlyQVRate
open Matrix Finset Gauss EEBridge MomentDuhamel
variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- T262 with the near-supported remainder of `EEDef.ee_le_EEpath_sym'`. -/
theorem quadVar_lkFun_le_ee_sym' (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ}
    {Smax ε : ℝ} (hε : 0 ≤ ε)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤
      (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 *
        ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564' : (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
        4 * ellStar (B.W N : ℝ) ℓu →
      ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu <
        (zdist (B.L N) (a 0 - b) : ℝ) →
        EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤
          ε * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (a 0 - a 1)) ^ 2 /
            ((B.W N : ℝ) * (B.L N : ℝ)))
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D
        (zdist (B.L N) (x - y))) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a)
      (X.H N u ω) ≤
        APrimeQVEndpoint.diagShape' B N ℓu ℓs ηu D J Smax ε a := by
  have hbridge := quadVar_lkFun_le_norm_eeFun (n := 0) hE hu0 hu1 σ
    (X.hermitian N u ω) a
  have hc0 : EEBridge.rightArg (Fin.append a a) 0 =
      EEBridge.leftArg (Fin.append a a) 0 := by
    rw [EEBridge.leftArg_append, EEBridge.rightArg_append]
  have hc1 : EEBridge.rightArg (Fin.append a a) 1 =
      EEBridge.leftArg (Fin.append a a) 1 := by
    rw [EEBridge.leftArg_append, EEBridge.rightArg_append]
  have h564'' : (zdist (B.L N)
      (EEDef.lab₁ (Fin.append a a) - EEDef.lab₂ (Fin.append a a)) : ℝ) ≤
      4 * ellStar (B.W N : ℝ) ℓu →
      ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu <
        (zdist (B.L N) (EEDef.lab₁ (Fin.append a a) - b) : ℝ) →
        EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤
          ε * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N)
              (EEDef.lab₁ (Fin.append a a) - EEDef.lab₂ (Fin.append a a))) ^ 2 /
            ((B.W N : ℝ) * (B.L N : ℝ)) := by
    rw [lab₁_append, lab₂_append]
    exact h564'
  have hee := EEDef.ee_le_EEpath_sym' X E u ω σ (Fin.append a a)
    hℓu hℓs hηu hJ hc0 hc1 hε hGm0 hGm hGsq0 hGsq2 hrow
    hSmax h273 h564'' h42sq
  rw [lab₁_append, lab₂_append] at hee
  have hcast : ((0 : ℕ) : ℝ) + 2 = 2 := by norm_num
  rw [hcast] at hbridge
  have hmain := hbridge.trans (mul_le_mul_of_nonneg_left hee (by norm_num : (0 : ℝ) ≤ 2))
  convert hmain using 1
  unfold APrimeQVEndpoint.diagShape' APrimeQVEndpoint.diagNearRate
    APrimeQVEndpoint.diagFarRate
  have hWne : (B.W N : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (EEDef.one_le_W B N))
  field_simp [hWne, ne_of_gt hηu, ne_of_gt hℓs]
  ring

end EarlyQVRate

namespace APrimeQVEndpoint
variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem sqrt_add_le_t280g (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  have hxy : 0 ≤ √x * √y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt (add_nonneg hx hy), Real.sqrt_nonneg x,
    Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y)]

theorem sqrt_three_le_t280g {A B C T χ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hχ : χ = 0 ∨ χ = 1) :
    √((A * χ + B) * T ^ 2 + C)
      ≤ √A * (T * χ) + √B * T + √C := by
  rcases hχ with rfl | rfl
  · simp only [mul_zero, zero_add, mul_zero, zero_add]
    calc
      √(B * T ^ 2 + C) ≤ √(B * T ^ 2) + √C :=
        sqrt_add_le_t280g _ _ (mul_nonneg hB (sq_nonneg _)) hC
      _ = √B * T + √C := by rw [Real.sqrt_mul hB, Real.sqrt_sq hT]
  · simp only [mul_one]
    have hAB : 0 ≤ A * T ^ 2 + B * T ^ 2 :=
      add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _))
    have heq : (A + B) * T ^ 2 + C = (A * T ^ 2 + B * T ^ 2) + C := by ring
    rw [heq]
    calc
      √(A * T ^ 2 + B * T ^ 2 + C)
        ≤ √(A * T ^ 2 + B * T ^ 2) + √C := sqrt_add_le_t280g _ _ hAB hC
      _ ≤ (√(A * T ^ 2) + √(B * T ^ 2)) + √C := by
        gcongr
        exact sqrt_add_le_t280g _ _ (mul_nonneg hA (sq_nonneg _))
          (mul_nonneg hB (sq_nonneg _))
      _ = √A * T + √B * T + √C := by
        rw [Real.sqrt_mul hA, Real.sqrt_mul hB, Real.sqrt_sq hT]


theorem sqrt_quadVar_Uker_le_diagShape' (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ε : ℝ} (hε : 0 ≤ ε)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ c b, EEDef.eeL6 X E N u ω σ (Fin.append c c) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2
        * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564' : ∀ c, (zdist (B.L N) (c 0 - c 1) : ℝ) ≤
        4 * ellStar (B.W N : ℝ) ℓu →
      ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu <
        (zdist (B.L N) (c 0 - b) : ℝ) →
        EEDef.eeL6 X E N u ω σ (Fin.append c c) b ≤
          ε * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (c 0 - c 1)) ^ 2 /
            ((B.W N : ℝ) * (B.L N : ℝ)))
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b) M') a)
        (X.H N u ω))
      ≤ ∑ b : LoopArg (B.L N) (0 + 2),
          ‖∏ i : Fin (0 + 2), edgeKer (B.L N) (xiOf (mSigma E) σ i)
              (u : ℂ) (v : ℂ) (a i) (b i)‖ *
            √(diagShape' B N ℓu ℓs ηu D J Smax ε b) := by
  have hmink := sqrt_quadVar_Uker_loopObs_le X hE (u := u) (v := v) hu1 ω σ a
  refine hmink.trans (Finset.sum_le_sum fun b _ => ?_)
  have hdiag : Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' σ b) (X.H N u ω)
      ≤ diagShape' B N ℓu ℓs ηu D J Smax ε b := by
    exact EarlyQVRate.quadVar_lkFun_le_ee_sym' X hE hu0 hu1 ω σ b
      hℓu hℓs hηu hJ hε hGm0 hGm hGsq0 hGsq2 hrow hSmax
      (h273 b) (h564' b) h42sq
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdiag) (norm_nonneg _)

/-- The new diagonal envelope has only near and far tail terms. -/
theorem sqrt_diagShape_le_two' (B : Band Ω) (N : ℕ)
    {ℓu ℓs ηu D J Smax ε : ℝ}
    (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu)
    (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    (hJ : 1 ≤ J) (hε : 0 ≤ ε)
    (b : LoopArg (B.L N) (0 + 2)) :
    √(diagShape' B N ℓu ℓs ηu D J Smax ε b) ≤
      √(diagNearRate B N ℓu ℓs ηu + 2 * ε) *
        (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) *
          (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤
            4 * ellStar (B.W N : ℝ) ℓu then 1 else 0)) +
      √(diagFarRate B N ℓu ηu D J Smax) *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) := by
  let T : ℝ := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1))
  let χ : ℝ := if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤
    4 * ellStar (B.W N : ℝ) ℓu then 1 else 0
  let An : ℝ := diagNearRate B N ℓu ℓs ηu + 2 * ε
  let Af : ℝ := diagFarRate B N ℓu ηu D J Smax
  have hnear0 : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) ℓu :=
    Lemma57.cNear2_nonneg hW hℓu
  have hfar0 : 0 ≤ Lemma57.cFar2 (B.W N : ℝ) ℓu :=
    Lemma57.cFar2_nonneg hW hℓu
  have hAn : 0 ≤ An := by dsimp [An, diagNearRate]; positivity
  have hAf : 0 ≤ Af := by dsimp [Af, diagFarRate]; positivity
  have hT : 0 ≤ T := tailT_nonneg (by linarith : (0 : ℝ) ≤ B.W N) _
  have hχ : χ = 0 ∨ χ = 1 := by simp only [χ]; split_ifs <;> simp
  have hshape : diagShape' B N ℓu ℓs ηu D J Smax ε b =
      (An * χ + Af) * T ^ 2 + 0 := by
    dsimp [diagShape', An, Af, T, χ]
    ring
  rw [hshape]
  simpa only [Real.sqrt_zero, add_zero] using
    (sqrt_three_le_t280g hAn hAf (by norm_num : (0 : ℝ) ≤ 0) hT hχ)


set_option maxHeartbeats 2000000 in
-- The endpoint elaborates the pointwise T262 hypothesis bundle.
theorem sqrt_evolvedQV_le_endpoint' (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (ω : Ω)
    (a : LoopArg (B.L N) 2)
    {ℓs D J : ℝ} (hℓs : 0 < ℓs) (hJ : 1 ≤ J)
    (hD : 1 ≤ D)
    (hAu : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u)
    (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ε : ℝ} (hε : 0 ≤ ε)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ c b, EEDef.eeL6 X E N u ω Step2.sigPM (Fin.append c c) b
      ≤ (B.ell N u / ℓs) ^ 5 *
        ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹) ^ 2 *
        ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (h564' : ∀ c, (zdist (B.L N) (c 0 - c 1) : ℝ) ≤
        4 * ellStar (B.W N : ℝ) (B.ell N u) →
      ∀ b, Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) <
        (zdist (B.L N) (c 0 - b) : ℝ) →
        EEDef.eeL6 X E N u ω Step2.sigPM (Fin.append c c) b ≤
          ε * Step2.tT B E N D u (zdist (B.L N) (c 0 - c 1)) ^ 2 /
            ((B.W N : ℝ) * (B.L N : ℝ)))
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2
        ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * Step2.tT B E N D u (zdist (B.L N) (x - y))) :
    √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
          (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u)
            (Gauss.toIdx Step2.sigPM b) M') a)
        (X.H N u ω))
      ≤ √(diagNearRate B N (B.ell N u) ℓs (etaT E u) + 2 * ε) *
          ((((1 - u) / (1 - v)) ^ 2 *
              Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
              Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) *
            (if (zdist (B.L N) (a 0 - a 1) : ℝ)
                ≤ 6 * ellStar (B.W N : ℝ) (B.ell N v) then 1 else 0)
          + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
              (B.W N : ℝ) ^ (-D) *
              Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))
        + √(diagFarRate B N (B.ell N u) (etaT E u) D J Smax) *
          (((1 - u) / (1 - v)) ^ 2 *
            Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
            Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))
        := by
  classical
  have hu1 : u < 1 := huv.trans_lt hv1
  have hL1 : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hℓu : 1 ≤ B.ell N u :=
    one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hW0 : 0 ≤ (B.W N : ℝ) := by positivity
  have hW1 : 1 ≤ (B.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hW
  have hℓv : 0 < ellHat (B.L N) (v : ℂ) := by
    have := one_le_ellHat_of_nonneg hL1 (hu0.trans huv) hv1
    linarith
  have hAuv : (B.W N : ℝ) * ellHat (B.L N) (v : ℂ) *
      ((1 - v) * (mE E).im) ≤
      (B.W N : ℝ) * ellHat (B.L N) (u : ℂ) *
      ((1 - u) * (mE E).im) := by
    have h := flowScale_antitoneOn hW0 (B.L N) E
      (Set.mem_Iic.2 (huv.trans hv1.le)) (Set.mem_Iic.2 hv1.le) huv
    exact h
  have hdiag := sqrt_quadVar_Uker_le_diagShape' X hE (u := u) (v := v) hu0 hu1 ω
    Step2.sigPM a hℓu hℓs hηu hJ hε hGm0 hGm hGsq0 hGsq2
    hrow hSmax h273 (by simpa only [Step2.tT] using h564')
      (by simpa only [Step2.tT] using h42sq)
  have hthree := weightedKernel_three_le (B.L N) (B.three_le_L N)
    (D := D)
    (Cn := √(diagNearRate B N (B.ell N u) ℓs (etaT E u) + 2 * ε))
    (Cf := √(diagFarRate B N (B.ell N u) (etaT E u) D J Smax))
    (Cr := 0)
    (mE_im_pos hE) (mE_im_le_one hE)
    hu0 huv hv1 hW hAuv
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0)
    (fun b : LoopArg (B.L N) 2 =>
      √(diagShape' B N (B.ell N u) ℓs (etaT E u) D J Smax ε b))
    (fun b => by
      convert (sqrt_diagShape_le_two' B N hW1
        (by linarith : 0 < B.ell N u) hℓs hηu hJ hε b) using 1
      simp only [Band.ell, Step2.etaT_eq, add_zero]
      rfl) a
  rw [Step2.sigPM_xi hE.le] at hdiag
  have hAu' : 1 ≤ (B.W N : ℝ) * ellHat (B.L N) (u : ℂ) *
      ((1 - u) * (mE E).im) := by
    simpa only [Band.ell, Step2.etaT_eq] using hAu
  have hnear := nearConvBd_le_indicator_farTail (B.L N)
    (m := (mE E).im) (u := u) (v := v)
    (W := (B.W N : ℝ)) (D := D) hW (by linarith : 0 ≤ D) hAu' hℓv hlog a
  have hmul := mul_le_mul_of_nonneg_left hnear (Real.sqrt_nonneg
    (diagNearRate B N (B.ell N u) ℓs (etaT E u) + 2 * ε))
  simp only [zero_mul, add_zero] at hthree
  have hmain := hdiag.trans hthree
  have hfinal :
      √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u)
            (Gauss.toIdx Step2.sigPM b) M') a) (X.H N u ω))
        ≤ √(diagNearRate B N (B.ell N u) ℓs (etaT E u) + 2 * ε) *
            (((1 - u) / (1 - v)) ^ 2 * Step2.xiK (B.L N) (B.W N : ℝ)
              (mE E).im *
              tailT (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                ((1 - v) * (mE E).im) D (zdist (B.L N) (a 0 - a 1)) *
              (if (zdist (B.L N) (a 0 - a 1) : ℝ)
                  ≤ 6 * ellStar (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                then 1 else 0)
            + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
                (B.W N : ℝ) ^ (-D) *
                tailT (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                  ((1 - v) * (mE E).im) D
                  (zdist (B.L N) (a 0 - a 1)))
          + √(diagFarRate B N (B.ell N u) (etaT E u) D J Smax) *
            (((1 - u) / (1 - v)) ^ 2 * Step2.xiK (B.L N) (B.W N : ℝ)
              (mE E).im *
              tailT (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                ((1 - v) * (mE E).im) D (zdist (B.L N) (a 0 - a 1)))
          := by
    linarith only [hmain, hmul]
  rw [Step2.sigPM_xi hE.le, Step2.tT, Band.ell, Step2.etaT_eq]
  exact hfinal

end APrimeQVEndpoint

/-- The endpoint hypotheses in §17 do not force `log W ≥ 3`: with `D = 0`,
`W = exp 1` satisfies all three hypotheses while `log W = 1`.  The
near/far `b` producer therefore needs an additional lower bound on `D` or
directly on `log W`. -/
theorem not_log_three_of_endpoint_hlog :
    ¬ (∀ (W D : ℝ), Real.exp 1 ≤ W → 0 ≤ D →
      (4 * D) ^ 2 ≤ Real.log W → 3 ≤ Real.log W) := by
  intro h
  have hlog : (4 * (0 : ℝ)) ^ 2 ≤ Real.log (Real.exp 1) := by
    norm_num [Real.log_exp]
  have hthree := h (Real.exp 1) 0 le_rfl (by norm_num) hlog
  norm_num [Real.log_exp] at hthree

end RBM
