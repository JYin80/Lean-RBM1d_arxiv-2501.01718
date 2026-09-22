/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftNearAbsorb

/-!
# T364: multiplier-aware near branch of the three-loop drift

Both source multipliers are retained.  The far-internal-label remainder is
absorbed only on the near-output support; no far-output or event assertion is
made here.
-/

namespace RBM.APrimeEGNearScaled

open Real

/-- The finite-sum split keeps the length-three source multiplier explicit. -/
theorem near_sum_scaled (L : ℕ) [NeZero L] {W ℓu ℓs ηu n ζ₃ C₃ ρ : ℝ}
    (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs)
    (hn : 0 < n) (hC₃ : 0 < C₃) (hρ : 0 ≤ ρ)
    (a₁ : ZMod L) {L3 : ZMod L → ℝ}
    (h273 : ∀ b, L3 b ≤ C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2 *
      ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L3 b ≤ ρ) :
    ∑ b : ZMod L, L3 b ≤
      (2 * Lemma57.ellStarStar W ℓu + 2) *
        (C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2 *
          ((W * ℓu * ηu) ^ 2)⁻¹) + (L : ℝ) * ρ := by
  have hss : 0 ≤ Lemma57.ellStarStar W ℓu :=
    Lemma57.ellStarStar_nonneg hW hℓu.le
  have hq : 0 ≤ C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2 *
      ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hsplit := Lemma57.sum_le_split_one L (fun _ => hρ) hss a₁ hq
    (fun b _ => h273 b) (fun b hb => h554 b hb)
  have hconst : (∑ _b : ZMod L, ρ) = (L : ℝ) * ρ := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rwa [hconst] at hsplit

/-- Multiplier-aware (5.53)–(5.54): the near principal coefficient retains
both the averaged one-loop and length-three source losses. -/
theorem eG_near_le_scaled (L : ℕ) [NeZero L]
    {W ℓu ℓs ηu D n ζ₁ ζ₃ C₁ C₃ ρ : ℝ}
    (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    (hn : 0 < n) (hC₁ : 0 < C₁) (hC₃ : 0 < C₃) (hρ : 0 ≤ ρ)
    {a₁ a₂ : ZMod L}
    (hnear : (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu)
    {L3 : ZMod L → ℝ} {EG : ℝ}
    (h273 : ∀ b, L3 b ≤ C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2 *
      ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L3 b ≤ ρ)
    (hEG : EG ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
      (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ 2 * C₁ * C₃ * n ^ (ζ₁ + ζ₃) * ηu⁻¹ *
        (ℓu / ℓs) ^ 3 * Lemma57.cNear W ℓu *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) +
      (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
        (ℓu * ηu)⁻¹ * (L : ℝ) * ρ := by
  have hℓ : 0 < ℓu := by linarith
  have hW0 : 0 < W := by linarith
  have hstar : 0 ≤ Lemma57.ellStarStar W ℓu :=
    Lemma57.ellStarStar_nonneg hW hℓ.le
  have hκ : 0 ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) * (ℓu * ηu)⁻¹ := by
    positivity
  have hsum := near_sum_scaled L hW hℓ hℓs hn hC₃ hρ a₁ h273 h554
  have hfloor := Lemma57.inv_sq_le_tailT (D := D) hW hℓ hηu hnear
  have hfac : 0 ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
      (ℓu * ηu)⁻¹ *
      (2 * Lemma57.ellStarStar W ℓu + 2) *
      (C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2) := by positivity
  have htail := mul_le_mul_of_nonneg_left hfloor hfac
  have hnorm :
      (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
          (ℓu * ηu)⁻¹ *
          (2 * Lemma57.ellStarStar W ℓu + 2) *
          (C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2) *
          (Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
            tailT W ℓu ηu D (zdist L (a₁ - a₂))) =
        2 * C₁ * C₃ * n ^ (ζ₁ + ζ₃) * ηu⁻¹ *
          (ℓu / ℓs) ^ 3 * Lemma57.cNear W ℓu *
            tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
    rw [Real.rpow_add hn]
    unfold Lemma57.cNear Lemma57.ellStarStar
    field_simp
  calc
    EG ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
        (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b := hEG
    _ ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) * (ℓu * ηu)⁻¹ *
        ((2 * Lemma57.ellStarStar W ℓu + 2) *
          (C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2 *
            ((W * ℓu * ηu) ^ 2)⁻¹) + (L : ℝ) * ρ) :=
      mul_le_mul_of_nonneg_left hsum hκ
    _ ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
          (ℓu * ηu)⁻¹ *
          (2 * Lemma57.ellStarStar W ℓu + 2) *
          (C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2) *
          (Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
            tailT W ℓu ηu D (zdist L (a₁ - a₂))) +
        (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
          (ℓu * ηu)⁻¹ * (L : ℝ) * ρ := by
      nlinarith [htail]
    _ = _ := by rw [hnorm]

/-- The scaled near branch after T357 absorbs its supported remainder.  The
source's `h554` is requested only when the output pair is near. -/
theorem eG_near_indicator_le_scaled_absorb (L : ℕ) [NeZero L]
    {W ℓu ℓs ηu n ζ₁ ζ₃ C₁ C₃ J : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hn : 1 ≤ n)
    (hC₁ : 0 < C₁) (hC₃ : 0 < C₃)
    (hζ₁0 : 0 ≤ ζ₁) (hζ₁1 : ζ₁ ≤ 1) (hζ₃ : 0 ≤ ζ₃)
    (hJ0 : 0 ≤ J) (hJ : J ≤ n)
    (hr : 1 ≤ ℓu / ℓs)
    (hA1 : 1 ≤ W * ℓu * ηu) (hA : W * ℓu * ηu ≤ n)
    (hL : (L : ℝ) ≤ n) (hη : ηu⁻¹ ≤ n) (hnW : n ≤ W ^ 2)
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log W)
    (hCcap : 4 * C₁ ≤ W)
    (a₁ a₂ : ZMod L) {L3 : ZMod L → ℝ} {EG : ℝ}
    (h273 : ∀ b, L3 b ≤ C₃ * n ^ ζ₃ * (ℓu / ℓs) ^ 2 *
      ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu →
      ∀ b, Lemma57.ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) →
        L3 b ≤ ηu⁻¹ * J *
          tailT W ℓu ηu 60 (APrimeDriftNearAbsorb.gap W ℓu))
    (hEG : EG ≤ (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) *
      (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG * (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0) ≤
      (2 * C₁ * C₃ * n ^ (ζ₁ + ζ₃) * ηu⁻¹ *
          (ℓu / ℓs) ^ 3 * Lemma57.cNear W ℓu *
            tailT W ℓu ηu 60 (zdist L (a₁ - a₂)) +
        W⁻¹ * APrimeDriftNearAbsorb.nearRate W ℓu ηu 60
          (ℓu / ℓs) (zdist L (a₁ - a₂) : ℝ)) *
        (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0) := by
  by_cases hd : (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu
  · simp only [if_pos hd, mul_one]
    have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
    have hρ : 0 ≤ ηu⁻¹ * J *
        tailT W ℓu ηu 60 (APrimeDriftNearAbsorb.gap W ℓu) := by
      have ht : 0 ≤ tailT W ℓu ηu 60 (APrimeDriftNearAbsorb.gap W ℓu) :=
        (tailT_pos ((Real.exp_pos 1).trans_le hW) _).le
      positivity
    have hbase := eG_near_le_scaled L (D := 60) hW1 hℓu hℓs hηu
      (by linarith : 0 < n) hC₁ hC₃ hρ hd h273 (h554 hd) hEG
    have hres_eq :
        (2 * C₁ * n ^ ζ₁ * (ℓu / ℓs)) * (ℓu * ηu)⁻¹ *
          (L : ℝ) *
          (ηu⁻¹ * J * tailT W ℓu ηu 60
            (APrimeDriftNearAbsorb.gap W ℓu)) =
        APrimeDriftNearAbsorb.residual W L ℓu ηu 60 J
          (ℓu / ℓs) C₁ n ζ₁ := by
      unfold APrimeDriftNearAbsorb.residual
      field_simp
    have hrem := APrimeDriftNearAbsorb.residual_indicator_le_invW
      hW hℓu hηu hr hn hζ₁0 hζ₁1
      (Nat.cast_nonneg L) hJ0 hC₁.le hL hJ hA1 hA hη hnW hlog hCcap
      (d := (zdist L (a₁ - a₂) : ℝ))
    simp only [if_pos hd, mul_one] at hrem
    rw [hres_eq] at hbase
    exact le_trans hbase (add_le_add le_rfl hrem)
  · simp only [if_neg hd, mul_zero]
    exact le_rfl

private theorem witness_far_distance :
    zdist (2 ^ 100) ((0 : ZMod (2 ^ 100)) - (2 ^ 99 : ZMod (2 ^ 100))) =
      2 ^ 99 := by
  rw [Lemma57.zdist_sub_comm]
  decide +kernel

private theorem witness_W_ge_L :
    (2 ^ 100 : ℝ) ≤ Real.exp 57600 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    (2 : ℝ) ^ 100 ≤ (Real.exp 1) ^ 100 :=
      pow_le_pow_left₀ (by norm_num) htwo _
    _ = Real.exp 100 := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ Real.exp 57600 :=
      Real.exp_le_exp.2 (by norm_num)

/-- The new abstract source hypotheses are jointly satisfiable with positive
near and far geometry, a nonzero summand and a strict first time cell. -/
theorem first_cell_scaled_witness :
    let W : ℝ := Real.exp 57600
    let n : ℝ := W ^ 2
    let η : ℝ := W⁻¹
    let L : ℕ := 2 ^ 100
    let b : ZMod L := 2 ^ 99
    let ρ : ℝ := η⁻¹ * (1 : ℝ) *
      tailT W 1 η 60 (APrimeDriftNearAbsorb.gap W 1)
    ∃ (L3 : ZMod L → ℝ) (EG : ℝ),
      0 < ρ ∧ 0 < L3 b ∧ 0 < EG ∧
      gridT W 1 (1 / 2) 0 = 0 ∧
      0 < gridT W 1 (1 / 2) 1 ∧
      (zdist L ((0 : ZMod L) - 0) : ℝ) ≤ ellStar W 1 ∧
      Lemma57.ellStarStar W 1 <
        (zdist L ((0 : ZMod L) - b) : ℝ) ∧
      (∀ c, L3 c ≤ (1 : ℝ) * n ^ (0 : ℝ) * (1 / 1 : ℝ) ^ 2 *
        ((W * 1 * η) ^ 2)⁻¹) ∧
      (∀ c, Lemma57.ellStarStar W 1 <
          (zdist L ((0 : ZMod L) - c) : ℝ) → L3 c ≤ ρ) ∧
      EG ≤ (2 * (1 : ℝ) * n ^ (0 : ℝ) * (1 / 1 : ℝ)) *
        (1 * η)⁻¹ * ∑ c : ZMod L, L3 c ∧
      (L : ℝ) ≤ n ∧ η⁻¹ ≤ n ∧
      1 ≤ W * 1 * η ∧ W * 1 * η ≤ n ∧ n ≤ W ^ 2 ∧
      (4 * (60 : ℝ)) ^ 2 ≤ Real.log W ∧ 4 * (1 : ℝ) ≤ W := by
  let W : ℝ := Real.exp 57600
  let n : ℝ := W ^ 2
  let η : ℝ := W⁻¹
  let L : ℕ := 2 ^ 100
  let b : ZMod L := 2 ^ 99
  let ρ : ℝ := η⁻¹ * (1 : ℝ) *
    tailT W 1 η 60 (APrimeDriftNearAbsorb.gap W 1)
  letI : NeZero L := ⟨by dsimp [L]; norm_num⟩
  let L3 : ZMod L → ℝ := fun _ => min 1 ρ
  let EG : ℝ := min 1 ρ
  have hW0 : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp (by norm_num)
  have hW4 : 4 ≤ W := by
    have h := Real.add_one_le_exp (57600 : ℝ)
    dsimp [W]
    linarith
  have hn : 1 ≤ n := by dsimp [n]; nlinarith
  have hη : 0 < η := inv_pos.mpr hW0
  have hηinv : η⁻¹ = W := by dsimp [η]; simp
  have hA : W * (1 : ℝ) * η = 1 := by
    dsimp [η]
    field_simp
  have hT : 0 < tailT W 1 η 60 (APrimeDriftNearAbsorb.gap W 1) :=
    tailT_pos hW0 _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hEG : 0 < EG := by dsimp [EG]; exact lt_min (by norm_num) hρ
  have hL3 : 0 < L3 b := hEG
  have hgrid0 : gridT W 1 (1 / 2) 0 = 0 := gridT_zero (by norm_num)
  have hgrid1 : 0 < gridT W 1 (1 / 2) 1 := by
    have hp : W ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1 < W) (by norm_num)
    unfold gridT gridS
    simp only [Nat.cast_one, one_mul]
    exact lt_min (sub_pos.mpr hp) (by norm_num)
  have hnear : (zdist L ((0 : ZMod L) - 0) : ℝ) ≤ ellStar W 1 := by
    simp only [sub_self, zdist_zero, Nat.cast_zero]
    unfold ellStar
    simpa only [mul_one] using
      (Real.rpow_nonneg (Real.log_nonneg hW1) (3 / 2 : ℝ))
  have hfar : Lemma57.ellStarStar W 1 <
      (zdist L ((0 : ZMod L) - b) : ℝ) := by
    have hd : zdist L ((0 : ZMod L) - b) = 2 ^ 99 :=
      witness_far_distance
    rw [hd]
    dsimp [Lemma57.ellStarStar, W]
    rw [Real.log_exp]
    norm_num
  have h273 : ∀ c : ZMod L, L3 c ≤ (1 : ℝ) * n ^ (0 : ℝ) *
      (1 / 1 : ℝ) ^ 2 * ((W * 1 * η) ^ 2)⁻¹ := by
    intro c
    dsimp [L3]
    rw [hA]
    norm_num
  have h554 : ∀ c : ZMod L, Lemma57.ellStarStar W 1 <
      (zdist L ((0 : ZMod L) - c) : ℝ) → L3 c ≤ ρ := by
    intro c _
    exact min_le_right _ _
  have hsum : (∑ c : ZMod L, L3 c) = (L : ℝ) * EG := by
    simp [L3, EG]
  have hcoeff : 1 ≤ 2 * W * (L : ℝ) := by
    have hL1 : (1 : ℝ) ≤ L := by dsimp [L]; norm_num
    nlinarith [mul_nonneg (by linarith : 0 ≤ W - 1)
      (by linarith : 0 ≤ (L : ℝ) - 1)]
  have hEGsrc : EG ≤
      (2 * (1 : ℝ) * n ^ (0 : ℝ) * (1 / 1 : ℝ)) *
        (1 * η)⁻¹ * ∑ c : ZMod L, L3 c := by
    rw [hsum]
    simp only [one_mul, Real.rpow_zero, mul_one, one_div_one]
    rw [hηinv]
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) hEG.le]
  have hLcap : (L : ℝ) ≤ n := by
    have hLw : (L : ℝ) ≤ W := by simpa only [L, W, Nat.cast_pow, Nat.cast_ofNat] using witness_W_ge_L
    have hWn : W ≤ n := by dsimp [n]; nlinarith [sq_nonneg (W - 1)]
    linarith
  have hηcap : η⁻¹ ≤ n := by
    rw [hηinv]
    dsimp [n]
    nlinarith [sq_nonneg (W - 1)]
  have hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log W := by
    dsimp [W]
    rw [Real.log_exp]
    norm_num
  exact ⟨L3, EG, hρ, hL3, hEG, hgrid0, hgrid1, hnear, hfar,
    h273, h554, hEGsrc, hLcap, hηcap,
    by rw [hA], by rw [hA]; exact hn, le_rfl, hlog,
    by simpa only [mul_one] using hW4⟩

end RBM.APrimeEGNearScaled

#print axioms RBM.APrimeEGNearScaled.near_sum_scaled
#print axioms RBM.APrimeEGNearScaled.eG_near_le_scaled
#print axioms RBM.APrimeEGNearScaled.eG_near_indicator_le_scaled_absorb
#print axioms RBM.APrimeEGNearScaled.first_cell_scaled_witness
