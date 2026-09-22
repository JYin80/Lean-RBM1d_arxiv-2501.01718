/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftNearTriple

/-!
# T357: numerical absorption of the near-only drift remainder

The one-loop multiplier `C N^ζ` is retained.  All inequalities here are
deterministic and conditional on the stated numerical cap for the actual block
witness.  No common event or averaged one-loop producer is asserted.
-/

namespace RBM.APrimeDriftNearAbsorb

open Real Filter

noncomputable def gap (W ℓu : ℝ) : ℝ :=
  Lemma57.ellStarStar W ℓu - ellStar W ℓu

noncomputable def residual (W L ℓu ηu D J r C N ζ : ℝ) : ℝ :=
  2 * C * N ^ ζ * (r * L / (ℓu * ηu)) *
    (ηu⁻¹ * J * tailT W ℓu ηu D (gap W ℓu))

noncomputable def nearRate (W ℓu ηu D r d : ℝ) : ℝ :=
  ηu⁻¹ * r ^ 3 * tailT W ℓu ηu D d

/-- The exact ratio keeps both powers of `ηu⁻¹` in the residual and cancels
only one against the target near rate. -/
theorem residual_ratio_eq {W L ℓu ηu D J r C N ζ d : ℝ}
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hr : 0 < r)
    (hW : 0 < W) :
    residual W L ℓu ηu D J r C N ζ /
        nearRate W ℓu ηu D r d =
      2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) *
        (tailT W ℓu ηu D (gap W ℓu) / tailT W ℓu ηu D d) := by
  have hTd : 0 < tailT W ℓu ηu D d := tailT_pos hW d
  unfold residual nearRate
  field_simp

/-- The near-output tail floor gives the exact `A² exp((log W)^(3/4))`
ratio loss; no powers of `ηu` or `r` are silently removed. -/
theorem residual_ratio_le {W L ℓu ηu D J r C N ζ d : ℝ}
    (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hr : 0 < r) (hL : 0 ≤ L) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hN : 0 < N) (hnear : d ≤ ellStar W ℓu) :
    residual W L ℓu ηu D J r C N ζ /
        nearRate W ℓu ηu D r d ≤
      2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) *
        ((W * ℓu * ηu) ^ 2 * Real.exp (Real.log W ^ (3 / 4 : ℝ))) *
          tailT W ℓu ηu D (gap W ℓu) := by
  have hW0 : 0 < W := by linarith
  have hTd : 0 < tailT W ℓu ηu D d := tailT_pos hW0 d
  have hA : 0 < W * ℓu * ηu := by positivity
  have hA2 : 0 < (W * ℓu * ηu) ^ 2 := sq_pos_of_pos hA
  have hfloor := Lemma57.inv_sq_le_tailT (D := D) hW hℓu hηu hnear
  have hOne : (1 : ℝ) ≤
      (W * ℓu * ηu) ^ 2 *
        (Real.exp (Real.log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d) := by
    have hmul := mul_le_mul_of_nonneg_left hfloor hA2.le
    calc
      (1 : ℝ) = (W * ℓu * ηu) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹ := by
        field_simp
      _ ≤ (W * ℓu * ηu) ^ 2 *
            (Real.exp (Real.log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d) := hmul
  have hInvTd : (tailT W ℓu ηu D d)⁻¹ ≤
      (W * ℓu * ηu) ^ 2 * Real.exp (Real.log W ^ (3 / 4 : ℝ)) := by
    rw [← one_div]
    apply (div_le_iff₀ hTd).2
    nlinarith [hOne]
  have hpref : 0 ≤ 2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) := by
    positivity
  have hTF : 0 ≤ tailT W ℓu ηu D (gap W ℓu) :=
    (tailT_pos hW0 _).le
  rw [residual_ratio_eq hℓu hηu hr hW0]
  calc
    2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) *
        (tailT W ℓu ηu D (gap W ℓu) / tailT W ℓu ηu D d)
      = (2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) *
          tailT W ℓu ηu D (gap W ℓu)) *
            (tailT W ℓu ηu D d)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ (2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) *
          tailT W ℓu ηu D (gap W ℓu)) *
            ((W * ℓu * ηu) ^ 2 * Real.exp (Real.log W ^ (3 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hInvTd (mul_nonneg hpref hTF)
    _ = _ := by ring

theorem gap_tail_le_two_floor {W ℓu ηu D : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hA : 1 ≤ W * ℓu * ηu) (hD : 0 ≤ D)
    (hlog4 : 4 ≤ Real.log W)
    (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    tailT W ℓu ηu D (gap W ℓu) ≤ 2 * W ^ (-D) := by
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar
    exact mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hW1) _) hℓu.le
  have hgap : Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu ≤ gap W ℓu := by
    dsimp [gap]
    linarith
  have hmono : tailT W ℓu ηu D (gap W ℓu) ≤
      tailT W ℓu ηu D (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) :=
    tailT_antitone hℓu hgap
  have hexp := EEDef.exp_nearFar_le_floor hW hℓu hD hlog4 hlog
  have hAinv : ((W * ℓu * ηu) ^ 2)⁻¹ ≤ 1 := by
    have hAsq : 1 ≤ (W * ℓu * ηu) ^ 2 := by nlinarith
    exact (inv_le_one₀ (by positivity : 0 < (W * ℓu * ηu) ^ 2)).2 hAsq
  have htail : tailT W ℓu ηu D
      (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) ≤
      2 * W ^ (-D) := by
    have hq0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    have he0 : 0 ≤ Real.exp (-Real.sqrt
      ((Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) / ℓu)) :=
      (Real.exp_pos _).le
    have hp := mul_le_mul hAinv hexp he0 (by positivity : 0 ≤ (1 : ℝ))
    dsimp [tailT] at hp ⊢
    nlinarith
  exact hmono.trans htail

theorem exp_subpow_le_W {W : ℝ} (hW : 0 < W)
    (hlog : 1 ≤ Real.log W) :
    Real.exp (Real.log W ^ (3 / 4 : ℝ)) ≤ W := by
  have hpow : Real.log W ^ (3 / 4 : ℝ) ≤ Real.log W := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hlog
      (by norm_num : (3 / 4 : ℝ) ≤ 1))
  simpa only [Real.exp_log hW] using Real.exp_le_exp.2 hpow

theorem cap_coefficient_le {W L ℓu ηu J r N : ℝ}
    (hW : 0 < W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu)
    (hr : 1 ≤ r) (hN : 1 ≤ N)
    (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J)
    (hL : L ≤ N) (hJ : J ≤ N)
    (hA : W * ℓu * ηu ≤ N) (hη : ηu⁻¹ ≤ N) :
    (L * J / (ℓu * ηu * r ^ 2)) * (W * ℓu * ηu) ^ 2 ≤ N ^ 5 := by
  have hℓinv : ℓu⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < ℓu)).2 hℓu
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hrinv : (r ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity : 0 < r ^ 2)).2 hr2
  have hA0 : 0 ≤ W * ℓu * ηu := by positivity
  calc
    (L * J / (ℓu * ηu * r ^ 2)) * (W * ℓu * ηu) ^ 2 =
        L * J * ℓu⁻¹ * ηu⁻¹ * (r ^ 2)⁻¹ * (W * ℓu * ηu) ^ 2 := by
          field_simp
    _ ≤ N * N * 1 * N * 1 * N ^ 2 := by gcongr
    _ = N ^ 5 := by ring

/-- Honest one-loop growth leaves the exponent `5+ζ`. -/
theorem residual_ratio_le_N {W L ℓu ηu D J r C N ζ d : ℝ}
    (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu)
    (hr : 1 ≤ r) (hN : 1 ≤ N)
    (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J) (hC : 0 ≤ C)
    (hL : L ≤ N) (hJ : J ≤ N)
    (hA : W * ℓu * ηu ≤ N) (hη : ηu⁻¹ ≤ N)
    (hnear : d ≤ ellStar W ℓu) :
    residual W L ℓu ηu D J r C N ζ /
        nearRate W ℓu ηu D r d ≤
      2 * C * N ^ (5 + ζ) *
        Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
          tailT W ℓu ηu D (gap W ℓu) := by
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hℓ0 : 0 < ℓu := by linarith
  have hr0 : 0 < r := by linarith
  have hcoeff := cap_coefficient_le hW0 hℓu hηu hr hN
    hL0 hJ0 hL hJ hA hη
  calc
    residual W L ℓu ηu D J r C N ζ /
        nearRate W ℓu ηu D r d ≤
      2 * C * N ^ ζ * (L * J / (ℓu * ηu * r ^ 2)) *
        ((W * ℓu * ηu) ^ 2 * Real.exp (Real.log W ^ (3 / 4 : ℝ))) *
          tailT W ℓu ηu D (gap W ℓu) :=
      residual_ratio_le hW hℓ0 hηu hr0 hL0 hJ0 hC hN0 hnear
    _ = (2 * C * N ^ ζ) *
        ((L * J / (ℓu * ηu * r ^ 2)) * (W * ℓu * ηu) ^ 2) *
        Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
          tailT W ℓu ηu D (gap W ℓu) := by ring
    _ ≤ (2 * C * N ^ ζ) * N ^ 5 *
        Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
          tailT W ℓu ηu D (gap W ℓu) := by
            gcongr
            exact (tailT_pos hW0 _).le
    _ = 2 * C * N ^ (5 + ζ) *
        Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
          tailT W ℓu ηu D (gap W ℓu) := by
      rw [Real.rpow_add hN0]
      norm_cast
      ring

/-- The exact power of `W` keeps the one-loop loss `2ζ`. -/
theorem residual_ratio_le_W {W L ℓu ηu D J r C N ζ d : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hζ : 0 ≤ ζ)
    (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J) (hC : 0 ≤ C)
    (hL : L ≤ N) (hJ : J ≤ N)
    (hA1 : 1 ≤ W * ℓu * ηu) (hA : W * ℓu * ηu ≤ N)
    (hη : ηu⁻¹ ≤ N) (hNW : N ≤ W ^ 2)
    (hnear : d ≤ ellStar W ℓu) (hD : 0 ≤ D)
    (hlog4 : 4 ≤ Real.log W)
    (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    residual W L ℓu ηu D J r C N ζ /
        nearRate W ℓu ηu D r d ≤
      4 * C * W ^ (11 + 2 * ζ - D) := by
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hW0 : 0 < W := (Real.exp_pos 1).trans_le hW
  have hN0 : 0 ≤ N := by linarith
  have hℓ0 : 0 < ℓu := by linarith
  have hNpow : N ^ (5 + ζ) ≤ W ^ (10 + 2 * ζ) := by
    calc
      N ^ (5 + ζ) ≤ (W ^ 2) ^ (5 + ζ) :=
        Real.rpow_le_rpow hN0 hNW (by linarith)
      _ = W ^ (10 + 2 * ζ) := by
        rw [show W ^ 2 = W ^ (2 : ℝ) by norm_cast]
        rw [← Real.rpow_mul hW0.le]
        congr 1
        ring
  have hTF := gap_tail_le_two_floor hW hℓ0 hηu hA1 hD hlog4 hlog
  have hExp := exp_subpow_le_W hW0 (by linarith : 1 ≤ Real.log W)
  calc
    residual W L ℓu ηu D J r C N ζ /
        nearRate W ℓu ηu D r d ≤
      2 * C * N ^ (5 + ζ) *
        Real.exp (Real.log W ^ (3 / 4 : ℝ)) *
          tailT W ℓu ηu D (gap W ℓu) :=
      residual_ratio_le_N hW1 hℓu hηu hr hN hL0 hJ0 hC
        hL hJ hA hη hnear
    _ ≤ 2 * C * W ^ (10 + 2 * ζ) * W * (2 * W ^ (-D)) := by
      gcongr
      exact (tailT_pos hW0 _).le
    _ = 4 * C * W ^ (11 + 2 * ζ - D) := by
      have hpow : W ^ (10 + 2 * ζ) * W * W ^ (-D) =
          W ^ (11 + 2 * ζ - D) := by
        have hbase : W ^ (10 + 2 * ζ) * W =
            W ^ ((10 + 2 * ζ) + 1) := by
          simpa only [Real.rpow_one] using
            (Real.rpow_add hW0 (10 + 2 * ζ) 1).symm
        calc
          W ^ (10 + 2 * ζ) * W * W ^ (-D) =
              W ^ ((10 + 2 * ζ) + 1) * W ^ (-D) := by rw [hbase]
          _ = W ^ (((10 + 2 * ζ) + 1) + (-D)) :=
                (Real.rpow_add hW0 _ _).symm
          _ = W ^ (11 + 2 * ζ - D) := by congr 1; ring
      calc
        2 * C * W ^ (10 + 2 * ζ) * W * (2 * W ^ (-D)) =
            4 * C * (W ^ (10 + 2 * ζ) * W * W ^ (-D)) := by ring
        _ = 4 * C * W ^ (11 + 2 * ζ - D) := by rw [hpow]

theorem residual_ratio_le_invW {W L ℓu ηu J r C N ζ d : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J) (hC : 0 ≤ C)
    (hL : L ≤ N) (hJ : J ≤ N)
    (hA1 : 1 ≤ W * ℓu * ηu) (hA : W * ℓu * ηu ≤ N)
    (hη : ηu⁻¹ ≤ N) (hNW : N ≤ W ^ 2)
    (hnear : d ≤ ellStar W ℓu) (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log W)
    (hCcap : 4 * C ≤ W) :
    residual W L ℓu ηu 60 J r C N ζ /
        nearRate W ℓu ηu 60 r d ≤ W⁻¹ := by
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hW0 : 0 < W := (Real.exp_pos 1).trans_le hW
  have hlog4 : 4 ≤ Real.log W := by linarith
  have hbound := residual_ratio_le_W hW hℓu hηu hr hN hζ0
    hL0 hJ0 hC hL hJ hA1 hA hη hNW hnear
    (by norm_num : (0 : ℝ) ≤ 60) hlog4 hlog
  have hpow : W ^ (11 + 2 * ζ - (60 : ℝ)) ≤ W ^ (-47 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hpow_eq : W * W ^ (-47 : ℝ) = W ^ (-46 : ℝ) := by
    have h := Real.rpow_add hW0 (1 : ℝ) (-47 : ℝ)
    norm_num at h ⊢
    exact h.symm
  calc
    residual W L ℓu ηu 60 J r C N ζ /
        nearRate W ℓu ηu 60 r d ≤
      4 * C * W ^ (11 + 2 * ζ - (60 : ℝ)) := hbound
    _ ≤ 4 * C * W ^ (-47 : ℝ) := by gcongr
    _ ≤ W * W ^ (-47 : ℝ) :=
      mul_le_mul_of_nonneg_right hCcap (Real.rpow_nonneg hW0.le _)
    _ = W ^ (-46 : ℝ) := hpow_eq
    _ ≤ W⁻¹ := by
      simpa only [Real.rpow_neg_one] using
        (Real.rpow_le_rpow_of_exponent_le hW1
          (by norm_num : (-46 : ℝ) ≤ -1))

/-- The local scalar absorption retains the near indicator. -/
theorem residual_indicator_le_invW {W L ℓu ηu J r C N ζ d : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J) (hC : 0 ≤ C)
    (hL : L ≤ N) (hJ : J ≤ N)
    (hA1 : 1 ≤ W * ℓu * ηu) (hA : W * ℓu * ηu ≤ N)
    (hη : ηu⁻¹ ≤ N) (hNW : N ≤ W ^ 2)
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log W)
    (hCcap : 4 * C ≤ W) :
    residual W L ℓu ηu 60 J r C N ζ *
        (if d ≤ ellStar W ℓu then 1 else 0) ≤
      W⁻¹ * nearRate W ℓu ηu 60 r d *
        (if d ≤ ellStar W ℓu then 1 else 0) := by
  by_cases hd : d ≤ ellStar W ℓu
  · simp only [if_pos hd, mul_one]
    have hW0 : 0 < W := (Real.exp_pos 1).trans_le hW
    have hRate : 0 < nearRate W ℓu ηu 60 r d := by
      unfold nearRate
      have ht : 0 < tailT W ℓu ηu 60 d := tailT_pos hW0 d
      positivity
    exact (div_le_iff₀ hRate).mp
      (residual_ratio_le_invW hW hℓu hηu hr hN hζ0 hζ1
        hL0 hJ0 hC hL hJ hA1 hA hη hNW hd hlog hCcap)
  · simp only [if_neg hd, mul_zero]
    exact le_rfl

/-- A pointwise near/far loop bound passes through the deterministic numerical
absorption without dropping its near indicator. -/
theorem local_loop_indicator_absorb {W L ℓu ηu J r C N ζ d x : ℝ}
    (hx : x * (if d ≤ ellStar W ℓu then 1 else 0) ≤
      (ηu⁻¹ * J * tailT W ℓu ηu 60 (gap W ℓu)) *
        (if d ≤ ellStar W ℓu then 1 else 0))
    (hW : Real.exp 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J) (hC : 0 ≤ C)
    (hL : L ≤ N) (hJ : J ≤ N)
    (hA1 : 1 ≤ W * ℓu * ηu) (hA : W * ℓu * ηu ≤ N)
    (hη : ηu⁻¹ ≤ N) (hNW : N ≤ W ^ 2)
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log W)
    (hCcap : 4 * C ≤ W) :
    (2 * C * N ^ ζ * (r * L / (ℓu * ηu))) *
        (x * (if d ≤ ellStar W ℓu then 1 else 0)) ≤
      W⁻¹ * nearRate W ℓu ηu 60 r d *
        (if d ≤ ellStar W ℓu then 1 else 0) := by
  have hfac : 0 ≤ 2 * C * N ^ ζ * (r * L / (ℓu * ηu)) := by
    have hℓ0 : 0 < ℓu := by linarith
    positivity
  calc
    (2 * C * N ^ ζ * (r * L / (ℓu * ηu))) *
        (x * (if d ≤ ellStar W ℓu then 1 else 0)) ≤
      (2 * C * N ^ ζ * (r * L / (ℓu * ηu))) *
        ((ηu⁻¹ * J * tailT W ℓu ηu 60 (gap W ℓu)) *
          (if d ≤ ellStar W ℓu then 1 else 0)) :=
      mul_le_mul_of_nonneg_left hx hfac
    _ = residual W L ℓu ηu 60 J r C N ζ *
        (if d ≤ ellStar W ℓu then 1 else 0) := by
      unfold residual
      ring
    _ ≤ W⁻¹ * nearRate W ℓu ηu 60 r d *
        (if d ≤ ellStar W ℓu then 1 else 0) :=
      residual_indicator_le_invW hW hℓu hηu hr hN hζ0 hζ1
        hL0 hJ0 hC hL hJ hA1 hA hη hNW hlog hCcap

/-- Application to the actual Gaussian three-loop term from T350.  Every
numerical cap is an explicit hypothesis, including the actual `jG` cap. -/
theorem gaussian_local_loop_indicator_absorb (gd : Gauss.Dims)
    {E : ℝ} (hE : |E| < 2) (n : ℕ) {u : ℝ} (hu : u < 1)
    (ω : Gauss.Ω gd) {ℓu r C M ζ : ℝ}
    (hW : Real.exp 1 ≤ (gd.W n : ℝ))
    (hℓu : 1 ≤ ℓu) (hηu : 0 < etaT E u)
    (hr : 1 ≤ r) (hM : 1 ≤ M) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hC : 0 ≤ C)
    (hL : (gd.L n : ℝ) ≤ M)
    (hJ : APrimeJG.jG (Gauss.sample gd) E n u ω ℓu (etaT E u) 60 ≤ M)
    (hA1 : 1 ≤ (gd.W n : ℝ) * ℓu * etaT E u)
    (hA : (gd.W n : ℝ) * ℓu * etaT E u ≤ M)
    (hη : (etaT E u)⁻¹ ≤ M) (hMW : M ≤ (gd.W n : ℝ) ^ 2)
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log (gd.W n : ℝ))
    (hCcap : 4 * C ≤ (gd.W n : ℝ))
    (a₁ a₂ b : ZMod (gd.L n))
    (hb : Lemma57.ellStarStar (gd.W n : ℝ) ℓu <
      (zdist (gd.L n) (a₂ - b) : ℝ)) :
    (2 * C * M ^ ζ * (r * (gd.L n : ℝ) / (ℓu * etaT E u))) *
        (‖gloop (gd.L n) (gd.W n) ((Gauss.sample gd).H n u ω) (zt E u)
          ⟨[false, true, true], [a₂, b, a₁]⟩‖ *
          (if (zdist (gd.L n) (a₂ - a₁) : ℝ) ≤
            ellStar (gd.W n : ℝ) ℓu then (1 : ℝ) else 0)) ≤
      (gd.W n : ℝ)⁻¹ *
        nearRate (gd.W n : ℝ) ℓu (etaT E u) 60 r
          (zdist (gd.L n) (a₂ - a₁) : ℝ) *
        (if (zdist (gd.L n) (a₂ - a₁) : ℝ) ≤
          ellStar (gd.W n : ℝ) ℓu then (1 : ℝ) else 0) := by
  have hW0 : 0 < (gd.W n : ℝ) := (Real.exp_pos 1).trans_le hW
  have hlog4 : 4 ≤ Real.log (gd.W n : ℝ) := by linarith
  have hJ0 : 0 ≤ APrimeJG.jG (Gauss.sample gd) E n u ω ℓu (etaT E u) 60 :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (APrimeJG.one_le_jG (Gauss.sample gd) E n u ω
        (ℓu := ℓu) (ηu := etaT E u) (D := 60) hW0)
  have hx := APrimeDriftNearTriple.gaussian_three_near_far_indicator_le
    gd hE n hu ω (D := 60) (by linarith : 0 < ℓu) hlog4 a₁ a₂ b hb
  exact local_loop_indicator_absorb (by simpa only [gap] using hx)
    hW hℓu hηu hr hM hζ0 hζ1 (Nat.cast_nonneg _) hJ0 hC
    hL hJ hA1 hA hη hMW hlog hCcap

/-- Strict first-cell geometry with positive source multiplier, block cap and
far tail.  The parameters satisfy the full deterministic absorption budget. -/
theorem first_cell_nondegenerate_witness :
    let W : ℝ := Real.exp 57600
    let M : ℝ := W ^ 2
    let η : ℝ := W⁻¹
    gridT W 1 (1 / 2) 0 = 0 ∧
      0 < gridT W 1 (1 / 2) 1 ∧
      0 < (1 : ℝ) ∧
      0 < tailT W 1 η 60 (gap W 1) ∧
      0 < residual W 1 1 η 60 1 1 1 M 0 ∧
      residual W 1 1 η 60 1 1 1 M 0 *
        (if (0 : ℝ) ≤ ellStar W 1 then 1 else 0) ≤
        W⁻¹ * nearRate W 1 η 60 1 0 *
          (if (0 : ℝ) ≤ ellStar W 1 then 1 else 0) := by
  let W : ℝ := Real.exp 57600
  let M : ℝ := W ^ 2
  let η : ℝ := W⁻¹
  have hW0 : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp (by norm_num)
  have hW4 : 4 ≤ W := by
    have h := Real.add_one_le_exp (57600 : ℝ)
    dsimp [W]
    linarith
  have hWexp : Real.exp 1 ≤ W :=
    Real.exp_le_exp.2 (by norm_num : (1 : ℝ) ≤ 57600)
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have hη : 0 < η := inv_pos.mpr hW0
  have hA : W * (1 : ℝ) * η = 1 := by
    dsimp [η]
    field_simp
  have hηinv : η⁻¹ = W := by dsimp [η]; simp
  have hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log W := by
    dsimp [W]
    rw [Real.log_exp]
    norm_num
  have htail : 0 < tailT W 1 η 60 (gap W 1) := tailT_pos hW0 _
  have hres : 0 < residual W 1 1 η 60 1 1 1 M 0 := by
    unfold residual
    have hM0 : 0 < M := by linarith
    positivity
  have hgrid0 : gridT W 1 (1 / 2) 0 = 0 := gridT_zero (by norm_num)
  have hgrid1 : 0 < gridT W 1 (1 / 2) 1 := by
    have hp : W ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1 < W) (by norm_num)
    unfold gridT gridS
    simp only [Nat.cast_one, one_mul]
    exact lt_min (sub_pos.mpr hp) (by norm_num)
  refine ⟨hgrid0, hgrid1, by norm_num, htail, hres, ?_⟩
  exact residual_indicator_le_invW hWexp (by norm_num) hη
    (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith [sq_nonneg (W - 1)]) (by nlinarith [sq_nonneg (W - 1)])
    (by rw [hA]) (by rw [hA]; exact hM)
    (by rw [hηinv]; nlinarith [sq_nonneg (W - 1)])
    (by rfl) hlog (by simpa only [mul_one] using hW4)

/-- For fixed `C`, the final numerical threshold follows from the growing
bandwidth.  The other scale and block caps remain conditional. -/
theorem eventually_residual_indicator_le_invW {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω)
    (L ℓu ηu J r d : ℕ → ℝ) {C ζ : ℝ}
    (hC : 0 ≤ C) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hbudget : ∀ᶠ n : ℕ in atTop,
      Real.exp 1 ≤ (B.W n : ℝ) ∧
      1 ≤ ℓu n ∧ 0 < ηu n ∧ 1 ≤ r n ∧
      0 ≤ L n ∧ 0 ≤ J n ∧
      L n ≤ (n : ℝ) ∧ J n ≤ (n : ℝ) ∧
      1 ≤ (B.W n : ℝ) * ℓu n * ηu n ∧
      (B.W n : ℝ) * ℓu n * ηu n ≤ (n : ℝ) ∧
      (ηu n)⁻¹ ≤ (n : ℝ) ∧
      (4 * (60 : ℝ)) ^ 2 ≤ Real.log (B.W n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      residual (B.W n : ℝ) (L n) (ℓu n) (ηu n) 60
          (J n) (r n) C n ζ *
          (if d n ≤ ellStar (B.W n : ℝ) (ℓu n) then 1 else 0) ≤
        (B.W n : ℝ)⁻¹ *
          nearRate (B.W n : ℝ) (ℓu n) (ηu n) 60 (r n) (d n) *
          (if d n ≤ ellStar (B.W n : ℝ) (ℓu n) then 1 else 0) := by
  filter_upwards [hbudget, Step2.eventually_le_W_sq B,
      (Step2.tendsto_W B).eventually_ge_atTop (4 * C),
      Filter.eventually_ge_atTop 1] with n hb hNW hCcap hn
  rcases hb with ⟨hW, hℓu, hηu, hr, hL0, hJ0,
    hL, hJ, hA1, hA, hη, hlog⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact residual_indicator_le_invW hW hℓu hηu hr hn1 hζ0 hζ1
    hL0 hJ0 hC hL hJ hA1 hA hη hNW hlog hCcap

end RBM.APrimeDriftNearAbsorb

#print axioms RBM.APrimeDriftNearAbsorb.residual_ratio_eq
#print axioms RBM.APrimeDriftNearAbsorb.residual_ratio_le
#print axioms RBM.APrimeDriftNearAbsorb.gap_tail_le_two_floor
#print axioms RBM.APrimeDriftNearAbsorb.exp_subpow_le_W
#print axioms RBM.APrimeDriftNearAbsorb.cap_coefficient_le
#print axioms RBM.APrimeDriftNearAbsorb.residual_ratio_le_N
#print axioms RBM.APrimeDriftNearAbsorb.residual_ratio_le_W
#print axioms RBM.APrimeDriftNearAbsorb.residual_ratio_le_invW
#print axioms RBM.APrimeDriftNearAbsorb.residual_indicator_le_invW
#print axioms RBM.APrimeDriftNearAbsorb.local_loop_indicator_absorb
#print axioms RBM.APrimeDriftNearAbsorb.gaussian_local_loop_indicator_absorb
#print axioms RBM.APrimeDriftNearAbsorb.first_cell_nondegenerate_witness
#print axioms RBM.APrimeDriftNearAbsorb.eventually_residual_indicator_le_invW
