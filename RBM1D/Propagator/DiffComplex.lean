/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Decay
import RBM1D.Propagator.RateComplex
import RBM1D.Propagator.Edges

/-!
# The difference estimates (2.53)--(2.54) for complex spectral parameter

`Propagator/Decay.lean` proves (2.53) and (2.54) for real `xi = t`.  The identities they
rest on -- the closed form, `kern_succ_sub`, `kern_second_diff` and the two-sided
`norm_Theta_sub_shift_le_two_mul` -- hold for every `xi`; only the *bounds* on
`A(1-rho)` and `A(1-rho)^2` were stated for real `xi`.  This file supplies the complex
versions, so the difference estimates hold on the whole disc.

The ingredients are the exact identity `‖1-rho‖^2 = ‖1-xi‖ * ‖1+rho+rho^2‖`
(`norm_one_sub_rho_sq_eq`) with `‖1+rho+rho^2‖ ≤ 3`, and the lower bound
`‖1+rho‖ ≥ 1/2` proved here.
-/

namespace RBM

section OneAddRho

variable {ξ : ℂ}

/-- `(1+rho)^2 * xi = rho * (3+xi)`: the characteristic relation, rearranged. -/
theorem one_add_rho_sq_mul (hξ0 : ξ ≠ 0) :
    (1 + rho ξ) ^ 2 * ξ = rho ξ * (3 + ξ) := by
  linear_combination xi_mul_poly hξ0

/-- **`‖1 + rho‖ ≥ 1/2`.**  The root can never approach `-1` on the unit disc: that would
force `xi` towards `-3`.  Quantitatively `‖1+rho‖^2 ‖xi‖ = ‖rho‖ ‖3+xi‖ ≥ 2‖rho‖`, which
handles large `‖rho‖`, while small `‖rho‖` is handled by the triangle inequality. -/
theorem half_le_norm_one_add_rho (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) : 1 / 2 ≤ ‖1 + rho ξ‖ := by
  have hnorm : ‖1 + rho ξ‖ ^ 2 * ‖ξ‖ = ‖rho ξ‖ * ‖3 + ξ‖ := by
    have h := congrArg (‖·‖) (one_add_rho_sq_mul hξ0)
    simpa [norm_mul, norm_pow] using h
  have h3 : 2 < ‖3 + ξ‖ := by
    have h := norm_sub_le ((3 : ℂ) + ξ) ξ
    simp only [add_sub_cancel_right] at h
    have h3' : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3'] at h
    linarith
  rcases le_total (‖rho ξ‖) (1 / 4) with hsmall | hbig
  · have h := norm_sub_le ((1 : ℂ) + rho ξ) (rho ξ)
    simp only [add_sub_cancel_right, norm_one] at h
    linarith
  · have hpos : (0 : ℝ) ≤ ‖1 + rho ξ‖ := norm_nonneg _
    have hxi0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
    have hkey : 1 / 2 ≤ ‖1 + rho ξ‖ ^ 2 := by
      have h1 : ‖rho ξ‖ * ‖3 + ξ‖ ≥ (1 / 4) * 2 := by nlinarith [norm_nonneg (rho ξ)]
      nlinarith [hnorm, hxi0, hξ, h1]
    nlinarith [hkey, hpos]

end OneAddRho

section ComplexConstants

variable (L : ℕ) {ξ : ℂ}

/-- `‖1 - rho‖^2 ≤ 3 ‖1 - xi‖`, from the exact identity and `‖1+rho+rho^2‖ ≤ 3`. -/
theorem norm_one_sub_rho_sq_le_three (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖1 - rho ξ‖ ^ 2 ≤ 3 * ‖1 - ξ‖ := by
  rw [norm_one_sub_rho_sq_eq hξ0]
  have h := norm_one_add_rho_add_sq_le hξ0 hξ
  nlinarith [norm_nonneg (1 - ξ), norm_nonneg (1 + rho ξ + rho ξ ^ 2)]

/-- **One lattice difference, complex `xi`**: `‖A(1-rho)‖ ≤ 6/(1 - ‖rho‖^L)`. -/
theorem norm_AA_mul_one_sub_rho_le_complex (hL : L ≠ 0) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖AA L ξ * (1 - rho ξ)‖ ≤ 6 / (1 - ‖rho ξ‖ ^ L) := by
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hr0 : (0 : ℝ) ≤ ‖rho ξ‖ := norm_nonneg _
  have hpowlt : ‖rho ξ‖ ^ L < 1 := pow_lt_one₀ hr0 hnr hL
  have hden : (0 : ℝ) < 1 - ‖rho ξ‖ ^ L := by linarith
  have hxi1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have hD : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hxi1
  have hρL : (1 : ℂ) - rho ξ ^ L ≠ 0 := by
    intro h
    have : rho ξ ^ L = 1 := by linear_combination -h
    rw [← norm_pow, this, norm_one] at hpowlt
    exact absurd hpowlt (lt_irrefl 1)
  have hPL : 0 < ‖1 - rho ξ ^ L‖ := norm_pos_iff.mpr hρL
  have hhalf : 1 / 2 ≤ ‖1 + rho ξ‖ := half_le_norm_one_add_rho hξ0 hξ
  have hPos : 0 < ‖1 + rho ξ‖ := by linarith
  have hlow : 1 - ‖rho ξ‖ ^ L ≤ ‖1 - rho ξ ^ L‖ := by
    have h := norm_add_le ((1 : ℂ) - rho ξ ^ L) (rho ξ ^ L)
    have h2 : (1 : ℂ) - rho ξ ^ L + rho ξ ^ L = 1 := by ring
    rw [h2, norm_one, norm_pow] at h
    linarith
  have hA : AA L ξ * (1 - rho ξ)
      = (1 - rho ξ) ^ 2 / ((1 - ξ) * (1 - rho ξ ^ L) * (1 + rho ξ)) := by
    rw [AA_eq hL hξ0 hξ]; ring
  rw [hA, norm_div, norm_mul, norm_mul, norm_pow]
  rw [div_le_div_iff₀ (by positivity) hden]
  have hnum : ‖1 - rho ξ‖ ^ 2 ≤ 3 * ‖1 - ξ‖ := norm_one_sub_rho_sq_le_three hξ0 hξ
  calc ‖1 - rho ξ‖ ^ 2 * (1 - ‖rho ξ‖ ^ L)
      ≤ 3 * ‖1 - ξ‖ * (1 - ‖rho ξ‖ ^ L) := mul_le_mul_of_nonneg_right hnum hden.le
    _ ≤ 3 * ‖1 - ξ‖ * ‖1 - rho ξ ^ L‖ := mul_le_mul_of_nonneg_left hlow (by positivity)
    _ ≤ 6 * (‖1 - ξ‖ * ‖1 - rho ξ ^ L‖ * ‖1 + rho ξ‖) := by
        have hfac : (0 : ℝ) ≤ 3 * ‖1 - ξ‖ * ‖1 - rho ξ ^ L‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hhalf hfac]

end ComplexConstants

section Assemble

variable (L : ℕ) [NeZero L] {ξ : ℂ}

/-- **The decay length against the geometric factor.**
`ℓ̂(ξ) · ‖1-ξ‖^{1/2} ≤ 12 (1 - ‖ρ‖^L)`.

Both regimes of the `min` in `ℓ̂` are used, exactly as in the real case: when
`ℓ̂ = ‖1-ξ‖^{-1/2}` the left side is `1` and `L(1-‖ρ‖) ≳ 1`; when `ℓ̂ = L` the left side
is `L‖1-ξ‖^{1/2}` and `L(1-‖ρ‖)` is comparable to it and bounded. -/
theorem ellHat_mul_sqrt_le (hL3 : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ellHat L ξ * Real.sqrt ‖1 - ξ‖ ≤ 12 * (1 - ‖rho ξ‖ ^ L) := by
  obtain ⟨hlow, hhigh⟩ := rho_complex_bounds hξ0 hξ
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hr0 : (0 : ℝ) ≤ ‖rho ξ‖ := norm_nonneg _
  have hxi1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have hD : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hxi1
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.mpr hD
  have hs8 : Real.sqrt (‖1 - ξ‖ / 8) * 3 ≥ Real.sqrt ‖1 - ξ‖ := by
    have h8 : Real.sqrt ‖1 - ξ‖ = Real.sqrt 8 * Real.sqrt (‖1 - ξ‖ / 8) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
      congr 1
      field_simp
    have hs8' : Real.sqrt 8 ≤ 3 := by
      have : Real.sqrt 8 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
      have h9 : Real.sqrt 9 = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith [this, h9.le, h9.ge]
    nlinarith [h8, Real.sqrt_nonneg (‖1 - ξ‖ / 8), hs8']
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    have : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [this, h4.le, h4.ge]
  have hLr : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by omega
    exact_mod_cast this
  -- `y := L (1 - ‖ρ‖)` and the geometric bound
  have hy0 : (0 : ℝ) ≤ (L : ℝ) * (1 - ‖rho ξ‖) := by
    have : (0 : ℝ) ≤ 1 - ‖rho ξ‖ := by linarith
    positivity
  have hgeom := le_one_sub_pow (r := ‖rho ξ‖) hr0 hnr.le L
  have hprod : (L : ℝ) * (1 - ‖rho ξ‖)
      ≤ (1 - ‖rho ξ‖ ^ L) * (1 + (L : ℝ) * (1 - ‖rho ξ‖)) := by
    rw [div_le_iff₀ (by linarith)] at hgeom
    linarith
  have hu1 : ‖rho ξ‖ ^ L ≤ 1 := pow_le_one₀ hr0 hnr.le
  -- lower bound `y ≥ L √‖1-ξ‖ / 3`
  have hylow : (L : ℝ) * Real.sqrt ‖1 - ξ‖ / 3 ≤ (L : ℝ) * (1 - ‖rho ξ‖) := by
    have h1 : Real.sqrt ‖1 - ξ‖ / 3 ≤ 1 - ‖rho ξ‖ := by
      have := hlow
      linarith [hs8]
    nlinarith [h1, hLr]
  rcases le_total (1 / Real.sqrt ‖1 - ξ‖) ((L : ℝ)) with hcase | hcase
  · -- `ℓ̂ = ‖1-ξ‖^{-1/2}`
    have hell : ellHat L ξ = 1 / Real.sqrt ‖1 - ξ‖ := by
      rw [ellHat, min_eq_left hcase]
    rw [hell]
    have hone : 1 / Real.sqrt ‖1 - ξ‖ * Real.sqrt ‖1 - ξ‖ = 1 := by field_simp
    rw [hone]
    have hLs : 1 ≤ (L : ℝ) * Real.sqrt ‖1 - ξ‖ := by
      rw [div_le_iff₀ hs] at hcase
      linarith
    have hy3 : (1 : ℝ) / 3 ≤ (L : ℝ) * (1 - ‖rho ξ‖) := by linarith [hylow, hLs]
    nlinarith [hprod, hy3, hu1]
  · -- `ℓ̂ = L`
    have hell : ellHat L ξ = (L : ℝ) := by
      rw [ellHat, min_eq_right hcase]
    rw [hell]
    have hLs : (L : ℝ) * Real.sqrt ‖1 - ξ‖ ≤ 1 := by
      rw [le_div_iff₀ hs] at hcase
      linarith
    have hyup : (L : ℝ) * (1 - ‖rho ξ‖) ≤ 2 := by
      have h1 : 1 - ‖rho ξ‖ ≤ 2 * Real.sqrt ‖1 - ξ‖ := by
        nlinarith [hhigh, hsqrt3, Real.sqrt_nonneg ‖1 - ξ‖]
      nlinarith [h1, hLs, hLr]
    nlinarith [hprod, hylow, hyup, hu1, hs.le, hLr]

/-- **(2.53) for complex `ξ`**:
`|(Θ_ξ)_{x,y} - (Θ_ξ)_{x,y+1}| ≤ 144 / (ℓ̂(ξ) ‖1-ξ‖^{1/2})`. -/
theorem norm_Theta_sub_shift_le_complex (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1)
    (x y : ZMod L) :
    ‖Theta L ξ x y - Theta L ξ x (y + 1)‖
      ≤ 144 / (ellHat L ξ * Real.sqrt ‖1 - ξ‖) := by
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hr0 : (0 : ℝ) ≤ ‖rho ξ‖ := norm_nonneg _
  have hL0 : L ≠ 0 := by omega
  have hpowlt : ‖rho ξ‖ ^ L < 1 := pow_lt_one₀ hr0 hnr hL0
  have hden : (0 : ℝ) < 1 - ‖rho ξ‖ ^ L := by linarith
  have hxi1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have hD : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hxi1
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.mpr hD
  have hellpos : 0 < ellHat L ξ := by
    have := half_le_ellHat L hL hξ
    linarith
  have h1 := norm_Theta_sub_shift_le_two_mul L hL hξ0 hξ x y
  have h2 := norm_AA_mul_one_sub_rho_le_complex L hL0 hξ0 hξ
  have hstep : ‖Theta L ξ x y - Theta L ξ x (y + 1)‖ ≤ 12 / (1 - ‖rho ξ‖ ^ L) := by
    have : 2 * ‖AA L ξ * (1 - rho ξ)‖ ≤ 2 * (6 / (1 - ‖rho ξ‖ ^ L)) := by linarith
    have heq : (12 : ℝ) / (1 - ‖rho ξ‖ ^ L) = 2 * (6 / (1 - ‖rho ξ‖ ^ L)) := by ring
    rw [heq]
    linarith
  refine hstep.trans ?_
  rw [div_le_div_iff₀ hden (by positivity)]
  have hkey := ellHat_mul_sqrt_le L hL hξ0 hξ
  nlinarith [hkey, hden]

/-- **(2.53) on the whole disc, `ξ = 0` included.**  The `ρ`-machinery needs `ξ ≠ 0`; at
`ξ = 0` the propagator is the identity, `ℓ̂(0) = 1` and `‖1-0‖ = 1`, so the bound reads
`1 ≤ 144`. -/
theorem norm_Theta_sub_shift_le_complex' (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    ‖Theta L ξ x y - Theta L ξ x (y + 1)‖
      ≤ 144 / (ellHat L ξ * Real.sqrt ‖1 - ξ‖) := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · rw [ellHat_zero L hL, sub_zero, norm_one, Real.sqrt_one, mul_one]
    exact (norm_Theta_zero_sub_shift_le L hL x y).trans (by norm_num)
  · exact norm_Theta_sub_shift_le_complex L hL hξ0 hξ x y

end Assemble

section SecondDiffComplex

variable (L : ℕ) [NeZero L] {ξ : ℂ}

theorem norm_one_sub_rho_le_sqrt (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖1 - rho ξ‖ ≤ Real.sqrt 3 * Real.sqrt ‖1 - ξ‖ := by
  have h2 := norm_one_sub_rho_sq_le_three hξ0 hξ
  have h := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)] at h
  exact h

/-- **Two lattice differences, complex `ξ`**: `‖A(1-ρ)²‖ ≤ 144/ℓ̂(ξ)`.
The extra factor `‖1-ρ‖ ≤ √3‖1-ξ‖^{1/2}` cancels the `‖1-ξ‖^{1/2}` that
`ellHat_mul_sqrt_le` leaves behind, so the `‖1-ξ‖` disappears entirely --- exactly as in
the real case, and this is why (2.54) has no `|1-ξ|` on its right-hand side. -/
theorem norm_AA_mul_one_sub_rho_sq_le_complex (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖AA L ξ * (1 - rho ξ) ^ 2‖ ≤ 144 / ellHat L ξ := by
  have hL0 : L ≠ 0 := by omega
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hr0 : (0 : ℝ) ≤ ‖rho ξ‖ := norm_nonneg _
  have hpowlt : ‖rho ξ‖ ^ L < 1 := pow_lt_one₀ hr0 hnr hL0
  have hden : (0 : ℝ) < 1 - ‖rho ξ‖ ^ L := by linarith
  have hxi1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have hD : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hxi1
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.mpr hD
  have hellpos : 0 < ellHat L ξ := by
    have := half_le_ellHat L hL hξ
    linarith
  have h1 := norm_AA_mul_one_sub_rho_le_complex L hL0 hξ0 hξ
  have h2 := norm_one_sub_rho_le_sqrt hξ0 hξ
  have hkey := ellHat_mul_sqrt_le L hL hξ0 hξ
  have hsplit : ‖AA L ξ * (1 - rho ξ) ^ 2‖ = ‖AA L ξ * (1 - rho ξ)‖ * ‖1 - rho ξ‖ := by
    rw [← norm_mul]
    congr 1
    ring
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (3:ℝ) ≤ 4)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h, h4.le, h4.ge]
  rw [hsplit]
  -- `‖A(1-ρ)‖ ‖1-ρ‖ ≤ (6/(1-‖ρ‖^L)) (2 √‖1-ξ‖)`
  have hstep : ‖AA L ξ * (1 - rho ξ)‖ * ‖1 - rho ξ‖
      ≤ 6 / (1 - ‖rho ξ‖ ^ L) * (2 * Real.sqrt ‖1 - ξ‖) := by
    have hb : ‖1 - rho ξ‖ ≤ 2 * Real.sqrt ‖1 - ξ‖ := by
      nlinarith [h2, hsqrt3, hs.le]
    have hA0 : (0 : ℝ) ≤ ‖AA L ξ * (1 - rho ξ)‖ := norm_nonneg _
    have hc0 : (0 : ℝ) ≤ 6 / (1 - ‖rho ξ‖ ^ L) := by positivity
    exact mul_le_mul h1 hb (norm_nonneg _) hc0
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hellpos]
  nlinarith [hkey, hs.le, hellpos, hden]

/-- **(2.54) with the decay retained, complex `ξ`**:
`‖2Θ_{x,y} - Θ_{x,y+1} - Θ_{x,y-1}‖ ≤ 288 ‖ρ‖^{‖x-y‖-1} / ℓ̂(ξ)`. -/
theorem norm_Theta_second_diff_le_complex (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1)
    {x y : ZMod L} (hxy : x ≠ y) :
    ‖2 * Theta L ξ x y - Theta L ξ x (y + 1) - Theta L ξ x (y - 1)‖
      ≤ 288 * ‖rho ξ‖ ^ (zdist L (x - y) - 1) / ellHat L ξ := by
  have hellpos : 0 < ellHat L ξ := by
    have := half_le_ellHat L hL hξ
    linarith
  have h1 := norm_Theta_second_diff_le_pow L hL hξ0 hξ hxy
  have h2 := norm_AA_mul_one_sub_rho_sq_le_complex L hL hξ0 hξ
  have hp : (0 : ℝ) ≤ ‖rho ξ‖ ^ (zdist L (x - y) - 1) := by positivity
  refine h1.trans ?_
  have : 2 * ‖AA L ξ * (1 - rho ξ) ^ 2‖ ≤ 2 * (144 / ellHat L ξ) := by linarith
  calc 2 * ‖AA L ξ * (1 - rho ξ) ^ 2‖ * ‖rho ξ‖ ^ (zdist L (x - y) - 1)
      ≤ 2 * (144 / ellHat L ξ) * ‖rho ξ‖ ^ (zdist L (x - y) - 1) :=
        mul_le_mul_of_nonneg_right this hp
    _ = 288 * ‖rho ξ‖ ^ (zdist L (x - y) - 1) / ellHat L ξ := by
        field_simp
        ring

/-- **(2.54) with the decay retained, on the whole disc, `ξ = 0` included.**  At `ξ = 0` the
propagator is the identity: for `‖x-y‖ ≥ 2` all three entries vanish, and for `‖x-y‖ = 1` the
decay factor is `‖ρ‖^0 = 1` and the bound reads `1 ≤ 288`. -/
theorem norm_Theta_second_diff_le_complex' (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
    {x y : ZMod L} (hxy : x ≠ y) :
    ‖2 * Theta L ξ x y - Theta L ξ x (y + 1) - Theta L ξ x (y - 1)‖
      ≤ 288 * ‖rho ξ‖ ^ (zdist L (x - y) - 1) / ellHat L ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · rw [ellHat_zero L hL]
    rcases lt_or_ge (zdist L (x - y)) 2 with hsmall | hbig
    · have hd : zdist L (x - y) - 1 = 0 := by omega
      rw [hd, pow_zero]
      exact (norm_Theta_zero_second_diff_le L hL hxy).trans (by norm_num)
    · have hx1 : x ≠ y + 1 := by
        rintro rfl
        have h1 : y + 1 - y = 1 := by ring
        have := zdist_one_le L hL
        rw [← h1] at this; omega
      have hx2 : x ≠ y - 1 := by
        rintro rfl
        have h1 : y - 1 - y = -1 := by ring
        have := zdist_neg_one_le L hL
        rw [← h1] at this; omega
      simp only [Theta_zero, Matrix.one_apply, if_neg hxy, if_neg hx1, if_neg hx2]
      norm_num
  · exact norm_Theta_second_diff_le_complex L hL hξ0 hξ hxy


/-- **(2.54) in the paper's form, complex `ξ`**:
`‖2Θ_{x,y} - Θ_{x,y+1} - Θ_{x,y-1}‖ ≤ 1728/(‖x-y‖+1)` for `x ≠ y`.
As in the real case the decay factor is what makes this follow; a bound of size `1/ℓ̂`
alone would not. -/
theorem norm_Theta_second_diff_le_inv_dist_complex (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1)
    {x y : ZMod L} (hxy : x ≠ y) :
    ‖2 * Theta L ξ x y - Theta L ξ x (y + 1) - Theta L ξ x (y - 1)‖
      ≤ 1728 / ((zdist L (x - y) : ℝ) + 1) := by
  obtain ⟨hlow, hhigh⟩ := rho_complex_bounds hξ0 hξ
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hr0 : (0 : ℝ) ≤ ‖rho ξ‖ := norm_nonneg _
  have hlam : 0 < 1 - ‖rho ξ‖ := by linarith
  have hxi1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have hD : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hxi1
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.mpr hD
  have hell : 1 / 2 ≤ ellHat L ξ := half_le_ellHat L hL hξ
  have hellpos : 0 < ellHat L ξ := by linarith
  -- `x ≠ y` gives `dist ≥ 1`
  have hd1 : 1 ≤ zdist L (x - y) := by
    rcases Nat.eq_zero_or_pos (zdist L (x - y)) with h0 | hpos
    · exfalso
      have hval : (x - y).val = 0 ∨ L - (x - y).val = 0 := by
        rw [zdist] at h0
        rcases min_cases (x - y).val (L - (x - y).val) with ⟨h, _⟩ | ⟨h, _⟩
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hlt : (x - y).val < L := ZMod.val_lt _
      have : (x - y).val = 0 := by omega
      exact hxy (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp this))
    · exact hpos
  have hcast : ((zdist L (x - y) - 1 : ℕ) : ℝ) = (zdist L (x - y) : ℝ) - 1 := by
    have : (1 : ℕ) ≤ zdist L (x - y) := hd1
    push_cast [Nat.cast_sub this]
    ring
  have hpow1 : ‖rho ξ‖ ^ (zdist L (x - y) - 1) ≤ 1 := pow_le_one₀ hr0 hnr.le
  have hpow0 : (0 : ℝ) ≤ ‖rho ξ‖ ^ (zdist L (x - y) - 1) := by positivity
  have hrd : ‖rho ξ‖ ^ (zdist L (x - y) - 1)
      ≤ Real.exp (-(((zdist L (x - y) : ℝ) - 1) * (1 - ‖rho ξ‖))) := by
    have hre : ‖rho ξ‖ ≤ Real.exp (-(1 - ‖rho ξ‖)) := by
      have := Real.add_one_le_exp (-(1 - ‖rho ξ‖)); linarith
    calc ‖rho ξ‖ ^ (zdist L (x - y) - 1)
        ≤ Real.exp (-(1 - ‖rho ξ‖)) ^ (zdist L (x - y) - 1) := pow_le_pow_left₀ hr0 hre _
      _ = Real.exp (((zdist L (x - y) - 1 : ℕ) : ℝ) * -(1 - ‖rho ξ‖)) :=
          (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(((zdist L (x - y) : ℝ) - 1) * (1 - ‖rho ξ‖))) := by rw [hcast]; ring_nf
  have hkey : ((zdist L (x - y) : ℝ) + 1) * ‖rho ξ‖ ^ (zdist L (x - y) - 1)
      ≤ 6 * ellHat L ξ := by
    rcases le_total (1 / Real.sqrt ‖1 - ξ‖) ((L : ℝ)) with hcase | hcase
    · -- `ℓ̂ = ‖1-ξ‖^{-1/2}`; the exponential carries the estimate
      have hellval : ellHat L ξ = 1 / Real.sqrt ‖1 - ξ‖ := by rw [ellHat, min_eq_left hcase]
      have hprod : ellHat L ξ * Real.sqrt ‖1 - ξ‖ = 1 := by
        rw [hellval]; field_simp
      have hsplit : Real.sqrt ‖1 - ξ‖ = Real.sqrt (‖1 - ξ‖ / 8) * Real.sqrt 8 := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp
      have hs8 : Real.sqrt 8 ≤ 3 := by
        have h := Real.sqrt_le_sqrt (by norm_num : (8:ℝ) ≤ 9)
        have h9 : Real.sqrt 9 = 3 := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        linarith [h, h9.le, h9.ge]
      have hsle : Real.sqrt ‖1 - ξ‖ ≤ 3 * (1 - ‖rho ξ‖) := by
        rw [hsplit]
        nlinarith [hlow, hs8, Real.sqrt_nonneg (‖1 - ξ‖ / 8)]
      have hinv : 1 ≤ 3 * ellHat L ξ * (1 - ‖rho ξ‖) := by
        nlinarith [hprod, hsle, hellpos, hs.le]
      -- `(d-1) e^{-(d-1)λ} ≤ e^{-1}/λ ≤ (3/2) ℓ̂` and `2 e^{-…} ≤ 2 ≤ 4 ℓ̂`
      have hu0 : (0 : ℝ) ≤ ((zdist L (x - y) : ℝ) - 1) * (1 - ‖rho ξ‖) := by
        have : (1 : ℝ) ≤ (zdist L (x - y) : ℝ) := by exact_mod_cast hd1
        nlinarith [hlam]
      have hue := mul_exp_neg_le_exp_neg_one hu0
      have he1 := exp_neg_one_le_half
      have hexp0 : (0 : ℝ) < Real.exp (-(((zdist L (x - y) : ℝ) - 1) * (1 - ‖rho ξ‖))) :=
        Real.exp_pos _
      have hexp1 : Real.exp (-(((zdist L (x - y) : ℝ) - 1) * (1 - ‖rho ξ‖))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      nlinarith [hrd, hue, he1, hexp0.le, hexp1, hinv, hellpos, hlam, hpow0]
    · -- `ℓ̂ = L`; the prefactor alone suffices since `dist ≤ L/2`
      have hellval : ellHat L ξ = (L : ℝ) := by rw [ellHat, min_eq_right hcase]
      have hhalf := two_mul_zdist_le L (x - y)
      have hhalf' : 2 * (zdist L (x - y) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hhalf
      have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      rw [hellval]
      nlinarith [hpow1, hpow0, hhalf', hL3]
  have hstep := norm_Theta_second_diff_le_complex L hL hξ0 hξ hxy
  refine hstep.trans ?_
  rw [div_le_div_iff₀ hellpos (by positivity)]
  nlinarith [hkey, hellpos]

/-- **(2.54) in the paper's form, on the whole disc, `ξ = 0` included.**  At `ξ = 0` the
propagator is the identity: the second difference vanishes for `‖x-y‖ ≥ 2`, and for
`‖x-y‖ = 1` the bound reads `1 ≤ 864`. -/
theorem norm_Theta_second_diff_le_inv_dist_complex' (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
    {x y : ZMod L} (hxy : x ≠ y) :
    ‖2 * Theta L ξ x y - Theta L ξ x (y + 1) - Theta L ξ x (y - 1)‖
      ≤ 1728 / ((zdist L (x - y) : ℝ) + 1) := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · rcases lt_or_ge (zdist L (x - y)) 2 with hsmall | hbig
    · have hd1 : (zdist L (x - y) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 hsmall
      refine (norm_Theta_zero_second_diff_le L hL hxy).trans ?_
      rw [le_div_iff₀ (by positivity)]
      linarith
    · have hx1 : x ≠ y + 1 := by
        rintro rfl
        have h1 : y + 1 - y = 1 := by ring
        have := zdist_one_le L hL
        rw [← h1] at this; omega
      have hx2 : x ≠ y - 1 := by
        rintro rfl
        have h1 : y - 1 - y = -1 := by ring
        have := zdist_neg_one_le L hL
        rw [← h1] at this; omega
      simp only [Theta_zero, Matrix.one_apply, if_neg hxy, if_neg hx1, if_neg hx2]
      norm_num
      positivity
  · exact norm_Theta_second_diff_le_inv_dist_complex L hL hξ0 hξ hxy

end SecondDiffComplex

end RBM
