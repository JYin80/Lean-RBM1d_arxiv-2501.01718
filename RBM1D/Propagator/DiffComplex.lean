/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Decay
import RBM1D.Propagator.RateComplex

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
  rcases le_or_lt (‖rho ξ‖) (1 / 4) with hsmall | hbig
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
    have h := norm_sub_le ((1 : ℂ) - rho ξ ^ L) (1 : ℂ)
    have h2 : ‖(1 : ℂ) - rho ξ ^ L - 1‖ = ‖rho ξ‖ ^ L := by
      rw [show (1 : ℂ) - rho ξ ^ L - 1 = -(rho ξ ^ L) from by ring, norm_neg, norm_pow]
    rw [h2, norm_one] at h
    linarith
  have hA : AA L ξ * (1 - rho ξ)
      = (1 - rho ξ) ^ 2 / ((1 - ξ) * (1 - rho ξ ^ L) * (1 + rho ξ)) := by
    rw [AA_eq hL hξ0 hξ]; ring
  rw [hA, norm_div, norm_mul, norm_mul, norm_pow]
  rw [div_le_div_iff₀ (by positivity) hden]
  have hnum : ‖1 - rho ξ‖ ^ 2 ≤ 3 * ‖1 - ξ‖ := norm_one_sub_rho_sq_le_three hξ0 hξ
  nlinarith [hnum, hlow, hhalf, hD, hPL, hden, norm_nonneg (1 - rho ξ)]

end ComplexConstants

end RBM
