/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Decay

/-!
# The decay rate `1 - ‖ρ(ξ)‖` for complex `ξ`

`RBM.rho_real_bounds` gives `√(1-t) ≤ 1 - ρ(t) ≤ √3 √(1-t)` for real `t ∈ (0,1)`.
Here we prove the same two-sided bound, with worse constants, uniformly on the whole
punctured disc `0 < ‖ξ‖ < 1`:

  `‖1 - ξ‖ / 8 ≤ (1 - ‖ρ(ξ)‖)² ≤ 3 ‖1 - ξ‖`.

This covers the short-edge case `ξ = t m²` of the paper as well as the long-edge one,
so the decay length of (2.52) is `‖1 - ξ‖^{-1/2}` for every admissible `ξ`.

## The argument

The upper bound is `1 - ‖ρ‖ ≤ ‖1 - ρ‖` together with `RBM.one_sub_rho_sq`,
`(1 - ρ)² = (1 - ξ)(1 + ρ + ρ²)`, and `‖1 + ρ + ρ²‖ ≤ 3`.

For the lower bound the danger is `ρ` close to the unit circle but far from `1`.
`‖ξ‖ < 1` rules this out: by `RBM.xi_mul_poly` it says `3‖ρ‖ < ‖1 + ρ + ρ²‖`.
With `p = Re ρ`, `r = ‖ρ‖` this is the polynomial inequality `g > 0`, and one has the
exact identity (using `(Im ρ)² = r² - p²`)

  `g = -4 (r - p - (1-r)²)(r + p) + (r² - 4r + 1)(r² + 1 - 2p)`.

For `r ≥ 1/2` the factor `r² - 4r + 1` is negative and `r² + 1 - 2p ≥ (1-r)² ≥ 0`, so
`g > 0` forces `r - p ≤ (1-r)²`, i.e. `ρ` lies in a parabolic region around `1`.
Then `‖1 - ρ‖² = (1-r)² + 2(r - p) ≤ 3(1-r)²`, and dividing by `‖1+ρ+ρ²‖ > 3r ≥ 3/2`
gives `‖1 - ξ‖ ≤ 2(1-r)²`.  For `r < 1/2` simply `‖1 - ξ‖ < 2 < 8(1-r)²`.

## Main results

* `RBM.sq_one_sub_norm_rho_le` : `(1 - ‖ρ‖)² ≤ 3 ‖1 - ξ‖`
* `RBM.norm_one_sub_xi_le` : `‖1 - ξ‖ ≤ 8 (1 - ‖ρ‖)²`
* `RBM.rho_complex_bounds` : `√(‖1-ξ‖/8) ≤ 1 - ‖ρ‖ ≤ √3 √‖1-ξ‖`
-/

namespace RBM

section RealLemma

/-- The real-variable core: if `r = ‖ρ‖ ≥ 1/2` and `3‖ρ‖ < ‖1 + ρ + ρ²‖`, written in
`p = Re ρ`, `q = Im ρ`, then `ρ` lies in the parabolic region `r - p ≤ (1 - r)²`. -/
theorem sub_re_le_of_poly {p q r : ℝ} (hr : r ^ 2 = p ^ 2 + q ^ 2) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hr2 : 1 / 2 ≤ r)
    (hg : 9 * r ^ 2 < (1 + p + p ^ 2 - q ^ 2) ^ 2 + (q + 2 * p * q) ^ 2) :
    r - p ≤ (1 - r) ^ 2 := by
  have hpr : p ≤ r := by nlinarith [sq_nonneg q, sq_nonneg (p + r)]
  have hpr' : -r ≤ p := by nlinarith [sq_nonneg q, sq_nonneg (p - r)]
  have key : (1 + p + p ^ 2 - q ^ 2) ^ 2 + (q + 2 * p * q) ^ 2 - 9 * r ^ 2 =
      -4 * (r - p - (1 - r) ^ 2) * (r + p) + (r ^ 2 - 4 * r + 1) * (r ^ 2 + 1 - 2 * p) := by
    linear_combination (-(q ^ 2 + r ^ 2 + p ^ 2 + 2 * p - 1)) * hr
  have hneg : r ^ 2 - 4 * r + 1 < 0 := by nlinarith
  have hpos : 0 ≤ r ^ 2 + 1 - 2 * p := by nlinarith
  rcases le_or_gt (r - p) ((1 - r) ^ 2) with h | h
  · exact h
  · nlinarith [mul_nonneg (sub_nonneg.2 h.le) (neg_le_iff_add_nonneg.1 hpr'),
      mul_nonneg (neg_nonneg.2 hneg.le) hpos]

end RealLemma

variable {ξ : ℂ}

/-- `‖1 + ρ + ρ²‖ ≤ 3` on the disc. -/
theorem norm_one_add_rho_add_sq_le (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖1 + rho ξ + rho ξ ^ 2‖ ≤ 3 := by
  have h1 := (norm_rho_lt_one hξ0 hξ).le
  calc ‖1 + rho ξ + rho ξ ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖rho ξ‖ + ‖rho ξ ^ 2‖ := norm_add₃_le
    _ ≤ 3 := by
      rw [norm_one, norm_pow]
      nlinarith [norm_nonneg (rho ξ)]

/-- `‖ξ‖ < 1` in terms of `ρ`: `3‖ρ‖ < ‖1 + ρ + ρ²‖`. -/
theorem three_mul_norm_rho_lt (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    3 * ‖rho ξ‖ < ‖1 + rho ξ + rho ξ ^ 2‖ := by
  have h := congrArg (‖·‖) (xi_mul_poly hξ0)
  simp only [norm_mul] at h
  have hρ : 0 < ‖rho ξ‖ := norm_pos_iff.2 (rho_ne_zero hξ0 hξ)
  have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [h3] at h
  have hP : 0 < ‖1 + rho ξ + rho ξ ^ 2‖ := by
    rcases (norm_nonneg (1 + rho ξ + rho ξ ^ 2)).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at h
      linarith
    · exact h0
  nlinarith

/-- `‖1 - ρ‖² = ‖1 - ξ‖ ‖1 + ρ + ρ²‖`, the norm form of `RBM.one_sub_rho_sq`. -/
theorem norm_one_sub_rho_sq_eq (hξ0 : ξ ≠ 0) :
    ‖1 - rho ξ‖ ^ 2 = ‖1 - ξ‖ * ‖1 + rho ξ + rho ξ ^ 2‖ := by
  have h := congrArg (‖·‖) (one_sub_rho_sq hξ0)
  simpa [norm_pow, norm_mul] using h

/-- **Upper bound on the rate**: `(1 - ‖ρ‖)² ≤ 3 ‖1 - ξ‖`. -/
theorem sq_one_sub_norm_rho_le (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    (1 - ‖rho ξ‖) ^ 2 ≤ 3 * ‖1 - ξ‖ := by
  have h1 : 0 ≤ 1 - ‖rho ξ‖ := sub_nonneg.2 (norm_rho_lt_one hξ0 hξ).le
  have h2 : 1 - ‖rho ξ‖ ≤ ‖1 - rho ξ‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (rho ξ)
  have h3 := norm_one_sub_rho_sq_eq hξ0
  have h4 := norm_one_add_rho_add_sq_le hξ0 hξ
  calc (1 - ‖rho ξ‖) ^ 2 ≤ ‖1 - rho ξ‖ ^ 2 := pow_le_pow_left₀ h1 h2 2
    _ = ‖1 - ξ‖ * ‖1 + rho ξ + rho ξ ^ 2‖ := h3
    _ ≤ ‖1 - ξ‖ * 3 := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = 3 * ‖1 - ξ‖ := mul_comm _ _

/-- **Lower bound on the rate**: `‖1 - ξ‖ ≤ 8 (1 - ‖ρ‖)²`. -/
theorem norm_one_sub_xi_le (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖1 - ξ‖ ≤ 8 * (1 - ‖rho ξ‖) ^ 2 := by
  set ρ := rho ξ with hρdef
  have hr1 : ‖ρ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hr0 : 0 ≤ ‖ρ‖ := norm_nonneg _
  have hξ1 : ‖1 - ξ‖ < 2 := by
    calc ‖1 - ξ‖ ≤ ‖(1 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
      _ < 2 := by rw [norm_one]; linarith
  rcases lt_or_ge ‖ρ‖ (1 / 2) with hsmall | hbig
  · nlinarith
  · have hP := three_mul_norm_rho_lt hξ0 hξ
    have hsq : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hPsq : ‖1 + ρ + ρ ^ 2‖ ^ 2 =
        (1 + ρ.re + ρ.re ^ 2 - ρ.im ^ 2) ^ 2 + (ρ.im + 2 * ρ.re * ρ.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, pow_two,
        Complex.mul_re, Complex.mul_im]
      ring
    have hg : 9 * ‖ρ‖ ^ 2 <
        (1 + ρ.re + ρ.re ^ 2 - ρ.im ^ 2) ^ 2 + (ρ.im + 2 * ρ.re * ρ.im) ^ 2 := by
      rw [← hPsq]; nlinarith
    have hpar := sub_re_le_of_poly hsq hr0 hr1 hbig hg
    have h1ρ : ‖1 - ρ‖ ^ 2 = (1 - ‖ρ‖) ^ 2 + 2 * (‖ρ‖ - ρ.re) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith [hsq]
    have h3 := norm_one_sub_rho_sq_eq hξ0
    rw [← hρdef] at h3
    nlinarith [norm_nonneg (1 - ξ)]

/-- **The decay rate of (2.52), complex case**: for `0 < ‖ξ‖ < 1`,
`√(‖1 - ξ‖/8) ≤ 1 - ‖ρ(ξ)‖ ≤ √3 √‖1 - ξ‖`. -/
theorem rho_complex_bounds (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    Real.sqrt (‖1 - ξ‖ / 8) ≤ 1 - ‖rho ξ‖ ∧
      1 - ‖rho ξ‖ ≤ Real.sqrt 3 * Real.sqrt ‖1 - ξ‖ := by
  have h1 : 0 ≤ 1 - ‖rho ξ‖ := sub_nonneg.2 (norm_rho_lt_one hξ0 hξ).le
  constructor
  · rw [Real.sqrt_le_left h1]
    have := norm_one_sub_xi_le hξ0 hξ
    linarith
  · rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.le_sqrt_of_sq_le (sq_one_sub_norm_rho_le hξ0 hξ)

end RBM
