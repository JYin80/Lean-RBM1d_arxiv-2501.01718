/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Symbol
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Two-sided bound on the Fourier multiplier (B.3)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Appendix B, (B.3):

  `|1 - ξ Ŝ(p)| ≍ |1 - ξ| + |p|²`,  `‖ξ‖ < 1`, `p ∈ (-π, π]`.

The frequency `p ∈ ZMod L` of `RBM1D.Propagator.Symbol` stands for the momentum
`θ(p) = 2π p̃ / L`, where `p̃ = ZMod.valMinAbs p ∈ (-L/2, L/2]` is the representative closest
to `0`; so `|θ(p)| ≤ π` and `Ŝ(p) = (1 + 2 cos θ(p))/3` (`RBM.Shat_eq_cos_theta`).

This is the entry point of the general Fourier machinery (T8-T11); it does not use the
nearest-neighbour closed form of `RBM1D.Propagator.Decay`.

## The argument

Write `s = 1 - Ŝ = (2/3)(1 - cos θ) ∈ [0, 4/3]`.  Then `1 - cos θ ≍ θ²` on `[-π, π]`:
`1 - cos θ ≤ θ²/2`, and `1 - cos θ = 2 sin²(θ/2) ≥ 2θ²/π²` by Jordan's inequality.

* Upper: `1 - ξŜ = (1 - ξ) + ξ s`, so `|1 - ξŜ| ≤ |1 - ξ| + s ≤ |1 - ξ| + θ²/3`.
* Lower, `Ŝ ≥ 1/2`: `1 - ξŜ = s + Ŝ(1 - ξ)` with `Re(1 - ξ) > 0`, so `|1 - ξŜ| ≥ s` and
  `|1 - ξŜ| ≥ Ŝ|1 - ξ| - s`; adding, `3|1 - ξŜ| ≥ s + |1 - ξ|/2`.
* Lower, `Ŝ < 1/2`: `|1 - ξŜ| ≥ 1 - |Ŝ| > 1/2`, while `|1 - ξ| + s ≤ 2 + 4/3`.

## Main results

* `RBM.theta`, `RBM.abs_theta_le_pi`, `RBM.Shat_eq_cos_theta`
* `RBM.norm_one_sub_mul_Shat_le` : `|1 - ξŜ(p)| ≤ |1 - ξ| + θ(p)²`
* `RBM.le_norm_one_sub_mul_Shat` : `(|1 - ξ| + θ(p)²) / (6π²) ≤ |1 - ξŜ(p)|`
* `RBM.norm_one_sub_mul_Shat_asymp` : both, as `∃ c C > 0`
-/

namespace RBM

open Real

variable (L : ℕ) [NeZero L]

/-- The momentum of the frequency `p`: `θ(p) = 2π valMinAbs(p) / L ∈ [-π, π]`. -/
noncomputable def theta (p : ZMod L) : ℝ := 2 * π * p.valMinAbs / L

theorem abs_theta_le_pi (p : ZMod L) : |theta L p| ≤ π := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have h := ZMod.natAbs_valMinAbs_le p
  have h' : |(p.valMinAbs : ℝ)| ≤ L / 2 := by
    have e : |(p.valMinAbs : ℝ)| = (p.valMinAbs.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    calc (p.valMinAbs.natAbs : ℝ) ≤ ((L / 2 : ℕ) : ℝ) := by exact_mod_cast h
      _ ≤ L / 2 := Nat.cast_div_le
  rw [theta, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
    abs_of_pos hL, div_le_iff₀ hL]
  nlinarith [pi_pos]

/-- `cos(2π p.val / L) = cos θ(p)`: the two representatives differ by `0` or `L`. -/
theorem cos_val_eq_cos_theta (p : ZMod L) :
    cos (2 * π * p.val / L) = cos (theta L p) := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  rw [theta, ZMod.valMinAbs_def_pos]
  split_ifs
  · push_cast; rfl
  · push_cast
    have : 2 * π * ((p.val : ℝ) - L) / L = 2 * π * p.val / L - 2 * π := by
      field_simp
    rw [this, cos_sub_two_pi]

/-- The symbol in terms of the momentum: `Ŝ(p) = (1 + 2 cos θ(p))/3`. -/
theorem Shat_eq_cos_theta (p : ZMod L) :
    Shat L p = (((1 + 2 * cos (theta L p)) / 3 : ℝ) : ℂ) := by
  rw [Shat_eq_cos, cos_val_eq_cos_theta]

/-- `1 - cos θ ≤ θ²/2`. -/
theorem one_sub_cos_le (x : ℝ) : 1 - cos x ≤ x ^ 2 / 2 := by
  linarith [one_sub_sq_div_two_le_cos (x := x)]

/-- `1 - cos θ ≥ 2θ²/π²` on `[-π, π]` (Jordan's inequality at `θ/2`). -/
theorem le_one_sub_cos {x : ℝ} (hx : |x| ≤ π) : 2 / π ^ 2 * x ^ 2 ≤ 1 - cos x := by
  have hy0 : 0 ≤ |x| / 2 := by positivity
  have hy1 : |x| / 2 ≤ π / 2 := by linarith
  have hJ := mul_le_sin hy0 hy1
  have hcos : cos x = 1 - 2 * sin (|x| / 2) ^ 2 := by
    have h1 : cos x = cos |x| := (cos_abs x).symm
    have h2 : |x| = 2 * (|x| / 2) := by ring
    rw [h1, h2, cos_two_mul, mul_div_cancel_left₀ _ (two_ne_zero)]
    nlinarith [sin_sq_add_cos_sq (|x| / 2)]
  have hpi : 0 < π := pi_pos
  have hs : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have hsq : (2 / π * (|x| / 2)) ^ 2 ≤ sin (|x| / 2) ^ 2 := pow_le_pow_left₀ hs hJ 2
  have e : (2 / π * (|x| / 2)) ^ 2 = x ^ 2 / π ^ 2 := by
    rw [mul_pow, div_pow, div_pow, sq_abs]
    field_simp
  rw [e] at hsq
  rw [hcos]
  have : 2 / π ^ 2 * x ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
  linarith

variable {L}

/-- `s(p) = 1 - Ŝ(p)`, real and in `[0, 4/3]`, comparable to `θ(p)²`. -/
theorem Shat_bounds (p : ZMod L) :
    ∃ S : ℝ, Shat L p = (S : ℂ) ∧ -1 / 3 ≤ S ∧ S ≤ 1 ∧
      4 / (3 * π ^ 2) * theta L p ^ 2 ≤ 1 - S ∧ 1 - S ≤ theta L p ^ 2 / 3 := by
  refine ⟨(1 + 2 * cos (theta L p)) / 3, Shat_eq_cos_theta L p, ?_, ?_, ?_, ?_⟩
  · linarith [neg_one_le_cos (theta L p)]
  · linarith [cos_le_one (theta L p)]
  · have := le_one_sub_cos (abs_theta_le_pi L p)
    have e : 4 / (3 * π ^ 2) * theta L p ^ 2 = 2 / 3 * (2 / π ^ 2 * theta L p ^ 2) := by
      field_simp
      ring
    rw [e]
    linarith
  · linarith [one_sub_cos_le (theta L p)]

/-- **(B.3), upper bound**: `|1 - ξ Ŝ(p)| ≤ |1 - ξ| + θ(p)²` for `‖ξ‖ ≤ 1`. -/
theorem norm_one_sub_mul_Shat_le {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (p : ZMod L) :
    ‖1 - ξ * Shat L p‖ ≤ ‖1 - ξ‖ + theta L p ^ 2 := by
  obtain ⟨S, hS, -, hS2, -, hup⟩ := Shat_bounds p
  have e : 1 - ξ * Shat L p = (1 - ξ) + ξ * ((1 - S : ℝ) : ℂ) := by
    rw [hS]; push_cast; ring
  have hs0 : 0 ≤ 1 - S := by linarith
  rw [e]
  calc ‖(1 - ξ) + ξ * ((1 - S : ℝ) : ℂ)‖ ≤ ‖1 - ξ‖ + ‖ξ‖ * (1 - S) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    _ ≤ ‖1 - ξ‖ + 1 * (theta L p ^ 2 / 3) := by gcongr
    _ ≤ ‖1 - ξ‖ + theta L p ^ 2 := by nlinarith [sq_nonneg (theta L p)]

/-- **(B.3), lower bound**: `(|1 - ξ| + θ(p)²) / (6π²) ≤ |1 - ξ Ŝ(p)|` for `‖ξ‖ < 1`. -/
theorem le_norm_one_sub_mul_Shat {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : ZMod L) :
    (‖1 - ξ‖ + theta L p ^ 2) / (6 * π ^ 2) ≤ ‖1 - ξ * Shat L p‖ := by
  obtain ⟨S, hS, hS1, hS2, hlow, -⟩ := Shat_bounds p
  set s := 1 - S with hsdef
  set X := 1 - ξ * Shat L p with hX
  have hpi : 3 < π := pi_gt_three
  -- `θ² ≤ (3π²/4) s`, so it suffices to bound `‖1 - ξ‖ + s`
  have hθ : theta L p ^ 2 ≤ 3 * π ^ 2 / 4 * s := by
    have h := hlow
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
    nlinarith
  have hw : ‖1 - ξ‖ < 2 := by
    calc ‖1 - ξ‖ ≤ ‖(1 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
      _ < 2 := by rw [norm_one]; linarith
  -- the key estimate `(‖1 - ξ‖ + s) ≤ 7 ‖X‖`
  have key : ‖1 - ξ‖ + s ≤ 7 * ‖X‖ := by
    rcases lt_or_ge S (1 / 2) with hsmall | hbig
    · -- `‖X‖ ≥ 1 - ‖ξ‖ |S| ≥ 1/2`
      have h1 : 1 - ‖ξ * Shat L p‖ ≤ ‖X‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (ξ * Shat L p)
      have h2 : ‖ξ * Shat L p‖ ≤ 1 / 2 := by
        rw [norm_mul, hS, Complex.norm_real, Real.norm_eq_abs]
        have : |S| ≤ 1 / 2 := abs_le.2 ⟨by linarith, hsmall.le⟩
        nlinarith [norm_nonneg ξ, abs_nonneg S]
      linarith
    · -- `X = s + S (1 - ξ)` and `Re (1 - ξ) ≥ 0`
      have e : X = (s : ℂ) + (S : ℂ) * (1 - ξ) := by
        rw [hX, hS, hsdef]; push_cast; ring
      have hre : 0 ≤ (1 - ξ).re := by
        have := Complex.re_le_norm ξ
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hs0 : 0 ≤ s := by linarith
      have hA : s ≤ ‖X‖ := by
        calc s ≤ (X).re := by
              rw [e]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                Complex.ofReal_im, zero_mul, sub_zero]
              nlinarith
          _ ≤ ‖X‖ := Complex.re_le_norm X
      have hB : S * ‖1 - ξ‖ - s ≤ ‖X‖ := by
        have h := norm_sub_norm_le ((S : ℂ) * (1 - ξ)) (-(s : ℂ))
        rw [sub_neg_eq_add, add_comm, ← e, norm_neg, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ S), Complex.norm_real,
          Real.norm_of_nonneg hs0] at h
        linarith
      nlinarith [norm_nonneg (1 - ξ), mul_nonneg (by linarith : (0 : ℝ) ≤ S - 1 / 2)
        (norm_nonneg (1 - ξ))]
  have hX0 : 0 ≤ ‖X‖ := norm_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have hπ1 : 1 ≤ 3 * π ^ 2 / 4 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  calc ‖1 - ξ‖ + theta L p ^ 2 ≤ ‖1 - ξ‖ + 3 * π ^ 2 / 4 * s := by linarith
    _ ≤ 3 * π ^ 2 / 4 * (‖1 - ξ‖ + s) := by nlinarith [norm_nonneg (1 - ξ)]
    _ ≤ 3 * π ^ 2 / 4 * (7 * ‖X‖) := by gcongr
    _ ≤ ‖X‖ * (6 * π ^ 2) := by nlinarith [sq_nonneg π]

/-- **(B.3)**: `|1 - ξ Ŝ(p)| ≍ |1 - ξ| + |p|²`, uniformly in `L`, `‖ξ‖ < 1` and `p`. -/
theorem norm_one_sub_mul_Shat_asymp :
    ∃ c > 0, ∃ C > 0, ∀ (L : ℕ) [NeZero L] (ξ : ℂ), ‖ξ‖ < 1 → ∀ p : ZMod L,
      c * (‖1 - ξ‖ + theta L p ^ 2) ≤ ‖1 - ξ * Shat L p‖ ∧
        ‖1 - ξ * Shat L p‖ ≤ C * (‖1 - ξ‖ + theta L p ^ 2) := by
  refine ⟨1 / (6 * π ^ 2), by positivity, 1, one_pos, fun L _ ξ hξ p => ⟨?_, ?_⟩⟩
  · have := le_norm_one_sub_mul_Shat hξ p
    rw [one_div_mul_eq_div]; exact this
  · rw [one_mul]; exact norm_one_sub_mul_Shat_le hξ.le p

end RBM
