/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.RateComplex
import RBM1D.Propagator.DecayComplex

/-!
# `1 - ‖ρ(ξ)‖ ≍ |1 - ξ|^{1/2}` and the decay length `ℓ̂(ξ)`

`RBM1D/Propagator/Decay.lean` and `RBM1D/Propagator/RateComplex.lean` contain the
two halves of the quantitative estimate on the decay rate:

* `RBM.rho_real_bounds` : `√(1-t) ≤ 1 - ρ(t) ≤ √3 √(1-t)` for real `t ∈ (0,1)`;
* `RBM.sq_one_sub_norm_rho_le` / `RBM.norm_one_sub_xi_le` :
  `‖1-ξ‖/8 ≤ (1 - ‖ρ(ξ)‖)² ≤ 3‖1-ξ‖` for every `0 < ‖ξ‖ < 1`.

This file is the packaging layer.  It records the two-sided estimate in the
`∃ c > 0, ∃ C > 0, ∀ …` shape the project uses for `≍` (see
`RBM.norm_one_sub_mul_Shat_asymp` for the same idiom), and it connects the rate
to the decay length `ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)` of (2.52): `ℓ̂` is, up to
absolute constants, the true decay length `1/(1 - ‖ρ(ξ)‖)` capped at `L`.

## Why `ξ ≠ 0` cannot be dropped

At `ξ = 0` the characteristic equation degenerates: `cc 0 = -1` (division by zero),
so `ρ² + ρ + 1 = 0` and both roots are primitive cube roots of unity, of modulus
`1`.  Hence `1 - ‖ρ(0)‖ = 0` while `√‖1 - 0‖ = 1`, and the lower bound genuinely
fails at the origin.
This is harmless for the propagator, since `Θ_0 = 1` has no tail at all, but it
means every statement below carries `hξ0 : ξ ≠ 0`, exactly as `RBM.norm_rho_lt_one`
does.

## Main results

* `RBM.sqrt_norm_one_sub_le_three_mul` : `√‖1-ξ‖ ≤ 3 (1 - ‖ρ(ξ)‖)`
* `RBM.one_sub_norm_rho_le_two_mul_sqrt` : `1 - ‖ρ(ξ)‖ ≤ 2 √‖1-ξ‖`
* `RBM.one_sub_norm_rho_asymp` : the two together, as `∃ c C > 0`
* `RBM.ellHat_mul_one_sub_norm_rho_le` : `ℓ̂(ξ) (1 - ‖ρ(ξ)‖) ≤ 2`
* `RBM.min_le_ellHat` : `min (1/(3(1 - ‖ρ(ξ)‖))) L ≤ ℓ̂(ξ)`
* `RBM.norm_rho_pow_le_exp` : `‖ρ(ξ)‖^n ≤ e · exp(-n/(3 ℓ̂(ξ)))` for `n ≤ L`
-/

namespace RBM

variable {ξ : ℂ}

section Rate

/-- **The lower bound on the rate, in root form**: `√‖1-ξ‖ ≤ 3 (1 - ‖ρ(ξ)‖)`.

This is `RBM.norm_one_sub_xi_le` (`‖1-ξ‖ ≤ 8 (1 - ‖ρ‖)²`) with the square root
taken and `√8` relaxed to `3`. -/
theorem sqrt_norm_one_sub_le_three_mul (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    Real.sqrt ‖1 - ξ‖ ≤ 3 * (1 - ‖rho ξ‖) := by
  have h0 : 0 ≤ 1 - ‖rho ξ‖ := sub_nonneg.2 (norm_rho_lt_one hξ0 hξ).le
  have h := norm_one_sub_xi_le hξ0 hξ
  have hle : ‖1 - ξ‖ ≤ (3 * (1 - ‖rho ξ‖)) ^ 2 := by nlinarith
  calc Real.sqrt ‖1 - ξ‖ ≤ Real.sqrt ((3 * (1 - ‖rho ξ‖)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 3 * (1 - ‖rho ξ‖) := Real.sqrt_sq (by linarith)

/-- **The upper bound on the rate, in root form**: `1 - ‖ρ(ξ)‖ ≤ 2 √‖1-ξ‖`.

This is `RBM.sq_one_sub_norm_rho_le` (`(1 - ‖ρ‖)² ≤ 3 ‖1-ξ‖`) with the square root
taken and `√3` relaxed to `2`. -/
theorem one_sub_norm_rho_le_two_mul_sqrt (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    1 - ‖rho ξ‖ ≤ 2 * Real.sqrt ‖1 - ξ‖ := by
  have h0 : 0 ≤ 1 - ‖rho ξ‖ := sub_nonneg.2 (norm_rho_lt_one hξ0 hξ).le
  have h := sq_one_sub_norm_rho_le hξ0 hξ
  have hs : Real.sqrt ‖1 - ξ‖ ^ 2 = ‖1 - ξ‖ := Real.sq_sqrt (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg ‖1 - ξ‖]

/-- **T1**: `1 - ‖ρ(ξ)‖ ≍ |1 - ξ|^{1/2}`, uniformly on the punctured disc
`0 < ‖ξ‖ < 1`, with absolute constants `c = 1/3` and `C = 2`.

This is the quantitative statement behind the decay length `ℓ̂(ξ) = |1-ξ|^{-1/2}`
of (2.52).  The square root is not an artefact of the estimates: by
`RBM.one_sub_xi_mul` one has the *exact* identity `1 - ξ = (1-ρ)²/(1+ρ+ρ²)`, so
`ξ = 1` is a double zero. -/
theorem one_sub_norm_rho_asymp :
    ∃ c > 0, ∃ C > 0, ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      c * Real.sqrt ‖1 - ξ‖ ≤ 1 - ‖rho ξ‖ ∧ 1 - ‖rho ξ‖ ≤ C * Real.sqrt ‖1 - ξ‖ := by
  refine ⟨1 / 3, by norm_num, 2, by norm_num, fun ξ hξ0 hξ => ⟨?_, ?_⟩⟩
  · have := sqrt_norm_one_sub_le_three_mul hξ0 hξ
    linarith
  · exact one_sub_norm_rho_le_two_mul_sqrt hξ0 hξ

end Rate

section EllHatRate

/-- `ℓ̂(ξ) ≥ 0`: both branches of the `min` are nonnegative. -/
theorem ellHat_nonneg (L : ℕ) (ξ : ℂ) : 0 ≤ ellHat L ξ := by
  rw [ellHat]
  exact le_min (by positivity) (Nat.cast_nonneg L)

/-- **`ℓ̂` never exceeds the true decay length.**  `ℓ̂(ξ) (1 - ‖ρ(ξ)‖) ≤ 2`, i.e.
`ℓ̂(ξ) ≤ 2 / (1 - ‖ρ(ξ)‖)`.

Together with `RBM.min_le_ellHat` this says that the length scale `ℓ̂` of (2.52)
*is* the decay length of the closed form, capped at `L`, up to absolute constants. -/
theorem ellHat_mul_one_sub_norm_rho_le (L : ℕ) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ellHat L ξ * (1 - ‖rho ξ‖) ≤ 2 := by
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := sqrt_norm_one_sub_pos hξ
  have h0 : 0 ≤ 1 - ‖rho ξ‖ := sub_nonneg.2 (norm_rho_lt_one hξ0 hξ).le
  have h1 : ellHat L ξ ≤ 1 / Real.sqrt ‖1 - ξ‖ := by rw [ellHat]; exact min_le_left _ _
  have h3 := one_sub_norm_rho_le_two_mul_sqrt hξ0 hξ
  calc ellHat L ξ * (1 - ‖rho ξ‖)
      ≤ (1 / Real.sqrt ‖1 - ξ‖) * (2 * Real.sqrt ‖1 - ξ‖) :=
        mul_le_mul h1 h3 h0 (by positivity)
    _ = 2 := by field_simp

/-- **`ℓ̂` is at least the true decay length, capped at `L`.**
`min (1/(3 (1 - ‖ρ(ξ)‖))) L ≤ ℓ̂(ξ)`.

The cap at `L` is unavoidable: `ℓ̂` is a `min` with `L`, and for `ξ` extremely close
to `1` the true decay length exceeds the size of the system. -/
theorem min_le_ellHat (L : ℕ) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    min (1 / (3 * (1 - ‖rho ξ‖))) (L : ℝ) ≤ ellHat L ξ := by
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := sqrt_norm_one_sub_pos hξ
  have hkey := sqrt_norm_one_sub_le_three_mul hξ0 hξ
  have h : 1 / (3 * (1 - ‖rho ξ‖)) ≤ 1 / Real.sqrt ‖1 - ξ‖ :=
    one_div_le_one_div_of_le hs hkey
  rw [ellHat]
  exact min_le_min h le_rfl

/-- **The exponential factor of (2.52), driven by the rate.**
For `0 < ‖ξ‖ < 1` and `n ≤ L`,

  `‖ρ(ξ)‖^n ≤ e · exp(-n / (3 ℓ̂(ξ)))`.

Both branches of the `min` in `ℓ̂` are used, exactly as in the real-`ξ` argument
inside `RBM.norm_Theta_apply_le_of_real`:

* `ℓ̂ = ‖1-ξ‖^{-1/2}`: then `‖ρ‖^n ≤ exp(-n(1-‖ρ‖)) ≤ exp(-n √‖1-ξ‖/3)` by
  `RBM.sqrt_norm_one_sub_le_three_mul`;
* `ℓ̂ = L`: the exponential is useless (`n ≤ L` gives `exp(-n/(3L)) ≥ e^{-1}`) and
  `‖ρ‖^n ≤ 1` carries the bound on its own.

Combined with `RBM.norm_theta_apply_le_rho_pow` this is the closed-form route to
the exponential factor of (2.52) for complex `ξ`, independent of the contour shift
plus Poisson summation used in `RBM1D/Propagator/DecayComplex.lean`. -/
theorem norm_rho_pow_le_exp (L : ℕ) (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1)
    {n : ℕ} (hn : n ≤ L) :
    ‖rho ξ‖ ^ n ≤ Real.exp 1 * Real.exp (-(n : ℝ) / (3 * ellHat L ξ)) := by
  set r := ‖rho ξ‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := norm_rho_lt_one hξ0 hξ
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := sqrt_norm_one_sub_pos hξ
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by omega
    exact_mod_cast this
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  -- `r^n ≤ exp(-n (1 - r))`
  have hrn : r ^ n ≤ Real.exp (-(n : ℝ) * (1 - r)) := by
    have hre : r ≤ Real.exp (-(1 - r)) := by
      have := Real.add_one_le_exp (-(1 - r)); linarith
    calc r ^ n ≤ Real.exp (-(1 - r)) ^ n := pow_le_pow_left₀ hr0 hre n
      _ = Real.exp ((n : ℝ) * -(1 - r)) := (Real.exp_nat_mul _ n).symm
      _ = Real.exp (-(n : ℝ) * (1 - r)) := by ring_nf
  rcases le_total (1 / Real.sqrt ‖1 - ξ‖) ((L : ℝ)) with hcase | hcase
  · -- `ℓ̂ = ‖1-ξ‖^{-1/2}`
    have hell : ellHat L ξ = 1 / Real.sqrt ‖1 - ξ‖ := by
      rw [ellHat]; exact min_eq_left hcase
    have hx : -(n : ℝ) / (3 * (1 / Real.sqrt ‖1 - ξ‖))
        = -(n : ℝ) * (Real.sqrt ‖1 - ξ‖ / 3) := by field_simp
    rw [hell, hx]
    have hkey := sqrt_norm_one_sub_le_three_mul hξ0 hξ
    rw [← hrdef] at hkey
    calc r ^ n ≤ Real.exp (-(n : ℝ) * (1 - r)) := hrn
      _ ≤ Real.exp (-(n : ℝ) * (Real.sqrt ‖1 - ξ‖ / 3)) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
      _ = 1 * Real.exp (-(n : ℝ) * (Real.sqrt ‖1 - ξ‖ / 3)) := (one_mul _).symm
      _ ≤ Real.exp 1 * Real.exp (-(n : ℝ) * (Real.sqrt ‖1 - ξ‖ / 3)) :=
          mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
  · -- `ℓ̂ = L`
    have hell : ellHat L ξ = (L : ℝ) := by
      rw [ellHat]; exact min_eq_right hcase
    rw [hell]
    have hnL : (n : ℝ) ≤ (L : ℝ) := by exact_mod_cast hn
    have hexp : Real.exp (-1 : ℝ) ≤ Real.exp (-(n : ℝ) / (3 * (L : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div, neg_le_neg_iff, div_le_one (by positivity)]
      linarith
    calc r ^ n ≤ 1 := pow_le_one₀ hr0 hr1.le
      _ = Real.exp 1 * Real.exp (-1 : ℝ) := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp 1 * Real.exp (-(n : ℝ) / (3 * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos 1).le

end EllHatRate

end RBM

