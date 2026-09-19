/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The characteristic root `ρ(ξ)`

Groundwork for the sharp exponential decay (2.52) of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

For the nearest-neighbour `S^(B)` in `d = 1`, the equation `(1 - ξ S^(B)) Θ = 1`
is, entrywise in the circulant kernel `k`, the three-term recursion

  `k(u) - (ξ/3)[k(u-1) + k(u) + k(u+1)] = δ_{u,0}`,

whose characteristic equation is `ρ² - c ρ + 1 = 0` with `c = 3/ξ - 1`.  The two
roots multiply to `1`.

The key fact, proved here, is that for `0 < ‖ξ‖ < 1` **neither root lies on the
unit circle**, so exactly one of them is inside it.  This is what fails for
`‖ξ‖ ≥ 1`, and it is the same statement as `1 - ξ Ŝ(p) ≠ 0` in the Fourier
picture of Appendix B.

The argument needs only the triangle inequality: if `‖ρ‖ = 1` then
`‖c‖ = ‖ρ + ρ⁻¹‖ ≤ 2`, hence `3/‖ξ‖ = ‖c + 1‖ ≤ 3`, i.e. `‖ξ‖ ≥ 1`.
-/

namespace RBM

variable {ξ : ℂ}

/-- `c(ξ) = 3/ξ - 1`, the coefficient in the characteristic equation. -/
noncomputable def cc (ξ : ℂ) : ℂ := 3 / ξ - 1

/-- A square root of the discriminant `c² - 4`, chosen arbitrarily; `ℂ` is
algebraically closed so one exists. -/
noncomputable def disc (ξ : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (cc ξ ^ 2 - 4) (n := 2) (by norm_num))

theorem disc_sq (ξ : ℂ) : disc ξ ^ 2 = cc ξ ^ 2 - 4 :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (cc ξ ^ 2 - 4) (n := 2) (by norm_num))

/-- The two roots of `ρ² - c ρ + 1 = 0`. -/
noncomputable def root1 (ξ : ℂ) : ℂ := (cc ξ + disc ξ) / 2

/-- The two roots of `ρ² - c ρ + 1 = 0`. -/
noncomputable def root2 (ξ : ℂ) : ℂ := (cc ξ - disc ξ) / 2

theorem root_add (ξ : ℂ) : root1 ξ + root2 ξ = cc ξ := by
  unfold root1 root2; ring

theorem root_mul (ξ : ℂ) : root1 ξ * root2 ξ = 1 := by
  have h := disc_sq ξ
  unfold root1 root2
  field_simp
  linear_combination -h

theorem root1_eq (ξ : ℂ) : root1 ξ ^ 2 - cc ξ * root1 ξ + 1 = 0 := by
  have hm := root_mul ξ
  have ha := root_add ξ
  rw [← ha, ← hm]; ring

theorem root2_eq (ξ : ℂ) : root2 ξ ^ 2 - cc ξ * root2 ξ + 1 = 0 := by
  have hm := root_mul ξ
  have ha := root_add ξ
  rw [← ha, ← hm]; ring

/-- **No root lies on the unit circle** when `0 < ‖ξ‖ < 1`.
This is the statement that fails for `‖ξ‖ ≥ 1`. -/
theorem norm_root_ne_one (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) {ρ : ℂ}
    (hρ : ρ ^ 2 - cc ξ * ρ + 1 = 0) : ‖ρ‖ ≠ 1 := by
  intro h1
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    norm_num at hρ
  have hsum : ρ + ρ⁻¹ = cc ξ := by
    have h : ρ ^ 2 + 1 = cc ξ * ρ := by linear_combination hρ
    field_simp
    linear_combination h
  have hc : ‖cc ξ‖ ≤ 2 := by
    rw [← hsum]
    calc ‖ρ + ρ⁻¹‖ ≤ ‖ρ‖ + ‖ρ⁻¹‖ := norm_add_le _ _
      _ = 2 := by rw [norm_inv, h1]; norm_num
  have h3 : (3 : ℂ) / ξ = cc ξ + 1 := by unfold cc; ring
  have hle : ‖(3 : ℂ) / ξ‖ ≤ 3 := by
    rw [h3]
    calc ‖cc ξ + 1‖ ≤ ‖cc ξ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith
  rw [norm_div] at hle
  have hn : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ0
  have h3n : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [h3n, div_le_iff₀ hn] at hle
  linarith

/-- `ρ(ξ)`: the root of `ρ² - (3/ξ - 1) ρ + 1 = 0` of modulus `< 1`. -/
noncomputable def rho (ξ : ℂ) : ℂ := if ‖root1 ξ‖ < 1 then root1 ξ else root2 ξ

theorem rho_eq (ξ : ℂ) : rho ξ ^ 2 - cc ξ * rho ξ + 1 = 0 := by
  unfold rho
  split_ifs
  · exact root1_eq ξ
  · exact root2_eq ξ

theorem norm_rho_lt_one (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) : ‖rho ξ‖ < 1 := by
  unfold rho
  split_ifs with h
  · exact h
  · rw [not_lt] at h
    have hne : ‖root1 ξ‖ ≠ 1 := norm_root_ne_one hξ0 hξ (root1_eq ξ)
    have h1 : 1 < ‖root1 ξ‖ := lt_of_le_of_ne h (Ne.symm hne)
    have hm : ‖root1 ξ‖ * ‖root2 ξ‖ = 1 := by
      rw [← norm_mul, root_mul, norm_one]
    nlinarith [norm_nonneg (root2 ξ)]

theorem rho_ne_zero (_hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) : rho ξ ≠ 0 := by
  intro h
  have := rho_eq ξ
  rw [h] at this
  norm_num at this

end RBM
