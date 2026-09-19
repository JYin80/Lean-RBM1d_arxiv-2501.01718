/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Dist
import RBM1D.Propagator.Bounds

/-!
# Band structure and a first exponential decay bound

`S^(B)` is a band matrix: `(S^(B))^k` vanishes outside the band of width `k`
(`RBM.SB_pow_apply_eq_zero`).  Truncating the Neumann series of Definition 2.13
at order `d = dist(x,y)` therefore gives

`|(Θ_ξ)_{xy}| ≤ ‖ξ‖^{dist(x,y)} / (1 - ‖ξ‖)`,

which is an exponential decay with length `1 / log(1/‖ξ‖)`.

This is *weaker* than Lemma 2.14 (4): the sharp statement (2.52) has decay length
`min(|1-ξ|^{-1/2}, L)`, governed by `|1 - ξ|` rather than `1 - |ξ|`.  The
difference matters exactly in the regime the paper cares about, where
`ξ = t m^2` has `‖ξ‖ → 1` while `|1 - ξ|` stays of order one.  The sharp bound is
the next target; see `docs/STATUS.md`.
-/

namespace RBM

open Matrix
open scoped Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- `(S^(B))^k` vanishes outside the band of width `k`. -/
theorem SB_pow_apply_eq_zero (hL : 3 ≤ L) :
    ∀ (k : ℕ) (x y : ZMod L), k < zdist L (x - y) → (SB L ^ k) x y = 0 := by
  intro k
  induction k with
  | zero =>
    intro x y h
    have hxy : x - y ≠ 0 := ne_zero_of_zdist_ne_zero L (by omega)
    have : x ≠ y := fun he => hxy (by rw [he, sub_self])
    simp [this]
  | succ k ih =>
    intro x y h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : k < zdist L (x - z)
    · rw [ih x z h1, zero_mul]
    · have h2 : 1 < zdist L (z - y) := by
        by_contra h3
        have htri : zdist L (x - y) ≤ zdist L (x - z) + zdist L (z - y) := by
          have : x - y = (x - z) + (z - y) := by ring
          rw [this]
          exact zdist_add_le L _ _
        omega
      rw [SB_apply_eq_zero L hL h2, mul_zero]

/-- Truncated Neumann series: `Θ_ξ = ∑_{k < N} (ξ S^(B))^k + (ξ S^(B))^N Θ_ξ`. -/
theorem Theta_eq_geom_add (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (N : ℕ) :
    Theta L ξ = (∑ k ∈ Finset.range N, (ξ • SB L) ^ k) + (ξ • SB L) ^ N * Theta L ξ := by
  have hgs : (∑ k ∈ Finset.range N, (ξ • SB L) ^ k) * (1 - ξ • SB L)
      = 1 - (ξ • SB L) ^ N := by
    have h := geom_sum_mul (ξ • SB L) N
    have h2 : (∑ k ∈ Finset.range N, (ξ • SB L) ^ k) * (1 - ξ • SB L)
        = -((∑ k ∈ Finset.range N, (ξ • SB L) ^ k) * ((ξ • SB L) - 1)) := by
      noncomm_ring
    rw [h2, h, neg_sub]
  have key : (∑ k ∈ Finset.range N, (ξ • SB L) ^ k)
      = Theta L ξ - (ξ • SB L) ^ N * Theta L ξ := by
    calc (∑ k ∈ Finset.range N, (ξ • SB L) ^ k)
        = (∑ k ∈ Finset.range N, (ξ • SB L) ^ k) * ((1 - ξ • SB L) * Theta L ξ) := by
          rw [mul_Theta L hL hξ, mul_one]
      _ = ((∑ k ∈ Finset.range N, (ξ • SB L) ^ k) * (1 - ξ • SB L)) * Theta L ξ :=
          (mul_assoc _ _ _).symm
      _ = (1 - (ξ • SB L) ^ N) * Theta L ξ := by rw [hgs]
      _ = Theta L ξ - (ξ • SB L) ^ N * Theta L ξ := by rw [sub_mul, one_mul]
  rw [key]
  abel

/-- The truncated part of the Neumann series vanishes inside the band. -/
theorem geom_sum_apply_eq_zero (hL : 3 ≤ L) (ξ : ℂ) {N : ℕ} {x y : ZMod L}
    (h : N ≤ zdist L (x - y)) :
    (∑ k ∈ Finset.range N, (ξ • SB L) ^ k) x y = 0 := by
  rw [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkN : k < N := Finset.mem_range.mp hk
  rw [smul_pow, Matrix.smul_apply, SB_pow_apply_eq_zero L hL k x y (by omega), smul_zero]

/-- A first exponential decay bound for the propagator:
`|(Θ_ξ)_{xy}| ≤ ‖ξ‖^{dist(x,y)} / (1 - ‖ξ‖)`. -/
theorem norm_Theta_apply_le_pow (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    ‖Theta L ξ x y‖ ≤ ‖ξ‖ ^ (zdist L (x - y)) * (1 - ‖ξ‖)⁻¹ := by
  set d := zdist L (x - y) with hd
  have hdecomp := Theta_eq_geom_add L hL hξ d
  have hzero : (∑ k ∈ Finset.range d, (ξ • SB L) ^ k) x y = 0 :=
    geom_sum_apply_eq_zero L hL ξ (le_refl d)
  have hentry : Theta L ξ x y = ((ξ • SB L) ^ d * Theta L ξ) x y := by
    have := congrFun (congrFun hdecomp x) y
    simpa [Matrix.add_apply, hzero] using this
  rw [hentry]
  refine le_trans (norm_entry_le_norm L _ x y) ?_
  calc ‖(ξ • SB L) ^ d * Theta L ξ‖
      ≤ ‖(ξ • SB L) ^ d‖ * ‖Theta L ξ‖ := norm_mul_le _ _
    _ ≤ ‖ξ‖ ^ d * (1 - ‖ξ‖)⁻¹ := by
        refine mul_le_mul ?_ (norm_Theta_le L hL hξ) (norm_nonneg _) (by positivity)
        calc ‖(ξ • SB L) ^ d‖ ≤ ‖ξ • SB L‖ ^ d := norm_pow_le _ d
          _ = ‖ξ‖ ^ d := by rw [norm_smul_SB L hL]

end RBM
