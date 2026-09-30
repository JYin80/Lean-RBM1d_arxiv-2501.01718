/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel
import RBM1D.Gauss.GridPath

/-!
# A quantitative max-norm bound for the backward evolution kernel

The backward kernel `U_{u_{j+1},u_k} = U_{u_k,t}^{-1} U_{u_{j+1},t}` uses the explicit inverse
`U_{u_k,t}^{-1} = Uker ξ t u_k` (the semigroup law `RBM.Uker_comp` with `RBM.Uker_self`), i.e.
`RBM.Uker`/`RBM.edgeKer` run with the *large* time first and the *small* time second.  This file
gives a quantitative bound, **uniform in the earlier time `u ∈ [0,t]`**, used for the Azuma
step on the grid (the martingale `M̃_k`).

## The row bound

For `0 ≤ u ≤ t < 1` and `‖ξ‖ ≤ 1` the row `l^1` bound of the single back-edge is
`1 + (t-u)·‖ξ‖·(1-u‖ξ‖)⁻¹`, and this quantity is bounded by `2` on the whole range,
*including `‖ξ‖ = 1`*: `t < 1` gives `t‖ξ‖ ≤ 1`, which is exactly what is needed for
`(t-u)‖ξ‖ ≤ 1-u‖ξ‖`.  The constant `2` is approached (never exceeded) as `t → 1⁻`, `‖ξ‖ → 1`,
`u → 0`.

## Main results

* `RBM.norm_Uker_back_le` : the `2^n` max-norm bound for `Uker L ξ t u`, uniform in
  `u ∈ [0,t]`, from the row bound `≤ 1 + (t-u)‖ξ‖(1-u‖ξ‖)⁻¹ ≤ 2` of each back-edge.
-/

namespace RBM

open Matrix Finset

section Arithmetic

/-- The complex norm of a nonnegative real scalar times `ξ`, in real terms. -/
private lemma norm_real_mul (r : ℝ) (hr : 0 ≤ r) (ξ : ℂ) : ‖(r : ℂ) * ξ‖ = r * ‖ξ‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The purely real arithmetic core of `norm_Uker_back_le`: given `0 ≤ u ≤ t < 1` and `0 ≤ r ≤ 1`,
`u r < 1` and `1 + (t-u) r (1-ur)⁻¹ ≤ 2`. -/
private lemma back_bound_real {u t r : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    u * r < 1 ∧ 1 + (t - u) * r * (1 - u * r)⁻¹ ≤ 2 := by
  have ht0 : 0 ≤ t := hu0.trans hut
  have hur_le_u : u * r ≤ u := mul_le_of_le_one_right hu0 hr1
  have hur_lt1 : u * r < 1 := lt_of_le_of_lt hur_le_u (lt_of_le_of_lt hut ht1)
  have htr_le_t : t * r ≤ t := mul_le_of_le_one_right ht0 hr1
  have htr_le1 : t * r ≤ 1 := htr_le_t.trans ht1.le
  have hden_pos : 0 < 1 - u * r := by linarith
  refine ⟨hur_lt1, ?_⟩
  have hnum_le : (t - u) * r ≤ 1 - u * r := by nlinarith
  have hratio_le_one : (t - u) * r * (1 - u * r)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hden_pos).mpr hnum_le
  linarith

end Arithmetic

section Edge

variable (L : ℕ) [NeZero L]

end Edge

section Kernel

variable (L : ℕ) [NeZero L]

/-- **(T2)**: the backward evolution kernel `Uker L ξ t u`, for `n` edges each with
`‖ξ i‖ ≤ 1`, has max-norm at most `2^n`, **uniformly in `u ∈ [0,t]`** (the constant does not
blow up as `u → t` or as `t → 1⁻`; see the module docstring). -/
theorem norm_Uker_back_le (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {u t : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    {M : ℝ} (hM0 : 0 ≤ M) {A : LoopArg L n → ℂ} (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L n) :
    ‖Uker L ξ (t : ℂ) (u : ℂ) A a‖ ≤ 2 ^ n * M := by
  have hut' : ∀ i, ‖(u : ℂ) * ξ i‖ < 1 := fun i => by
    rw [norm_real_mul u hu0 (ξ i)]
    exact (back_bound_real hu0 hut ht1 (norm_nonneg (ξ i)) (hξ i)).1
  have hC : ∀ i, 1 + ‖((t : ℂ) - (u : ℂ)) * ξ i‖ * (1 - ‖(u : ℂ) * ξ i‖)⁻¹ ≤ 2 := fun i => by
    have hcast : (t : ℂ) - (u : ℂ) = ((t - u : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, norm_real_mul (t - u) (by linarith) (ξ i), norm_real_mul u hu0 (ξ i)]
    exact (back_bound_real hu0 hut ht1 (norm_nonneg (ξ i)) (hξ i)).2
  exact norm_Uker_apply_le L hL hut' hM0 hC hA a

end Kernel

section Grid

variable (L : ℕ) [NeZero L]

end Grid

end RBM
