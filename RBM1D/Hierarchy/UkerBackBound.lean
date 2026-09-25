/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel
import RBM1D.Gauss.GridPath

/-!
# T1500: a quantitative max-norm bound for the backward evolution kernel

Ticket T1500 (`docs/tickets/T1500.md`), pilot doc §9 repair (A). The backward kernel
`U_{u_{j+1},u_k} = U_{u_k,t}^{-1} U_{u_{j+1},t}` uses, by T1485's `Uker_factor`
(`RBM.Gauss.Grid.Uker_factor`), the explicit inverse `U_{u_k,t}^{-1} = Uker ξ t u_k`, i.e.
`RBM.Uker`/`RBM.edgeKer` run with the *large* time first and the *small* time second. This file
supplies the missing quantitative bound, **uniform in the earlier time `u ∈ [0,t]`**, needed for
the Doob/Azuma step of the A5 assembly (the martingale `M̃_k`).

## Step 0 finding

For `0 ≤ u ≤ t < 1` and `‖ξ‖ ≤ 1` the row `l^1` bound of the single back-edge is
`1 + (t-u)·‖ξ‖·(1-u‖ξ‖)⁻¹`, and this quantity **is** bounded by `2` on the whole hypothesis
range, *including the boundary `‖ξ‖ = 1` exactly*: the slack comes from the ticket's own strict
hypothesis `t < 1`, which forces `t‖ξ‖ ≤ t < 1 ≤ 1`, and `t‖ξ‖ ≤ 1` is exactly what is needed to
push `(t-u)‖ξ‖ ≤ 1-u‖ξ‖`. The constant `2` is only approached (never exceeded) as `t → 1⁻`,
`‖ξ‖ → 1`, `u → 0`. So the ticket's proposed constant `2` is **confirmed**, not falsified; no
alternate constant is used.

## Main results

* `RBM.sum_norm_edgeKer_back_row_le` : (T1), the row bound `≤ 1 + (t-u)‖ξ‖(1-u‖ξ‖)⁻¹ ≤ 2`.
* `RBM.norm_Uker_back_le`            : (T2), the `2^n` max-norm bound for `Uker L ξ t u`,
  uniform in `u ∈ [0,t]`.
* `RBM.norm_Uker_back_grid_le`       : (T3), the same bound instantiated at T1481's grid times
  `u = Gauss.Grid.time s t K N k`, `k ≤ K N`.
-/

namespace RBM

open Matrix Finset

section Arithmetic

/-- The complex norm of a nonnegative real scalar times `ξ`, in real terms. -/
private lemma norm_real_mul (r : ℝ) (hr : 0 ≤ r) (ξ : ℂ) : ‖(r : ℂ) * ξ‖ = r * ‖ξ‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The purely real arithmetic core of (T1): given `0 ≤ u ≤ t < 1` and `0 ≤ r ≤ 1`,
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

/-- **(T1)**: the row `l^1` norm of the *backward* edge factor `edgeKer L ξ t u`
(large time `t` first, small time `u` second — the direction `Uker_factor`'s inverse uses) is at
most `1 + (t-u)‖ξ‖(1-u‖ξ‖)⁻¹`, and that quantity never exceeds `2` on `0 ≤ u ≤ t < 1`,
`‖ξ‖ ≤ 1` (including the boundary `‖ξ‖ = 1`; see the module docstring). -/
theorem sum_norm_edgeKer_back_row_le (hL : 3 ≤ L) {u t : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t)
    (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (x : ZMod L) :
    (∑ c : ZMod L, ‖edgeKer L ξ (t : ℂ) (u : ℂ) x c‖
        ≤ 1 + (t - u) * ‖ξ‖ * (1 - u * ‖ξ‖)⁻¹) ∧
      1 + (t - u) * ‖ξ‖ * (1 - u * ‖ξ‖)⁻¹ ≤ 2 := by
  have hbound := back_bound_real hu0 hut ht1 (norm_nonneg ξ) hξ
  have hut' : ‖(u : ℂ) * ξ‖ < 1 := by rw [norm_real_mul u hu0 ξ]; exact hbound.1
  refine ⟨?_, hbound.2⟩
  have hrow := sum_norm_edgeKer_row_le L (s := (t : ℂ)) hL hut' x
  have heq : ‖((t : ℂ) - (u : ℂ)) * ξ‖ = (t - u) * ‖ξ‖ := by
    have hcast : (t : ℂ) - (u : ℂ) = ((t - u : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, norm_real_mul (t - u) (by linarith) ξ]
  have heq2 : ‖(u : ℂ) * ξ‖ = u * ‖ξ‖ := norm_real_mul u hu0 ξ
  rwa [heq, heq2] at hrow

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

/-- Arithmetic bracket for T1481's grid times: `0 ≤ time ≤ t N` for `k ≤ K N`,
given `0 ≤ s N ≤ t N` and `K N ≠ 0`. -/
private lemma grid_time_mem (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (hK : K N ≠ 0)
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (hk : k ≤ K N) :
    0 ≤ Gauss.Grid.time s t K N k ∧ Gauss.Grid.time s t K N k ≤ t N := by
  have hK' : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  have hKpos : (0 : ℝ) < (K N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hstep0 : 0 ≤ Gauss.Grid.step s t K N := by
    unfold Gauss.Grid.step
    exact div_nonneg (by linarith) hKpos.le
  have hkcast : (k : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hk
  have hkstep_le : (k : ℝ) * Gauss.Grid.step s t K N ≤ (K N : ℝ) * Gauss.Grid.step s t K N :=
    mul_le_mul_of_nonneg_right hkcast hstep0
  have hKstep : (K N : ℝ) * Gauss.Grid.step s t K N = t N - s N := by
    unfold Gauss.Grid.step
    rw [mul_div_cancel₀ _ hK']
  have hk_nonneg : 0 ≤ (k : ℝ) * Gauss.Grid.step s t K N := mul_nonneg (Nat.cast_nonneg k) hstep0
  constructor
  · change 0 ≤ s N + (k : ℝ) * Gauss.Grid.step s t K N
    linarith
  · change s N + (k : ℝ) * Gauss.Grid.step s t K N ≤ t N
    rw [hKstep] at hkstep_le
    linarith

/-- **(T3)**: the `2^n` bound of (T2) at T1481's grid times `u = time s t K N k`, for every
`k ≤ K N` — the concrete instantiation matching the inverse kernel `Uker ξ t (time …)` produced
by `RBM.Gauss.Grid.Uker_factor`. -/
theorem norm_Uker_back_grid_le (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (hK : K N ≠ 0) (hs0 : 0 ≤ s N) (hst : s N ≤ t N)
    (ht1 : t N < 1) (hk : k ≤ K N)
    {M : ℝ} (hM0 : 0 ≤ M) {A : LoopArg L n → ℂ} (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L n) :
    ‖Uker L ξ (t N : ℂ) (Gauss.Grid.time s t K N k : ℂ) A a‖ ≤ 2 ^ n * M := by
  obtain ⟨hu0, hut⟩ := grid_time_mem s t K N k hK hs0 hst hk
  exact norm_Uker_back_le L hL hξ hu0 hut ht1 hM0 hA a

end Grid

end RBM
