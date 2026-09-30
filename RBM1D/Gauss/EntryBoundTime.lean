/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDENetClose
import RBM1D.Green.EntryBoundFloor

/-!
# Absorbing an additive floor in (4.2) and (4.3) along the flow

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4, (4.2) and (4.3).

The time-uniform large deviation estimates (`RBM1D/Gauss/LDENetClose.lean`) give (4.2) and
(4.3) along the flow only with an **additive floor** `N^{-B}` in the control: their unfloored,
time-uniform forms are equivalent to a polynomial lower bound on their own controls, and those
controls are exponentially small in the band distance.  The deterministic kernel of the floored
(4.2) is `RBM.norm_sq_green_le_blk_floor` (`RBM1D/Green/EntryBoundFloor.lean`).

## Why the floor costs nothing

The consumers of (4.2) and (4.3) along the flow compose them with controls that carry an
**unconditional** `W⁻¹`.  Since `3 W ≤ W L ≤ N` (`RBM.Gauss.Dims.dim` and `3 ≤ L`), the floor at
`B = 1` already satisfies `2 N⁻¹ ≤ W⁻¹`, and a constant added inside an indicator is absorbed by
a control that dominates it.

## Main results

* `RBM.Gauss.stochDom_indicator_add_const` — a constant added inside an indicator is absorbed
  by a control that dominates it.
* `RBM.Gauss.eventually_two_rpow_neg_one_le_W_inv`, `RBM.Gauss.eventually_rpow_neg_one_le_W_inv`
  — `2 N⁻¹ ≤ W⁻¹` and `N⁻¹ ≤ W⁻¹` eventually.
* `RBM.Gauss.stochDom_normSq_Hflow_diag_idx` — the diagonal input `‖H_{u,ii}‖² ≺ S_{ii}` of (4.3)
  with the time inside the index set.  Widening the index set of the fixed-time
  `RBM.Gauss.stochDom_normSq_Hflow_diag` is free: `‖H_{u,ii}‖² = u ‖X_{ii}‖²` is monotone in `u`,
  and the control `S_{ii}` does not depend on `u`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

/-! ### (4.2) and (4.3) along the flow: absorbing the floor -/

section Flow

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

/-! ### Absorbing the floor at the consumer -/

section Absorb

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {U : ℕ → Type*}

/-- **A constant added inside an indicator is absorbed by a control that dominates it.**

If `1_A f ≺ ζ` and the constant `c_N` is eventually at most `ζ` itself, then
`1_A (f + c_N) ≺ ζ`: the factor `N^τ` in the definition of `≺` has room to spare. -/
theorem stochDom_indicator_add_const {A : ∀ N, U N → Set Ω} {f ζ : ∀ N, U N → Ω → ℝ}
    {c : ℕ → ℝ} (h : StochDom P (fun N u ω => (A N u).indicator (f N u) ω) ζ)
    (hζ0 : ∀ N u ω, 0 ≤ ζ N u ω)
    (hc : ∀ᶠ N : ℕ in atTop, ∀ u ω, c N ≤ ζ N u ω) :
    StochDom P (fun N u ω => (A N u).indicator (fun ω => f N u ω + c N) ω) ζ := by
  refine StochDom.of_subset h fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [hc, eventually_le_rpow 2 (show (0 : ℝ) < τ / 2 by linarith),
    Filter.eventually_ge_atTop 1] with N hcN h2 hN1
  rintro ω ⟨u, hu⟩
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hζ := hζ0 N u ω
  have hcu := hcN u ω
  refine ⟨u, ?_⟩
  show (N : ℝ) ^ (τ / 2) * ζ N u ω < (A N u).indicator (f N u) ω
  replace hu : (N : ℝ) ^ τ * ζ N u ω < (A N u).indicator (fun ω => f N u ω + c N) ω := hu
  by_cases hmem : ω ∈ A N u
  · rw [Set.indicator_of_mem hmem] at hu ⊢
    rw [hsplit] at hu
    set x : ℝ := (N : ℝ) ^ (τ / 2) with hx
    have hpos : (0 : ℝ) ≤ x * x - x - 1 := by nlinarith
    nlinarith [mul_nonneg hζ hpos]
  · rw [Set.indicator_of_notMem hmem] at hu
    exact absurd hu (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) hζ))

end Absorb

section Consumer

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {Φ : ∀ N, RBM.TimeIcc s t N → ℝ}

/-- `2 N⁻¹ ≤ W⁻¹` eventually: `3 W ≤ W L ≤ N` by `RBM.Gauss.Dims.dim` and `3 ≤ L`. -/
theorem eventually_two_rpow_neg_one_le_W_inv (d : Dims) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (-(1 : ℝ)) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by
  filter_upwards [d.dim] with N hdim
  have hW : 0 < d.W N := d.W_pos N
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hWN : 3 * d.W N ≤ N := by
    have h3 : 3 * d.W N ≤ d.L N * d.W N := Nat.mul_le_mul hL (le_refl (d.W N))
    have hcm : d.L N * d.W N = d.W N * d.L N := Nat.mul_comm _ _
    have hd := hdim.1
    omega
  have hW' : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast hW
  have hN' : (0 : ℝ) < (N : ℝ) := by
    have : 0 < 3 * d.W N := by omega
    have : 0 < N := by omega
    exact_mod_cast this
  have hWN' : 3 * (d.W N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hWN
  have he : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := by
    rw [Real.rpow_neg hN'.le, Real.rpow_one]
  rw [he, inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hN' hW']
  linarith

/-! ### (4.3) along the flow: the diagonal input -/

/-- **The diagonal input of (4.3) with the time inside the index set.**

`RBM.Gauss.stochDom_normSq_Hflow_diag` fixes the time `u`.  Widening the index set costs
nothing: `‖H_{u,ii}‖² = u ‖X_{ii}‖²` is monotone in `u`, so for `u ≤ 1` the failure event at any
time is contained in the failure event at `u = 1`, and the control `S_{ii}` does not depend on
the time at all. -/
theorem stochDom_normSq_Hflow_diag_idx {U : ℕ → Type*} (uf : ∀ N, U N → ℝ)
    (hu0 : ∀ N q, 0 ≤ uf N q) (hu1 : ∀ N q, uf N q ≤ 1) :
    StochDom (P d)
      (fun N (q : U N × BIdx d.L d.W N) ω => ‖Hflow d N (uf N q.1) ω q.2 q.2‖ ^ 2)
      (fun N (q : U N × BIdx d.L d.W N) _ => Sblk (d.L N) (d.W N) q.2 q.2) := by
  have h := stochDom_normSq_Hflow_diag (d := d) (u := 1) zero_le_one
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  rintro ω ⟨q, hq⟩
  refine Set.mem_union_left _ ⟨q.2, ?_⟩
  have e1 : ‖Hflow d N (uf N q.1) ω q.2 q.2‖ ^ 2
      = uf N q.1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 := normSq_Hflow_diag (hu0 N q.1) ω q.2
  have e2 : ‖Hflow d N 1 ω q.2 q.2‖ ^ 2
      = 1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 := normSq_Hflow_diag zero_le_one ω q.2
  have hsq : (0 : ℝ) ≤ (ω ⟨N, q.2, q.2, true⟩) ^ 2 := sq_nonneg _
  have hmono : uf N q.1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 ≤ 1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 :=
    mul_le_mul_of_nonneg_right (hu1 N q.1) hsq
  show (N : ℝ) ^ τ * Sblk (d.L N) (d.W N) q.2 q.2 < ‖Hflow d N 1 ω q.2 q.2‖ ^ 2
  rw [e2]
  have hq' : (N : ℝ) ^ τ * Sblk (d.L N) (d.W N) q.2 q.2
      < ‖Hflow d N (uf N q.1) ω q.2 q.2‖ ^ 2 := hq
  rw [e1] at hq'
  linarith

/-! ### Absorbing the (4.3) floor at the consumer -/

/-- `N⁻¹ ≤ W⁻¹` eventually — the `B = 1` floor of (4.3), which carries no factor `2`, is a
fortiori below the bound of `RBM.Gauss.eventually_two_rpow_neg_one_le_W_inv`. -/
theorem eventually_rpow_neg_one_le_W_inv (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by
  filter_upwards [eventually_two_rpow_neg_one_le_W_inv d] with N hN
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

end Consumer

end Flow

end RBM.Gauss
