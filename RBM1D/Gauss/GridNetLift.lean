/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder

set_option maxHeartbeats 4000000

/-!
# The net lift of (2.76) uniformly in `u ∈ [s_N, t_N]`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

The grid stopping argument, together with the single-time transfer `map_H_eq`, gives the (2.76)
bound at one fixed time `u(N)` for each sequence `u`.  The lift to the whole window
`u ∈ [s_N, t_N]`, uniformly, in the `√u·X` Gaussian model `sample d`, is deterministic (a
Hölder-1/2 modulus on `{‖X‖ ≤ N}`) and goes through the abstract net lemma
`RBM.Gauss.netLift_of_relaxed` (`RBM1D/Gauss/Step1Hyp.lean`).  This file supplies its elementary
estimates.

## Main results

* `RBM.Gauss.Grid.sqrt_abs_sub_le_rpow`, `RBM.Gauss.Grid.abs_exp_neg_sub_exp_neg_le`,
  `RBM.Gauss.Grid.inv_le_const_mul_inv_of_le_const_mul`,
  `RBM.Gauss.Grid.eventually_mul_rpow_le_mul_rpow` — the elementary estimates of the modulus.
* `RBM.Gauss.Grid.lkErr_eq_norm_lkT` — `lkErr` at the `2`-loop `pmLoop a b` is the norm of
  `SumZeroDyn.lkT` at charges `(+, -)`.
-/

namespace RBM
namespace Gauss
namespace Grid

open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator

/-! ### A generic exponent-comparison helper -/

/-- `C N^p ≤ κ N^q` eventually, for any fixed `C`, `κ > 0` and `p < q`. -/
theorem eventually_mul_rpow_le_mul_rpow (C κ : ℝ) (hκ : 0 < κ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ p ≤ κ * (N : ℝ) ^ q := by
  filter_upwards [eventually_const_mul_rpow_le_rpow (C / κ) hpq] with N hN
  have h2 : κ * ((C / κ) * (N : ℝ) ^ p) ≤ κ * (N : ℝ) ^ q :=
    mul_le_mul_of_nonneg_left hN hκ.le
  have h3 : κ * (C / κ) = C := by field_simp
  rwa [← mul_assoc, h3] at h2

/-- `√|u - u'| ≤ N^{-A/2}` from `|u - u'| ≤ N^{-A}`. -/
theorem sqrt_abs_sub_le_rpow {N : ℕ} {u u' A : ℝ} (h : |u - u'| ≤ (N : ℝ) ^ (-A)) :
    Real.sqrt |u - u'| ≤ (N : ℝ) ^ (-A / 2) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h1 : Real.sqrt |u - u'| ≤ Real.sqrt ((N : ℝ) ^ (-A)) := Real.sqrt_le_sqrt h
  have h2 : Real.sqrt ((N : ℝ) ^ (-A)) = (N : ℝ) ^ (-A / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]
    ring_nf
  rwa [h2] at h1

/-- `|exp(-x) - exp(-y)| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · -- `x ≤ y`: `exp(-x) ≥ exp(-y)` and `|x - y| = y - x`.
    have hex : Real.exp (-x) * ((x - y) + 1) ≤ Real.exp (-x) * Real.exp (x - y) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
    rw [← Real.exp_add, show -x + (x - y) = -y from by ring] at hex
    have hex1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hd1 : Real.exp (-x) - Real.exp (-y) ≤ y - x := by nlinarith [hex, hex1]
    have hd2 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    have hxy2 : |x - y| = y - x := by rw [abs_of_nonpos (by linarith : x - y ≤ 0)]; ring
    rw [hxy2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (-x) - Real.exp (-y))]
    exact hd1
  · -- `y ≤ x`: symmetric.
    have hey : Real.exp (-y) * ((y - x) + 1) ≤ Real.exp (-y) * Real.exp (y - x) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
    rw [← Real.exp_add, show -y + (y - x) = -x from by ring] at hey
    have hey1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hd1 : Real.exp (-y) - Real.exp (-x) ≤ x - y := by nlinarith [hey, hey1]
    have hd2 : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    have hxy2 : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [hxy2, abs_of_nonpos (by linarith : Real.exp (-x) - Real.exp (-y) ≤ 0)]
    linarith [hd1]

/-! ### (T1) -/

/-! ### More generic helpers, for (T2) -/

/-- `b⁻¹ ≤ κ a⁻¹` from `a ≤ κ b` (positive `a, b`). -/
theorem inv_le_const_mul_inv_of_le_const_mul {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ κ * b) : b⁻¹ ≤ κ * a⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hb ha]
  nlinarith [h]

/-- The charge vector `(+, -)` and the bridge to `pmLoop`. -/
theorem idx_mySig {L : ℕ} (a b : ZMod L) :
    LoopData.idx ((![true, false] : Fin 2 → Bool), (![a, b] : LoopArg L 2)) = pmLoop a b := by
  simp [LoopData.idx, pmLoop, List.ofFn_succ]

/-- `lkErr` at the `2`-loop `pmLoop a b` is the norm of `SumZeroDyn.lkT` at charges `(+, -)`. -/
theorem lkErr_eq_norm_lkT {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) (E : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω) (a b : ZMod (B.L N)) :
    X.lkErr E N u ω (pmLoop a b) =
      ‖SumZeroDyn.lkT X E N u ω (![true, false]) (![a, b] : LoopArg (B.L N) 2)‖ := by
  rw [SumZeroDyn.norm_lkT, idx_mySig]

/-! ### (T2) -/

end Grid
end Gauss
end RBM
