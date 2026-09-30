/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.Gauss.Eq45Flow
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.Step2Close
import RBM1D.Gauss.Step2Plain

/-!
# The sharp one-loop bound `Ξ₁ ≺ 1` at a grid point: the scale arithmetic

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.5) composed with (2.76): the `Ξ₁` input of `goodSet514`.

The sharp block-average bound `‖trace((G_u - m) E_a)‖ ≺ Ψ_N · Ψ_N` at one deterministic grid
time `u_N` is a bound on the `1`-loop: `RBM.Gauss.lkErr_one_eq_norm_trace` shows the `1`-loop
`L - K` **is** this block average for either charge — `σ = -` differs only by a complex
conjugation that the norm does not see.  Choosing the control `Ψ_N` to be the **tight**
per-point local-law scale `(scale_{u_N})⁻¹^{1/2}` (not an interval-uniform majorant) gives
`scale_{u_N} · Ψ_N · Ψ_N = 1` exactly, i.e. the sharp bound `Ξ^{(L-K)}_{u_N,1} ≺ 1` at that grid
point.  This file proves the arithmetic of that choice.

## Main results

* `RBM.Gauss.scale_mul_inv_rpow_half_sq` — `scale_u · Ψ_u · Ψ_u = 1` for
  `Ψ_u = (scale_u)⁻¹^{1/2}`.
* `RBM.Gauss.W_rpow_neg_half_le_scale_inv_rpow_half` — the bandwidth floor `W^{-1/2} ≤ Ψ_u`.
* `RBM.Gauss.band_scale_antitone` — `u ↦ W ℓ_u η_u` is antitone.
* `RBM.Gauss.scale_inv_rpow_half_le_of_rpow_le` — `N^c ≤ scale_u` gives `Ψ_u ≤ N^{-c/2}`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

section OneLoopSharpGrid

variable (d : Dims)

/-- **The arithmetic identity `scale_u · Ψ_u · Ψ_u = 1`** for the tight pointwise scale
`Ψ_u := (scale_u)⁻¹^{1/2}`. -/
theorem scale_mul_inv_rpow_half_sq {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (band d).scale E N u *
      (((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) * ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2))
      = 1 := by
  have hx : 0 < (band d).scale E N u := (band d).scale_pos' hE N hu0 hu1
  have hxi : 0 < ((band d).scale E N u)⁻¹ := inv_pos.mpr hx
  rw [← Real.rpow_add hxi, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one,
    mul_inv_cancel₀ hx.ne']

/-- **The bandwidth floor of the tight scale is automatic**: `W^{-1/2} ≤ (scale_u)⁻¹^{1/2}`, from
`scale_u = W ℓ_u η_u ≤ W` (`RBM.Gauss.Grid.DriftPt.scale_le_W`). -/
theorem W_rpow_neg_half_le_scale_inv_rpow_half {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) := by
  have hx : 0 < (band d).scale E N u := (band d).scale_pos' hE N hu0 hu1
  have hW : (band d).scale E N u ≤ (d.W N : ℝ) := Grid.DriftPt.scale_le_W (band d) hE N hu0 hu1
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  rw [neg_div, Real.rpow_neg hw.le, ← Real.inv_rpow hw.le]
  exact Real.rpow_le_rpow (inv_nonneg.mpr hw.le) (inv_anti₀ hx hW) (by norm_num)

/-- `u ↦ W ℓ_u η_u` is antitone on `(-∞, 1]` (`RBM.flowScale_antitoneOn`). -/
theorem band_scale_antitone {E : ℝ} {N : ℕ} {u v : ℝ} (huv : u ≤ v) (hv1 : v ≤ 1) :
    (band d).scale E N v ≤ (band d).scale E N u := by
  change flowScale ((band d).W N : ℝ) ((band d).L N) E v ≤
    flowScale ((band d).W N : ℝ) ((band d).L N) E u
  exact flowScale_antitoneOn (Nat.cast_nonneg _) _ _
    (Set.mem_Iic.mpr (le_trans huv hv1)) (Set.mem_Iic.mpr hv1) huv

/-- The polynomial lower bound `N^c ≤ scale_u` gives `(scale_u)⁻¹^{1/2} ≤ N^{-c/2}`. -/
theorem scale_inv_rpow_half_le_of_rpow_le {E c : ℝ} {N : ℕ} {u : ℝ} (hN1 : 1 ≤ N)
    (h : (N : ℝ) ^ c ≤ (band d).scale E N u) :
    ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(c / 2)) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNc : 0 < (N : ℝ) ^ c := Real.rpow_pos_of_pos hn0 _
  have hx : 0 < (band d).scale E N u := hNc.trans_le h
  have h1 : ((band d).scale E N u)⁻¹ ≤ (N : ℝ) ^ (-c) := by
    rw [Real.rpow_neg hn0.le]
    exact inv_anti₀ hNc h
  calc
    ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) ^ (-c)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hx.le) h1 (by norm_num)
    _ = (N : ℝ) ^ (-(c / 2)) := by
      rw [← Real.rpow_mul hn0.le]
      ring_nf

end OneLoopSharpGrid

end RBM.Gauss

