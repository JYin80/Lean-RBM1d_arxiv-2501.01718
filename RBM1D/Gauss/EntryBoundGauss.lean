/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuadDom

/-!
# Lemma 4.1 for the Gaussian model, with no large deviation hypotheses — T97

`RBM.entry_bound_stochDom` ((4.2)) and `RBM.diag_bound_stochDom` ((4.3)) of
`RBM1D/Green/EntryBound.lean` carry the paper's large deviation estimates as hypotheses,
because the paper takes them from `[39, Lemma 3.3]`.  For the Gaussian flow `H_u = √u X` all
four are now theorems:

| hypothesis | proved in |
| --- | --- |
| `hLrow`  | `RBM.Gauss.stochDom_ldeRow` (T91) |
| `hLcol`  | `RBM.Gauss.stochDom_ldeCol` (T91) |
| `hLdiag` | `RBM.Gauss.stochDom_normSq_Hflow_diag` (T92) |
| `hLquad` | `RBM.Gauss.stochDom_ldeQuad` (T96) |

This file is the assembly: (4.2) and (4.3) hold for the Gaussian flow with no large deviation
input at all.  Nothing here is new mathematics; it is the point where the two halves of the
project meet.

## Main statements

* `RBM.Gauss.entry_bound_gauss` : (4.2) for `H_u = √u X`
* `RBM.Gauss.diag_bound_gauss`  : (4.3) for `H_t = √t X`
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

variable {d : Dims}

/-- **Lemma 4.1, (4.2), for the Gaussian flow.**  `1_Ω |G_{ij}|² ≺ ∑ L_{(+,-)} + W⁻¹1(|[i]-[j]|≤1)`
uniformly in `i ≠ j`, with **no** large deviation hypothesis: the row and column estimates are
`RBM.Gauss.stochDom_ldeRow` and `RBM.Gauss.stochDom_ldeCol`. -/
theorem entry_bound_gauss {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {z : ℂ} (hz : z.im ≠ 0)
    {m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) :
    StochDom (P d)
      (fun N (p : OffPair d.L d.W N) ω =>
        (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N u ω) z m δ N).indicator
          (fun ω => ‖green (Hflow d N u ω) z p.1.1 p.1.2‖ ^ 2) ω)
      (fun N (p : OffPair d.L d.W N) ω =>
        (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N u ω) z (p.1.2.1 + b) (p.1.1.1 + a))
          + if p.1.1.1 - p.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) :=
  entry_bound_stochDom (P d) (L := d.L) (W := d.W) d.three_le_L
    (fun N ω => Hflow d N u ω) (fun N ω => Hflow_isHermitian d N u ω) hz hm hδ0 hc₀ hδ
    (stochDom_ldeRow d hu0 hu1 hz) (stochDom_ldeCol d hu0 hu1 hz)

/-- **Lemma 4.1, (4.3), for the Gaussian flow.**  `1_Ω |G_{ii} - m(E)|² ≺ max L_{(+,-)}`
uniformly in `i`, with **no** large deviation hypothesis: the four estimates are
`RBM.Gauss.stochDom_ldeRow`, `RBM.Gauss.stochDom_ldeCol`, `RBM.Gauss.stochDom_ldeQuad` and
`RBM.Gauss.stochDom_normSq_Hflow_diag`. -/
theorem diag_bound_gauss {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) :
    StochDom (P d)
      (fun N (i : BIdx d.L d.W N) ω =>
        (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ N).indicator
          (fun ω => ‖green (Hflow d N t ω) (zt E t) i i - mE E‖ ^ 2) ω)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hzt : (zt E t).im ≠ 0 := zt_im_ne_zero hκ0 hE ht1
  exact diag_bound_stochDom (P d) (L := d.L) (W := d.W) d.three_le_L
    (fun N ω => Hflow d N t ω) (fun N ω => Hflow_isHermitian d N t ω)
    hκ0 hκ1 hE ht0 ht1 hδ0 hc₀ hδ
    (stochDom_ldeRow d ht0 ht1.le hzt) (stochDom_ldeCol d ht0 ht1.le hzt)
    (stochDom_ldeQuad hzt ht0 ht1.le) (stochDom_normSq_Hflow_diag ht0)

end RBM.Gauss
