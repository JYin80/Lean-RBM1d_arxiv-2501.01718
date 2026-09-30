/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Close
import RBM1D.EnergyN.Gauss.Step2Eq557
import RBM1D.EnergyN.Gauss.GridJStar

/-!
# The row form of (5.57) on the grid, at an `N`-dependent energy

`RBM.Gauss.Grid.highProb_grid_rowSetN`: with high probability the grid process lies in `rowSet`
at all grid times, at an `N`-dependent energy `E : ℕ → ℝ`. No energy-dependent constant is fixed
in this file: `κ` is explicit (`hE : ∀ N, |E N| ≤ 2 - κ`), and the proof uses
`Gauss.Step2.highProb_eq557_colRowN` (`Step2Eq557.lean`) and the generic (`E`-free)
`highProb_flow_restrict`/`highProb_grid_of_flow` (`GridJStar.lean`/`GridGoodSet.lean`).
`rowSet`/`measurableSet_rowSet` are energy-free, deterministic per fixed `(E, N)`, used at `E N`.
-/

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

/-- **The grid `HighProb` of the row form of (5.57)**, uniformly over grid indices `k ≤ K N`, for
a grid endpoint `u ∈ [s, t]` and polynomially many grid points. No energy-dependent constant is
fixed here: `κ` is explicit. -/
theorem highProb_grid_rowSetN (d : Dims) {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) (τ : ℝ) (hτ : 0 < τ)
    {u : ℕ → ℝ} (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s u K N k ω ∈ rowSet d (E N) N (time s u K N k) ((band d).ell N (s N)) τ}) := by
  have hflow : HighProb (P d) (fun N => {ω | ∀ v : TimeIcc s t N,
      Hflow d N (v : ℝ) ω ∈ rowSet d (E N) N (v : ℝ) ((band d).ell N (s N)) τ}) := by
    have h := Gauss.Step2.highProb_eq557_colRowN d hκ hE hB hs0 hst ht1 hcond hc0 hreg τ hτ
    refine h.mono (Filter.Eventually.of_forall fun N ω hω => ?_)
    intro v x y r hr
    exact (hω v x y).2 r hr
  have hflow' := highProb_flow_restrict d hut
    (fun N v => rowSet d (E N) N v ((band d).ell N (s N)) τ) hflow
  exact highProb_grid_of_flow d s u K hs0 hsu hK0 hC0 hKcard
    (fun N v => rowSet d (E N) N v ((band d).ell N (s N)) τ)
    (fun N v => measurableSet_rowSet d (E N) N v ((band d).ell N (s N)) τ) hflow'

section Compat

end Compat

end RBM.Gauss.Grid
