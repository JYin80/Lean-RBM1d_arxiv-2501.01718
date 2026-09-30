/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridJStar
import RBM1D.EnergyN.Gauss.Step2Eq557
import RBM1D.EnergyN.Gauss.EntryBoundTime
import RBM1D.EnergyN.Hierarchy.Step1

/-!
# The events of (2.73) and (5.57) along the flow and on the grid, at an `N`-dependent energy

Four statements at an `N`-dependent energy `E : ℕ → ℝ`: with high probability the flow lies in
`eq273Set` and in `eq557Set` at all times `u ∈ [s, t]`
(`RBM.Gauss.Grid.highProb_flow_eq273N`, `RBM.Gauss.Grid.highProb_flow_eq557N`), and the grid
process lies in them at all grid times (`RBM.Gauss.Grid.highProb_grid_eq273N`,
`RBM.Gauss.Grid.highProb_grid_eq557N`). No energy-dependent constant is fixed in them.

All four take an external `κ` (`{κ} (hκ) {E} (hE : ∀ N, |E N| ≤ 2 - κ)`). `jSMat`, `eq273Set`,
`measurableSet_eq273Set`, `eq557Set`, `measurableSet_eq557Set`, `mem_Icc_time` and the generic
transfer combinator `highProb_grid_of_flow` (no `E`-binder of its own: it takes an abstract
measurable matrix-set family `S`) are deterministic per fixed `(E, N, u)` or fully `E`-free, and
are used at `E N`. `highProb_flow_eq273N`/`highProb_flow_eq557N` use `highProb_eq557_colN`
(`Step2Eq557.lean`) and `step1Hyp_gauss_of_scale''N`/`Step1.aprioriN`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! #### `(2.73)` -/

/-- **With high probability `Hflow u ∈ eq273Set` for all `u ∈ [s, t]`** (the bound (2.73) for loops
of length `n`). No energy-dependent constant is fixed here: `κ` is explicit. -/
theorem highProb_flow_eq273N {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) (hτ : 0 < τ) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈ eq273Set d (E N) N n (u : ℝ) ((band d).ell N (s N)) τ}) := by
  have hStep : Step1.HypN (sample d) E s t :=
    step1Hyp_gauss_of_scale''N d hκ hE hB hs0 hst ht1 hcond hc0 hreg
  have hApriori := Step1.aprioriN (sample d) hκ hE hB hs0 hst ht1 hcond hc0 hreg hStep n hn
  have hHP := hApriori.highProb hτ
  apply hHP.mono
  filter_upwards with N ω hω u v
  exact (hω (u, v)).trans_eq (by ring)

/-- **The grid form of `highProb_flow_eq273N`**: with high probability the grid process lies in
`eq273Set` at all grid times, via the generic (`E`-free) `highProb_grid_of_flow`. -/
theorem highProb_grid_eq273N {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) (hτ : 0 < τ) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s t K N k ω ∈ eq273Set d (E N) N n (time s t K N k) ((band d).ell N (s N)) τ}) :=
  highProb_grid_of_flow d s t K hs0 hst hK0 hC0 hKcard
    (fun N u => eq273Set d (E N) N n u ((band d).ell N (s N)) τ)
    (fun N u => measurableSet_eq273Set d (E N) N n u ((band d).ell N (s N)) τ)
    (highProb_flow_eq273N d hκ hE hB hs0 hst ht1 hcond hc0 hreg n hn τ hτ)

/-! #### `(5.57)` -/

/-- **With high probability `Hflow u ∈ eq557Set` for all `u ∈ [s, t]`** (the bound (5.57)). It uses
`Gauss.Step2.highProb_eq557_colN`. -/
theorem highProb_flow_eq557N {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (τ : ℝ) (hτ : 0 < τ) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈ eq557Set d (E N) N (u : ℝ) ((band d).ell N (s N)) τ}) := by
  have hHP := Gauss.Step2.highProb_eq557_colN d hκ hE hB hs0 hst ht1 hcond hc0 hreg τ hτ
  apply hHP.mono
  filter_upwards with N ω hω u x y p hp
  exact hω u x y p hp

/-- **The grid form of `highProb_flow_eq557N`**, via the generic (`E`-free)
`highProb_grid_of_flow`. -/
theorem highProb_grid_eq557N {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    (τ : ℝ) (hτ : 0 < τ) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s t K N k ω ∈ eq557Set d (E N) N (time s t K N k) ((band d).ell N (s N)) τ}) :=
  highProb_grid_of_flow d s t K hs0 hst hK0 hC0 hKcard
    (fun N u => eq557Set d (E N) N u ((band d).ell N (s N)) τ)
    (fun N u => measurableSet_eq557Set d (E N) N u ((band d).ell N (s N)) τ)
    (highProb_flow_eq557N d hκ hE hB hs0 hst ht1 hcond hc0 hreg τ hτ)

section Compat

end Compat

end RBM.Gauss.Grid

end
