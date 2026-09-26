/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OneLoopSharpGrid
import RBM1D.Gauss.Lemma514Moment

/-!
# The sharp one-loop bound `Ξ₁ ≺ 1` simultaneously at all grid points (T1532)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.5) composed with (2.76), promoted from
`RBM.Gauss.stochDom_lkMax_one_of_steps12` (T1527, `OneLoopSharpGrid.lean`, a *single* fixed grid
point) to a statement that holds with high probability *simultaneously* at every point of a
discrete grid `s = u_0 < u_1 < ⋯ < u_{K N} = t`
with `K N + 1 ≤ N^C` (docs/reports/T1526-prove.md §1.4 PP-1(b), the `Ξ₁` input of `goodSet514`).

## Route (mandatory, per the ticket)

`docs/tickets/T1532.md` prescribes the route explicitly, and forbids `Grid.highProb_grid_of_flow`
(the generic grid transfer of `GridJStar.lean`): that lemma needs a **continuum-simultaneous**
input `HighProb (P d) (fun N => {ω | ∀ u ∈ [s N, t N], Hflow d N u ω ∈ S N u})`, which this ticket
does not have (and cannot get from a single-time producer without an extra Hölder-continuity
argument, which is exactly what the net engine `stochDom_timeIcc_of_unifDom` supplies elsewhere).
What is available is only a **pointwise, threshold-uniform** statement,
`RBM.Gauss.UnifDomIcc` (`Lemma514Moment.lean`): the same `(τ, D) ↦ N₀(τ, D)` works at *every*
single time `u ∈ [s N, t N]`, but the bound is not a probability of a joint (all-`u`) event.  The
route this file follows is therefore:

1. T1527's `stochDom_lkMax_one_of_steps12`, at an *arbitrary* grid-valued sequence `v`.
2. `RBM.Gauss.unifDomIcc_of_forall_stochDom` (`Lemma514Moment.lean:128`) turns "for every `v`, a
   `StochDom` at `v`" into a single `UnifDomIcc` object — the quantifier exchange is legitimate
   here because the thresholds `τ, D` of Definition 2.1 (i) sit *in front of* the `∀ᶠ N`, with no
   existential constant to smuggle a dependence on `u` back in.
3. `RBM.Gauss.Grid.map_H_eq` (`GridPath.lean:452`) transfers the resulting per-grid-point bound
   from the flow measure `P d` to the grid measure `Grid.Pg d`, at each individual grid index
   `k ≤ K N` (an *equality* of probabilities, since `map_H_eq` says the two one-time laws agree).
4. A union bound over the `(K N + 1) · #(LoopData (d.L N) 1)` many pairs `(k, v)` — polynomially
   many, since `K N + 1 ≤ N^C` (hypothesis) and `#(LoopData L 1) ≤ N^2` eventually
   (`RBM.Gauss.card_loopData_le`) — assembles the individual bounds into one `HighProb` statement
   via `RBM.HighProb.biInter`.

No Hölder/net-engine machinery is used or needed: the union is over the *grid* (polynomially many
points), not over the continuum.

## Main results

* `RBM.Gauss.highProb_grid_xiLK_one` (T1) — the sharp one-loop bound simultaneously at every grid
  point, both charges, from exactly `RBM.Gauss.steps12_gauss`'s hypothesis list (T1524, no `Hy`)
  plus a grid `(K, C)` with `K N + 1 ≤ N^C` and `K N ≠ 0`.

No `RBM.MomentDuhamel.Hyp`, `RBM.Step2.Hyp`, `RBM.EarlyQVRateEv.jStar`, `gmOfJS`-`h560` or
`exampleGrow` constant occurs in the dependency closure (checked below, §(b) of the prove
report); the A'-era declarations that do occur (through the merged `steps12_gauss`, exactly as in
T1527) are listed there (DECISIONS §10b).
-/

namespace RBM.Gauss

open MeasureTheory Filter

variable (d : Dims)

/-- **(T1)** The sharp one-loop bound `Ξ^{(L-K)}_{u_k,1} ≺ 1`, both charges, **simultaneously at
every grid point** `u_k = time s t K N k`, `k ≤ K N`, general `Dims`, from exactly
`RBM.Gauss.steps12_gauss`'s hypothesis list (T1524, no `Hy`) plus a grid resolution `K` with
`K N ≠ 0` and polynomially many points `K N + 1 ≤ N^C`.

The route is exactly the one the ticket mandates: T1527's pointwise `StochDom` at an arbitrary
grid-valued sequence, `RBM.Gauss.unifDomIcc_of_forall_stochDom` for the threshold-uniform
statement over `[s_N, t_N]`, `RBM.Gauss.Grid.map_H_eq` to transfer each individual grid-point bound
to the grid measure, and a union bound (`RBM.HighProb.biInter`) over the `(K N + 1) ×
#(LoopData (d.L N) 1)` many pairs `(k, v)`. `RBM.Gauss.Grid.highProb_grid_of_flow` is *not* used. -/
theorem highProb_grid_xiLK_one {κ E c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    {ε : ℝ} (hε : 0 < ε) :
    HighProb (Grid.Pg d) (fun N => {ω | ∀ k : Fin (K N + 1), ∀ v : LoopData (d.L N) 1,
      (band d).scale E N (Grid.time s t K N k)
        * lkErrMat d E N (Grid.time s t K N k) (Grid.H d s t K N k ω) v.idx
      ≤ (N : ℝ) ^ ε}) := by
  have hE' : |E| < 2 := by linarith
  -- Step 1 + 2: T1527's pointwise `StochDom` at every grid-valued sequence `v`, exchanged into a
  -- single threshold-uniform `UnifDomIcc` statement over `[s_N, t_N]`.
  have hunif : UnifDomIcc (P d) s t
      (fun N u (_ : Unit) ω => (band d).scale E N u * Sample.lkMax (sample d) E N u ω 1)
      (fun _ _ _ _ => (1 : ℝ)) :=
    unifDomIcc_of_forall_stochDom hst
      (fun v hv => stochDom_lkMax_one_of_steps12 d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg hv)
  -- The combined index `(k, v)` is polynomially large.
  have hcardV := card_loopData_le (B := band d) 1
  have hcard2 : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (K N + 1) × LoopData (d.L N) 1) : ℝ) ≤ (N : ℝ) ^ (C + 2) := by
    filter_upwards [hKcard, hcardV, eventually_ge_atTop 1] with N h1 h2 hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hpow1 : (0 : ℝ) ≤ (N : ℝ) ^ C := Real.rpow_nonneg hN0.le _
    have hcardnn : (0 : ℝ) ≤ (Fintype.card (LoopData (d.L N) 1) : ℝ) := Nat.cast_nonneg _
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc ((K N + 1 : ℕ) : ℝ) * (Fintype.card (LoopData (d.L N) 1) : ℝ)
        ≤ (N : ℝ) ^ C * (N : ℝ) ^ (((1 : ℕ) : ℝ) + 1) := mul_le_mul h1 h2 hcardnn hpow1
      _ = (N : ℝ) ^ (C + 2) := by rw [← Real.rpow_add hN0]; norm_num
  -- Rewrite the goal event as an intersection over the combined index `(k, v)`.
  have hset : ∀ N, {ω : Grid.Ωg d | ∀ k : Fin (K N + 1), ∀ v : LoopData (d.L N) 1,
      (band d).scale E N (Grid.time s t K N k)
        * lkErrMat d E N (Grid.time s t K N k) (Grid.H d s t K N k ω) v.idx
      ≤ (N : ℝ) ^ ε}
    = ⋂ p : Fin (K N + 1) × LoopData (d.L N) 1,
        {ω | (band d).scale E N (Grid.time s t K N p.1)
          * lkErrMat d E N (Grid.time s t K N p.1) (Grid.H d s t K N p.1 ω) p.2.idx
          ≤ (N : ℝ) ^ ε} := by
    intro N
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Prod.forall]
  simp only [hset]
  refine HighProb.biInter (by linarith : (0 : ℝ) ≤ C + 2) hcard2 ?_
  intro D hD
  filter_upwards [hunif ε hε D hD] with N hN
  rintro ⟨k, v⟩
  dsimp only
  -- Step 3 + 4: transfer the fixed-grid-point bound from the flow measure to the grid measure.
  set uk : ℝ := Grid.time s t K N k with huk
  have hmemk : uk ∈ Set.Icc (s N) (t N) :=
    Grid.mem_Icc_time s t K N k (hs0 N) (hst N) (Nat.lt_succ_iff.mp k.isLt)
  have hu0k : 0 ≤ uk := (hs0 N).trans hmemk.1
  have hu1k : uk < 1 := lt_of_le_of_lt hmemk.2 (ht1 N)
  have hHmeas : Measurable (Grid.H d s t K N k) :=
    (Grid.H_measurable_filt d s t K N k).mono ((Grid.filt d).le k) le_rfl
  have hHflowmeas : Measurable (Hflow d N uk) := RBM.measurable_H (sample d) N uk
  set Sgood : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
    {M | (band d).scale E N uk * lkErrMat d E N uk M v.idx ≤ (N : ℝ) ^ ε} with hSgood
  have hSmeas : MeasurableSet Sgood :=
    measurableSet_le ((measurable_lkErrMat d E N uk v.idx).const_mul _) measurable_const
  have hcompl_eq : (Grid.Pg d)
        {ω | (band d).scale E N uk * lkErrMat d E N uk (Grid.H d s t K N k ω) v.idx
          ≤ (N : ℝ) ^ ε}ᶜ
      = (P d)
        {ω' | (band d).scale E N uk * lkErrMat d E N uk (Hflow d N uk ω') v.idx
          ≤ (N : ℝ) ^ ε}ᶜ := by
    change (Grid.Pg d) ((Grid.H d s t K N k) ⁻¹' Sgood)ᶜ = (P d) ((Hflow d N uk) ⁻¹' Sgood)ᶜ
    rw [← Set.preimage_compl, ← Set.preimage_compl,
      ← Measure.map_apply hHmeas hSmeas.compl, ← Measure.map_apply hHflowmeas hSmeas.compl,
      Grid.map_H_eq s t K N k (hs0 N) (hst N) (hK0 N)]
  have hxpos : 0 < (band d).scale E N uk := (band d).scale_pos' hE' N hu0k hu1k
  have hsub : {ω' | (band d).scale E N uk * lkErrMat d E N uk (Hflow d N uk ω') v.idx
        ≤ (N : ℝ) ^ ε}ᶜ
      ⊆ {ω' | (N : ℝ) ^ ε * 1 < (band d).scale E N uk * Sample.lkMax (sample d) E N uk ω' 1} := by
    intro ω' hω'
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω'
    have hlkeq : lkErrMat d E N uk (Hflow d N uk ω') v.idx
        = (sample d).lkErr E N uk ω' v.idx := (lkErr_eq_lkErrMat d E N uk ω' v.idx).symm
    have hle : (band d).scale E N uk * lkErrMat d E N uk (Hflow d N uk ω') v.idx
        ≤ (band d).scale E N uk * Sample.lkMax (sample d) E N uk ω' 1 := by
      rw [hlkeq]
      exact mul_le_mul_of_nonneg_left (Sample.lkErr_le_lkMax (sample d) v) hxpos.le
    have hgt : (N : ℝ) ^ ε < (band d).scale E N uk * Sample.lkMax (sample d) E N uk ω' 1 :=
      lt_of_lt_of_le hω' hle
    simpa using hgt
  have hbound : (P d)
      {ω' | (band d).scale E N uk * lkErrMat d E N uk (Hflow d N uk ω') v.idx ≤ (N : ℝ) ^ ε}ᶜ
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
    le_trans (measure_mono hsub) (hN uk hmemk Unit.unit)
  rw [hcompl_eq]
  exact hbound

end RBM.Gauss

#print axioms RBM.Gauss.highProb_grid_xiLK_one
