Prover model: claude-sonnet-5

# T1532 — G1c (Step 3): the sharp `Ξ₁ ≺ 1` bound simultaneously at all grid points (PP-1(b))

Branch `t/T1532`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1532`. Sole writable file
`RBM1D/Gauss/OneLoopSharpGridAll.lean`. Dependency: T1527 (merged, `RBM1D/Gauss/OneLoopSharpGrid.lean`).

Materials read (only these, per the ticket): `CLAUDE.md` §3; `docs/tickets/T1532.md`;
`docs/reports/T1527-prove.md`, `docs/reports/T1527-audit.md`; `RBM1D/Gauss/OneLoopSharpGrid.lean`;
the statements of `RBM.Gauss.Grid.map_H_eq` (`GridPath.lean:452`), `RBM.Gauss.Grid.mem_Icc_time`
(`GridJStar.lean:187`), `RBM.Gauss.UnifDomIcc`/`unifDomIcc_of_forall_stochDom`/`card_loopData_le`
(`Lemma514Moment.lean`), `RBM.Gauss.lkErrMat`/`measurable_lkErrMat`/`lkErr_eq_lkErrMat`
(`Step2Gauss.lean`), `RBM.HighProb`/`RBM.StochDom` (`Defs/StochDom.lean`), `RBM.Sample.lkMax`/
`lkErr_le_lkMax` (`Hierarchy/Step3.lean`), `RBM.Gauss.Grid.H_measurable_filt`/`filt`
(`GridStopFilt.lean`, `GridPath.lean`).

## (a) Math preflight (written before any Lean of this round)

### (T1) `RBM.Gauss.highProb_grid_xiLK_one`

* **Statement vs paper.** Lemma 4.1 (4.5) composed with (2.76) at `n = 1`, both charges, held
  simultaneously at every point of a discrete grid `u_k = time(s,t,K,N,k)`, `k = 0,…,K N`
  (`docs/reports/T1526-prove.md` §1.4 PP-1(b), the `Ξ₁` input of `goodSet514`). The conclusion is
  `HighProb (Grid.Pg d) {ω | ∀ k ≤ K N, ∀ v : LoopData(d.L N,1), scale(u_k)·lkErrMat(u_k,H_k ω,v.idx)
  ≤ N^ε}`; `LoopData (d.L N) 1 = (Fin 1 → Bool) × (Fin 1 → ZMod (d.L N))`, so `∀ v` ranges over both
  charge bits (`Bool`) simultaneously — literally "both charges" as required.  `scale·lkErr(v.idx) ≤
  N^ε` for **every** `v` is equivalent to `scale·lkMax(·,1) ≤ N^ε` (finite sup ≤ c ↔ every summand ≤
  c), so this is exactly T1527's pointwise conclusion, now stated at every grid point at once.
* **Hypotheses.** Exactly `steps12_gauss`'s list (`hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`, T1524, no
  `Hy`), plus a grid resolution `K : ℕ → ℕ` with `hK0 : ∀N, K N ≠ 0` (needed by `map_H_eq`) and
  `hC0 : 0 ≤ C`, `hKcard : ∀ᶠN, (K N+1 : ℝ) ≤ N^C` (the ticket's "K polynomial"), plus `ε > 0`.  No
  hypothesis is dropped, weakened, or added beyond the grid data the ticket itself names.
* **Quantifier order.** `d, κ, E, c, s, t, K, C, ε` are all fixed (theorem parameters) before
  `HighProb`'s own `∀ D > 0, ∀ᶠ N`.  In particular `ε` sits **before** the `∀ᶠ N` — the auditor's
  named check — exactly mirroring `RBM.StochDom.highProb`'s own quantifier placement.
* **Boundary cases.** `k = 0` (`u_0 = s N`) and `k = K N` (`u_{K N} = t N`) are both included
  (`Fin (K N + 1)`, i.e. `k ≤ K N`); `Grid.mem_Icc_time` covers the whole closed interval
  `[s N, t N]`, not an open/collapsed sub-window. `K N = 0` is excluded by `hK0` (a single-point
  grid `u_0 = s N` only, degenerate for `map_H_eq`'s division `step = (t-s)/K`); this is the
  ticket's own hypothesis, not a new restriction introduced here.
* **Dependencies (all already accepted).** `RBM.Gauss.stochDom_lkMax_one_of_steps12` (T1527,
  merged); `RBM.Gauss.unifDomIcc_of_forall_stochDom` (`Lemma514Moment.lean`, general quantifier
  exchange, no `MomentDuhamel`/`SumZeroDyn.Hierarchy` content — see the module docstring's own
  soundness argument, reproduced in the route section below); `RBM.Gauss.Grid.map_H_eq`
  (T1481, merged); `RBM.Gauss.Grid.mem_Icc_time`, `RBM.Gauss.Grid.H_measurable_filt`,
  `RBM.Gauss.Grid.filt`, `RBM.Gauss.card_loopData_le`, `RBM.Gauss.measurable_lkErrMat`,
  `RBM.Gauss.lkErr_eq_lkErrMat`, `RBM.Sample.lkErr_le_lkMax`, `RBM.HighProb.biInter` — all
  pre-existing, unconditional (no open hypothesis) lemmas/definitions.
* **Route soundness (the ticket's mandatory route, and why `highProb_grid_of_flow` is not used).**
  `RBM.Gauss.UnifDomIcc` (from step 2) is **not** a joint/continuum-simultaneous statement: its
  content is "for every `u ∈ [s_N,t_N]` *separately*, `P(bad event at u) ≤ N^{-D}}` with a single
  `N₀(τ,D)` that works for all `u`" — it says nothing about the probability that *several* `u`'s
  fail at once. `Grid.highProb_grid_of_flow`'s hypothesis `hFlow` is the strictly stronger
  continuum-joint statement `HighProb (P d) {ω | ∀ u ∈ [s_N,t_N], Hflow u ω ∈ S N u}` (a single
  event, probability of its complement bounded), which is not derivable from `UnifDomIcc` alone
  (that would need an extra Hölder-continuity/net argument, e.g.
  `stochDom_timeIcc_of_unifDom`, which this ticket does not invoke and does not need). The route
  here instead takes the union bound only over the **grid's own finitely many points** `u_k`,
  `k ≤ K N` (plus the finitely many `v : LoopData 1`), which is exactly what `UnifDomIcc`'s
  per-point bound supports via `HighProb.biInter`. `highProb_grid_of_flow` is confirmed **not**
  used (checked directly in the file and by the closure script, §(b)).
* **Simultaneous satisfiability (witness, paper argument, as in T1527's audited witness).**
  `steps12_gauss`'s witness carries over unchanged (T1527's report/audit, confirmed PASS):
  `d = Dims.exampleGrow`, `E = 0`, `κ=1`, `s ≡ 0`, `1-t_N = N^{-1/100}`, `c = 1/10` (used only as a
  witness, never as an input). The grid data `(K,C)` is an independent free parameter of this
  ticket; take `K N := N+1` (so `hK0` holds for **every** `N`, including `N=0`: `K 0 = 1 ≠ 0`) and
  `C := 2` (`hKcard`: `N+2 ≤ N^2` eventually, `N ≥ 2`). `ε` is any positive real, e.g. `ε := 1`.
  None of the four parameters (`d,E,s,t` vs `K,C,ε`) interact, so the joint witness is simply the
  product of the two independent witnesses: non-vacuous, no astronomically large quantity, no
  collapsed window (`K N ≥ 1`, so the grid genuinely has ≥ 2 points), and `N = 0` is not reached
  (all statements are `∀ᶠ N`/`∀ N` and hold at every `N`, with the interesting content eventual).
* **Step 0 checks (ticket-specific).** (i) the grid is arbitrary: `s, t, K` are all universally
  quantified (implicit) theorem parameters, not fixed to a specific sequence — confirmed by
  reading the final signature (§(b)); (ii) `ε` is quantified before `N` — confirmed above; (iii)
  both charges are in the bound (`v : LoopData (d.L N) 1` ranges over `Fin 1 → Bool` too) —
  confirmed above; (iv) `highProb_grid_of_flow` is not used — confirmed by the closure script
  (§(b), it does not appear as a node) and by direct inspection of the file's imports/proof term.
* **Verdict: PASS.**

## (b) Lean: declarations, build, axioms, closure

File `RBM1D/Gauss/OneLoopSharpGridAll.lean` (new), namespace `RBM.Gauss`.

### Declaration

```
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
      ≤ (N : ℝ) ^ ε})
```

Route implemented exactly as mandated: (1) `stochDom_lkMax_one_of_steps12` at an arbitrary
grid-valued sequence `v`; (2) `unifDomIcc_of_forall_stochDom` to exchange into a single
`UnifDomIcc` object; (3) `Grid.map_H_eq` (via `Measure.map_apply` on both sides) transfers each
individual grid-point/index bound from `P d` to `Grid.Pg d`; (4) `RBM.HighProb.biInter` over the
`Fin (K N+1) × LoopData (d.L N) 1` index (cardinality `≤ N^{C+2}$ eventually, from `hKcard` and
`card_loopData_le`). `Grid.highProb_grid_of_flow` is not referenced anywhere in the file.

### Build

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1532 && lake build RBM1D.Gauss.OneLoopSharpGridAll
```
```
ℹ [3968/3968] Built RBM1D.Gauss.OneLoopSharpGridAll (2.8s)
info: RBM1D/Gauss/OneLoopSharpGridAll.lean:174:0: 'RBM.Gauss.highProb_grid_xiLK_one' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3968 jobs).
```
No warnings from this file (fixed the two style lints: `Set.mem_ofPred_eq` instead of the
deprecated `Set.mem_setOf_eq`, `change` instead of `show`). No `sorry`/`admit`/`axiom` (grep
empty). Root `RBM1D.lean` not touched (import to be added at merge).

### (T2) Transitive-closure check (real compiled script, same method as T1527's)

Script: BFS over each constant's type/value/inductive constructors/recursor rules (`Closure.lean`
of T1527's report, reused verbatim, run as a scratch `lake env lean` file on
`highProb_grid_xiLK_one`, not committed).

```
RBM.Gauss.highProb_grid_xiLK_one: closure=70150
  forbidden hits=0: []
  types binding h560=9: [RBM.Gauss.Grid.eG_le_reduced_of_schwarz', RBM.Lemma57.sum_far_le,
 RBM.Gauss.Grid.eGpm_le_rhs535', RBM.Gauss.Grid.eG_le', RBM.Gauss.Grid.eGpm_le_reduced',
 RBM.Lemma57.eG_far_le, RBM.Gauss.Grid.drift_point_le', RBM.Gauss.Grid.eG_le_reduced',
 RBM.Lemma57.case2_pointwise]
  all names with component jStar=5: [RBM.Step2.jStar, RBM.Step2.jStar._proof_1,
 RBM.Step2.jStar._proof_2, RBM.Step2.jStar.congr_simp, RBM.Step2.jStar.eq_1]
  APrime-module constants=169, modules=[RBM1D.Gauss.APrimeGoodSetFlowGeneralDims,
 RBM1D.Gauss.APrimeRawSourcesGeneralDims, RBM1D.Gauss.APrimeGeneralMovingCarrierCore,
 RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims, RBM1D.Gauss.APrimeQVEndpoint,
 RBM1D.Gauss.APrimeFixedOneLoopGeneralDims, RBM1D.Gauss.APrimeCenteredModulusGeneralDims,
 RBM1D.Gauss.APrimeDuhamel, RBM1D.Gauss.APrimeTwoChargeOneLoop, RBM1D.Gauss.APrimeNearRem,
 RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims, RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore,
 RBM1D.Gauss.APrimeJG, RBM1D.Gauss.APrimeFullQV]
  MomentDuhamel constants=5: [RBM.Gauss.genD_eq_sum_pairs, RBM.Gauss.sum_used_eq_sum_pairs_coordD2_pt,
 RBM.MomentDuhamel.EEpath, RBM.MomentDuhamel.eeFun, RBM.MomentDuhamel.lkFun]
```

Interpretation (identical to T1527's, since this ticket adds no new APrime/MomentDuhamel
dependency — it only calls T1527's own theorem plus generic grid/probability machinery):
* `RBM.MomentDuhamel.Hyp`, `RBM.Step2.Hyp`: **absent**.
* `RBM.EarlyQVRateEv.jStar`: **absent** — the only `jStar` name is `RBM.Step2.jStar` (paper
  (5.29)), reached via `steps12_gauss`'s own chain, exactly as documented in T1527.
* `h560` (the `gmOfJS` form): **absent** — `h535_of_jS`, `eGpm_le_rhs535_of_jS`, `gmOfJS` do not
  occur; the 9 constants that bind a variable *named* `h560` are the generic Lemma 5.7 statements,
  discharged by `drift_point_le_blk'` with `Gm := gmBlkM` (T1501), as in T1527.
* `exampleGrow`: **absent** from the closure (used only in the paper witness above, never
  compiled into the theorem itself).
* `MomentDuhamel` constants: the same 5 (definitions `EEpath`, `eeFun`, `lkFun`, and two
  module-located lemmas), all via the merged `steps12_gauss`; no `.Hyp`.
* APrime-module constants: **identical set of 169, in the same 14 modules**, to T1527's list
  (checked by `diff` of the sorted `#aprimeList` output against `docs/reports/T1527-prove.md`'s
  list — byte-identical). This ticket introduces **no new APrime dependency**: every APrime
  constant enters solely through `stochDom_lkMax_one_of_steps12` → `steps12_gauss`, already
  audited admissible under DECISIONS §10b in T1527's audit. `Grid.mem_Icc_time`,
  `Grid.map_H_eq`, `Grid.H_measurable_filt`, `card_loopData_le`, `measurable_lkErrMat`,
  `lkErr_eq_lkErrMat`, `unifDomIcc_of_forall_stochDom`, `Sample.lkErr_le_lkMax`,
  `RBM.HighProb.biInter` are all non-APrime, hypothesis-free (given their own explicit
  arguments) or general-`Dims` lemmas; none is `exampleGrow`-only.
* Closure size 70150 vs T1527's 70142 for `stochDom_lkMax_one_of_steps12`: the +8 is exactly the
  handful of new non-APrime helper constants this file adds/reaches (`Grid.mem_Icc_time`,
  `Grid.H_measurable_filt`, `Grid.filt`, `card_loopData_le`, `HighProb.biInter`,
  `measurable_lkErrMat`, `lkErr_eq_lkErrMat`, `Sample.lkErr_le_lkMax`), none forbidden.
* `Grid.highProb_grid_of_flow` does **not** appear among the 70150 reached constants (checked by
  grep on the printed closure and by direct inspection of the 34-line proof term, which never
  mentions that name) — confirming the ticket's "do not use `highProb_grid_of_flow`" instruction
  was honored.

**Verdict: PASS** (both (T1) and (T2)).

## (c) Key lemmas used

`RBM.Gauss.stochDom_lkMax_one_of_steps12` (T1527, `OneLoopSharpGrid.lean:222`),
`RBM.Gauss.unifDomIcc_of_forall_stochDom` (`Lemma514Moment.lean:128`),
`RBM.Gauss.Grid.map_H_eq` (`GridPath.lean:452`), `RBM.Gauss.Grid.mem_Icc_time`
(`GridJStar.lean:187`), `RBM.Gauss.Grid.H_measurable_filt` (`GridStopFilt.lean:36`),
`RBM.measurable_H` (flow measurability), `RBM.Gauss.measurable_lkErrMat`/`lkErr_eq_lkErrMat`
(`Step2Gauss.lean`), `RBM.Sample.lkErr_le_lkMax` (`Hierarchy/Step3.lean`),
`RBM.Gauss.card_loopData_le` (`Lemma514Moment.lean`), `RBM.HighProb.biInter`,
`Band.scale_pos'`, `Measure.map_apply`, `Set.preimage_compl`.

## (d) Open issues

* None specific to this ticket. The satisfiability witness is a paper argument reusing T1527's
  audited witness for `steps12_gauss`, plus a trivial, independent grid witness `K N := N+1`,
  `C := 2`; it is not compiled (consistent with T1527's own convention, itself following the
  T1524 precedent).
* No paper delta: (T1) is Lemma 4.1 (4.5) + (2.76) at `n = 1`, simultaneously over a polynomial
  grid — a routine union-bound promotion of the already-accepted pointwise statement, with no
  change of hypotheses or conclusion shape beyond the grid index itself.
