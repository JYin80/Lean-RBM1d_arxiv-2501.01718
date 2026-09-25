Prover model: claude-sonnet-5

# T1507: J* on the grid — `jSMat` and matrix-set forms of σ's inputs

## 0. Method

Read: `CLAUDE.md` §3; `docs/supervisor/2026-09-25-2045.md` §4; `docs/reports/T1488-prove.md` §1
(Table A); `RBM1D/Gauss/GridPath.lean`, `GridStopFilt.lean`, `Step2Eq557.lean`; the file defining
`Step2.jS` (`RBM1D/Gauss/APrimeSmoothPrefixCanonicalCore.lean`). Also inspected (Step 0 read-only,
plus what is needed to cite the exact declarations used): `RBM1D/Flow/Hypotheses.lean` (`Sample`,
`Band`, `LoopData`, `TimeIcc`), `RBM1D/Loop/GLoop.lean` (`gloop`, `Gsig`), `RBM1D/Loop/Index.lean`
(`LoopIdx`), `RBM1D/Hierarchy/Kernel.lean` (`LoopArg`), `RBM1D/Gauss/Model.lean` (`band`, `sample`,
`Hflow`, `Idx`), `RBM1D/Hierarchy/Step1.lean` (`Step1.apriori`), `RBM1D/Gauss/EntryBoundTime.lean`
(`step1Hyp_gauss_of_scale''`), `RBM1D/Defs/MatrixMeasurable.lean` (`measurable_matrix_inv_apply`),
`RBM1D/Flow/Eq548Producer.lean` (measurability chain pattern, `measurable_mul_apply`), and
`RBM1D/Defs/StochDom.lean` (`StochDom`, `HighProb`, `HighProb.biInter`).

## 1. Math preflight (before any Lean)

**(T1) `jSMat` + `jS_eq_jSMat`. Verdict: PASS.**
`Step2.jS X E D N u ω := jStar (B.L N) (fun a => ‖lk X E N u ω a‖) (B.W N) (B.ell N u) (etaT E u) D`,
and `lk X E N u ω a = X.Lval E N u ω (LoopData.idx (sigPM,a)) - B.Kval E N u (LoopData.idx (sigPM,a))`,
where `X.Lval E N u ω I = gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) I` (`Sample.Lval`, literally a
function of the matrix `X.H N u ω` and nothing else about `ω`). For `X := sample d`, `B := band d`,
`(sample d).H N u ω` reduces (structure-literal projection, `rfl`) to `Hflow d N u ω`, and
`(band d).L N`, `(band d).W N` reduce to `d.L N`, `d.W N`. Hence defining `jSMat E D N u M` by the
identical formula with `M` substituted for `(sample d).H N u ω` produces a term syntactically
identical, after substitution `M := Hflow d N u ω`, to `Step2.jS (sample d) E D N u ω`; the equation
is `rfl`. `NeZero (B.L N)`/`NeZero (d.L N)` instances used inside `jStar` are proofs of a `Prop`
(`NeZero` is a `Prop`-valued class), so any two instances are definitionally equal (proof
irrelevance) — no obstruction from which instance typeclass search finds. Dependencies: none beyond
`Gauss.Dims`, already accepted (T1481 `Hflow`/`band`/`sample`). No hypotheses, so no
vacuity/satisfiability question.

**(T2) `measurable_jSMat`. Verdict: PASS.**
`jSMat` is `Finset.univ.sup' Finset.univ_nonempty (fun a => ‖gloop … M …‖ / tailT …) + 1`, a finite
`sup'` (`Finset.measurable_sup'`, already used for exactly this pattern in `Flow/Eq548Producer.lean`
`measurable_jSfarSm` and `Gauss/XiLKTwoCutModulus.lean`). It remains to show `M ↦ ‖gloop (d.L N)
(d.W N) M z I‖` is measurable **for every matrix `M`, unconditionally** (not just Hermitian `M`,
since `isStoppingTime_firstHit_grid`'s hypothesis `∀ j, Measurable (F j)` is global on
`Matrix (d.Idx N) (d.Idx N) ℂ`). `green M z := (M - z•1)⁻¹`; matrix inversion is **not continuous**
at singular matrices (only guaranteed invertible when `M` Hermitian and `z.im ≠ 0`,
`continuous_green_comp` in `Gauss/Hierarchy.lean`, which is therefore *not* the tool to use here),
but it **is measurable everywhere**, because `A⁻¹ = Ring.inverse (det A) • adjugate A` with `det`,
`adjugate` continuous (polynomial) and `Ring.inverse = (·)⁻¹` measurable on `ℂ`
(`RBM.Gauss.measurable_matrix_inv_apply`, `Defs/MatrixMeasurable.lean`, already used exactly this
way for `measurable_green_apply` through `ω ↦ Hflow d N u ω`). Applying it with the identity map
`Θ := Matrix (d.Idx N) (d.Idx N) ℂ`, `M := id - z•1` (continuous, hence measurable, via
`Mathlib.Topology.Instances.Matrix`) gives entrywise measurability of `M ↦ green M z` directly (no
`ω`, no Hermitian hypothesis, no probability space). `Gsig` (two `green` cases), `gloopProd`
(finite `foldr` of `Gsig * Eblk * Acc`, an induction identical in shape to
`RBM.measurable_gloopProd_apply`/`continuous_gloopProd_Hflow` but with `Measurable` throughout and
`M` instead of `Hflow d N u ω`) and `gloop` (`Matrix.trace` = finite sum of diagonal entries,
`rfl`, as used for `measurable_Lval`) are then a mechanical repeat of the existing pattern. No new
hypotheses; PASS.

**(T3) `jS_grid_law`. Verdict: PASS.**
Both sides are pushforwards of the SAME jointly-measurable function `jSMat E D N u_k` composed with
a matrix-valued map (`H d s t K N k` on the grid space, `Hflow d N u_k` on the flow space). Chain:
`jS_eq_jSMat` (T1) turns `Step2.jS (sample d) E D N u_k ·` into `jSMat E D N u_k ∘ Hflow d N u_k`;
`measurable_jSMat` (T2) plus `Measure.map_map` reduces both sides to `((Pg d).map (H d s t K N k))
.map (jSMat …)` and `((P d).map (Hflow d N u_k)).map (jSMat …)`; `map_H_eq` (T1481, already merged,
hypotheses `0 ≤ s N`, `s N ≤ t N`, `K N ≠ 0`) equates the two inner pushforwards. Whole-matrix
measurability of `H d s t K N k` (needed for `Measure.map_map`) comes from `H_measurable_filt`
(T1489, already merged) plus `Filtration.le` (a sub-σ-algebra map is measurable for the ambient
σ-algebra); whole-matrix measurability of `Hflow d N u` comes from the `Sample.measurable` field via
`RBM.measurable_H (sample d) N u`. No new hypotheses beyond `map_H_eq`'s own, already known
satisfiable (T1481). PASS.

**(T4) matrix-set forms of (2.73) and (5.57), transferred to the grid. Verdict: PASS for exactly
what is attempted (2.73, 5.57); the rest (`(4.2)` alone as opposed to via `5.57`, `(5.31)`, and the
uses of the other Table A/B targets M1–M7) is explicitly left open, per the ticket's allowance.**

Design: a **single reusable transfer lemma** `highProb_grid_of_flow`, generic in a matrix-set family
`S N u`, that:
1. takes a **continuum-uniform** flow-level statement `HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s
   t N, Hflow d N u ω ∈ S N u})` (this is exactly the shape `Step1.apriori.highProb` and
   `Gauss.Step2.highProb_eq557_col`/`highProb_eq557_colRow` already produce — `StochDom`'s
   union-over-the-parameter-set is *inside* the probability by Definition 2.1(i), so these
   statements are already uniform over the **whole continuous window**, not just one time);
2. for each grid index `k ≤ K N`, restricts (`.mono`, a deterministic ∀-instantiation, no
   probability loss) the continuum statement to the single grid time `u_k = time s t K N k` — valid
   because `u_k ∈ [s_N, t_N]` for `k ≤ K N` (elementary arithmetic on `time`/`step`, proved as
   `mem_Icc_time`) — and transfers that single-time statement to the grid exactly (equality, not
   inequality, of probabilities) via `map_H_eq`, exactly as in T3;
3. **must** then combine the `K N + 1` many single-grid-time statements into one event (this is a
   genuine new probability bound, since the paper's model shares only one-time marginals, per
   `CLAUDE.md` §3.5 / `Gauss/Model.lean`'s own scope note — a grid path is *not* jointly determined
   by the flow's laws at each time). This is `HighProb.biInter` (`Defs/StochDom.lean`, already in
   the codebase for exactly "polynomially many w.h.p. events hold simultaneously"), and it needs a
   **new hypothesis**: `∀ᶠ N, ((K N + 1 : ℕ) : ℝ) ≤ N^C` for some `C ≥ 0` (the grid has polynomially
   many points). This hypothesis is about the auxiliary sequence `K` alone; it does not touch `E, s,
   t` or any of the Step-1/`Cond272`/`BoundsCore` hypotheses used by (2.73)/(5.57), so it is jointly
   satisfiable with them (witness: `K N := N`, or any polynomial-growth `K`, together with any
   previously-established witness for the Step-1 hypotheses, e.g.
   `eventually_commonEvent_nonempty`'s list cited in T1488 §3). No `N = 0`/empty-window/degenerate
   collapse: the witness list is unchanged from prior tickets, `K` is a free new parameter not
   constrained to be huge, and `Fin (K N + 1)` is always nonempty (`k = 0` always present, and the
   whole-window `k = K N` reaches `t_N` by `time_last`, so the grid genuinely covers `[s_N, t_N]`,
   not a degenerate point).

`(2.73)` instance (`eq273Set`): for `n ≥ 1`, membership means `∀ v : LoopData (d.L N) n, ‖gloop … M
(zt E u) v.idx‖ ≤ N^τ (ℓ_u/ℓ_s)^{n-1} A_u^{-(n-1)}`, literally `Step1.apriori`'s conclusion at `n`
with `X.Lval` unfolded to `gloop … M …` and `X.H N u ω` renamed `M`. Flow-level `HighProb` comes from
`Step1.apriori (sample d) … n hn` (discharged by `step1Hyp_gauss_of_scale''`, the same hypothesis
list already shown satisfiable in T1488/earlier tickets) followed by `.highProb`. Measurability of
`eq273Set`: finite intersection (`LoopData (d.L N) n` is a `Fintype`) of `measurableSet_le` on
`‖gloop_matrix‖` (T2's building block). The ticket's Table A row A1 also mentions "loops of length ≤
6"; this is a downstream restriction of `n` (used in (5.64)) and does not change the shape here — I
give the family for every `n ≥ 1` as `apriori` itself does, matching or exceeding what is asked.

`(5.57)` instance (`eq557Set`): membership is `Gauss.Step2.highProb_eq557_col`'s column inequality
verbatim with `Hflow d N u ω` renamed `M`. Flow-level `HighProb` is `Gauss.Step2.highProb_eq557_col`
itself (T1492, already merged; same hypothesis list as `step1Hyp_gauss_of_scale''` plus `τ`).
Measurability: nested finite intersections over `x, y : ZMod (d.L N)` (plain, `MeasurableSet.iInter`)
and `p` with the guard `p.1 = y` (an implication, handled by a small generic helper
`measurableSet_setOf_forall_imp`, `{x | ∀ i, p i → x ∈ s i} = ⋂ i, if p i then s i else univ`).

Left open (unattempted, as the ticket allows): `(4.2)` alone as a standalone matrix set distinct from
`(5.57)` (M2's target already packages `(4.2) ⇒ (5.57)`, so a bare `(4.2)` matrix set would need a
separate `entryBoundFlow_floor`/`diag_bound_stochDom` wiring not attempted here); `(5.31)` (`eq531`
is a **deterministic**, not `StochDom`, statement — `∀ᶠ N, ∀ ω u a b`, so its "matrix-set form" is a
different, simpler shape not requiring `map_H_eq` transfer at all, and I leave the bookkeeping of
restating it on the grid to a later ticket); M4–M7 (not yet available per T1488, out of scope here).

## 2. Declarations added

File: `RBM1D/Gauss/GridJStar.lean` (namespace `RBM.Gauss.Grid`).

* `jSMat`, `jS_eq_jSMat` — (T1).
* `measurable_green_matrix`, `measurable_Gsig_matrix`, `measurable_gloopProd_matrix`,
  `measurable_gloop_matrix`, `measurable_jSMat` — (T2), the measurability chain.
* `jS_grid_law` — (T3).
* `mem_Icc_time` — arithmetic helper (`time s t K N k ∈ [s N, t N]` for `k ≤ K N`).
* `highProb_grid_of_flow` — the generic transfer lemma (flow-continuum `HighProb` + measurable
  matrix-set family + grid-size polynomial growth ⇒ grid `HighProb` uniform over `k ≤ K N`).
* `eq273Set`, `measurableSet_eq273Set`, `highProb_flow_eq273`, `highProb_grid_eq273` — (T4), (2.73).
* `measurableSet_setOf_forall_imp` (generic helper), `eq557Set`, `measurableSet_eq557Set`,
  `highProb_flow_eq557`, `highProb_grid_eq557` — (T4), (5.57).

## 3. Build

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1507 && lake build RBM1D.Gauss.GridJStar
```
Result: **success**, 0 errors, no `sorry`/`admit`/`axiom` (only style/lint warnings: two long
docstring/tactic lines, one unused-hypothesis lint on `measurableSet_setOf_forall_imp`'s
`[Fintype ι]`/`[DecidablePred p]`, one unused-binder-name lint, one `show`-vs-`change` lint, one
deprecated-lemma lint — none block the build or introduce unsoundness).

`#print axioms` on every public declaration in the file (`jSMat`, `measurable_jSMat`,
`jS_eq_jSMat`, `jS_grid_law`, `mem_Icc_time`, `highProb_grid_of_flow`, `eq273Set`,
`measurableSet_eq273Set`, `highProb_flow_eq273`, `highProb_grid_eq273`, `eq557Set`,
`measurableSet_eq557Set`, `highProb_flow_eq557`, `highProb_grid_eq557`) reports, for each:
`[propext, Classical.choice, Quot.sound]` — the three permitted axioms only.

## 4. Open issues

* T4's `(5.31)` and bare `(4.2)` matrix-set forms, and M4–M7, are not attempted (ticket allows this).
* The new hypothesis `∀ᶠ N, (K N + 1 : ℝ) ≤ N^C` is added only to `highProb_grid_eq273`/
  `highProb_grid_eq557` (the "union over k ≤ K" corollaries); it is not needed by, and does not
  weaken, T1–T3 or the single-grid-time-only statements.
