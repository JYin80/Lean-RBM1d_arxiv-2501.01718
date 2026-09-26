Prover model: claude-sonnet-5

# T1517 — `step2` packaged for the Gaussian model without `Hy`

## (a) Math preflight (before any Lean)

Read: `RBM1D/Hierarchy/Step2.lean` (1600–1760, 2040–2080: `localLaw_of_scale_facts`,
`localLaw`, `step2`), `RBM1D/Gauss/GridNetLift.lean` (`etaT_inv_le_of_hreg`,
`h276_of_pointwise`), `RBM1D/Gauss/GridPath.lean` (30–70, 440–492: `H`, `time`, `time_last`,
`map_H_eq`), `RBM1D/Gauss/GridJStar.lean` (100–260: `measurable_gloop_matrix`, `jSMat`,
`jS_eq_jSMat`), `RBM1D/Gauss/EntryBoundTime.lean` (640–700: `step1Hyp_gauss_of_scale''`),
`RBM1D/Gauss/GridStopFilt.lean` (`H_measurable_filt`, `filt`), `RBM1D/Gauss/Model.lean`
(`band`, `sample`, `band_L`, `band_W`, `sample_H`), `docs/paper-deltas.md` (none needed),
CLAUDE.md §3.

**(T1) `step2_gauss_of_pointwise`.** Target: `Step2.step2`'s conclusion for `X := sample d`,
`B := band d`, with `Hy : Hyp X E s t` and `h1 : Step1.Hyp X E s t` removed, `hpt` (T1511's
`h276_of_pointwise` input) added.
- Statement vs. paper: `step2` is Step 2 of Theorem 2.21, (2.75)–(2.76); the packaging itself
  (not a new mathematical fact) matches the ticket's Route exactly: `h276 :=
  h276_of_pointwise …`, `hc272 := cond272_of_strict …`, `hreg'` as in `step2`'s own proof, `h1 :=
  step1Hyp_gauss_of_scale'' …`, `h274 := Step1.weakLaw …`, conclusion `⟨localLaw … h276 h274
  h1.lemma41, h276⟩`.
- Hypotheses: identical to `step2`'s own (`hκ0, hκ1, hEκ, hB, hs0, hst, ht1, hc0, hreg`) minus
  `Hy`, minus `h1`, plus `hpt` verbatim from `h276_of_pointwise`.
- Dependencies: `Grid.h276_of_pointwise` (T1511, merged), `step1Hyp_gauss_of_scale''`
  (`EntryBoundTime.lean`, pre-existing), `Step2.cond272_of_strict`, `Step2.eventually_R4_le_scale`,
  `Step1.weakLaw`, `Step2.localLaw` — all already-accepted results, no cycle back to this
  ticket's own targets.
- Quantifier order / parameters: unchanged from `step2` (all fixed parameters, `s, t, c, κ, E`
  before the `∀ᶠ N` inside `hreg`/`hpt`); no new hypothesis added beyond `hpt` itself, which
  T1511 already supplies satisfiably (its own report gives the witness).
- Boundary cases: none introduced; `s0/hst/ht1/hc0` unchanged from `step2`.
- Verdict: **PASS**.

**(T2) `hpt_of_grid` / `GridPointwise`.** Target: an interface lemma turning a grid-side
statement into T1511's pointwise `hpt`.
- The grid transfer is an *equality* of laws, not an approximation: `Grid.map_H_eq` at
  `k = K N` together with `Grid.time_last` (`time s u K N (K N) = u N` given `K N ≠ 0`) gives
  `(Pg d).map (H d s u K N (K N)) = (P d).map (Hflow d N (u N))` for *any* grid resolution `K`
  with `K N ≠ 0`; since `StochDom` is defined purely through the pushforward measure of a
  failure event (`P (badSet …)`), and the failure event here is a preimage of a matrix-set
  through `H`/`Hflow` respectively (measurability of the matrix-set via
  `Grid.measurable_gloop_matrix`, finiteness of the label set `ZMod L × ZMod L`), the two
  `StochDom` statements are *equivalent*, not merely one implying the other with loss.
- Non-vacuity: `GridPointwise` (defined with an outer `∃ K, (∀ N, K N ≠ 0) ∧ ∃ C ≥ 0, (grid-card
  bound) ∧ StochDom(grid)`) is satisfiable by taking `K := 1` and `C := 1`: the resulting
  `StochDom(grid)` reduces, via the exact transfer above, to `step2`'s own second conjunct
  restricted to a fixed time sequence `u` (`StochDom.precomp_param`) — i.e. it is *implied by*
  the paper's own target, so it is not an artificially strengthened or vacuous hypothesis. Given
  as a Lean `example` in the file (acceptance criterion).
- Hypotheses/parameters: `s, t, E` fixed before `∀ D, ∀ u`; `K, C` existentially quantified
  after `u, D` (their existence is exactly what R4c's stopping-time grid construction is free to
  choose, matching the ticket's phrasing "with a grid of `K N + 1 ≤ N^C` points").
- Verdict: **PASS**.

**(T3) `step2_gauss_of_grid`.** `(T1) ∘ (T2)`, under `GridPointwise`; direct composition, no new
mathematical content. Verdict: **PASS**.

**Reuse check (DECISIONS §10b).** `Hy`, any `Step2.Hyp` field, and `aprioriDecay` do not occur
anywhere in `RBM1D/Gauss/Step2Gauss.lean` except inside docstrings describing what was avoided
(`grep` confirms: the only three matches are documentation lines, none in a signature or proof
term). `Step1.Hyp` is used only as the *internal* output of `step1Hyp_gauss_of_scale''`
(reused, already-accepted), never as an external hypothesis of any of (T1)–(T3).

## (b) Declarations, builds, axioms

File: `RBM1D/Gauss/Step2Gauss.lean` (sole writable file), branch `t/T1517`, committed as
`3504438`.

Declarations (all in namespace `RBM.Gauss`):
- `lkErrMat`, `measurable_lkErrMat`, `lkErr_eq_lkErrMat` — the matrix-level `lkErr` and its two
  interface facts (mirrors `Grid.jSMat`/`Grid.jS_eq_jSMat`'s pattern for `lkErr`).
- `stochDom_grid_iff_flow` — the exact grid ↔ flow transfer at the last grid step.
- `GridPointwise` (def) — the grid-side hypothesis R4c is to discharge.
- `hpt_of_grid` — (T2) `hpt` from `GridPointwise`.
- `step2_gauss_of_pointwise` — (T1).
- `step2_gauss_of_grid` — (T3).
- two `example`s: (i) `step2_gauss_of_pointwise`'s conclusion stated verbatim as `step2`'s
  two-conjunct conclusion at `X := sample d`, `B := band d` (T1's syntactic-match acceptance
  criterion); (ii) `GridPointwise` derived from `step2`'s own (assumed) second conjunct plus
  `map_H_eq` (non-vacuity acceptance criterion).

Build:
```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1517 && lake build RBM1D.Gauss.Step2Gauss
```
Result: **success**, 0 errors (3894/3894 jobs). Only pre-existing warnings elsewhere in the
tree and one local deprecation warning (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, cosmetic,
line 132).

Axioms (`lake env lean` on a throwaway probe file importing `RBM1D.Gauss.Step2Gauss` and
running `#print axioms` on every new declaration):
```
'RBM.Gauss.lkErrMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.measurable_lkErrMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.lkErr_eq_lkErrMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.stochDom_grid_iff_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.GridPointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.hpt_of_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.step2_gauss_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.step2_gauss_of_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/`axiom`.

## (c) Key lemmas used

`Grid.h276_of_pointwise` (T1511), `Step2.cond272_of_strict`, `Step2.eventually_R4_le_scale`,
`step1Hyp_gauss_of_scale''` (`EntryBoundTime.lean`), `Step1.weakLaw`, `Step2.localLaw`,
`Grid.map_H_eq`, `Grid.time_last`, `Grid.H_measurable_filt`, `Grid.filt`,
`Grid.measurable_gloop_matrix`, `RBM.measurable_H`, `StochDom.precomp_param`,
`Measure.map_apply`.

## (d) Open issues

- `GridPointwise`'s exact shape (existential `K`/`C` after `∀ D, ∀ u`) is a design choice made
  in this ticket (the ticket only prescribes the informal shape); R4c is free to discharge it
  with whatever grid construction its stopping-time argument produces, since the transfer holds
  for every valid `K`. If R4c's natural output has a different shape (e.g. one `K` shared across
  all `D`), a thin adapter would be needed, but the current `GridPointwise` is implied by the
  paper's target (see the non-vacuity `example`), so it is not an obstacle.
- One cosmetic warning (`Set.mem_setOf_eq` deprecated) left as-is; does not affect correctness.
