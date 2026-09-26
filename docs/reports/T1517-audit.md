Auditor model: claude-opus-5-5[1m]

# T1517 audit: `step2` packaging for the Gaussian model, without `Hy`

Branch `t/T1517` @ `3504438` (base `199bf1d`). Diff against base: one new file, `RBM1D/Gauss/Step2Gauss.lean` (+285). This is the ticket's sole writable file. No other file is touched, so no frozen signature changed. Main has since moved to `5ff2ffd` (T1516: `RBM1D.lean`, `Gauss/GridExpansion.lean`). Neither file is a dependency of this module, so the drift does not matter.

Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1517-audit`. It is a fresh detached checkout of `t/T1517` with a copy-on-write cache clone; the prover's worktree was not reused. `Step2Gauss.olean` was absent before the build and was produced by this build.

## Overall verdict: PASS (T1, T2, T3)

## 1. Math preflight
`T1517-prove.md` §(a) has a per-target preflight with a PASS for each of T1, T2 and T3, placed before the Lean section (b). The first line is `Prover model: claude-sonnet-5`.

## 2. Statement vs ticket / paper
- **(T1) `step2_gauss_of_pointwise`.**
  - Hypotheses: those of `Step2.step2` (Step2.lean:2054) at `X := sample d`, `B := band d`, minus `Hy` and minus `h1`, plus `hpt`. The kept hypotheses are `hκ0, hκ1, hEκ, hB, hs0, hst, ht1, hc0, hreg`, with the same forms and the same parameter order. The fixed parameters `κ, E, s, t, c` come before the `∀ᶠ N` inside `hreg`/`hpt`.
  - `hpt` matches T1511's `h276_of_pointwise` (GridNetLift.lean:154–158), with one difference: the label type is written `ZMod (d.L N)` instead of `ZMod ((band d).L N)`. The two are definitionally equal (structure projection of `band d`), but not at reducible transparency. The proof passes `hpt` straight into `h276_of_pointwise`, so the difference has no effect. Cosmetic only.
  - Proof route: exactly the ticket's. `h276 := Grid.h276_of_pointwise …`, `hc272 := cond272_of_strict …`, `hreg'` via `eventually_R4_le_scale`, `h1 := step1Hyp_gauss_of_scale'' …`, `h274 := Step1.weakLaw …`, conclusion `⟨localLaw … h276 h274 h1.lemma41, h276⟩`.
  - **Syntactic conclusion check (compiled by the auditor).** In a scratch probe I took `a := Step2.step2 (sample d) … Hy h1 …` with `Hy`, `h1` as free variables and `b0 := step2_gauss_of_pointwise d … hpt`. Both of these pass:
    - `with_reducible exact b0 : type_of% a`
    - `guard_hyp b0 :ₐ type_of% a` (alpha-equivalence)

    So (T1)'s conclusion is syntactically `step2`'s conclusion at `sample d`. The prover's in-file `example` also type-checks.
- **(T2) `GridPointwise` / `hpt_of_grid`.**
  - `GridPointwise d E s t` has the form: `∀ D > 0, ∀ u : ∀ N, TimeIcc s t N, ∃ K, (∀ N, K N ≠ 0) ∧ ∃ C ≥ 0, (∀ᶠ N, K N + 1 ≤ N^C) ∧ StochDom (Grid.Pg d) (lkErrMat(u N, Grid.H d s u K N (K N) ω)) (same bound as hpt)`.
  - `lkErrMat` is `‖gloop (d.L N) (d.W N) M (zt E u) I − (band d).Kval E N u I‖`. `lkErr_eq_lkErrMat` holds by `rfl`.
  - Transfer (`stochDom_grid_iff_flow`): at each `N` and `τ`, the two bad-set probabilities are equal. The proof uses `Grid.map_H_eq` at `k = K N`, then `Grid.time_last`, then `Measure.map_apply`. Measurability of the matrix set comes from `measurable_gloop_matrix`, using a finite union over labels. The transfer is therefore an exact equivalence, with no loss.
  - `K` and `C` are existential after `D` and `u`. This is a design choice (open issue (d) of the prove report). It is compatible with the ticket's wording, "with a grid of `K N + 1 ≤ N^C` points".
- **(T3) `step2_gauss_of_grid`.** Composition `(T1) ∘ hpt_of_grid`. Its conclusion is the same two-conjunct `step2` conclusion (same text as T1).

## 3. Vacuity / hidden hypotheses / cycles
- **New hypotheses:** only `hpt` (T1) and `GridPointwise` (T3). Neither is a structure bundle, so nothing is hidden in a structure field. All other hypotheses are exactly `step2`'s own, which were already accepted.
- **Non-vacuity of `GridPointwise` (compiled by the auditor).** I wrote an `example` that takes `Hy`, `h1` and step2's other hypotheses, and derives `GridPointwise d E s t` from the second conjunct of `Step2.step2 (sample d) …`. That conjunct is used in its literal form, with `(band d).P` and `(band d).L`. The steps are:
  1. `StochDom.precomp_param` restricts it to `u`.
  2. The grid is `K := 1` (`time_last`) and `C := 1`, with `2 ≤ N^1` eventually.
  3. The explicit `Grid.map_H_eq` instance at `k = 1` is stated.
  4. The flow-to-grid direction of `stochDom_grid_iff_flow` finishes the proof.

  The example compiles, so `GridPointwise` is implied by the target. `hpt` is likewise implied by the target (precomposition), so neither new hypothesis is stronger than the goal. Because `K := 1` is allowed, `GridPointwise` is in fact equivalent to `hpt`.
- **Boundary cases:**
  - No `N = 0` loophole: all statements are `∀ᶠ N` / `StochDom`.
  - `TimeIcc s t N` is nonempty under `hst`.
  - `D > 0` is kept.
  - The window `[s N, t N]` is `step2`'s own and is not collapsed.
  - The label set `ZMod (d.L N) × ZMod (d.L N)` is the full label set.
- **Cycles:** none. The dependencies are T1511 (`h276_of_pointwise`, merged), T1507/T1481 (grid `map_H_eq`, `time_last`, `measurable_gloop_matrix`, merged), `step1Hyp_gauss_of_scale''`, `Step1.weakLaw`, `Step2.localLaw`, `cond272_of_strict` and `eventually_R4_le_scale`. All are already accepted.

## 4. Forbidden inputs (`Hy`, `Step2.Hyp`, `aprioriDecay`)
- **Grep of `Step2Gauss.lean`:** `Hy`, `aprioriDecay` and `Step2.Hyp` appear only in docstrings (lines 12, 18–21, 181–183). `Step1.Hyp` appears only at line 211, as the type of the internally produced `h1`. It is not an external hypothesis.
- **Compiled transitive-closure check.** I walked the used constants of `step2_gauss_of_pointwise`, `hpt_of_grid`, `step2_gauss_of_grid` and `GridPointwise`, about 48k–64k constants each. None of them contains `RBM.Step2.aprioriDecay`, `RBM.Step2.Hyp` or any of its fields, `RBM.Step2.step2`, or `sorryAx`.

## 5. Builds and axioms
- `lake build RBM1D.Gauss.Step2Gauss` (audit worktree): **Build completed successfully (3894 jobs)**. One local warning: deprecated `Set.mem_setOf_eq` at line 132 (cosmetic).
- `lake build RBM1D` (audit worktree): **Build completed successfully (9664 jobs)**, with no errors. The root import of `Step2Gauss` is added at merge, per the ticket.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 8 new declarations: `lkErrMat`, `measurable_lkErrMat`, `lkErr_eq_lkErrMat`, `stochDom_grid_iff_flow`, `GridPointwise`, `hpt_of_grid`, `step2_gauss_of_pointwise`, `step2_gauss_of_grid`.
- The file contains no `sorry`, `admit`, `axiom`, `opaque`, `unsafe` or `implemented_by`.

## 6. Acceptance criteria
- (T1)–(T3) exist with the ticket's names; no `sorry`/`admit`/`axiom`; the prove report's first line is correct: met.
- (T1)'s conclusion is syntactically `step2`'s: met (alpha-equivalence check compiled).
- No `Hy`, `Step2.Hyp` field or `aprioriDecay` is used: met (grep plus the closure check).
- `GridPointwise` is not vacuous: met. Both the prover's example and the auditor's example (from step2's literal conclusion plus `map_H_eq`) compile.

## Notes (non-blocking)
- This closes the downstream packaging only. G1b stays open until R4c proves `GridPointwise`.
- `hpt`'s label type uses `d.L` rather than `(band d).L`. They are definitionally equal by structure projection, but not at reducible transparency. The difference is harmless.
- Paper deltas: none needed. The Lean statement is `step2`'s conclusion verbatim, and the dropped `Hy`/`h1` are discharged internally or replaced.
