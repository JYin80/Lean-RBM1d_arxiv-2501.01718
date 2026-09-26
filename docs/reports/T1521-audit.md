Auditor model: claude-opus-5-5[1m]

# T1521 audit: Steps 1–2 of `RBM.Steps` for the Gaussian model (`Steps12Gauss.lean`)

Branch `t/T1521` @ `ec2ed8e`, base `db76845` (= current `main`). Diff vs `main`: one new file, `RBM1D/Gauss/Steps12Gauss.lean` (+171), which is the ticket's sole writable file. No other file is touched, so no frozen signature changed.
Audit worktree: a fresh detached checkout at `/Users/junyin/Lean_proof/RBM1D-wt/T1521-audit`, not the prover's worktree.

## Overall verdict: PASS (T1, T2, T3)

## 0. Math preflight
`docs/reports/T1521-prove.md` §(a) has the per-target preflight (T1 PASS, T2 PASS, T3 PASS) before §(b) (Lean). The first line is `Prover model: claude-opus-5-5`. The preflight answers the ticket's interface question: nothing is missing. `Cond272`, the bare `N^c ≤ scale(t)`, and `Step1.Hyp` all come from step2's own list, via `Step2.cond272_of_strict`, `Step2.eventually_R4_le_scale` and `step1Hyp_gauss_of_scale''`. This is the same route `Step2.step2`'s proof uses (Step2.lean:2066–2072).

## (T1) `RBM.Steps12`, `RBM.Steps.toSteps12`, `RBM.Steps.ofSteps12`: PASS
- **The fields are literally `Steps`'s first four.** I extracted the field block of `structure Steps12` (from `apriori` through the end of `aprioriDecay`) and the matching block of `structure Steps` in `Flow/Hypotheses.lean` (up to `sharpLoop`), then compared them with `diff`. The result was **IDENTICAL**: same names, same order, same types, docstrings included. The binders `(X : Sample B) (E : ℝ) (s t : ℕ → ℝ)`, `: Prop`, and the section variables `{Ω} [MeasurableSpace Ω] {B : Band Ω}` are the same as for `Steps`.
- The structure lives in the new file, not in `Flow/Hypotheses.lean`.
- `toSteps12` is a one-line anonymous constructor from the four projections. `ofSteps12` takes the four remaining fields as explicit arguments, with types verbatim from `Steps.sharpLoop/sharpLmK/sharpDecay/sharpExpect`, and is one line.
- Extra compiled check (scratch file): `(Steps.ofSteps12 h _ _ _ _).toSteps12 = h := rfl` typechecks.

## (T2) `RBM.Gauss.steps12_gauss_of_grid`: PASS
Printed signature (`#check`):
`(d) {κ} (0<κ) (κ≤1) {E} (|E|≤2-κ) {s t} (BoundsCore (sample d) E s) (∀N,0≤s N) (∀N,s N≤t N) (∀N,t N<1) {c} (0<c) (∀ᶠ N, N^c·(η_s/η_t)^30 ≤ (band d).scale E N (t N)) (GridPointwise d E s t) → Steps12 (sample d) E s t`.

- **Every hypothesis is one of step2's or `GridPointwise`.** `Step2.step2`'s list (Step2.lean:2054–2058) is `hκ0, hκ1, hEκ, Hy, h1, hB, hs0, hst, ht1, hc0, hreg`. T2's list is `hκ0, hκ1, hEκ, hB, hs0, hst, ht1, hc0, hreg` (each with an identical type at `X := sample d`, `B := band d`) plus `hgp : GridPointwise d E s t`. The ticket's list is the same, and so is T1517's `step2_gauss_of_grid` list.
- **Neither `Hy` nor `aprioriDecay` is used.** The proof of `steps12_gauss_of_grid` does not mention `Step2.Hyp`, `Step2.aprioriDecay` or `Step2.step2`. `Step1.Hyp` is derived internally by `step1Hyp_gauss_of_scale''`. The `aprioriDecay` field is filled by the second conjunct of `step2_gauss_of_grid`, whose signature contains no `Hy`.
- **Route matches the ticket.** `apriori` is `Step1.apriori (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' h1` and `weakLaw` is `Step1.weakLaw` with the same arguments. `hcond := cond272_of_strict`, `hreg'` comes from `eventually_R4_le_scale` at `u = t N`, and `h1 := step1Hyp_gauss_of_scale''`. `localLaw` and `aprioriDecay` are the two conjuncts of `step2_gauss_of_grid`.
- **κ conventions.** `step1Hyp_gauss_of_scale''` caps κ at `min κ 1` internally, and T2 also carries `hκ1` (needed by `step2_gauss_of_grid`). There is no mismatch.
- **Statement vs paper.** Steps 1–2 of §2.7 give (2.73)–(2.76). The field shapes are the frozen `Steps` fields. Fixed parameters (`d, κ, E, s, t, c`) are universally quantified, and `N` appears only inside `∀ᶠ`/`StochDom`. There is no special case: this is general `d : Dims`, general `E` with `|E| ≤ 2-κ`, and general `s ≤ t < 1`.
- **Boundary cases.** `N = 0` gives no loophole: every N-dependent claim is `∀ᶠ N`/`StochDom`. `TimeIcc s t N` is nonempty (`hst`). `s = t` is allowed and gives the trivial window, which is harmless and not assumed.

## (T3) nondegeneracy: PASS
- Part 1: `example (h : Steps X E s t) : Steps12 X E s t := h.toSteps12`. `Steps12` is weaker than `Steps`, not an independent assumption.
- Part 2: the helper `gridPointwise_of_step2Hyp` derives `GridPointwise d E s t` from `Step2.Hyp (sample d)` plus step2's other hypotheses. It uses `Step2.aprioriDecay`, then `stochDom_grid_iff_flow` at the trivial grid `K := 1` with `C := 1` (`2 ≤ N^1` eventually). The example then shows that step2's hypothesis list implies all of T2's hypotheses. `Hy`/`Step2.aprioriDecay` appear only in this T3 reduction, which is what the ticket's "implied by step2's" asks for. They do not appear in T2.
- Minor, not a defect: the Part 2 example carries an unused `_h1 : Step1.Hyp` binder, which makes it literally a superset of step2's list.
- **Satisfiability.** T2 adds no hypothesis beyond `step2_gauss_of_grid`'s. That list, including `GridPointwise`, was audited PASS for vacuity and satisfiability in `docs/reports/T1517-audit.md`. There is no circularity: T2 depends only on merged T1517/Step 1/Step 2 lemmas, and nothing merged depends on this new file.

## Dependencies (all already merged in `main` @ `db76845`)
`RBM.Steps` (Flow/Hypotheses), `Step1.apriori`, `Step1.weakLaw`, `Step1.Hyp` (Hierarchy/Step1), `Step2.cond272_of_strict`, `Step2.eventually_R4_le_scale`, `Step2.aprioriDecay`, `Step2.Hyp` (Hierarchy/Step2), `Gauss.step1Hyp_gauss_of_scale''` (Gauss/EntryBoundTime), `Gauss.step2_gauss_of_grid`, `Gauss.GridPointwise`, `Gauss.stochDom_grid_iff_flow` (Gauss/Step2Gauss, T1517).

## Build and axioms (audit worktree)
- `lake build RBM1D.Gauss.Steps12Gauss`: rc 0, `Build completed successfully (3895 jobs)`. The olean was freshly produced in the audit worktree. No errors, and no warnings from the new file.
- `lake build RBM1D`: rc 0, `Build completed successfully (9666 jobs)`. The root does not import the new file yet; the import is added at merge.
- `#print axioms` for `RBM.Steps.toSteps12`, `RBM.Steps.ofSteps12`, `RBM.Gauss.steps12_gauss_of_grid` and `RBM.Gauss.gridPointwise_of_step2Hyp` gives `[propext, Classical.choice, Quot.sound]` each.
- `grep sorry|admit|axiom` on the new file: no matches.
