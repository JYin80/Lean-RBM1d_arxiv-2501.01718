Auditor model: claude-opus-5-5[1m]

# T1502 audit: `hjG` — `jG ≤ N^{2ε}·jS` on one high-probability event

Audited 2026-09-25T20:57Z (UTC). Branch `t/T1502` at `c035b85` (base `752dd76`), checked out in a fresh
audit worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1502-audit2` (not the prover's worktree).
`git diff --name-only main...t/T1502` = `RBM1D/Gauss/Step2JGle.lean` only (the sole writable file).
Main has advanced since the base only by `RBM1D/Gauss/Step2QVEvent.lean` + root import (T1497), which
the new file does not depend on.

## Target (T1) `RBM.Gauss.Step2.highProb_jG_le_jS` — **PASS**

### 1. Math preflight
`docs/reports/T1502-prove.md` §(a) contains a per-target preflight, verdict PASS, placed before the
Lean section and stamped 2026-09-25T20:53Z. (The branch commit is at 20:53:10Z, so timestamps alone
cannot establish the ordering; the report asserts it and its structure is correct. No defect.)

### 2. Statement vs source / ticket
Compiled signature (`#check`):
`∀ d : Dims, 0<κ → |E| ≤ 2-κ → BoundsCore (sample d) E s → (∀N, 0 ≤ s N) → (∀N, s N ≤ t N) →
(∀N, t N < 1) → Cond272 (band d) E s t → 0<c → (∀ᶠ N, N^c ≤ (band d).scale E N (t N)) →
∀ D, 0 ≤ D → ∀ ε, 0 < ε → HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
APrimeJG.jG (sample d) E N u ω ((band d).ell N u) (etaT E u) D ≤ N^(2ε) · Step2.jS (sample d) E D N u ω})`.

- Name, namespace and conclusion match the ticket's (T1) literally (ℓ_u = `(band d).ell N u`,
  η_u = `etaT E u`, per T1488 §3 notation).
- Hypothesis list is exactly that of `RBM.Gauss.step1Hyp_gauss_of_scale''` (EntryBoundTime.lean:654),
  checked token by token: `hκ, hE, hB, hs0, hst, ht1, hcond, hc0, hreg`. The only additional binders
  are the free parameters `D ≥ 0` (already in the ticket's statement, as the `jG`/`jS` argument) and
  `ε > 0`. No new hypothesis beyond the Step-1 list. (Acceptance criterion: met.)
- Exponent `2ε`: `ε` is universally quantified over all `ε > 0`. (Acceptance criterion: met.)
- `jStar` not used: the file never references `jStar` (only occurrence is a docstring sentence);
  the statement uses `Step2.jS` (whose library definition is the standard one via `jStar`, which is
  the intended quantity). (Acceptance criterion: met.)
- Quantifier order: fixed parameters `d, κ, E, s, t, c, D, ε` precede `HighProb`, which unfolds to
  `∀ Δ > 0, ∀ᶠ N, P(Ξ_N^c) ≤ N^{-Δ}` (Defs/StochDom.lean:95). Correct.
- Uniform in time: the event is `∀ u ∈ TimeIcc s t N` inside one set — the ticket's full form, not
  the fixed-`u` fallback.
- Constant form: the chain gives `1 + N^ε(9e^{√3}·jS + 2)`, absorbed via `1 ≤ jS` and
  `3 + 9e^{√3} ≤ N^ε` eventually into `N^{2ε}·jS` — the ticket's product form. The `9e^{√3}` (shift
  by 3 via `tailT_shift_three`) instead of the ticket's `18e²`/`T(d−2) ≤ e²T(d)` reflects the
  neighbour-distance correction `d−3` recorded by the T1499 auditor (N2); it is the correct form and
  does not change the statement. No paper formula is altered; no paper-delta needed.
- Special-case check: general `d : Dims`, general `E` with `|E| ≤ 2-κ`, general window `[s,t]`; not
  `exampleGrow`/first-cell/`E=0`/fixed-`u`.

### 3. Vacuity / hidden hypotheses / cycles
- Nondegenerate witness of the full hypothesis list is compiled on `main`:
  `d := Dims.exampleGrow` (W grows like `N^{5/8}`), `E := 0`, `κ := 1`, `s := 0`,
  `t := firstCellT τ'`, `c := 1/2`: `firstCell_boundsCore` and `firstCell_cond272Reg`
  (APrimeFirstCellInitialMomentBudget.lean:36/41) give `BoundsCore`, `Cond272` and `hreg`; `hs0`,
  `hst`, `ht1` from `APrimeSupportRunning.firstT_bounds`. `D := 1`, `ε := 1` are free and independent.
  No astronomically-large-only witness; window `[0, t_N]` nondegenerate.
- No structure-field smuggling: all hypotheses are explicit Props already used by accepted theorems.
- Boundary cases: `D = 0` allowed and harmless; `jS ≥ 1` always (`Step2Moment.one_le_jS`), so no
  `jS = 0` collapse; the proof uses `N ≥ 1` only inside `∀ᶠ N`; the index set `TimeIcc s t N` is the
  unnarrowed window.
- No cycle: the file imports only `Gauss.APrimeJG`, `Gauss.APrimeGoodSetFlowGeneralDims`,
  `Hierarchy.Step2Moment`; nothing imports the new file.

### 4. Dependencies (all committed on `main`, root-imported where applicable)
`APrimeJG.highProb_jG_le_of_entryBoundFlow` (APrimeJG.lean:569, commit 9d6dde5),
`Gauss.entryBoundFlow_floor`, `rpow_neg_one_le_etaT_of_scale_ge`, `flowDelta_le_rpow_neg`
(EntryBoundTime.lean, 8241709), `APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow` (ab96505),
`Step2Moment.one_le_jS` (6e92b71), `HighProb.mono`, `eventually_le_rpow`. Signatures checked:
the instantiation `K := 1, c₀ := c/6, B := D` of `entryBoundFlow_floor` produces exactly the floor
`2·N^{-D}` required by `highProb_jG_le_of_entryBoundFlow`. T1499 is merged (state file).
None of these is on the DECISIONS §10b banned list.

### 5. Build and axioms (audit worktree)
- `lake build RBM1D.Gauss.Step2JGle`: `Build completed successfully (3880 jobs)`; the module's
  `.olean` was absent from the copied cache and was compiled fresh. No errors.
- `lake build RBM1D`: `Build completed successfully (9649 jobs)` (root does not yet import the
  new module; import is added at merge per ticket).
- `#print axioms RBM.Gauss.Step2.highProb_jG_le_jS`: `[propext, Classical.choice, Quot.sound]`.
- `grep sorry|admit|axiom` on the new file: no match. No frozen signature touched (only one new file).
- Prove report first line: `Prover model: claude-sonnet-5`. (Acceptance criterion: met.)

## Verdict
T1502 (T1): **PASS**.
