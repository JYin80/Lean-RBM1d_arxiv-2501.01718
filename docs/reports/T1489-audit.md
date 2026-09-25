Auditor model: claude-opus-5-5[1m]

# T1489 audit — grid stopping times specialised to the coordinate filtration

Audited: branch `t/T1489` at `774d49e` (one commit over `main`), audit worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1489-audit` (clean, detached at `774d49e`). Date: 2026-09-25 18:08 UTC.

Diff vs `main`: exactly one new file, `RBM1D/Gauss/GridStopFilt.lean` (+93), the ticket's sole
writable file. No other file touched; `RBM1D.lean` unchanged (root import is to be added at merge).

## Verdict per target

| Target | Declaration(s) | Verdict |
|---|---|---|
| (T1) | `RBM.Gauss.Grid.isStoppingTime_firstHit_grid` | PASS |
| (T2) | `RBM.Gauss.Grid.lt_firstHit_grid_measurableSet` | PASS |
| (T3) | `RBM.Gauss.Grid.isStoppingTime_min_firstHit_grid`, `RBM.Gauss.Grid.lt_min_firstHit_grid_measurableSet` | PASS |

Helpers (public, not targets): `H_measurable_filt` (Step-0 matrix-level lemma asked for by the
ticket) and `adapted_of_measurable_H`.

**Overall: PASS.**

## 1. Math preflight

`docs/reports/T1489-prove.md` §(a) has a per-target math preflight (T1/T2/T3 each PASS) plus
the Step-0 check, placed before the Lean section §(b). PASS.

## 2. Statement vs source and ticket

Source: `docs/claude-team/pilot-P4P5-paper.md` §4: τ := min{j : J*_{u_j,D} ≥ threshold} and
σ := min{j : some bound fails at u_j}, where both quantities are *deterministic functions of
H_{u_j}*. The source says τ, σ are F-stopping times and 1(j < τ), 1(j < σ) are F_j-measurable, and
it uses τ∧σ.

- (T1) Signature: for fixed `d s t K N`, `{F : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}`,
  `hF : ∀ j, Measurable (F j)`, `θ K'`, the conclusion is
  `IsStoppingTime (filt d) (fun ω => firstHit (fun j ω => F j (H d s t K N j ω)) θ K' ω)`.
  This is the ticket's form "J j ω = F j (H d s t K N j ω)". The Lean writes J inline, which is
  equivalent to a separate J plus an equation hypothesis. `F` depends on the grid index `j`, so the
  time-dependent observables f_{u_j} (with z = z_{u_j}) are covered. The filtration is the
  accepted `filt d` (`Filtration.piLE`, i.e. σ(ω 0,…,ω k) = F_k of the source §2). Matches.
- (T2) `MeasurableSet[filt d j] {ω | j < firstHit … ω}`: this matches the ticket and the source's
  claim that 1(j < τ) is F_j-measurable.
- (T3) Both families `F, F'` get their own thresholds `θ, θ'` over a common horizon `K'`. This gives
  the stopping time property and the `j < min` measurability, i.e. τ∧σ in the source. Matches.
  σ ("some bound fails") fits this form by taking `F' j` = the indicator of the failure set at
  time j and `θ' = 1`.
- No `∀ᶠ N` is involved. These are fixed-N filtration facts, and the parameters `d s t K N`
  come first. The range is `hittingBtwn … 0 K'`, i.e. j ∈ [0, K'], with value K' if the threshold is
  never hit. That is the source's capped min over the grid {0,…,K}: set K' = K N. Hitting at j = 0
  is allowed, which is consistent with the source §6 case "T = s".

## 3. Vacuity / hidden hypotheses / cycles

- The only hypothesis is `hF : ∀ j, Measurable (F j)` (and `hF'`). It uses Mathlib's standard
  `Matrix.instMeasurableSpace` (the product Borel structure). No structure fields and no extra
  assumptions. The theorems hold for every `d s t K N θ K'`, and `N = 0` or `K' = 0` makes them
  trivially true rather than vacuous.
- **Compiled satisfiability witness for the real application** (scratch file outside the repo,
  run with `lake env lean` in the audit worktree; it compiled with no errors):
  - `audit_resolvent_meas`: for any finite `n`, `z : ℂ`, `x y`, `θ0`, the map
    `M ↦ ‖(M - z • 1)⁻¹ x y‖ - θ0` is measurable on **all** of `Matrix n n ℂ`. This is a
    resolvent-entry threshold observable. The proof goes through `Matrix.inv_def`,
    `Ring.inverse_eq_inv'`, continuity of `det` and `adjugate`, and `measurable_inv`, so no
    Hermitian or invertibility restriction is needed.
  - An `example` that instantiates `isStoppingTime_min_firstHit_grid` with
    `F j = ‖(H_j - z j • 1)⁻¹ x y‖` and `F' j = ‖(H_j - z j • 1)⁻¹ x x‖`, with time-dependent
    spectral parameter `z j`.

  So the hypothesis holds for the intended loop-observable thresholds: J* is a finite max of such
  entries and products. The hypothesis is not stronger than needed (no continuity or boundedness is
  required). It is also not weaker than needed: measurability of `F j` is the natural minimal
  condition for adaptedness.
- Scope note (not a defect): the ticket fixes the form where J depends only on the current
  H_{u_j}. The source's τ and σ have exactly this form. A J that depends on the whole past path would
  need a different adapter, and the ticket does not ask for one.
- Cycles: the file imports only `GridPath` and `GridStop`, and neither imports it. None.

## 4. Dependencies

`H_adapted` (GridPath.lean, T1481, merged on `main` at ef7f0e4). `firstHit`,
`isStoppingTime_firstHit`, `lt_firstHit_measurableSet`, `isStoppingTime_min_firstHit` and
`lt_min_firstHit_measurableSet` (GridStop.lean, T1483, merged at be67a6b). Mathlib:
`Matrix.measurable_iff`, `stronglyMeasurable_iff_measurable`, `Measurable.comp`. All of these are
already accepted.

## 5. Builds and axioms

- `lake build RBM1D.Gauss.GridStopFilt` (audit worktree): `Build completed successfully (3703 jobs)`,
  with no errors and no warnings from GridStopFilt.lean.
- `lake build RBM1D` (audit worktree): exit 0, `Build completed successfully (9635 jobs)`. The root
  axiom audit line says: `20664 declarations in RBM, all within [propext, Classical.choice, Quot.sound]`.
  The root does not import the new module yet, so its axioms were checked separately.
- `#print axioms` for all six new declarations (scratch file importing `RBM1D.Gauss.GridStopFilt`):
  each depends on `[propext, Classical.choice, Quot.sound]` only.
- `grep` finds no `sorry`/`admit`/`axiom` in the new file. No frozen signature is touched, because
  the only change is a new file.

## Paper deltas

None required. These are pure filtration/API facts that match the source §4 claims verbatim.
