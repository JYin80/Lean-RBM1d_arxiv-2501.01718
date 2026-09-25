Auditor model: claude-opus-5-5[1m]

# T1491 audit — (5.36) in the proof-exponent shape

Audited commit: `e8ec942` (branch `t/T1491`; audit worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1491-audit`,
detached at `e8ec942` because `t/T1491` is already checked out in the prover worktree).
Diff vs `main`: exactly one new file, `RBM1D/Hierarchy/Lemma57Reduced.lean` (+136). `Lemma57.lean`
and `RBM1D.lean` untouched (empty diff). No root import (ticket: none).

## Overall verdict: PASS (T1 PASS, T2 PASS)

## 1. Math preflight
`docs/reports/T1491-prove.md` §0–§1 contain Step 0 and a per-target math preflight (T1 PASS, T2 PASS)
placed before the proof/build sections (§2–§4). Step 0 correctly confirms that `ee_le_paper` is proved
from `ee_le` with the ticket's `μ`, so there is no hypothesis gap. OK.

## 2. Statement vs ticket / paper

**(T1) `RBM.Lemma57.ee_le_reduced`.**
- Hypotheses: I compared the binder block from `theorem ee_le_reduced` through the colon with the one
  of `ee_le_paper` (`Lemma57.lean:1874–1892`) programmatically, after normalizing whitespace. They are
  identical: same names, order, implicit/explicit status and types (`hW hℓu hℓs hηu hJ hA hr a₁ a₂
  {Gsq L6 ρ EE} hρ hL6 hGsq h273 h564 h42sq h566 h572 hsym hEE`). The section variables
  `(L : ℕ) [NeZero L]` and `{W ℓu ℓs ηu D J : ℝ}` match the `EE` section. No new hypothesis.
- Conclusion: it matches the ticket formula term for term:
  `ηu⁻¹ * (cNear2·(ℓu/ℓs)^5·1[zdist ≤ 4ℓ*] + cFar2·(r·√r·(√A)⁻¹)·J^2 + 72·J^3·A⁻¹)·T^2 +
  (W L ρ + 2 W L W^(-D) J^3 T^2)`.
  The far bracket keeps `J²·r^{3/2}A^{-1/2}` and `J³·A^{-1}` as **separate** terms. This is the
  (5.71)/(5.72) shape (pilot §9 (B)) and is not the merged `(cFar2+72)·r^{3/2}A^{-1/2}·J³` of
  `ee_le_paper`.
- Route: `ee_le` with `μ := r·√r·((√A)⁻¹·A⁻¹)` (the same `μ` as in `ee_le_paper`), then
  `A·μ = r·√r·(√A)⁻¹` by `field_simp`, then `ring` for an equality. No merge and no loss. So the
  conclusion is exactly `ee_le`'s RHS at this `μ`.
- Parameter order: unchanged from `ee_le_paper`. This is deterministic finite algebra with no `∀ᶠ N`.
  Losses/constants `cNear2`, `cFar2` (the `W^{o(1)}` factors `log W`, `loss1 W`), the `r^{3/2}` factor
  (Jun's ruling in delta #113 ③), the far-`b` remainder `ρ` and the `W^{-D}` floor summed over `L`
  are all kept explicit, as in the accepted `ee_le`/`ee_le_paper`.

**(T2) `RBM.Lemma57.ee_le_paper_of_reduced`.**
- LHS is verbatim `ee_le_reduced`'s RHS. RHS is verbatim `ee_le_paper`'s RHS. The hypotheses are
  `hW hℓu hℓs hηu hJ hA hr` (they include the ticket's `1 ≤ J`, `1 ≤ Wℓuηu`, `1 ≤ ℓu/ℓs`, plus
  positivity facts that `ee_le_paper` already assumes). `a₁ a₂ ρ` are free.
- This is a pointwise RHS comparison, as the ticket asks ("`ee_le_paper`'s right-hand side is ≥
  `ee_le_reduced`'s"). With `ee_le_reduced` it re-derives `ee_le_paper`, which confirms that (T1) is
  the sharper statement. OK.

## 3. Vacuity / hidden hypotheses / cycles
- No new hypotheses. All hypotheses are inherited verbatim from the accepted `ee_le_paper`, and no
  structure fields are involved.
- `L6`, `Gsq`, `EE` appear only through upper bounds with nonnegativity, so the hypotheses are
  monotone and satisfiable at every admissible parameter point. No parameter is forced to collapse:
  `W, ℓu ≥ 1`, `ℓs, ηu > 0`, `J ≥ 1`, `A ≥ 1`, `r ≥ 1`, with `L`, `D`, `a₁`, `a₂` free.
- Compiled witness (scratch file outside the source tree, checked with `lake env lean` against the
  built module): `L = 7`, `W = 2`, `ℓu = 4`, `ℓs = 1`, `ηu = 1`, `D = 3`, `J = 2`, `a₁ = 0`, `a₂ = 3`
  (distinct), `Gsq ≡ 0`, `L6 ≡ 0`, `ρ = 0`, `EE = -1`. Every hypothesis of `ee_le_reduced` is
  discharged and the theorem instantiates. The parameters are nondegenerate (`r = 4`, `A = 8`, `L > 1`,
  `a₁ ≠ a₂`). No `N = 0` or empty-index loophole: `L` carries `[NeZero L]`. (T2) has only the
  normalization inequalities, which are satisfiable at the same point.
- Boundary cases: all inverses are of strictly positive quantities (`ηu > 0`, `A ≥ 1`, `√A > 0`,
  `ℓs > 0`). The indicator is the classical `if` on `ℝ`, the same as in `ee_le`.
- No cycle. The new file imports only `RBM1D.Hierarchy.Lemma57`, and nothing in the repository imports
  it.

## 4. Dependencies
`RBM.Lemma57.ee_le` (committed on main), `cFar2_nonneg`, `tailT_nonneg` (committed), and Mathlib
lemmas only. All of these are accepted results. `ee_le_paper` is not used in the proof. It is only the
comparison target in (T2).

## 5. Build / axioms / forbidden tokens
- `lake build RBM1D.Hierarchy.Lemma57Reduced`: `Build completed successfully (2956 jobs)`, no errors.
- `lake build RBM1D`: `Build completed successfully (9636 jobs)`, no errors. The root does not import
  the new file, as the ticket specifies.
- `#print axioms RBM.Lemma57.ee_le_reduced`: `[propext, Classical.choice, Quot.sound]`.
- `#print axioms RBM.Lemma57.ee_le_paper_of_reduced`: `[propext, Classical.choice, Quot.sound]`.
- `grep sorry|admit|axiom` on the new file: nothing. No frozen signature touched, because
  `Lemma57.lean` has an empty diff.

## 6. Observations (non-blocking, for the dispatcher)
- The prover report says pilot §9 candidate (ii) ("Lemma 5.7 uses the proof exponents (5.55)(5.63)
  (5.71)(5.72), not the displayed (5.35)(5.36)") is "already recorded" in `docs/paper-deltas.md`. I
  found no such entry: grepping for `5.72)`, `pilot`, `T1488`, `proof exponent` gave no match. The
  closest entry is #113 ③, which covers only the `r^{3/2}` factor. `ee_le_reduced` states (5.36) in a
  shape different from the display, so CLAUDE.md §3.7 calls for a delta entry. `docs/paper-deltas.md`
  is outside this ticket's sole writable files, so this is not a prover defect. The dispatcher should
  record candidate (ii).
- Style-linter warnings only (unused variables in the new file). No action needed.
