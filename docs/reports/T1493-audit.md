Auditor model: claude-opus-5-5[1m]

# T1493 audit: (5.36) proof-exponent shape for `EEpath` (target M5)

Branch `t/T1493`, head `ec7d0f9`. Audited in detached worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1493-audit` (the branch itself is checked out in the prover
worktree). Diff vs `main`: exactly one new file, `RBM1D/Hierarchy/EEReduced.lean` (+165), the
ticket's sole writable file. No other file touched; no frozen signature changed.

## Verdicts

| Target | Verdict |
|---|---|
| (T1) `RBM.EEDef.ee_le_reduced_EEpath_sym` | **PASS** |
| (T2, optional) `RBM.Lemma57.ee_le_reduced_sym` | **PASS** |

## 1. Math preflight

`docs/reports/T1493-prove.md` §1 contains a math preflight with verdict PASS for both targets,
placed before §2 (Lean declarations/build). Step 0 checks of `ee_le_EEpath_sym`,
`ee_le_paper_EEpath_sym`, `ee_le_sym`/`ee_le_paper_sym` and T1491's `ee_le_reduced` recorded.

## 2. Statement vs ticket / paper

- Hypotheses (T1): the binder list (lines 102-126) is textually identical to
  `ee_le_paper_EEpath_sym` (EEDef.lean:1359-1383) — checked by `diff` after renaming. That is,
  `ee_le_EEpath_sym`'s list plus `hA`, `hr`, `hμbd`, same order. This satisfies the ticket's
  acceptance criterion "the hypotheses are those of `ee_le_paper_EEpath_sym`"; the target prose
  "plus `hμbd`, as in `ee_le_paper_EEpath_sym`" reads the same way. Nothing added, nothing dropped.
- Hypotheses (T2): binder list textually identical to `Lemma57.ee_le_paper_sym`
  (Lemma57.lean:2711-2730), checked by `diff`.
- Conclusion (T1): `ηu⁻¹ * (cNear2·r⁵·1(dist ≤ 4ℓ*) + cFar2·(r√r·(√A)⁻¹)·(2J)² +
  72·(2J)³·A⁻¹) · T² + (W L ρ + 2 W L W^(-D) (2J)³ T²)`. The `J²` term and the `J³·A⁻¹` term are
  separate summands (auditor check 1). Remainders are verbatim those of `ee_le_paper_EEpath_sym`
  (auditor check 2 covers hypotheses; remainders also match). Shape is exactly T1491's
  `ee_le_reduced` conclusion (Lemma57Reduced.lean:55-58) instantiated at `J := 2J`,
  `a₁,a₂ := lab₁ c, lab₂ c`, `W := B.W N`, `L := B.L N`.
- Relation to paper: this is the unmerged (5.71)+(5.72) form of (5.36); it implies the displayed
  merged form under `hJ`, `hA` (as `ee_le_paper_of_reduced` shows abstractly), so it is not a
  weaker variant. Near/far indicator at `4ℓ*_u`, loop length 2, `a' = a` (`hc0`,`hc1`, paper-delta
  #113 ①) are inherited unchanged from the accepted `ee_le_*_EEpath_sym` family; no new
  Lean/paper difference, so no paper-delta needed.
- Parameter order: same as the donor lemmas (deterministic, pathwise statement at fixed
  `X,E,N,u,ω,σ,c`; no `∀ᶠ N` involved).

## 3. Vacuity / hidden hypotheses / cycles

- No new hypothesis. Joint satisfiability of the exact list is the already-accepted
  `RBM.EEDef.ee_sym_hyp_consistent` (EEDef.lean:1447), whose statement lists every hypothesis of
  `ee_le_paper_EEpath_sym` (incl. `hA`, `hr`, `hμbd`) for arbitrary labels `a₁,a₂` and `a' = a`.
  Witness: `ℓu = 1`, `ηu = W⁻¹` (A_u = 1), `D = 0`, `ℓs = R⁻¹`, `J = 1 + S + M²`; `N`, `L N`,
  `W N` untouched (no `N = 0`/empty-index loophole; `ZMod (B.L N)` with `NeZero`).
- No structure field carries hypotheses; all assumptions are explicit binders.
- `hr` is unused in (T2)'s proof (linter warning) and only forwarded in (T1); it is kept to match
  the donor hypothesis list, as in T1491's precedent. Carrying an unused, satisfiable hypothesis
  is harmless.
- No cycle: the new file imports only `RBM1D.Hierarchy.EEDef`; no existing file references the new
  names (grep).

## 4. Dependencies

`Lemma57.ee_le_sym`, `cNear2`, `cFar2`, `EEDef.eeL6_two_le_near₁/₂`, `eeL6_two_le_far`,
`norm_EEpath_le_W_sum`, `lab₁/lab₂`, `one_le_W`, `tailT_nonneg` — all in committed, merged
modules on `main`. (T1491's `ee_le_reduced` is not used; T2 re-derives its sym twin.)

## 5. Build, axioms, forbidden tokens

- `lake build RBM1D.Hierarchy.EEReduced`: `Build completed successfully (3731 jobs)`; only
  warning in the new file: `EEReduced.lean:46:41: Variable name hr is not explicitly referenced`.
- `lake build RBM1D`: `Build completed successfully (9639 jobs)`, no errors. (Root import of
  `EEReduced` is added at merge per ticket; the branch's `RBM1D.lean` does not yet import it.)
- `#print axioms` (scratch file, `lake env lean`):
  `RBM.Lemma57.ee_le_reduced_sym` and `RBM.EEDef.ee_le_reduced_EEpath_sym` depend on
  `[propext, Classical.choice, Quot.sound]` only.
- No `sorry`/`admit`/`axiom` in the new file.

## Merge note

Merge only `RBM1D/Hierarchy/EEReduced.lean`; add `import RBM1D.Hierarchy.EEReduced` to the root.
