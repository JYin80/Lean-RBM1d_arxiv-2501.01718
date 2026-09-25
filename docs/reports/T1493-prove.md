Prover model: claude-sonnet-5

# T1493: (5.36) proof-exponent shape for `EEpath` (target M5)

## 1. Math preflight (before any Lean)

Source: `docs/reports/T1488-prove.md` §3, target **M5**:

> `ee_le_reduced_EEpath_sym`: the hypotheses of `EEDef.ee_le_EEpath_sym` plus `hμbd` (as in
> `ee_le_paper_EEpath_sym`), with the conclusion **not merged**:
> `… ≤ η_u⁻¹(cNear2·r⁵·1(≤4ℓ*_u) + cFar2·(2J)²·r^{3/2}A_u^{-1/2} + 72(2J)³A_u⁻¹)·T² + (remainders)`.

Step 0 (read-only checks), done by reading the three theorems named in the ticket plus T1491:

- `RBM.EEDef.ee_le_EEpath_sym` (EEDef.lean:1294): (5.36) for `MomentDuhamel.EEpath` at loop
  length 2, `a' = a` (`hc0`,`hc1`), abstract `μ = 2√Smax`. Built from `Lemma57.ee_le_sym`
  applied at `J := 2*J` and `a₁,a₂ := lab₁ c, lab₂ c`.
- `RBM.EEDef.ee_le_paper_EEpath_sym` (:1359): same hypotheses plus `hA : 1 ≤ A_u`,
  `hr : 1 ≤ ℓ_u/ℓ_s`, `hμbd : 2√Smax ≤ r√r·(√A_u)⁻¹·A_u⁻¹`; conclusion **merged**
  `(cFar2+72)·r^{3/2}A_u^{-1/2}·(2J)³`. Proof: instantiate the abstract `μ` of the two
  `eeL6_two_le_near₁/₂` bounds via `hμbd`, then call `Lemma57.ee_le_paper_sym` directly.
- `RBM.Lemma57.ee_le_sym` (Lemma57.lean:2661) / `ee_le_paper_sym` (:2711): the abstract,
  `hsym`/`h566`-free pair. `ee_le_paper_sym`'s proof calls `ee_le_sym` with the concrete
  `μ := r√r·(√A)⁻¹·A⁻¹`, rewrites `A·μ = r√r·(√A)⁻¹` (`hAμ`, by `field_simp`), then merges
  `cFar2·J²·ν + 72·J³·A⁻¹ ≤ (cFar2+72)·ν·J³` (needs `hJ23 : J² ≤ J³`, itself from `hJ`).
- T1491's `RBM.Lemma57.ee_le_reduced` (Lemma57Reduced.lean:36): the **non-sym** analogue,
  built from the master `ee_le` (which needs `h566`/`hsym`), by the identical `hAμ` rewrite
  but **stopping before** the merge step. Its own hypothesis list keeps `hA`,`hr` (docstring:
  "exactly `ee_le_paper`'s hypotheses"), even though the proof shown does not use `hr` and
  uses `hA` only to shortcut `0 < A` via `linarith`.

Consequence for M5: the same "stop before the merge" move applies one rung up, to the `sym`
family, and needs **no** `h566`/`hsym` (T190's point already removes them from `ee_le_sym`).
Concretely: apply `Lemma57.ee_le_sym` at the concrete `μ := r√r·(√A)⁻¹·A⁻¹` (the same `μ`
`ee_le_paper_sym` uses), rewrite `A·μ = r√r·(√A)⁻¹` by the identical `hAμ`, and stop — no
`hbr`/`hJ23` merge step. This gives exactly the target unmerged bracket
`cFar2·J²·(r√r·(√A)⁻¹) + 72·J³·A⁻¹`, i.e. (with `J := 2*J`, `a₁,a₂ := lab₁ c, lab₂ c`) the
target's `cFar2·(2J)²·r^{3/2}A_u^{-1/2} + 72·(2J)³·A_u⁻¹`.

Checks:
- **Statement vs. paper formula / dependencies.** (5.36) is (5.71)+(5.72) of the paper; the
  Lean master `Lemma57.ee_le`/`ee_le_sym` is already accepted (T156/T190, merged), and T1491's
  `ee_le_reduced` is already accepted (merged, `docs/reports/T1491*`). No new external input;
  everything is a rearrangement of already-proved inequalities.
- **Hypotheses / quantifier order.** Ticket's target text says "plus `hμbd`", but the
  ticket's acceptance criteria is explicit and more precise: "the hypotheses are those of
  `ee_le_paper_EEpath_sym`" — i.e. `ee_le_EEpath_sym`'s list plus `hA`, `hr`, `hμbd` (all
  three `ee_le_paper_EEpath_sym` adds). I follow the acceptance criterion literally: the new
  theorem's hypothesis list is byte-for-byte `ee_le_paper_EEpath_sym`'s list (same names, same
  types, same order), only the conclusion is unmerged. This also matches T1491's own choice
  (`ee_le_reduced` keeps `ee_le_paper`'s full list, `hr` included, though unused in the proof).
  No hypothesis is added beyond that list; none is dropped; the ∀-order (fixed `X,E,N,u,ω,σ,c`
  before the real/function parameters, as in the source lemmas) is preserved.
- **Simultaneous satisfiability.** `RBM.EEDef.ee_sym_hyp_consistent` (EEDef.lean:1447) already
  proves joint satisfiability of every hypothesis of both `ee_le_EEpath_sym` **and**
  `ee_le_paper_EEpath_sym` — which is exactly the union `ee_le_EEpath_sym` ∪ `{hA,hr,hμbd}` I
  am reusing verbatim. No new hypothesis is introduced, so no new witness is needed; I did not
  re-derive it, only checked (by reading) that its statement lists `hA`, `hr`, `hμbd` and the
  full `ee_le_EEpath_sym` list, and that its witness section explains `hμbd` is satisfiable
  with room to spare (`R^{3/2} ≥ R ≥ 1+4Smax⁺ ≥ 2√Smax`).
- **Boundary cases.** The `if … then 1 else 0` split (near/far, at `4ℓ*_u`) is inherited
  unchanged from `ee_le_sym`; `D`, `ρ` are free with only `0 ≤ ρ`; no `N = 0`/empty-index
  degeneracy is introduced since nothing about `N`, `L N`, `W N` changes.
- **J² vs J³·A⁻¹ separateness** (the auditor's first check): by construction the conclusion
  literally has `cFar2·(...)·(2J)^2` as one summand and `72·(2J)^3·(...)⁻¹` as a separate
  summand of the same three-term sum inside the outer parentheses, mirroring `ee_le_sym`'s own
  (never-merged) shape — there is no `ring`/`nlinarith` step between them that could hide a
  further merge.

**Verdict: PASS**, both for (T1) `RBM.EEDef.ee_le_reduced_EEpath_sym` and for the optional
(T2) `RBM.Lemma57.ee_le_reduced_sym`.

## 2. Declarations added, build, axioms

File: `RBM1D/Hierarchy/EEReduced.lean` (new; the ticket's sole writable file).

- `RBM.Lemma57.ee_le_reduced_sym` (optional twin, T2): (5.36) for the abstract `sym` layer
  (no `h566`/`hsym`), in the unmerged shape; same hypotheses as `Lemma57.ee_le_paper_sym`.
  Proof: `ee_le_sym` at the concrete `μ`, then `hAμ` (`field_simp`) + `ring`, no merge step —
  literally T1491's `ee_le_reduced` proof with `ee_le`/`h566`/`h572`/`hsym` replaced by
  `ee_le_sym`/`hnear₁`/`hnear₂`/`hfarb`.
- `RBM.EEDef.ee_le_reduced_EEpath_sym` (T1, the ticket's named target, M5): (5.36) for
  `MomentDuhamel.EEpath` at loop length 2, `a' = a`, in the unmerged shape. Proof: identical
  wiring to `ee_le_paper_EEpath_sym` (the same `h42sq'` doubling and the same
  `eeL6_two_le_near₁/₂`/`eeL6_two_le_far` calls), but the final call is to
  `Lemma57.ee_le_reduced_sym` instead of `Lemma57.ee_le_paper_sym`.

Build:
```
lake build RBM1D.Hierarchy.EEReduced
```
Result: `Build completed successfully (3731 jobs)`, module built (`⚠ [3731/3731] Built
RBM1D.Hierarchy.EEReduced (3.4s)`). One linter-only warning (not an error): `hr` in
`ee_le_reduced_sym` is unused in the proof body (kept in the signature deliberately, to match
`ee_le_paper_sym`'s exact hypothesis list, per the acceptance criterion and per T1491's own
precedent). No `sorry`, no `admit`, no `axiom`.

Axioms (`lake env lean` on a scratch file importing the module):
```
'RBM.Lemma57.ee_le_reduced_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EEDef.ee_le_reduced_EEpath_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms.

## 3. Key lemmas used

`RBM.Lemma57.ee_le_sym`, `RBM.Lemma57.cNear2`/`cFar2`, `RBM.EEDef.eeL6_two_le_near₁`/`_near₂`/
`_far`, `RBM.EEDef.norm_EEpath_le_W_sum`, `RBM.EEDef.lab₁`/`lab₂`, `RBM.tailT_nonneg`,
`RBM.EEDef.one_le_W`. Reused (not modified) for satisfiability: `RBM.EEDef.ee_sym_hyp_consistent`.

## 4. Open issues

- None specific to this ticket. M5 was scoped as "instance plus algebra"; no new hypothesis,
  no new witness, and no paper-delta was needed.
- As noted in the preflight, the ticket's item-(T1) prose ("plus `hμbd`") is slightly looser
  than its own acceptance criterion ("the hypotheses are those of `ee_le_paper_EEpath_sym`");
  I followed the acceptance criterion (the more specific, auditor-facing text), which also
  matches T1491's precedent of keeping the full donor hypothesis list. Flagging this only so
  the auditor checks the same reading; no paper-delta is warranted since both readings agree
  on the sole substantive content (the unmerged conclusion) and the stricter reading is a
  superset, so nothing was left out.
