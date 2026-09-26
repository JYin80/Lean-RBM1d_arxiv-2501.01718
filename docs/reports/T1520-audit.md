Auditor model: claude-opus-5-5

# T1520 audit, round 2: grid bootstrap (R4c-2a), repair of the amended (T3)/(T4)

Date: 2026-09-26 11:11 UTC. Branch `t/T1520` at `0fc3fd3`, which sits on top of `651f006` (base `db76845`). Against its base, the branch touches only `RBM1D/Gauss/GridBootstrap.lean`, the ticket's sole writable file (+466 lines, of which +250 are new in `0fc3fd3`). `git diff main` also lists files that were deleted since the fork. That happens only because `main` has moved on (T1518 and T1521 were merged after `db76845`); the branch itself deletes nothing.

Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1520-audit`, a detached checkout of `0fc3fd3`. It is separate from the prover's worktree. Live spec: the AMEND NOTE at the top of `docs/tickets/T1520.md`. (T1) and (T2) already had PASS in round 1 and their code is unchanged, so they were not re-audited in depth.

## Overall verdict: **PASS**

## 1. Math preflight
`docs/reports/T1520-prove.md` contains "Math preflight for the amended targets (written 2026-09-26 11:03 UTC, before any new Lean)", with a PASS for (T3′a), (T3′b), (T3′c) and (T4′). The repair commit `0fc3fd3` is dated 11:07:13 UTC, so the ordering is consistent. The first line of the report is `Prover model: claude-opus-5-5`. **PASS.**

## 2. Amended (T3′)

### `GridPointwise'` (def, line 226): matches the amend note exactly
- Binder order: `∀ D > 0, ∀ u : ∀ N, TimeIcc s t N, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ D₁ > 0, ∃ K : ℕ → ℕ, (∀ N, K N ≠ 0) ∧ (∃ C, 0 ≤ C ∧ ∀ᶠ N, (K N + 1 : ℝ) ≤ N^C) ∧ ∀ᶠ N, Pg d bad ≤ ofReal (N^(-D₁))`.
- K is chosen after both δ and D₁, so it may depend on both, as the note allows. C is chosen together with K.
- Placement of δ₀: `∃ δ₀ > 0` comes right after `u` and before `∀ δ`. That is the placement fixed in the round-1 audit. Letting δ₀ depend on (D, u) is harmless, because `hpt` is proved from it with a fixed conclusion (see below).
- Bad set: `{ω | ∃ p, N^δ · ((η_s/η_{u N})⁴ · scale⁻² · decayProf N (u N) D p.1 p.2) < lkErrMat d E N (u N) (H d s u K N (K N) ω) (pmLoop p.1 p.2)}`.
  - This is literally `badSet` (`Defs/StochDom.lean:82`), using T1517's `GridPointwise` integrand and bound (`Step2Gauss.lean:152–162`), at exponent δ.
  - The labels range over the full `ZMod (d.L N)²`, the energy is E, and the window is `[s N, t N]`.
- The old `GridPointwise` is left unchanged, as the note requires.

### `hpt_of_gridPointwise'` (line 277): **PASS**
- The conclusion is character-for-character the `hpt` binder of `step2_gauss_of_pointwise` (`Step2Gauss.lean:191–195`). The composition below type-checks, which confirms this.
- The only extra hypothesis is `hs0 : ∀ N, 0 ≤ s N`, which step2 also assumes.
- Route, for StochDom's target τ and exponent D₁:
  - It takes δ := min τ δ₀ and obtains `K = K(min τ δ₀, D₁)`.
  - Then, **for each N separately**, it applies `pg_bad_eq_flow`. That lemma (line 242) uses `map_H_eq` at `k = K N`, rewritten by `time_last`, to identify the image laws of `H_{K N}` and `Hflow(u N)`, with both events written as preimages of one measurable matrix set (via `measurable_lkErrMat`). This turns the grid probability into the flow probability of `{∃ p, N^δ ζ < lkErr(u N)}`.
  - Finally, `N^{min τ δ₀} ≤ N^τ` for N ≥ 1, together with the nonnegativity of ζ, puts the flow bad set at τ inside the one at δ.
- The flow event does not involve K, so letting K depend on (δ, D₁) cannot leak into `hpt`. No path identity is inferred from `H_u = √u X`; only one-time laws are used (CLAUDE.md §3.5).

### `step2_gauss_of_gridPointwise'` (line 309): **PASS**
- Its body is `step2_gauss_of_pointwise d … (hpt_of_gridPointwise' d hs0 hgp)`.
- Its hypotheses are exactly those of T1517's `step2_gauss_of_grid`, with `GridPointwise'` in place of `GridPointwise`.
- A scratch check compiles a type ascription: `step2_gauss_of_gridPointwise' … hgp : type_of% (step2_gauss_of_grid … _)`. So the conclusion is syntactically step2's second conclusion pair, at `X := sample d`.

### Non-vacuity of `GridPointwise'`
- `gridPointwise'_of_gridPointwise` (line 330) takes δ₀ := 1 and, for every (δ, D₁), the same K and C. It is correct.
- The committed `example` (line 339) derives `GridPointwise'` from step2's own (2.76) conjunct for `sample d`. It uses the nondegenerate grid `K ≡ 1`, `C = 1` (`2 ≤ N` eventually) and `stochDom_grid_iff_flow`.
- No loophole: `N = 0` is not used, the label set is not empty, the window is not collapsed, and no parameter is astronomically large.
- The round-1 audit's example also derived the old `hend` from `Step2.jS_stochDom`. Hence the whole chain `(5.47) ⇒ GridPointwise ⇒ GridPointwise'` is satisfiable.

## 3. Amended (T4′): `endpoint_of_bootstrap'` (line 390), **PASS**

### Statement
- τ ω := `min (firstHit (j ↦ jSMat d E D N u_j (H_j ω) − thr E s δ N u_j) 0 (K N) ω) (firstHit (J' N) θ' (K N) ω)`.
- Hypotheses:
  - `hK0 : ∀ N, K N ≠ 0`;
  - `HighProb (Pg d) G`;
  - `hgood : ∀ ω ∈ G N, ∀ j ≤ K N, J' N j ω < θ'` (the good set holds at every j, so the second hitting time never fires);
  - `hat : ∀ ω ∈ G N, J_{τ ω} ω < thr(u_{τ ω})`.
- Conclusion: `HighProb {τ = K N ∧ jSMat d E D N (u N) (H_{K N}) < thr E s δ N (u N)}`.
- The hypothesis is imposed **only at the random target τ**. There is no quantifier over k and no union over k, as the note requires. The conclusion is `τ = K ∧ J_K < thr(u_K)`, with `u_K = u N` obtained from `time_last`.

### Proof
- The deterministic core is `min_firstHit_eq_of_at` (line 367).
  - `hgood` and `firstHit_eq_of_below` give that the second `firstHit` equals K. So τ is the first hit a of `J − thr`, and a ≤ K.
  - If a < K, then `hittingBtwn_mem_set_of_hittingBtwn_lt` gives `J_a − thr_a ≥ 0`, which contradicts `hat`.
  - Therefore τ = K, and `hat` at τ = K together with `time_last` gives the endpoint bound.
- No strong induction is used. The old (T1) is kept only as the pre-existing lemma.

### Agreement with `gridTau`
- `main` has no `gridTau`.
- In the T1519 worktree, `GridGoodEvent.lean:59–64` (uncommitted T1519 repair work) defines `gridTau` as exactly this `min` of two `firstHit`s: the second process is `1_{goodSet(u_j)ᶜ}(H_j)` at level `1/2`.
- (T4′)'s generic `J'`/`θ'` therefore specialises to it. The prover reports a scratch `rfl` check. I confirmed that the shapes match syntactically, but did not re-compile the check, because T1519 is not merged. Keeping `J'` generic is a generalisation, not a special case.
- **Merge-time item for R4c-2b:** instantiate with the merged `gridTau` there.

### Non-vacuity (compiled by the auditor)
The scratch file is `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM1D/c89db6b5-4fbc-4b34-995c-1e741f3b37d2/scratchpad/AuditT1520r2.lean`; it is not part of the branch. It compiles with no errors and produces a fully nondegenerate instance of (T4′). The assumptions are step2's own: `Step2.Hyp (sample d) E s t`, `BoundsCore`, `hs0`, `hst`, `ht1`, `hc0`, `hreg`, `60 ≤ D` and `0 < δ`. Steps:
- Take the grid `K ≡ 1`, the genuine `J_j = jSMat`, the genuine `thr`, `J' := 0` and `θ' := 1`.
- Set `G N := {J_0 < thr(u_0)} ∩ {J_1 < thr(u_1)}`.
- Each factor is HighProb (auxiliary theorem `auditHP`). The proof applies `Step2.jS_stochDom` (5.47) at τ = δ/2 and transfers it to the grid through `jS_grid_law` (`map_H_eq`), using `time_zero` and `time_last`.
- Strictness comes from `N^{δ/2} R⁴ < N^δ R⁴`. This uses N ≥ 2 and `R > 0` (from `etaT_pos'`); no large parameter is needed.
- `hat` holds on G because τ ≤ 1 forces τ ∈ {0, 1}.
- `endpoint_of_bootstrap'` then applies and gives its conclusion.

This shows the hypotheses can hold together with actual Step-2 data. The committed `example` at line 435 additionally shows that the old (T4) hypotheses imply the new `hat`.

## 4. Dependencies and cycles
- Imports: `Gauss.Step2Gauss` (T1517) and `Gauss.GridStop`.
- New lemmas used: `map_H_eq`, `time_last`, `H_measurable_filt`, `filt`, `RBM.measurable_H`, `measurable_lkErrMat`, `step2_gauss_of_pointwise`, `stochDom_grid_iff_flow` (used only in the example), `firstHit_le`, `hittingBtwn_mem_set_of_hittingBtwn_lt` and `HighProb.mono`.
- All of these are merged and accepted (T1481, T1507, T1517 and earlier) or come from Mathlib.
- No cycle. The derivation of `GridPointwise'` from step2's conclusion appears only in an `example`, used as a non-vacuity witness.

## 5. Builds, axioms, forbidden tokens
- `lake build RBM1D.Gauss.GridBootstrap` in the audit worktree: **Build completed successfully (3895 jobs)**, exit 0. The two local warnings are old and cosmetic: the unused `hM` (line 81) and the deprecated `Set.mem_setOf_eq` (line 153).
- `lake build RBM1D`: **Build completed successfully (9666 jobs)**, exit 0. The root import is added at merge, per the ticket.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 13 declarations: `GridPointwise'`, `pg_bad_eq_flow`, `hpt_of_gridPointwise'`, `step2_gauss_of_gridPointwise'`, `gridPointwise'_of_gridPointwise`, `min_firstHit_eq_of_at`, `endpoint_of_bootstrap'`, `below_of_bootstrap`, `firstHit_eq_of_below`, `min_firstHit_eq_of_below`, `lk_le_of_jS`, `gridPointwise_of_endpoint` and `endpoint_of_bootstrap`.
- A grep of the file finds no `sorry`, `admit`, `axiom`, `opaque`, `unsafe` or `implemented_by`.
- No frozen signature is touched: this is a new file, and `GridPointwise` and `step2_gauss_of_grid` are unchanged.

## Per-target verdicts
| Target | Verdict |
|---|---|
| (T1) `below_of_bootstrap`, `firstHit_eq_of_below`, `min_firstHit_eq_of_below` | PASS (round 1, unchanged) |
| (T2) `lk_le_of_jS` | PASS (round 1, unchanged) |
| old (T3) `gridPointwise_of_endpoint`, old (T4) `endpoint_of_bootstrap` | kept as extra lemmas; correct against the original spec |
| (T3′) `GridPointwise'`, `hpt_of_gridPointwise'`, `step2_gauss_of_gridPointwise'` | **PASS** |
| (T4′) `endpoint_of_bootstrap'` (with `min_firstHit_eq_of_at`) | **PASS** |

## Paper deltas
None needed. K(δ, D₁) exists only on the grid: it never appears in `hpt`/(2.76), whose flow event has no K. (T4′) uses the step bound only at the stopping time, which is how the paper's (5.43) bootstrap argues.

## Notes for R4c-2b (not defects)
- Instantiate (T4′) with the merged `gridTau` (`J' N j := 1_{goodSet(u_j)ᶜ}(H_j)`, `θ' := 1/2`). The `hgood` hypothesis then says "the good set holds at every j ≤ K N" on G.
