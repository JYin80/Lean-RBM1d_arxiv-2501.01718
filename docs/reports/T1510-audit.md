Auditor model: claude-opus-5-5[1m]

# T1510 audit — weighted Duhamel sum for the drift terms, (5.39)–(5.41) on the grid

Branch `t/T1510` @ `9c5ac3e` (one commit, one file: `RBM1D/Gauss/GridDriftSum.lean`, +260).
Fresh audit worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1510-audit2`. The existing
`RBM1D-wt/T1510` and `RBM1D-wt/T1510-audit` were not used. All `GridDriftSum` build artefacts were
deleted before building, so the module was rebuilt from scratch.
Sources read: ticket, prove report, paper p. 57 ((5.39)–(5.41)) and p. 59 ((5.47)),
`docs/supervisor/2026-09-25-2045.md` §1, and the signature of `RBM.Step2.norm_Uker_le_of_tail`
(`Hierarchy/Step2.lean:448`) together with `xiK` (`:433`).

## Verdicts

| Target | Verdict |
|---|---|
| (T1) `RBM.Gauss.Grid.weighted_duhamel_sum_le` | **PASS** |
| (T2) `RBM.Gauss.Grid.weighted_duhamel_sum_stopped` | **PASS** |
| (aux) `RBM.Gauss.Grid.tailT_mono_time` (T1508 (T1) statement, reproved locally) | PASS (see merge note N1) |

## 1. Math preflight
The prove report's section (a) gives a math preflight with a PASS verdict for T1 and T2. It
comes before the Lean section (b). It covers the Step 0 checks the ticket asks for: `hAuv`,
`exp 1 ≤ W`, the meaning of `m` (so η_x = (1-x)m), `xiK`, and ℓ_u = `ellHat L u`. First line
`Prover model: claude-sonnet-5` is present.

## 2. Statement vs ticket / paper / supervisor note
- **(T1) conclusion.** The Lean conclusion is
  `‖(∑_{j<k} Δ • Uker L 1 u_{j+1} u_k (A j)) a‖ ≤ (∑_{j<k} Δ·M_j·((1-u_{j+1})/(1-u_k))²·xiK L W m) · tailT W ℓ̂(u_k) ((1-u_k)m) D (zdist(a₀-a₁))`.
  This is exactly the ticket formula. The right-hand side depends on the label `a` through
  `T_{u_k,D}(|a₁-a₂|)`. So the conclusion **keeps the T_{u_k} profile**. It is not a sup-norm
  bound, which is what supervisor §1 (last bullet) requires. The factor
  `((1-u_{j+1})/(1-u_k))² = (η_{u_{j+1}}/η_{u_k})²` is the paper's expansion factor
  `(η_u/η_t)²` from (5.40)/(5.41). `xiK = W^{o(1)}` is the known Lemma 7.1 near-window cost that
  the accepted kernel lemma already carries.
- **(T1) hypotheses.**
  - `hA` bounds each A_j against the T_{u_j} profile for j<k, with `M_j ≥ 0`.
  - `hAuv` is the side condition of `norm_Uker_le_of_tail` at the pair (u_{j+1}, u_k).
  - All other side conditions of that lemma are present: `3 ≤ L`, `0<m≤1`, `0≤u_{j+1}≤u_k<1`
    (from `u 0 ≥ 0`, step-monotone `u`, `u k < 1`), `exp 1 ≤ W`, and `M_j ≥ 0`.
  - `Δ ≥ 0` is a free scalar. Not tying Δ to u_{j+1}-u_j makes the statement more general,
    not weaker.
  - σ = (+,−) is encoded as ξ ≡ 1, n = 2. This matches the kernel lemma and supervisor §3(ii).
  - The statement is deterministic, with no `∀ᶠ N`, as the ticket specifies. There is no
    parameter-order issue.
- **(T2).** Here k is replaced by `min k (τ ω)`, and `hA`/`hAuv` are required only for
  `j < τ ω`. This matches the ticket verbatim. τ is an arbitrary function, which is appropriate
  for a pointwise corollary. The proof is (T1) at k' = min k (τ ω), using j < k' ⇒ j < τ ω.
- **Route.** The proof applies `norm_Uker_le_of_tail` termwise. It uses `tailT_mono_time` to
  bridge the T_{u_j} bound to a T_{u_{j+1}} bound, then applies `norm_sum_le` and
  `Finset.sum_mul`. This is the route the ticket prescribes.
- **No use of T1504 (T3).** The file imports only `RBM1D.Hierarchy.Step2`. The proofs cite only
  `Step2.norm_Uker_le_of_tail`, `Step3.ellHat_mono`, `ellHat_ofReal`,
  `one_le_ellHat_of_nonneg`, `tailT_nonneg`/`tailT_pos` and Mathlib. T1504 is named only in a
  docstring, to say that it is *not* used.

## 3. Vacuity, hidden hypotheses, cycles, boundary cases
- **`hAuv` is not a restriction.** It follows from grid monotonicity. The file proves
  `ℓ̂(v)(1-v) ≤ ℓ̂(u)(1-u)` for u ≤ v < 1 (private `ellHat_mul_one_sub_antitone`), via
  `ℓ̂(x)(1-x) = min(√(1-x), L(1-x))`. I checked this argument: it is correct and unconditional.
- **No hidden hypotheses.** There are no structure fields and no smuggled assumptions. No
  hypothesis forces `k = 0`, an empty sum, or a collapsed window. For k = 0 both sides are 0,
  which is true and harmless. The general k is covered.
- **Independent compiled witness (auditor's own scratch file, not committed).**
  - Data: `L = 3`, `W = 10`, `m = 1/2`, `D = 5`, `Δ = 1/4`, grid `u_j = j/4`, `k = 2`
    (distinct times 0, 1/4, 1/2), `M_j = 2`,
    `A_j b = 2·T_{u_j,D}(zdist(b₀-b₁))` (nonzero, label-dependent).
  - `hAuv` at j = 0 is the strict case (u₁ = 1/4, u₂ = 1/2). It was proved directly from
    `ellHat_ofReal`, not by `le_refl`.
  - `weighted_duhamel_sum_le` applies to this data, and the file compiles under
    `lake env lean` against the built module.
  - Nothing in the witness is astronomically large. The prover's in-file one-step witness
    (`section Witness`) also compiles.
- **No cycles.** The only dependency is the already-committed `norm_Uker_le_of_tail`.

## 4. Dependencies
Only accepted results are used: `norm_Uker_le_of_tail` (committed), `Step3.ellHat_mono` and basic
`ellHat`/`tailT` lemmas on main. T1508 is not merged (`state: proving`), so its (T1) is reproved
locally, as the ticket permits.

## 5. Build and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridDriftSum`: `Build completed successfully (3749 jobs)`, with no
  errors and no warnings in `GridDriftSum.lean`.
- `lake build RBM1D`: `Build completed successfully (9655 jobs)`, no errors. The root import is
  not on the branch; it is added at merge.
- A scratch file with `import RBM1D` plus `import RBM1D.Gauss.GridDriftSum` compiles, so there is
  no name clash with main.
- `#print axioms` for `tailT_mono_time`, `weighted_duhamel_sum_le` and
  `weighted_duhamel_sum_stopped` gives `[propext, Classical.choice, Quot.sound]`.
- There is no `sorry`/`admit`/`axiom` in the file. Only the one new file changed, so no frozen
  signature was touched.

## Notes (non-blocking, for dispatcher / hub)
- **N1 (merge coordination).** T1508's ticket names its (T1) `RBM.Gauss.Grid.tailT_mono_time`.
  That is the same fully-qualified name T1510 declares here. If T1508 declares it again,
  root-importing both modules will fail with a duplicate declaration. T1508's own ticket says
  "cite it if it already exists", so T1508 should import `RBM1D.Gauss.GridDriftSum` (or rename)
  if T1510 merges first. If T1508 merges first, T1510 needs a one-line change before merge:
  drop the local copy and import T1508's.
- **N2 (downstream interface).** (T1)/(T2) need the drift bound against the T_{u_j} profile, as
  the ticket specifies. The paper's (5.35)/(5.36) normalise by T_t instead. Since T_t ≥ T_u, a
  T_t-profile bound does not imply a T_{u_j}-profile bound. The Step 2 assembly must therefore
  supply the pointwise drift bounds (T1501/T1502/(5.34)) in T_{u_j} normalisation on
  {j < τ}, which is natural from J*_{u_j,D}.
- **N3 (paper-deltas).** The grid Riemann-sum form (U_{u_{j+1},u_k}, free Δ), the T_{u_j}
  normalisation of the hypothesis, and the explicit `xiK` factor are Lean/paper formulation
  differences fixed by the ticket. The prover could not write `docs/paper-deltas.md` (sole
  writable file), so the dispatcher may want a `T1510a` entry.
- `hAuv` is redundant given grid monotonicity. It is kept because the ticket lists it. A
  public version of `ellHat_mul_one_sub_antitone` would let callers discharge it; it is
  currently `private`.
