# T1485-amend-1 — discrete Duhamel telescoping identity (pilot P5)

Role: prover. Branch `t/T1485`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1485`.
Sole writable file: `RBM1D/Gauss/GridDuhamel.lean`.

## Step 0 (read-only checks)

* `RBM.Uker_self` (`RBM1D/Hierarchy/Kernel.lean:282`):
  `Uker_self (hL : 3 ≤ L) {n} {ξ} {t} (ht : ∀ i, ‖t * ξ i‖ < 1) (A) : Uker L ξ t t A = A`.
* `RBM.Uker_comp` (`Kernel.lean:306`):
  `Uker_comp (hL : 3 ≤ L) {n} {ξ} {s u t} (hu : ∀ i, ‖u * ξ i‖ < 1) (ht : ∀ i, ‖t * ξ i‖ < 1) (A) :
    Uker L ξ u t (Uker L ξ s u A) = Uker L ξ s t A`.
  Side condition on the *start* time `s` is **not required** (only on the middle time `u` and the
  end time `t`); this matches `edgeKer_mul`'s hypotheses, which only need `‖u*ξ‖<1`, `‖t*ξ‖<1`.
* `RBM.Uker_duhamel` (grepped: it lives in `RBM1D/Gauss/Step6HierarchyGauss.lean:293`, not in
  `Kernel.lean`; it is the *continuous* Itô/Duhamel formula for `Uker`, not needed for (T1)-(T4)
  here, which only use `Uker_comp`/`Uker_self`). No side condition beyond `hL`, `ht`, plus the
  differentiability data it needs (irrelevant to this ticket).
* Dependency check: `RBM.Uker`, `RBM.Uker_comp`, `RBM.Uker_self` are already committed
  (`Kernel.lean`, present on `main`). `T1481`'s `time` function is **not merged**
  (`docs/queue/T1481.state`: `state: claimed`), so per the ticket's fallback, (T3)/(T4) below are
  stated for an arbitrary sequence `u : ℕ → ℝ`, which is at least as strong as the specialisation
  to `time s t K N`.

## Math preflight (per target)

**(T1) `duhamel_telescope`** — generic additive group telescoping identity.
Statement: `V` an `AddCommGroup`, `U : ℕ → ℕ → V →+ V` with `U k k = id` (∀k) and
`(U j k).comp (U i j) = U i k` for `i ≤ j ≤ k`, `A : ℕ → V`, `k : ℕ`:
`A k - U 0 k (A 0) = ∑_{j<k} U (j+1) k (A (j+1) - U j (j+1) (A j))`.

* Hypotheses vs conclusion: standard induction on `k`.
  - `k = 0`: LHS `= A 0 - U 0 0 (A 0) = A 0 - A 0 = 0` (using `U 0 0 = id`); RHS is the empty sum
    `= 0`. Equal.
  - `k → k+1`: split the RHS sum at `k` via `Finset.sum_range_succ`. The tail term is
    `U (k+1)(k+1) (A(k+1) - U k (k+1)(A k)) = A(k+1) - U k(k+1)(A k)` (self-law). For `j < k`,
    rewrite `U (j+1)(k+1) = (U k (k+1)).comp (U (j+1) k)` (comp-law with `i:=j+1 ≤ k`, `j:=k`,
    `k:=k+1`), pull `U k (k+1)` out of the sum by `map_sum` (it is additive), and apply the
    induction hypothesis to the inner sum `∑_{j<k} U(j+1) k (...) = A k - U 0 k (A 0)`. Then
    `U k(k+1) (A k - U 0 k (A0)) = U k(k+1)(Ak) - U k(k+1)(U 0 k(A0))` (`map_sub`), and
    `(U k(k+1)).comp(U 0 k) = U 0 (k+1)` (comp-law `i:=0≤k, j:=k, k:=k+1`). Summing the two pieces
    telescopes exactly to `A(k+1) - U 0(k+1)(A0)`. **Verified by hand, holds unconditionally
    given the two structural hypotheses; no missing case.**
* Quantifier order: `V`, `U`, its two structural hypotheses, then `A`, then `k` — matches the
  natural order (parameters before the "grid size" `k`, analogous to fixed parameters before
  `∀ᶠ N`).
* Dependencies: none beyond Mathlib (`AddCommGroup`, `AddMonoidHom`, `Finset.sum_range_succ`,
  `map_sum`, `map_sub`) — self-contained algebra, no RBM-specific input.
* Boundary case `k = 0`: checked above, non-vacuous (empty sum, both sides genuinely `0` via the
  self-law, not by convention alone).
* Non-triviality / satisfiability of hypotheses (CLAUDE.md §3.4, and the auditor's explicit
  check against `U ≡ id`): take `V := ℝ`, fix `r : ℝ` with `r ≠ 1` (e.g. `r = 2`), and
  `U j k := r ^ (k - j) • (AddMonoidHom.id ℝ)` bundled as an `AddMonoidHom` (scalar multiplication
  by a fixed real is additive). Then `U k k = r^0 • id = id`, and for `i ≤ j ≤ k`,
  `(U j k).comp (U i j) = r^(k-j) * r^(j-i) • id = r^((k-j)+(j-i)) • id = r^(k-i) • id = U i k`
  since `(k-j)+(j-i) = k-i` in `ℕ` exactly because `i ≤ j ≤ k` (no truncation). This `U` is
  **not** `U ≡ id` (`r = 2 ≠ 1` makes `U 0 1 ≠ id`), so the hypotheses are satisfiable by a
  genuinely non-trivial family, and the identity is not a disguised tautology. This witness is
  recorded in the report; I will not clutter the acceptance-relevant file with it unless asked,
  but can add it as a `example`/`#check` if the auditor wants a compiled witness — **added as a
  compiled example in the file, see below, to leave no doubt.**
* Verdict: **PASS**.

**(T2) `duhamel_telescope_stopped`** — same identity with `k` replaced by `min k (τ ω)` for
`τ : Ω' → ℕ`, per fixed `ω`.
* This is literally an application of (T1) at the natural number `min k (τ ω)` in place of `k`;
  no new hypotheses, no probabilistic content (it is a per-`ω`, i.e. pointwise, restatement — no
  measurability, adaptedness or expectation is claimed here, matching the ticket's description
  "a corollary of (T1)"). Trivial substitution, no boundary issue (`min k (τ ω)` is always a
  well-defined `ℕ`, including when `τ ω = 0` or `k = 0`).
* Verdict: **PASS**.

**(T3) `Uker_grid_semigroup`** — the family `fun j k => Uker ξ (u j) (u k)` (bundled as
`AddMonoidHom`s) satisfies (T1)'s hypotheses, for `u : ℕ → ℝ` an arbitrary sequence (T1481's
`time` is not merged, so using the ticket's sanctioned fallback, which is at least as strong).
* Needed hypothesis: `∀ k i, ‖(u k : ℂ) * ξ i‖ < 1` (smallness at **every** grid time, since any
  index can play the role of "middle" or "end" time in the comp-law, and every index needs the
  self-law). This is exactly the hypothesis `Uker_self`/`Uker_comp` already need pointwise — no
  hypothesis is added beyond what the existing lemmas require.
  - `U k k = id`: `Uker_self hL (hu k) A = A`, for every `A` — apply `funext`/`AddMonoidHom.ext`.
  - `(U j k).comp(U i j) = U i k` for `i ≤ j ≤ k`: `Uker_comp hL (hu j) (hu k) A`, note this
    only needs `hu` at `j` (the middle time) and `k` (the end time), not at `i` — consistent with
    `Uker_comp`'s actual hypotheses (no `hs`).
* Simultaneous satisfiability of `∀ k i, ‖(u k:ℂ)*ξ i‖<1`: e.g. `u` any bounded sequence with
  `|u k| ≤ M` for all `k` (true of any genuine grid `time s t K N` on a compact window `[s,t]`)
  and `ξ` with `‖ξ i‖ < 1/(M+1)`, `ξ ≠ 0` — non-degenerate (`ξ_i` can be any small nonzero
  complex number, `u` any nonconstant bounded sequence, e.g. `u k = (k : ℝ)/(k+1)` bounded by 1).
  Not vacuous, not requiring `N` astronomically large, no collapsed window.
* Verdict: **PASS**.

**(T4) `Uker_factor`** — factorisation `Uker ξ (u(j+1)) (u k) = (Uker ξ (u k) t)⁻¹ ∘ Uker ξ (u(j+1)) t`,
stated positively as `Uker ξ (u k) t ∘ Uker ξ (u(j+1)) (u k) = Uker ξ (u(j+1)) t`, together with
two-sided invertibility of `Uker ξ (u k) t` (explicit inverse `Uker ξ t (u k)`, no quantitative
bound on the inverse — matches the ticket's explicit exclusion of a quantitative bound).
* The equation is `Uker_comp hL (hu : ‖(u k:ℂ)*ξ i‖<1) (ht : ‖(t:ℂ)*ξ i‖<1) A` with
  `s := u (j+1)`, `u := u k`, `t := t` — a direct instance, **no hypothesis on `u (j+1)`
  needed** (matches `Uker_comp`'s actual signature, which has no `hs`).
* Invertibility: both directions are needed.
  - `Uker ξ (u k) t (Uker ξ t (u k) B) = B`: `Uker_comp hL hu ht B` with `s := t`, `u := u k`,
    `t := t`, then `Uker_self hL ht B` — uses exactly `hu`, `ht` (no extra hypothesis).
  - `Uker ξ t (u k) (Uker ξ (u k) t B) = B`: `Uker_comp hL ht hu B` (roles of `hu`,`ht` swapped:
    middle time is `t`, end time is `u k`) with `s := u k`, then `Uker_self hL hu B`.
  Both use only `hu` (at `u k`) and `ht` (at `t`) — the "same conditions as in `Uker`'s existing
  lemmas" the ticket asks for; no side condition on the intermediate index `j` beyond what is
  already assumed for the equation.
* Simultaneous satisfiability: same witness family as (T3) (bounded `u`, small nonzero `ξ`, and
  `t` in the same bounded range) — non-degenerate.
* Verdict: **PASS**.

## Overall preflight verdict: PASS for (T1)-(T4).

No target is blocked; T1481's non-merge only forces stating (T3)/(T4) for an arbitrary real
sequence `u : ℕ → ℝ` rather than the concrete grid `time s t K N`, exactly as the ticket
anticipates and licenses.

---

## Lean work

File: `RBM1D/Gauss/GridDuhamel.lean` (namespace `RBM.Gauss.Grid`).

### Declarations added

* `duhamel_telescope` — (T1), the generic telescoping identity for `U : ℕ → ℕ → V →+ V`
  (`V` an `AddCommGroup`) satisfying `U k k = id` and `(U j k).comp (U i j) = U i k` for
  `i ≤ j ≤ k`. Proved by induction on `k` using `Finset.sum_range_succ`, `map_sum`, `map_sub`,
  and the two structural hypotheses, exactly following the hand proof in the preflight.
* `duhamel_telescope_stopped` — (T2), corollary of (T1) at `k := min k (τ ω)`, per `ω`.
* `UkerHom` — `RBM.Uker` bundled as `(LoopArg L n → ℂ) →+ (LoopArg L n → ℂ)` via
  `AddMonoidHom.mk'` and `RBM.Uker_add`, plus `UkerHom_apply` (`@[simp]`) unfolding it to `Uker`.
  (Helper, not one of the four named targets, needed to state (T3) in `AddMonoidHom` language.)
* `Uker_grid_semigroup` — (T3): for an arbitrary `u : ℕ → ℝ` and `hu : ∀ k i, ‖(u k:ℂ)*ξ i‖<1`,
  the family `fun j k => UkerHom L ξ (u j) (u k)` satisfies both structural hypotheses of (T1),
  proved directly from `RBM.Uker_self` and `RBM.Uker_comp` via `AddMonoidHom.ext`.
* `Uker_factor` — (T4): for `u : ℕ → ℝ`, `t : ℝ`, `hu` at `u k`, `ht` at `t`, gives the
  equation `Uker ξ (u k) t (Uker ξ (u (j+1)) (u k) A) = Uker ξ (u (j+1)) t A` (an instance of
  `Uker_comp`) together with both directions of two-sided invertibility of `Uker ξ (u k) t`
  (explicit inverse `Uker ξ t (u k)`, via `Uker_comp` + `Uker_self` each way). No hypothesis on
  `u (j+1)` is used, matching the preflight.
* A compiled `example` (non-degeneracy witness for (T1)): the scalar family
  `r^(k-j) • id` on `ℝ` with `r = 2 ≠ 1` satisfies the exponent identity
  `(k-j)+(j-i) = k-i` for `i ≤ j ≤ k` (checked by `omega`), witnessing that (T1)'s hypotheses
  admit non-identity solutions.

### Build

```
$ lake build RBM1D.Gauss.GridDuhamel
✔ Built RBM1D.Gauss.GridDuhamel (2428 jobs)
```

### Axioms (of all six new public declarations)

```
'RBM.Gauss.Grid.duhamel_telescope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.duhamel_telescope_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.UkerHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.UkerHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.Uker_grid_semigroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.Uker_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms; no `sorry`/`admit`/declared `axiom` anywhere in the file
(grepped, none found).

### Key lemmas used

`RBM.Uker_self`, `RBM.Uker_comp`, `RBM.Uker_add` (`Kernel.lean`); `Finset.sum_range_succ`,
`map_sum`, `map_sub`, `AddMonoidHom.mk'`, `AddMonoidHom.ext`, `AddMonoidHom.comp_apply` (Mathlib).

### Open issues

* T1481 (`time`) is not yet merged; (T3)/(T4) are stated for an arbitrary `u : ℕ → ℝ` as the
  ticket's fallback licenses. Once T1481 merges, a thin specialisation
  `Uker_grid_semigroup (time s t K N)` / `Uker_factor (time s t K N)` can be added (not done here
  — out of this ticket's scope, and would need T1481's exact monotonicity/domain facts, which are
  not available in this worktree).
* No paper-delta entries needed: this ticket is pure algebra plus direct instances of already-
  accepted `Kernel.lean` lemmas; nothing in the paper's displayed formulas is contradicted or
  amended.

## Commit

Committed `RBM1D/Gauss/GridDuhamel.lean` only, on branch `t/T1485`.
