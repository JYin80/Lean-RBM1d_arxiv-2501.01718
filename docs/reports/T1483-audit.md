# T1483 (amend-1) audit — grid stopping times (pilot P3)

Auditor worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1483-audit` (detached at `t/T1483` = `9bf470f`;
the branch itself is checked out in the prover worktree). Audit date 2026-09-25T16:45Z.
Diff `main...t/T1483`: only `RBM1D/Gauss/GridStop.lean` (+135), the sole writable file. No root import
(ticket: "Root import: none"); `RBM1D.lean` untouched; no frozen signature touched.

## Overall verdict: PASS (all of T1–T5)

## Common checks
- Math preflight PASS for every target, written in the report before the Lean section (report §"Math preflight", §"Simultaneous satisfiability witness", then §"Lean").
- Step 0: confirmed that pinned Mathlib has no `MeasureTheory.hitting`; the API is `hittingBtwn u s n m` (`HittingTime.lean:56`, "else `m`"), which matches the ticket's "else `K`" convention exactly. The ticket told the prover to follow Mathlib and document the difference; this is done in the report and in the module docstring.
- Filtration: every statement uses the arbitrary variable `ℱ : Filtration ℕ m` over an arbitrary `{m : MeasurableSpace Ω'}`. It is not `⊤`, and nothing is specialised to a concrete filtration.
- Dependencies: Mathlib only (`hittingBtwn`, `hittingBtwn_le`, `notMem_of_lt_hittingBtwn`, `Adapted.isStoppingTime_hittingBtwn`, `IsStoppingTime.measurableSet_le`, Finset lemmas). No project dependency, so no cycle.
- Builds: `lake build RBM1D.Gauss.GridStop` gives "Build completed successfully (2987 jobs)", with no error, warning or `sorry` lines. `lake build RBM1D` gives "Build completed successfully (9324 jobs)". The module is not imported by the root, as the ticket specifies.
- Axioms (`#print axioms`, run by the auditor on all 9 declarations): only `[propext, Classical.choice, Quot.sound]`.
- grep: no `sorry` / `admit` / `axiom` in the file.

## Per target

**T1 `firstHit` — PASS.** `firstHit J θ K ω := hittingBtwn J (Set.Ici θ) 0 K ω`. This is the ticket's definition with `hitting` renamed to `hittingBtwn`, as required by Step 0. The threshold set is `Ici θ` (`θ ≤ J j ω`), the window is `[0,K]`, and the value is `K` when the threshold is never hit.

**T2 `isStoppingTime_firstHit`, `firstHit_le` — PASS.** Signature: `Adapted ℱ J → IsStoppingTime ℱ (fun ω => (firstHit J θ K ω : ℕ))`. The only hypothesis is `Adapted ℱ J`, the ℕ→`WithTop ℕ` coercion is the one Mathlib uses itself, and the filtration is the given `ℱ`. `firstHit_le : firstHit J θ K ω ≤ K` holds with no hypotheses.

**T3 `lt_firstHit_measurableSet`, `lt_firstHit_imp` — PASS.** `MeasurableSet[ℱ j] {ω | j < firstHit J θ K ω}` for every `j`, from `Adapted ℱ J`. `lt_firstHit_imp : j < firstHit J θ K ω → J j ω < θ` is strict. The strictness follows because the hit set is `Ici θ`, so non-membership means `J j ω < θ` (via `notMem_of_lt_hittingBtwn` with `n = 0`). No extra hypothesis is needed.

**T4 min — PASS (with a naming note).** The ticket lets the prover either prove `isStoppingTime_min` or cite Mathlib's `IsStoppingTime.min`. Mathlib's `IsStoppingTime.min` (`Stopping.lean:358`) covers an arbitrary `τ ⊓ σ`. The prover also added `isStoppingTime_min_firstHit`, `lt_min_firstHit_measurableSet` and `lt_min_firstHit_imp` for two `firstHit` times on the same horizon `K`. Their hypotheses are exactly `Adapted ℱ J`, `Adapted ℱ J'`. The "strictly below both thresholds" conclusion follows from `lt_min_iff` plus T3.
- This shape is general enough for σ in `pilot-P4P5-paper.md` §4 ("first failure of an input bound"). Take `J' j = indicator of the failure event at u_j` and `θ' = 1`. The same horizon `K` matches the grid.
- The name differs from the ticket's `isStoppingTime_min`. The ticket explicitly allows citing Mathlib instead, so this is not a defect. Downstream code that needs a σ which is not of `firstHit` form can use `IsStoppingTime.min` directly.

**T5 `sum_stopped` — PASS.** The statement matches the ticket character for character: `∑ j ∈ range (min k (τ ω)), Y (j+1) ω = ∑ j ∈ range k, ({ω' | j < τ ω'}.indicator (Y (j+1))) ω`, for any `AddCommMonoid M`, any `τ : Ω' → ℕ`, and any `k`, `ω`. It is a genuine identity. The right-hand side sums an explicit `Set.indicator` over the fixed range `range k`. The proof rewrites via `(range k).filter (· < τ ω) = range (min k (τ ω))` and `Finset.sum_filter`, so this is not a definitional restatement. Boundary cases `k = 0`, `τ ω = 0` and `τ ω ≥ k` are all covered because the statement is universal.

## Vacuity / witness (compiled by the auditor, scratch file, not committed)
- Witness: `Ω' = ℝ` (Borel), the constant filtration `F := ⟨fun _ => inferInstance, …⟩`, `J j ω = ω`, `θ = 1`, `K = 3`.
- Compiled facts:
  - `Adapted F J` holds.
  - `IsStoppingTime F (firstHit J 1 3)` holds.
  - `firstHit J 1 3 0 = 3`: the threshold is never hit, so the value is `K`.
  - `firstHit J 1 3 2 = 0`: an immediate hit.
  - `lt_firstHit_imp` gives `J 2 0 < 1` from `2 < firstHit J 1 3 0 = 3`.
- So the stopping time takes nondegenerate values in both regimes, and the strict-below conclusion is exercised with a nonempty window (`K = 3`). It does not rely on `N = 0`, an empty index set, a collapsed window, or a huge threshold.
- No structure fields and no hidden hypotheses.

## Open items (not defects for this ticket)
- The `filt d` specialisation (T1481, `RBM1D/Gauss/GridPath.lean`) is not instantiated because that file does not exist yet. The ticket states that (T1)–(T5) have no dependency in generic form, and the acceptance criteria list only the generic targets. A follow-up is needed once T1481 lands.
- No Lean/paper statement difference is introduced here. The N^δ threshold correction lives in the caller's choice of `θ`, so no paper-delta entry is needed for this module.
