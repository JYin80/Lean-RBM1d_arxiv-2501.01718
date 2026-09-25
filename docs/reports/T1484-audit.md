# T1484 (amend-1) — audit report

Auditor run: 2026-09-25T17:22Z. Ticket: `docs/tickets/T1484-amend-1.md`. Prove report:
`docs/reports/T1484-prove.md`. Branch `t/T1484` at `75059b85`, audited in a detached worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1484-audit`. (`git worktree add` refused the branch itself
because the prover's worktree still has it checked out.)

**Overall verdict: PASS** (all five targets).

## Scope of the diff
`git diff --stat main...t/T1484`: one file only, `RBM1D/Gauss/GridAzuma.lean` (+344). That is the
ticket's sole writable file. No existing file is changed, so no frozen signature is touched, and
no root import was added (the ticket says "Root import: none").

## Gate 1: math preflight
The prove report §(a) has a per-target math preflight marked PASS, written before the Lean. It
includes the Step 0 checks: the exact signatures of `measure_sum_ge_le_of_hasCondSubgaussianMGF`
and `maximal_ineq`, and the finding that Mathlib has no `Martingale.stoppedProcess`. It also
records that the pilot failure signal (BDG, Burkholder or continuous-time calculus needed) did
not trigger. **OK.**

## Gate 2: statement vs ticket (the math source is pilot-P4P5-paper §4, §9(A); no paper formula numbers)
- **(T1) `azuma_two_sided`** — **PASS.**
  - The hypotheses `StronglyAdapted ℱ Y`, `HasSubgaussianMGF (Y 0) (c 0) μ` and
    `∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i+1)) (c (i+1)) μ` match the ticket
    verbatim.
  - `c : ℕ → ℝ≥0` is deterministic, as the acceptance criterion requires.
  - With `ε ≥ 0` the conclusion is `μ.real {ε ≤ |∑_{i<n} Y i|} ≤ 2 exp(-ε²/(2∑_{i<n} c i))`,
    exactly as in the ticket.
  - The extra instance `[StandardBorelSpace Ω']` does not add an assumption: the Mathlib
    definition of `HasCondSubgaussianMGF` requires it (SubGaussian.lean:535).
  - Boundary case `∑ c = 0`: Lean's `x/0 = 0` makes the bound `2`, which is trivially true. The
    statement stays consistent.
- **(T2) `azuma_complex`** — **PASS.**
  - The six hypotheses are the (T1) hypotheses for `Re Z` and for `Im Z`, with the same
    deterministic `c`.
  - The conclusion `μ.real {ε ≤ ‖∑ Z i‖} ≤ 4 exp(-ε²/(4∑ c i))` matches the ticket. The constant
    is the sharp √2 split, not the weaker `8∑c`.
- **(T3) `doob_L2_max`** — **PASS.**
  - The hypotheses are: a martingale `M`, `M 0 = 0`, `∀ k, MemLp (M k) 2 μ`, and `0 < x`.
  - The conclusion is
    `μ.real {x ≤ (range (K+1)).sup' _ (fun k => |M k ω|)} ≤ (∫ (M K)²)/x²`.
  - It bounds the maximum over **all** `k ≤ K` at once, as the acceptance criterion requires.
  - `hM0` is not used in the proof (`_hM0`). It is in the ticket's statement, so keeping it is
    faithful. The only effect is a statement slightly weaker than it could be, which is harmless.
- **(T4) `martingale_sq_eq_sum`** — **PASS.** The hypotheses are the same as (T3). The conclusion
  `∫ (M K)² = ∑_{k<K} ∫ (M(k+1) - M k)²` matches the ticket.
- **(T5) `stopped_martingale`** — **PASS.**
  - The hypotheses are `Martingale M ℱ μ`, `τ : Ω' → ℕ` and
    `IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ))`. The conclusion is
    `Martingale (fun k ω => M (min k (τ ω)) ω) ℱ μ`.
  - The ticket says "bounded stopping time". The Lean statement does not require a uniform bound;
    it only requires `τ` to be ℕ-valued (finite). So its hypotheses are weaker than the ticket's
    and the conclusion is the same. The bounded case the ticket asks for is a direct
    instantiation, so the Lean statement generalizes the target rather than restricting it.
    Mathlib's `Submartingale.stoppedProcess` has no boundedness hypothesis either.
  - Downstream note: a consumer must present `τ` as an ℕ-valued function (e.g. a grid hitting
    time capped at `K`), coerced to `WithTop ℕ`.

## Gate 3: vacuity
- There are no bespoke hypotheses. Every hypothesis is a standard Mathlib predicate, and the (T1)
  bundle is exactly the hypothesis list of Mathlib's `measure_sum_ge_le_of_hasCondSubgaussianMGF`.
  No structure fields hide assumptions. There is no `N = 0`, empty-index or collapsed-window
  loophole: `n` and `K` are free, and `range 0` gives the correct trivial edge case.
- **Compiled witness (auditor's own scratch file, not in the branch):**
  `.../scratchpad/T1484Witness.lean`. It was compiled with `lake env lean` in the audit worktree.
  It has no errors, and every witness's axioms are `[propext, Classical.choice, Quot.sound]`.
  It instantiates all five theorems with the nondegenerate Gaussian example the ticket asks for,
  on `Ω' = ℝ` with `μ = gaussianReal 0 1`:
  - (T1) `T1_gauss`: `Y 0 = id`, which is N(0,1) with a compiled
    `HasSubgaussianMGF id 1 (gaussianReal 0 1)` from `mgf_fun_id_gaussianReal`. Also
    `Y i = 0` for `i ≥ 1`, `c = (1,0,0,…)`, `n = 2`. Since `∑ c = 1`, the conclusion is the
    genuine bound `2 exp(-ε²/2)`.
  - (T2) `T2_gauss`: `Z i = Y i·(1+i)`, so both the real and the imaginary part are N(0,1).
  - (T3), (T4) `T3_gauss`, `T4_gauss`: the martingale is `M k = E[X | ℱ k]` with
    `ℱ 0 = ⊥`, `ℱ k = full` for `k ≥ 1` and `X ~ N(0,1)`. Compiled facts: `M 0 = 0` exactly,
    `M 1 = id` (so the example is nonzero), and every `M k` is in `L²`.
  - (T5) `T5_gauss`: the same `M` with `τ ≡ 1`.
  - The ticket's zero witness (`Y ≡ 0`, `c ≡ 0`) is covered by Mathlib's `@[simp]` lemmas
    `stronglyAdapted_zero`, `HasSubgaussianMGF.fun_zero` and `HasCondSubgaussianMGF.fun_zero`.
- In the Gaussian witness, the conditional hypothesis `h_subG` is met only by a zero later
  increment. For a *nonzero* `HasCondSubgaussianMGF` instance, the repository already has an
  accepted compiled one: `uniformPerm_prefixFourierDoobAzuma_two_witness` on `main`, in
  `RBM1D/Gauss/PermutationFourierDoobAzumaScalar.lean`, imported in the root. It is a nonconstant
  conditional increment with `c = 16`. This is enough to show the predicate is not vacuous. A
  conditional-Gaussian (independent increment) instance would need the "freezing" lemma that the
  pilot paper §9 already lists as separate P4 engineering. It is not a gap in this ticket.
- There is no circular dependency: the file imports only Mathlib.

## Gate 4: dependencies
Only Mathlib is used: `SubGaussian`, `OptionalStopping`, and the conditional-expectation API. No
repository declaration is used, and the ticket lists none. **OK.**

## Gate 5: builds and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridAzuma` succeeded ("Build completed successfully (3203 jobs)") with
  no errors or warnings.
- `lake build RBM1D` succeeded ("Build completed successfully (9324 jobs)"). GridAzuma is not
  imported in the root, per the ticket.
- The printed axioms for all five public declarations are
  `[propext, Classical.choice, Quot.sound]`.
- `grep` finds no `sorry`, `admit` or `axiom` in the file. The one `private` helper is
  `condExp_sq_eq_add`.

## Paper deltas
None needed. This is generic probability with no paper formula, and it makes no Brownian or
`√u·X` claim.

## Verdicts
| Target | Verdict |
|---|---|
| (T1) `azuma_two_sided` | PASS |
| (T2) `azuma_complex` | PASS |
| (T3) `doob_L2_max` | PASS |
| (T4) `martingale_sq_eq_sum` | PASS |
| (T5) `stopped_martingale` | PASS (the Lean statement drops the boundedness assumption; the bounded target follows directly) |
