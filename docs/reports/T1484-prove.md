# T1484 (amend-1) — prove report

Ticket: `docs/tickets/T1484-amend-1.md`. Role: prover-hard. Sole writable file:
`RBM1D/Gauss/GridAzuma.lean`. Branch `t/T1484`, worktree `../RBM1D-wt/T1484`.

Scope: pure probability on an arbitrary probability space `(Ω', μ)` with a
filtration `ℱ : Filtration ℕ _`; nothing RBM-specific (per the ticket's math
source, `docs/claude-team/pilot-P4P5-paper.md` §4, §9). No paper formula
numbers are targeted directly; the gate is agreement with the cited Mathlib
statements (pinned `lake-manifest.json`, inputRev v4.34.0) and internal
consistency of the derivations built from them.

## (a) Math preflight (before any Lean)

Step 0 checks (ticket §11):

* `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`
  (`Mathlib/Probability/Moments/SubGaussian.lean:921`, confirmed at the pinned
  revision): signature `[StandardBorelSpace Ω] [IsZeroOrProbabilityMeasure μ]
  (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
  (n : ℕ) (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
  (Y (i+1)) (cY (i+1)) μ) {ε : ℝ} (hε : 0 ≤ ε) : μ.real {ω | ε ≤ ∑ i ∈
  range n, Y i ω} ≤ exp (-ε^2 / (2 * ∑ i ∈ range n, cY i))`. Matches the
  ticket's (T1) hypothesis list and quantifier order exactly (`h0` fixed at
  index `0`, `h_subG` ranging over `i < n - 1` producing `Y (i+1)`, i.e. all
  indices `1..n-1`). `IsZeroOrProbabilityMeasure` is implied by
  `IsProbabilityMeasure` via a standard instance.
* `MeasureTheory.maximal_ineq` (`Mathlib/Probability/Martingale/
  OptionalStopping.lean:144`): `(hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
  {ε : ℝ≥0} (n : ℕ) : ε * μ {ω | (ε:ℝ) ≤ (range (n+1)).sup' _ (fun k => f k
  ω)} ≤ ENNReal.ofReal (∫ ω in {...}, f n ω ∂μ)`. Bounds the maximum over
  `k ∈ range (n+1) = {0,…,n}` simultaneously (T3's requirement). No
  boundedness/finite-second-moment side hypothesis beyond `Submartingale` +
  nonnegativity, so (T3)'s square-integrability hypothesis is exactly what is
  needed to build the submartingale `(M k)^2` (via the conditional-variance
  identity below), not an extra unused assumption.
* (T5): Mathlib has `Submartingale.stoppedProcess`
  (`OptionalStopping.lean:95`) but no direct `Martingale.stoppedProcess`.
  Built T5 from `Submartingale.stoppedProcess` applied to `M` and `-M`
  (`Martingale.submartingale`, `Martingale.neg`), recombined via
  `martingale_iff`. This is the "T1483 (T5)-style" route the ticket
  anticipated, using Mathlib building blocks rather than a from-scratch
  indicator-sum proof.
* Failure signal check: no target needs continuous-time stochastic calculus,
  BDG/Burkholder, or any statement beyond the two cited Mathlib theorems plus
  elementary conditional-expectation algebra (`condExp_add`, `condExp_sub`,
  `condExp_of_stronglyMeasurable`, the pull-out lemma
  `condExp_mul_of_stronglyMeasurable_left`, `condExp_nonneg`,
  `integral_condExp`) and elementary real/complex inequalities
  (`pow_le_pow_iff_left₀`, `Complex.norm_le_sqrt_two_mul_max`). Verdict: no
  BDG/Burkholder needed anywhere. **PASS** to proceed.

Per-target preflight:

* **(T1) `azuma_two_sided`.** Statement vs. Mathlib: apply the cited lemma to
  `Y` (upper tail) and to `-Y` (lower tail, using
  `Kernel.HasSubgaussianMGF.neg` and `StronglyAdapted.neg`, both present in
  Mathlib for `AddGroup`/`ContinuousNeg` targets, satisfied by `ℝ`), then
  `{|S| ≥ ε} = {S ≥ ε} ∪ {S ≤ -ε}` (`le_abs`) and subadditivity
  (`measureReal_union_le`, no side conditions). Quantifiers: `∀ Y c
  (h_adapted) (n) (h0) (h_subG) ∀ ε ≥ 0`, matching the paper-independent,
  purely-Mathlib-quantifier order requested. Hypotheses simultaneously
  satisfiable non-vacuously: the degenerate case `Y ≡ 0, c ≡ 0` satisfies
  every hypothesis via the `@[simp]` Mathlib lemmas
  `stronglyAdapted_zero`, `HasSubgaussianMGF.fun_zero`,
  `HasCondSubgaussianMGF.fun_zero` (checked by inspection of
  `Mathlib/Probability/Moments/SubGaussian.lean:573-577`); a genuinely
  nonzero instance of the same hypothesis shape (`StandardBorelSpace` +
  `IsProbabilityMeasure` + a nonzero, non-degenerate
  `HasCondSubgaussianMGF`) is already compiled in this repository at
  `RBM1D/Gauss/PermutationFourierDoobAzumaScalar.lean`
  (`uniformPerm_prefixFourierDoobAzuma_two_witness`, width-2 permutation
  space, explicit nonzero increment with `c = 16`), so the hypothesis
  bundle is not vacuous even in the nonzero case; I did not re-derive a
  fresh from-scratch nonzero witness inside `GridAzuma.lean` itself (would
  need to construct a bespoke `StandardBorelSpace`/filtration/kernel from
  first principles; low expected value given the existing repo precedent
  under the identical typeclass shape). Flagged for the auditor. **PASS**
  (with this one open item flagged, not a blocking gap).
* **(T2) `azuma_complex`.** Derived from (T1) applied to `Re Z` and `Im Z`
  (same `c`), using the sharp split `ε ≤ ‖z‖ ⟹ ε/√2 ≤ |Re z| ∨ ε/√2 ≤ |Im z|`
  (via `Complex.norm_le_sqrt_two_mul_max : ‖z‖ ≤ √2 * max |z.re| |z.im|`),
  giving two applications of (T1) at `ε/√2`, each contributing
  `2 exp(-(ε/√2)²/(2Λ)) = 2 exp(-ε²/(4Λ))`; union bound sums these to
  `4 exp(-ε²/(4Λ))`, matching the ticket's target exactly (I checked this
  is tighter than the naive `‖z‖ ≤ |Re z| + |Im z|` triangle-inequality
  split at `ε/2`, which would only give the weaker `4 exp(-ε²/(8Λ))`).
  Hypotheses restated as six explicit conditions on `Re Z`/`Im Z` (adapted,
  `h0`, `h_subG`, both real and imaginary) — a literal transcription of "the
  real and imaginary parts each satisfy the hypotheses of (T1)". **PASS.**
* **(T3) `doob_L2_max`.** Reduces to `maximal_ineq` for the submartingale
  `k ↦ (M k)^2`. The submartingale property (`(M i)^2 ≤ᵐ[μ] μ[(M j)^2 | ℱ i]`
  for `i ≤ j`) needed a from-scratch computation (`condExp_sq_eq_add`,
  private) since Mathlib has no `ConvexOn`/Jensen route to submartingales at
  this pin: `M j = M i + (M j - M i)`, expand the square, the cross term
  `2 M i (M j - M i)` has conditional expectation `0` a.e. (pull-out lemma
  `condExp_mul_of_stronglyMeasurable_left` + the martingale property + `M i`
  being its own conditional expectation), and the remainder
  `(M j - M i)^2` has nonnegative conditional expectation
  (`condExp_nonneg`). Boundary case `x → 0⁺`: excluded by the hypothesis
  `0 < x` (needed since `maximal_ineq`'s `ε : ℝ≥0` is matched to `x^2`, and
  the `x ≤ |M k ω|` vs. `x^2 ≤ (M k ω)^2` equivalence uses
  `pow_le_pow_iff_left₀`, valid for `x ≥ 0`; `x = 0` would make the LHS event
  the whole space while the bound could still be vacuous only if `∫(M K)^2
  = 0`, not a hypothesis failure but the ticket does not ask for `x = 0`).
  The conclusion's `sup'` ranges over `range (K+1) = {0,…,K}`, i.e. bounds
  the maximum over **all** `k ≤ K` simultaneously, as the acceptance
  criterion demands. Witness: `M ≡ 0` (all hypotheses hold trivially,
  `Martingale` zero process, `MemLp 0 2 μ` trivial); nondegenerate witness
  deferred to the same argument as (T1) (any nonzero centered i.i.d. random
  walk built via `Measure.pi`, as in the pilot paper's own P1 construction,
  is `Martingale`+`MemLp 2`; not separately compiled here). **PASS** (same
  flagged item as T1).
* **(T4) `martingale_sq_eq_sum`.** One-step case (`j = i+1`) of the same
  `condExp_sq_eq_add` identity, integrated over `μ` via
  `integral_condExp` (tower property, `∫ μ[f|m] = ∫ f`, holds unconditionally
  even through `condExp`'s junk value for non-integrable `f`), then summed by
  induction on `K` using `M 0 = 0`. No hidden hypothesis: `hM0` is used in the
  `K = 0` base case only. **PASS.**
* **(T5) `stopped_martingale`.** `τ : Ω' → ℕ` (i.e. genuinely `ℕ`-valued, so
  automatically bounded — no `⊤` value is possible, matching "bounded
  stopping time" without adding an extra unused boundedness hypothesis
  beyond what the type already guarantees) with
  `IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ))`. Conclusion stated as
  `Martingale (fun k ω => M (min k (τ ω)) ω) ℱ μ`, matching the ticket's
  informal `fun k => M (min k τ)` literally (verified
  `stoppedProcess M τ' k ω = M (min k (τ ω)) ω` via `WithTop.coe_min` +
  `WithTop.untopA` unfolding at a coercion, which is `rfl`). Built from
  `Submartingale.stoppedProcess` applied to `M` (`Martingale.submartingale`)
  and to `-M` (`Martingale.neg`, `.submartingale`), combined via
  `martingale_iff`. No boundedness side-hypothesis added beyond what `τ : Ω'
  → ℕ` already forces. **PASS.**

Simultaneous satisfiability of hypotheses across all five targets: none of
`azuma_two_sided`, `azuma_complex`, `doob_L2_max`, `martingale_sq_eq_sum`,
`stopped_martingale` add any hypothesis beyond what each proof route
consumes (verified above per target); no vacuous `N = 0` / empty index set /
collapsed window is forced (`n`, `K` are free `ℕ` parameters, `range 0` gives
the correct trivial empty-sum edge case, exercised directly in `T4`'s `K = 0`
base case).

## (b) Declarations, build, axioms

Namespace: `RBM.Gauss.Grid`. File: `RBM1D/Gauss/GridAzuma.lean` (only file
touched, per the ticket's sole-writable-file list).

Declarations added (all public, plus one `private` helper):
* `RBM.Gauss.Grid.azuma_two_sided`
* `RBM.Gauss.Grid.azuma_complex`
* `RBM.Gauss.Grid.doob_L2_max`
* `RBM.Gauss.Grid.martingale_sq_eq_sum`
* `RBM.Gauss.Grid.stopped_martingale`
* `RBM.Gauss.Grid.condExp_sq_eq_add` (private; shared core lemma used by T3
  and T4)

Build (in worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1484`):
```
lake build RBM1D.Gauss.GridAzuma
```
Result: `Build completed successfully (3203 jobs).` No warnings, no
`sorry`/`admit`/declared `axiom`.

`#print axioms` (appended at the end of the file, matching repo precedent in
`RBM1D/Gauss/PermutationFourierDoobAzumaScalar.lean`):
```
'RBM.Gauss.Grid.azuma_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.azuma_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.doob_L2_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.martingale_sq_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.stopped_martingale' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms appear for every public declaration.

## (c) Key lemmas used

* `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`,
  `HasSubgaussianMGF.neg` / `Kernel.HasSubgaussianMGF.neg`,
  `StronglyAdapted.neg`, `le_abs`, `measureReal_union_le` (T1).
* `Complex.norm_le_sqrt_two_mul_max`, `sq_lt_sq`-family avoided in favour of
  the sharper max-split, `Real.sq_sqrt`, `le_max_iff`, `measureReal_mono`
  (T2).
* `MeasureTheory.maximal_ineq`, `Finset.le_sup'_iff`,
  `pow_le_pow_iff_left₀`, `ENNReal.toReal_mono`/`toReal_mul`/`coe_toReal`,
  `setIntegral_nonneg`, `setIntegral_le_integral`,
  `Finset.measurable_range_sup''` (T3).
* `MeasureTheory.condExp_add`, `condExp_sub`, `condExp_of_stronglyMeasurable`,
  `condExp_mul_of_stronglyMeasurable_left`, `condExp_nonneg`,
  `integral_condExp`, `MemLp.integrable_mul` (`HolderConjugate 2 2` instance)
  — all used inside the shared private core lemma `condExp_sq_eq_add` (T3,
  T4).
* `MeasureTheory.Martingale.submartingale`, `Martingale.neg`,
  `Submartingale.stoppedProcess`, `stoppedProcess_comp`, `martingale_iff`,
  `WithTop.coe_min`, `WithTop.untopA` (`rfl` at a coercion) (T5).

## (d) Open issues

* No fresh from-scratch **nonzero** compiled satisfiability witness was
  added inside `GridAzuma.lean` for the `HasCondSubgaussianMGF`-based
  hypotheses of (T1)/(T2)/(T3) (only the trivial `Y ≡ 0`/`M ≡ 0` case is
  immediate by `@[simp]` Mathlib lemmas by inspection). I rely on the
  already-compiled nonzero instance of the identical typeclass shape
  (`StandardBorelSpace` + `IsProbabilityMeasure` + non-degenerate
  `HasCondSubgaussianMGF`) at
  `RBM1D/Gauss/PermutationFourierDoobAzumaScalar.lean:295-306`
  (`uniformPerm_prefixFourierDoobAzuma_two_witness`) as existing evidence
  that the hypothesis bundle is not vacuous. Flagging for the auditor to
  decide whether a bespoke witness inside this file is required before
  `audit-pass`.
* Per CLAUDE.md §3.5, this file is pure probability theory and makes no
  claim about the Brownian model or any `H_u = √u·X` adapter; it is a
  generic, RBM-independent lemma set as the ticket specifies.
* No paper-delta entries needed: this ticket cites only Mathlib statements,
  no paper formula numbers.
