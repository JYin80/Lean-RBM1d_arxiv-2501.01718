# T1483 (amend-1) — grid stopping times τ, σ (pilot P3)

Sole writable file: `RBM1D/Gauss/GridStop.lean`. Branch `t/T1483`, worktree
`../RBM1D-wt/T1483`.

## Step 0 (read-only checks)

`Mathlib/Probability/Process/HittingTime.lean` (pinned Mathlib, `lake-manifest.json`)
does **not** contain `MeasureTheory.hitting` or `hitting_isStoppingTime` as named in
the ticket text. The current API (post-rename) is:

- `MeasureTheory.hittingBtwn (u : ι → Ω → β) (s : Set β) (n m : ι) : Ω → ι`,
  `hittingBtwn u s n m ω = sInf (Set.Icc n m ∩ {i | u i ω ∈ s})` if that intersection
  is nonempty, **else `m`** (line 56-59, `HittingTime.lean`). This is exactly the
  "first `j ≤ K` with `θ ≤ J j ω`, else `K`" convention the ticket asks for with
  `n := 0`, `m := K`, so `firstHit` is defined as `hittingBtwn J (Set.Ici θ) 0 K`.
- `MeasureTheory.hittingAfter` is the unbounded variant (`Ω → WithTop ι`, "else `⊤`"),
  not used here since the ticket wants a bounded grid time (`else K`).
- The stopping-time lemma is `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`
  (line 399-410): for `[ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  [Countable ι]`, `Adapted f u → MeasurableSet s → IsStoppingTime f (fun ω ↦
  (hittingBtwn u s n n' ω : ι))`. All three instances hold for `ι = ℕ`
  (`ConditionallyCompleteLinearOrder ℕ`, `WellFoundedLT ℕ`, `Countable ℕ` are
  registered instances). `IsStoppingTime` itself is `∀ i, MeasurableSet[f i]
  {ω | τ ω ≤ i}` for `τ : Ω → WithTop ι` (`Stopping.lean:76`), so the ticket's
  cast `(firstHit J θ K ω : ℕ)` inside a term of expected type `Ω' → WithTop ℕ` is
  exactly the ℕ → WithTop ℕ coercion used verbatim by Mathlib's own theorem
  statement — same idiom, not a typo.
- `MeasureTheory.notMem_of_lt_hittingBtwn {m k} (hk₁ : k < hittingBtwn u s n m ω)
  (hk₂ : n ≤ k) : u k ω ∉ s` (line 121) gives (T3)'s `lt_firstHit_imp` directly with
  `n = 0`, `hk₂ = Nat.zero_le j`.
- `MeasureTheory.hittingBtwn_le (ω) : hittingBtwn u s n m ω ≤ m` gives `firstHit_le`.
- `IsStoppingTime.min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
  IsStoppingTime f (fun ω => min (τ ω) (π ω))` (`Stopping.lean:359-364`) is the cited
  Mathlib lemma for (T4); combined with `WithTop.coe_min` (`↑(min a b) = min ↑a ↑b`,
  used the same way elsewhere in Mathlib, e.g. `PadicNumbers.lean:1173`) it gives the
  stopping-time property of the ℕ-valued minimum of two `firstHit`s.
- Required reading `RBM1D/Gauss/GridPath.lean` (listed for the `filt d`
  specialisation from T1481) **does not exist yet** in this worktree, in the main
  worktree, or anywhere in the repo outside archives — T1481 is claimed but has not
  produced it. The ticket's acceptance criteria (T1)-(T5) are stated in the
  fully generic filtration form and do **not** mention `filt d`; the dependency
  line explicitly says "none for (T1)-(T5) in the generic form". I therefore do
  the generic work only and record the missing specialisation as an open issue,
  per the ticket's own dependency statement — no signature or scope is widened to
  compensate.

## Math preflight (per target)

All targets are stated for an arbitrary measurable space `Ω'` (`m : MeasurableSpace
Ω'`) and an arbitrary filtration `ℱ : Filtration ℕ m`; no vacuity risk from a
degenerate `Ω'` because every target is a universally quantified implication /
identity that holds for every `Ω'`, including nontrivial ones (e.g. `Ω' = ℝ` with
`J j ω = ω`, checked below as the satisfiability witness).

**(T1) `firstHit`.** Definition only: `firstHit J θ K ω := hittingBtwn J (Set.Ici θ)
0 K ω`. Matches the ticket's description "first `j ≤ K` with `θ ≤ J j ω`, else `K`"
exactly, given the Step-0 finding above. PASS.

**(T2) `isStoppingTime_firstHit`, `firstHit_le`.**
- `isStoppingTime_firstHit`: direct specialisation of
  `Adapted.isStoppingTime_hittingBtwn` at `n = 0`, `n' = K`, `s = Set.Ici θ`
  (measurable: `measurableSet_Ici`, standard order-topology fact for `ℝ`). Hypothesis
  order matches the paper's usage (fix `ℱ`, `J`, `θ`, `K`, then require `Adapted ℱ
  J`). No hidden hypothesis beyond `Adapted ℱ J`, which is exactly what the ticket
  states. PASS.
- `firstHit_le`: direct specialisation of `hittingBtwn_le`. PASS.

**(T3) `lt_firstHit_measurableSet`, `lt_firstHit_imp`.**
- `lt_firstHit_measurableSet`: from `hτ.measurableSet_le j : MeasurableSet[ℱ j]
  {ω | (↑(firstHit J θ K ω) : WithTop ℕ) ≤ ↑j}`; converting the coercion inequality
  to the ℕ inequality (`WithTop.coe_le_coe`) and taking the complement (linear order
  on ℕ: `j < firstHit … ↔ ¬(firstHit … ≤ j)`) gives the stated set, still measurable
  since complementation preserves measurability in any `MeasurableSpace`. Needs
  `Adapted ℱ J` (to invoke (T2)); this is the same hypothesis, not an added one.
  PASS.
- `lt_firstHit_imp`: direct instance of `notMem_of_lt_hittingBtwn` with `s = Set.Ici
  θ`, unfolding `∉ Set.Ici θ ↔ < θ` on a linear order. No hypothesis at all (holds
  for every `J`, `θ`, `K`, `j`, `ω` — a purely order-theoretic fact about
  `hittingBtwn`, doesn't even need adaptedness). Boundary case `j = K`: vacuous
  premise `K < firstHit … ≤ K` is impossible, so nothing to check. PASS.

**(T4) `IsStoppingTime.min` for τ ⊓ σ, plus the two (T3) facts.** The ticket's τ
(threshold crossing of `J*`) and σ (first failure of an input bound) are both of
`firstHit` shape (a bounded grid hitting time of some real-valued adapted process
against a real threshold), so I instantiate the generic combination with two
independent `firstHit`s `firstHit J θ K` and `firstHit J' θ' K` on the same grid
horizon `K` (matching the paper's τ, σ living on the same grid). Hypotheses:
`Adapted ℱ J`, `Adapted ℱ J'` (both needed, both already required individually by
(T2), so no new hypothesis class). Combine via `IsStoppingTime.min` +
`WithTop.coe_min` for the stopping-time fact; complement trick as in (T3) for the
measurable-set fact; and `lt_min_iff` + two `lt_firstHit_imp` for the "still below
both thresholds" fact. No quantifier-order or vacuity issue: same witness as (T3)
plus a second real-valued process `J'` and threshold `θ'` (can even take `J' = J`,
`θ' = θ` as a degenerate but non-vacuous case, or genuinely different — checked in
the satisfiability witness below). PASS.

**(T5) `sum_stopped`.** Pure finite-combinatorics identity, no probability, no
measurability, no stopping-time hypothesis: for any `M` an `AddCommMonoid`, any `Y :
ℕ → Ω' → M`, any `τ : Ω' → ℕ`, any `k : ℕ`, any `ω : Ω'`,
`∑_{j<min k (τ ω)} Y(j+1) ω = ∑_{j<k} indicator{j<τ ω}(Y(j+1)) ω`. Proof: `(range
k).filter (· < τ ω) = range (min k (τ ω))` (via `lt_min_iff`), then
`Finset.sum_filter` unfolds the RHS indicator sum to exactly the filtered sum. This
is a genuine identity (not defeq): the LHS's index set depends on `min k (τ ω)`
computed once, while the RHS is literally a sum over the fixed set `range k` of an
`if`-expression per term; they are propositionally, not definitionally, equal (the
two `Finset`s `range (min k (τ ω))` and `(range k).filter (· < τ ω)` are equal as
sets but not syntactically/definitionally the same term), matching the audit
requirement that this not be a "definitional tautology hiding the indicator".
Boundary cases: `k = 0` (both sides `0`, since `range 0 = ∅` and `min 0 _ = 0`);
`τ ω = 0` (LHS `∑_{j<0} = 0`, RHS all indicators `0` since `¬(j<0)` for all `j : ℕ`);
`τ ω ≥ k` (indicator is `1` on the whole range, LHS/RHS both `∑_{j<k}`). PASS.

## Simultaneous satisfiability witness

`Ω' := ℝ` (nontrivial, uncountable), `m := Real.measurableSpace` (Borel), `ℱ :=`
the constant filtration `fun _ => m` (adapted-to-everything, i.e. `⊤`-filtration
restricted; concretely `Filtration.mk (fun _ => m) (fun _ _ => le_refl m)` — every
process is `Adapted` to it), `J := fun j ω => ω` (adapted, since `ω ↦ ω` is
measurable w.r.t. any `m`), `J' := fun j ω => -ω`, `θ := (1:ℝ)`, `θ' := (1:ℝ)`,
`K := 3` (a genuinely bounded, non-empty, non-degenerate grid; `K = 0` is not used
as the witness). This is not an "astronomically large" or `N = 0`/empty-index-set
witness: `K = 3` gives four grid points `{0,1,2,3}`, `firstHit J 1 3` is `0` for
`ω ≥ 1`, `3` for `ω < 1` (never hits), and similarly for `J'`; `min` of the two
`firstHit`s and the (T3)/(T4) strict-inequality facts are all non-vacuously
exercised (e.g. `ω = 0`: `firstHit J 1 3 ω = 3`, `firstHit J' 1 3 ω = 3` since
`-0 = 0 < 1`, and for `j = 0,1,2` the "still below threshold" conclusion `J j ω < θ`
holds with room to spare, not merely because `θ` is huge). All five targets'
hypotheses (`Adapted ℱ J`, `Adapted ℱ J'`) are satisfied together, non-vacuously.

**Verdict for all of (T1)-(T5): PASS.** Proceeding to Lean.

## Lean

File: `RBM1D/Gauss/GridStop.lean` (namespace `RBM.Gauss.Grid`). Declarations added:

- `firstHit` (T1)
- `isStoppingTime_firstHit`, `firstHit_le` (T2)
- `lt_firstHit_measurableSet`, `lt_firstHit_imp` (T3)
- `isStoppingTime_min_firstHit`, `lt_min_firstHit_measurableSet`,
  `lt_min_firstHit_imp` (T4, generic form: two independent `firstHit`s on the same
  grid horizon `K`)
- `sum_stopped` (T5)

Build: `lake build RBM1D.Gauss.GridStop` — `✔ Built RBM1D.Gauss.GridStop`, full
target set (2987 jobs) succeeded, no errors, no warnings after the final revision
(one earlier `Preorder ℕ` instance-diamond issue in the `IsStoppingTime.min`
application was worked around by proving `isStoppingTime_min_firstHit` directly
from `IsStoppingTime.measurableSet_le` + `Set.union` instead of citing
`IsStoppingTime.min` verbatim — see "Lean" notes below).

Axioms (`#print axioms` on each new public declaration, all clean —
`propext, Classical.choice, Quot.sound` only):
```
'RBM.Gauss.Grid.firstHit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.isStoppingTime_firstHit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.firstHit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.lt_firstHit_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.lt_firstHit_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.isStoppingTime_min_firstHit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.lt_min_firstHit_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.lt_min_firstHit_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.sum_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`, `admit`, or declared `axiom` anywhere in the file (checked by grep).

### Key lemmas used

- `MeasureTheory.hittingBtwn`, `hittingBtwn_le`, `notMem_of_lt_hittingBtwn`
  (`Mathlib/Probability/Process/HittingTime.lean`).
- `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`
  (`HittingTime.lean:399-410`, the discrete-stopping-time construction).
- `MeasureTheory.IsStoppingTime.measurableSet_le`, `.compl`, `.union`
  (`Stopping.lean:88`, base `MeasurableSet` API).
- `min_le_iff`, `lt_min_iff`, `not_le` (order lemmas, generic linear order).
- `Finset.mem_filter`, `Finset.mem_range`, `Finset.sum_filter`,
  `Finset.sum_congr` (T5's combinatorial identity).

A note on (T4, part 1): the ticket allows citing Mathlib's `IsStoppingTime.min`
verbatim ("or cite Mathlib's `IsStoppingTime.min`"). I attempted this first; it
type-checks the underlying mathematical fact but the tactic proof hit a genuine
Mathlib-internal `Preorder ℕ` instance-diamond (`Nat.instPreorder` vs
`instDistribLatticeOfLinearOrder.toSemilatticeInf.toPreorder`, both provably equal
orders but not syntactically unifying inside `rw`/`simpa [WithTop.coe_min]`).
Rather than force the citation through with a fragile workaround, I proved
`isStoppingTime_min_firstHit` directly from the definition of `IsStoppingTime`
(`∀ i, MeasurableSet[f i] {ω | τ ω ≤ i}`) using `min_le_iff` to split into a union
of the two individual `measurableSet_le` facts and `convert … using 2` to close the
remaining set-equality goal — mathematically this *is* the proof of
`IsStoppingTime.min` inlined (same `min_le_iff` + `Set.ofPred_or` argument as
`Stopping.lean:358-363`), just without going through the polymorphic `[LinearOrder
ι]` lemma that triggered the diamond. No hypothesis was added or weakened to work
around this; it is purely a proof-engineering choice, noted here for the auditor.

### Open issues

- `RBM1D/Gauss/GridPath.lean` (the `filt d` specialisation from T1481) does not
  exist yet; the `filt d` line mentioned in the ticket's math-source paragraph is
  therefore not instantiated. Per the ticket's own dependency statement this is
  fine for (T1)-(T5) as accepted here; a follow-up ticket should add the
  `Gauss.sample d`/`filt d` specialisation once T1481 lands.
- (T4) is formalised with two `firstHit`-shaped stopping times sharing one grid
  horizon `K`, which is the natural reading of "τ (threshold crossing) and σ (first
  failure of an input bound)" from `pilot-P4P5-paper.md` §4 (both are grid hitting
  times against a real threshold). If a future ticket needs σ to have a different
  underlying shape (e.g. not expressible as a single real threshold on a single
  real process), `isStoppingTime_min_firstHit` should be read as an illustrative
  corollary of the fully generic `IsStoppingTime.min` fact, which is available
  directly from Mathlib without any of this file's help.
