Prover model: claude-sonnet-5

# T1489 — Grid stopping times specialised to the coordinate filtration

## (a) Math preflight (before any Lean)

Source cited by the ticket: `pilot-P4P5-paper.md` §4 (τ, σ are stopping times of the grid
path); required reading restricted by the ticket to `CLAUDE.md` §3, `RBM1D/Gauss/GridPath.lean`
(T1481, merged) and `RBM1D/Gauss/GridStop.lean` (T1483, merged). Both dependencies are
already-accepted results (present on `main`); no other file was read.

**Step 0 (read-only check).** `H_adapted` in `GridPath.lean` gives, for each fixed grid step
`k` and each pair of matrix indices `i j : d.Idx N`, `StronglyMeasurable[filt d k] (fun ω =>
H d s t K N k ω i j)`, i.e. only *entrywise* adaptedness. `Matrix (d.Idx N) (d.Idx N) ℂ` carries
the measurable-space instance `Matrix.instMeasurableSpace` (`Mathlib/Analysis/Matrix/
MeasurableSpace.lean`), definitionally the one on `d.Idx N → d.Idx N → ℂ`, and Mathlib's
`Matrix.measurable_iff : Measurable M ↔ ∀ i j, Measurable (M · i j)` is stated for an arbitrary
source `MeasurableSpace β` (no countability/finiteness hypothesis on the index types `m n`). Hence
entrywise measurability **does** assemble to the matrix; per the ticket's Step-0 branch this is
proved as the matrix-level lemma `H_measurable_filt` in the new file, using
`stronglyMeasurable_iff_measurable` to convert `H_adapted`'s strong-measurability statements to
plain measurability first. (Lean-technical note, not a math issue: applying `Matrix.measurable_iff`
or the generic `measurable_pi_iff` via `rw`/`.2` against a goal whose *source* instance is the
explicit non-default `filt d k` fails with a "synthesized instance not defeq" / rewrite-pattern
error, because the lemma's own `[MeasurableSpace β]` instance argument gets eagerly resolved by
typeclass search to the ambient/default instance on `Ωg d` rather than unified against `filt d k`.
The fix is to instantiate the lemma's instance argument *explicitly* with `filt d k` via
`@Matrix.measurable_iff (d.Idx N) (d.Idx N) ℂ _ (Ωg d) (filt d k) _`, bypassing search. Also
discovered in passing: as of the Mathlib version pinned here, `MeasureTheory.Adapted` itself was
redefined (2026-01-13) to require `Measurable[f i] (u i)` directly, not
`StronglyMeasurable[f i] (u i)` as `GridPath.lean`'s doc-comments describe (the old meaning is now
named `StronglyAdapted`); this only simplifies the proof here (no `stronglyMeasurable_iff_measurable`
wrapping needed after `H_measurable_filt`) and changes no statement's mathematical content.)

**(T1) `isStoppingTime_firstHit_grid`.** Statement to prove: for fixed `d s t K N`, any family
`F : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ` with `hF : ∀ j, Measurable (F j)`, the process
`J j ω := F j (H d s t K N j ω)` is `filt d`-adapted (via `H_measurable_filt` composed with
`hF j`, using `Measurable.comp` and `stronglyMeasurable_iff_measurable`), and then
`GridStop.isStoppingTime_firstHit` (T1483, generic, filtration-agnostic) is instantiated at
`ℱ := filt d`, `J`, `θ`, `K'`. Quantifier order matches the paper's use: `d s t K N` (fixed
parameters, including the size parameter `N`) are fixed first, then `F`/`hF` (the loop-observable
family) and finally the threshold `θ` and grid horizon `K'`; no `∀ᶠ N` is involved because this is
a pointwise (fixed-`N`) filtration fact, exactly as in the generic `GridStop.lean` lemmas it
specialises. Dependencies (`H_adapted`, `isStoppingTime_firstHit`) are both already-accepted
(merged) results; no new axioms are introduced. Hypothesis `hF` is non-vacuously satisfiable: the
intended application takes `F j = fun M => (a loop observable of M) - θ'`-type continuous
functions (e.g. a matrix entry, its real/imaginary part, or its modulus), all of which are
continuous, hence measurable — so the hypothesis is exactly as strong as needed for the real
application and not weaker (matches the acceptance criterion). Boundary case `K' = 0`: `firstHit`
is then the constant `0` function for every `ω` (Mathlib's `hittingBtwn` returns the right
endpoint when the trivial range `{0}` is not hit at index 0, and the right endpoint is `K' = 0`),
which is trivially a stopping time; no vacuity, just a degenerate special case already handled by
the generic lemma. Verdict: **PASS**.

**(T2) `lt_firstHit_grid_measurableSet`.** Same hypotheses as (T1); conclusion
`MeasurableSet[filt d j] {ω | j < firstHit J θ K' ω}` follows directly from
`GridStop.lt_firstHit_measurableSet` instantiated at `ℱ := filt d` with the same adaptedness
witness built for (T1). No new mathematical content beyond (T1)'s adaptedness assembly. Verdict:
**PASS**.

**(T3) minimum of two grid-observable hitting times.** For two families `F F'` (with `hF hF'`)
and thresholds `θ θ'` over the same horizon `K'`, `GridStop.isStoppingTime_min_firstHit` and
`GridStop.lt_min_firstHit_measurableSet` are instantiated at `ℱ := filt d` with the two
adaptedness witnesses (one per family, both built by the same construction as (T1)). Both `F` and
`F'` can simultaneously be arbitrary measurable families (e.g. two different loop observables at
different matrix entries/indices), so the two hypotheses `hF`, `hF'` are simultaneously
satisfiable by construction (they do not interact). Verdict: **PASS**.

All three targets: math preflight **PASS**. Proceeding to Lean.

## (b) Declarations, build, axioms

New file: `RBM1D/Gauss/GridStopFilt.lean` (namespace `RBM.Gauss.Grid`), importing only
`RBM1D.Gauss.GridPath` and `RBM1D.Gauss.GridStop`.

Declarations added:
- `H_measurable_filt (N k : ℕ) : Measurable[filt d k] (fun ω : Ωg d => H d s t K N k ω)`
  — the matrix-level assembly lemma flagged in the ticket's Step 0.
- `adapted_of_measurable_H {F : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ} (hF : ∀ j, Measurable (F j)) :
  Adapted (filt d) (fun j ω => F j (H d s t K N j ω))` — helper packaging `H_measurable_filt`
  with `hF` into full adaptedness of the grid-observable process.
- `isStoppingTime_firstHit_grid` (T1).
- `lt_firstHit_grid_measurableSet` (T2).
- `isStoppingTime_min_firstHit_grid` (T3, part 1).
- `lt_min_firstHit_grid_measurableSet` (T3, part 2).

Build:
```
lake build RBM1D.Gauss.GridStopFilt
```
Result: `Build completed successfully (3703 jobs).`

Axioms of the new public declarations (`#print axioms`, checked via a scratch file importing
`RBM1D.Gauss.GridStopFilt` and run with `lake env lean`, then removed):
```
'RBM.Gauss.Grid.H_measurable_filt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.adapted_of_measurable_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.isStoppingTime_firstHit_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.lt_firstHit_grid_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.isStoppingTime_min_firstHit_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.lt_min_firstHit_grid_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/custom axioms.

## (c) Key lemmas used

- `RBM.Gauss.Grid.H_adapted` (`GridPath.lean`, T1481): entrywise `StronglyMeasurable[filt d k]`
  of the grid path.
- `Matrix.measurable_iff` (`Mathlib/Analysis/Matrix/MeasurableSpace.lean`): assembling entrywise
  (relative) measurability into the matrix-level measurability statement, for an arbitrary source
  measurable space (instantiated explicitly at `filt d k`, see the Lean-technical note above).
- `stronglyMeasurable_iff_measurable`: converts between `StronglyMeasurable[·]` and `Measurable[·]`
  for the real-valued target (real numbers are second countable / pseudometrizable).
- `RBM.Gauss.Grid.isStoppingTime_firstHit`, `lt_firstHit_measurableSet`,
  `isStoppingTime_min_firstHit`, `lt_min_firstHit_measurableSet` (`GridStop.lean`, T1483):
  the generic, filtration-agnostic stopping-time facts, instantiated at `ℱ := filt d`.

## (d) Open issues

None. This ticket is pure API plumbing (per the ticket's own "Upstream/downstream" note):
specialising the already-accepted generic stopping-time lemmas of `GridStop.lean` to the
coordinate filtration of `GridPath.lean`, with the one genuinely new fact being the
matrix-vs-entrywise measurability assembly `H_measurable_filt`, which reuses an idiom already
present (for the unrelativised measurable space) in `GridPath.lean`. The auditor should confirm
that `hF`/`hF'` are exactly the hypotheses the eventual loop-observable application needs (a
continuous/measurable function of the matrix, not e.g. a stronger continuity or boundedness
requirement that would not hold for the intended thresholded loop observables), per the ticket's
acceptance criterion.
