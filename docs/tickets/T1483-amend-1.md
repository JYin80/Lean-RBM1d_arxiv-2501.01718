Ticket: T1483 (amend-1; supersedes T1483.md, withdrawn before any work started)
Group / type: pilot-TruePath (G1b) / prove — pilot P3
Role: prover
Release condition for the audit stage: prove report shows math preflight PASS; `lake build RBM1D.Gauss.GridStop` succeeds.
Math source and targets: the grid stopping times τ (threshold (5.43), with the N^δ correction of `docs/claude-team/pilot-P4P5-paper.md` §6) and σ (first failure of an input bound), `pilot-P4P5-paper.md` §4. Generic in the filtration; specialised to `filt d` of T1481.
  (T1) `RBM.Gauss.Grid.firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) : Ω' → ℕ := fun ω => MeasureTheory.hitting J (Set.Ici θ) 0 K ω` (first `j ≤ K` with `θ ≤ J j ω`, else `K`), for an arbitrary measurable space `Ω'` and filtration `ℱ : Filtration ℕ _`.
  (T2) `isStoppingTime_firstHit`: `Adapted ℱ J → IsStoppingTime ℱ (fun ω => (firstHit J θ K ω : ℕ))`; and `firstHit_le : firstHit J θ K ω ≤ K`.
  (T3) `lt_firstHit_measurableSet`: `MeasurableSet[ℱ j] {ω | j < firstHit J θ K ω}` for every `j`; and `lt_firstHit_imp : j < firstHit J θ K ω → J j ω < θ` (strictly below threshold before the stop).
  (T4) `isStoppingTime_min` for `τ ⊓ σ` (or cite Mathlib's `IsStoppingTime.min`) and the same two facts for `τ ⊓ σ`.
  (T5) `sum_stopped`: `∑ j ∈ Finset.range (min k (τ ω)), Y (j+1) ω = ∑ j ∈ Finset.range k, ({ω | j < τ ω}.indicator (Y (j+1))) ω` (per-ω identity used to put stopped sums in Azuma form).
Step 0 (read-only checks): exact signature of `MeasureTheory.hitting` and `hitting_isStoppingTime` in `Mathlib/Probability/Process/HittingTime.lean` (T1/T2 adapt to it; if the Mathlib convention for "never hit" differs from "= K", follow Mathlib and document it).
Dependencies (must already be accepted): none for (T1)–(T5) in the generic form; the specialisation line `firstHit` over `filt d` uses T1481.
Upstream / downstream: consumed by the A5 Step 2 assembly. prover: Mathlib API.
Sole writable files: `RBM1D/Gauss/GridStop.lean`        Must not touch: every other file.
Root import: none.
Branch: t/T1483
Required reading (only these): `CLAUDE.md` §3; `Mathlib/Probability/Process/HittingTime.lean`; `Mathlib/Probability/Process/Stopping.lean` (statements only); `RBM1D/Gauss/GridPath.lean`; `docs/claude-team/pilot-P4P5-paper.md` §4, §6.
Acceptance criteria: (T1)–(T5) with these names in `RBM.Gauss.Grid`; no `sorry`/`admit`/`axiom`; auditor checks that the filtration in (T2)/(T3) is the given `ℱ` (not `⊤`), that (T3)'s strict inequality really follows (the threshold set is `Ici θ`), and that (T5) is a genuine identity, not a definitional tautology hiding the indicator.
