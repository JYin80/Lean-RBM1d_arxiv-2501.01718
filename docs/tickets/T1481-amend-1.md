Ticket: T1481 (amend-1; supersedes T1481.md, which was withdrawn before any work started)
Group / type: pilot-TruePath (G1b) / prove — pilot P1
Role: prover
Release condition for the audit stage: prove report shows math preflight PASS; `lake build RBM1D.Gauss.GridPath` succeeds.
Math source and targets: the discrete grid path that replaces the Brownian flow (2.34) in §5.3; design in `docs/claude-team/pilot-P4P5-paper.md` §2. Parameters: `d : Gauss.Dims`, `s t : ℕ → ℝ`, `K : ℕ → ℕ`.
  (T1) `RBM.Gauss.Grid.Ωg d := ℕ → Ω d`, `RBM.Gauss.Grid.Pg d := Measure.infinitePi (fun _ : ℕ => Gauss.P d)`; instance `IsProbabilityMeasure (Pg d)`.
  (T2) `RBM.Gauss.Grid.step s t K N := (t N - s N) / K N` and `RBM.Gauss.Grid.time s t K N k := s N + k * step s t K N`; theorems `time_zero : time s t K N 0 = s N` and `time_last : K N ≠ 0 → time s t K N (K N) = t N`.
  (T3) `RBM.Gauss.Grid.H d s t K N k ω := (√(s N) : ℂ) • Xmat d N (ω 0) + (√(step s t K N) : ℂ) • ∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i)`; theorems `H_isHermitian` and `measurable_H` (entrywise, as for `Gauss.measurable_Hflow`).
  (T4) **Transfer lemma** `map_H_eq : 0 ≤ s N → s N ≤ t N → K N ≠ 0 → (Pg d).map (H d s t K N k) = (Gauss.P d).map (Gauss.Hflow d N (time s t K N k))` for every `k` (not only `k ≤ K N`: `time` is then simply larger). Proof route: coordinatewise, a sum of independent centred `gaussianReal` variables is `gaussianReal` with added variances (Mathlib `Probability/Distributions/Gaussian/Real.lean`, `Basic.lean`); variances add to `(s N + k·step)·gvar`, which is the law of `√u·X` at `u = time …`.
  (T5) `RBM.Gauss.Grid.filt d := MeasureTheory.Filtration.piLE` on `Ωg d` (coordinates `≤ k`); theorem `H_adapted : ∀ N, StronglyMeasurable[filt d k]` of each entry of `H d s t K N k`.
  (T6) **Increment independence and law** `indep_incr : ∀ k, Indep (MeasurableSpace.comap (fun ω => ω (k+1)) inferInstance) (filt d k) (Pg d)` and `map_incr : (Pg d).map (fun ω => ω (k+1)) = Gauss.P d`.
Step 0 (read-only checks the dispatcher could not verify): (a) `Measure.infinitePi` accepts an index type `ℕ` with the probability-measure instance needed (as used in `Gauss/Model.lean:223`); (b) `Filtration.piLE` exists at `Mathlib/Probability/Process/Filtration.lean:484`; (c) a sum/convolution lemma for `gaussianReal` exists. If (a) or (b) fails, stop and report `preflight-fail` with the exact missing declaration; if only (c) fails, prove the needed special case in this file.
Dependencies (must already be accepted): `RBM.Gauss.P`, `RBM.Gauss.Xmat`, `RBM.Gauss.Hflow`, `RBM.Gauss.gvar` (all in `Gauss/Model.lean`, committed).
Upstream / downstream: downstream T1482, T1483 (released after this is accepted); later A5 tickets. prover (not prover-hard): constructive, no analytic bound.
Sole writable files: `RBM1D/Gauss/GridPath.lean`        Must not touch: every other file (in particular `RBM1D.lean`, `RBM1D/Gauss/Model.lean`, anything `APrime*`).
Root import: none (the hub adds `import RBM1D.Gauss.GridPath` only under a later merge instruction).
Branch: t/T1481
Required reading (only these): `CLAUDE.md` §3; `RBM1D/Gauss/Model.lean` (lines 130–260, 363–425); `docs/claude-team/pilot-P4P5-paper.md` §2, §5.
Acceptance criteria: all of (T1)–(T6) with these exact names in namespace `RBM.Gauss.Grid`; no `sorry`/`admit`/`axiom`; `#print axioms RBM.Gauss.Grid.map_H_eq` ⊆ {propext, Classical.choice, Quot.sound}; auditor checks that (T4) is stated for the actual `Gauss.P d` / `Gauss.Hflow` (not an abstract measure), that `filt` is the coordinate filtration (not `⊤`), and that the hypotheses of (T4) are satisfiable (witness: `s = 0`, `t = 1/2`, `K = 1`).
