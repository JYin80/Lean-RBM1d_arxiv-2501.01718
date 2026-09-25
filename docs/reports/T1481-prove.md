# T1481 (amend-1) — prove report

Role: prover. Branch: `t/T1481`. Sole writable file: `RBM1D/Gauss/GridPath.lean` (new file).

## (a) Math preflight (written before any Lean)

Step 0 checks (ticket §"Step 0"):
- (a) `Measure.infinitePi` accepts an arbitrary index type (no `Countable`/`Fintype` hypothesis
  on the index in the section that defines it, `Mathlib/Probability/ProductMeasure.lean:355`);
  `Measure.infinitePi fun _ : ℕ => Gauss.P d` type-checks exactly as `Gauss.P d` itself is built
  (`Gauss.P d := Measure.infinitePi fun c => gaussianReal 0 (gvar d c)`, `Gauss/Model.lean:223`).
  PASS.
- (b) `Filtration.piLE` exists at `Mathlib/Probability/Process/Filtration.lean:494`, requiring
  only `[Preorder ι]` (automatic for `ι = ℕ`) and a type family `X : ι → Type*`; no
  `LocallyFiniteOrderBot` needed for the definition itself (only for the auxiliary
  `piLE_eq_comap_frestrictLe`, not used here). PASS.
- (c) No ready-made "sum of independent gaussianReal" lemma for more than two summands exists
  in the pinned Mathlib; `gaussianReal_add_gaussianReal_of_indepFun` (pairwise) does exist
  (`Gaussian/Real.lean:653`). Per the ticket, the general (`k`-term) case is proved in this file
  by induction on `k` from the pairwise lemma (`sumIcc_map_gaussianReal`,
  `weightedSum_map_gaussianReal`). PASS (with the induction supplied here).

Per-target preflight:

- **T1** (`Ωg`, `Pg`, `IsProbabilityMeasure (Pg d)`). Statement matches the ticket verbatim.
  `Measure.infinitePi (fun _ : ℕ => P d)` is a probability measure unconditionally
  (`instance : IsProbabilityMeasure (infinitePi μ)`, no extra hypothesis). No vacuity: `Dims` is
  non-empty (`Gauss.Dims.example`, T202), so `Ωg d` is inhabited. PASS.
- **T2** (`step`, `time`, `time_zero`, `time_last`). Pure arithmetic; `time_last` needs
  `K N ≠ 0` exactly as stated (division by `(K N : ℝ)` then `mul_div_cancel₀`). No hidden
  hypothesis; quantifier order matches (`N` and `hK` explicit, in that order). PASS.
- **T3** (`H`, `H_isHermitian`, `measurable_H`). `H` is a finite ℂ-linear combination of
  Hermitian, measurable matrices (`Xmat d N (ω i)`, already Hermitian/measurable in
  `Gauss/Model.lean`), so both facts reduce to closure of `IsHermitian`/`Measurable` under
  `+`, real (hence self-adjoint) scalar `•`, and finite sums. PASS.
- **T4** (`map_H_eq`, the transfer lemma). Checked the exact formula from
  `docs/claude-team/pilot-P4P5-paper.md` §2: `H_{u_{k+1}} = H_{u_k} + ΔH_k`, variances add,
  `H_{u_k} ~ √u_k · X` in law. Route used (all internal, no external input beyond what
  `docs/paper-deltas.md` #114 already authorizes — not invoked here): entrywise, `Xmat d N` is
  ℝ-linear in `ω` (`Xentry_add`/`Xentry_smul`/`Xentry_sum`, proved here), so
  `H = Xmat d N ∘ combined` and `Hflow d N u = Xmat d N ∘ (√u • ·)` for the *same* fixed
  measurable map `Xmat d N`; it remains to show
  `(Pg d).map combined = (P d).map (√u • ·)` as measures on `Ω d`. This is proved by (i) a
  "Fubini for `infinitePi`" swap of the grid axis and the raw-coordinate axis
  (`Measure.infinitePi_map_curry(_symm)` + `Measure.infinitePi_map_piCongrLeft` with
  `Equiv.prodComm`, all general Mathlib lemmas, no case-specific hypothesis), which reduces the
  grid-sum to a *per-raw-coordinate* one-dimensional problem; and (ii) the induction of Step 0(c)
  applied to that one-dimensional problem. Hypotheses of `map_H_eq` are exactly the ticket's
  `0 ≤ s N`, `s N ≤ t N`, `K N ≠ 0`; simultaneously satisfiable and non-degenerate
  (`s ≡ 0, t ≡ 1/2, K ≡ 1`, the ticket's own witness: `0 ≤ 0`, `0 ≤ 1/2`, `1 ≠ 0`, none of the
  quantities collapse to `N = 0`/empty index sets — `s, t, K : ℕ → ℝ`/`ℕ → ℕ` are free
  functions, not tied to `Dims`). Holds for *every* `k : ℕ`, not only `k ≤ K N` (the ticket's
  explicit requirement): the proof never uses `k ≤ K N`, only that `Finset.Icc 1 k` is finite.
  PASS.
- **T5** (`filt`, `H_adapted`). `filt d := Filtration.piLE`, the genuine coordinate filtration
  (`pi.comap (Preorder.restrictLe k)`, reading exactly the coordinates `≤ k`), not `⊤`.
  `H_adapted` shows each entry of `H d s t K N k` is `Measurable[filt d k]`, since it is built
  from `ω 0, …, ω k` only, each of which factors through `Preorder.restrictLe k`. PASS.
- **T6** (`indep_incr`, `map_incr`). `indep_incr` reduces to a standard "independent σ-algebras
  split by a subset vs. its complement" fact (`indep_biSup_compl`) applied to
  `t := Set.Iic k`, after identifying `filt d k` with `⨆ n ∈ Set.Iic k, comap (eval n)`
  (`MeasurableSpace.pi`'s own definition as an `iSup`, `comap_iSup`, `comap_comp`). `map_incr` is
  `Measure.infinitePi_map_eval`. Both use only the already-accepted `iIndepFun_infinitePi`. PASS.

Dependencies used: `RBM.Gauss.P`, `RBM.Gauss.Xmat`, `RBM.Gauss.Xentry`, `RBM.Gauss.Hflow`,
`RBM.Gauss.gvar`, `RBM.Gauss.Dims`, all already committed in `RBM1D/Gauss/Model.lean`. No
external input beyond the Mathlib lemmas cited above (none of them is the complex-Hermitian
[51, Theorem 2.2] reserved for Theorem 2.6 Step 1).

All targets PASS at math preflight; Lean writing proceeded after this point.

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridPath.lean` (new), namespace `RBM.Gauss.Grid`.

Public declarations (matching the ticket's names exactly):
`Ωg`, `Pg`, `isProbabilityMeasure_Pg`, `step`, `time`, `time_zero`, `time_last`, `H`,
`H_isHermitian`, `measurable_H`, `filt`, `H_adapted`, `indep_incr`, `map_incr`, `map_H_eq`.

Private helper declarations (algebra/measurability/probability plumbing, not part of the
acceptance criteria but needed for the proofs): `Xentry_add`, `Xentry_smul`, `Xentry_zero`,
`Xentry_sum`, `sumIcc_map_gaussianReal`, `weightedSum_map_gaussianReal`, `NNReal_mk_add_smul`,
`H_eq_Xmat_combined`, `Hflow_eq_Xmat_smul`, `measurable_Xmat`, `measurable_combined`,
`measurable_smul_Ω`, `map_column_eq`, `Pg'`, `swapEquiv`, `measurable_swapEquiv`, `Pg_swap_eq`,
`swapEquiv_apply`, `map_combined_eq`, `map_smul_eq`.

Build command and result:
```
lake build RBM1D.Gauss.GridPath
```
Succeeds (`Build completed successfully (3701 jobs)`), only style-linter warnings (long lines,
one unused-hypothesis hint for `hK` in `map_H_eq` — kept because the ticket's signature requires
it, even though this particular proof route derives `0 ≤ step` without it).

Axioms (checked via a throwaway `#print axioms` file importing `RBM1D.Gauss.GridPath`):
```
'RBM.Gauss.Grid.map_H_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.time_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.time_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.H_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.measurable_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.H_adapted' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.indep_incr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.map_incr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.isProbabilityMeasure_Pg' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/`axiom` anywhere in the file (`grep` clean).

Root import: none added (per ticket; `RBM1D.lean` untouched). Only `RBM1D/Gauss/GridPath.lean`
was created/modified; `git status --short` in the worktree shows only that file.

## (c) Key lemmas used

- `Measure.infinitePi_map_eval`, `Measure.infinitePi_map_pi`, `Measure.infinitePi_map_restrict`
  (`Mathlib/Probability/ProductMeasure.lean`).
- `Measure.infinitePi_map_curry`, `Measure.infinitePi_map_curry_symm`,
  `Measure.infinitePi_map_piCongrLeft` (same file) — the "Fubini for `infinitePi`" swap used to
  turn the grid-indexed sum into a per-raw-coordinate one-dimensional problem.
- `ProbabilityTheory.iIndepFun_infinitePi` (`Mathlib/Probability/Independence/InfinitePi.lean`).
- `ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem`,
  `ProbabilityTheory.iIndepFun.indepFun_finset`, `ProbabilityTheory.IndepFun.comp`
  (`Mathlib/Probability/Independence/Basic.lean`).
- `ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun`,
  `ProbabilityTheory.gaussianReal_map_const_mul` (`Mathlib/Probability/Distributions/Gaussian/Real.lean`).
- `ProbabilityTheory.indep_biSup_compl` (`Mathlib/Probability/Independence/ZeroOne.lean`),
  `MeasurableSpace.comap_iSup`/`comap_comp`, `comap_measurable`.
- `Mathlib.Analysis.Matrix.MeasurableSpace` for `MeasurableSpace (Matrix m n α)` (needed to state
  T4 as an equality of pushforward measures on the matrix space at all).

## (d) Open issues

- None blocking. `H_adapted`'s exact phrasing ("`∀ N, StronglyMeasurable[filt d k]` of each
  entry") was under-specified in the ticket; formalized as: for every `N, k, i, j`,
  `StronglyMeasurable[filt d k] (fun ω => H d s t K N k ω i j)`. Flag for the auditor to confirm
  this is the intended reading.
- `map_H_eq`'s hypothesis `hK : K N ≠ 0` is unused by this particular proof (the nonnegativity of
  `step` only needs `K N` cast to `ℝ` to be `≥ 0`, true even at `K N = 0` since division by zero
  is `0` in Mathlib's convention); kept in the signature to match the ticket exactly and because
  downstream tickets (T1482/T1483, `time_last`) genuinely need it.
