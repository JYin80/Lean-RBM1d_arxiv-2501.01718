Prover model: claude-sonnet-5

# T1494: Cauchy–Schwarz for the `E⊗E` kernel off the diagonal (M7a)

## (a) Math preflight (before any Lean)

Source: `docs/reports/T1488-prove.md` §3, target **M7a** (statement and proposed route), read
together with the required Step 0 definitions.

### Step 0 (read-only checks)

- `RBM.Gauss.emartEdge` (`RBM1D/Gauss/DischargeBDG.lean:323`): `E^{(M)}_{σ,a}(α,k)`, a single
  complex number built from `loopCut`.
- `RBM.Gauss.eeEdge` (`DischargeBDG.lean:328`):
  `eeEdge d N z M I I' k = ∑ i ∑ j, emartEdge d N z I M k i j * (starRingEnd ℂ) (emartEdge d N z I' M k i j)`.
  **The second argument's second factor is conjugated by `starRingEnd ℂ`.** This is exactly what
  makes `eeTens` a Gram-type kernel; the ticket's Step 0 obstacle ("if it does not conjugate,
  e.g. it uses `σ̄` instead of `conj`, report blocked") does **not** occur — the definition already
  conjugates via `starRingEnd ℂ`, not via a `σ̄`-only trick.
- `RBM.Gauss.eeTens` (`DischargeBDG.lean:334`): `eeTens d N z M I I' = ∑ k ∈ Finset.range I.length, eeEdge d N z M I I' k`,
  i.e. a finite sum of the `eeEdge` terms over the edges `k < I.length` (note: the range is
  `I.length`, the *first* argument's length — matters only when `I.length ≠ I'.length`, which
  does not arise below).
- `RBM.Gauss.eeEdge_self` (`DischargeBDG.lean:360`): `eeEdge d N z M I I k = ((∑ i ∑ j, ‖emartEdge d N z I M k i j‖^2 : ℝ) : ℂ)`,
  confirming the diagonal is a sum of squared norms (real, nonneg) — the expected form for (T2).
- `RBM.EEBridge.eeArg`/`eeArg_append` (`RBM1D/Hierarchy/EEBridgeArgCore.lean:51/55`):
  `eeArg d N z M σ c = eeTens d N z M (toIdx σ (leftArg c)) (toIdx σ (rightArg c))`, and
  `eeArg d N z M σ (Fin.append a a') = eeTens d N z M (toIdx σ a) (toIdx σ a')` (`eeArg_append`,
  by `rfl` plus `leftArg_append`/`rightArg_append`). The second factor of `eeArg`/`eeTens` here
  uses `toIdx σ a'` — the *same* `σ`, not `σ̄` — because the conjugation is already carried
  internally by `eeTens`/`eeEdge`'s `starRingEnd ℂ`. Consistent with T74's convention recorded
  in the module docstring ("read as the complex conjugate").
- `RBM.MomentDuhamel.EEpath` (`RBM1D/Gauss/MomentDuhamel.lean:404`):
  `EEpath X E n N u ω σ c = eeFun B E N u (X.H N u ω) σ c` (`rfl`), and
  `RBM.MomentDuhamel.eeFun` (`MomentDuhamelEEFunCore.lean:23`):
  `eeFun B E N u M σ c = EEBridge.eeArg B.toDims N (zt E u) M σ c` (`rfl`). So, for `n = 0`,
  `EEpath X E 0 N u ω σ (Fin.append a a') = eeTens B.toDims N (zt E u) (X.H N u ω) (toIdx σ a) (toIdx σ a')`
  for **every** `X : Sample B` — `EEpath`'s definition puts no hypothesis on `X` at all, so the
  statement is proved in exactly the generality the definition allows, as instructed.
- `RBM.Gauss.toIdx_length` (`DischargeBDG.lean:476`): `(toIdx σ a).length = n` for
  `a : LoopArg L n`. Applied to `a a' : LoopArg (B.L N) (0+2)`, both `toIdx σ a` and
  `toIdx σ a'` have length `0+2`, so `I.length = I'.length` holds automatically for the two
  loops built from `Fin.append a a'`/`Fin.append a a`/`Fin.append a' a'` — the hypothesis needed
  by the Cauchy–Schwarz route below is available for free at this instantiation, not an added
  hypothesis on the target.

**Verdict of Step 0: no obstacle found.** `eeTens` genuinely conjugates the second argument via
`starRingEnd ℂ` (not via `σ̄`), so it is a Gram kernel and M7a's route is not blocked.

### Preflight per target

**(T1) `RBM.Gauss.norm_EEpath_offDiag_sq_le`.**
- Statement vs paper/report: exactly the statement of M7a (T1) in `T1488-prove.md`, with the
  same names `a a' : LoopArg (B.L N) (0+2)`, `σ : Fin (0+2) → Bool`, no free hypothesis.
- Quantifier order: `X`, `E`, `N`, `u`, `ω`, `σ`, `a`, `a'` all universally quantified with no
  constraint among them (`EEpath` is defined for all reals `u`, all `ω`, unconditionally).
- Dependencies: only already-accepted, committed declarations —
  `RBM.MomentDuhamel.EEpath`/`eeFun` (`rfl` unfolding), `RBM.EEBridge.eeArg_append`,
  `RBM.Gauss.eeTens`/`eeEdge`/`emartEdge`/`toIdx`/`toIdx_length` — all already in the repo
  before this ticket (T74, T127, T135, T190 lineage per `T1488-prove.md`).
- Boundary cases: `N = 0` is not excluded by the statement, but nothing in the proof needs
  `N ≠ 0`, `L ≠ 0` etc. beyond what `d.Idx N` (a `Fintype`) already requires structurally;
  no witness/satisfiability issue arises because **no new hypothesis is added** — the statement
  is unconditional in `(X, E, N, u, ω, σ, a, a')`, so there is nothing to check for simultaneous
  satisfiability (an unconditional universally-quantified statement is trivially "satisfiable":
  it just has to hold at every instantiation, which is what the proof establishes).
- Route: `EEpath = eeTens` at `(toIdx σ a, toIdx σ a')` (Step 0 above) reduces (T1) to Cauchy–
  Schwarz for `eeTens`, i.e. to the elementary finite Cauchy–Schwarz inequality applied to the
  triple sum defining `eeTens`, using `I.length = I'.length` from `toIdx_length` (available for
  free, see Step 0).
- Verdict: **PASS**. Provable with no added hypothesis, matching the ticket's instruction "no
  positive-semidefiniteness hypothesis is needed."

**(T2) `RBM.Gauss.eeTens_self_nonneg`.**
- Statement vs report: "`eeTens I I` is real and nonnegative." Formalized as
  `∃ r : ℝ, 0 ≤ r ∧ eeTens d N z M I I = (r : ℂ)`, for arbitrary `d N z M I` — no hypothesis.
- Route: `eeEdge_self` (already committed) gives the diagonal of each edge as a real, nonneg
  sum of squared norms; summing over `k` preserves this.
- Verdict: **PASS**, unconditional, no added hypothesis.

Both targets: **no new hypothesis, no vacuity, no witness needed** (the statements are
unconditional). The auditor's checklist item "no hypothesis was added" is satisfied by
inspection of the two signatures above.

## (b) Declarations added, build, axioms

File: `RBM1D/Gauss/EEOffDiag.lean` (the ticket's sole writable file).

Declarations (all in namespace `RBM.Gauss` except where noted):
- `finset_inner_cauchy_schwarz {ι : Type*} (s : Finset ι) (F G : ι → ℂ) : ‖∑ i ∈ s, F i * (starRingEnd ℂ) (G i)‖ ^ 2 ≤ (∑ i ∈ s, ‖F i‖ ^ 2) * (∑ i ∈ s, ‖G i‖ ^ 2)` —
  the elementary finite complex Cauchy–Schwarz inequality, proved from the triangle inequality
  (`norm_sum_le`) and the real Cauchy–Schwarz inequality for finsets
  (`Finset.sum_mul_sq_le_sq_mul_sq`), with no inner-product-space machinery.
- `eeTens_eq_sum_flat (d : Dims) (N : ℕ) (z : ℂ) (M) (I I' : LoopIdx (ZMod (d.L N))) : eeTens d N z M I I' = ∑ p ∈ (Finset.range I.length) ×ˢ (Finset.univ ×ˢ Finset.univ), emartEdge d N z I M p.1 p.2.1 p.2.2 * (starRingEnd ℂ) (emartEdge d N z I' M p.1 p.2.1 p.2.2)` —
  flattens the triple sum into one `Finset` sum, via `Finset.sum_product'` (twice).
- `eeTens_self_nonneg (d N z M) (I) : ∃ r : ℝ, 0 ≤ r ∧ eeTens d N z M I I = (r : ℂ)` — (T2).
- `norm_eeTens_sq_le (d N z M) (I I' : LoopIdx (ZMod (d.L N))) (hlen : I.length = I'.length) : ‖eeTens d N z M I I'‖ ^ 2 ≤ ‖eeTens d N z M I I‖ * ‖eeTens d N z M I' I'‖` —
  Cauchy–Schwarz for `eeTens`.
- `norm_EEpath_offDiag_sq_le {Ω} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) (σ : Fin (0 + 2) → Bool) (a a' : LoopArg (B.L N) (0 + 2)) : ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a')‖ ^ 2 ≤ ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a)‖ * ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a' a')‖` —
  (T1), the ticket's named target.

Build:
- `lake build RBM1D.Gauss.EEOffDiag` — succeeded (`✔ [3729/3729] Built RBM1D.Gauss.EEOffDiag`),
  no `sorry`/`admit`/`axiom`, no warnings from this file (one `show`→`change` lint warning was
  fixed during development).

Axioms printed (`lake env lean` on a scratch file importing `RBM1D.Gauss.EEOffDiag`):
```
'RBM.Gauss.finset_inner_cauchy_schwarz' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.eeTens_eq_sum_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.eeTens_self_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_eeTens_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_EEpath_offDiag_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms.

Commit: branch `t/T1494`, commit `75b55341eac5a6a4ec2586c47a05f7274651302f`, sole file
`RBM1D/Gauss/EEOffDiag.lean` (163 insertions, new file).

## (c) Key existing lemmas used

`RBM.Gauss.eeTens`, `eeEdge`, `emartEdge`, `eeEdge_self` (`DischargeBDG.lean`);
`RBM.EEBridge.eeArg`, `eeArg_append`, `leftArg_append`, `rightArg_append`
(`EEBridgeArgCore.lean`); `RBM.Gauss.toIdx`, `toIdx_length` (`DischargeBDG.lean`);
`RBM.MomentDuhamel.EEpath`, `EEpath_eq_eeField`, `eeFun` (`MomentDuhamel.lean`,
`MomentDuhamelEEFunCore.lean`); `RBM.Gauss.mul_conj_eq` (`MomentGronwall.lean`);
Mathlib: `norm_sum_le`, `Finset.sum_mul_sq_le_sq_mul_sq`, `Finset.sum_product'`,
`Complex.norm_conj`, `Complex.norm_real`, `Complex.ofReal_sum`.

## (d) Open issues

- None for M7a itself. M7b (the actual displaced-argument bound with the loss factor
  `exp(√(2C)(log W)^{3/4})`) is a separate, larger target per `T1488-prove.md` and is not part
  of this ticket.
- The report's Step 0 finding that `eeTens`'s conjugation is via `starRingEnd ℂ` (not `σ̄`)
  should be read together with the `eeArg`/`eeArg_append` docstring's remark that the *second
  loop's* charge vector is "read as the complex conjugate" (T74's convention) — these are two
  different, compatible mechanisms (one at the tensor level, one at the loop-charge level), and
  no inconsistency was found between them for M7a's purposes.
