Auditor model: claude-opus-5-5[1m]

# T1494 audit: Cauchy–Schwarz for the `E⊗E` kernel off the diagonal (M7a)

Branch `t/T1494` @ `75b5534` (base `5ef3f4a`). Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1494-audit`
(detached at `75b5534`, since `t/T1494` is already checked out in the prover worktree).
Diff vs main: one new file, `RBM1D/Gauss/EEOffDiag.lean` (+163). No other file touched.

## Verdict

| Target | Verdict |
|---|---|
| (T1) `RBM.Gauss.norm_EEpath_offDiag_sq_le` | **PASS** |
| (T2) `RBM.Gauss.eeTens_self_nonneg` | **PASS** |

Ticket verdict: **PASS**.

## 1. Math preflight

`docs/reports/T1494-prove.md` §(a) contains the Step 0 definition checks and a per-target preflight PASS
for (T1) and (T2). It comes before the Lean section (b).

## 2. Statement vs target

- Source: `docs/reports/T1488-prove.md` §3, M7a (lines 231–236). T1488 is an internal inventory item.
  M7a is a hypothesis-free Cauchy–Schwarz sub-lemma. It is not a paper formula, and no paper formula
  number is at stake.
- (T1) compiled signature (`#check`):
  `∀ {Ω} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) (σ : Fin (0+2) → Bool) (a a' : LoopArg (B.L N) (0+2)),
   ‖EEpath X E 0 N u ω σ (Fin.append a a')‖ ^ 2 ≤ ‖EEpath X E 0 N u ω σ (Fin.append a a)‖ * ‖EEpath X E 0 N u ω σ (Fin.append a' a')‖`.
  This matches the ticket/T1488 display character for character. It uses the repo's actual
  `RBM.MomentDuhamel.EEpath` (`Gauss/MomentDuhamel.lean:404`), which has type
  `Fin (n+2) → Bool` → `LoopArg (B.L N) ((n+2)+(n+2))` → ℂ. At `n = 0`, `Fin.append a a'` has the right type.
  `X : Sample B` is arbitrary, so this is the full generality the definition allows, as the ticket asks.
  No hypothesis was added.
- (T2) compiled signature: `∀ d N z M (I : LoopIdx (ZMod (d.L N))), ∃ r : ℝ, 0 ≤ r ∧ eeTens d N z M I I = ↑r`.
  This is a faithful formalization of "eeTens I I is real and nonnegative". It holds for arbitrary `d, N, z, M, I`.
- Helper `norm_eeTens_sq_le` carries `hlen : I.length = I'.length`. This is a hypothesis of a helper
  lemma, not of the target. In (T1) it is discharged by `toIdx_length` (both lengths are `0+2`). It is
  also necessary: `eeTens` sums over `range I.length`.
- Step 0 check (ticket): `eeEdge` (`DischargeBDG.lean:328`) is
  `∑ i ∑ j, emartEdge … I … k i j * starRingEnd ℂ (emartEdge … I' … k i j)`. The second argument is
  complex-conjugated, so `eeTens` is a genuine Gram kernel and there is no blocked condition.
  Remark, not a defect of this ticket: the `eeEdge` docstring quotes the paper's
  `E_{σ,a}·E_{σ̄,a'}`. The accepted definition (T74 lineage) implements this as `conj`. That
  definitional convention predates T1494 and is outside its scope.

## 3. Vacuity / hidden hypotheses / cycles

- Neither target has any hypothesis, so there is no satisfiability question and no `N = 0`, empty-index
  or collapsed-window loophole. Both are universally quantified identities/inequalities over all inputs.
- No structure fields were introduced. `Sample B` is the existing structure and is used only through `X.H`.
- No circularity: the new file imports only `RBM1D.Gauss.MomentDuhamel`. Nothing imports the new file.
- Degenerate inputs (e.g. `N` with empty `d.Idx N`) make both sides 0. The statement is still true
  and non-vacuous for nondegenerate inputs.

## 4. Dependencies

The following committed, accepted declarations are used: `EEpath`/`eeFun` (by defeq, via `change`),
`EEBridge.eeArg_append`, `eeTens`, `eeEdge`, `emartEdge`, `toIdx_length`, and `mul_conj_eq`. The
Mathlib lemmas used are `norm_sum_le`, `Finset.sum_mul_sq_le_sq_mul_sq`, `Finset.sum_product'`,
`Complex.norm_conj`, `Complex.norm_real` and `Complex.ofReal_sum`. The dependency files
(`MomentDuhamel.lean`, `DischargeBDG.lean`, `EEBridgeArgCore.lean`, `MomentDuhamelEEFunCore.lean`,
`MomentGronwall.lean`) are unchanged between the branch base `5ef3f4a` and current main `a3e7e36`.
None of the five new declaration names appears anywhere else in the repo.

## 5. Build and axioms (audit worktree)

- `lake build RBM1D.Gauss.EEOffDiag`: `✔ [3729/3729] Built RBM1D.Gauss.EEOffDiag`, Build completed
  successfully. No warnings or errors from `EEOffDiag.lean`; the only warnings are pre-existing lint
  warnings in other files.
- `lake build RBM1D`: Build completed successfully (9639 jobs). The root import is added at merge,
  per the ticket.
- `#print axioms` for all five declarations (`norm_EEpath_offDiag_sq_le`, `eeTens_self_nonneg`,
  `norm_eeTens_sq_le`, `finset_inner_cauchy_schwarz`, `eeTens_eq_sum_flat`) returns only
  `[propext, Classical.choice, Quot.sound]`.
- `grep` finds no `sorry`/`admit`/`axiom` in the file. No frozen signature is touched; the change is
  one new file only.

## Paper-deltas

None required. The target is an internal Lean lemma with no paper-statement difference.
