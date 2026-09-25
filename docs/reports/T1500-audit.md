Auditor model: claude-opus-5-5[1m]

# T1500 audit: quantitative max-norm bound for the backward kernel `Uker L ξ t u`

Branch `t/T1500` @ `ef796d4`, audited in a detached worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1500-audit` (the branch itself is checked out in the prover worktree). Diff vs `main`: one new file, `RBM1D/Hierarchy/UkerBackBound.lean` (+156). No other file touched, so no frozen signature changed.

## Overall verdict: PASS (T1, T2, T3 all PASS)

## 1. Math preflight
`docs/reports/T1500-prove.md` has a "Math preflight (before any Lean)" section giving PASS for T1/T2/T3 before the Lean section. It includes a satisfiability witness, boundary cases (`u = t`, `u = 0`, `ξ = 0`, `n = 0`, `k = 0`, `k = K N`) and the Step 0 answer: the constant 2 holds at `‖ξ‖ = 1`, because `t‖ξ‖ ≤ t < 1`. Present: yes.

## 2. Statement vs ticket / paper (pilot §9 repair (A), Lemma 7.1 / (5.18), (2.52))
Conventions checked against the signatures: `edgeKer L ξ s t = (1 − sξ•SB)·Θ(tξ)`; `edgeKer_eq`: `= 1 − (s−t)ξ•(SB·Θ(tξ))`; `Uker_factor` (T1485) gives `Uker L ξ t (u k)` as the explicit two-sided inverse of `Uker L ξ (u k) t`. The pilot §9 inverse `⊗(1 + (u_k − t)ξSΘ_{u_kξ})` is exactly `edgeKer L ξ t u_k`. So the audited direction (large time first, small time second) is the right one.
- **T1** `sum_norm_edgeKer_back_row_le (hL : 3 ≤ L) (0 ≤ u) (u ≤ t) (t < 1) (‖ξ‖ ≤ 1) x`: `∑ c ‖edgeKer L ξ t u x c‖ ≤ 1 + (t−u)‖ξ‖(1−u‖ξ‖)⁻¹ ∧ that ≤ 2`. Matches the ticket's (T1) exactly: real `u, t` cast to ℂ, both inequalities.
- **T2** `norm_Uker_back_le`: `∀ i, ‖ξ i‖ ≤ 1`, `0 ≤ u ≤ t < 1`, `0 ≤ M`, `∀ b, ‖A b‖ ≤ M` ⟹ `∀ a, ‖Uker L ξ t u A a‖ ≤ 2^n * M`. This is the ticket's allowed "∀ M" form. The extra `0 ≤ M` costs nothing, since it follows from `hA` whenever `LoopArg L n` is nonempty, which it always is.
- **T3** `norm_Uker_back_grid_le`: same bound for `Uker L ξ (t N) (Gauss.Grid.time s t K N k)` with `k ≤ K N`, under the grid well-formedness hypotheses `K N ≠ 0`, `0 ≤ s N ≤ t N`, `t N < 1`. `time`/`step` are T1481's definitions (`time = s N + k·(t N − s N)/K N`). The argument order matches the inverse produced by `Uker_factor` with `u := time s t K N`, `t := t N`.
- **Uniformity (acceptance criterion):** the constant is `2^n` and nothing else. It does not depend on `u`, and there is no `(1−t)⁻¹` or `(1−u)⁻¹` in any conclusion. The only `(1−u‖ξ‖)⁻¹` sits in T1's intermediate expression, which T1 itself bounds by 2 on the whole hypothesis range. The real-arithmetic core (`back_bound_real`) needs only `t‖ξ‖ ≤ 1`.
- **σ = (+,−), ξ = |m|² (acceptance criterion):** the hypothesis is `‖ξ‖ ≤ 1` with arbitrary complex ξ, inclusive at 1. So it covers `ξ = |m|² ∈ [0,1]`, including the boundary `|m| = 1`. The compiled witness below uses `ξ = 1` exactly.
- Quantifier order: no `∀ᶠ N` is involved. T3 is stated at a fixed `N`, so it holds for every `N` and every `k ≤ K N`. That is uniform in `k`, as repair (A) needs.
- No paper delta is needed: the statements are exactly the ticket's (T1)–(T3).

## 3. Vacuity / hidden hypotheses / cycles
- Every hypothesis is an explicit inequality in the signature; there are no structure fields and no smuggled assumptions.
- Satisfiable with nondegenerate witnesses, compiled in the audit worktree (`lake env lean` scratch file importing the module, exit 0, no errors):
  - T2: `L = 3`, `n = 2`, `ξ ≡ 1` (the boundary `‖ξ‖ = 1`), `u = 0`, `t = 1/2`, `A ≡ 1`, `M = 1`.
  - T3: `L = 3`, `n = 1`, `ξ ≡ 1`, `s ≡ 0`, `t ≡ 9/10`, `K ≡ 5`, `N = 7`, `k = 3` (an interior grid point, with `u = 0.54 < t`).
- No loophole from `N = 0`, an empty index set or a collapsed window: `u < t` is allowed, and `u = t` is only a permitted endpoint. Nothing depends on a quantity being astronomically large.
- Dependencies: `sum_norm_edgeKer_row_le`, `norm_Uker_apply_le` (Kernel.lean, committed); `Gauss.Grid.time`/`step` (GridPath.lean, T1481, merged). All are on `main`. `Uker_factor` is not invoked; it only fixes the argument convention. There is no cycle, since the new file imports only `Hierarchy.Kernel` and `Gauss.GridPath`.

## 4. Build and axioms (audit worktree)
- `lake build RBM1D.Hierarchy.UkerBackBound`: Build completed successfully (3703 jobs).
- `lake build RBM1D`: Build completed successfully (9646 jobs); the root axiom audit is clean (20724 declarations, all within [propext, Classical.choice, Quot.sound]). Note: the root does not yet import the new module; per the ticket, the import is added at merge.
- `#print axioms` for `sum_norm_edgeKer_back_row_le`, `norm_Uker_back_le`, `norm_Uker_back_grid_le`: `[propext, Classical.choice, Quot.sound]`.
- `grep` finds no `sorry`/`admit`/`axiom` in the new file.

## Per-target verdicts
| Target | Verdict |
|---|---|
| T1 `RBM.sum_norm_edgeKer_back_row_le` | PASS |
| T2 `RBM.norm_Uker_back_le` | PASS |
| T3 `RBM.norm_Uker_back_grid_le` | PASS |
