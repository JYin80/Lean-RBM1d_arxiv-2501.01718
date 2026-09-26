Auditor model: claude-opus-5-5

# T1524 audit (R4c-2b: Step 2 closes)

Branch `t/T1524` @ `6f56b8c`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1524`. The diff against `main` (ce3a0d2) touches exactly one file, the sole writable file `RBM1D/Gauss/Step2Close.lean` (+611 lines). No existing file changed, so no frozen signature was touched.

## Overall verdict: PASS (T1, T2, T3, T4)

## 1. Math preflight
`docs/reports/T1524-prove.md` §(a) has a math preflight marked PASS for each target (T1)–(T4). It comes before §(b), which covers the Lean. It records the Step 0 read of every merged interface, lists 9 interface mismatches with a proved bridge for each, and states the parameter choices with a check that they are simultaneously satisfiable. PASS.

## 2. Statement vs paper and ticket
- **(T1) `RBM.Gauss.Grid.gridPointwise'_gauss`**
  - Hypotheses: `hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`. These are step2's hypotheses minus `Hy` and `h1`.
  - Conclusion: the frozen T1520 `GridPointwise' d E s t` (`GridBootstrap.lean:226`), unchanged. It is proved, not assumed.
  - Quantifier order is the frozen one: `∀ D>0, ∀ u, ∃ δ₀>0, ∀ δ∈(0,δ₀], ∀ D₁>0, ∃ K, (K≠0) ∧ (∃ C, K+1 ≤ N^C eventually) ∧ ∀ᶠ N, Pg(bad) ≤ N^{-D₁}`.
  - The bad set has the full (2.76) bound: the factor `N^δ (η_s/η_u)^4 A_u^{-2} decayProf_D`, for every label pair and every endpoint `u ∈ [s,t]`.
  - `hκ1` is unused (linter warning). It is kept only so the hypothesis list matches the ticket. This is harmless.
- **(T2) `RBM.Gauss.step2_gauss`**
  - Conclusion: both conjuncts of `Step2.step2`, (2.75) and (2.76), at `B := band d`, `X := sample d`.
  - Hypotheses: step2's minus `Hy`. `h1 : Step1.Hyp` is also dropped, because it is discharged internally by `step1Hyp_gauss_of_scale''`.
  - This is the general statement: general `Dims`, `E` with `|E| ≤ 2-κ`, general windows `0 ≤ s ≤ t < 1`, all `D > 0`. It is not a special case or a conditional adapter.
- **(T3) `RBM.Gauss.steps12_gauss`**: `Steps12 (sample d) E s t` under the same hypotheses. It uses T1521's route with `step2_gauss` in place of the `hgp` input.
- **(T4)** Example (a): from step2's hypothesis list minus `Hy` (`h1` unused), `step2_gauss` proves step2's conclusion written out verbatim. Example (b): the target type is `type_of% (Step2.step2 (sample d) … Hy h1 …)`, proved by `step2_gauss` without `Hy` or `h1`.
- **Independent check.** In a scratch file importing `RBM1D` and `RBM1D.Gauss.Step2Close`, `type_of% (Step2.step2 (sample d) …) = type_of% (step2_gauss d …)` closes by `rfl`. So the conclusion is literally step2's for `sample d`.

PASS.

## 3. Vacuity, hidden hypotheses, cycles
- **Critical check (1), no `Hy` / `Step2.Hyp` anywhere.** I wrote my own metaprogram that computes the transitive constant closure over types and values:
  - `step2_gauss`: 4966 constants.
  - `steps12_gauss`: 4412 constants.
  - `gridPointwise'_gauss`: 4984 constants.
  - I searched each closure for `RBM.Step2.Hyp*`, any name containing `Step2.Hyp`, `RBM.Step2.step2` and `RBM.Step2.aprioriDecay`. There were **no hits**.
  - Positive control: the same checker on `RBM.Step2.step2` reports `[RBM.Step2.Hyp, RBM.Step2.step2]`.
- **Hidden hypotheses.** No new hypothesis, no structure-field hypothesis, and no new `Prop`-valued structure. `GridAE` and `rowSet` are auxiliary definitions. The theorems derive them: `GridAE` from T1516 a.e. (`ae_gridAE`), and `rowSet` from T1492 `highProb_eq557_colRow` (`highProb_grid_rowSet`). Neither is assumed.
- **Critical check (2), parameters fixed before `N` and independent of `ω`.**
  - `D' = max(D+4,64)` depends on `D`. `δ₀ = min(c/24,1)` depends on `c`.
  - `ζ = δ/96`, `ε = δ/4`, `τ₁ = δ/32`, `ζCtr = τ3 = ζ`, `τ57 = ζ/2`, and `κ' = δ/32` (used only inside `mgDrift_le`).
  - `K = gridK D' (D₁+2)` and `C = CK D' (D₁+2) + 2`.
  - All of these are `set` or `refine`d before the single `filter_upwards` over `N`. None mentions `ω`.
  - The only `ω`-dependent index is the random stopping time `gridTau ω`. It is the random target, as the ticket intends, not a parameter.
- **Critical check (3), `K` depends only on `(D, D₁, E, c)`.** `gridK D D₁ N = max 1 ⌈N^{D₁+2D+80}⌉` (`GridGoodEvent.lean:1648–1651`). With `D' = max(D+4,64)` and `D₁+2`, `K` depends only on `D` and `D₁`. That is a subset of `(D, D₁, E, c)`. PASS.
- **Cycles.** The new file imports only already-merged modules. Nothing on `main` imports it. No cycle.

## 4. Boundary cases
- **Degenerate grid `u N = s N`.** T1516 needs `s N < u N`. In this case `Δ = 0`, so `H_k = H_0` and `time_k = time_0` (proved lemmas `H_eq_H_zero_of_eq` and `time_eq_time_zero_of_eq`). The `J_0 < thr(u_0)` component of T1519's event then gives the result directly. The case is handled, not excluded.
- **`s N = 0`**: allowed, since only `0 ≤ s` is used.
- **Small `N`**: excluded only through `∀ᶠ N`, and `N ≥ 2` is used for `2N^{-(D₁+1)} ≤ N^{-D₁}`.
- **Probability budget.** The ticket's `G N` is extended with the row form of (5.57) (T1492). To pay for it, T6′ is used at `D₁+1`, so `K = gridK D' (D₁+2)`. The total is `N^{-(D₁+1)} + N^{-(D₁+1)} + 0 ≤ N^{-D₁}`, which is correct.
- **Coefficient bridge.** T1515 (T5)'s coefficient is converted to T1518 `driftCoef … (mgDrift …)` by `heG_coef_eq_driftCoef`, proved by `ring` after unfolding. This is an exact identity.
- **`Mg` budget.** `65·2752 N^{3δ/32} ≤ N^{δ/8}` holds once `N^{δ/32} ≥ 178880`, which is eventual in `N`, with `δ` fixed. This is not an astronomically-large-parameter witness.

## 5. Witness
No new hypothesis is introduced, so no new satisfiability witness is needed. The hypothesis set is exactly `Step2.step2`'s minus `Hy` and `h1`. Nondegenerate instances of its components already exist, for example `firstCell_boundsCore : BoundsCore (sample d) 0 (fun _ => 0)` (`APrimeFirstCellInitialMomentBudget.lean:36`).

## 6. Dependencies
All dependencies are merged on `main`: T1492, T1513, T1515 (amend-1), T1516, T1517, T1518, T1519 (amend-1), T1520 and T1521. The branch contains only the one new file on top of `main` @ ce3a0d2. PASS.

## 7. Build and axioms
- `lake build RBM1D.Gauss.Step2Close`: `Build completed successfully (3966 jobs)`. The only warning in this file is the unused `hκ1`.
- `lake build RBM1D`: `Build completed successfully (9672 jobs)`. The root import is not yet added; it comes at merge, per the ticket.
- **Root-adjacent check.** A scratch file importing both `RBM1D` and `RBM1D.Gauss.Step2Close` elaborates with no errors and no name clashes. In it, `#print axioms` for `step2_gauss`, `steps12_gauss` and `gridPointwise'_gauss` gives `[propext, Classical.choice, Quot.sound]`.
- **In-file axioms.** The in-file `#print axioms` for all 14 declarations give the same three axioms.
- **Forbidden tokens.** A grep finds no `sorry`, `admit` or `axiom` in the file.

## Per-target verdicts
- (T1) `RBM.Gauss.Grid.gridPointwise'_gauss`: **PASS**
- (T2) `RBM.Gauss.step2_gauss`: **PASS**
- (T3) `RBM.Gauss.steps12_gauss`: **PASS**
- (T4) audit examples and `#print axioms step2_gauss`: **PASS**

Note for merge: after the root import is added, the hub should re-run the root axiom audit on `main`. I expect it to be clean, based on the root-adjacent check above.
