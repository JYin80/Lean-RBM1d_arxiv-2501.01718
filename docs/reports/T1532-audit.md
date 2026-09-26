Auditor model: claude-opus-5-5[1m]

# T1532 audit: sharp `Ξ₁ ≺ 1` simultaneously at all grid points (PP-1(b), G1c Step 3)

Audited: branch `t/T1532` @ `10259ba` (one commit on top of `main` `43d3e79`; `git diff main...t/T1532` touches only `RBM1D/Gauss/OneLoopSharpGridAll.lean`, +174). Worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1532`. Ticket `docs/tickets/T1532.md`. Prove report `docs/reports/T1532-prove.md`. Audit time: 2026-09-26T16:47Z.

**Overall: PASS.** (T1) PASS, (T2) PASS. There is one non-blocking correction to the prove report (§4 below): `highProb_grid_of_flow` **is** in the transitive closure, although only through T1527 and not through this file.

## 1. Math preflight
Prove report §(a) contains a math preflight for (T1), with verdict PASS, written before the Lean. It covers the statement vs paper (Lemma 4.1 (4.5) + (2.76), n = 1), hypotheses, quantifier order, boundary cases, dependencies, route soundness and a witness. PASS.

## 2. Statement vs ticket and paper
The ticket target is: under `steps12_gauss`'s hypotheses, for every ε > 0 and every grid (s, u, K) with K+1 ≤ N^C, `HighProb (Pg d) {ω | ∀ j ≤ K N, ∀ w, scale(u_j)·lkErrMat(u_j, H_j ω, w) ≤ N^ε}`, for both charges.

The Lean statement is `RBM.Gauss.highProb_grid_xiLK_one`:
- **Hypotheses.** `hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg` are verbatim the list of T1527's `stochDom_lkMax_one_of_steps12`, apart from T1527's per-point `hu`, which the grid replaces. The grid data is `K : ℕ → ℕ`, `hK0 : ∀ N, K N ≠ 0`, `hC0 : 0 ≤ C`, and `hKcard : ∀ᶠ N, (K N + 1 : ℝ) ≤ N^C`.
  - `hK0` is the nondegeneracy condition that `Grid.map_H_eq` and `Grid.time_last` need. Without it the grid does not end at t. The same hypothesis appears in the accepted `Grid.highProb_grid_of_flow`. It is not a special case.
  - `hC0` is harmless: K+1 ≥ 2 already forces C > 0 eventually.
- **Arbitrary grid: PASS.** `s, t, K, C` are universally quantified theorem parameters. There is no specialization to `exampleGrow`, fixed D, first cell, E = 0, or a particular sequence. The grid times are `Grid.time s t K N k` for `k : Fin (K N + 1)`, which includes both endpoints k = 0 (= s N) and k = K N (= t N). `Grid.mem_Icc_time` keeps every grid time in the closed window `[s N, t N]`.
- **ε before N: PASS.** `ε` and `hε : 0 < ε` are theorem parameters. `HighProb` unfolds to `∀ D > 0, ∀ᶠ N, (Pg d)(·)ᶜ ≤ N^{-D}` (`Defs/StochDom.lean:95`), so the order is ε, D, then N. There is no per-N choice of ε.
- **Both charges: PASS.** `v : LoopData (d.L N) 1 = (Fin 1 → Bool) × (Fin 1 → ZMod L)` ranges over both charge bits. The pointwise bound comes from `Sample.lkErr_le_lkMax` for every `v`.
- **Loss/exponent.** The bound is `≤ N^ε` with no extra loss. This is `≺ 1` at the tight scale `(band d).scale E N u_k`, the same scale as T1527's audited statement.
- **Random object.** `Grid.H d s t K N k` under `Grid.Pg d` is the grid matrix path of `GridPath.lean`. The transfer uses only one-time laws at each fixed k (`map_H_eq`, an equality of pushforward measures). The event is a finite intersection of one-time events, and the union bound is applied on the grid side, so there is no stopped-path or joint-law claim. This complies with CLAUDE.md §3.5.

## 3. Vacuity, hidden hypotheses, cycles
- The steps12 hypothesis list is T1527's audited list, with its audited paper witness: `exampleGrow`, E = 0, κ = 1, s ≡ 0, 1 − t_N = N^{-1/100}, c = 1/10.
- The grid data is independent of that list. The witness is K N = N+1 (so `hK0` holds for all N) and C = 2 (`N+2 ≤ N^2` for N ≥ 2). This gives at least 2 grid points, no collapsed window, and nothing astronomically large.
- Loopholes checked:
  - N = 0 is not used.
  - The index set `Fin (K N + 1) × LoopData` is nonempty.
  - There is no structure-field hypothesis.
  - There is no cycle: the file imports only `OneLoopSharpGrid` and `Lemma514Moment`, both merged.
- The witness is a paper argument, not compiled. This follows the T1524/T1527 convention and adds only trivially satisfiable grid hypotheses. Non-blocking.

## 4. Dependencies and route
- The route used matches the ticket's route:
  1. `stochDom_lkMax_one_of_steps12` (T1527), at an arbitrary grid-valued `v`;
  2. `unifDomIcc_of_forall_stochDom` (`Lemma514Moment.lean:128`, merged). This is a legitimate quantifier exchange, because `StochDom`'s τ and D precede `∀ᶠ N`. `UnifDomIcc` (`Eq45FlowInputs.lean:126`) is per-u, uniform in u;
  3. `Grid.map_H_eq` (`GridPath.lean:452`) via `Measure.map_apply` on both sides, with measurability from `H_measurable_filt`, `measurable_H` and `measurable_lkErrMat`;
  4. `HighProb.biInter` (`Defs/StochDom.lean:313`) over `Fin (K N+1) × LoopData`, with cardinality ≤ N^{C+2} eventually from `hKcard` and `card_loopData_le`.
- All dependencies are already accepted, merged results.
- **`highProb_grid_of_flow` not used: PASS, with a correction to the prove report.** The file's proof term does not reference it. However, my independent closure BFS finds `RBM.Gauss.Grid.highProb_grid_of_flow` **in** the closure of `highProb_grid_xiLK_one`. It is equally in the closure of T1527's `stochDom_lkMax_one_of_steps12`, so it comes from the merged `steps12_gauss` chain, where `Step2Close.lean:148` and `GridGoodSet.lean:877` apply it with their own continuum inputs. Prove report §(b) says "`Grid.highProb_grid_of_flow` does **not** appear among the 70150 reached constants". That sentence is factually wrong. The ticket's prohibition is about the route of this step, and it is honored: nothing here feeds a `UnifDomIcc` or pointwise input into `highProb_grid_of_flow`. This is a documentation error only and does not affect the verdict.

## 5. (T2) Transitive closure (independent script)
I wrote my own scratch script, not committed. It does a worklist BFS over type, value (`allowOpaque`), inductive constructors and recursor rules, and I ran it with `lake env lean` in the audit worktree after the module build.
- Closure size: 70150 (T1527's `stochDom_lkMax_one_of_steps12`: 70142). This matches the prover's count.
- `RBM.MomentDuhamel.Hyp`: absent. `RBM.Step2.Hyp`: absent. `RBM.EarlyQVRateEv.jStar`: absent.
- The `jStar`-named constants are `RBM.Step2.jStar` (paper (5.29)) and its lemmas, plus Mathlib `conjStarAlgAut*` false positives. All of these are identical to T1527's audited closure. `RBM.Step2.jStar` is not the banned object (per T1527 audit / §10b).
- Constant names containing `h560`: none. `gmOfJS`, `h535_of_jS`, `exampleGrow`, `sorryAx`: absent.
- `RBM.Step1.Hyp` (and `.mk/.lift/...`) is present, as in T1527. `steps12_gauss` discharges it, and it is not banned.
- APrime use is inherited unchanged from T1527 (DECISIONS §10b, audited in T1527). This file adds no new APrime dependency, because every new constant it reaches is a generic grid/probability lemma.

## 6. Build and axioms
- `lake build RBM1D.Gauss.OneLoopSharpGridAll`: `Build completed successfully (3968 jobs)`, with no errors and no warnings from this file. `#print axioms RBM.Gauss.highProb_grid_xiLK_one`: `[propext, Classical.choice, Quot.sound]`.
- `lake build RBM1D` (root, audit worktree; the new module is not yet root-imported, so the import is added at merge): `Build completed successfully (9676 jobs)`, no errors.
- `sorry`/`admit`/`axiom` grep on the file: empty. The diff is a single new file, so no frozen signature is touched.

## Verdicts
- (T1) `RBM.Gauss.highProb_grid_xiLK_one`: **PASS**
- (T2) axioms + transitive-closure criterion: **PASS** (correct the prove report's claim that `highProb_grid_of_flow` is absent from the closure; it is inherited via T1527/`steps12_gauss`)
