# STATUS — current project state

> Updated 2026-09-22 11:14 UTC. This file holds only current decisions, blockers, and a short recent record. Completed ticket rows go to `docs/archive/TASKS-done.md`; full ticket evidence goes to `docs/reports/Txxx.md`. The previous STATUS snapshot is preserved verbatim in `docs/archive/STATUS-2026-09-22_11.md`; older history is in `docs/archive/STATUS-2026-09-19_22.md`. Search archives by ticket or formula number and read only the matching span.

## 1. Objective and proof boundary

- Formalize the whole paper `paper/250520-YinJun-v2.pdf`, including the six-step cycle, Theorem 2.21, Lemmas 2.18–2.20, main theorems, Theorem 2.6, and the final Lean report. The current tickets are the next dependencies, not the project endpoint.
- The sole authorized external mathematical input is the complex Hermitian form of [51] Theorem 2.2. The final report must identify the universality use of that input; all other paper components require independent Lean proofs.
- No `sorry` or new `axiom`; printed axioms may contain only `propext`, `Classical.choice`, and `Quot.sound`. Do not change frozen signatures. A conditional theorem is not a closed model witness. New hypotheses require a simultaneous nondegenerate satisfiability witness. Compare statements with the paper and record differences in `docs/paper-deltas.md`.
- The scheduler audits, assigns, integrates and pushes accepted work; Codex workers write Lean. `docs/TASKS.md` is the live queue. Theorem 2.6 starts after the other high-risk blocks are resolved, per Jun's ruling. Blueprint/Pages work is paused at Jun's request.

## 2. Current critical paths

| Component | Verified state | Next work |
|---|---|---|
| Step 2 first pass (A′), paper (2.71) | T280f's block-level `jG` conditional probability chain and T280g's near/endpoint evolved QV chain, including `ε ≤ W⁻¹`, build with allowed axioms. T280e proves endpoint-uniform `hinit`. The actual `hfamily` and `APrimeSlot'` are **not** closed. | T286 tests the common Good event and `jG ≤ cWt·Λ`; T291 proves time integrability of actual drift/cross and evolved QV rates; T287 queues `fitLhs.Qb`. The remaining `QBd`/family budgets must be tracked explicitly. |
| Lemma 5.14 / merged slot 4 | T278's bounded-length K chain and conditional `ψF ≺ η_u⁻¹` build with allowed axioms. T288 found a dependency cycle in the available `XiLK_(n+2) ≺ 1` supplier through `Lemma514 2`. The slot is **not** closed. | T290 replaces only the additive-error branch by a deterministic polynomial `xiSum` bound. T289 queues a genuine high-probability `FastDecay(H.F)` producer. Check the remaining `hnum` asymptotics and Case 1 before acceptance. |
| Equation (4.5), first grid cell / merged slot 5 | T279 separates good-event threshold `δ` from net spacing `μ`. T284 supplies `hg/hKp/hBK` from the Step 2 `LocalLawUnifIcc`; `first_cell_step5_of_localLaw'` now has only that existing upstream probabilistic input. Positive-length and eventually nonempty event witness, module/root builds and allowed-axiom audit passed. | Supply the Step 2 local law at the chosen first-cell scales and check the remaining cells in the final assembly. Do not infer whole-paper slot closure from the first-cell result. |
| Remaining slots and endpoint | T277's evolved endpoint QV work is partial. T281/T282 await a genuine first-pass witness; T283 is the independent six-step/main-theorem audit. | Continue by dependency order; audit the actual merged theorem hypothesis table and paper fidelity. |

## 3. Active work and ready queue

- Active, file-disjoint Codex tasks: T290 (`Gauss/Lemma514XiPoly.lean` and a primed insertion in `Lemma514QAssembly.lean`), T286 (`Gauss/APrimeJGModel.lean`), T291 (`Gauss/APrimeRateRegularity.lean`). These are in the three existing worker tasks; no new sidebar task was created for the heartbeat.
- Ready when a worker frees: T289 (`FastDecay(H.F)` event) and T287 (`fitLhs.Qb`). T281/T282 depend on full T280; T283 follows the production chain. See `docs/TASKS.md` for exact scopes and owners. T217 is the final-report revision lane; T159 is an older end-to-end audit ticket and must be reconciled with T283 before both are declared done.
- T285 proved the third weighted-Minkowski prefix integrability premise from time continuity of the actual weighted moment and integrability of `A+B`; it also compiled Gaussian counterexamples showing pointwise moments alone cannot provide the first two rate-integrability premises. T291 owns those two genuine model producers. Report: `docs/reports/T285.md`.

## 4. Decisions that still constrain work

- T230 route (B), which feeds exceptional-event mass through the time net, was compiled as vacuous. Continue the smooth-weight (A′) route; `WeightedMoment` must be supplied for the actual model, not merely a conditional constructor. See `docs/reports/T230.md` and `docs/CODEX-TICKETS.md`.
- Keep the first grid cell starting at `s=0`: the event-restricted Hölder modulus is the D17 route. The proposed paper change T251a was rejected. Do not reinstate the impossible all-sample modulus.
- For evolved (5.42), the global-diagonal `EarlyQVRateEv.jStar` cannot serve as the `J ≤ cWt·Λ` variable. T280f's block-level `jG` is the intended model; T280g's near-only remainder replaces the invalid bare `ρfar` row. The earlier claim that `log W ≥ 3` follows with `D=0` is false; the primed endpoint uses `D≥1` and the corrected logarithmic premise. See `docs/CODEX-TICKETS.md` §§17–18.
- The full `jSnorm` family estimate must be made **after** the coordinate-family sum using widened weights. The pre-family `weightedMoment_of_stepBound_mono` route cannot accept T280b's post-family exponent. This is D22 in `docs/CODEX-TICKETS.md` §18.
- For Lemma 5.14, use a finite-length K bound and the projected-drift estimate `norm_Qop_le_of_fastDecay`, without the `SumZeroDyn.Hierarchy` fiat. Do not set the error to zero to discharge `hnum`; choose decay exponents after fixed length and tolerance. T288's top-length `XiLK ≺ 1` route is circular at the base case.

## 5. Recent acceptance and repository state

- T279/T284 were independently checked: `lake build RBM1D.Gauss.Eq45FlowBudget` and root `lake build RBM1D` passed after the two Eq45 imports; the root audit reported 14515 `RBM` declarations, all within the three allowed axioms. Exactly their modules, reports, and two root imports were committed as `f1f26d0` and pushed to `origin/main` on 2026-09-22. Other workers' root imports and Lean files remained unstaged.
- T280f/g/e, T278, T285 and T288 have accepted **partial/conditional** results with reports, not complete first-pass or slot-4 closure. Do not count their uncommitted files as delivered to GitHub until integration audit and an appropriate build. The shared working tree can turn red during edits; check timestamps before interpreting `build.log`.
- `docs/paper-deltas.md` contains temporary `T274a`, `T275a`, `T277a` rows and other uncommitted work. Assign numeric IDs only after this shared file is stable. No new decision from Jun is pending in this snapshot.

## 6. Maintenance on every heartbeat

1. Re-read the live queue and recent reports, audit completions and assign every ownerless remainder to a bounded ticket. Keep at least three ready, file-disjoint tickets; recycle existing worker tasks when possible.
2. Run `python3 scripts/archive_done_tasks.py` to preview, then `--apply` for audited completed/closed rows. Never archive partial, blocked or merely claimed rows.
3. Keep this STATUS focused on current dependencies, rulings and at most eight recent acceptance items. Move obsolete narrative to a dated `docs/archive/STATUS-*.md` snapshot before removing it. Do not repeatedly append an unchanged heartbeat. Target ≤120 lines; archive sooner if stale material appears.
4. Commit only reviewed files and push accepted commits to `origin/main`; keep concurrent workers' unfinished files and shared paper-deltas out of the commit. Continue the same-thread 12-minute heartbeat quietly when nothing material changes.
