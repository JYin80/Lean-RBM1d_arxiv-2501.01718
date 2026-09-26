Auditor model: claude-opus-5-5

# T1525 re-audit (repair r1): G1c P0(c) read-only inventory

Audited: `docs/reports/T1525-prove.md` (repair r1, 711 lines), against ticket `docs/tickets/T1525.md` and the previous audit (RETURN, 7 fixes). `main` is at `9641a9a`. `git diff --stat ae718fe HEAD -- '*.lean'` prints nothing. Branch `t/T1525` has no commits (`git log main..t/T1525` is empty). No tracked `.lean` file is modified. Report-only ticket: there is no module to build.

The checks below were run by the auditor with `lake env lean` on scratch files in the session scratchpad, against the main-worktree oleans. The auditor wrote its own independent constant-closure script, `Aud1525r.lean`. It follows type + value of thm/defn/opaque, inductive → ctors, ctor → inductive, and rec → major inductive. It flags names containing `MomentDuhamel.Hyp` or `Step2.Hyp`, names with a `jStar` name component, types with an `h560` binder, and constants whose module name contains `APrime`.

## Overall verdict: PASS

All 7 fixes are addressed in substance. The quoted outputs reproduce exactly. The new findings F1–F4 check out.

## Fix-by-fix check

| # | Required fix | Status | Evidence |
|---|---|---|---|
| 1 | (I2): `flow_hs1` with five attributes; all-charge premise; (+,−)-only variant | DONE | The #check signature matches the report's row 5 verbatim: `h277` is over `TimeIcc × LoopData (B.L N) 2`, `‖Lval‖ ≤ scale⁻¹^(2-1)`. StepGlue.lean:515–527 builds `hpm` by `h277.precomp_param` along `Step45.pmData` and uses only `hpm`, `h45` and `stochDom_flowXiLK`, so the claim that "only (+,−) is used" is correct. The M2a/M2b smallest-missing statements are precise, and the (I2) answer is revised |
| 2 | (I1) dependency column for eq45Flow producers | DONE | Own script: `eq45Flow_of_unifDom` closure 56538, `eq45Flow_of_goodSetFlow_highProb` 57649, each with exactly 1 APrime constant `RBM.Gauss.goodSetFlow` (APrimeGeneralMovingCarrierCore). Identical to report §0.4/A.4 |
| 3 | Transitive check everywhere; re-run of the Lemma514Holder, condExpDiag and producer greps | DONE | See "Re-run commands" below. The script core is quoted, and its counts are reproduced exactly by an independent script |
| 4 | (I4) full consumer list with file:line, no "presumably", `AprioriDecayAll` as entry | DONE | `grep -n presumably` finds nothing in the report body (only the fix-map row mentions the word). All 18 StepGlue line numbers checked with `sed` (386/437/453/469/493/535/542/590/599/617/627/634/701/704/710/715/725/730), plus Step3 473/502/524/594/606/608/625/639/656, Step45 242/257, Step2PP 322/345/408/426, Step3FlowSharp 33/65, ChargeReduce 215/229. All match. `#print AprioriDecayAll` and `AprioriDecayPP` and `#check aprioriDecayAll_of_pp'` match the report |
| 5 | Correct the three names; correct the `norm_lkErr_one_le` description | DONE | `#check` succeeds for `RBM.StepGlue.norm_lkErr_one_le` (`(∀ ij, llErr ≤ c) → lkErr v.idx ≤ c`, `v : LoopData _ 1`), `RBM.StepGlue.flow_lkErr_one_le'` (`LocalLawFlow → StochDom lkErr (scale⁻¹^(1/2))`) and `RBM.StepGlue.flow_S_one'` (`… Cond272 → LocalLawFlow → ∀ l, S … 1 l`). The descriptions match |
| 6 | Five attributes for every (I2)–(I4) citation; `Lemma514Premises` antecedent | DONE (one cosmetic gap, below) | (I2) has 10 rows with every column filled. (I4) has 19 consumer rows with every column filled. (I3) is filled except the forbidden-lemma row. The `hseq` antecedent `Lemma514Premises X E s t n Λ Φ` is now listed, together with its 4 interval-uniform conjuncts |
| 7 | (I1) missing pieces | DONE | The (4.5)∘(2.76) shape and the "not `Eq45Flow`" statement are explicit. S1 names the restriction (`StochDom.precomp_param` + `localLawUnifIcc_of_localLawFlow`, `hmaj` by `le_rfl`). S2 discharges `hΨlo` via `Step1.inv_W_le_inv_scale` (checked: `(B.W N)⁻¹ ≤ (B.scale E N u)⁻¹` for `0 ≤ u < 1`), `hΨhi` via `Step2.eventually_R4_le_scale` (checked: gives `N^c ≤ scale u` on `TimeIcc`) and `hη` via `W·ℓ·η`, `ℓ ≤ L` and `WL = N`. S5 names `stochDom_reindex_of_forall_seq` / `eventually_forall_measure_slice_le` plus a union bound. The T1524 references now say merged (`step2_gauss` :519, `steps12_gauss` :541; #check signatures match the report's description). `grep -in pending` finds only the meta sentence on line 6 |

## Re-run commands (auditor's own runs, compared with the report)

1. **A.2 Lemma514Holder grep.** 4 hits (942, 950, 985, 1011), identical to the report.
2. **A.3 condExpDiag grep.** 28 lines. The file:line set is identical to the report (CondExpMod ×8, CondStableFlow ×8, CondDom ×5, DetFlucAvgTimeNet ×1, DetIBPWeighted ×4, IBP ×2). `#check norm_condExpDiag_flow_sub_le_rpow` confirms that it is a two-time modulus (`∀ u v ∈ Icc`, `≤ N^K|u−v|^{1/2}` on `flowNetEvent`). `#check holIBP_of_inputs` confirms it discharges the `hHolIBP` shape under `HolConst`. The report's classification (CondDom/IBP/DetIBPWeighted give fixed-time remainders; CondExpMod/CondStableFlow give time moduli) is correct. F4 holds.
3. **A.1 `(h560` grep.** 8 lines, identical.
4. **A.5.** Both restriction greps print nothing, identical.
5. **`git log -S "def goodSetFlow"` / `"def sigPM"`.** `9d6dde5`, `a0214fc` / `6e92b71`, `34831e4`, identical.
6. **Constant closure (independent script), 16 declarations.** Closure sizes and flag counts equal the report's §0.4 in every case:
   - `detAvgIBP_stochDom_of_localLaw_complete`: 57540, APrime 1 (`goodSetFlow`), others 0.
   - `step2_gauss`: 70124; MD 0, S2H 0; jStar names `RBM.Step2.jStar*` only; h560 9; APrime 169 in 14 modules.
   - `steps12_gauss_of_grid`: 63742, APrime 4 (`sigPM`, `aprioriRhs`, `flowDelta`, `flowDelta._proof_1`).
   - `flow_hs1` 20640, `AprioriDecayAll` 19744, `flow_sharpLoop_glue` 52079, `Step2PP.xiLK_two_le` 20577, `lemma514_of_seq` 20732, `hHol_flow` 53365: all clean.
   - `lemma514_of_hHol_flow` 59164 and `flow_sharpLmK_of_hHol_flow` 59441: MD 6 each.
   - `Step2.kval_stochDom` 19455: `sigPM` only. `norm_condExpDiag_flow_sub_le_rpow` 54708: `goodSetFlow` only.
   - `Lemma514OneLoopSharp.stochDom_flowXiLK_one_of_gaussian_hypotheses`: 69731, h560 3, APrime 1687 in 151 modules.
   - The previous audit's figure of 4599 constants for the producer was an undercount from its own script. The report's correction (F1) is right: `goodSetFlow` is reachable.
7. **F3 compiled negative.** `lake env lean t1525r/Neg.lean` exits 0 and prints `'t1525_hfine_hWδ_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound]`, with no `sorry`. Its `hfine` and `hWδ` are verbatim the binders at Eq45Small:512–513/525 and MinorDiffCond:1304–1305/1317 (checked with `sed`). Rows 6 and 8 are therefore vacuous as claimed.

## Section verdicts

- **(I1): PASS.** The recommendation is `detAvgIBP_stochDom_of_localLaw_complete` at fixed grid times, general `Dims`, via M1 (`xiLK_one_le_one_at_seq` + grid form, 1 ticket). M1's hypotheses are `step2_gauss`'s plus `hu : u N ∈ Icc (s N) (t N)`, so the T1524 witness with `u := t` gives nondegenerate satisfiability. The flow producers (rows 5–8) are correctly marked as not usable.
- **(I2): PASS.** `flow_hs1` is found and analysed. M2a/M2b are precise. The route choice (M1 for goodSet514's Ξ_1) is justified.
- **(I3): PASS.** The `lemma514_of_seq` hypothesis list, including the `Lemma514Premises` antecedent, matches Lemma514Moment:408–424. No hypothesis is a stopped-path statement. The four `MomentDuhamel.Hyp` consumers are forbidden; `flow_sharpLmK_of_hHol_flow` is a new catch.
- **(I4): PASS.** The input shapes match #check. The charge-sup is correct. `AprioriDecayAll`, and its one-charge reduction to `ChargeReduce.AprioriDecayPP` via `aprioriDecayAll_of_pp'`, is correctly identified as the (+,+)/(−,−) entry point. `Step2PP.BootPP.step` is correctly flagged as a stopped-path hypothesis.

## Non-blocking notes (no return required)

1. In the (I3) row for the four forbidden `MomentDuhamel.Hyp` lemmas, Time and Dims are "—". These lemmas are excluded, and the one attribute that matters, the dependency (MD: 6), is given and verified.
2. The A.5 parenthetical lists `LocalLawUnifIcc d E u u` hits only in `APrimeFixedOneLoopGeneralDims.lean:32/:82`. The raw grep has 12 hits. The other 10 are hypotheses (DetAvgIBPFlow, DetFlucAvg*, DetFlucThreshold) or a self-transform (DetFlucThreshold:69, from `hll` of the same shape), so the claim "only producer outside the consumers" stands, but the text reads as if it were the full output.
3. Open issues O1 (the merged `step2_gauss` reaches 169 APrime theorem constants; the recommended producer reaches the relocated def `goodSetFlow`) and O3 (paper-delta for the (4.5)∘(2.76) shape) are dispatcher decisions. They are correctly escalated, not decided.

## Build / axioms / files

- No Lean changed on `t/T1525` or in the main worktree for this ticket. Frozen signatures are untouched.
- Scratch `Neg.lean` axioms: `[propext, Classical.choice, Quot.sound]`. Report-only ticket; no `lake build` target.
