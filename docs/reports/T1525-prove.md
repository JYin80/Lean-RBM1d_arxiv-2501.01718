Prover model: claude-opus-5-5

# T1525: G1c P0(c) inventory of the Lean state for (4.5), S(1,l), the §10b reuse checks and the S(2,l) inputs (repair r1)

- Repair of the report returned by `docs/reports/T1525-audit.md` (verdict RETURN, 7 required fixes).
- Written 2026-09-26 12:27 UTC (`date -u`), against `main` at `ae718fe`. T1524 is merged: `step2_gauss` is at `Gauss/Step2Close.lean:519` and `steps12_gauss` at `:541`. Every "pending" reference from r0 is replaced.
- This is a report-only ticket:
  - No `.lean` file in the repository was created or edited.
  - Every check ran with `lake env lean` on scratch files in the session scratchpad, against the oleans of the main worktree.
  - There is no module to build.
- CLAUDE.md §3.6 applies: every attribute below comes from the signature and from the dependency script. Nothing is taken from docstrings.
- Re-verified 2026-09-26 15:14 UTC (`date -u`) against `main` at `9641a9a`:
  - `git diff --stat ae718fe HEAD -- '*.lean'` printed nothing, so no Lean file changed after the runs below (T1526 is report-only).
  - `lake env lean <scratchpad>/t1525r/Compact3.lean` re-ran with exit 0 and reproduced the lines quoted in §0.4 verbatim. These cover `AprioriDecayPP`, `aprioriDecayAll_of_pp'/_of_pp`, `flow_sharpLoop_glue`, `flow_steps45_glue`, `SharpLoopFlow`, `traceMomentBound_gauss`, `flow_steps45_W` (0 flags each) and `flow_sharpLmK_of_hHol_flow` (MD: 6).
  - The A.2 grep re-ran with the same 4 hits. The A.3 grep re-ran with the same 28 lines.
  - `sed -n` spot checks confirmed every §I4 file:line: StepGlue 386/437/453/469/493/507/515/522/535/542/590/599/617/627/634/701/704/710/715/725/730; Step3 473/502/524/594/606/608 and 625; Step45 242 and 257; Step2PP 322 and 408; Step3FlowSharp 33 and 65; ChargeReduce 215 and 229; Step2Close 519 and 541.
  - The §I4 consumer table now has the five attributes on every row.

## Where each audit fix is addressed

| Audit §4 item | Where |
|---|---|
| 1. `flow_hs1` with five attributes; its all-charge premise; the (+,−)-only variant | §I2, table row 5, "Answer" and M2a/M2b |
| 2. goodSetFlow dependency of the eq45Flow producers | §0.4, §I1 rows 5–8 |
| 3. Transitive check everywhere; Lemma514Holder, condExpDiag and producer greps re-run and explained | §0 (script and outputs), §I1 "condExpDiag", §I3, Appendix A |
| 4. Every §3 consumer with file:line; no "presumably"; AprioriDecayAll as the entry point | §I4 |
| 5. Correct names; correct description of `norm_lkErr_one_le` | §I2 rows 1–3 |
| 6. Five attributes for every (I2)–(I4) citation; `Lemma514Premises` antecedent | §I2–§I4 tables; §I3 `lemma514_of_seq` |
| 7. (I1) missing pieces: the (4.5)∘(2.76) shape, restriction step, hΨlo/hΨhi/hη, grid step, T1524 now merged | §I1 "Recommended producer" M1, steps S1–S5 |

**New findings of this repair.** Each one is backed by a command in §0 or Appendix A.

- **(F1) The recommended producer uses one constant defined in an `APrime*` file.** `detAvgIBP_stochDom_of_localLaw_complete` reaches `RBM.Gauss.goodSetFlow` through `detAvgIBP_stochDom_of_localLaw'`. `goodSetFlow` sits in `APrimeGeneralMovingCarrierCore.lean`, so r0 and the audit were both wrong to call it clean.
  - `goodSetFlow` is a plain event definition. It was moved into that file by commit `9d6dde5` (git log in §0.3).
  - No APrime *theorem* is reachable (§0.5).
- **(F2) The merged Step 2 output `step2_gauss` depends on APrime theorem files.** Its closure contains 169 constants from 14 `APrime*` modules. These include `APrimeAllTimeOneLoopGeneralDims.highProb_centeredEvent`, `APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`, `APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale` and `APrimeFullQV.early_raw_full` (§0.5).
  - It does **not** contain `MomentDuhamel.Hyp`, `Step2.Hyp` or `EarlyQVRateEv.jStar`.
  - It does contain `RBM.Step2.jStar`, which is a different constant.
  - It also contains 9 lemmas carrying an `h560` binder. `step2_gauss` itself has no `h560` binder, so these are discharged internally.
  - This is recorded as open issue O1 for the dispatcher. It is not a verdict on T1524.
- **(F3) Two eq45Flow producers named by the ticket are vacuous.** `eq45Flow_of_goodSetFlow_highProb` (Eq45Small:507) and `eq45Flow_of_goodSetFlow_budget` (MinorDiffCond:1299) both contain the hypothesis pair `(hfine, hWδ)`, and that pair is unsatisfiable. A negative statement was compiled (Appendix A.6).
- **(F4) r0 was wrong that no `condExpDiag` time modulus exists.** Two exist: `RBM.Gauss.norm_condExpDiag_flow_sub_le` (CondExpMod:339) and `_rpow` (CondExpMod:420). The three Hölder slots `hHolIBP/hHolRow/hHolBlk` are discharged by `holIBP_of_inputs`/`holRow_of_inputs`/`holBlk_of_inputs` (CondStableFlow:1627/1586/1604), under `HolConst`.
  - This does not rescue the flow producers, because they fail on F3 and on the `(hfine, hΩ)` pair.
  - The recommendation does not change.

---

## §0 Dependency method and raw outputs (fix 3)

### 0.1 The check

The script `Closure.lean` imports the root `RBM1D` and does the following for each declaration `n`:

- It computes the **transitive constant closure**: every constant occurring in the type or the value (the proof term) of `n`, closed recursively, plus the constructors of every inductive type reached.
- It flags constants in these categories:
  - names containing `MomentDuhamel.Hyp`;
  - names containing `Step2.Hyp`;
  - names having `jStar` as a **name component**. This avoids the audit's `conjStar` false positive; substring-only matches are printed separately.
  - names containing `560`;
  - constants whose *type* contains a binder literally named `h560`. `h560` is a binder name, not a constant; see the grep in A.1.
  - constants defined in a module whose name contains `APrime`.
- It prints `file:line` from `findDeclarationRanges?` (the `selectionRange`), the transitive import closure of the module, and `Lean.collectAxioms`.

The core of the script (verbatim):
```lean
def usedConsts (ci : ConstantInfo) : Array Name :=
  let a := ci.type.getUsedConstants
  let b := match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  let c := match ci with
    | .inductInfo ii => ii.ctors.toArray
    | _ => #[]
  a ++ b ++ c

def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work : Array Name := #[root]
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci => for m in usedConsts ci do
        if !seen.contains m then work := work.push m
    | none => pure ()
  return seen
```
Two companion commands, both in the same scratch directory:

- `#compact` prints counts per category.
- `#aprimepath` runs a BFS with parent pointers. It prints the shortest usage chain to an APrime-module constant and the "frontier" of APrime constants referenced from non-APrime ones.

Command used: `cd /Users/junyin/Lean_proof/RBM1D && lake env lean <scratchpad>/t1525r/{Run,Compact,Compact2,Compact3,Path,Path2,Path3}.lean`. All runs exited 0.

### 0.2 Why an import-chain grep is not used as the verdict

An import-chain grep flags every module that imports `Hierarchy.StepGlue`, because `StepGlue`'s import closure already contains two APrime modules. The constant closure of the same declarations contains no APrime constant. Verbatim `Run.lean` output:
```
== RBM.StepGlue.flow_hs1  @ RBM1D.Hierarchy.StepGlue:507
  closure size: 20640; flagged: 0 []
  'jStar' substring, not a name component (false positives): []
  module import closure: 5289 modules, of which APrime*: 2 [RBM1D.Gauss.APrimeGeneralMovingCarrierCore,
 RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore]
  axioms: [propext, Classical.choice, Quot.sound]
```
The import closure is therefore reported only as supporting information. The verdict comes from the constant closure.

### 0.3 The APrime "core" modules contain relocated paper definitions

Four constants flagged below are old definitions that later refactor commits moved into `APrime*` core files: `goodSetFlow`, `aprioriRhs`, `flowDelta` and `sigPM` (`tT` is the same case). Verbatim:
```
$ git log --oneline -S "def goodSetFlow" -- RBM1D
9d6dde5 Accept audited carrier predicate core extraction
a0214fc T124: the (4.5) flow inputs up to the net; slow variation from a modulus, not from Lmax ~ 1/W
$ git log --oneline -S "def sigPM" -- RBM1D
6e92b71 Accept audited T651 T652 T654 T659 clean cores
34831e4 T61: §5.3 Step 2 — (2.75)(2.76) via the self-improving inequality at the stopping time
$ git log --oneline -S "def aprioriRhs" -- RBM1D
9d6dde5 Accept audited carrier predicate core extraction
f428012 T67: §5.1 Step 1 — (2.73)(2.74) via the (5.9) forbidden-region lemma
```
`goodSetFlow` at `APrimeGeneralMovingCarrierCore.lean:72` (verbatim):
`def goodSetFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (δ : ℕ → ℝ) (N : ℕ) : Set (Ω d) := {ω | ∀ u ∈ Set.Icc (s N) (t N), GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) (δ N)}`.

Its own closure contains no other APrime constant:
```
== RBM.Gauss.goodSetFlow  @ RBM1D.Gauss.APrimeGeneralMovingCarrierCore:72
  closure size: 17272; flagged: 1 [RBM.Gauss.goodSetFlow [APrime-module] (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
```
Under the ticket's literal criterion ("any `APrime*` file"), a dependency on these constants **counts as YES**. The table therefore says "YES (relocated def only)" when the only APrime constants reached are these, and "YES (APrime theorems)" otherwise.

### 0.4 Result table (every declaration cited in this report)

Legend:
- MD = `MomentDuhamel.Hyp`; S2H = `Step2.Hyp`; jS = `EarlyQVRateEv.jStar` (other `jStar` constants are named where they occur).
- "h560" means a constant named `*560*` or with an `h560` binder in its type.
- "Ax std" means `[propext, Classical.choice, Quot.sound]`.
- "0/0/0/0" means no MD, S2H, jS or h560 hit.
- Every declaration printed Ax std, except `RBM.LoopData`, which printed `[]`.

| Declaration | file:line | closure | MD/S2H/jS/h560 | APrime |
|---|---|---|---|---|
| `RBM.norm_trace_green_sub_mul_Eblk_le` | Green/EntryBound:1338 | 46814 | 0/0/0/0 | none (import closure also 0) |
| `RBM.avg_bound_stochDom` | Green/EntryBound:1628 | 46899 | 0/0/0/0 | none |
| `RBM.StepGlue.Eq45Flow` | Hierarchy/StepGlue:398 | 19741 | 0/0/0/0 | none |
| `RBM.Gauss.eq45Flow_of_inputs` | Gauss/Eq45Flow:227 | 47012 | 0/0/0/0 | none |
| `RBM.Gauss.eq45Flow_gauss` | Gauss/Eq45Flow:246 | 51581 | 0/0/0/0 | none |
| `RBM.Gauss.eq45Flow_of_unifDom` | Gauss/Eq45FlowInputs:628 | 56538 | 0/0/0/0 | **YES (relocated def only)**: `goodSetFlow` |
| `RBM.Gauss.eq45Flow_of_goodSetFlow_highProb` | Gauss/Eq45Small:507 | 57649 | 0/0/0/0 | **YES (relocated def only)**: `goodSetFlow` (in its signature, `hΩ`) |
| `RBM.Gauss.eq45Flow_of_localLaw_gain_budget` | Gauss/MinorDiffCond:1229 | 57370 | 0/0/0/0 | **YES (relocated def only)**: `goodSetFlow` |
| `RBM.Gauss.eq45Flow_of_goodSetFlow_budget` | Gauss/MinorDiffCond:1299 | 57624 | 0/0/0/0 | **YES (relocated def only)**: `goodSetFlow` |
| `RBM.Gauss.Lemma514OneLoopSharp.stochDom_flowXiLK_one_of_gaussian_hypotheses` | Gauss/Lemma514OneLoopSharp:66 | 69731 | 0/0/0; other jStar: `RBM.Step2.jStar`; h560: 3 (`Lemma57.case2_pointwise`, …) | **YES (APrime theorems)**: 1687 constants in 151 modules |
| `RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete` | Gauss/DetAvgIBPFlow:274 | 57540 | 0/0/0/0 | **YES (relocated def only)**: exactly `goodSetFlow`, via `detAvgIBP_stochDom_of_localLaw'` (DetAvgIBPFlow:209) |
| `RBM.Gauss.localLawUnifIcc_of_localLawFlow` | Gauss/GoodSetFlow:230 | 48219 | 0/0/0/0 | none |
| `RBM.Gauss.localLawUnifIcc_of_steps` | Gauss/GoodSetFlow:283 | 48310 | 0/0/0/0 | none |
| `RBM.Gauss.step2_gauss` | Gauss/Step2Close:519 | 70124 | 0/0/0; other jStar: `RBM.Step2.jStar` (+4 aux); h560: 9 | **YES (APrime theorems)**: 169 constants in 14 modules (§0.5) |
| `RBM.Gauss.steps12_gauss` | Gauss/Step2Close:541 | 70127 | as `step2_gauss` | as `step2_gauss` |
| `RBM.Gauss.steps12_gauss_of_grid` | Gauss/Steps12Gauss:102 | 63742 | 0/0/0/0 | YES (relocated defs only): `aprioriRhs`, `flowDelta`(+proof), `sigPM` |
| `RBM.Gauss.Grid.step2_gauss_of_gridPointwise'` | Gauss/GridBootstrap:309 | 63735 | 0/0/0/0 | YES (relocated defs only), same 4 |
| `RBM.Gauss.lkErr_one_eq_norm_trace` | Gauss/Eq45Flow:89 | 19958 | 0/0/0/0 | none |
| `RBM.Gauss.condExpDiag` | Gauss/FlucAvg:607 | 36825 | 0/0/0/0 | none |
| `RBM.Gauss.norm_condExpDiag_sub_le` | Gauss/IBP:1108 | 43293 | 0/0/0/0 | none |
| `RBM.Gauss.norm_condExpDiag_sub_le_offdiag` | Gauss/CondDom:775 | 43293 | 0/0/0/0 | none |
| `RBM.Gauss.norm_condExpDiag_flow_sub_le` | Gauss/CondExpMod:339 | 54699 | 0/0/0/0 | none |
| `RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow` | Gauss/CondExpMod:420 | 54708 | 0/0/0/0 | YES (relocated def only), via `flowNetEvent` |
| `RBM.Gauss.holIBP_of_inputs` / `holRow_of_inputs` / `holBlk_of_inputs` | Gauss/CondStableFlow:1627/1586/1604 | 54721/54721/54722 | 0/0/0/0 | YES (relocated def only) |
| `RBM.Gauss.HolConst` | Gauss/CondStableFlow:1550 | 16340 | 0/0/0/0 | none |
| `RBM.Gauss.flowNetEvent` | Gauss/Eq45FlowInputs:400 | 28814 | 0/0/0/0 | YES (relocated def only): `goodSetFlow` |
| `RBM.Gauss.abs_norm_green_flow_entry_sub_le` | Gauss/GoodSetFlow:88 | 30348 | 0/0/0/0 | none |
| `RBM.Gauss.goodSetFlow` | Gauss/APrimeGeneralMovingCarrierCore:72 | 17272 | 0/0/0/0 | itself |
| `RBM.Gauss.LocalLawUnifIcc` | Gauss/GoodSetFlow:114 | 36808 | 0/0/0/0 | none |
| `RBM.Gauss.highProb_goodSetFlow_of_localLaw` | Gauss/GoodSetFlow:184 | 52848 | 0/0/0/0 | YES (relocated def only) |
| `RBM.Gauss.no_joint_grid_scales` | Gauss/Eq45FlowGrid:57 | 16737 | 0/0/0/0 | none |
| `RBM.Gauss.eq45Flow_delta_hyps_consistent` | Gauss/Eq45Small:600 | 16723 | 0/0/0/0 | none |
| `RBM.APrimeFixedOneLoopGeneralDims.centered_block_trace_stochDom` | Gauss/APrimeFixedOneLoopGeneralDims:52 | 63090 | 0/0/0/0 | YES (APrime theorems), 19 flagged |
| `RBM.StochDom.precomp_param` | Flow/Hypotheses:108 | 18255 | 0/0/0/0 | none |
| `RBM.Gauss.unifDomIcc_of_stochDom_timeIcc` | Gauss/GoodSetFlow:214 | 18257 | 0/0/0/0 | none |
| `RBM.Gauss.stochDom_reindex_of_forall_seq` | Gauss/Step1Hyp:269 | 18610 | 0/0/0/0 | none |
| `RBM.Gauss.eventually_forall_measure_slice_le` | Gauss/Step1Hyp:237 | 18250 | 0/0/0/0 | none |
| `RBM.StochDom.of_forall_seq` | Flow/EnergyUniform:933 | 18625 | 0/0/0/0 | none |
| `RBM.Gauss.Grid.time` | Gauss/GridPath:51 | 5027 | 0/0/0/0 | none |
| `RBM.Step1.inv_W_le_inv_scale` | Hierarchy/Step1:302 | 18307 | 0/0/0/0 | none |
| `RBM.etaT_mul_ellHat_le` | Loop/KBound:1171 | 11368 | 0/0/0/0 | none |
| `RBM.Step2.eventually_R4_le_scale` | Hierarchy/Step2:1546 | 18460 | 0/0/0/0 | none |
| `RBM.Gauss.Dims.dim` | Gauss/Model:138 | 16340 | 0/0/0/0 | none |
| `RBM.ellHat` | Propagator/Decay:480 | 10856 | 0/0/0/0 | none |
| `RBM.LocalLawFlow` / `RBM.AprioriDecayFlow` / `RBM.SharpLoopFlow` | Flow/Hypotheses:357/364/373 | 19101/19748/19114 | 0/0/0/0 | none |
| `RBM.StepGlue.stochDom_flowXiLK` | Hierarchy/StepGlue:94 | 20547 | 0/0/0/0 | none |
| `RBM.StepGlue.norm_lkErr_one_le` | Hierarchy/StepGlue:125 | 20201 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_lkErr_one_le'` | Hierarchy/StepGlue:323 | 20797 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_S_one'` | Hierarchy/StepGlue:342 | 21059 | 0/0/0/0 | none |
| `RBM.StepGlue.AprioriDecayAll` | Hierarchy/StepGlue:386 | 19744 | 0/0/0/0 | none |
| `RBM.StepGlue.aprioriDecay_pm'` | Hierarchy/StepGlue:410 | 20001 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_xiLK_two_le` | Hierarchy/StepGlue:437 | 20621 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_hs2` | Hierarchy/StepGlue:453 | 20764 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_S_two` | Hierarchy/StepGlue:469 | 20821 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_S_le_two'` | Hierarchy/StepGlue:493 | 21081 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_hs1` | Hierarchy/StepGlue:507 | 20640 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_sharpLoop_glue'` | Hierarchy/StepGlue:535 | 52070 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_steps45_glue_W'` | Hierarchy/StepGlue:590 | 52141 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_steps45_glue'` | Hierarchy/StepGlue:627 | 52151 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_S_le_two` | Hierarchy/StepGlue:701 | 26775 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_sharpLoop_glue` | Hierarchy/StepGlue:710 | 52079 | 0/0/0/0 | none |
| `RBM.StepGlue.flow_steps45_glue` | Hierarchy/StepGlue:725 | 52159 | 0/0/0/0 | none |
| `RBM.Step3.exists_norm_Kval_le` | Hierarchy/Step3:906 | 51677 | 0/0/0/0 | none |
| `RBM.Step3.flow_xiL_le_of` | Hierarchy/Step3:918 | 20518 | 0/0/0/0 | none |
| `RBM.Step2.kval_stochDom` | Hierarchy/Step2:1582 | 19455 | 0/0/0/0 | YES (relocated def only): `sigPM` |
| `RBM.Step2.localLaw_of_scale_facts` | Hierarchy/Step2:1610 | 51761 | 0/0/0/0 | YES (relocated def only): `sigPM` |
| `RBM.ChargeReduce.AprioriDecayPP` | Hierarchy/ChargeReduce:215 | 19743 | 0/0/0/0 | none |
| `RBM.ChargeReduce.aprioriDecayAll_of_pp'` / `_of_pp` | Hierarchy/ChargeReduce:229/255 | 29571/33265 | 0/0/0/0 | none |
| `RBM.Gauss.lemma514_of_seq` | Gauss/Lemma514Moment:408 | 20732 | 0/0/0/0 | none |
| `RBM.Gauss.Lemma514Premises` | Gauss/Lemma514Moment:388 | 19752 | 0/0/0/0 | none |
| `RBM.Gauss.stochDom_flowXiLK_of_seq` | Gauss/Lemma514Moment:343 | 20722 | 0/0/0/0 | none |
| `RBM.Gauss.hHol_flow` | Gauss/Lemma514Holder:721 | 53365 | 0/0/0/0 | none |
| `RBM.Gauss.hKb_flow` | Gauss/Lemma514Holder:864 | 51684 | 0/0/0/0 | none |
| `RBM.Gauss.exists_highProb_normX` | Gauss/Lemma514Holder:1049 | 51773 | 0/0/0/0 | none |
| `RBM.Gauss.traceMomentBound_gauss` | Gauss/TraceMoment:935 | 51015 | 0/0/0/0 | none |
| `RBM.Gauss.card_loopData_le` | Gauss/Lemma514Moment:188 | 18573 | 0/0/0/0 | none |
| `RBM.Gauss.norm_Psum_lkT_mul_vartheta_le` | Gauss/Lemma514QRoute:182 | 46910 | 0/0/0/0 | none |
| `RBM.SumZeroDyn.WardP` | Hierarchy/SumZeroDyn:1647 | 19757 | 0/0/0/0 | none |
| `RBM.Gauss.lemma514_of_hHol_flow` | Gauss/Lemma514Holder:948 | 59164 | **MD: 6** | none |
| `RBM.Gauss.lemma514_forall_of_hHol_flow` | Gauss/Lemma514Holder:983 | 59166 | **MD: 6** | none |
| `RBM.Gauss.flow_sharpLmK_of_hHol_flow` | Gauss/Lemma514Holder:1008 | 59441 | **MD: 6** | none |
| `RBM.Gauss.lemma514_of_momentDuhamel` | Gauss/Lemma514Moment:535 | 34978 | **MD: 6** | none |
| `RBM.Step3.S` / `Lemma514` / `Hyp` | Hierarchy/Step3:376/386/398 | 18249/18246/18250 | 0/0/0/0 | none (import closure 0) |
| `RBM.Step3.xiLK_two_le` / `S_of_S` / `S_all` / `xiLK_le` / `xiL_le_one` | Hierarchy/Step3:473/502/594/625/656 | 18587/19353/19358/19364/19368 | 0/0/0/0 | none |
| `RBM.Step3.flowXiLK`; `RBM.Sample.lkMax`; `RBM.Sample.xiLK` | Hierarchy/Step3:863/781/785 | 19743/19736/19741 | 0/0/0/0 | none |
| `RBM.loopMax` | Loop/Split:350 | 13050 | 0/0/0/0 | none |
| `RBM.LoopData` | Flow/Hypotheses:135 | 51 | 0/0/0/0 | none (axioms `[]`) |
| `RBM.Step3.flow_sharpLoop_of` / `flow_sharpLoop` | Hierarchy/Step3FlowSharp:33/65 | 52025/52026 | 0/0/0/0 | none |
| `RBM.Step45.xiLK_le_one` / `xiLK_le_one_of_hyp` | Hierarchy/Step45:183/242 | 19212/19395 | 0/0/0/0 | none |
| `RBM.Step45.flow_sharpLmK` / `flow_steps45` / `flow_steps45_W` | Hierarchy/Step45:306/477/669 | 52052/52101/52099 | 0/0/0/0 | none |
| `RBM.Step2PP.xiLK_two_le` / `flow_S_two_of` / `flow_S_le_two_of'` | Hierarchy/Step2PP:345/408/426 | 20577/20199/21063 | 0/0/0/0 | none |
| `RBM.Step2PP.flow_S_le_two_of` / `flow_hs2_of` / `flow_sharpLoop_glue_of` / `flow_steps45_glue_of` | Hierarchy/Step2PP:914/925/942/960 | 26761/26597/52076/52165 | 0/0/0/0 | none |

Discrepancy with the audit: the audit reported 4599 constants and 0 hits for `detAvgIBP_stochDom_of_localLaw_complete`. The shortest chain printed in §0.5 (the declaration → `detAvgIBP_stochDom_of_localLaw'` → `goodSetFlow`) shows that `goodSetFlow` is used by a proof term one step down. Likewise the T1524 audit reported a 4966-constant closure for `step2_gauss`, against 70124 here. Both earlier scripts apparently did not follow proof terms fully.

### 0.5 Shortest chains (verbatim `#aprimepath` output; Path.lean / Path3.lean)

```
== RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete
  shortest chain to an APrime-module constant:
    RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete (RBM1D.Gauss.DetAvgIBPFlow)
    -> RBM.Gauss.detAvgIBP_stochDom_of_localLaw' (RBM1D.Gauss.DetAvgIBPFlow)
    -> RBM.Gauss.goodSetFlow (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)
  frontier APrime-module constants (referenced from non-APrime constants): [RBM.Gauss.goodSetFlow (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
== RBM.Gauss.eq45Flow_of_goodSetFlow_highProb
  shortest chain to an APrime-module constant:
    RBM.Gauss.eq45Flow_of_goodSetFlow_highProb (RBM1D.Gauss.Eq45Small)
    -> RBM.Gauss.goodSetFlow (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)
== RBM.Step2.kval_stochDom
  shortest chain to an APrime-module constant:
    RBM.Step2.kval_stochDom (RBM1D.Hierarchy.Step2)
    -> RBM.Step2.sigPM (RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore)
== RBM.Gauss.steps12_gauss_of_grid
  shortest chain to an APrime-module constant:
    RBM.Gauss.steps12_gauss_of_grid (RBM1D.Gauss.Steps12Gauss)
    -> RBM.Step1.apriori (RBM1D.Hierarchy.Step1)
    -> RBM.Step1.aprioriRhs (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)
```
Path3.lean runs the same search while *ignoring* the two relocated-definition core modules (`APrimeSmoothPrefixCanonicalCore`, `APrimeGeneralMovingCarrierCore`):
```
== RBM.Gauss.step2_gauss
  shortest chain to an APrime-module constant outside the two relocated-definition core modules:
    RBM.Gauss.step2_gauss (RBM1D.Gauss.Step2Close)
    -> RBM.Gauss.Grid.gridPointwise'_gauss (RBM1D.Gauss.Step2Close)
    -> RBM.Gauss.Grid.goodSet (RBM1D.Gauss.GridGoodSet)
    -> RBM.Gauss.Grid.qvSet (RBM1D.Gauss.GridGoodSet)
    -> RBM.APrimeQVEndpoint.diagShape' (RBM1D.Gauss.APrimeNearRem)
  frontier APrime-module constants (referenced from non-APrime constants): [RBM.APrimeAllTimeOneLoopGeneralDims.control._proof_1 (RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims),
 [... 31 further entries elided; they include ...]
 RBM.APrimeAllTimeOneLoopGeneralDims.highProb_centeredEvent (RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims),
 RBM.APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale (RBM1D.Gauss.APrimeRawSourcesGeneralDims),
 RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow (RBM1D.Gauss.APrimeJG),
 RBM.APrimeFullQV.early_raw_full (RBM1D.Gauss.APrimeFullQV),
 RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow (RBM1D.Gauss.APrimeGoodSetFlowGeneralDims),
 RBM.APrimeAllTimeOneLoopGeneralDims.qExt (RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims)]
== RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete: no APrime-module constant reachable
== RBM.Gauss.steps12_gauss_of_grid: no APrime-module constant reachable
```
`#compact` output for `step2_gauss` (verbatim, module list truncated at 12 by the script):
```
RBM.Gauss.step2_gauss @ RBM1D.Gauss.Step2Close:519 | closure 70124 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 5 [RBM.Step2.jStar,
 RBM.Step2.jStar._proof_1,
 RBM.Step2.jStar._proof_2,
 RBM.Step2.jStar.congr_simp,
 RBM.Step2.jStar.eq_1] | 560/h560: 9 [RBM.Lemma57.case2_pointwise,
 RBM.Lemma57.eG_far_le,
 RBM.Lemma57.sum_far_le,
 RBM.Gauss.Grid.drift_point_le',
 RBM.Gauss.Grid.eG_le',
 RBM.Gauss.Grid.eG_le_reduced'] | APrime-module constants: 169 in 14 modules [RBM1D.Gauss.APrimeGoodSetFlowGeneralDims,
 RBM1D.Gauss.APrimeRawSourcesGeneralDims,
 RBM1D.Gauss.APrimeGeneralMovingCarrierCore,
 RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims,
 RBM1D.Gauss.APrimeQVEndpoint,
 RBM1D.Gauss.APrimeFixedOneLoopGeneralDims,
 RBM1D.Gauss.APrimeCenteredModulusGeneralDims,
 RBM1D.Gauss.APrimeDuhamel,
 RBM1D.Gauss.APrimeTwoChargeOneLoop,
 RBM1D.Gauss.APrimeNearRem,
 RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims,
 RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore]
RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete @ RBM1D.Gauss.DetAvgIBPFlow:274 | closure 57540 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 0 [] | 560/h560: 0 [] | APrime-module constants: 1 in 1 modules [RBM1D.Gauss.APrimeGeneralMovingCarrierCore]
```
`RBM.Step2.jStar` is defined at `APrimeSmoothPrefixCanonicalCore.lean:79` (`noncomputable def jStar (L : ℕ) [NeZero L] (f : LoopArg L 2 → ℝ)`). It is not the ticket's `EarlyQVRateEv.jStar` (`EarlyQVRateEv.lean:146`). No declaration in this report depends on `EarlyQVRateEv.jStar`.

---

## (I1) Producers of (4.5)

Paper (p.48, Lemma 4.1): (4.5) is `max_a |⟨(G_t − m)E_a⟩| ≺ max_{a,b} L_{t,(+,−),(a,b)}`, under `‖G_t − m‖_max ≺ W^{−c}` (4.4).

Column meanings:
- "Kind" is per-sample deterministic, `StochDom` or `HighProb`, for the hypotheses and the conclusion.
- "Time" is fixed-time, or uniform in `u` (a statement whose index set contains `TimeIcc s t N`, with the union over `u` inside the probability).
- "Dims" is arbitrary `Gauss.Dims`, `exampleGrow` or first cell, or not Dims-typed.
- "Dep." refers to §0.4.

| # | Declaration, file:line | Kind | Time | Dims | Dep. | Status |
|---|---|---|---|---|---|---|
| 1 | `RBM.norm_trace_green_sub_mul_Eblk_le`, Green/EntryBound:1338 | per-sample deterministic: `‖tr((G−m)E_a)‖ ≤ B' + Kstab κ·(A+B)` from entrywise bounds `hIBP, hFA, hFA'` on one matrix `G` | fixed (one real `t`) | not Dims-typed (raw `L W`, `3 ≤ L`) | clean | deterministic kernel of (4.5); inputs open |
| 2 | `RBM.avg_bound_stochDom`, Green/EntryBound:1628 | StochDom → StochDom, random control `Lmax` | fixed `t` | raw `L W : ℕ → ℕ` | clean | fixed-time (4.5); three StochDom inputs `hIBP/hFArow/hFAblk` open |
| 3 | `RBM.StepGlue.Eq45Flow`, StepGlue:398 (def) | bound transfer: ∀Φ ≥ 0, `‖L_{u,(+,−)}‖ ≺ Φ_u` ⟹ `|L−K|_{u,1} ≺ Φ_u` (StochDom → StochDom) | uniform in `u` | any `Sample B` | clean | a `Prop`, consumed by `flow_hs1` (§I2) |
| 4 | `RBM.Gauss.eq45Flow_of_inputs` Eq45Flow:227; `eq45Flow_gauss` :246 | hyps `IBPFlow/FlucRowFlow/FlucBlkFlow` (time-indexed StochDom); concl `Eq45Flow` | uniform | any `Sample` / arbitrary `d` | clean | the three time-uniform inputs are hypotheses, not discharged here |
| 5 | `RBM.Gauss.eq45Flow_of_unifDom`, Eq45FlowInputs:628 | hyps: `hΩ : HighProb (goodSetFlow d E s t δ)`; `hfixIBP/hfixRow/hfixBlk : UnifDomIcc` (Lmax control); `hHol*` deterministic on `flowNetEvent`; `hfine`; concl StochDom | uniform | arbitrary `d` | **APrime YES** (`goodSetFlow`) | `hHol*` are dischargeable (F4). `hfix*` remain open. `hfine` gives `δ_N ≤ (16N⁶)⁻¹` (η ≤ 1), and then `hΩ` would need `‖G_u−m‖_max ≤ δ_N` for all `u` w.h.p. The Gaussian model does not satisfy this. **Not compiled**; the compiled neighbour is `no_joint_grid_scales` (Eq45FlowGrid:57) for the margin form |
| 6 | `RBM.Gauss.eq45Flow_of_goodSetFlow_highProb`, Eq45Small:507 | as 5, plus `hll : LocalLawUnifIcc d E s t (2δ)` and `hWδ : ∀ N, W⁻¹ ≤ 4(2δ_N)²` | uniform | arbitrary `d` | **APrime YES** (`goodSetFlow`) | **VACUOUS**: `(hfine, hWδ)` is unsatisfiable, compiled as `t1525_hfine_hWδ_inconsistent` (A.6). The repo witness `eq45Flow_delta_hyps_consistent` (Eq45Small:600) omits `hWδ` |
| 7 | `RBM.Gauss.eq45Flow_of_localLaw_gain_budget`, MinorDiffCond:1229 | as 5, with `hg : FlucGainUpTo' …` and `hΨW'` (on `Ψ`) | uniform | arbitrary `d` | **APrime YES** (`goodSetFlow`) | carries the same `(hfine, hΩ)` pair as 5. `Ψ` and `δ` are not syntactically linked, so no negative was compiled |
| 8 | `RBM.Gauss.eq45Flow_of_goodSetFlow_budget`, MinorDiffCond:1299 | as 6 (`hWδ`, `hfine`) | uniform | arbitrary `d` | **APrime YES** (`goodSetFlow`) | **VACUOUS**: same `(hfine, hWδ)` pair, same compiled negative |
| 9 | `RBM.Gauss.Lemma514OneLoopSharp.stochDom_flowXiLK_one_of_gaussian_hypotheses`, Lemma514OneLoopSharp:66 | StochDom, `Ξ_1 ≺ 1` | uniform | **`Dims.exampleGrow` only** (`private noncomputable abbrev d : Dims := Dims.exampleGrow`, line 24) | **APrime YES (theorems)**: imports `RBM1D.Gauss.APrimeFreeLossGaussianStep2`; 1687 APrime constants | special case, not general |
| 10 | **`RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete`, DetAvgIBPFlow:274** | StochDom: `‖tr((G_{u_N}−m)E_b)‖ ≺ Ψ_N·Ψ_N` over `b : ZMod (d.L N)`; hyps: one StochDom-type input `hll : LocalLawUnifIcc d E u u Ψ`, the rest deterministic | **fixed time per sequence** (`u : ℕ → ℝ`, window `u..u`); no time net, no Hölder slot | arbitrary `d` | APrime YES (relocated def `goodSetFlow` only; no APrime theorem, §0.5) | **recommended**, see below |
| 11 | `RBM.APrimeFixedOneLoopGeneralDims.centered_block_trace_stochDom`, :52 | StochDom, ≺ `2·selectorQ` | fixed selector `u` | arbitrary `d` | APrime YES (theorems) | an existing composition of #10 with an APrime singleton local law; takes `hStep : Step1.Hyp`; not reusable under the APrime restriction |

G1b outputs feeding (I1):

| Declaration, file:line | Kind | Time | Dims | Dep. |
|---|---|---|---|---|
| `RBM.Gauss.step2_gauss`, Step2Close:519 (merged, `ae718fe`) | StochDom (conclusion: `llErr ≺ scale^{-1/2}` over `TimeIcc s t N × Idx²`, i.e. `LocalLawFlow (sample d) E s t` verbatim, ∧ (2.76) for `pmLoop`) | uniform | arbitrary `d` | APrime YES (theorems), F2 |
| `RBM.Gauss.steps12_gauss`, Step2Close:541 | `Steps12 (sample d) E s t` | uniform | arbitrary `d` | as `step2_gauss` |
| `RBM.Gauss.steps12_gauss_of_grid`, Steps12Gauss:102 (T1521) | same shape | uniform | arbitrary `d` | relocated defs only |
| `RBM.Gauss.localLawUnifIcc_of_localLawFlow`, GoodSetFlow:230 | StochDom → `UnifDomIcc`; `hmaj` deterministic eventual | uniform → fixed-time-uniform | arbitrary `d` | clean |

### condExpDiag: re-run grep and correction of r0 (fix 3, F4)

The grep output is quoted verbatim in A.3. Classification of its hits:

- **CondDom / IBP / DetIBPWeighted hits are fixed-time remainder bounds, not time moduli.**
  - `norm_condExpDiag_sub_le` (IBP:1108) has binders `(ht0 : 0 ≤ t) (ht : t < 1) (i) (ω)`. It bounds `‖condExpDiag d N t … i ω − t·m²·Σ_k S_ik(G_kk − m)‖ ≤ A` at **one** time `t`.
  - `norm_condExpDiag_sub_le_offdiag` (CondDom:775) has the same single `t`, with the weighted remainder `A + S_ii·Adiag`.
  - `norm_condExpDiag_sub_le_two_phi` (DetIBPWeighted:24) is the same kind of bound.
  - None of them compares two times `u, v`.
- **CondExpMod / CondStableFlow / DetFlucAvgTimeNet hits are genuine time moduli.**
  - `norm_condExpDiag_flow_sub_le` (CondExpMod:339) bounds `‖condExpDiag d N u … k ω − condExpDiag d N v … k ω‖ ≤ η_u⁻¹η_v⁻¹(|√u−√v|(‖X‖+2‖X‖²+5/2) + |u−v|)`. It is per-sample and deterministic, for a pair of times, with a random constant.
  - `norm_condExpDiag_flow_sub_le_rpow` (CondExpMod:420) gives `≤ N^K |u−v|^{1/2}` on `flowNetEvent`, under `hK` (η lower bound).
  - The three slots are assembled by `holIBP_of_inputs` / `holRow_of_inputs` / `holBlk_of_inputs` (CondStableFlow:1627/1586/1604) under `hKc` and `HolConst E t Kc K` (CondStableFlow:1550: `N^Kc + η_t^{-2}(N+1) + (η_t^{-1}+1) ≤ N^K` eventually).
  - r0's "missing piece: no condExpDiag modulus" is **withdrawn**.
- Consequence for the flow producers (rows 5–8): the Hölder slots are closed, but rows 6 and 8 are vacuous and rows 5 and 7 carry `(hfine, hΩ)`. The flow route to `Eq45Flow` therefore does not close for the Gaussian model on a non-degenerate window.

### Recommended producer and its missing pieces (fix 7)

**Recommendation: `RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete`** (DetAvgIBPFlow:274), used at fixed grid times.

Full hypothesis list (verbatim binders):
- `(d : Dims) {E κ : ℝ} {u Ψ : ℕ → ℝ} {a K : ℝ}`;
- `(hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)`;
- `(hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)`;
- `(hη : ∀ᶠ N, (N:ℝ)^(-K) ≤ etaT E (u N))`;
- `(hΨlo : ∀ᶠ N, (d.W N:ℝ)^(-(1:ℝ)/2) ≤ Ψ N)`;
- `(hΨhi : ∀ᶠ N, Ψ N ≤ (N:ℝ)^(-a))`;
- `(hll : LocalLawUnifIcc d E u u Ψ)`.

Conclusion: `StochDom (P d) (fun N (b : ZMod (d.L N)) ω => ‖trace((green (Hflow d N (u N) ω) (zt E (u N)) - mE E • 1) * Eblk (d.L N) (d.W N) b)‖) (fun N _ _ => Ψ N * Ψ N)`.

**What this producer yields, compared with the paper.**
- It gives (4.5)∘(2.76) at the fixed time `u_N`: `max_a |⟨(G_{u_N} − m)E_a⟩| ≺ Ψ_N² = (Wℓ_{u_N}η_{u_N})⁻¹` when `Ψ_N = scale(u_N)^{-1/2}`. In paper terms, this is (4.5) with its right side `max L_{(+,−)}` already bounded by `(Wℓη)⁻¹`, as (2.76) and the K bound (2.59) would give.
- It is **not** the bound-transfer form `StepGlue.Eq45Flow` (∀Φ, `L_{(+,−)} ≺ Φ ⟹ |L−K|_1 ≺ Φ`). So it cannot be plugged into `StepGlue.flow_hs1`.
- It needs no 2-loop input at all.
- If M1 is ticketed, this shape difference should get a `docs/paper-deltas.md` entry. That file is outside this ticket's writable scope; see open issue O3.

**Missing statement M1: Ξ_1 at a grid point, both charges.** Proposed target:
```lean
theorem xiLK_one_le_one_at_seq (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (u : ℕ → ℝ) (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    StochDom (P d) (fun N (_ : Unit) ω => (sample d).xiLK E N (u N) ω 1) (fun _ _ _ => (1 : ℝ))
```
There is also a grid form. It takes `K : ℕ → ℕ`, `hKcard : ∀ᶠ N, ((K N + 1 : ℕ) : ℝ) ≤ N^C` and `θ : ∀ N, Fin (K N + 1) → TimeIcc s t N`, and concludes `StochDom (P d) (fun N k ω => (sample d).xiLK E N (θ N k) ω 1) 1`.

The hypotheses are exactly `step2_gauss`'s, plus `hu`. They are therefore simultaneously satisfiable wherever `step2_gauss`'s are (T1524 witness), for example with `u := t`, and non-degenerately when `s < t`.

Proof steps, each named:

- **S1. Restriction from `LocalLawFlow (sample d) E s t` to the singleton window `u..u`.**
  - `(step2_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg).1` is `LocalLawFlow (sample d) E s t` verbatim (compare the conclusion at Step2Close:524–527 with the definition at Flow/Hypotheses:357).
  - Apply `RBM.StochDom.precomp_param` (Flow/Hypotheses:108) along `ι_N : TimeIcc u u N × Idx² → TimeIcc s t N × Idx²`, `ι(v, ij) = (⟨v, (hu N).1.trans v.2.1, v.2.2.trans (hu N).2⟩, ij)`. This gives `LocalLawFlow (sample d) E u u`.
  - Then apply `RBM.Gauss.localLawUnifIcc_of_localLawFlow` (GoodSetFlow:230) with `s := u, t := u` and `Ψ_N := ((band d).scale E N (u N))⁻¹ ^ (1/2)`. Its `hmaj` holds with `le_rfl`, because `v ∈ Icc (u N) (u N)` forces `v = u N`.
  - No lemma performs this restriction under a name. The grep found none: `grep -rn "LocalLawFlow .* u u"` has no hit (A.5). The only singleton converter, `localLawUnifIcc_of_selector_llErr`, lives in an APrime file and is specialised to `selectorPsi`, but it is the proof template (`precomp_param` + `unifDomIcc_of_stochDom_timeIcc`).
- **S2. Discharge of `hΨlo`, `hΨhi`, `hη` from (2.72).**
  - `hΨlo`, meaning `scale ≤ W`, i.e. `ℓη ≤ 1`: `RBM.Step1.inv_W_le_inv_scale` (Step1:302) gives `W⁻¹ ≤ scale(u_N)⁻¹` for `0 ≤ u_N < 1`. It is proved from `RBM.etaT_mul_ellHat_le` (KBound:1171, `etaT E t * ellHat L t ≤ 1`). Then apply `Real.rpow_le_rpow` at exponent `1/2`. This holds for every `N`.
  - `hΨhi` with `a := c/2`: `RBM.Step2.eventually_R4_le_scale hE hst ht1 hc0 hreg` (Step2:1546) gives `∀ᶠ N, ∀ v : TimeIcc s t N, … ∧ N^c ≤ scale v`. At `v = ⟨u N, hu N⟩` this gives `scale(u_N)^{-1/2} ≤ N^{-c/2}`.
  - `hη` with `K := 1`: from `N^c ≤ scale(u_N) = W·ℓ·η` (`Band.scale`, Flow/Hypotheses:191), `ℓ ≤ L` (`RBM.ellHat` is `min(…, L)`, Propagator/Decay:480) and `W·L ≤ N` eventually (`Dims.dim`, Model:138). Together, `η(u_N) ≥ N^{c−1} ≥ N^{-1}`.
  - `hu0` and `hu1` follow from `hs0`, `hu` and `ht1`. The constants `κ` and `hK : 0 ≤ 1` are given.
- **S3.** Apply the producer: `‖tr((G−m)E_b)‖ ≺ Ψ_N² = scale(u_N)⁻¹` over `b`.
- **S4. Both charges and the sup.**
  - `RBM.Gauss.lkErr_one_eq_norm_trace` (Eq45Flow:89) gives, for every `v : LoopData (L N) 1`, whatever its charge `σ = v.1 0 ∈ {+,−}`: `lkErr = ‖tr((G−m)E_{v.2 0})‖`. For `σ = −` this goes through `Gsig_conjTranspose`, so the case is covered.
  - `precomp_param` along `v ↦ v.2 0` moves this to `LoopData 1`.
  - The sup `lkMax = ⨆ v` is handled by `StochDom.of_subset_union`, exactly as in `RBM.StepGlue.stochDom_flowXiLK` (StepGlue:94).
  - Multiplying by `scale` gives `scale·scale⁻¹ = 1`.
- **S5. Grid uniformity.**
  - Apply `RBM.Gauss.stochDom_reindex_of_forall_seq` (Step1Hyp:269) with `V N := Unit`, `θ` := the grid times (`RBM.Gauss.Grid.time`, GridPath:51, packaged into `TimeIcc`) and `hcard : #Fin (K N + 1) ≤ N^C`.
  - Internally it applies `eventually_forall_measure_slice_le` (Step1Hyp:237). That is the worst-grid-point sequence: the per-sequence StochDom is applied to the sequence that picks, at each `N`, the worst point.
  - A union bound (`measure_iUnion_fintype_le`) over the `≤ N^C` grid points then costs `N^C·N^{-(D+C)}`.
  - The generic version is `RBM.StochDom.of_forall_seq` (EnergyUniform:933).

**Estimate for M1: 1 ticket.** It is a mechanical composition with no new inequality, and one ticket covers σ = + and σ = −.

**Dependency caveat (open issue O1).**
- M1's own new code would add no APrime constant.
- The producer brings in `goodSetFlow`, a relocated definition.
- The input `step2_gauss` brings in the APrime theorem modules listed in F2.

---

## (I2) The S(1,l) chain: Ξ^{(L−K)}_{u,1} ≺ 1

Target (Step3 normalization): `X 1 = Step3.flowXiLK X E s t 1`, i.e. `Sample.xiLK E N u ω 1 = lkMax·scale`, bounded by `1 ≤ N^ε`, for both σ = (+) and (−).

| # | Declaration, file:line | Statement (from the signature) | Kind | Time | Dims | Dep. |
|---|---|---|---|---|---|---|
| 1 | `RBM.StepGlue.norm_lkErr_one_le`, StepGlue:125 | for `v : LoopData (B.L N) 1` and `c`: `(∀ ij, X.llErr E N u ω ij ≤ c) → X.lkErr E N u ω v.idx ≤ c`. **Entrywise `llErr ≤ c` ⟹ 1-loop `lkErr ≤ c`**, both charges (σ = − via `Gsig_conjTranspose`). It is *not* the block-trace identity; that identity is `RBM.Gauss.lkErr_one_eq_norm_trace` (Eq45Flow:89) | per-sample deterministic | fixed `(N,u,ω)` | any `Sample B` | clean |
| 2 | `RBM.StepGlue.flow_lkErr_one_le'`, StepGlue:323 | `LocalLawFlow X E s t → StochDom (TimeIcc × LoopData 1 ↦ lkErr) ((scale)⁻¹^{1/2})` | StochDom | uniform | any | clean |
| 3 | `RBM.StepGlue.flow_S_one'`, StepGlue:342 | `S(1,l)` for every `l`: `Ξ_1 ≺ Ψ(1,l)` (via `Ξ_1 ≺ scale^{1/2} ≤ flowAs^{1/2}`), hyps `hE hs0 hst ht1 hc hll` | StochDom | uniform | any | clean |
| 4 | `RBM.StepGlue.stochDom_flowXiLK`, StepGlue:94 | loopwise `lkErr ≺ f_u` over `TimeIcc × LoopData m` ⟹ `Ξ_m ≺ f_u·scale^m` | StochDom → StochDom | uniform | any | clean |
| 5 | **`RBM.StepGlue.flow_hs1`, StepGlue:507** | `(hE : |E| < 2) (hs0) (ht1) (h45 : Eq45Flow X E s t) (h277 : StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => ‖X.Lval E N p.1 ω p.2.idx‖) (fun N p _ => (B.scale E N p.1)⁻¹ ^ (2 - 1))) : StochDom B.P (Step3.flowXiLK X E s t 1) fun _ _ _ => 1` | StochDom (h277); bound transfer (h45); concl StochDom | **uniform in u** (TimeIcc in the index set) | any `Sample B` (general `Band`) | clean (20640 constants, 0 flags, Ax std) |
| 6 | `RBM.StepGlue.aprioriDecay_pm'`, StepGlue:410 | `AprioriDecayFlow X E s t → StochDom (pm lkErr) ((η_s/η_u)⁴ scale^{-2})` | StochDom | uniform | any | clean |
| 7 | `RBM.Step3.exists_norm_Kval_le`, Step3:906 | `∃ C ≥ 0, ∀ N (u : TimeIcc) (v : LoopData n), ‖Kval‖ ≤ C·scale^{-(n-1)}` (2.59), **all charges** | deterministic | all `u ∈ [s,t]` | any `Band` | clean |
| 8 | `RBM.Step2.kval_stochDom`, Step2:1582 | the deterministic K bound at `n = 2` ⟹ `‖K_{(+,−)}‖ ≺ scale⁻¹` | StochDom (deterministic) | uniform | any | relocated def `sigPM` |
| 9 | `RBM.Step2.localLaw_of_scale_facts`, Step2:1610 | its proof contains, as the private `have hL` (Step2.lean:1663–1672), `‖L_{u,(+,−)}‖ ≺ scale⁻¹` from (2.76), the K bound and `hfacts`; this is not a public declaration | StochDom | uniform | any | relocated def `sigPM` |
| 10 | `RBM.Gauss.Lemma514OneLoopSharp.stochDom_flowXiLK_one_of_gaussian_hypotheses`, :66 | sharp `Ξ_1 ≺ 1` | StochDom | uniform | `exampleGrow` only | APrime theorems |

**Answer.** r0's answer is revised.

- **A general-`Band` Lean statement does exist:** `RBM.StepGlue.flow_hs1`. It gives `Ξ_1 ≺ 1` uniformly on `[s,t]` from (4.5) in the `Eq45Flow` form plus a 2-loop bound. Both charges are covered, since `flowXiLK 1` sups over `LoopData 1`, whose first factor is the charge.
- **Its 2-loop premise `h277` ranges over all four charges.** `LoopData (B.L N) 2 = (Fin 2 → Bool) × (Fin 2 → ZMod L)`, so it includes the constant charges (+,+) and (−,−). It bounds `‖L‖`, not `L−K`, at the (2.77) scale `scale^{-1}`.
- **The proof uses only the (+,−) part.** Lines 515–521 build `hpm` (StochDom of `‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖` over `TimeIcc × ZMod L × ZMod L`) as `h277.precomp_param` along `Step45.pmData`. Lines 522–527 use only `hpm`, `h45` and `stochDom_flowXiLK`. So the all-charge premise is stronger than the paper needs; the paper uses (2.76) for (+,−) only (p.72).
- **Smallest missing statements for this route.**
  - **M2a `flow_hs1_pm`:** `flow_hs1` with `h277` replaced by the (+,−)-only premise `hpm`, shaped exactly as at StepGlue:515–518. The proof is StepGlue:522–527 verbatim. It weakens the hypotheses of a primed successor and leaves the frozen `flow_hs1` unchanged.
  - **M2b `stochDom_norm_Lval_pm_of_aprioriDecay`:** `AprioriDecayFlow X E s t` + `hfacts` (`(η_s/η_u)⁴ ≤ scale u` eventually, from `Step2.eventually_R4_le_scale`) + the K bound (`Step3.exists_norm_Kval_le`, via `Step2.kval_stochDom`) ⟹ `‖L_{u,(+,−)}‖ ≺ scale⁻¹`. This is the `hL` block of `localLaw_of_scale_facts`, made public.
  - Estimate: 1 small ticket for M2a and M2b together.
  - With them, `Ξ_1 ≺ 1` on `[s,t]` needs `Eq45Flow` + `step2_gauss.2`, and **no (+,+)/(−,−) input**.
- **But `Eq45Flow` has no non-vacuous closed producer for the Gaussian model** (§I1, rows 4–8). So the flow route stays blocked at `Eq45Flow`, not at the charge issue.
- **For goodSet514's Ξ_1 set (supervisor 1a(i)) the recommended route is M1 (§I1).** It gives `Ξ_1(u_N) ≺ 1` at every grid point, uniformly over polynomially many grid points (S5), for both charges, from Step 2's local law alone. It needs neither `Eq45Flow` nor any 2-loop premise, and it works for general `Dims`. Its dependency caveat is O1.

---

## (I3) The §10b reuse checks

| Declaration, file:line | Kind | Time | Dims | Dep. | Reusable as is? |
|---|---|---|---|---|---|
| `RBM.Gauss.lemma514_of_seq`, Lemma514Moment:408 | concl `Step3.Lemma514`; hyps listed below | see below; no hypothesis is a stopped-path statement | any `Band` / `Sample` | clean | **yes**; `hHol` and `hseq` remain to be supplied |
| `RBM.Gauss.Lemma514Premises`, Lemma514Moment:388 (def) | conjunction of 4 StochDoms | **uniform in u** (all over `TimeIcc s t`) | any | clean | appears only as an antecedent inside `hseq` (assumed, not discharged) |
| `RBM.Gauss.stochDom_flowXiLK_of_seq`, Lemma514Moment:343 | the engine `lemma514_of_seq` calls | per-sequence fixed-time StochDom + event Hölder ⟹ uniform StochDom | any | clean | yes |
| `RBM.Gauss.hHol_flow`, Lemma514Holder:721 | per-sample deterministic on `Ξ N`: `∀ᶠ N, ∀ ω ∈ Ξ N, ∀ q, ∀ u v ∈ [s,t], |scale_u^m‖lkT_u‖ − scale_v^m‖lkT_v‖| ≤ N^{c(3m+4)+1}|u−v|^{1/2}`; hyps `hreg` (η_t⁻¹ ≤ N^c), `hXΞ`, `hKb` | a modulus of continuity for pairs `(u,v)` of **one realized path**; not a stopped-path or joint-law statement | arbitrary `d` | clean | yes |
| `RBM.Gauss.hKb_flow`, Lemma514Holder:864 | deterministic (no ω): `‖Kval E N w J‖ ≤ N^{cm+1}` for `w ∈ [0,t_N]`, `2 ≤ |J| ≤ m` | uniform in `w` (deterministic) | any `Band Ωb` | clean | yes |
| `RBM.Gauss.exists_highProb_normX`, Lemma514Holder:1049 | `∃ Ξ, HighProb Ξ ∧ ∀ᶠ N, ∀ ω ∈ Ξ N, ‖X‖+1 ≤ N^c`; hyp `TraceMomentBound d` | no time | arbitrary `d` | clean | yes; `TraceMomentBound d` is discharged for every `d` by `RBM.Gauss.traceMomentBound_gauss` (TraceMoment:935, clean) |
| `RBM.Gauss.card_loopData_le`, Lemma514Moment:188 | deterministic: `∀ᶠ N, #LoopData (B.L N) m ≤ N^{m+1}` | none | any `Band` | clean | yes |
| `RBM.Gauss.norm_Psum_lkT_mul_vartheta_le`, Lemma514QRoute:182 | per-sample deterministic at one `(N, v, ω)`; good-event premises `hX : X.xiLK E N v ω (n+1) ≤ K·φ`, `hdec : ∀ ρ b, lkErr(…)·farInd(…) ≤ δ`, plus `hW : SumZeroDyn.WardP X E n` | **fixed time** (a real `v`, a bare `ω`) | any `Sample` | clean | yes. `WardP` (SumZeroDyn:1647) is a deterministic identity quantified `∀ N u ω`; it is a hypothesis to supply |
| `RBM.Gauss.lemma514_of_momentDuhamel` Lemma514Moment:535; `lemma514_of_hHol_flow` Lemma514Holder:948; `lemma514_forall_of_hHol_flow` :983; `flow_sharpLmK_of_hHol_flow` :1008 | take `MomentDuhamel.Hyp` | — | — | **MD: 6 constants each** | **no, forbidden** (supervisor §3(i)) |

**`lemma514_of_seq`: full hypothesis list, in order** (Lemma514Moment:408–424):
1. `hE : |E| < 2`, `hs0 : ∀ N, 0 ≤ s N`, `hst : ∀ N, s N ≤ t N`, `ht1 : ∀ N, t N < 1`: deterministic regime.
2. `{n}`; `hcard : ∀ᶠ N, (Fintype.card (LoopData (B.L N) n) : ℝ) ≤ N^Cv`: combinatorial, discharged by `card_loopData_le`.
3. `hK : 0 ≤ K`, `hγ : 0 < γ`: constants.
4. `hΞ : HighProb B.P Ξ`: one fixed event sequence.
5. `hHol : ∀ᶠ N, ∀ ω ∈ Ξ N, ∀ q, ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N), |scale_u^n ‖lkT_u‖ − scale_v^n ‖lkT_v‖| ≤ N^K |u−v|^γ`: a deterministic modulus on the event.
6. `hseq : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N, 1 ≤ Λ N) → Lemma514Premises X E s t n Λ Φ → ∀ v : ℕ → ℝ, (∀ N, v N ∈ Icc (s N) (t N)) → StochDom B.P (fun N (q : LoopData (B.L N) n) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖) (fun N _ _ => (Λ N^{1/2} + Φ N) * (scale E N (v N)^n)⁻¹)`.
   - **The antecedent `Lemma514Premises X E s t n Λ Φ`** (Lemma514Moment:388–395) is the conjunction of four StochDoms, each **uniform over `TimeIcc s t`**:
     - `flowXiL (2n+2) ≺ Λ`;
     - `∀ m ∈ [1,n), flowXiLK m ≺ Φ`;
     - `∀ m ∈ [2,n], flowXiLK m · flowXiLK (n−m+2) · flowA⁻¹ ≺ Φ`;
     - `flowXiL (n+1) ≺ Φ`.
   - This antecedent is **assumed**: whoever proves `hseq` gets it for free.
   - The **consequent** is a StochDom at the single time `v_N` for each terminal sequence `v`. So `hseq` is "∀ terminal sequence, a fixed-time StochDom, given interval-uniform premises". It is not a stopped-path statement.
   - Its producer must reach the fixed-time bound at `v_N` from interval-uniform premises. That is the supervisor's per-terminal-sequence pattern (T1511 `h276_of_pointwise`).
- The conclusion is `Step3.Lemma514 B.P (flowXiLK X E s t) (flowXiL X E s t) (flowA B E s t) n`, which has the same four premises (Step3:386–393).

**Re-run Lemma514Holder grep (fix 3).** The output, verbatim in A.2, has 4 hits:
- line 942 is docstring text;
- line 950 is the binder `{n : ℕ} (H : MomentDuhamel.Hyp (sample d) E s t n)` of `lemma514_of_hHol_flow`;
- line 985 is the binder `(H : ∀ n, MomentDuhamel.Hyp …)` of `lemma514_forall_of_hHol_flow`;
- line 1011 is the same binder of `flow_sharpLmK_of_hHol_flow` (Lemma514Holder:1008), a fourth `MomentDuhamel.Hyp` consumer that r0 missed. It is also forbidden.

None of these hits is inside `hHol_flow`, `hKb_flow` or `exists_highProb_normX`, and their constant closures contain no `MomentDuhamel.Hyp` (§0.4).

**`Lemma514Q716` / `NonAlt` base lemmas.** These are cross-referenced to T1522's Step 0, not duplicated (T1522 state `merged`). Verbatim grep of `docs/reports/T1522-prove.md`:
```
22:`RBM.norm_Uker_fastDecay_le_sumZero` (`Hierarchy/KernelDecay.lean:1489`), and its `_sigma`
23:specialisation `norm_Uker_fastDecay_le_sumZero_sigma` (line 1615) for the paper's charge
25:`Lemma514NonAlt.momNorm_Uker_short_*` trace back to `norm_Uker_fastDecay_le_short`
41:Their dependency closure is purely deterministic complex/real analysis on `Matrix (ZMod L)
```

---

## (I4) Where Lean needs S(2,l) for all charges

**Input shapes** (Step3.lean, verbatim binders):
- `S_all (h : Hyp P X Y As R A) (h0 : ∀ m, 1 ≤ m → S P X As R A m 0) (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S P X As R A m l) : ∀ k n, 1 ≤ n → S P X As R A n k` (:594).
- `S_of_S (h) {n k} (hn : 3 ≤ n) (hk : 1 ≤ k) (hSk : ∀ m, 1 ≤ m → m ≤ n - 1 → S … m k) (hSk1 : ∀ m, 1 ≤ m → m ≤ n + 2 → S … m (k - 1)) (hS2 : S P X As R A 2 3) : S P X As R A n k` (:502).
- `xiLK_two_le (h) (hS2 : S P X As R A 2 3) : StochDom P (X 2) fun N _ _ => As N ^ (1/2)` (:473).
- All three are abstract in `X`: per-sample-free StochDom statements over an abstract index `U N`, for any `P`, with clean closures.

**`X m` is a sup over all charge vectors.**
- `Step3.flowXiLK X E s t n N u ω = X.xiLK E N u ω n` (:863).
- `Sample.xiLK = lkMax · scale^m` (:785).
- `Sample.lkMax E N t ω m = ⨆ u : LoopData (B.L N) m, X.lkErr E N t ω u.idx` (:781).
- `LoopData (L n) := (Fin n → Bool) × (Fin n → ZMod L)` (Flow/Hypotheses:135), whose first factor is the charge vector.
- So `X 2` sups over all four `σ ∈ {+,−}²`.
- `RBM.loopMax` (Loop/Split:350) is the same sup for the raw matrix loop.

**The Lean input where (+,+)/(−,−) 2-loops enter: `RBM.StepGlue.AprioriDecayAll`** (StepGlue:386, a def):
- Statement: `StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => X.lkErr E N p.1 ω p.2.idx) (fun N p _ => (etaT E (s N) / etaT E p.1)^4 * (B.scale E N p.1)⁻¹^2)`.
- Kind StochDom; uniform in `u`; any `Sample`; clean.
- It is (2.76) without the decay profile, over **all** charges.
- Steps 1–2 supply only (+,−): `step2_gauss.2` and `aprioriDecay_pm'`.
- `RBM.ChargeReduce.aprioriDecayAll_of_pp'` (ChargeReduce:229) reduces it to the single missing charge `RBM.ChargeReduce.AprioriDecayPP` (ChargeReduce:215, `σ = (+,+)`, `ppLoop`). The (−,−) charge follows by conjugation, and (+,−)/(−,+) are free. This is the one-charge gap of supervisor §2A. Both declarations are StochDom, uniform in `u`, any `Sample`, clean.

**Every consumer where `X 2` or a 2-loop enters for σ ∈ {(+,+),(−,−)}.** The attributes are per row. The dependency entries come from the constant-closure outputs in §0.4. The first runs are in the scratch files `run.out`, `compact.out` and `compact2.out`. For rows 8 and 18, the lines for `flow_sharpLoop_glue`, `flow_steps45_glue` and `flow_steps45_W` were reproduced in the Compact3 re-run of 15:14 UTC.

| # | Declaration, file:line | How the all-charge 2-loop enters | Kind | Time | Dims | Dep. (§0.4, Compact3 re-run below) |
|---|---|---|---|---|---|---|
| 1 | `StepGlue.flow_xiLK_two_le`, StepGlue:437 | hyp `(h276 : AprioriDecayAll X E s t)` ⟹ `X 2 ≺ (η_s/η_u)⁴` | StochDom → StochDom | uniform in u (TimeIcc) | any `Sample B` | clean (0/0/0/0, no APrime) |
| 2 | `StepGlue.flow_hs2`, StepGlue:453 | hyp `h276 : AprioriDecayAll` ⟹ `X 2 ≺ flowA^{1/4}` (Step 4's `h2`) | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 3 | `StepGlue.flow_S_two`, StepGlue:469 | hyp `h276 : AprioriDecayAll` ⟹ `S(2,l)` | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 4 | `StepGlue.flow_S_le_two'`, StepGlue:493 | hyps `hll`, `h276 : AprioriDecayAll` ⟹ `h12` | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 5 | `StepGlue.flow_S_le_two`, StepGlue:701 | bundle form, hyp `h276 : AprioriDecayAll` (StepGlue:704) | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 6 | `StepGlue.flow_sharpLoop_glue'`, StepGlue:535 | hyp `h276 : AprioriDecayAll` (:542), fed to `Step3.flow_sharpLoop` | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 7 | `StepGlue.flow_steps45_glue_W'`, StepGlue:590; `flow_steps45_glue'`, :627 | hyps `h276 : AprioriDecayAll` (:599/:634) **and** `hsharp : SharpLoopFlow` whose `n = 2` instance (all charges, `‖L‖`) is passed as `flow_hs1`'s `h277` (:617) | StochDom (+ bound transfer `h45`) → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 8 | `StepGlue.flow_sharpLoop_glue`, :710; `flow_steps45_glue`, :725 | bundle forms, hyp `h276 : AprioriDecayAll` (:715/:730) | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 9 | `StepGlue.flow_hs1`, StepGlue:507 | hyp `h277` over `LoopData 2` (all charges, `‖L‖`). Only (+,−) is used (§I2) | StochDom (+ bound transfer) → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 10 | `Step2PP.flow_S_two_of`, Step2PP:408 | hyp `hΘ : StochDom (flowXiLK X E s t 2) Θ` (all charges) ⟹ `S(2,l)` | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 11 | `Step2PP.flow_S_le_two_of'` :426, `flow_S_le_two_of` :914, `flow_hs2_of` :925, `flow_sharpLoop_glue_of` :942, `flow_steps45_glue_of` :960 | the same `hΘ` on `flowXiLK 2` (all charges). `flow_hs2_of` and `flow_steps45_glue_of` also take `hone : X 1 ≺ 1` / `h45 : Eq45Flow` | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 12 | `Step2PP.xiLK_two_le`, Step2PP:345 | produces `hΘ` from `Hy : BootPP X E s t` (Step2PP:322). `BootPP.step` is a **stopped-path hypothesis**: `HighProb {ω | ∀ v ∈ [s,t], (∀ u ∈ [s,v], Ξ_{u,2} ≤ N^{2δ}Θ) → Ξ_{v,2} ≤ N^δ Θ}`. It is a hypothesis, not proved (CLAUDE.md §3.5) | HighProb (stopped-path `BootPP.step`) → StochDom | uniform in u; hypothesis is a **path** statement | any `Sample B` | clean (0/0/0/0, no APrime) |
| 13 | `Step3.flow_sharpLoop_of` Step3FlowSharp:33; `flow_sharpLoop` :65 | hyp `h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S … m l`; its `m = 2` instance is the all-charge `S(2,l)` | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 14 | `Step3.S_all` :594 | `h12 2 (k+1)` at `n = 2` (:606) and `h12 2 3` passed to every `S_of_S` call (:608) | StochDom → StochDom (abstract) | abstract index `U N` (instantiated as `TimeIcc`) | abstract `P X` | clean (0/0/0/0, no APrime) |
| 15 | `Step3.S_of_S` :502 | `hS2 : S(2,3)` → `xiLK_two_le` (:524) → the quadratic terms `m = 2` and `m = n` of (5.92) (:541–548). Also `hSk 2` for the short-loop term `m = 2 < n` (:517–522) | StochDom → StochDom (abstract) | abstract index `U N` | abstract `P X` | clean (0/0/0/0, no APrime) |
| 16 | `Step3.xiLK_le` :625, `xiL_le_one_of` :639, `xiL_le_one` :656 | hyp `h12` (all charges at `m = 2`), passed to `S_all` | StochDom → StochDom (abstract) | abstract index `U N` | abstract `P X` | clean (0/0/0/0, no APrime) |
| 17 | `Step45.xiLK_le_one_of_hyp`, Step45:242 | hyps `h12` and `h2 : X 2 ≺ A^{1/4}`; `Step3.xiLK_le h h0 h12` at Step45.lean:257 | StochDom → StochDom (abstract) | abstract index `U N` | abstract `P X` | clean (0/0/0/0, no APrime) |
| 18 | `Step45.flow_sharpLmK` :306, `flow_steps45` :477, `flow_steps45_W` :669 | hyps `h12` and `h2 : flowXiLK 2 ≺ flowA^{1/4}` (all charges) | StochDom → StochDom | uniform in u | any `Sample B` | clean (0/0/0/0, no APrime) |
| 19 | `Step3.Lemma514` (Step3:386) and `Gauss.Lemma514Premises` (Lemma514Moment:388) | premise 2 at `m = 2 < n` (`flowXiLK 2 ≺ Φ`) and premise 3 at `m = 2` and `m = n` (`flowXiLK 2 · flowXiLK n · flowA⁻¹ ≺ Φ`). In the P5 `n = 3` case these are the sub-terms of supervisor §2A | Prop defs (conjunctions of StochDoms) | uniform in u (TimeIcc) | abstract / any `Sample B` | clean (0/0/0/0, no APrime) |

No attempt was made to prove or refute S(2,l) for σ ∈ {(+,+),(−,−)}. P0(a) handles that on the dispatcher side.

---

## Open issues and ticket sizing

- **M1** (§I1/§I2, recommended): `xiLK_one_le_one_at_seq` plus its grid form. It gives Ξ_1(u_N) ≺ 1 at grid points, both charges, general `Dims`, from `step2_gauss` through `detAvgIBP_stochDom_of_localLaw_complete`, with steps S1–S5 as named above. Estimate: **1 ticket**.
- **M2a + M2b** (§I2): `flow_hs1_pm` and `stochDom_norm_Lval_pm_of_aprioriDecay`. They remove the (+,+)/(−,−) premise from Ξ_1 on the flow route. They are useful only once a non-vacuous `Eq45Flow` producer exists. Estimate: 1 small ticket.
- **O1 (for the dispatcher).**
  - `detAvgIBP_stochDom_of_localLaw_complete` uses `goodSetFlow`, a relocated definition in an APrime file (F1).
  - The merged `step2_gauss`/`steps12_gauss` use APrime **theorem** modules (F2).
  - Under the ticket's literal criterion both count as "depends on an `APrime*` file". Whether this is acceptable (for example, whether those APrime files are general-`Dims` and non-`exampleGrow`) is a dispatcher decision.
  - The T1524 audit's 4966-constant closure count disagrees with the 70124 found here.
- **O2 (F3).** `eq45Flow_of_goodSetFlow_highProb` and `eq45Flow_of_goodSetFlow_budget` have unsatisfiable hypotheses; the compiled negative is in A.6. `eq45Flow_of_unifDom` and `eq45Flow_of_localLaw_gain_budget` carry `(hfine, hΩ)`, which the Gaussian model does not satisfy; that is not compiled. The flow-uniform `Eq45Flow` route is therefore not usable as is.
- **O3.** If M1 is ticketed, the (4.5)∘(2.76) shape (≺ Ψ² at a fixed time, instead of the bound-transfer `Eq45Flow`) needs a `docs/paper-deltas.md` entry. That file is outside this ticket's scope.
- **O4 (I4/§2A).** S(2,l) for σ ∈ {(+,+),(−,−)}, equivalently `ChargeReduce.AprioriDecayPP`, has no Lean producer. It is out of scope (P0(a)).

## Build and axioms

- No module was built: report-only ticket, and no repository `.lean` file changed.
- Scratch checks: `lake env lean` on `Closure/Run/Compact/Compact2/Compact3/Path/Path2/Path3/Neg.lean` in the session scratchpad. All exited 0. The final `Neg.lean` has no `sorry`, and `#print axioms t1525_hfine_hWδ_inconsistent` gives `[propext, Classical.choice, Quot.sound]`.
- `Lean.collectAxioms` of every declaration in §0.4 printed `[propext, Classical.choice, Quot.sound]`, except `RBM.LoopData`, which printed `[]`.

---

## Appendix A: verbatim command outputs

**A.1 `h560` is a binder name, not a constant**
```
$ grep -rn "(h560" RBM1D | head -8
RBM1D/Hierarchy/H560Check.lean:273:    (h560 : ∀ b, ‖gloop L W H z ⟨[false, true, true], [b, a, a]⟩‖
RBM1D/Hierarchy/H560Check.lean:344:    (h560 : ∀ (b : LoopArg (B.L N) 2) (c : ZMod (B.L N)),
RBM1D/Hierarchy/EGDef.lean:283:    (h560 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
RBM1D/Hierarchy/Lemma57.lean:512:    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂) :
RBM1D/Hierarchy/Lemma57.lean:533:  refine (h560 b).trans (p2.trans (le_of_eq ?_))
RBM1D/Hierarchy/Lemma57.lean:557:    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂) :
RBM1D/Hierarchy/Lemma57.lean:1098:    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
RBM1D/Hierarchy/Lemma57.lean:1130:    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
```

**A.2 Lemma514Holder grep (4 hits; explained in §I3)**
```
$ grep -n "MomentDuhamel\|jStar\|h560\|APrime" RBM1D/Gauss/Lemma514Holder.lean
942:(T180/T187's `RBM.MomentDuhamel.Hyp`) and `hrhs` (T146/T157/T165, plus `hnum` and the `edgeKer`
950:    {n : ℕ} (H : MomentDuhamel.Hyp (sample d) E s t n)
985:    (H : ∀ n, MomentDuhamel.Hyp (sample d) E s t n)
1011:    (H : ∀ n, MomentDuhamel.Hyp (sample d) E s t n)
```

**A.3 condExpDiag grep (explained in §I1)**
```
$ grep -rn "condExpDiag" RBM1D/Gauss/*.lean | grep -i "hol\|sub_le"
RBM1D/Gauss/CondStableFlow.lean:974:`RBM.Gauss.norm_condExpDiag_sub_le_offdiag`: it enters with the coefficient
RBM1D/Gauss/CondStableFlow.lean:1067:    have hbound := norm_condExpDiag_sub_le_offdiag (gaussIBP d) hE hu0 hu1 i ω
RBM1D/Gauss/CondStableFlow.lean:1257:    (unifDomIcc_flucRow_condExpDiag d hE ht1 hg hpos hρ1 hcρ3 hδ1 hΩ hΦW) hHolBlk
RBM1D/Gauss/CondStableFlow.lean:1387:* the **`condExpDiag` half**, T129's `RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow`:
RBM1D/Gauss/CondStableFlow.lean:1394:`RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow` describes.
RBM1D/Gauss/CondStableFlow.lean:1402:`RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow` already carry, and it comes from (2.72); nothing
RBM1D/Gauss/CondStableFlow.lean:1570:  filter_upwards [norm_condExpDiag_flow_sub_le_rpow (δ := δ) (K := Kc) d hE hs0 ht1 hKc, hKtot]
RBM1D/Gauss/CondStableFlow.lean:1640:  filter_upwards [norm_condExpDiag_flow_sub_le_rpow (δ := δ) (K := Kc) d hE hs0 ht1 hKc, hKtot]
RBM1D/Gauss/CondDom.lean:67:* `RBM.Gauss.norm_condExpDiag_sub_le_offdiag`, `RBM.Gauss.condExpDiag_stochDom_of_offdiag` — the
RBM1D/Gauss/CondDom.lean:725:replaces the uniform bound of `RBM.Gauss.norm_condExpDiag_sub_le` by a weighted one, and needs
RBM1D/Gauss/CondDom.lean:768:/-- **The weighted reduction.**  `RBM.Gauss.norm_condExpDiag_sub_le` bounds the p. 50 remainder
RBM1D/Gauss/CondDom.lean:775:theorem norm_condExpDiag_sub_le_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
RBM1D/Gauss/CondDom.lean:875:    have hbound := norm_condExpDiag_sub_le_offdiag hG hE ht0 ht i ω
RBM1D/Gauss/DetIBPWeighted.lean:24:theorem norm_condExpDiag_sub_le_two_phi (hE : |E| < 2) (hu0 : 0 ≤ u)
RBM1D/Gauss/DetIBPWeighted.lean:38:      norm_condExpDiag_sub_le_offdiag (gaussIBP d) hE hu0 hu1 i ω
RBM1D/Gauss/DetIBPWeighted.lean:44:#print axioms norm_condExpDiag_sub_le_two_phi
RBM1D/Gauss/DetIBPWeighted.lean:129:    have hbound := norm_condExpDiag_sub_le_two_phi hE hu0 hu1 i ω ha0 hΦ0
RBM1D/Gauss/CondExpMod.lean:60:of `RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow`.
RBM1D/Gauss/CondExpMod.lean:78:* `RBM.Gauss.norm_condExpDiag_flow_sub_le` — **the modulus**, with the random constant:
RBM1D/Gauss/CondExpMod.lean:80:* `RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow` — the same in the `hHol` shape of
RBM1D/Gauss/CondExpMod.lean:339:theorem norm_condExpDiag_flow_sub_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {u v : ℝ}
RBM1D/Gauss/CondExpMod.lean:407:This is `hHol` of `RBM.Gauss.stochDom_timeIcc_Lmax_of_unifDom` for the `condExpDiag` half of
RBM1D/Gauss/CondExpMod.lean:410:random constant of `RBM.Gauss.norm_condExpDiag_flow_sub_le` into `N^K`.
RBM1D/Gauss/CondExpMod.lean:420:theorem norm_condExpDiag_flow_sub_le_rpow (d : Dims) {E : ℝ} (hE : |E| < 2) {s t δ : ℕ → ℝ}
RBM1D/Gauss/CondExpMod.lean:455:  have hmain := norm_condExpDiag_flow_sub_le d N hE hu1 hv1 k ω
RBM1D/Gauss/DetFlucAvgTimeNet.lean:38:  have hC := norm_condExpDiag_flow_sub_le d N (E := 0) (by norm_num) hu1 hv1 k ω
RBM1D/Gauss/IBP.lean:1108:theorem norm_condExpDiag_sub_le (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht : t < 1)
RBM1D/Gauss/IBP.lean:1171:  exact absurd (norm_condExpDiag_sub_le hG hE ht0 ht i ω hall) (not_le.2 hi)
```

**A.4 Recommended producer: transitive check with all five patterns (MD, S2H, jStar component, 560/h560, APrime module)**
```
== RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete  @ RBM1D.Gauss.DetAvgIBPFlow:274
  closure size: 57540; flagged: 1 [RBM.Gauss.goodSetFlow [APrime-module] (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
  'jStar' substring, not a name component (false positives): [Unitary.conjStarAlgAut._proof_2 (Mathlib.Algebra.Star.UnitaryStarAlgAut),
 [... 9 further Mathlib `conjStar*` names elided ...]]
  module import closure: 5370 modules, of which APrime*: 2 [RBM1D.Gauss.APrimeGeneralMovingCarrierCore,
 RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore]
  axioms: [propext, Classical.choice, Quot.sound]
```
The eq45Flow producers (fix 2):
```
== RBM.Gauss.eq45Flow_of_unifDom  @ RBM1D.Gauss.Eq45FlowInputs:628
  closure size: 56538; flagged: 1 [RBM.Gauss.goodSetFlow [APrime-module] (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
== RBM.Gauss.eq45Flow_of_goodSetFlow_highProb  @ RBM1D.Gauss.Eq45Small:507
  closure size: 57649; flagged: 1 [RBM.Gauss.goodSetFlow [APrime-module] (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
== RBM.Gauss.eq45Flow_of_localLaw_gain_budget  @ RBM1D.Gauss.MinorDiffCond:1229
  closure size: 57370; flagged: 1 [RBM.Gauss.goodSetFlow [APrime-module] (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
== RBM.Gauss.eq45Flow_of_goodSetFlow_budget  @ RBM1D.Gauss.MinorDiffCond:1299
  closure size: 57624; flagged: 1 [RBM.Gauss.goodSetFlow [APrime-module] (RBM1D.Gauss.APrimeGeneralMovingCarrierCore)]
```
The forbidden `MomentDuhamel.Hyp` lemmas:
```
== RBM.Gauss.lemma514_of_hHol_flow  @ RBM1D.Gauss.Lemma514Holder:948
  closure size: 59164; flagged: 6 [RBM.MomentDuhamel.Hyp [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel),
 RBM.MomentDuhamel.Hyp.F [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel),
 RBM.MomentDuhamel.Hyp.cMD [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel),
 RBM.MomentDuhamel.Hyp.integrable [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel),
 RBM.MomentDuhamel.Hyp.mk [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel),
 RBM.MomentDuhamel.Hyp.momentDuhamel [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel)]
== RBM.Gauss.lemma514_forall_of_hHol_flow  @ RBM1D.Gauss.Lemma514Holder:983
  closure size: 59166; flagged: 6 [RBM.MomentDuhamel.Hyp [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel), ...same 6...]
== RBM.Gauss.lemma514_of_momentDuhamel  @ RBM1D.Gauss.Lemma514Moment:535
  closure size: 34978; flagged: 6 [RBM.MomentDuhamel.Hyp [MomentDuhamel.Hyp] (RBM1D.Gauss.MomentDuhamel), ...same 6...]
RBM.Gauss.flow_sharpLmK_of_hHol_flow @ RBM1D.Gauss.Lemma514Holder:1008 | closure 59441 | MomentDuhamel.Hyp: 6 [RBM.MomentDuhamel.Hyp, ...]
```
`flow_hs1` and the reusable (I3) lemmas:
```
RBM.StepGlue.flow_hs1 @ RBM1D.Hierarchy.StepGlue:507 | closure 20640 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 0 [] | 560/h560: 0 [] | APrime-module constants: 0 in 0 modules []
RBM.Gauss.lemma514_of_seq @ RBM1D.Gauss.Lemma514Moment:408 | closure 20732 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 0 [] | 560/h560: 0 [] | APrime-module constants: 0 in 0 modules []
RBM.Gauss.hHol_flow @ RBM1D.Gauss.Lemma514Holder:721 | closure 53365 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 0 [] | 560/h560: 0 [] | APrime-module constants: 0 in 0 modules []
RBM.Gauss.exists_highProb_normX @ RBM1D.Gauss.Lemma514Holder:1049 | closure 51773 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 0 [] | 560/h560: 0 [] | APrime-module constants: 0 in 0 modules []
RBM.Step3.S_all @ RBM1D.Hierarchy.Step3:594 | closure 19358 | MomentDuhamel.Hyp: 0 [] | Step2.Hyp: 0 [] | jStar-named: 0 [] | 560/h560: 0 [] | APrime-module constants: 0 in 0 modules []
```

**A.5 No named window-restriction lemma for `LocalLawFlow`/`LocalLawUnifIcc`**
```
$ grep -rn -E "LocalLawFlow \(?[a-zA-Z ]*\)? ?E (u u|s' t'|\(fun)" RBM1D | head
$ grep -rn -E "(theorem|def) [A-Za-z_.']*(timeIcc|TimeIcc)[A-Za-z_.']*(incl|restrict|mono|sub|ofLe|of_le|embed|map)" RBM1D | head
```
Both commands printed nothing. The only `LocalLawUnifIcc d E u u` producer outside the consumers is in an APrime file (`grep -rn "LocalLawUnifIcc d E u u" RBM1D`: `RBM1D/Gauss/APrimeFixedOneLoopGeneralDims.lean:32` and `:82`).

**A.6 Compiled negative (scratch `Neg.lean`, not a repository file)**
```lean
theorem t1525_hfine_hWδ_inconsistent (d : Dims) {E : ℝ} {s t δ : ℕ → ℝ} (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hδpos : ∀ N, 0 < δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hWδ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * (2 * δ N) ^ 2) : False
```
Proof idea: pick `N ≥ 2` with `W_N ≤ N` (`W_le_self`, Eq45FlowInputs:282) and `hfine` at `N`, and put `x = √δ_N`.
- From `η⁻¹ ≥ 1` (`RBM.Gauss.one_le_inv_etaT`, Step1Hyp:612), `hfine` gives `4N³x ≤ 1`, hence `256N¹²x⁴ ≤ 1`.
- `hWδ` gives `1 ≤ 16W_N x⁴ ≤ 16N x⁴`.
- Since `16N < 256N¹²`, these contradict each other.

The hypotheses `hδpos`, `hfine` (verbatim) and `hWδ` (verbatim) all appear in the signatures of `eq45Flow_of_goodSetFlow_highProb` (Eq45Small:510/512/525) and `eq45Flow_of_goodSetFlow_budget` (MinorDiffCond:1302/1304/1317), together with `hE hs0 ht1 hst`.

Output:
```
$ lake env lean <scratchpad>/t1525r/Neg.lean
't1525_hfine_hWδ_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound]
```
