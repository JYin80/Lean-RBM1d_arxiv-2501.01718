Auditor model: claude-opus-5-5

# T1527 re-audit (repair round 1): sharp one-loop bound `Ξ₁ ≺ 1` at a grid point

Audited: branch `t/T1527` @ `854e777` (commits `41f1bc5`, `854e777`; `git diff main...t/T1527` touches only `RBM1D/Gauss/OneLoopSharpGrid.lean`, +256). Worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1527`. Ticket `docs/tickets/T1527.md`, amended by CONTROL H36: (T3)'s APrime* ban is replaced by DECISIONS §10b; `MomentDuhamel.Hyp`, `Step2.Hyp`, `jStar` (§10b: `EarlyQVRateEv.jStar`), `h560` (`h535_of_jS` / `eGpm_le_rhs535_of_jS`) and exampleGrow-only results remain forbidden. Prove report: `docs/reports/T1527-prove.md`. Prior audit: BLOCKED (overwritten here). Audit time: 2026-09-26T15:26Z.

**Overall: PASS.** (T1) PASS, (T2) PASS, (T3) PASS.

## 1. Math preflight
The prove report §(a) has a math preflight, written before the Lean changes of this round, with PASS for (T1)–(T3). It includes a table resolving each item of the prior audit and a §10b admissibility argument for `goodSetFlow`. PASS.

## 2. Statement vs ticket and paper
- **(T1) `RBM.Gauss.stochDom_lkMax_one_of_localLaw`.**
  - Hypotheses: `hκ0 hκ1 hE hu0 hu1 ha hK hη hΨhi hll`. This is the list of `detAvgIBP_stochDom_of_localLaw_complete` (`DetAvgIBPFlow.lean:274`) with `Ψ N = (scale_{u_N})⁻¹^{1/2}`, minus `hΨlo`.
  - `hΨlo` is proved inside the proof by `W_rpow_neg_half_le_scale_inv_rpow_half`, from `Grid.DriftPt.scale_le_W`. This strictly strengthens the theorem.
  - `hll : LocalLawUnifIcc d E u u (fun N => (scale_{u_N})⁻¹^{1/2})` is the ticket's tight pointwise local law, verbatim.
  - Conclusion: `StochDom (P d) (N,_,ω ↦ scale_{u_N} · lkMax … (u N) ω 1) 1`. This is `Sample.xiLK … 1` (5.76) up to `pow_one`. General `Dims`.
  - Parameter order: `d, E, κ, u, a, K` are fixed before `StochDom`'s `∀ τ D, ∀ᶠ N`. Correct.
- **Tight scale: PASS.**
  - The control is the constant `1`.
  - `hΨΨ1` gives `scale_{u_N} · (Ψ_N · Ψ_N) = 1` exactly, for every `N` (`scale_mul_inv_rpow_half_sq`, via `scale_pos'`).
  - It is applied at the same `τ`, with no split and no loss. The bound is `≺ 1`, not `≺ (Wℓη)^{1/2}`.
- **Both charges: PASS.**
  - `lkMax … 1 = ⨆ v : LoopData (L N) 1`, where `LoopData L 1 = (Fin 1 → Bool) × (Fin 1 → ZMod L)` (`Flow/Hypotheses.lean:135`). So both charges are in the supremum.
  - `lkErr_one_eq_norm_trace` (`Eq45Flow.lean:89`) holds for every `v`, including the charge bit.
  - The supremum is removed by `exists_lt_of_lt_ciSup` over a finite nonempty type.
- **(T2) `RBM.Gauss.stochDom_lkMax_one_of_steps12`: PASS.**
  - Binders are exactly `steps12_gauss`'s (`Step2Close.lean:541`): `hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`. Added is only `hu : ∀ N, u N ∈ Icc (s N) (t N)`, which is the ticket's "at any `u` with `u N ∈ [s N, t N]`".
  - The previous extra binders `a K ha hK hη hΨlo hΨhi` are gone. The prior RETURN item is fixed.
  - The derivation in `eventually_regime_of_hreg` is proved, and I checked it line by line:
    - `η_t ≤ η_s` gives `(η_s/η_t)^30 ≥ 1`, so `N^c ≤ scale_t`.
    - `band_scale_antitone` (via `flowScale_antitoneOn`) and `u ≤ t` give `N^c ≤ scale_u`.
    - `scale_t ≤ W·L·η_t ≤ N·η_t` (from `ℓ_t ≤ L` and `Band.dim`) with `1 ≤ N^c` gives `N^{-1} ≤ η_t ≤ η_u`.
    - With `a := c/2` and `K := 1`, the result is `hΨhi` and `hη`.
  - `hll` comes from `steps12_gauss … |>.localLaw`, restricted to `TimeIcc u u` by `localLawFlow_singleton_of_localLawFlow` (uses `hu`). It then goes through `localLawUnifIcc_of_localLawFlow`, whose majorant on `Icc (u N) (u N)` is trivial (`v = u N`).
  - The remark carries over from the prior audit: at `u = s` the result already follows from `hB`; the content is `u ∈ (s, t]`.

## 3. Vacuity, hidden hypotheses, cycles
- **`hΩ` is genuinely discharged. It has not come back under another name.**
  - Neither target has a hypothesis involving `goodSetFlow`, `HighProb` or a threshold `δ`. The T1 binders are all listed in §2, and each has its original producer meaning.
  - Inside `detAvgIBP_stochDom_of_localLaw'` (`DetAvgIBPFlow.lean:230`), `hΩ` is constructed by `highProb_detFlucDelta_of_localLaw` (`DetFlucThreshold.lean:322`). That lemma's hypotheses are only `hE hu0 hu1 ha hK hθ0 hθa hθ1 hη hΨhi hll`, and the `θ` hypotheses are discharged by `detFlucTheta_specs`.
  - `highProb_detFlucDelta_of_localLaw` in turn calls `highProb_goodSetFlow_of_localLaw` (`GoodSetFlow.lean:184`) at `s = t = u`, which uses the net bound `stochDom_timeIcc_localLaw`.
  - My closure script finds the path `stochDom_lkMax_one_of_localLaw → …_complete → detAvgIBP_stochDom_of_localLaw' → highProb_detFlucDelta_of_localLaw`.
  - `LocalLawUnifIcc` is an `abbrev` for a `UnifDomIcc` statement (`GoodSetFlow.lean:114`). It is not a structure and has no hidden fields.
- **`goodSetFlow` is fixed-time. I checked this myself.**
  - Definition (`APrimeGeneralMovingCarrierCore.lean:72`): `{ω | ∀ u ∈ Icc (s N) (t N), GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) (δ N)}`. It has no other time dependence.
  - It is a hypothesis-free `Set` definition for any `d : Dims`.
  - On the T1 route it is instantiated only as `goodSetFlow d E u u (detFlucDelta Ψ θ)`. `Icc (u N) (u N) = {u N}`, so this is the fixed-time good event (4.1) at the deterministic time `u N`, with a threshold that depends only on `Ψ, θ, N`.
  - The `hll` and IBP inputs on this route are likewise all at `(s, t) = (u, u)`.
  - The singleton window is the ticket's intended pointwise target, not a collapsed-window loophole: the conclusion is a pointwise statement at `u_N`.
- **Satisfiability.**
  - (T2) adds no hypothesis beyond `steps12_gauss`'s (audited in T1524) and `hu`, which `u := t` satisfies.
  - (T2)'s compiled proof instantiates (T1) with every hypothesis derived. So (T1)'s hypotheses are satisfiable whenever `steps12_gauss`'s are.
  - I checked the paper witness in the report:
    - `Dims.exampleGrow` (`W ≈ N^{3/4}`, `L ≈ N^{1/4}`), `E = 0`, `κ = 1`, `s ≡ 0`, with `BoundsCore` from `BoundsCore_zero`/`firstCell_boundsCore`.
    - `1 - t_N = N^{-ε}` and `u = t`, which give `scale_t ≈ N^{3/4-ε/2}` and `(η_s/η_t)^30 = N^{30ε}`.
    - With `ε = 1/100` and `c = 1/10`, `hreg` holds eventually (`0.4 < 0.745`).
    - The witness is nondegenerate: `η_u → 0` and `u_N ∈ (0,1)`. Nothing in it is astronomically large, and exampleGrow is used only as a witness, never as an input.
  - The earlier wrong citation of `detAvgIBP_firstCell_witness` has been withdrawn.
- There is no cycle. The new helpers are generic and are used only in this file.

## 4. Dependencies and the amended (T3) criterion: independent closure check
I wrote my own script (scratch, not committed; independent of the prover's). It does a worklist BFS with `Expr.foldConsts` over each constant's type and value (`allowOpaque := true`), inductive constructors and `all`, constructor → inductive, and recursor rules. It flags names containing `MomentDuhamel.Hyp`, `Step2.Hyp`, `jStar`, `EarlyQVRateEv`, `exampleGrow`, `h535_of_jS`, `rhs535_of_jS`, `gmOfJS` or `h560`; binder names containing `h560` in types; any `Hyp` name component; module names containing `EarlyQVRateEv`, `MomentDuhamel` or `APrime`; and `APrime`-named constants that live outside APrime modules. I ran it with `lake env lean` in the audit worktree after the module build.
- **(T1)** closure 57681.
  - The only flags are Mathlib `conjStarAlgAut*` substring matches on `jStar`, which are false positives.
  - APrime-module constants: 1, `RBM.Gauss.goodSetFlow`, reached by the path `… → detAvgIBP_stochDom_of_localLaw' → goodSetFlow`. There are no APrime-namespace constants outside APrime modules.
  - There are no `EarlyQVRateEv`, `MomentDuhamel`, `h560` or exampleGrow constants.
- **(T2)** closure 70142; `steps12_gauss` alone has closure 70127.
  - `RBM.MomentDuhamel.Hyp`: NOT in closure. `RBM.Step2.Hyp`: NOT in closure.
  - `RBM.Step2FarInputs.h535_of_jS` and `eGpm_le_rhs535_of_jS`: NOT in closure. No `gmOfJS` constant.
  - `jStar`:
    - Only `RBM.Step2.jStar`, the paper's (5.29) J* over 2-loops (`APrimeSmoothPrefixCanonicalCore.lean:79`), and its lemmas in `Hierarchy/Step2`. The path is `steps12_gauss → step2_gauss → gridPointwise'_gauss → grid_thr_improve → jSMat_le_of_Agrid → Step2.jStar_le`.
    - `RBM.EarlyQVRateEv.jStar`, the flagged object of TASKS "待查"(a), is absent.
    - The `EarlyQVRateEv` constants that do occur (`sMax`, `sDet`, `glueLD0/1`, `eeL6_two_le`, `re_gloop_four_le_sMax`) are not banned.
  - `h560`:
    - 9 constants have types that bind `h560`: the generic `Lemma57.{case2_pointwise, eG_far_le, sum_far_le}` and `Grid.{drift_point_le', eG_le', eG_le_reduced', eG_le_reduced_of_schwarz', eGpm_le_reduced', eGpm_le_rhs535'}`. They are reached via `drift_of_goodSet → drift_point_le_heG → drift_point_le_blk' → drift_point_le'`.
    - I read `drift_point_le_blk'` (`GridDriftPoint.lean:1942`). It has no `h560` binder, and it supplies that slot by the proof `norm_gloop_three_le_gmBlkM` with `Gm := gmBlkM`. So `h560` is proved; it is not the unsatisfiable `gmOfJS` form.
    - Positive control: my script on `Step2FarInputs.h535_of_jS` does flag `h535_of_jS`, `eGpm_le_rhs535_of_jS` and `gmOfJS*`, so the detector works.
  - exampleGrow: absent.
  - `MomentDuhamel` constants: `MomentDuhamel.{EEpath, eeFun, lkFun}` (definitions) and `Gauss.{genD_eq_sum_pairs, sum_used_eq_sum_pairs_coordD2_pt}` (module `MomentDuhamelHypGauss`). None of them is `MomentDuhamel.Hyp`.
  - `Step1.Hyp` is present, but `steps12_gauss` discharges it by `step1Hyp_gauss_of_scale''`, and it is not banned.
- **APrime list (§10b).**
  - My list of the 169 APrime-module constants in T2's closure is identical to the prove report's list, checked by `diff` after sorting. The report's extra `goodSetFlow` line is its separate (T1) list.
  - §10b compliance:
    - Every one of them enters only through the merged `steps12_gauss`, inside a proof term in which `d : Dims` is a free variable. So each is used at a generic `Dims`, and any hypotheses it has are discharged there.
    - No exampleGrow constant is in the closure, so none of them is an exampleGrow-only result.
    - The 7 constants from `APrimeSmoothPrefixCanonicalCore` are the Step 2 core definitions `jS`, `jStar`, `lk`, `sigPM`, `tT` (plus 2 `_proof_i`), not smooth-prefix-weight cross terms.
    - T2's own open hypotheses are exactly `steps12_gauss`'s plus `hu`.
  - For T1, the single APrime constant is the definition `goodSetFlow`, which §3 shows is fixed-time. It is admissible, as H36 explicitly states.
- All other dependencies are accepted, merged results: `detAvgIBP_stochDom_of_localLaw_complete`, `lkErr_one_eq_norm_trace`, `localLawUnifIcc_of_localLawFlow`, `steps12_gauss` (T1524), `Grid.DriftPt.scale_le_W` (T1515), `flowScale_antitoneOn`, `Band.scale_pos'`, `StochDom.precomp_param`.
- The prover's closure figures (57681 for T1 and 70142 for T2, 0 forbidden, 169 APrime) reproduce exactly. The prior (T3) RETURN is resolved.

## 5. Build and axioms
- `lake build RBM1D.Gauss.OneLoopSharpGrid`: `Build completed successfully (3967 jobs)`. No errors, and no warnings from this file.
- `lake build RBM1D` in the audit worktree: `Build completed successfully (9673 jobs)`. The root import is added at merge.
- Merge adjacency:
  - The branch base is `ae718fe`, and `main` is now `f0d4c95`. Since then `main` has changed only `RBM1D.lean` and the new `GridHierarchyN.lean` among `.lean` files.
  - None of the 8 declaration names in this file occurs anywhere on `main` (`git grep`), so there is no collision risk.
- `#print axioms`: `stochDom_lkMax_one_of_localLaw` and `stochDom_lkMax_one_of_steps12` both give `[propext, Classical.choice, Quot.sound]`. The six helpers give the same, as quoted in the prove report.
- There is no `sorry`, `admit` or `axiom` (grep is empty). Only the sole writable file is changed, and no frozen signature is touched.

## 6. Non-blocking notes
- The prove report's closure summary does not list the non-banned `EarlyQVRateEv` constants (`sMax`, `sDet`, `glueLD*`, …) that are in T2's closure through `steps12_gauss`. They are informational only.
- `goodSetFlow` still sits in an APrime-named file. Moving it to a non-APrime module would be cosmetic and is outside this ticket.
- The satisfiability witness is a paper argument. This follows the T1524 convention: no new hypothesis is introduced beyond an audited list plus the trivially satisfiable `hu`.

## Verdicts
- (T1) `stochDom_lkMax_one_of_localLaw`: **PASS**
- (T2) `stochDom_lkMax_one_of_steps12`: **PASS**
- (T3) axioms and amended dependency criterion: **PASS**
