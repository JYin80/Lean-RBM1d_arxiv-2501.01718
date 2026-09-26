Auditor model: claude-opus-5-5

# T1530 re-audit (repair r1) — G1c pilot P4a, Lemma 5.9 at a fixed time

Branch `t/T1530` @ `3847714cd4ef350830f777dd08310c036a619e43` (parent `525cc86`, which was audited earlier as T1–T4 PASS, T5 RETURN). Worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1530`. Re-audit date: 2026-09-26T16:23Z.
Diff vs `main`: one file, `RBM1D/Gauss/LoopDecayFixed.lean` (the ticket's only writable file). The new file is not merged yet, so no frozen signature is touched.

## Overall verdict: PASS

T1 PASS · T2 PASS · T3 PASS · T4 PASS · **T5 PASS**. The earlier T5 RETURN is resolved. The ticket's check "nothing depends on `APrime*`" is resolved by reading it through DECISIONS §10b; see the dependency check below. The dispatcher should confirm that reading.

## Global checks

- **Math preflight.** `docs/reports/T1530-prove.md` §(a) contains a repair preflight for T5 (flow, fixed-time and grid forms), each marked PASS and labelled as written before the Lean change. It addresses each of the four earlier defects. The T1–T4 preflight stands from the first round.
- **Build.** `lake build RBM1D.Gauss.LoopDecayFixed` succeeds (3967 jobs). The only warnings are the deprecated `if_pos`/`if_neg` calls in the two measurability proofs, which are cosmetic. `lake build RBM1D` succeeds (9673 jobs). The root does not import the module yet; that happens at merge. Auditor scratch files import both `RBM1D` and the module and elaborate with no name clash.
- **Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 11 declarations: `decaySet`, `measurableSet_decaySet`, `loop_decay_of_entry_decay`, `K_decay`, `lk_decay`, `lkDecaySet`, `measurableSet_lkDecaySet`, `mem_decaySets_of_lre`, `highProb_flow_decaySet`, `highProb_fixedTime_decaySet`, `highProb_grid_decaySet`. A grep for `sorry`/`admit`/`axiom` in the file finds nothing.
- **Transitive-closure check.** I wrote my own Lean meta script: type + value, `allowOpaque`, applied recursively.
  - `highProb_flow_decaySet`: 70207 constants. It contains `RBM.Gauss.steps12_gauss`, `RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecay`, `RBM.Lre_eq`, `RBM.Decay.loopDecay_Kgen` and `highProb_grid_of_flow`.
  - Name patterns absent from the closure: `Step2.Hyp`, `MomentDuhamel.Hyp`, `exampleGrow`, `FirstCell`, `OneLoopSharp`, `sorryAx`.
  - `APrime*`: 144 constants. `MomentDuhamel.*`: 3 definitions (`eeFun`, `EEpath`, `lkFun`); none of them is the `Hyp` structure.
  - Closure of `steps12_gauss` alone (70120 constants): exactly the same 144 `APrime*` and 3 `MomentDuhamel.*` constants, and no `exampleGrow`.
  - Closure of all the T1530-authored parts plus `highProb_flowDec_of_aprioriDecay` (54852 constants): **0** `APrime`, **0** `MomentDuhamel`, **0** `exampleGrow`.
  - Conclusion: every A′-named dependency enters only through the merged, accepted `steps12_gauss` (T1524), which the ticket itself requires as the source of T5. Those dependencies are proved general-`Dims` lemmas (the `*GeneralDims`, `APrimeJG`, … modules), not hypotheses, and they do not involve `exampleGrow`. DECISIONS §10b (A′ abandoned; reuse allowed for fixed-time, deterministic or arbitrary-`Gauss.Dims` declarations) permits this, and T1524's audit accepted it.
  - Read literally, the ticket's "nothing depends on `APrime*`" contradicts its own requirement that T5 come "from `steps12_gauss`". I read the check as "no dependence on an A′ hypothesis, on an `exampleGrow`-only result, on `MomentDuhamel.Hyp` or on `Step2.Hyp`", and under that reading it passes. **Dispatcher confirmation requested** (this is the prove report's open issue 1). It does not block the mathematics.
- **Dependencies accepted.** All are merged: `steps12_gauss` (T1524, `Gauss/Step2Close.lean`); `LKDecayQuant.*` (T126/T138, root import); `Lre_eq`; `Decay.*` (T59); `GridJStar.highProb_grid_of_flow`. There is no cycle, since the file only imports merged modules.
- **Fixed-time.** `decaySet` and `lkDecaySet` are sets of matrices at one time `u`, with spectral parameter `zt E u` and deterministic `Kval E N u`. The flow statement quantifies these fixed-time sets over `v ∈ [s_N, t_N]` inside the event. The fixed-time corollary uses one deterministic `u(N)`. PASS.
- **D after n.** The binder order is `… hreg (m₀ : ℕ) {τ} (hτ) {D} (hD)`, followed by `HighProb` (which quantifies over `D''` and then `∀ᶠ N`). So `D` comes after the length cap `m₀`, and every fixed parameter comes before `N`. PASS.

## Per target

### (T1)–(T4) — PASS (spot check: unchanged)
`git diff 525cc86 3847714` shows no change to `decaySet`, `mem_decaySet_iff`, `measurableSet_decaySet`, `loop_decay_of_entry_decay`, `K_decay`, `ell_mul_rpow_pos` or `lk_decay` beyond two things: the binder names in `instCountableLoopIdx` were renamed to `_J _J'`, and module docstring text was updated. The earlier audit's findings stand. T3 still covers every σ and every length ≤ m₀ via `Decay.loopDecay_Kgen`. The new `lkDecaySet` (the L−K set, radius `ℓ_u W^τ`, error `W^{-D}`) has the same shape as `decaySet`. Its measurability proof follows the same pattern, and `Kval` is deterministic.

### (T5) `highProb_flow_decaySet` / `highProb_fixedTime_decaySet` / `highProb_grid_decaySet` — PASS

**Earlier defect 1 (vacuity) — fixed; the counterexample cannot be reproduced.** The old counterexample needed N-independent binders `{R δG : ℝ}` and the hypothesis `hδ' : ∀ᶠ N, δG·max(1,|Im z|⁻¹)^{m₀} ≤ W^{-D}`, which force `δG = 0` when `D > 0`. `#check @highProb_flow_decaySet` shows that the new signature has no `R`, `δG` or `hδ'`, and no other numerical hypothesis on the radius, the error, `1−u` or `D`. Its hypotheses are exactly `steps12_gauss`'s list: `hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`, compared token by token with `Step2Close.lean:541`. After that come only `m₀`, `τ > 0` and `D > 0`. The entry radius `R_v(N) = ℓ_v N^{τ/4}` and error `N^{-(D+2m₀+1)}` are internal and depend on N. The only extra numeric side conditions are in the deterministic core `mem_decaySets_of_lre`: `2m₀ ≤ N^{τ/4}`, `2 ≤ N^{τ/4}`, `2·max(1,1/Im m)^{m₀} ≤ N`, and "exp beats poly". Each is an eventual fact in N for fixed parameters, and each is discharged inside the flow theorem (`eventually_const_mul_rpow_le`, `eventually_exp_small`). None can force a degenerate value. So the old counterexample cannot be written down, and the compiled witness below shows that the new hypothesis list is jointly satisfiable for every `D > 0`.

**Earlier defect 2 (conditional adapter) — fixed.** At l.495 the proof calls `steps12_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg` and passes `h12.aprioriDecay` ((2.76)) to `highProb_flowDec_of_aprioriDecay`. The signature of that lemma takes exactly this `hdecay` type and nothing else (`LKDecayQuant.lean:799`). The closure check confirms that `steps12_gauss` really is in the proof term and is not just a hypothesis name. The rest of the route is `FlowDec`, then `Lre ≤ N^{-(2D'+2)}` beyond `ℓ_v N^{τ/4}`, then `Lre_eq` (entry bound, `W ≤ N`), then `norm_Gsig_apply_le` for both charges, then (T2). This is the route the earlier audit asked for, and it avoids Lemma 4.1.

**Earlier defect 3 ((5.75) incomplete) — fixed.** The conclusion is `Hflow ∈ decaySet ∧ Hflow ∈ lkDecaySet`, so it gives `|L| ≤ W^{-D}` and `|L − K| ≤ W^{-D}` for every loop of length ≤ m₀ that has a label pair at distance ≥ `ℓ_v W^τ`. The K term `cKdecay·exp(…)` is absorbed through the ℓ̂ dichotomy (`term2_le`). In the cut-off regime `L√(1−v) < 1` the radius `L·W^τ` exceeds `L/2`, so both conditions hold vacuously, as they do in the paper. Otherwise `1/(1−v) ≤ N²`. No hypothesis `1−u ≥ N^{-C}` is added. (5.75) bounds the sum `|L| + |L−K|`; the two separate `W^{-D}` bounds with `D > 0` arbitrary give it (sum ≤ `2W^{-D} ≤ W^{-D+1/2}`, because W→∞).

**Earlier defect 4 (degenerate grid window) — fixed.** The grid statement uses the genuine window `[s, t]` and `highProb_grid_of_flow`'s own grid hypotheses (`K N ≠ 0`, `K N + 1 ≤ N^C`). `highProb_fixedTime_decaySet` gives the literal "fixed time u(N)" form for any deterministic `u(N) ∈ [s_N, t_N]`.

**Statement vs paper.** Lemma 5.9 / (5.75) with Definition 5.8 (5.74): radius `ℓ_u W^τ`, error `W^{-D}`, all σ and a, loop lengths ≤ m₀ (general, which covers the paper's 2n+2). The paper's probability `1 − O(W^{-D'})` is rendered as `HighProb`, i.e. `1 − O(N^{-D''})` for all `D''`. This is equivalent because `N^{1/2} ≤ W ≤ N`. Uniformity in `v` makes the statement stronger than a single time. The hypotheses are the Step 1–2 outputs' assumptions (`steps12_gauss`), matching the paper's use of Steps 1–2 at the current window. This is the general statement: general `Dims`, general `E` with `|E| ≤ 2−κ`, general window. It is not a special case and not a conditional adapter.

**Witness (compiled by the auditor, 0 errors; scratch files below).**
- `audit_hreg (d : Dims)`: `hreg` holds for `E = 0`, `s ≡ 0`, `t ≡ 1/2`, `c = 1/4`, for every `d`. The proof uses `N^{1/4}·2^{30} ≤ W·ℓ_{1/2}·½`, from (2.2) and `ℓ ≥ 1`.
- The full `highProb_flow_decaySet` elaborates at general `d` with `κ = 1`, `hB := BoundsCore_zero (sample d)`, for `(m₀, τ, D) = (4, 1/10, 1)` and for `(9, 1/1000, 1000)`. `highProb_grid_decaySet` elaborates at `Dims.exampleGrow` with `K N = N+1`, `C = 2`. So the hypotheses are jointly satisfiable at an interior time `1/2` (`1 − t = 1/2`), for every `D > 0`.
- The conclusion is not vacuous. `audit_far_pair_exists` proves that on `Dims.exampleGrow` (L ≈ N^{1/4}, W ≈ N^{3/4}), at `v = 1/2` and `τ = 1/10`, there are eventually block labels `x, y` with `ℓ_v W^τ ≤ zdist(x − y)`. Hence `decaySet`/`lkDecaySet` impose a real `W^{-D}` bound on actual resolvent loops. This is not a collapsed window and not an empty index set.

## Boundary cases
- `m₀ = 0, 1`: no far pair exists, so the statement is trivially true there. This is harmless and does not collapse `m₀ ≥ 2`.
- `v = s_N`, `v = t_N`: both included. Cut-off regime (`ℓ_v = L`): vacuous exactly as in (5.74).
- No `N = 0` loophole: all bounds are eventual, and `mem_decaySets_of_lre` requires `1 ≤ N`.

## Paper deltas (for the hub/dispatcher at merge; not a verdict issue)
The prove report lists three candidates but did not append them: (i) the `HighProb` rendering of `1 − O(W^{-D'})`, which is equivalent; (ii) the entry bound via (2.76) + `Lre_eq` instead of Lemma 4.1, which changes the route only; (iii) uniformity in v, which is stronger. Under CLAUDE.md §3.7 these should be recorded with tag `T1530a`. None changes the mathematical content.

## Auditor scratch files (not in the repo)
`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM1D/c89db6b5-4fbc-4b34-995c-1e741f3b37d2/scratchpad/Audit1530.lean` (axioms, `hreg` witness, instantiations), `Audit1530b.lean` (non-vacuity of the conclusion), `Audit1530c.lean` (closure check). Each was compiled with `lake env lean` in the T1530 worktree.
