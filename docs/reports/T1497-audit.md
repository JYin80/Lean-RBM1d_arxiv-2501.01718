Auditor model: claude-opus-5-5[1m]

# T1497 (amend-1) audit: M6 restated with a per-u jS-cap premise

Date: 2026-09-25 20:47 UTC. Branch `t/T1497` at `e315ca2`, base `a3e7e36`, which is T1493's merge.
Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1497-audit`. It is a fresh detached worktree, separate from the prover's. The build cache is an APFS clone of main's, and main's cache had no `Step2QVEvent` artifact, so the module was compiled from scratch.
Inputs: `docs/tickets/T1497.md`, `docs/tickets/T1497-amend-1.md` (the amendment supersedes the original), `docs/reports/T1497-prove.md`, `docs/reports/T1488-prove.md` §3 (M6), and `docs/DECISIONS.md` §10b.

## Verdicts

| Target | Verdict |
|---|---|
| (T1) `RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS` | **PASS** |
| (T2) `RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS_le` (optional corollary) | **PASS** |

## 1. Math preflight
- Line 1 of the report reads `Prover model: claude-sonnet-5`.
- §(a) "Math preflight" gives a PASS with reasons and appears before the Lean section (b).
- The report was overwritten in place after the restart, and the branch has one commit. The order in which it was written therefore cannot be checked independently. The structure is compliant.

## 2. Statement vs ticket and paper
- **T1 matches amend-1 exactly.**
  - The premise is `Step2.jS (sample d) E D N u ω ≤ (N:ℝ)^((1:ℝ)/2)`, inside the event, per `u`, before `∀ a`. This is the same term as the ticket's `(1/2 : ℝ)`.
  - The `quadVar`/`diagShape'` part is verbatim M6 (T1488-prove §3). Its arguments are `ℓ_u = (band d).ell N u`, `ℓ_s = (band d).ell N (s N)`, `η_u = etaT E u`, `D`, `J = APrimeJG.jG (sample d) E N u ω ℓ_u η_u D`, `Smax = EarlyQVRateEv.sDet (band d) E N u ℓ_s`, and `ε = EEDef.nearEpsilon W L ℓ_u η_u D J`.
  - The `nearEpsilon` arguments were checked against its definition (`APrimeNearRem.lean:271`, signature `(W L ℓu ηu D J : ℝ)`).
- **Hypotheses.** The hypotheses are exactly the Step-1 list of `step1Hyp_gauss_of_scale''` (`EntryBoundTime.lean:654`): `hκ, hE, hB, hs0, hst, ht1, hcond, hc0, hreg`. The only addition is `{D} (hD : 60 ≤ D)`. `D` is free in the conclusion and is required by `early_raw_full` and M6, so this addition is forced. Relative to M6, the only new condition is the per-`u` implication premise `jS ≤ N^{1/2}` (amend-1, criterion 1).
- **Quantifier order.** The fixed parameters `d, E, s, t, κ, c, D` come first, then `∀ τ > 0`, then `HighProb`, which is `∀ D' > 0, ∀ᶠ N`. `u` and `a` are inside the event. The paper's order is preserved.
- **Proof-exponent shape.**
  - `diagShape'` (`APrimeNearRem.lean:714`, with `diagNearRate`/`diagFarRate` at `APrimeQVEndpoint.lean:807/810`) is the unmerged proof-level shape: near `cNear2·(ℓ_u/ℓ_s)^5·1(≤4ℓ*)`, far `cFar2(2J)²A·2√Smax + 72(2J)³A⁻¹`, plus the explicit `W^{-D}` remainder. This is the (5.71)/(5.72) form that pilot §9(B) requires. The difference from the displayed (5.36) is already covered by paper-deltas #113.
  - The original ticket said to use T1493's `ee_le_reduced_EEpath_sym`. The proof does not use it. The shape is fixed by the target statement itself, and it arrives through `early_raw_full`. This is a route difference, not a statement defect.
- **T2 is a legitimate consequence, not a weakening.** It uses the same hypotheses plus `hΘ : ∀ᶠ N, Θ N ≤ N^{1/2}`. Its premise is `jS ≤ Θ N`, and the proof is `HighProb.mono` of T1 via `hjSle.trans hΘN`. With `Θ := fun N => N^{1/2}`, `hΘ` holds trivially and T2 is T1 verbatim. T1 itself is proved in the exact ticket form.

## 3. Vacuity, hidden hypotheses, cycles, boundary cases
- **Compiled nondegenerate witness.** I compiled a scratch file with `lake env lean` in the audit worktree; it gave no errors and no warnings.
  - Setup: take `positive_length_exampleGrow_resident`, with `s ≡ 0`, `t` satisfying `∀ᶠ N, s N < t N` (a positive-length window), `c > 0`, `Cond272Reg`, and `BoundsCore (sample exampleGrow) 0 s`. Set `κ := 1`, `E := 0`, `D := 60`.
  - Result: for every `τ > 0`, `∀ᶠ N, ∃ ω` such that ω lies in T1's event **and** `Step2.jS … (s N) ω ≤ N^{1/2}`.
  - How: intersect T1's event with `Step2.stochDom_jS_init` (M1, `Hierarchy/Step2Init.lean:32`, at `τ = 1/2`) and apply `HighProb.nonempty`. `1 ≤ scale(s N)` came from `Step1.eventually_scale_facts` at `u = s N`.
  - So the premise actually fires at a genuine time `u = s N ∈ [s N, t N]` in a non-collapsed window. The conclusion there is a real bound on `quadVar`.
  - No quantity is astronomically large: `D = 60`, `E = 0`, and the window is a first time cell of positive length.
- **Premise also holds on the whole window in the stopping-time regime.** `Step2.jS_highProb` (`Step2.lean:1293`) gives `jS ≤ C N^{δ/4}(η_s/η_u)^4` w.h.p., uniformly in `u`, under the `N^c`-gained (2.72). Since `(η_s/η_t)^{30} ≲ Wℓ_tη_t ≤ N`, this is `≲ N^{δ/4+2/15} ≤ N^{1/2}`. This is consistent with the ticket's argument `J*_u ≤ N^{δ+2/15}` before the stop.
- **The exponent 1/2 suffices for `hJcap` (criterion 2).**
  - `highProb_jG_le_of_entryBoundFlow` at `τ' = 1/4` gives `jG ≤ 1 + N^{1/4}(9e^{√3}jS + 2)`.
  - With `jS ≤ N^{1/2}`, the private lemma `eventually_jcap_bound` proves in Lean that `1 + N^{1/4}(9e^{√3}N^{1/2} + 2) ≤ N` eventually. It dominates each term by `N^{7/8}` and uses `(3 + 9e^{√3}) ≤ N^{1/8}`.
  - Any cap exponent `< 1` would do.
- **Hidden hypotheses.** None. The private helpers take only positivity/`q ≥ 1` side conditions, and all of them are discharged in the proof. No structure field carries an extra assumption. `BoundsCore` is itself one of the Step-1 hypotheses.
- **Boundary cases.** `N = 0` and small `N` are excluded only through `∀ᶠ N`. `TimeIcc s t N` is nonempty because `s ≤ t`. The witness window has positive length.
- **Cycles.** None. The new file is imported by nothing, and all of its dependencies are pre-existing modules.

## 4. Dependencies and §10b
- **Declarations used.** All are already merged:
  - `APrimeFullQV.early_raw_full`: fixed `u`, per ω, abstract `Sample`.
  - `APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale`: general `d`.
  - `APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`: general `d`.
  - `APrimeJG.highProb_jG_le_of_entryBoundFlow` and `jG`: general `d`.
  - `Gauss.entryBoundFlow_floor`, `rpow_neg_one_le_etaT_of_scale_ge`, `flowDelta_le_rpow_neg`, `etaT_le_of_le`.
  - `Step1.eventually_scale_facts`, `Band.eventually_le_W`, `Step2.eventually_le_W_sq`, `EEBridge.eeFacts`.
  - `diagShape'`/`diagNearRate`/`diagFarRate`, `sDet`, `nearEpsilon`. All of these are deterministic: `sDet = (ℓ_u/ℓ_s)^3·scale⁻³`, and `diagShape'` depends only on `W, L, ℓ_u, ℓ_s, η_u, D, J, Smax, ε, a`. None of them involves a smooth-prefix weight.
- **Transitive scan.** I walked the constants in each theorem's type and value with a metaprogram. The closure of T1 and of T2 contains:
  - **no** `RBM.EarlyQVRateEv.jStar` (criterion 3);
  - no `exampleGrow`;
  - no `h560`/`rhs535`;
  - no constant whose name contains `Prefix` or `Smooth`;
  - from `EarlyQVRateEv`, only `sDet`.
- **About `RBM.Step2.jStar`.** The closure does contain `RBM.Step2.jStar`. This is the generic (5.29) max functional `J*_{u,D}`, which defines `Step2.jS`, the premise object that amend-1 prescribes. It is not the banned `EarlyQVRateEv.jStar`.
- **Direct grep.** `grep jStar RBM1D/Gauss/Step2QVEvent.lean` returns nothing.
- **§10b.** All conditions hold: every A′-era input is fixed-time, deterministic, or valid for general `Dims`. None depends only on exampleGrow or on smooth-prefix weights, and neither `jStar` nor `h560` is used.

## 5. Build, axioms, scope
- `lake build RBM1D.Gauss.Step2QVEvent`: `Build completed successfully (3913 jobs)`, rc 0. There are no errors. The warnings are linter-only: one unused variable `hSmax` at 65:18, and `show`-tactic style at 256, 261 and 296.
- `lake build RBM1D` in the audit worktree: `Build completed successfully (9642 jobs)`, rc 0. The new file is not yet root-imported; the import is added at merge.
- `#print axioms` on both public theorems gives `[propext, Classical.choice, Quot.sound]`.
- The file contains no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`.
- `git diff --stat a3e7e36 t/T1497` shows only `RBM1D/Gauss/Step2QVEvent.lean` (+500), so frozen signatures are untouched.
- Since the branch point, main has only **added** files (plus `RBM1D.lean` imports). No dependency changed, and neither public name exists on main, so the merge has no conflict risk.

## 6. The prover's open issues
1. **Generic `Θ` in T2.** This is non-blocking. T2 is optional, and the acceptance criteria require only T1. Specializing to `N^{δ+2/15}` needs the (2.72) arithmetic `(η_s/η_t)^4 ≲ N^{2/15}`, which belongs to the A5 consumer. It works whenever `δ + 2/15 < 1/2`.
2. **Crude `√(qS) ≤ q√S` bound in `diagFarRate_le_two_mul_of_Smax_scale`.** This is non-blocking. It lives in a private intermediate lemma. The resulting `2N^{τ/2}` loss is absorbed into `N^τ` (`hpow`), and the public conclusion is exactly the target with no residual loss. The target only asks for `∀ τ > 0`, so it states no rate that could be degraded.

## 7. Notes for the dispatcher (non-blocking)
- **Inaccurate satisfiability argument in the report.** The report says the premise is satisfiable "since `jS ≥ 1` always". That does not follow. The compiled witness in §3, via `stochDom_jS_init`, is the correct argument. The report also cites exampleGrow satisfiability without a compiled check; §3 supplies one.
- **Paper-delta candidate `T1497a`.** In the paper, (5.36)/(5.44) are used only before the stop σ, which supplies `J* ≤ N^δ(η_s/η_t)^4 ≤ N^{δ+2/15}`. The Lean M6 makes this an explicit per-`u` premise `jS ≤ N^{1/2}`. The ticket forbids the prover from touching `docs/paper-deltas.md`, so the dispatcher should append this entry.
