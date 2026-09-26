Prover model: claude-opus-5-5

# T1530 — repair r1 (audit `docs/reports/T1530-audit.md`: T1–T4 PASS, T5 RETURN)

Branch `t/T1530` (base of this repair: `525cc86`), worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1530`,
sole writable file `RBM1D/Gauss/LoopDecayFixed.lean`.

This repair touches only (T5). (T1)–(T4) (`decaySet`, `measurableSet_decaySet`,
`loop_decay_of_entry_decay`, `K_decay`, `lk_decay`) keep their signatures and proofs. (T3) still
covers every σ and every length ≤ m₀ via `Decay.loopDecay_Kgen`; the 2–3 fallback is not used.
The earlier preflight for T1–T4 (Step 0: reuse of `Hierarchy/Decay.lean`, T59) stands as audited.

## (a) Math preflight for the repaired (T5), written before any Lean change

### Audit defects addressed

1. **Vacuity** (constant `R, δG` force `δG = 0`): the repaired (T5) has **no** free `R`/`δG`
   hypotheses. The radius and the entry error are internal and depend on N (and on the time v):
   `R_v(N) := ℓ_v · N^{τ/4}` and `δG(N) := N^{-D'}` with `D' := D + 2m₀ + 1`. The only
   hypotheses left are `steps12_gauss`'s list, verbatim, plus the fixed parameters `m₀`, `τ > 0`,
   `D > 0`. Since those parameters are unconstrained, the auditor's counterexample (a
   hypothesis that forces `δG = 0`) no longer applies.
2. **Conditional adapter**: the entry-decay event is now **derived**, not assumed. The chain is
   `steps12_gauss` (T1524, merged) → `.aprioriDecay` ((2.76)) →
   `LKDecayQuant.highProb_flowDec_of_aprioriDecay` (T138, merged, root l.242; it proves exactly
   the audit's route: (2.76) + `Decay.loopDecay_Kgen` at length 2 + `Lre ≤ |L−K| + |K|`, using
   that `Lre` is the real part of the `(+,−)` 2-loop) → `RBM.Lre_eq` → entry bound on `green`
   → `Decay.norm_Gsig_apply_le` (both charges) → (T2).
3. **Incompleteness vs (5.75)**: the conclusion carries both halves, `|L| ≤ W^{-D}` (decaySet)
   **and** `|L − K| ≤ W^{-D}` (new `lkDecaySet`). The `cKdecay · exp` K-term is absorbed
   internally (`LKDecayQuant.term2_le`, `cKdecay_le_bound`). The lower bound `1 − u ≥ N^{-C}` is
   **not a hypothesis**. It comes from the ℓ̂ dichotomy: if `L√(1−v) < 1`, then `ℓ_v = L`, the
   target radius `L·W^τ` exceeds the diameter `L/2`, and both statements are vacuous (true). If
   `L√(1−v) ≥ 1`, then `1/(1−v) ≤ L² ≤ N²`.
4. **Grid window**: the flow statement is now uniform in `v ∈ [s_N, t_N]`, so the grid transfer
   uses a genuine window `[s, t]` with a polynomial grid (no degenerate `s = t = u`). A
   fixed-time corollary at any deterministic `u(N) ∈ [s_N, t_N]` is also given.

### Target (T5-flow) `highProb_flow_decaySet`

Statement: for `d : Dims`, `κ ∈ (0,1]`, `|E| ≤ 2 − κ`, `s, t : ℕ → ℝ`, with steps12_gauss's
hypotheses verbatim (`hB : BoundsCore (sample d) E s`, `hs0`, `hst`, `ht1`, `c > 0`, `hreg`), for
every `m₀ : ℕ`, `τ > 0`, `D > 0` (D after m₀; all before the `∀ᶠ N` inside `HighProb`):
`HighProb (P d) (N ↦ {ω | ∀ v ∈ [s_N, t_N], H_v(ω) ∈ decaySet m₀ v τ D ∧ H_v(ω) ∈ lkDecaySet m₀ v τ D})`.
Here `lkDecaySet` is the (5.75) `L − K` set: every loop of length ≤ m₀ with a pair of labels at
distance ≥ ℓ_v W^τ has `|L_{v,σ,a}(M) − K_{v,σ,a}| ≤ W^{-D}`.

Paper: Lemma 5.9 (5.75), with Definition 5.8 (5.74), at every time `v` of the window. The paper
states probability `1 − O(W^{-D'})`. `HighProb` means `1 − O(N^{-D''})` for every `D''`, which is
equivalent because `N^{1/2} ≤ W ≤ N` eventually. The radius `ℓ_u W^τ` and the error `W^{-D}` are
the paper's own (W-scale), not the repository's `N^τ` convention of `LKDecayQuant`.

Proof (pathwise on the high-probability event, N large):

* `h12 := steps12_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`; `hdec := h12.aprioriDecay`,
  which has literally the type of the `hdecay` argument of `highProb_flowDec_of_aprioriDecay` at
  `B := band d`, `X := sample d`.
* `highProb_flowDec_of_aprioriDecay (τ := τ/2) (c := 2D' + 2)`: w.h.p., for all `v ∈ [s,t]` and
  all blocks `a, b` with `ℓ_v N^{τ/4} ≤ zdist(a − b)`, `Lre(H_v, z_v, a, b) ≤ N^{-(2D'+2)}`.
* Fix `v`, write `δ = 1 − v`. Dichotomy (`LKDecayQuant.ellHat_eq_L` / `ellHat_mul_sqrt_eq_one`):
  - `L√δ < 1`: `ℓ_v = L` and `ℓ_v W^τ ≥ L > L/2 ≥ zdist`, so both LoopDecays hold vacuously
    (`loopDecay_of_half_lt`).
  - `L√δ ≥ 1`: `ℓ_v √δ = 1` and `1/δ ≤ N²` (since `L ≤ N`).
    * Entry bound. For `x, y` with `R_v ≤ zdist(x.1 − y.1)`, apply FlowDec with `a = y.1`,
      `b = x.1` (`zdist_neg`). Then `Lre_eq` gives
      `W^{-2}‖G_{xy}‖² ≤ W^{-2} Σ_{β,α} ‖G_{(x.1,β),(y.1,α)}‖² = Lre ≤ N^{-(2D'+2)}`, so
      `‖G_{xy}‖² ≤ W² N^{-(2D'+2)} ≤ N^{-2D'}` (`W ≤ N`) and `‖G_{xy}‖ ≤ N^{-D'}`. Both
      charges follow from `norm_Gsig_apply_le`.
    * (T2) with `R = R_v > 0`, `δG = N^{-D'}`: `LoopDecay m₀ (2m₀R_v) (N^{-D'} max(1,|Im z_v|⁻¹)^{m₀})`.
      Radius: `2m₀ ℓ_v N^{τ/4} ≤ ℓ_v N^{τ/2} ≤ ℓ_v W^τ` once `2m₀ ≤ N^{τ/4}` (eventual) and
      `N^{1/2} ≤ W` ((2.2), `bandwidth`). Error: `|Im z_v| = δ·Im m`, so
      `max(1,|Im z_v|⁻¹) ≤ C_E N²` with `C_E = max(1, (Im m)⁻¹)` (N-independent, `|E| < 2`).
      Hence the error is `≤ C_E^{m₀} N^{-D-1} ≤ ½ N^{-D} ≤ ½ W^{-D}`, once `2C_E^{m₀} ≤ N`,
      using `W ≤ N` and `D > 0`. This is `LKDecayQuant.term1_le` arithmetic.
    * K at radius `ρ = ℓ_v W^τ`, lengths ≤ m₀ ((T3)): error `cKdecay m₀ δ · e^{-c₀√δ ρ/4}`. Here
      `c₀√δ ρ/4 = (c₀/4) W^τ ≥ (c₀/4) N^{τ/2} ≥ (c₀/2) N^{τ/4}` once `N^{τ/4} ≥ 2`, and
      `LKDecayQuant.term2_le (τ := τ/2)` gives `≤ ½ N^{-D} ≤ ½ W^{-D}`. Its side condition is
      `SumZeroDyn.eventually_exp_small`.
    * Conclusion: L-error `½W^{-D} ≤ W^{-D}` (decaySet, `.mono`). L−K error `½W^{-D} + ½W^{-D} = W^{-D}`
      (`LoopDecay.sub`, then `.mono`).

Hypotheses: exactly steps12_gauss's list. Nothing is added, and no numerical hypothesis on `R`,
`δG`, `1 − u` or D remains.
Quantifier order: `m₀`, then `τ`, `D`, then `HighProb` (∀ D'' ∃ N₀ …). D comes after n = m₀.
Dependencies (all merged): `steps12_gauss` (T1524); `LKDecayQuant.highProb_flowDec_of_aprioriDecay`,
`term1_le`-style arithmetic, `term2_le`, `ellHat_eq_L`, `ellHat_mul_sqrt_eq_one`,
`loopDecay_of_half_lt`, `eventually_L_le` (T126/T138, root l.242); `Lre_eq` (Green/EntryBound);
`Decay.norm_Gsig_apply_le`, `loopDecay_gloop`, `loopDecay_Kgen`, `LoopDecay.sub/.mono` (T59).
None of these statements mentions `APrime*`, `MomentDuhamel.Hyp` or `Step2.Hyp`. A
transitive-closure check is run after the build (section (b)).
Boundary cases: `m₀ = 0, 1`: no far pair in a loop of length ≤ 1, so vacuous and harmless;
`2m₀R_v` is then 0 or tiny, and the radius inequality still holds. `v = s_N` or `v = t_N`:
included. Cut-off regime: vacuous, as the paper's (5.74) is (radius ≥ diameter).
Simultaneous satisfiability: the hypothesis list is steps12_gauss's. A nondegenerate witness
(general `d`, `E = 0`, `κ = 1`, `s ≡ 0`, `t ≡ 1/2`, `c = 1/4`, `BoundsCore_zero`) is compiled in a
scratch file (not in the module) after the build. D > 0 is free, so the statement is
nondegenerate for every `D > 0`.
Verdict: **PASS**.

### Target (T5-fixed) `highProb_fixedTime_decaySet`

For any deterministic `u : ℕ → ℝ` with `s_N ≤ u_N ≤ t_N`, the same conclusion holds at the single
time `u(N)`. This is the ticket's literal "fixed time u(N)" form, obtained by specialising
(T5-flow). The extra hypotheses `s ≤ u ≤ t` only choose the time and are satisfiable by `u = t`.
Verdict: **PASS**.

### Target (T5-grid) `highProb_grid_decaySet`

`highProb_grid_of_flow` applied to (T5-flow), with the measurable family
`S N v := decaySet ∩ lkDecaySet`. Measurability comes from a shared lemma: a LoopDecay set of
`M ↦ gloop M z I − c I` is a countable intersection over `LoopIdx`, each piece using
`measurable_gloop_matrix`. The grid hypotheses (`K N ≠ 0`, `K N + 1 ≤ N^C`) are
`highProb_grid_of_flow`'s own. The window `[s, t]` is genuine.
Verdict: **PASS**.

### Docstring correction

The module docstring claim that (T5) was "complete in full" is removed. The docstring will describe
exactly what is proved. Only the open items that remain are listed.

## (b) Lean: declarations, build, axioms

Commit `3847714` on `t/T1530` (parent `525cc86`). Only `RBM1D/Gauss/LoopDecayFixed.lean` changed
(+372/−94). The new import is `RBM1D.Hierarchy.LKDecayQuant` (merged, root l.242; no cycle).
All declarations are in namespace `RBM.Gauss.Grid`.

Kept unchanged (T1–T4, audited PASS): `decaySet`, `mem_decaySet_iff`, `instCountableLoopIdx`
(only the unused binder names were renamed `_J _J'`), `measurableSet_decaySet`,
`loop_decay_of_entry_decay`, `K_decay`, `ell_mul_rpow_pos`, `lk_decay`.

Removed: the old conditional (T5) `highProb_flow_decaySet` / `highProb_grid_decaySet` with
constant `{R δG : ℝ}` (vacuous for D > 0), and the helper `eq_of_mem_timeIcc_self`. None of these
was merged, so no frozen signature is affected.

New:
* `lkDecaySet d E N m₀ u τ D`: the (5.75) `L − K` fixed-time set (radius `ℓ_u W^τ`, error `W^{-D}`).
  `measurableSet_lkDecaySet`.
* `mem_decaySets_of_lre`: deterministic core. If `Lre(M, z_v, a, b) ≤ N^{-(2D'+2)}` beyond
  `ℓ_v N^{τ/4}` (`D' = D + 2m₀ + 1`), plus elementary eventual facts about N, then
  `M ∈ decaySet ∧ M ∈ lkDecaySet`.
* `highProb_flow_decaySet d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg m₀ hτ hD`. The hypotheses are
  steps12_gauss's list, verbatim, then `m₀`, `τ > 0`, `D > 0`. Conclusion:
  `HighProb (P d) (N ↦ {ω | ∀ v : TimeIcc s t N, Hflow d N v ω ∈ decaySet d E N m₀ v τ D ∧ Hflow d N v ω ∈ lkDecaySet d E N m₀ v τ D})`.
  The proof genuinely calls `steps12_gauss` and uses `.aprioriDecay`.
* `highProb_fixedTime_decaySet`: the same at one deterministic `u(N) ∈ [s_N, t_N]`.
* `highProb_grid_decaySet`: grid transfer on the window `[s, t]` via `highProb_grid_of_flow`
  (grid hypotheses `K N ≠ 0`, `K N + 1 ≤ N^C`).

Final internal choices: entry radius `R_v(N) = ℓ_v · N^{τ/4}` (with `ℓ_v = (band d).ell N v`);
entry error `δG(N) = N^{-D'}`, `D' = D + 2m₀ + 1`. `highProb_flowDec_of_aprioriDecay` is called
with `τ := τ/2` and `c := 2D' + 2`.

Build:
```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1530 && lake build RBM1D.Gauss.LoopDecayFixed
→ Build completed successfully (3967 jobs).
```
The only remaining warnings in the file are the deprecated `if_pos`/`if_neg` inside the two
measurability proofs (cosmetic). There is no `sorry`, `admit` or `axiom`.

Axioms (scratch file importing the module; `#print axioms`): `decaySet`, `measurableSet_decaySet`,
`loop_decay_of_entry_decay`, `K_decay`, `lk_decay`, `lkDecaySet`, `measurableSet_lkDecaySet`,
`mem_decaySets_of_lre`, `highProb_flow_decaySet`, `highProb_fixedTime_decaySet`,
`highProb_grid_decaySet` each print `[propext, Classical.choice, Quot.sound]`.

Transitive closure (Lean meta script, type + value with `allowOpaque := true`, over all 9 main
new/kept theorems; 70216 constants):
* `RBM.Gauss.steps12_gauss`, `RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecay` and `RBM.Lre_eq`
  are all in the closure. Defect 2 is resolved: steps12_gauss is really invoked.
* `RBM.MomentDuhamel.Hyp`, `RBM.Step2.Hyp` and `sorryAx` do not appear.
* **APrime-named constants: 144, all inherited through `steps12_gauss` alone.** Per-root check:
  `steps12_gauss` 144; `highProb_flowDec_of_aprioriDecay`, `term2_le`, `mem_decaySets_of_lre`,
  `measurableSet_lkDecaySet`, `highProb_grid_of_flow`, `K_decay`, `loop_decay_of_entry_decay`
  0 each. They come from 12 proved general-Dims modules that T1524 already uses
  (`Gauss.APrimeAllTimeOneLoopGeneralDims`, `APrimeJG`, `APrimeGeneralMovingCarrierCore`,
  `APrimeGoodSetFlowGeneralDims`, `APrimeFullQV`, `APrimeCenteredModulusGeneralDims`,
  `APrimeQVEndpoint`, `APrimeRawSourcesGeneralDims`, `APrimeNearRem`,
  `APrimeSingletonLocalLawGeneralDims`, `APrimeFixedOneLoopGeneralDims`,
  `APrimeTwoChargeOneLoop`). These are lemmas, not hypotheses: steps12_gauss's signature has no
  APrime hypothesis and its axioms are the standard three. See open issue 1.

Witness (scratch file, compiled with 0 errors and no `sorry`): for general `d : Dims`, take
`κ = 1`, `E = 0`, `s ≡ 0`, `t ≡ 1/2`, `hB := BoundsCore_zero (sample d)`, `c = 1/4`, with `hreg`
proved (`N^{1/4}·2^{30} ≤ W·ℓ_{1/2}·½` eventually, from (2.2)). Then
`highProb_flow_decaySet … 4 (τ := 1/10) (D := 1)`,
`highProb_flow_decaySet … 7 (τ := 1/100) (D := 100)` and
`highProb_grid_decaySet … (K := N+1) (C := 2)` all elaborate. The hypothesis list is jointly
satisfiable at an interior time, and D > 0 is free. The audit's counterexample (a hypothesis
that forces `δG = 0`) cannot be formed: no hypothesis mentions `R`, `δG` or D.

## (c) Key lemmas used

`RBM.Gauss.steps12_gauss` (+ `Steps12.aprioriDecay`); `RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecay`,
`term2_le`, `ellHat_mul_sqrt_eq_one`, `ellHat_eq_L`, `loopDecay_of_half_lt`, `eventually_L_le`;
`RBM.SumZeroDyn.eventually_exp_small`, `eventually_const_mul_rpow_le`; `RBM.Lre_eq`;
`RBM.Decay.norm_Gsig_apply_le`, `loopDecay_gloop`, `loopDecay_Kgen`, `LoopDecay.mono/.sub`;
`RBM.Gauss.Grid.highProb_grid_of_flow`, `measurable_gloop_matrix`; `mE_im_pos`, `zt_im`,
`one_le_ellHat_of_nonneg`, `zdist_neg`; `Real.rpow_le_rpow_of_nonpos`.

## (d) Open issues

1. **Ticket-internal tension (for the dispatcher).** The auditor's check "nothing depends on
   `APrime*`" (in the transitive closure) cannot hold together with "(T5) from `steps12_gauss`".
   The merged T1524 theorem itself transitively uses 12 `APrime*`-named general-Dims modules.
   These are proved lemmas with no hypotheses and no sorry, and `MomentDuhamel.Hyp` and
   `Step2.Hyp` are absent. Every part of T1530 outside steps12_gauss has zero APrime-named
   dependencies. I did not resolve this by avoiding steps12_gauss: that is the conditional
   adapter the audit rejected (defect 2). The dispatcher should decide whether the §10b rule
   targets A′-*hypothesis* dependence (then PASS) or any APrime-named module.
2. Paper-delta candidates (not written; `docs/paper-deltas.md` is outside this repair's scope):
   (i) (5.75) is rendered with `HighProb` (`1 − O(N^{-D''})` ∀D'') in place of `1 − O(W^{-D'})`.
   These are equivalent since `N^{1/2} ≤ W ≤ N`.
   (ii) The (4.2)-type entry bound is obtained from (2.76) + `Lre_eq` instead of Lemma 4.1.
   This changes the proof route, not the statement.
   (iii) The conclusion is uniform in `v ∈ [s_N, t_N]`, which is stronger than a single time.
   No hypothesis `1 − u ≥ N^{-C}` is needed.
3. The deprecated `if_pos`/`if_neg` warnings in the measurability proofs are cosmetic.

## Verdict

T1 PASS · T2 PASS · T3 PASS (every σ, every length ≤ m₀) · T4 PASS ·
T5 PASS (derived from steps12_gauss, both halves of (5.75), nondegenerate for every D > 0),
subject to the dispatcher's reading of open issue 1.
