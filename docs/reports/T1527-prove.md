Prover model: claude-opus-5-5

# T1527 — G1c (Step 3): the sharp one-loop bound `Ξ₁ ≺ 1` at a grid point (repair round 1)

Repair of branch `t/T1527` @ `41f1bc5` after `docs/reports/T1527-audit.md` (overall BLOCKED:
(T1) BLOCKED, (T2) BLOCKED + RETURN, (T3) RETURN), under the dispatcher's H36 amendment:
(T3)'s blanket "no `APrime*` file" ban is replaced by DECISIONS §10b (A'-era declarations may be
reused when fixed-time / deterministic / valid for any `Dims`, with hypotheses checked
satisfiable); the ban on `MomentDuhamel.Hyp`, `Step2.Hyp`, `EarlyQVRateEv.jStar`, `h560` (the
`gmOfJS` one of `Step2FarInputs.h535_of_jS` / `eGpm_le_rhs535_of_jS`) and `exampleGrow`-only
results stays in full force.

Materials read: `CLAUDE.md` §3; the ticket; the audit; `DECISIONS.md` §10b; the Lean files of the
route (`DetAvgIBPFlow.lean`, `DetFlucThreshold.lean:322`, `GoodSetFlow.lean:184`,
`APrimeGeneralMovingCarrierCore.lean:72`, `Eq45Flow.lean:89`, `Step2Close.lean`,
`Flow/Hypotheses.lean`, `Flow/Scales.lean:100`, `GridDriftPoint.lean:2787`).

## (a) Math preflight (written before any Lean change of this round)

### Audit defects and how each is addressed

| Audit item | Resolution |
|---|---|
| (T1) BLOCKED: route needs `hΩ : HighProb (goodSetFlow d E u u δ)`, `goodSetFlow` lives in an APrime file | Existing producer, no new lemma: `highProb_detFlucDelta_of_localLaw` (`DetFlucThreshold.lean:322`, general `Dims`, fixed time `u`) produces exactly `HighProb (P d) (goodSetFlow d E u u (detFlucDelta Ψ θ))` from `hll`, `hη`, `hΨhi`, via `highProb_goodSetFlow_of_localLaw` (`GoodSetFlow.lean:184`). It is already called inside `detAvgIBP_stochDom_of_localLaw'` (`DetAvgIBPFlow.lean:208`), so `hΩ` is **not** an open hypothesis of (T1); the only APrime-located constant in (T1)'s closure is the definition `RBM.Gauss.goodSetFlow` itself (see §10b check below). |
| (T2) RETURN: extra binders `a K ha hK hη hΨlo hΨhi` | Dropped. Derived inside the proof from `hreg`, `hst`, `hu`, `ht1`, `(band d).dim`, `scale_le_W` and antitonicity of `scale` (`flowScale_antitoneOn`), with `a := c/2`, `K := 1`. `hu : u N ∈ [s N, t N]` stays: it is the ticket's own quantifier "at any `u` with `u N ∈ [s N, t N]`". |
| (T3) RETURN: false closure output | Replaced by real output of a compiled closure script (§(b)); script path and method given. |
| §3: wrong satisfiability witness for (T1) | Corrected below. |
| (optional) `hΨlo` of (T1) is always true | Also dropped from (T1): it is `scale_le_W` (for every `N`), proved inside. |

### §10b admissibility of the only APrime declaration in (T1): `RBM.Gauss.goodSetFlow`

`goodSetFlow d E s t δ N := {ω | ∀ v ∈ Icc (s N) (t N), GoodEvent (G_v(ω)) (m) (δ N)}`
(`APrimeGeneralMovingCarrierCore.lean:72`, namespace `RBM.Gauss`, any `d : Dims`). It is a
plain `Set` definition with no hypotheses (nothing to satisfy); used here only at `s = t = u`,
where `Icc (u N) (u N) = {u N}`, so it is the fixed-time good event (4.1) at the single
deterministic time `u N`: fixed-time, deterministic in its parameters, valid for any `Dims`.
Its own closure contains no other APrime constant (audit §4, re-confirmed in §(b)). The
`HighProb` of it is **proved** (not assumed) by the non-APrime `highProb_detFlucDelta_of_localLaw`.
§10b: admissible.

### (T1) `RBM.Gauss.stochDom_lkMax_one_of_localLaw`

* Statement: for `d : Dims`, `0 < κ ≤ 1`, `|E| ≤ 2 - κ`, `0 ≤ u N < 1`, `0 < a`, `0 ≤ K`,
  `hη : ∀ᶠ N, N^{-K} ≤ η_{u_N}`, `hΨhi : ∀ᶠ N, (scale_{u_N})^{-1/2} ≤ N^{-a}`, and the tight
  pointwise local law `hll : LocalLawUnifIcc d E u u (N ↦ (scale_{u_N})⁻¹^{1/2})`:
  `StochDom (P d) (N,_,ω ↦ scale_{u_N} · lkMax(u_N, ω, 1)) 1`, i.e. `Ξ^{(L-K)}_{u_N,1} ≺ 1`,
  (2.76) at `n = 1` with the (4.5) averaging. Paper: Lemma 4.1 (4.5) + (2.76); `lkMax · scale^1`
  is `Sample.xiLK … 1` (`Step3.lean:786`) up to `pow_one`.
* Change vs round 0: `hΨlo` removed (always true: `scale_u ≤ W` by `Grid.DriftPt.scale_le_W`,
  so `W^{-1/2} ≤ scale_u^{-1/2}`). Strictly stronger statement; everything else unchanged
  (audit §2: tight scale PASS, both charges PASS, quantifier order PASS).
* Quantifier order: `d, E, κ, u, a, K` fixed before `StochDom`'s `∀ τ D, ∀ᶠ N`. Preserved.
* Boundary: `u N = 0` allowed (conclusion then trivial but consistent); `a, K` enter only
  through the producer.
* Dependencies (all merged): `detAvgIBP_stochDom_of_localLaw_complete`,
  `lkErr_one_eq_norm_trace`, `Grid.DriftPt.scale_le_W` (T1515, merged), `Band.scale_pos'`,
  `StochDom.precomp_param`. None carries a forbidden constant (§(b)).
* Satisfiability witness (corrected; paper argument, not compiled): (T2)'s compiled proof
  instantiates (T1) at `a = c/2`, `K = 1` with every (T1) hypothesis derived from
  `steps12_gauss`'s list, so (T1)'s hypotheses are satisfiable whenever `steps12_gauss`'s are.
  A nondegenerate instance of the latter: `d = Dims.exampleGrow` (`W ≥ N^{1/2+1/8}`), `E = 0`,
  `s ≡ 0` with `BoundsCore` at `0` (`firstCell_boundsCore`, used only as a witness, never as an
  input), `1 - t_N = N^{-ε}` with `ε, c` small: `η_0/η_t = N^{ε}`,
  `scale_t ≍ W N^{-ε/2}`, so `N^{c + 30ε} ≤ scale_t` eventually (`hreg`); take `u = t`
  (`η_u → 0`, `u > 0`, not the `u = 0` point where the loop error vanishes; nothing
  astronomically large). The previous citation of `detAvgIBP_firstCell_witness` (which uses
  `Ψ = firstCellPsiWeighted`, not the tight scale) is withdrawn.
* Verdict: **PASS**.

### (T2) `RBM.Gauss.stochDom_lkMax_one_of_steps12`

* Statement: hypotheses exactly `steps12_gauss`'s (`hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`) plus
  the grid point `u` with `hu : ∀ N, u N ∈ Icc (s N) (t N)` (the ticket's quantifier). Same
  conclusion as (T1) at `u`.
* Derivation of (T1)'s regime hypotheses at `u` (for `N` eventually, `N ≥ 1`, in the `hreg`
  and `(band d).dim` events):
  1. `η_s ≥ η_t > 0` (`η_v = (1-v) Im m`, `Im m > 0`, `s ≤ t < 1`), so `(η_s/η_t)^30 ≥ 1` and
     `hreg` gives `N^c ≤ scale_t`.
  2. `scale` is antitone on `(-∞,1]` (`flowScale_antitoneOn`, p. 24; `Band.scale` is
     definitionally `flowScale (W N) (L N) E`), `u ≤ t`, so `N^c ≤ scale_t ≤ scale_u`.
  3. `hΨhi` at `a = c/2 > 0`: `scale_u⁻¹ ≤ N^{-c}`, then `(·)^{1/2}` monotone:
     `scale_u^{-1/2} ≤ N^{-c/2}`.
  4. `hη` at `K = 1`: `scale_t = W ℓ_t η_t ≤ W L η_t ≤ N η_t` (`ℓ_t = min((1-t)^{-1/2}, L) ≤ L`,
     `W L ≤ N` from `Dims.dim`), and `1 ≤ N^c ≤ scale_t`, so `N^{-1} ≤ η_t ≤ η_u`
     (`η` antitone, `u ≤ t`).
  5. `hΨlo`: not needed any more ((T1) proves it).
  6. `hll`: `steps12_gauss … |>.localLaw : LocalLawFlow (sample d) E s t`, restricted to the
     singleton `{u N}` by `localLawFlow_singleton_of_localLawFlow` (uses `hu`), then
     `localLawUnifIcc_of_localLawFlow` with the trivial majorant on `Icc (u N) (u N)`.
  All of this is honest arithmetic; no hypothesis is added, weakened or strengthened.
* Quantifier order: `d, κ, E, c, s, t, u` fixed before `StochDom`. `a, K` are now chosen
  inside the proof as functions of `c` only.
* Boundary: `u = s` (then already `hB.LmK 1`) and `u = t` allowed; the content is `u ∈ (s,t]`.
* Satisfiability: no new hypothesis beyond `steps12_gauss`'s (audited PASS for T1524) and `hu`
  (satisfied by `u := t`, `⟨hst N, le_rfl⟩`); witness as in (T1).
* Dependencies: `steps12_gauss` (T1524, merged) and (T1). `steps12_gauss` transitively uses
  14 APrime modules and some `MomentDuhamel`-namespace **definitions** (`EEpath`, `eeFun`,
  `lkFun`); this is a pre-existing property of the merged T1524, admissible under §10b
  (its own signature is general `Dims`, the usual Step 2 Gaussian hypotheses, no
  `exampleGrow`). Every APrime declaration in the chain is listed in §(b), with the forbidden
  items checked separately.
* Verdict: **PASS**.

### (T3) axioms and amended dependency criterion

* Criterion (amended): neither target's transitive closure may contain `RBM.MomentDuhamel.Hyp`,
  `RBM.Step2.Hyp`, `RBM.EarlyQVRateEv.jStar*`, the `gmOfJS`-`h560` theorems
  (`Step2FarInputs.h535_of_jS`, `Step2FarInputs.eGpm_le_rhs535_of_jS`, `Step2FarInputs.gmOfJS`),
  or any `exampleGrow` constant; all APrime constants used must be listed.
* Pre-check on the route (real script output, §(b)): `detAvgIBP_stochDom_of_localLaw_complete`
  and `highProb_detFlucDelta_of_localLaw`: 0 forbidden hits, 1 APrime constant
  (`goodSetFlow`); `steps12_gauss`: 0 forbidden hits.
* Verdict: **PASS** (final numbers on the new theorems in §(b)).

## (b) Lean: declarations, build, axioms, closure

Branch `t/T1527`, commit `854e777` (on top of `41f1bc5`); sole file
`RBM1D/Gauss/OneLoopSharpGrid.lean`.

### Declarations (namespace `RBM.Gauss`)

* `scale_mul_inv_rpow_half_sq` (unchanged): `scale_u · (Ψ_u · Ψ_u) = 1`, `Ψ_u = scale_u⁻¹^{1/2}`.
* `W_rpow_neg_half_le_scale_inv_rpow_half` (new): `W^{-1/2} ≤ scale_u⁻¹^{1/2}` for `0 ≤ u < 1`.
* `band_scale_antitone` (new): `u ≤ v ≤ 1 → scale_v ≤ scale_u`.
* `eventually_regime_of_hreg` (new): from `hreg`, `hst`, `ht1`, `hc0`, `hu`:
  `∀ᶠ N, N^c ≤ scale_{u_N} ∧ N^{-1} ≤ η_{u_N}`.
* `scale_inv_rpow_half_le_of_rpow_le` (new): `1 ≤ N`, `N^c ≤ scale_u` ⟹ `scale_u⁻¹^{1/2} ≤ N^{-(c/2)}`.
* `stochDom_lkMax_one_of_localLaw` **(T1)**, final signature:
  ```
  theorem stochDom_lkMax_one_of_localLaw {E κ : ℝ} {u : ℕ → ℝ} {a K : ℝ}
      (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
      (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
      (ha : 0 < a) (hK : 0 ≤ K)
      (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
      (hΨhi : ∀ᶠ N : ℕ in atTop,
        ((band d).scale E N (u N))⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-a))
      (hll : LocalLawUnifIcc d E u u (fun N => ((band d).scale E N (u N))⁻¹ ^ (1 / 2 : ℝ))) :
      StochDom (P d)
        (fun N (_ : Unit) ω => (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1)
        (fun _ _ _ => (1 : ℝ))
  ```
* `localLawFlow_singleton_of_localLawFlow` (unchanged).
* `stochDom_lkMax_one_of_steps12` **(T2)**, final signature (exactly `steps12_gauss`'s list + `hu`):
  ```
  theorem stochDom_lkMax_one_of_steps12 {κ E c : ℝ} {s t u : ℕ → ℝ}
      (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
      (hB : BoundsCore (sample d) E s)
      (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
      (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
        (band d).scale E N (t N))
      (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
      StochDom (P d)
        (fun N (_ : Unit) ω => (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1)
        (fun _ _ _ => (1 : ℝ))
  ```
  `steps12_gauss`'s signature (`Step2Close.lean:541`): `hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg`,
  identical binders. The previous extra binders `a K ha hK hη hΨlo hΨhi` are gone.

### Build

`cd /Users/junyin/Lean_proof/RBM1D-wt/T1527 && lake build RBM1D.Gauss.OneLoopSharpGrid`:
```
ℹ [3967/3967] Built RBM1D.Gauss.OneLoopSharpGrid (4.1s)
info: RBM1D/Gauss/OneLoopSharpGrid.lean:252:0: 'RBM.Gauss.stochDom_lkMax_one_of_localLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/Gauss/OneLoopSharpGrid.lean:253:0: 'RBM.Gauss.stochDom_lkMax_one_of_steps12' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3967 jobs).
```
No warnings from this file. No `sorry` / `admit` / `axiom` (grep empty). Root `RBM1D.lean` not
touched (import added at merge).

### Axioms (helpers, via `lake env lean` on the closure script after the build)
```
'RBM.Gauss.W_rpow_neg_half_le_scale_inv_rpow_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.band_scale_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.eventually_regime_of_hreg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.scale_inv_rpow_half_le_of_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.scale_mul_inv_rpow_half_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.localLawFlow_singleton_of_localLawFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Transitive closure (T3), real output

Script (scratch, not committed; run as `lake env lean Run2.lean` in the worktree after the
module build, `Run2.lean` = the script below followed by `#cclosure <name>` / `#aprimeList <name>`
lines). BFS over each constant's type, value (definitions, theorems, opaques), inductive
constructors, constructor parent, recursor rules. Flags: `RBM.MomentDuhamel.Hyp*`,
`RBM.Step2.Hyp*`, `RBM.EarlyQVRateEv.*jStar*`, any `exampleGrow` component, and the
`gmOfJS`-`h560` theorems `h535_of_jS` / `eGpm_le_rhs535_of_jS` / `gmOfJS`; separately lists every
constant whose type binds a variable named `h560`, every name with a `jStar` component, every
constant defined in an `APrime*` module, and `MomentDuhamel` constants.

Positive controls (same script): `RBM.Step2FarInputs.h535_of_jS` → 3 forbidden hits
(`eGpm_le_rhs535_of_jS`, `gmOfJS`, `h535_of_jS`); `RBM.Gauss.detAvgIBP_firstCell_witness` → 5
forbidden hits (`Dims.exampleGrow` and its `_proof_i`). So the detector fires when it should.

Output on the final constants:
```
RBM.Gauss.stochDom_lkMax_one_of_localLaw: closure=57681
  forbidden hits=0: []
  types binding h560=0: []
  all names with component jStar=0: []
  APrime-module constants=1, modules=[RBM1D.Gauss.APrimeGeneralMovingCarrierCore]
  MomentDuhamel constants=0: []
RBM.Gauss.stochDom_lkMax_one_of_steps12: closure=70142
  forbidden hits=0: []
  types binding h560=9: [RBM.Gauss.Grid.eG_le_reduced_of_schwarz',
 RBM.Lemma57.sum_far_le,
 RBM.Gauss.Grid.eGpm_le_rhs535',
 RBM.Gauss.Grid.eG_le',
 RBM.Gauss.Grid.eGpm_le_reduced',
 RBM.Lemma57.eG_far_le,
 RBM.Gauss.Grid.drift_point_le',
 RBM.Gauss.Grid.eG_le_reduced',
 RBM.Lemma57.case2_pointwise]
  all names with component jStar=5: [RBM.Step2.jStar,
 RBM.Step2.jStar._proof_1,
 RBM.Step2.jStar._proof_2,
 RBM.Step2.jStar.congr_simp,
 RBM.Step2.jStar.eq_1]
  APrime-module constants=169, modules=[RBM1D.Gauss.APrimeGoodSetFlowGeneralDims,
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
 RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore,
 RBM1D.Gauss.APrimeJG,
 RBM1D.Gauss.APrimeFullQV]
  MomentDuhamel constants=5: [RBM.Gauss.genD_eq_sum_pairs,
 RBM.Gauss.sum_used_eq_sum_pairs_coordD2_pt,
 RBM.MomentDuhamel.EEpath,
 RBM.MomentDuhamel.eeFun,
 RBM.MomentDuhamel.lkFun]
RBM.Gauss.eventually_regime_of_hreg: closure=48223
  forbidden hits=0: []
  types binding h560=0: []
  all names with component jStar=0: []
  APrime-module constants=0, modules=[]
  MomentDuhamel constants=0: []
RBM.Gauss.W_rpow_neg_half_le_scale_inv_rpow_half: closure=48187
  forbidden hits=0: []
  types binding h560=0: []
  all names with component jStar=0: []
  APrime-module constants=0, modules=[]
  MomentDuhamel constants=0: []
```

Interpretation:
* `MomentDuhamel.Hyp`, `Step2.Hyp`: **absent** from both closures.
* `EarlyQVRateEv.jStar`: **absent**. The only `jStar` names are `RBM.Step2.jStar` (paper (5.29),
  defined in `APrimeSmoothPrefixCanonicalCore`) and its auxiliary equations, reached via
  `steps12_gauss → step2_gauss → gridPointwise'_gauss → grid_thr_improve → jSMat_le_of_Agrid →
  Step2.jStar_le → Step2.jStar`. Not the flagged `EarlyQVRateEv.jStar` (TASKS 待查 (a)).
* `h560` (the `gmOfJS` one): **absent** (`h535_of_jS`, `eGpm_le_rhs535_of_jS`, `gmOfJS` not in
  either closure). The 9 constants whose types bind a variable named `h560` are the generic
  Lemma 5.7 statements (`Lemma57.eG_far_le`, `sum_far_le`, `case2_pointwise`) and their grid
  wrappers (`Grid.eG_le'`, `eG_le_reduced'`, `eG_le_reduced_of_schwarz'`, `eGpm_le_reduced'`,
  `eGpm_le_rhs535'`, `drift_point_le'`), all reached through
  `drift_of_goodSet → drift_point_le_heG → drift_point_le_blk' → drift_point_le'`;
  `drift_point_le_blk'` discharges that `h560` by proof with `Gm := DriftPt.gmBlkM` (T1501
  "option B", `GridDriftPoint.lean:606`), so it is proved, not assumed, and not the
  `gmOfJS` form shown unsatisfiable by T1499.
* `exampleGrow`: **absent** from both closures.
* `MomentDuhamel` constants in (T2): `RBM.MomentDuhamel.EEpath`, `eeFun`, `lkFun` (definitions)
  and `RBM.Gauss.genD_eq_sum_pairs`, `sum_used_eq_sum_pairs_coordD2_pt` (module-located), all via
  the merged `steps12_gauss`; no `MomentDuhamel.Hyp`. None in (T1).
* The previous report's closure figures (4963/4961/4412/4599, 0 hits) were false and are
  withdrawn; the real sizes are 57681 (T1) and 70142 (T2).

### APrime declarations actually used (DECISIONS §10b list)

(T1), 1 constant — a hypothesis-free fixed-time set definition, general `Dims`:
```
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.Gauss.goodSetFlow [def]
```

(T2), 169 constants in 14 modules (133 theorems / `_proof_i`, 33 definitions, rest auxiliary),
all entering only through the merged `steps12_gauss` (T1524). Every one is applied inside a
proof term, so its hypotheses are discharged there; the only open hypotheses of (T2) are
`steps12_gauss`'s own (general `Dims`) plus `hu`. No `exampleGrow` constant occurs in the
closure (compiled check above), so none of them is an `exampleGrow`-only result. The 7
constants from `APrimeSmoothPrefixCanonicalCore` are the Step 2 core definitions
`Step2.jS`, `Step2.jStar` (5.29), `Step2.lk`, `Step2.sigPM`, `Step2.tT` (+2 `_proof_i`), not
smooth-prefix-weight cross terms.
```
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics [ind]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hB [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hK [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hT [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hcard [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hlen [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hst [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hγ [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.hδ [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.NetNumerics.mk [ctor]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.W_inv_le_q [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.centeredEvent [def]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.centeredTrace_false_stochDom_of_true [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.centeredTrace_twoCharge_stochDom_timeIcc [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.centeredTrace_unifDomIcc [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.clampTime [def]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.clampTime_eq [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.clampTime_mem [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.control [def]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.control._proof_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.control.eq_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.eventually_control_lower [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.eventually_inv_le_q [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.eventually_net_spacing_le [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.eventually_net_spacing_le._proof_1_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.eventually_qExt_short_time_comparable [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.eventually_qExt_short_time_comparable._proof_1_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.highProb_centeredEvent [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.meshSpacing [def]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.meshSpacing._proof_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.meshSpacing.eq_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.netNumerics [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.net_exponent_eq [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.q [def]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.qExt [def]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.qExt.eq_1 [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.qExt_eq_q [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.qExt_eq_selectorQ [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.qExt_nonneg [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.qExt_pos [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.q_eq_inv [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.q_eq_selectorQ [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.q_le_two_mul_of_abs_sub_le [thm]
RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims :: RBM.APrimeAllTimeOneLoopGeneralDims.q_pos [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.centeredTrace [def]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.centeredTrace.eq_1 [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.centeredTrace_false_eq_conj_true [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.eventually_centeredTrace_sub_le [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.eventually_centeredTrace_true_sub_le [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.eventually_centeredTrace_true_sub_le._abel_1_3 [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.eventually_centeredTrace_true_sub_le._proof_1_1 [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.highProb_normGood [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: RBM.APrimeCenteredModulusGeneralDims.normGood [def]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: _private.RBM1D.Gauss.APrimeCenteredModulusGeneralDims.0.RBM.APrimeCenteredModulusGeneralDims.eventually_endpoint_etaT_inv_le_sq [thm]
RBM1D.Gauss.APrimeCenteredModulusGeneralDims :: _private.RBM1D.Gauss.APrimeCenteredModulusGeneralDims.0.RBM.APrimeCenteredModulusGeneralDims.eventually_endpoint_etaT_inv_le_sq._proof_1_1 [thm]
RBM1D.Gauss.APrimeDuhamel :: RBM.Gauss.sqrt_wsum_add_le [thm]
RBM1D.Gauss.APrimeFixedOneLoopGeneralDims :: RBM.APrimeFixedOneLoopGeneralDims.centered_block_trace_stochDom [thm]
RBM1D.Gauss.APrimeFixedOneLoopGeneralDims :: RBM.APrimeFixedOneLoopGeneralDims.localLawUnifIcc_of_selector_llErr [thm]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.SourceEvent [ind]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.SourceEvent.four [thm]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.SourceEvent.mk [ctor]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.SourceEvent.six [thm]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.early_raw_full [thm]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.early_raw_full._proof_1_1 [thm]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.early_raw_full._proof_1_2 [thm]
RBM1D.Gauss.APrimeFullQV :: RBM.APrimeFullQV.sourceEvent_of_step1 [thm]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.gmBlk [def]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.gmBlk._proof_1 [thm]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.gsqBlk [def]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.gsqBlk._proof_1 [thm]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.jG [def]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.jG._proof_1 [thm]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.APrimeJG.jG._proof_2 [thm]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.Gauss.flowDelta [def]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.Gauss.flowDelta._proof_1 [thm]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.Gauss.goodSetFlow [def]
RBM1D.Gauss.APrimeGeneralMovingCarrierCore :: RBM.Step1.aprioriRhs [def]
RBM1D.Gauss.APrimeGoodSetFlowGeneralDims :: RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow [thm]
RBM1D.Gauss.APrimeGoodSetFlowGeneralDims :: RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow_of_step1 [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.eventually_Lre_le_jS_mul_tailT_quarter [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.eventually_twelve_le_ellStar [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.far_neighbor_not_support [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.far_neighbor_not_support._proof_1_1 [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.far_neighbor_not_support._proof_1_2 [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gmBlk_le_inv_etaT [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gmBlk_mul_le_of_sq_le [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gmBlk_mul_swap_le_gsqBlk [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gmBlk_nonneg [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gmBlk_row_le_gsqBlk [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gmBlk_sq_le_of_entry_sq_le [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gsqBlk_le_inv_etaT_sq [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gsqBlk_le_jG_mul_tailT [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.gsqBlk_nonneg [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.jG_le_of_neighbor_green_sq [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.mem_sbSupport_of_SB_ne_zero [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.neighbor_green_sq_le_of_entry_event [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.norm_Gsig_eq_green_or_swap [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.norm_Gsig_le_gmBlk [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.one_le_jG [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.shifted_pair_dist_ge [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.shifted_pair_dist_ge._proof_1_1 [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.shifted_pair_far [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.shifted_pair_far._proof_1_1 [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.sum_shifted_control_le_jS_tail [thm]
RBM1D.Gauss.APrimeJG :: RBM.APrimeJG.tailT_shift_three [thm]
RBM1D.Gauss.APrimeJG :: _private.RBM1D.Gauss.APrimeJG.0.RBM.APrimeJG.SB_diag_ne_zero [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.APrimeQVEndpoint.diagShape' [def]
RBM1D.Gauss.APrimeNearRem :: RBM.APrimeQVEndpoint.diagShape'._proof_1 [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.eeL6_le_nearFar [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.eeL6_near_remainder [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.ee_le_EEpath_sym' [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.ellStarStar_ge_nine_halves_ellStar [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.exp_nearFar_le_floor [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.nearEpsilon [def]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.nearEpsilon._proof_1 [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.nearEpsilon._proof_2 [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.nearEpsilon._proof_3 [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.nearEpsilon_le_inv [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EEDef.nearRem_of_nearFar [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym' [thm]
RBM1D.Gauss.APrimeNearRem :: RBM.Lemma57.ee_le_sym' [thm]
RBM1D.Gauss.APrimeQVEndpoint :: RBM.APrimeQVEndpoint.diagFarRate [def]
RBM1D.Gauss.APrimeQVEndpoint :: RBM.APrimeQVEndpoint.diagNearRate [def]
RBM1D.Gauss.APrimeQVEndpoint :: RBM.APrimeQVEndpoint.diagShape._proof_1 [thm]
RBM1D.Gauss.APrimeQVEndpoint :: RBM.APrimeQVEndpoint.diagShape._proof_3 [thm]
RBM1D.Gauss.APrimeQVEndpoint :: RBM.APrimeQVEndpoint.diagShape._proof_4 [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.general_moving_raw_sources [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.general_moving_raw_sources._proof_1_1 [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.highProb_sourceGood [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.measurableSet_sourceGood [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.normGood [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.rawEvent [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.rawThree_on_sourceGood [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceC3 [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceC4 [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceC6 [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceEll [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceEll._proof_1 [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceEll._proof_2 [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceEvent_on_sourceGood [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceGood [def]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: RBM.APrimeRawSourcesGeneralDims.sourceGood_subset_normGood [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: _private.RBM1D.Gauss.APrimeRawSourcesGeneralDims.0.RBM.APrimeRawSourcesGeneralDims.rawEvent_isClosed [thm]
RBM1D.Gauss.APrimeRawSourcesGeneralDims :: _private.RBM1D.Gauss.APrimeRawSourcesGeneralDims.0.RBM.APrimeRawSourcesGeneralDims.source_level_identity [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.W_inv_le_selectorQ [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.W_inv_sqrt_le_selectorPsi [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.W_rpow_neg_half_le_selectorPsi [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.eventually_selectorPsi_le [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.eventually_selectorPsi_le._proof_1_1 [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.eventually_selectorQ_le [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.eventually_selectorQ_le._proof_1_1 [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.eventually_selector_eta_floor [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.eventually_selector_eta_floor._proof_1_1 [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.general_moving_singleton_localLaw [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.llMax_sq_stochDom [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.selectorPsi [def]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.selectorQ [def]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.selectorQ_nonneg [thm]
RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims :: RBM.APrimeSingletonLocalLawGeneralDims.selector_llErr_stochDom [thm]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.jS [def]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.jStar [def]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.jStar._proof_1 [thm]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.jStar._proof_2 [thm]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.lk [def]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.sigPM [def]
RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore :: RBM.Step2.tT [def]
RBM1D.Gauss.APrimeTwoChargeOneLoop :: RBM.APrimeTwoChargeOneLoop.centered_block_trace_false_eq_conj_true [thm]
```

<details><summary>Closure script (Closure.lean)</summary>

```lean
import RBM1D.Gauss.OneLoopSharpGrid
open Lean Meta Elab Command

/-- All constants directly referenced by a constant: type, value (incl. opaque/theorem),
constructors of inductives, parent inductive of constructors, recursor rules. -/
def directDeps (ci : ConstantInfo) : Array Name := Id.run do
  let mut out : NameSet := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo v => out := out.union v.value.getUsedConstantsAsSet
  | .thmInfo v => out := out.union v.value.getUsedConstantsAsSet
  | .opaqueInfo v => out := out.union v.value.getUsedConstantsAsSet
  | .inductInfo v => for c in v.ctors do out := out.insert c
  | .ctorInfo v => out := out.insert v.induct
  | .recInfo v =>
      out := out.insert v.getMajorInduct
      for r in v.rules do out := out.union r.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return out.toArray

/-- Does the expression bind a variable named `h560`? -/
partial def bindsH560 : Expr → Bool
  | .forallE n t b _ => n == `h560 || bindsH560 t || bindsH560 b
  | .lam n t b _ => n == `h560 || bindsH560 t || bindsH560 b
  | .letE n t v b _ => n == `h560 || bindsH560 t || bindsH560 v || bindsH560 b
  | .app f a => bindsH560 f || bindsH560 a
  | .mdata _ e => bindsH560 e
  | .proj _ _ e => bindsH560 e
  | _ => false

def hasComp (n : Name) (s : String) : Bool := n.components.any (·.toString == s)

def isForbidden (n : Name) : Option String :=
  if n == `RBM.MomentDuhamel.Hyp || (`RBM.MomentDuhamel.Hyp).isPrefixOf n then some "MomentDuhamel.Hyp"
  else if n == `RBM.Step2.Hyp || (`RBM.Step2.Hyp).isPrefixOf n then some "Step2.Hyp"
  else if (`RBM.EarlyQVRateEv).isPrefixOf n && hasComp n "jStar" then some "EarlyQVRateEv.jStar"
  else if hasComp n "exampleGrow" then some "exampleGrow"
  else if hasComp n "h535_of_jS" || hasComp n "eGpm_le_rhs535_of_jS" || hasComp n "gmOfJS" then some "h560-theorem"
  else none

def constClosure (env : Environment) (root : Name) : NameSet × Std.HashMap Name Name := Id.run do
  let mut seen : NameSet := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut stack : Array Name := #[root]
  seen := seen.insert root
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if let some ci := env.find? n then
      for m in directDeps ci do
        if !seen.contains m then
          seen := seen.insert m
          parent := parent.insert m n
          stack := stack.push m
  return (seen, parent)

def pathTo (parent : Std.HashMap Name Name) (root n : Name) : List Name := Id.run do
  let mut acc : List Name := [n]
  let mut cur := n
  for _ in [0:200] do
    if cur == root then break
    match parent.get? cur with
    | some p => acc := p :: acc; cur := p
    | none => break
  return acc

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `current

elab "#cclosure " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  let (seen, parent) := constClosure env root
  let mut forb : Array (Name × String) := #[]
  let mut h560 : Array Name := #[]
  let mut jstarAll : Array Name := #[]
  let mut aprime : Array Name := #[]
  let mut aprimeMods : NameSet := {}
  let mut mdConsts : Array Name := #[]
  for n in seen.toArray do
    if let some tag := isForbidden n then forb := forb.push (n, tag)
    if hasComp n "jStar" then jstarAll := jstarAll.push n
    if let some ci := env.find? n then
      if bindsH560 ci.type then h560 := h560.push n
    let m := modOf env n
    if (m.toString.splitOn "APrime").length > 1 then
      aprimeMods := aprimeMods.insert m
      aprime := aprime.push n
    if (m.toString.splitOn "MomentDuhamel").length > 1 || hasComp n "MomentDuhamel" then
      mdConsts := mdConsts.push n
  logInfo m!"{root}: closure={seen.size}\n  forbidden hits={forb.size}: {forb.toList}\n  types binding h560={h560.size}: {h560.toList}\n  all names with component jStar={jstarAll.size}: {jstarAll.qsort (·.toString < ·.toString) |>.toList}\n  APrime-module constants={aprime.size}, modules={aprimeMods.toList}\n  MomentDuhamel constants={mdConsts.size}: {mdConsts.qsort (·.toString < ·.toString) |>.toList}"
  for (n, _) in forb do
    logInfo m!"  path to {n}: {pathTo parent root n}"

elab "#aprimeList " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  let (seen, _) := constClosure env root
  let mut lines : Array String := #[]
  for n in seen.toArray do
    let m := modOf env n
    if (m.toString.splitOn "APrime").length > 1 then
      if let some ci := env.find? n then
        let kind := match ci with
          | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind"
          | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | _ => "other"
        lines := lines.push s!"{m} :: {n} [{kind}]"
  let sorted := lines.qsort (· < ·)
  logInfo m!"{root}: APrime-module constants ({sorted.size}):\n{String.intercalate "\n" sorted.toList}"
```
</details>

## (c) Key lemmas used

`detAvgIBP_stochDom_of_localLaw_complete` (`DetAvgIBPFlow.lean:274`; internally
`highProb_detFlucDelta_of_localLaw`, `DetFlucThreshold.lean:322`, discharges `hΩ`),
`lkErr_one_eq_norm_trace` (`Eq45Flow.lean:89`), `steps12_gauss` (`Step2Close.lean:541`),
`localLawUnifIcc_of_localLawFlow` (`GoodSetFlow.lean:230`), `StochDom.precomp_param`,
`Band.scale_pos'`, `Grid.DriftPt.scale_le_W` (`GridDriftPoint.lean:2787`),
`flowScale_antitoneOn` (`Flow/Scales.lean:100`), `ellHat_ofReal`, `etaT_pos_of_lt_one'`,
`mE_im_pos`, `Band.dim`, `exists_lt_of_lt_ciSup`.

## (d) Open issues

* `hΩ`: discharged by the existing producer `highProb_detFlucDelta_of_localLaw` (already inside
  the ticket-mandated route); no new lemma was needed. The residual APrime-location dependency of
  (T1) is the definition `RBM.Gauss.goodSetFlow` only; relocating it to a non-APrime module is
  a cosmetic follow-up outside this ticket's file scope.
* The satisfiability witness in (a) is a paper argument (as in the audit §3), not compiled.
* (T2)'s A'-era dependencies are exactly those of the merged `steps12_gauss`; this ticket adds
  none. A per-declaration §10b re-audit of T1524's 169 APrime constants, if wanted, belongs to a
  T1524-level ticket.
* No paper delta: (T1)/(T2) are Lemma 4.1 (4.5) + (2.76) at `n = 1` at one grid time; no
  statement difference beyond the documented `Unit` index.
