Prover model: claude-sonnet-5

# T1497 (amend-1): M6 restated with a per-`u` `jS`-cap premise

This revision **supersedes** the previous report (`docs/reports/T1497-prove.md`, prover model
`claude-sonnet-5`, BLOCKED verdict for the unconditional M6). That report is read in full and
its findings are reused rather than re-derived: the exact "filled-in statement" of M6 (§(a),
the `nearEpsilon`/`sDet` argument instantiation), the deterministic side-condition analysis of
`early_raw_full` ("Secondary finding"), and the identification of
`highProb_jG_le_of_entryBoundFlow` as the only `D`-independent route to `hJcap`. What that
report could not close — `hJcap : jG ≤ N` unconditionally — is exactly what the amended
ticket's per-`u` premise `jS ≤ N^{1/2}` unlocks.

## 0. Method

Sources read, per the amended ticket's "Required reading" (= T1497.md's, restated in the
amend-1 ticket) plus `CLAUDE.md` §3:
- `docs/tickets/T1497-amend-1.md`, `docs/tickets/T1497.md`, `docs/reports/T1497-prove.md`
  (previous BLOCKED revision, read in full before writing anything).
- `docs/reports/T1488-prove.md` §2 (rows A3, B1–B3) and §3 (target M6).
- In full, the bodies of the Lean files the M6/T1497 route cites, in the `t/T1497` worktree
  (branched from `main` at `a3e7e36`, T1493's merge commit, confirmed present):
  `RBM1D/Gauss/APrimeFullQV.lean` (`SourceEvent`, `sourceEvent_of_step1`, `early_raw_full`),
  `RBM1D/Gauss/APrimeJG.lean` (`jG`, `one_le_jG`, `highProb_jG_le_of_entryBoundFlow`),
  `RBM1D/Gauss/APrimeQVEndpoint.lean` / `RBM1D/Gauss/APrimeNearRem.lean`
  (`diagShape'`, `diagNearRate`, `diagFarRate`, `nearEpsilon`, `nearEpsilon_le_inv`),
  `RBM1D/Gauss/EarlyQVRateEv.lean` (`sDet`, `sDet_nonneg`; confirmed `jStar` is a different,
  syntactically distinct declaration, not touched),
  `RBM1D/Gauss/EntryBoundTime.lean` (`step1Hyp_gauss_of_scale''`, `entryBoundFlow_floor`,
  `rpow_neg_one_le_etaT_of_scale_ge`, `flowDelta_le_rpow_neg`),
  `RBM1D/Gauss/FlowHolder.lean` (`RBM.Gauss.etaT_le_of_le`),
  `RBM1D/Hierarchy/Step1.lean` (`eventually_scale_facts`),
  `RBM1D/Hierarchy/Step2.lean` (`Step2.jS`, `eventually_le_W_sq`),
  `RBM1D/Hierarchy/EEBridge.lean` (`eeFacts`),
  `RBM1D/Gauss/APrimeRawSourcesGeneralDims.lean` (`sourceEll`, `sourceC4`, `sourceGood`,
  `general_moving_raw_sources_of_scale` — **already discharges the `SourceEvent` for general
  `d : Dims`**, with the exact shrunk reference length that `early_raw_full`'s `h6level`
  needs; this is the piece the previous BLOCKED report flagged as unresolved ("no such
  monotonicity lemma exists yet") but had not located),
  `RBM1D/Gauss/APrimeGoodSetFlowGeneralDims.lean` (`highProb_goodSetFlow`, taking
  `Cond272Reg` + `BoundsCore` directly, no `Step1.Hyp` construction needed by the caller),
  `RBM1D/Gauss/APrimeGeneralMovingDriftSourceGeneralDims.lean` (`highProb_commonEvent`,
  `blockEvent` — the accepted usage pattern of `highProb_jG_le_of_entryBoundFlow` for general
  `d`, confirming `hEntry`/`hGood` are dischargeable from the Step-1 hypotheses alone),
  `RBM1D/Gauss/APrimeGeneralMovingQVProfile.lean` (`eventually_qv_profile_on_common_support` —
  a **fixed-`d = Dims.exampleGrow`** assembly that already derives every deterministic side
  condition of `early_raw_full`/`qvAt_full_absorbed` (`hW, hlog4, hlog, heta, hAu, hAN, hWL,
  hNW`) from `Step1.eventually_scale_facts`, `Gauss.rpow_neg_one_le_etaT_of_scale_ge`,
  `Band.eventually_le_W`, `Step2.eventually_le_W_sq`, `Dims.dim`; this report reuses exactly
  that derivation pattern, generalized to arbitrary `d : Dims` — none of the ingredients it
  uses are themselves specific to `exampleGrow`, only the file's own private `abbrev d`
  fixation was, so it is not itself usable and is **not cited as a target**, only as a
  worked example of the deterministic bookkeeping).
- The declarations used were confirmed to exist with the stated signatures by direct
  `grep -n` + `Read`, and the final Lean file was `lake build`-checked (below), which is a
  strictly stronger verification than `#check`.

All Lean edits are confined to the ticket's sole writable file, `RBM1D/Gauss/Step2QVEvent.lean`
(new file), on branch `t/T1497` in the worktree `~/Lean_proof/RBM1D-wt/T1497`.

## (a) Math preflight

### Target (T1) `RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS`

**Statement** (as in the ticket, filled in per the previous report's already-verified
instantiation of `nearEpsilon`/`sDet`, with the `jS`-cap premise added):
```
theorem highProb_quadVar_diagShape_of_jS (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {κ c : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 (band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N, (N:ℝ)^c ≤ (band d).scale E N (t N)) {D : ℝ} (hD : 60 ≤ D) :
    ∀ τ : ℝ, 0 < τ →
      HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
        Step2.jS (sample d) E D N u ω ≤ (N:ℝ)^(1/2:ℝ) →
        ∀ a : LoopArg (d.L N) 2,
          quadVar (band d).toDims N (fun M' => MomentDuhamel.lkFun (band d) E N u M'
              Step2.sigPM a) (Hflow d N u ω) ≤
            (N:ℝ)^τ * APrimeQVEndpoint.diagShape' (band d) N ℓ_u ℓ_s η_u D
              (APrimeJG.jG (sample d) E N u ω ℓ_u η_u D)
              (EarlyQVRateEv.sDet (band d) E N u ℓ_s)
              (EEDef.nearEpsilon (band d).W N (band d).L N ℓ_u η_u D
                (APrimeJG.jG (sample d) E N u ω ℓ_u η_u D)) a})
```
with `ℓ_u := (band d).ell N u`, `ℓ_s := (band d).ell N (s N)`, `η_u := etaT E u` — identical to
the previous report's "Filled-in statement" for the unconditional M6, with the RHS of the event
wrapped in `Step2.jS (sample d) E D N u ω ≤ (N:ℝ)^(1/2:ℝ) → ...` as item 7 of the amended
ticket specifies.

**Step 0 checks, all PASS (mostly reused from the previous report, re-verified):**
- Hypothesis list is exactly the Step-1 hypotheses (`step1Hyp_gauss_of_scale''`'s list) plus
  `{D : ℝ} (hD : 60 ≤ D)`, unavoidable because `D` occurs free in the conclusion and every
  source lemma (`early_raw_full`, `sourceEvent_of_step1`) requires `60 ≤ D`. The *only* new
  hypothesis relative to the unconditional M6 is the per-`u` implication premise
  `jS ≤ N^{1/2}` — confirmed by direct comparison of the two hypothesis lists (acceptance
  criterion 1).
- Simultaneous satisfiability of the Step-1 hypotheses (+ `D := 60`) is established in
  `docs/reports/T1488-prove.md` §3 (`eventually_commonEvent_nonempty`) and re-confirmed here:
  `general_moving_raw_sources_of_scale`'s own construction (`APrimeRawSourcesGeneralDims.lean`)
  builds `HighProb` events under exactly this hypothesis list for arbitrary `d`, `E`, `s`, `t`
  satisfying it — a "witness exists" statement is not vacuous only if the antecedent list is
  jointly realizable, which the accepted `Dims.exampleGrow`/`E = 0` construction (used
  throughout the already-merged general-`Dims` files cited above) already exhibits. Adding the
  premise `jS ≤ N^{1/2}` inside the conclusion's implication does not add a new hypothesis to
  discharge — the conclusion remains true (vacuously on `{jS > N^{1/2}}`, non-vacuously
  whenever `jS ≤ N^{1/2}` holds, which happens with positive probability since `jS ≥ 1` always
  — `Step2Moment.one_le_jS` — so the premise is a *nontrivial, satisfiable* per-`u` condition,
  not one that is never met) (acceptance criterion 4).
- `diagShape'`/`sDet` reuse: unchanged from the previous report — `diagShape'`, `diagNearRate`,
  `diagFarRate`, `sDet` depend only on `B, N, ℓu, ℓs, ηu, D, J, Smax` and deterministic
  `Lemma57`/`tailT`/`ellStar` data, no smooth-prefix weight (`softMax`/`cutProd`/`χ`/`Θ`)
  anywhere — legitimate reuse under DECISIONS §10b.
- `EarlyQVRateEv.jStar` is not used anywhere in this file (`grep -n jStar
  RBM1D/Gauss/Step2QVEvent.lean` returns nothing) (acceptance criterion 3).
- The exponent `1/2` is exactly enough for `hJcap` (acceptance criterion 2, verified
  quantitatively below) — not more, not less: `highProb_jG_le_of_entryBoundFlow` gives, for any
  fixed `τ' > 0`, `jG ≤ 1 + N^τ'(9 e^{√3} jS + 2)` w.h.p.; with `jS ≤ N^{1/2}` this is
  `≤ 1 + 9 e^{√3} N^{τ'+1/2} + 2 N^{τ'}`, which is `≤ N` eventually **iff** `τ' + 1/2 < 1`,
  i.e. iff the cap exponent is `< 1/2` room below `1`. Fixing `τ' := 1/4` (any value in
  `(0, 1/2)` works) gives `τ' + 1/2 = 3/4 < 1`, so the bound holds eventually — this is the
  content of the new lemma `eventually_jcap_bound` below. A cap of `N^{θ}` for `θ ≥ 1` would
  make `τ' + θ ≥ 1` for every `τ' > 0`, so `1/2` is the sharp edge (any exponent `< 1` works;
  `1/2` is what the ticket asks for and what the paper's stopping-time argument supplies,
  per the ticket's Why-the-restatement note).

**The route that closes (traced in full, then written into Lean):**
1. `hEntry`, `hGood`: exactly as in `APrimeGeneralMovingDriftSourceGeneralDims.highProb_commonEvent`
   — `Gauss.entryBoundFlow_floor` fed by `Gauss.rpow_neg_one_le_etaT_of_scale_ge` and
   `Gauss.flowDelta_le_rpow_neg` (both from `Cond272`/`hreg` alone); `hGood` via
   `APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`, taking `Cond272Reg` + `BoundsCore`
   directly (no separate `Step1.Hyp` construction needed by the caller — it is built
   internally by `highProb_goodSetFlow`/`general_moving_raw_sources_of_scale` themselves).
2. `highProb_jG_le_of_entryBoundFlow d hE hs0 hst ht1 hcond D hD hEntry hGood (τ' := 1/4)` gives
   the high-probability event `jG ≤ 1 + N^{1/4}(9 e^{√3} jS + 2)`.
3. On the intersection of that event with `jS ≤ N^{1/2}` (the target's own per-`u` premise) and
   the eventual numeric fact `eventually_jcap_bound`, `jG ≤ N` — `hJcap`.
4. `SourceEvent`: **already built for general `d : Dims`** by
   `APrimeRawSourcesGeneralDims.general_moving_raw_sources_of_scale`, at the shrunk reference
   length `sourceEll d s ζ N = ℓ_s · (2 N^ζ)^{-1/5}` and inflated block bound
   `sourceC4 d E s ζ N u = N^ζ · sDet (band d) E N u ℓ_s` (verified by `unfold` + `ring`: the
   two definitions are literally the same formula up to associativity). This is exactly the
   "ellSource must be shrunk" step the previous BLOCKED report flagged as needing new work
   ("no such monotonicity lemma exists yet") — it turned out to already exist as an
   already-merged general-`Dims` producer the previous prover did not need to reach (it
   stopped at the `hJcap` blocker first).
5. `early_raw_full` at that shrunk source (with the deterministic side conditions `hW, hlog4,
   hlog, heta, hA, hAN, hWL, hNW` derived exactly as in
   `APrimeGeneralMovingQVProfile.eventually_qv_profile_on_common_support`, generalized from its
   fixed `d = Dims.exampleGrow` to arbitrary `d`) gives
   `quadVar ≤ diagShape'(ℓ_u, ellSource, η_u, D, jG, Smax_used, ε, a)`.
6. **New monotonicity lemmas** (`diagNearRate_ellSource_eq`, `diagFarRate_le_two_mul_of_Smax_scale`,
   `diagShape'_shrink_le`, all in the new file) convert this to
   `≤ (2 N^ζ) · diagShape'(ℓ_u, ℓ_s, η_u, D, jG, sDet, ε, a)`: `diagNearRate` scales by the
   *exact* factor `2 N^ζ` when `ellSource = ℓ_s (2N^ζ)^{-1/5}` (a `ring`-after-`unfold`
   identity); `diagFarRate` is affine in `√Smax` with nonnegative coefficients, and
   `√(N^ζ · sDet) = N^{ζ/2}√sDet ≤ N^ζ√sDet ≤ 2N^ζ√sDet` for `N ≥ 1`, `ζ ≥ 0`, so it scales by
   at most the same `2N^ζ` factor.
7. Choosing `ζ := τ/2` and using `2 N^{τ/2} ≤ N^τ` eventually (`N ≥ 2^{2/τ}`, via
   `RBM.eventually_le_rpow`) absorbs the loss into the target's own `N^τ`, using
   nonnegativity of `diagShape'(ℓ_u, ℓ_s, η_u, D, jG, sDet, ε, a)` (a sum of nonnegative terms,
   `hshape0` below) to multiply the final inequality through.

**Verdict: T1 — PASS.** Written into Lean, built, no `sorry`/`admit`/axiom.

### (T2) `RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS_le`

Convenience corollary: the same conclusion with `Θ N ≤ N^{1/2}` eventually replacing the fixed
`N^{1/2}` cap, obtained from T1 by `HighProb.mono`. **Verdict: PASS** (trivial from T1, same
hypotheses, no new obstruction).

## (b) Declarations added, build, axioms

File: `RBM1D/Gauss/Step2QVEvent.lean` (new; sole writable file for this ticket).

Public declarations:
- `RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS` (T1, as specified).
- `RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS_le` (T2, convenience corollary).

Private helper declarations (not exported, internal to the file):
`ellSource_ratio_pow5_eq`, `diagNearRate_ellSource_eq`, `diagFarRate_le_two_mul_of_Smax_scale`,
`diagShape'_shrink_le`, `eventually_jcap_bound`.

Build:
```
cd ~/Lean_proof/RBM1D-wt/T1497
lake build RBM1D.Gauss.Step2QVEvent
```
Result: `Build completed successfully (3913 jobs).` (rc 0). Only pre-existing style linter
warnings appear (`show`-tactic style, one unused-binder name in a private lemma); no error, no
`sorry`, no `admit`, no `axiom`.

Axioms (`lake env lean` on a scratch file `import RBM1D.Gauss.Step2QVEvent`):
```
'RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jS_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Exactly the three permitted axioms (CLAUDE.md §3.2).

`git status` in the worktree shows exactly one new file, `RBM1D/Gauss/Step2QVEvent.lean`;
nothing else touched. Committed on branch `t/T1497` (see below), only that file.

## (c) Key lemmas used

- `RBM.APrimeFullQV.SourceEvent`, `early_raw_full`.
- `RBM.APrimeJG.jG`, `one_le_jG`, `highProb_jG_le_of_entryBoundFlow`.
- `RBM.Gauss.entryBoundFlow_floor`, `rpow_neg_one_le_etaT_of_scale_ge`, `flowDelta_le_rpow_neg`,
  `etaT_le_of_le`.
- `RBM.APrimeRawSourcesGeneralDims.sourceEll`, `sourceC4`,
  `general_moving_raw_sources_of_scale` (general-`d` `SourceEvent` producer — the piece that
  unblocks the previously-flagged `ellSource`-shrink gap).
- `RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`.
- `RBM.Step1.eventually_scale_facts`; `RBM.Band.eventually_le_W`;
  `RBM.Step2.eventually_le_W_sq`; `RBM.Gauss.Dims.dim`; `RBM.EEBridge.eeFacts`.
- `RBM.APrimeQVEndpoint.diagShape'`, `diagNearRate`, `diagFarRate`; `RBM.EarlyQVRateEv.sDet`,
  `sDet_nonneg`; `RBM.EEDef.nearEpsilon`; `RBM.Lemma57.cNear2_nonneg`, `cFar2_nonneg`.
- `RBM.eventually_le_rpow` (the `N^a → ∞` eventual lower bound, used both for `hJcap`'s numeric
  threshold and for absorbing the `2N^{τ/2}` loss into `N^τ`).
- Reused **without modification**, as worked examples of the deterministic bookkeeping pattern
  (not cited as targets, since they are fixed-`d = Dims.exampleGrow`):
  `RBM.APrimeGeneralMovingDriftSourceGeneralDims.highProb_commonEvent` (accepted usage pattern
  of `highProb_jG_le_of_entryBoundFlow` for general `d`);
  `RBM.APrimeGeneralMovingQVProfile.eventually_qv_profile_on_common_support` (deterministic
  side-condition derivation pattern).

## (d) Open issues

None blocking. Two points for whoever consumes M6 next (A5 assembly):
1. The convenience corollary (T2) is stated with an arbitrary eventually-`N^{1/2}`-dominated
   envelope `Θ`; if the stopping-time argument in §5.3 produces a specific `Θ` (e.g.
   `N^{δ+2/15}` per the ticket's "Why the restatement" note, itself `≤ N^{1/2}` once
   `δ + 2/15 < 1/2`), that specialization is a one-line application of T2, not a new ticket.
2. The private lemma `diagFarRate_le_two_mul_of_Smax_scale` uses the crude bound
   `√(qS) ≤ q√S` (loss factor `2q` for the whole `diagShape'`, not the sharper `√q`) purely to
   keep the near- and far-row scaling factors identical (both `2q = 2N^ζ`) and hence the final
   combination step simple; since the target's `∀ τ > 0` already tolerates any positive loss,
   this crudeness costs nothing and is not itself a defect, but a future ticket wanting the
   *rate* (not just `∀τ>0` qualitative control) at this shape would want the sharper `√q`
   bound for the far row.
