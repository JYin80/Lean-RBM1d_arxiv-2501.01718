Prover model: claude-sonnet-5

# T1502: `hjG`: `jG ≤ N^{2ε} jS` on one high-probability event

2026-09-25T20:53Z (preflight written before any Lean).

## (a) Math preflight

### Step 0 (read-only checks)

- `RBM.Gauss.entry_bound_gauss` (`RBM1D/Gauss/EntryBoundGauss.lean:42`): (4.2) for the Gaussian
  flow `H_u = √u X`, with **no** large-deviation hypothesis (row/column large-deviation
  estimates are theorems for this model). Fixed time `u`, every off-diagonal block pair.
- `RBM.tailT_sub_le` (`RBM1D/Analysis/StretchedExp.lean:337`): `tailT W ℓu ηu D (ℓ-C) ≤
  exp(√C/√ℓu·…)·tailT W ℓu ηu D ℓ`-type shift bound (exact form: shifting the distance by a
  bounded amount costs only a fixed multiplicative constant). Consumed inside
  `RBM.APrimeJG.tailT_shift_three` (shift by 3 costs `exp(√3)`).
- The (5.30) neighbour-`K` bound: not a single named lemma but the floor
  `fl N = 2·N^{-D}` supplied by `RBM.Gauss.entryBoundFlow_floor` (via
  `RBM.Gauss.stochDom_ldeRow_flow_floor`/`stochDom_ldeCol_flow_floor`), which is exactly the
  "neighbour `K ≤ W^{-D}`, floored" input the ticket names.
- `jG`, `gmBlk`, `gsqBlk` (`RBM1D/Gauss/APrimeGeneralMovingCarrierCore.lean`, namespace
  `RBM.APrimeJG`): `gmBlk` = max Green entry between two physical blocks over both charges;
  `gsqBlk x y` = max over the `SB`-neighbours `x'` of `x` of `gmBlk y x' * gmBlk x' y`; `jG` =
  `1 + max` over far pairs `(x,y)` (`ellStar/2 ≤ zdist(x-y)`) of `gsqBlk x y / tailT … (x-y)`.
  Exactly the block-resolved witness of (5.42), matching the ticket's description.
- §10b reuse check: none of `jG`, `gmBlk`, `gsqBlk`, `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow`
  is on the banned list (DECISIONS §10b bans `Step2FarInputs.eGpm_le_rhs535_of_jS`/
  `h535_of_jS`, not this chain).
- **Key finding**: the target chain is already fully assembled and committed as
  `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow` (`RBM1D/Gauss/APrimeJG.lean:569`), proved by
  exactly the steps the ticket names: `jG_le_of_neighbor_green_sq` (`gsqBlk ≤ max gmBlk²`),
  `entry_bound_gauss` assembled along the flow with a floor (`entryBoundFlow_floor`, the (5.30)
  neighbour bound), and the nine shifted terms costing `9·exp(√3)` via `tailT_shift_three`
  (`tailT_sub_le`). Its conclusion is `jG ≤ 1 + N^τ·(9·exp(√3)·jS + 2)`, on the intersection of
  the floored-(4.2) event and the along-flow good event, for `τ` arbitrary `> 0`.
  What T1502 adds is purely the real-analysis absorption of the additive `1` and the constant
  `9·exp(√3)+3` into a single `N^ε` factor, using `1 ≤ jS` (`RBM.Step2Moment.one_le_jS`) and
  `N^ε → ∞` (`RBM.eventually_le_rpow`).

### Target (T1): `RBM.Gauss.Step2.highProb_jG_le_jS` — verdict: **PASS**

Statement checked against the ticket: for `d : Gauss.Dims`, under the Step-1 hypotheses (the
hypothesis list of `RBM.Gauss.step1Hyp_gauss_of_scale''`, per `docs/reports/T1488-prove.md` §3),
for every `D ≥ 0` and `∀ ε > 0`:
`HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N, APrimeJG.jG (sample d) E N u ω ℓ_u η_u D ≤
N^{2ε} · Step2.jS (sample d) E D N u ω})`.

- **Statement vs. source.** Matches `docs/reports/T1499-prove.md` §"Target (T2)", the paragraph
  "Satisfiability of `h560'`": `jG ≤ 1 + N^ε·18e²·jS ≤ N^{2ε}·jS`. The already-built Lean
  constant is `9·exp(√3)+2` (not `18e²`) — the informal estimate in the T1499 report was a
  back-of-envelope bound, not a claim about the literal Lean constant; using the actual proved
  constant is correct and is what "compiled" means. This is recorded as an observation, not a
  paper-delta (no paper formula is mis-transcribed; `≺`-style statements never pin the constant).
- **Hypotheses.** Exactly the Step-1 list (`hκ, hE, hB, hs0, hst, ht1, hcond, hc0, hreg`) plus
  two free parameters `D ≥ 0`, `ε > 0`. No hypothesis beyond this is used. `jStar` does not
  appear anywhere (checked by construction: only `APrimeJG.jG` and `RBM.Step2.jS` are used).
- **Quantifier order.** `∀ d, [Step-1 hyps], ∀ D ≥ 0, ∀ ε > 0, HighProb(...)`, and `HighProb`
  itself is `∀ Δ > 0, ∀ᶠ N, …` — fixed parameters precede `∀ᶠ N`, matching the paper's order.
- **Dependencies already accepted.** `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow`,
  `RBM.Gauss.entryBoundFlow_floor`, `RBM.Gauss.rpow_neg_one_le_etaT_of_scale_ge`,
  `RBM.Gauss.flowDelta_le_rpow_neg`, `RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`,
  `RBM.Step2Moment.one_le_jS`, `RBM.eventually_le_rpow` — all committed on `main` before this
  ticket (none is part of this ticket's own writable file).
- **Boundary cases.** `D = 0` is allowed (`hD : 0 ≤ D`, no division by `D` anywhere). `jS ≥ 1`
  always (`Step2Moment.one_le_jS`), so no vacuous `jS = 0` branch. `N` ranges over `atTop`, no
  `N = 0` vacuity; the index set `TimeIcc s t N` is exactly the paper's window, not narrowed.
- **Simultaneous satisfiability.** The Step-1 hypothesis list is the same list already shown
  simultaneously satisfiable and used to build `HighProb` statements in `RBM.Gauss.Step2Eq557`
  (T1492, merged) and in the M2/M6 targets of T1488 (`eventually_commonEvent_nonempty`,
  `APrimeGeneralMovingDriftSourceGeneralDims.lean:127`). `D ≥ 0` and `ε > 0` are free real
  parameters with no interaction with the rest of the list (e.g. `D := 1`, `ε := 1` are always
  valid together with any witness of the Step-1 list). No astronomically-large-only witness is
  needed.

Verdict: **PASS**. Proceeded to Lean.

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/Step2JGle.lean` (worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1502`, branch
`t/T1502`, commit `c035b85`). Imports `RBM1D.Gauss.APrimeJG`, `RBM1D.Gauss.APrimeGoodSetFlowGeneralDims`,
`RBM1D.Hierarchy.Step2Moment`. No other file touched.

Public declaration, namespace `RBM.Gauss.Step2`:

- `highProb_jG_le_jS (d : Dims) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
  (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
  (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ} (hc0 : 0 < c)
  (hreg : ∀ᶠ N, N^c ≤ (band d).scale E N (t N)) (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
  HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
    APrimeJG.jG (sample d) E N u ω ((band d).ell N u) (etaT E u) D ≤
    N^(2*ε) * RBM.Step2.jS (sample d) E D N u ω})`.

Proof: `Cond272Reg (band d) E s t c := ⟨hcond, hreg⟩` feeds
`APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow` for the along-flow good event;
`entryBoundFlow_floor` (with `K := 1`, `c₀ := c/6`, `B := D`) feeds the floored (4.2);
`APrimeJG.highProb_jG_le_of_entryBoundFlow` at `τ := ε` gives
`jG ≤ 1 + N^ε·(9·exp(√3)·jS + 2)` on one `HighProb` event; `HighProb.mono` then absorbs, using
`Step2Moment.one_le_jS` (`1 ≤ jS`) and `RBM.eventually_le_rpow (3+9·exp(√3)) hε`
(`3+9·exp(√3) ≤ N^ε` eventually), the chain
`1 + N^ε(A·jS+2) ≤ N^ε((3+A)·jS) ≤ N^ε·N^ε·jS = N^{2ε}·jS` (`A := 9·exp(√3)`).

Build:
```
$ lake build RBM1D.Gauss.Step2JGle
✔ [3880/3880] Built RBM1D.Gauss.Step2JGle (3.6s)
Build completed successfully (3880 jobs).
```
No `sorry`/`admit`/`axiom` (checked by `grep`, no match).

Axioms (`lake env lean` on a scratch file importing the module):
```
'RBM.Gauss.Step2.highProb_jG_le_jS' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## (c) Key lemmas used

`RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow` (the assembled `jG ≤ 1+N^τ(9e^{√3}jS+2)`, itself
built from `RBM.APrimeJG.jG_le_of_neighbor_green_sq`, `RBM.APrimeJG.neighbor_green_sq_le_of_entry_event`,
`RBM.APrimeJG.sum_shifted_control_le_jS_tail`, `RBM.APrimeJG.tailT_shift_three` ⟵ `tailT_sub_le`,
`RBM.Gauss.entryBoundFlow_floor` ⟵ `entry_bound_gauss`'s row/column large-deviation theorems);
`RBM.Gauss.rpow_neg_one_le_etaT_of_scale_ge`, `RBM.Gauss.flowDelta_le_rpow_neg`;
`RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`; `RBM.Step2Moment.one_le_jS`;
`RBM.HighProb.mono`, `RBM.eventually_le_rpow`, `Real.one_le_rpow`, `Real.rpow_add`.

## (d) Open issues

1. The constant produced by the already-accepted chain is `9·exp(√3)+2` (i.e. the multiplicative
   loss absorbed is `9·exp(√3)+3`), not the `18e²` estimated informally in
   `docs/reports/T1499-prove.md`. Both are fixed positive reals, absorbed identically by `N^ε`;
   no correction to that report is needed, this is just a note that the literal Lean constant
   differs from the back-of-envelope one, as expected for a `≺`-style bound. Not a paper-delta:
   no paper formula is involved in fixing this particular numeric constant.
2. `RBM.Gauss.Step2.highProb_jG_le_jS` is stated for a fixed `D` (not the `D'` two-parameter
   split seen in T1499's `tailT`/`gmOfJS` discussion); this matches the ticket's own statement,
   which uses a single `D` for both the `jG`/`tailT` argument and the entry-bound floor exponent,
   exactly as `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow` already does.
