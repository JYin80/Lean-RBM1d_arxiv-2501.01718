Prover model: claude-opus-5-5

# T1521 — Steps 1–2 of `RBM.Steps` for the Gaussian model (`Steps12Gauss.lean`)

## (a) Math preflight (written before any Lean)

### Step 0 read-only checks (done)

- `RBM.Steps` (`Flow/Hypotheses.lean:387–426`) and `BoundsCore_of_Steps` (`:435–438`): read.
  `Steps` bundles exactly 8 fields in the order `apriori, weakLaw, localLaw, aprioriDecay,
  sharpLoop, sharpLmK, sharpDecay, sharpExpect`.
- `RBM.Step1.apriori` (`Hierarchy/Step1.lean:812–838`) and `RBM.Step1.weakLaw` (`:791–806`): read.
  Both live in a `variable {Ω} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E} {s t}` section
  (`X` **explicit**), and both take, in order:
  `X (hκ : 0 < κ) (hE : |E| ≤ 2-κ) (hB : BoundsCore X E s) (hs0) (hst) (ht1)
   (hc : Cond272 B E s t) {c} (hc0 : 0 < c) (hreg : ∀ᶠ N, N^c ≤ B.scale E N (t N))
   (h : Step1.Hyp X E s t)`.
- `RBM.Gauss.step1Hyp_gauss_of_scale''` (`Gauss/EntryBoundTime.lean:654–677`): read. Signature
  `(d) {κ} (hκ : 0<κ) (hE : |E|≤2-κ) (hB : BoundsCore (sample d) E s) (hs0) (hst) (ht1)
   (hcond : Cond272 (band d) E s t) {c} (hc0) (hreg : N^c ≤ scale(t))`, conclusion
  `Step1.Hyp (sample d) E s t`.
- `RBM.Step2.step2`'s proof (`Hierarchy/Step2.lean:2054–2075`): read. It derives, from its own
  `hEκ, hst, ht1, hc0, hreg` (the *strong* `hreg` with the `(η_s/η_t)^30` gain),
  `hE : |E| < 2` (via `linarith` from `hEκ`+`hκ0`), `hc272 := cond272_of_strict hE hst ht1 hc0
  hreg : Cond272 B E s t`, and `hreg' := (from eventually_R4_le_scale) : N^c ≤ B.scale E N (t N)`,
  then `h1 := step1Hyp_gauss_of_scale'' … hcond hc0 hreg'` (Gaussian route) and finally calls
  `Step1.weakLaw X hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hreg' h1` (and, in the general `Step2.step2`,
  `Step1.apriori` is not called — but the *pattern* of discharging `Step1.apriori`/`Step1.weakLaw`'s
  hypotheses from `step2`'s own hypothesis list is exactly this).
- `RBM.Gauss.step2_gauss_of_grid`/`GridPointwise` (T1517, `Gauss/Step2Gauss.lean:147–258`): read.
  `step2_gauss_of_grid`'s hypothesis list is `(d) {κ} (hκ0 : 0<κ) (hκ1 : κ≤1) {E} (hEκ : |E|≤2-κ)
  {s t} (hB : BoundsCore (sample d) E s) (hs0) (hst) (ht1) {c} (hc0 : 0<c)
  (hreg : ∀ᶠ N, N^c (η_s/η_t)^30 ≤ scale(t)) (hgp : GridPointwise d E s t)`, conclusion the
  `∧`-pair `(2.75) ∧ (2.76)` = exactly `Steps.localLaw ∧ Steps.aprioriDecay` at `X := sample d`.
  `Step2Gauss.lean` also contains (unnamed, hence not directly reusable) an `example` (lines
  260–283) showing `GridPointwise` follows from `RBM.Step2.step2`'s own conclusion (`Hy`'s
  `aprioriDecay`) via `stochDom_grid_iff_flow` at the trivial one-step grid `K := 1`.

### Target (T1): `RBM.Steps12` + `RBM.Steps.toSteps12` / `RBM.Steps.ofSteps12`

Purely definitional packaging: a `Prop`-structure with the first four fields of `RBM.Steps`,
stated with the identical field types (copied verbatim from `Flow/Hypotheses.lean:388–406`), plus
two one-line conversions (`Steps → Steps12` by projection; `Steps12` + the 4 remaining fields as
arguments `→ Steps` by the anonymous constructor). No hypothesis, no vacuity risk, no dependency
beyond already-accepted `Steps`.

**Verdict: PASS.**

### Target (T2): `RBM.Gauss.steps12_gauss_of_grid`

Statement (from the ticket): hypotheses `hκ0 : 0<κ`, `hκ1 : κ≤1`, `hEκ : |E|≤2-κ`,
`hB : BoundsCore (sample d) E s`, `hs0 : ∀N,0≤s N`, `hst : ∀N,s N≤t N`, `ht1 : ∀N,t N<1`,
`{c} (hc0:0<c) (hreg : ∀ᶠ N, N^c (η_s/η_t)^30 ≤ scale(t))` (step2's own `hreg`, i.e. the *strong*
form with the `(η_s/η_t)^30` gain — the ticket's phrase "step2's `hreg`" and "T1517:2062–2071"
both point at this shape, not the bare `N^c ≤ scale(t)` form), and `hgp : GridPointwise d E s t`.
Conclusion: `Steps12 (sample d) E s t`.

**The interface question this ticket exists to answer:** does `Step1.apriori`/`Step1.weakLaw`
need anything this hypothesis list does not supply?

Checking each of `Step1.apriori`/`Step1.weakLaw`'s 10 hypotheses (`X, hκ, hE, hB, hs0, hst, ht1,
hc, hc0, hreg, h`) against what T2's list supplies or lets us derive in one step, *exactly along
`step2`'s own proof's route* (Step2.lean:2067–2073):

1. `X := sample d` — fixed.
2. `hκ`(`0<κ`) ← T2's `hκ0`. Exact match.
3. `hE`(`|E|≤2-κ`) ← T2's `hEκ`. Exact match.
4. `hB` ← T2's `hB`. Exact match.
5. `hs0, hst, ht1` ← T2's own. Exact match.
6. `hc : Cond272 B E s t` ← **not directly in T2's list**, but `RBM.Step2.cond272_of_strict
   (hE : |E|<2) hst ht1 hc0 hreg : Cond272 B E s t` derives it from T2's *own* `hst, ht1, hc0,
   hreg` plus `hE`, itself `by linarith` from T2's `hEκ`+`hκ0` (`|E| ≤ 2-κ < 2` since `κ>0`). This
   is the identical derivation `step2`'s own proof performs (`hc272`, Step2.lean:2069).
7. `hc0` ← T2's own `hc0`. Exact match (**same `c`** — T2's `hreg` uses the same `c` as `hc0`).
8. `hreg : ∀ᶠ N, N^c ≤ scale(t)` (the *bare*, unstrengthened form) ← **not directly in T2's
   list** (T2's `hreg` carries the extra `(η_s/η_t)^30` factor), but
   `RBM.Step2.eventually_R4_le_scale hE hst ht1 hc0 hreg` (T2's own `hst,ht1,hc0,hreg` + the
   derived `hE`) gives, at `u := t N` (`TimeIcc.last`), exactly this bare form. Identical to
   `step2`'s own `hreg'` (Step2.lean:2070–2072).
9. `h : Step1.Hyp X E s t` ← **not directly in T2's list**, but `RBM.Gauss.step1Hyp_gauss_of_scale''
   d hκ0 hEκ hB hs0 hst ht1 (the derived hc) hc0 (the derived hreg')` produces it, using only
   items 2–8 above (all already available or derived). Identical to `step2`'s own `h1`
   (Step2.lean:2071–2072, `EntryBoundTime.lean:654–677`).

**Conclusion of the check: every hypothesis `Step1.apriori`/`Step1.weakLaw` need is either
literally one of T2's own hypotheses, or is derived in one step from T2's own hypotheses by a
lemma that is itself already an accepted, already-merged result** (`Step2.cond272_of_strict`,
`Step2.eventually_R4_le_scale`, `Gauss.step1Hyp_gauss_of_scale''`), **using no hypothesis beyond
T2's list.** So there is *no* interface mismatch: `Step1.apriori`'s and `step2`'s hypothesis lists
line up exactly, via the same three glue lemmas `step2`'s own proof already uses for exactly this
purpose. This *is* the answer the ticket asks for — a positive one, not a gap to report as
FAIL/BLOCKED.

`localLaw`/`aprioriDecay` are literally the two conjuncts of `step2_gauss_of_grid d hκ0 hκ1 hEκ hB
hs0 hst ht1 hc0 hreg hgp` (same `hreg`, same `hgp`; no adaptation needed).

Simultaneous satisfiability of T2's own hypothesis list: `hκ0,hκ1,hEκ,hB,hs0,hst,ht1,hc0,hreg,hgp`
is the same list `step2_gauss_of_grid` (T1517, already accepted) already carries (T2 adds nothing
new), so its satisfiability is inherited from T1517's own report; T3 below gives, in addition, a
compiled derivation of `hgp` from `Step2.Hyp` + `step2`'s other hypotheses, i.e. an independent
non-degeneracy argument that does not bottom out only in T1517's witness.

**Verdict: PASS.**

### Target (T3): nondegeneracy `example`s

- `Steps12` is not vacuous: `Steps X E s t → Steps12 X E s t` is `Steps.toSteps12`, one line,
  compiles for any `Steps` instance (in particular any already-accepted `Steps` instance, e.g. the
  conclusion of `Thm221`/`Step2.step2` composed with Steps 3–6, none of which is invoked here — we
  only need the *implication*, which is unconditionally true and non-circular: `Steps12` is
  strictly weaker than `Steps`).
- `steps12_gauss_of_grid`'s hypothesis list is implied by (a superset of) `Step2.step2`'s own for
  `sample d`: given `Hy : Step2.Hyp (sample d) E s t` (`Step2.step2`'s own random-layer input) plus
  `hB, hs0, hst, ht1, hc0, hreg` (identical to T2's), `RBM.Step2.aprioriDecay (sample d) Hy hE hs0
  hst ht1 hB hc0 hreg` gives (2.76) at the flow level, which transfers to `GridPointwise` at the
  trivial one-step grid `K:=1` exactly as `Step2Gauss.lean`'s own (unnamed) nonvacuity example for
  `GridPointwise` does (`stochDom_grid_iff_flow` at `K:=1`); this yields `hgp`, and hence all of
  `steps12_gauss_of_grid`'s hypotheses, from `Step2.step2`'s own list. `Step2.Hyp`/`BoundsCore` are
  themselves known jointly satisfiable (accepted results feeding `Step2.step2`, already merged);
  this is not re-derived here, only the reduction `Step2.step2`'s-hyps ⟹ T2's-hyps is new.

**Verdict: PASS.**

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/Steps12Gauss.lean` (sole writable file).

Declarations added:
- `RBM.Steps12` (structure, `Prop`, fields `apriori, weakLaw, localLaw, aprioriDecay`).
- `RBM.Steps.toSteps12`.
- `RBM.Steps.ofSteps12`.
- `RBM.Gauss.steps12_gauss_of_grid`.
- `RBM.Gauss.gridPointwise_of_step2Hyp` (helper for (T3), not required by the ticket by name but
  needed to state (T3) compilably; uses only already-accepted lemmas).
- Two `example`s for (T3).

Build:
```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1521 && lake build RBM1D.Gauss.Steps12Gauss
```
Result: **succeeded**, `Built RBM1D.Gauss.Steps12Gauss (4.1s)`, `Build completed successfully
(3895 jobs)`. No `sorry`/`admit`/`axiom` in the new file.

Axioms (`#print axioms` via `lake env lean` on a scratch file importing `Steps12Gauss`, then
removed):
```
'RBM.Steps.toSteps12' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Steps.ofSteps12' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.steps12_gauss_of_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.gridPointwise_of_step2Hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms.

Committed on branch `t/T1521`, commit `ec2ed8e`, file `RBM1D/Gauss/Steps12Gauss.lean` only.

## (c) Key lemmas used

`RBM.Steps` (`Flow/Hypotheses.lean`), `RBM.Step1.apriori`, `RBM.Step1.weakLaw`, `RBM.Step1.Hyp`
(`Hierarchy/Step1.lean`), `RBM.Step2.cond272_of_strict`, `RBM.Step2.eventually_R4_le_scale`,
`RBM.Step2.aprioriDecay`, `RBM.Step2.Hyp` (`Hierarchy/Step2.lean`), `RBM.Gauss.
step1Hyp_gauss_of_scale''` (`Gauss/EntryBoundTime.lean`), `RBM.Gauss.step2_gauss_of_grid`,
`RBM.Gauss.GridPointwise`, `RBM.Gauss.lkErrMat`, `RBM.Gauss.stochDom_grid_iff_flow`
(`Gauss/Step2Gauss.lean`, T1517).

## (d) Open issues

None found at the interface level: `Step1.apriori`/`Step1.weakLaw`'s hypotheses line up exactly
with `steps12_gauss_of_grid`'s (T2's) own hypothesis list via the same three glue lemmas `Step2.
step2`'s own proof already uses. No hypothesis was added, no signature weakened.
