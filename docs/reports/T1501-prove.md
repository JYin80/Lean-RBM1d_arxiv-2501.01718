Prover model: claude-sonnet-5[1m]

# T1501: (5.35) far-field bound without `h560` — T1499 Option B

2026-09-25T20:48Z (preflight written before any Lean).

## (a) Math preflight

### Step 0 (read-only checks)

- `RBM.APrimeJG.gmBlk`, `RBM.APrimeJG.gsqBlk`, `RBM.APrimeJG.jG`
  (`RBM1D/Gauss/APrimeGeneralMovingCarrierCore.lean:138,145,153`) are declared under
  `variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}` — arbitrary `Band Ω`, hence
  arbitrary `Gauss.Dims`. **Generic — PASS.**
- `RBM.APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail` (`APrimeDriftNearTriple.lean:54`) is
  declared under the same `variable {Ω} {B : Band Ω}`, `(ω : Ω)`. **Generic — PASS.**
- `RBM.APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk` (`APrimeFirstCellEGFar.lean:140`) is
  **not** generic as committed: the file opens with
  `private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow` and
  `private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d` (lines 19–20), with no
  `variable {B : Band Ω}` anywhere in the file to shadow it. So although the theorem's
  signature reads `(X : Sample B) … (ω : Gauss.Ω d) …`, `B` there is the fixed value
  `Gauss.band Dims.exampleGrow`, not a bound `Band Ω`. **This is the exact
  `exampleGrow`-only situation the ticket's Step 0 asks to detect** (DECISIONS §10b: reuse is
  allowed only for "fixed-time, deterministic, or arbitrary-`Dims`" declarations; results true
  only for `Dims.exampleGrow` must not feed the true path).

**Resolution (not a stop, on inspection of the proof, not just the signature).** The *proof* of
`norm_gloop_three_le_gmBlk` uses only: `Lemma57.norm_gloop_three_le` (Hierarchy layer,
no `Dims`/`Band` dependence at all — generic in `L Wb : ℕ`, `H : Matrix _ _ ℂ`, `z : ℂ`),
`APrimeJG.norm_Gsig_le_gmBlk`, `APrimeJG.gmBlk_nonneg` (both generic, `variable {B : Band Ω}`,
`APrimeJG.lean:32,40`), and `APrimeDriftNearTriple.gmBlk_comm` (generic,
`APrimeDriftNearTriple.lean:25`). None of these depend on `exampleGrow` or on the smooth-prefix
weights. A **fully generic, arbitrary-`d : Dims`** copy of the same proof is already committed
— `private theorem norm_gloop_three_le_gmBlk (d : Dims) (X : Sample (band d)) …` in
`RBM1D/Gauss/APrimeGeneralMovingDriftSourceGeneralDims.lean:245–286` — but it is `private` to
that file (not importable) and stated over `Sample (band d)` rather than a bound `Band Ω`.
Likewise `two_loop_re_le_gsqBlk` (the (4.2)-off-diagonal half of `h531`) has a public but
`exampleGrow`-scoped copy at `APrimeFirstCellEGFar.lean:182` and a `private`,
arbitrary-`d`-but-not-`Band Ω` copy at `APrimeGeneralMovingDriftSourceGeneralDims.lean:288–359`.

Since (i) none of the *named* `exampleGrow`-scoped declarations are used as black-box inputs
below, (ii) the two facts needed (`h560`'s triple-loop bound and the two-loop `h531` bound) are
reconstructed inside `Step2FarInputsJG.lean` **from scratch**, using only the generic,
already-accepted sublemmas listed above (`Lemma57.norm_gloop_three_le`,
`Lemma57.sum_blkW_normSq`, `Lemma57.sum_blkW`, `Lemma57.blkW_nonneg`, `Gsig_true`,
`APrimeJG.norm_Gsig_le_gmBlk`, `APrimeJG.gmBlk_nonneg`, `APrimeJG.gmBlk_mul_swap_le_gsqBlk`,
`APrimeJG.gsqBlk_le_jG_mul_tailT`, `APrimeJG.one_le_jG`, `APrimeDriftNearTriple.gmBlk_comm`,
`APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail`), and (iii) this reconstruction adds no new
hypothesis and states no new claim beyond what those generic sublemmas already give — the
§10b reuse condition is satisfied in substance: only "fixed-time, deterministic, or
arbitrary-`Dims`" declarations are ever cited. The mechanical work is exactly mirroring the
already-committed *arbitrary-`d`* private proofs in `APrimeGeneralMovingDriftSourceGeneralDims.lean`,
generalized one step further from `Sample (band d)` to a bound `{B : Band Ω}` (a renaming, not
new mathematics). This is recorded here in full so the auditor can independently check that no
`exampleGrow`-specific fact is smuggled in. Flagged as a paper-delta / follow-up candidate in
(d): the two private lemmas should eventually be promoted to public, `Band Ω`-generic
declarations in their home files, so future tickets can cite them directly instead of
re-deriving.

Dependencies (T1499 report merged 2026-09-25; the cited lemmas are all already committed on
`main` at the paths above). No frozen signature is touched; `Step2FarInputsJG.lean` is a new
file.

### Target (T1): `RBM.Step2FarInputs.eGpm_le_rhs535_of_jG` — verdict **PASS**

Statement vs. paper: this is `RBM.Step2FarInputs.eGpm_le_rhs535` (frozen, proved, abstract `Gm`)
instantiated with `J := APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D'` and
`Gm := APrimeJG.gmBlk X E N u ω`, i.e. the paper's (5.60)→(5.61) route: bound the actual triple
loop entries first (5.60, deterministic, every `b`), then invoke the block two-loop (4.2)-type
bound `gsqBlk_le_jG_mul_tailT`/`gmBlk_le_sqrt_jG_tail` only on far pairs (5.31). No probabilistic
input, no `hK`, no `h560` hypothesis. Hypotheses are literally
"those of `eGpm_le_rhs535_of_jS` minus `hK` and `h560`", i.e. `hL, hW, hℓu, hℓs, hηu, hA, hr, hD,
a₁ a₂, hρ, h273, h554, h557C, h557R, m/hone, hκ`, all quantified in the same order as
`eGpm_le_rhs535_of_jS` (fixed parameters, then the sample and block indices; nothing is
reordered ahead of anything it depends on). No hypothesis is added. `1 ≤ jG` holds
unconditionally (`APrimeJG.one_le_jG`, from `hW : 1 ≤ (B.W N:ℝ)`, no further condition), so `jG`
is never a vacuous/degenerate quantity — the theorem is non-vacuous for the same reason
`eGpm_le_rhs535_of_jS` was (the surviving hypotheses `h273, h554, h557C, h557R, hone, hκ` are
those T1488/T1496 already exhibited a simultaneous witness for, since none of them mentions `J`
or `Gm`; adding `jG`/`gmBlk` in their place changes no other hypothesis). Boundary case `a₁ =
a₂` is allowed (nothing excludes it, matching `eGpm_le_rhs535`). Dependencies: `eGpm_le_rhs535`
(already accepted, frozen); the generic `APrimeJG`/`APrimeDriftNearTriple`/`Lemma57` sublemmas
above (already accepted). **PASS.**

### Target (T2, optional): `rhs535_mul_J_le` — verdict **PASS** (attempted)

`rhs535 Wr Lr ℓu ℓs ηu D (c^2*J) ρ d ≤ c^3 * rhs535 Wr Lr ℓu ℓs ηu D J ρ d` for `c ≥ 1`,
`J,ρ,Lr ≥ 0`, `Wr ≥ 1`, `ℓu,ℓs,ηu > 0`. Direct algebra on the definition of `rhs535`: the
indicator/near term and the `ρ`-remainder term do not mention `J` (degree `0`, so multiplying by
`c^0 = 1 ≤ c^3` suffices), the `cFar` term is degree `1` in `J` hence picks up `c^2 ≤ c^3`
after `√(c^2 J) = c√J` is expanded, and the `169`-term is degree `3/2` in `J`
(`(c^2J)*√(c^2J) = c^3*(J√J)`) hence is matched by `c^3` with equality. No new hypothesis; same
nonvacuity witness as `rhs535_div_le` (T1496). **PASS.**

## (b) Declarations, build, axioms

File: `RBM1D/Hierarchy/Step2FarInputsJG.lean` (worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1501`, branch `t/T1501`). Imports only
`RBM1D.Gauss.APrimeDriftNearTriple` (which pulls in `APrimeJG`, `Step2FarInputs`, `Lemma57`
transitively). Nothing else is touched.

Public declarations, namespace `RBM.Step2FarInputs` (the file reopens this namespace so the
ticket's requested name resolves as `RBM.Step2FarInputs.eGpm_le_rhs535_of_jG`):
- `norm_gloop_three_le_gmBlk'` (private helper, generic `{B : Band Ω}`): the (5.60) bound
  `‖gloop … [false,true,true],[a₂,b,a₁]‖ ≤ gmBlk a₂ b * gmBlk a₁ b * gmBlk a₂ a₁`.
- `two_loop_re_le_gsqBlk'` (private helper, generic `{B : Band Ω}`): `(gloop …
  [true,false],[x,y]).re ≤ gsqBlk x y`.
- `eGpm_le_rhs535_of_jG` (public, `RBM.Step2FarInputs` namespace): the (T1) target above.
- `rhs535_mul_J_le` (public, `RBM.Step2FarInputs` namespace): the (T2) target above.

Build:
```
$ cd /Users/junyin/Lean_proof/RBM1D-wt/T1501 && lake build RBM1D.Hierarchy.Step2FarInputsJG
...
Build completed successfully (3846 jobs).
```
No `sorry`/`admit`/`axiom`. Only benign warnings (`letI`/`if_neg` style/deprecation lints,
mirroring the pre-existing style of the private proofs this file's helpers are modelled on).

Axioms (`lake env lean` on a scratch file importing the module):
```
'RBM.Step2FarInputs.eGpm_le_rhs535_of_jG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Step2FarInputs.rhs535_mul_J_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## (c) Key lemmas used

`Lemma57.norm_gloop_three_le`, `Lemma57.sum_blkW_normSq`, `Lemma57.sum_blkW`,
`Lemma57.blkW_nonneg`, `Gsig_true`; `APrimeJG.norm_Gsig_le_gmBlk`, `APrimeJG.gmBlk_nonneg`,
`APrimeJG.gmBlk_mul_swap_le_gsqBlk`, `APrimeJG.gsqBlk_le_jG_mul_tailT`, `APrimeJG.one_le_jG`;
`APrimeDriftNearTriple.gmBlk_comm`, `APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail`;
`Step2FarInputs.eGpm_le_rhs535`, `Step2FarInputs.rhs535`; `Real.sqrt_mul`.

## (d) Open issues

1. The committed declarations `RBM.APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk` and
   `.two_loop_re_le_gsqBlk` are `exampleGrow`-scoped (file-local `abbrev B`), and the fully
   generic (arbitrary-`d`) proofs of the same content are `private` to
   `APrimeGeneralMovingDriftSourceGeneralDives.lean` (`Sample (band d)`, not a bound `Band Ω`).
   This ticket re-derives both, generalized to `{B : Band Ω}`, inside its own sole writable
   file, from already-generic sublemmas — see (a) Step 0. Recommend a small follow-up ticket to
   promote these two as public, `Band Ω`-generic lemmas in their natural homes
   (`APrimeJG.lean`/`APrimeDriftNearTriple.lean`), so downstream tickets can cite them by name
   instead of re-deriving.
2. `hK`, `h560`, `h535_of_jS`-style hypotheses are not used anywhere in this file (per
   acceptance criteria).
3. `h535_of_jG` (the `∀ u ∈ Ico` wrapper analogue of `h535_of_jS`) is not built here; it is a
   direct corollary (same pattern as `h535_of_jS` from `eGpm_le_rhs535_of_jS`) and is left for a
   consumer ticket if needed.
