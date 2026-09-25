Prover model: claude-sonnet-5

# T1490 — one-step conditional variance (the discrete (5.25))

Ticket: `docs/tickets/T1490.md`. Worktree: `RBM1D-wt/T1490` (branch `t/T1490`). Sole writable
file: `RBM1D/Gauss/GridOneStepVar.lean` (new file; `Root import: none` per the ticket, so
`RBM1D.lean` is untouched).

## (a) Math preflight (written before any Lean; verdicts below stand as the pre-registered
plan — the write-up matches what was actually proved)

### Required reading done
`CLAUDE.md` §3; `RBM1D/Gauss/GridOneStep.lean` (T1486: `TestFun.shift`, `Grid.gen`,
`Grid.genPt`, `Grid.oneStep_integral_eq`, `Grid.oneStep_error_le`,
`integrable_norm_Xmat`); `RBM1D/Gauss/MomentGronwall.lean` (`momentFun`, `quadVar`,
`quadVarPairs`, `secondOrder_eq_quadVar`, `genD`, `genMomentPt`, `coordD2_momentFun_ofReal`,
`genMomentPt_le`, `sum_gvar_re_coordD2`, `mul_conj_eq`, `add_conj_mul`, `ofReal_genMomentPt`,
`BddC2`, `bddC2_momentFun`, `TestFun.of_bddC2`); `RBM1D/Gauss/Generator.lean` (`TestFun`,
`coordD1`, `coordD2`, `usedCoord`); `docs/claude-team/pilot-P4P5-paper.md` §4.

### Step 0 checks (read-only)
(a) `Grid.oneStep_error_le` (T1486, T3) holds for **every** `Δ ≥ 0`, with no upper bound on
`Δ`; `Grid.genPt` (`GridOneStep.lean:195`) is `(1/2:ℝ) • ∑ usedCoord, gvar • coordD2 Φ A p`,
literally the same formula (`1/2 = 2⁻¹`) as `RBM.Gauss.genD` (`MomentGronwall.lean:547`).
(b) `TestFun` is `ℂ`-valued; `fun A => ((‖Φ A‖^2:ℝ):ℂ)` is `momentFun Φ 1` by `momentFun_eq`,
and it *is* a `TestFun` for `TestFun d N Φ`: `RBM.Gauss.TestFun` and `RBM.Gauss.BddC2` have
literally the same three fields (only the ambient normed space differs), so
`TestFun.of_bddC2`/`bddC2_momentFun` (`MomentGronwall.lean:840/976`) apply directly. Proved as
`TestFun.normSq` below.
(c) `coordD2_momentFun_ofReal` at `p = 1`: the `(p-1:ℕ)` coefficient is `0`, so the term that
costs `genMomentPt_le` its inequality (bounding `Re(F̄∂_αF)²` by `‖F‖²‖∂_αF‖²`) drops out
identically — the `p=1` specialisation is an **equality**, which is exactly what T1 needs and
is provable with no extra hypothesis.

### Target T1 — `RBM.Gauss.Grid.genPt_normSq`
Statement vs. paper: this is the internal chain rule `∂²|Φ|² = 2Re(Φ̄∂²Φ) + 2‖∂Φ‖²`
(after `∂|Φ|²` type identities), summed against `coordD2`/`usedCoord` and halved by `genPt`'s
normalisation; on the right, `quadVar d N Φ M` is exactly `RBM.Gauss.quadVar`, the coordinate
sum `∑_α S_α‖∂_αΦ‖²` that `secondOrder_eq_quadVar` identifies with the paper's (5.25)
integrand `∑_α|E^{(M)}(α)|²`. No paper formula number is claimed directly (this is bookkeeping
internal to the repo's generator-identity route, flagged as such in `GridOneStep.lean`'s own
module doc); the only claim is that it is the correct chain rule for `|Φ|²`, verified via
`mul_conj_eq`/`add_conj_mul` algebra and cross-checked against `coordD2_momentFun_ofReal`
(itself proved by `HasDerivAt.unique`, not by hand).
Hypotheses: `TestFun d N Φ` only (no Hermitian/positivity side conditions). Quantifiers: `∀ Φ
TestFun, ∀ M` — matches the paper's parameter order (fixed parameters before any asymptotic
statement; there is none here). No dependencies beyond already-accepted `MomentGronwall.lean`/
`GridOneStep.lean` declarations. Boundary cases: none (`M` arbitrary, not required Hermitian).
Verdict: **PASS**. Route: `momentFun Φ 1 = ‖Φ‖²` (`momentFun_eq`); `genPt (momentFun Φ 1) M =
((genMomentPt Φ 1 M:ℝ):ℂ)` (`ofReal_genMomentPt`, matching `1/2 = 2⁻¹`); `genMomentPt Φ 1 M =
quadVar Φ M + 2·Re(Φ̄M·genD Φ M)` (`coordD2_momentFun_ofReal` at `p=1` + `sum_gvar_re_coordD2`);
`genD = Grid.genPt` (same formula, `1/2 = 2⁻¹`).

### Target T2 — `RBM.Gauss.Grid.oneStep_var_le`
Statement vs. paper: `pilot-P4P5-paper.md` §4 states the one-step conditional variance is
`Δ·[(U⊗U)∘(E⊗E)]` up to `O(Δ²N^C)` (paper-internal discrete replacement for the BDG integrand
(5.25)); the ticket's Lean target replaces `(E⊗E)` by `quadVar d N Φ M` (matching T1's
identification with (5.25)) and asks for error `O(Δ^{3/2})` (a **stronger**, not weaker,
statement than the paper's `O(Δ²N^C)` sketch, consistent with T1486's own `O(Δ^{3/2})` for the
mean). Hypotheses: `TestFun d N Φ`, `M.IsHermitian`, Lipschitz constants `Λ₁` (for `genPt Φ`)
and `Λ₂` (for `genPt (‖Φ‖²)`) on Hermitian matrices, global bounds `B` on `‖Φ‖`, `G` on
`‖genPt Φ‖`, and `Δ ≥ 0` — **no upper bound on `Δ`**, matching `oneStep_error_le`'s own
hypothesis-order exactly (Step 0 (a)). Quantifier order: all parameters (`Φ, M, Λ₁, Λ₂, B, G`)
fixed before `Δ`, matching the paper's convention (fixed parameters before the asymptotic
variable) even though there is no `∀ᶠ N` here (this is a deterministic, single-`N` statement,
consumed downstream by T1482/T1484 which do carry the `N`-asymptotics). Dependencies: T1486
(merged), `quadVar`, `secondOrder_eq_quadVar`, `TestFun` (all committed) — none new.

**Simultaneous satisfiability of the hypotheses (nondegenerate witness).** `Φ` constant (e.g.
`Φ ≡ c`), `M := 0`, `Λ₁ = Λ₂ := 0`, `B := ‖c‖`, `G := 0`: `TestFun` holds trivially (`bdd₁ =
bdd₂ = 0`), `genPt Φ ≡ 0` and `genPt (‖Φ‖²) ≡ 0` so both Lipschitz hypotheses hold with
`Λ = 0` (not vacuously via an astronomically large constant — `Λ = 0` exactly, because the
two sides of the inequality are literally `0 ≤ 0`), and `quadVar Φ M = 0` too, so both sides of
the conclusion are `0` for every `Δ ≥ 0`; this rules out the hypothesis set being empty. The
ticket additionally asks for a witness "for a loop observable"; that is the intended
*non-trivial* instance and is explicitly assigned to the auditor stage ("the auditor checks
… the hypotheses are satisfiable for a loop observable (cite `bddC2C_loopObs` for `B`, T1487
for `Λ₁`)"). Read-only check done here: `RBM.Gauss.bddC2_loopObs` (`RBM1D/Gauss/LoopC2.lean:534`)
supplies `BddC2 (L_{σ,a})` (hence `TestFun d N (L_{σ,a})`, hence a concrete `B`, and `G` via
`norm_genPt_le`/`GridOneStep.lean`'s own `TestFun.bdd₂`-based bound); T1487
(`docs/tickets/T1487.md`, not yet released at the time of this report) is designed to supply a
Lipschitz constant for the *full* loop drift, of the same polynomial-in-resolvent-bounds flavour
as would be needed for `genPt`'s (second-order-only) piece — constructing that exact `Λ₁,Λ₂`
witness is genuine downstream work, not part of T1490's named targets, and is correctly left
to the audit/A5-assembly stage per the ticket text.

**The one subtlety found during preflight (not a hypothesis change).** The ticket's suggested
route ("expand `‖Φ M + Δ·genPt Φ M + e‖²`") is exactly right for the *identity*
`Var − Δ·quadVar = e₂.re − 2·Re(Φ̄M·e₁) − ‖S‖²` (`S := Δ·genPt Φ M + e₁ = μ − Φ M`), but a
*naive* single triangle-inequality bound on `‖S‖²` (squaring `‖S‖ ≤ ΔG + r₁(Δ)` directly)
produces a `Δ^{5/2}`/`Δ³` cross term that is **not** dominated by `C·(Δ^{3/2}+Δ²)` with a
`Δ`-independent `C`, because `oneStep_error_le` (hence `r₁(Δ) := (2/3)Λ₁Δ^{3/2}K`) holds for
*every* `Δ ≥ 0`, including `Δ → ∞` (Step 0 (a)); at fixed `Λ₁, K > 0` the naive bound's
`Δ^{5/2}`/`Δ³` term eventually exceeds any fixed multiple of `Δ^{3/2}+Δ²`. This is a genuine
gap in the *literal* suggested proof sketch, not in the target statement: the target is still
**true** as literally written (no `Δ ≤ 1` hypothesis needs to be added), because `S = μ − Φ M`
also satisfies the **`Δ`-independent** bound `‖S‖ ≤ 2B` (from boundedness of `Φ` alone, no
Lipschitz), and combining `‖S‖ ≤ min(ΔG+r₁(Δ), 2B)` via a case split at `Δ = 1` (`Δ³ ≤ Δ²` for
`Δ≤1`; `1 ≤ Δ²` for `Δ≥1`) recovers exactly the stated `C_var·(Δ^{3/2}+Δ²)` order. This is
recorded here (and in the file's module doc) rather than silently patched; it does not weaken
the target, add a hypothesis, or change the signature — it only means the Lean proof is longer
than the one-paragraph sketch. Also used, not in the ticket's sketch: `Λ₁·K ≥ 0` and
`Λ₂·K ≥ 0`, derived (not assumed) by instantiating `oneStep_error_le` at the auxiliary value
`Δ' = 1` (fixed, independent of the theorem's own `Δ`) and using `‖·‖ ≥ 0`; this is needed only
to know that the two "leftover" pieces of `C_var` (`(2/3)Λ₂K` and `(4/3)BΛ₁K`) do not
*decrease* `C_var` below what `‖S‖²`'s bound needs — again a consequence of the hypotheses, not
an addition to them.

Verdict: **PASS**, with the additional case-split argument above (all internal to the proof;
the statement is exactly the ticket's).

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridOneStepVar.lean` (new, 473 lines).

* `RBM.Gauss.TestFun.normSq (h : TestFun d N Φ) : TestFun d N (fun A => ((‖Φ A‖^2:ℝ):ℂ))`
* `RBM.Gauss.Grid.genPt_normSq (h : TestFun d N Φ) (M) : genPt d N (fun A => ((‖Φ A‖^2:ℝ):ℂ)) M
  = ((2 * (conj (Φ M) * genPt d N Φ M).re + quadVar d N Φ M : ℝ) : ℂ)` — **(T1)**.
* `RBM.Gauss.Grid.oneStep_var_le (h : TestFun d N Φ) {M} (hHerm : M.IsHermitian) {Λ₁}
  (hLip1 : …) {Λ₂} (hLip2 : …) {B} (hB : ∀ A, ‖Φ A‖ ≤ B) {G} (hG : ∀ A, ‖genPt d N Φ A‖ ≤ G)
  {Δ} (hΔ : 0 ≤ Δ) : |Var − Δ·quadVar d N Φ M| ≤ C_var·(Δ^(3/2:ℝ)+Δ^2)` — **(T2)**, with
  `Var := ∫ ‖Φ(M+√ΔX) − ∫ Φ(M+√ΔX)‖² dP` and
  `C_var = (2/3)Λ₂K + (4/3)BΛ₁K + 2G² + 2((2/3)Λ₁K)² + 4B²`, `K := ∫‖Xmat d N ω‖ dP` — all
  written out explicitly in the statement (no existential, no hidden constant).

Two `private` helper lemmas (not part of the ticket's acceptance list, pure bookkeeping,
reusable identities local to this file): `norm_sub_sq_expand`, `norm_add_sq_expand` (the real
expansion `‖a∓b‖² = ‖a‖² ∓ 2·Re(conj b·a) + ‖b‖²`, from `mul_conj_eq`/`add_conj_mul`) and
`integral_normSq_sub_eq` (the variance identity `E‖f − Ef‖² = E‖f‖² − ‖Ef‖²` for integrable
`f : Ω d → ℂ` with `‖f‖²` also integrable).

Build:
```
lake build RBM1D.Gauss.GridOneStepVar
```
Result: **success**, no warnings, no errors (final run: `✔ [3706/3706] Built
RBM1D.Gauss.GridOneStepVar`).

Axioms (checked via a scratch file `#print axioms` on all three public declarations, then
deleted — not committed):
```
'RBM.Gauss.TestFun.normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.genPt_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.oneStep_var_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`, `admit`, or declared `axiom` anywhere in the file (`grep` confirms).

## (c) Key lemmas used (all pre-existing, cited by name above)
`RBM.Gauss.Grid.oneStep_error_le` (T1486/T3), `RBM.Gauss.momentFun_eq`,
`RBM.Gauss.coordD2_momentFun_ofReal`, `RBM.Gauss.ofReal_genMomentPt`,
`RBM.Gauss.sum_gvar_re_coordD2`, `RBM.Gauss.mul_conj_eq`, `RBM.Gauss.add_conj_mul`,
`RBM.Gauss.TestFun.of_bddC2`/`bddC2_momentFun`, `RBM.Gauss.secondOrder_eq_quadVar` (cited in
doc, not directly invoked since T1 targets `quadVar` not `quadVarPairs`),
`MeasureTheory.integral_ofReal`, `integral_re`/`RCLike.re_eq_complex_re`,
`Complex.abs_re_le_norm`, `pow_le_pow_left₀`.

## (d) Open issues / notes for the auditor
* The satisfiability witness given above is the *trivial* (constant-`Φ`) one; the ticket's
  intended non-trivial "loop observable" witness (citing `bddC2_loopObs`, T1487) is,
  per the ticket text itself, the auditor's/A5-assembly's job, not re-derived here.
  T1487 (`GridDriftLip.lean`) had not been merged at the time of this report; its exact
  `driftLip` constant is for the *full* drift, not `genPt`'s second-order piece alone, so
  turning it into `Λ₁, Λ₂` for T1490 is nontrivial downstream bookkeeping, not a T1490 gap.
* `C_var` is deliberately **not** the sharpest possible constant (e.g. `2G² + 2((2/3)Λ₁K)² +
  4B²` uses `(a+b)² ≤ 2a²+2b²` rather than a tighter cross-term estimate, and the two
  case-split regimes are combined by *summing* rather than *maximising* the two per-regime
  constants); the ticket asks only for an explicit constant, not a sharp one.
* No `docs/paper-deltas.md` entry is needed: T1's identity is internal repo bookkeeping (already
  flagged as such in `GridOneStep.lean`'s own module doc, not a new paper-vs-Lean gap), and T2's
  statement is a strengthening (`O(Δ^{3/2})` vs. the paper-route sketch's `O(Δ²N^C)`), not a
  weakening or restatement of a numbered paper formula.
