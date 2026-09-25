Prover model: claude-sonnet-5

# T1482 (amend-1) — math preflight and proof report

Sole writable file: `RBM1D/Gauss/GridMarkov.lean`. Namespace: `RBM.Gauss.Grid`.

## Step 0 (read-only checks)

(a) T1481 accepted: `RBM1D/Gauss/GridPath.lean` builds on `main` (merged, commit `ef7f0e4`); its
`filt`, `Ωg`, `Pg`, `indep_incr`, `map_incr` are usable.

(b) `ProbabilityTheory.HasCondSubgaussianMGF` (`Mathlib/Probability/Moments/SubGaussian.lean:547`):
```
def HasCondSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)
```
with `variable {m mΩ} {hm : m ≤ mΩ} [StandardBorelSpace Ω]`. Note `StandardBorelSpace` is on the
**whole sample space** `Ω` (here `Ωg d`), not on the codomain of the frozen coefficient map; this
matters for (T2)/(T3) below (they only need `Ωg d` standard Borel, already available since
`Ωg d = ℕ → Ω d`, `Ω d = Coord d → ℝ`, `Coord d` countable ⇒ standard Borel).

(c) Existing pattern `uniformPerm_prefixFourierReal_hasCondSubgaussianMGF`
(`Gauss/PermutationFourierDoobCondMGF.lean:131`): builds a deterministic-Hoeffding-parameter
`HasCondSubgaussianMGF` from (i) a conditional-mean-zero fact and (ii) a deterministic a.e. bound,
via `condExpKernel`/`condExp_ae_eq_trim_integral_condExpKernel` plumbing. For (T2) here the
conditionally-Gaussian case is used instead of Hoeffding, via
`ProbabilityTheory.hasSubgaussianMGF_gaussianReal`-style facts and
`RBM.Gauss.map_sum_const_mul_coord` (`Gauss/LinearForm.lean:110`, already in the repo, unrelated to
this ticket) giving that a finite real-linear combination of the coordinates of `Ω d` is Gaussian
with variance `linVar (gvar d) a s`.

## (T1) `condExp_freeze` — math preflight: **PASS**

Statement (paraphrasing the ticket): for `k : ℕ`, `β` a measurable space, `Y : Ωg d → β` measurable
w.r.t. `filt d k`, `F : β → Ω d → ℝ` jointly measurable, `F(Y·)(·(k+1))` integrable:
```
(Pg d)[fun ω => F (Y ω) (ω (k+1)) | filt d k] =ᵐ[Pg d] fun ω => ∫ x, F (Y ω) x ∂(P d)
```

* Hypotheses vs. dependencies: uses only T1481's `indep_incr` (increment `k+1` independent of
  `filt d k`) and `map_incr` (its law is `P d`), both already accepted.
* Quantifier order: `d`, `k`, `Y`, `F` fixed, then the a.e. equality — matches the ticket (no
  `∀ᶠ N` here; T1 is a generic conditional-expectation fact, `N` is not a parameter of it).
* Boundary cases: `k = 0` is fine (`filt d 0` reads only `ω 0`, increment is `ω 1`, still
  independent by `indep_incr d 0`). `Y` constant, `F` depending only on its first argument, or
  `F = 0` are all legitimate, non-vacuous specializations exercised as sanity checks below.
* Simultaneous satisfiability: `Y := fun _ => (0:β)` (constant, trivially `filt d k`-measurable),
  `F := fun _ x => (0:ℝ)` gives an integrable, jointly-measurable instance with both sides `0`
  — a genuine (if trivial) witness that the hypotheses can be met together; the mathematically
  interesting instances (T2/T3 below) are non-constant.
* Standard-Borel hypothesis on `β`: the ticket asks for it; my proof below does **not** need it
  (it avoids `condDistrib`/disintegration by using only `Indep_iff`, `Measure.prod_eq`, and
  Fubini `integral_prod`/`integral_map`, none of which require a Doob–Dynkin factorisation of `Y`
  through the canonical prefix map). I keep the hypothesis in the signature (unused is harmless,
  not a vacuity risk) so the statement matches the ticket exactly.
* Mathlib-lemma risk (the ticket's explicit fallback trigger): checked that Mathlib has **no**
  ready-made "freeze an `m`-measurable `Y` against an independent `Z`" lemma for a *general*
  sub-`σ`-algebra `m` (only `condExp_indep_eq`, which handles a single `m₁`-measurable function,
  and `condDistrib`/`condExp_prod_ae_eq_integral_condDistrib`, which conditions on `comap X` for a
  literal map `X`, and would need `Y` to factor through the prefix map — a Doob–Dynkin fact not in
  Mathlib). I found a route that avoids this gap entirely: since `filt d k` is *exactly*
  `comap (restrictLe k)` and the increment is independent of the **whole** `filt d k` (not just
  `comap Y`), the set-wise identity `∫_A F(Y,Z) = ∫_A (∫F(Y(ω),·)dP)` for **every** `A ∈ filt d k`
  follows from: (i) `Indep_iff` applied to `A ∩ Y⁻¹(s) ∈ filt d k` and `Z⁻¹(t) ∈ comap Z` to get
  `μ.restrict A |>.map (Y,Z) = (μ.restrict A |>.map Y).prod (P d)` on rectangles, hence everywhere
  by `Measure.prod_eq`; (ii) Fubini (`integral_prod`) on that product measure; (iii) transport back
  along `Y`, `(Y,Z)` via `integral_map`. This is self-contained, no missing Mathlib lemma. Verdict:
  **PASS**, provable within budget (confirmed by the completed Lean below).

## (T2) `hasCondSubgaussianMGF_linear` — math preflight: **PASS**

Reads: `A : Ωg d → Matrix (d.Idx N)(d.Idx N) ℂ` filt-`k`-measurable, `lin A X := Re(trace(A*X))`,
`v A := ∑` over the raw real coordinates read by `Xmat d N` of `gvar d c · (coefficient of c in
lin A)²`. I formalise "coefficient of `c` in `lin A`" as `lin A (Xmat d N (Pi.single c 1))`
(evaluating the — provably ℝ-linear — map `y ↦ lin A (Xmat d N y)` at the standard basis vector of
`Ω d`); this is the standard meaning of "coefficient of a coordinate in a linear functional" and is
exactly what makes `RBM.Gauss.map_sum_const_mul_coord` applicable.

* Correctness of the variance formula: `y ↦ Xmat d N y` is ℝ-linear (`Xentry` is, entrywise, an
  ℝ-linear function of at most two raw coordinates: this needs re-deriving the algebraic identities
  `Xentry_add/_smul/_zero` — already proved *privately* in `GridPath.lean`, hence not reusable
  verbatim, but their proofs are 3–5 lines each and are restated locally); `X ↦ Re(trace(A*X))` is
  ℝ-linear in `X` (composition of ℂ-linear `trace(A * ·)` with `Re`, both ℝ-linear); hence the
  composite is ℝ-linear in `y` and, since `Xmat d N` reads only the finitely many coordinates with
  first component `N`, is a finite real-linear form in the coordinates of `Ω d`. By
  `RBM.Gauss.map_sum_const_mul_coord`, such a form is Gaussian with variance exactly the weighted
  sum of squared coefficients times `gvar`, i.e. exactly the `v A` above.
  Audit sanity check (ticket's own requirement): for `A` = the matrix with a single nonzero entry
  `1` at `(i,i)`, `lin A X = Re(X_{ii}) = X_{ii}` (real on the diagonal) and the only nonzero
  coefficient is at `c = ⟨N,i,i,true⟩` with value `1`, so `v A = gvar d ⟨N,i,i,true⟩` — the true
  one-coordinate variance. Matches.
* `HasCondSubgaussianMGF` target: `E.indicator (fun ω => √Δ · lin(Aω)(Xmat d N (ω(k+1))))`, where
  `Δ := step s t K N`. On `E` (filt-`k`-measurable), conditionally on `filt d k`, `A ω` is frozen
  and `ω(k+1)` is independent, so (by T1 applied to the identity function, or directly by the
  Gaussian-form fact above transported through the frozen `Aω`) the variable is, conditionally,
  exactly `gaussianReal 0 (Δ · v(Aω))`; a centred Gaussian of variance `σ²` has **exact**
  subgaussian mgf parameter `σ²` (`ProbabilityTheory.hasSubgaussianMGF_gaussianReal` /
  `mgf_gaussianReal`, already in Mathlib and used by this repo, e.g. `Gauss/LinearForm.lean`), so
  `Δ·v(Aω) ≤ c` (the hypothesis, for `ω ∈ E`) gives the deterministic sub-Gaussian bound. Off `E`
  the indicator is `0`, `HasSubgaussianMGF _ 0 _` trivially. Combining the two branches through the
  `condExpKernel` (same shape as the existing `actualPrefix_increment_hasCondSubgaussianMGF`
  private lemma in `PermutationFourierDoobCondMGF.lean`, adapted from Hoeffding to Gaussian) gives
  exactly `HasCondSubgaussianMGF (filt d k) _ (...) ⟨c,_⟩ (Pg d)`.
* Quantifier order / dependencies: `s,t,K,N,k,A,E,c` all fixed first (`c` deterministic, not
  depending on `ω`), matching the paper's discrete argument (§4 of `pilot-P4P5-paper.md`); no
  hidden dependence on `N` inside `c` beyond what's given.
* Non-vacuity / simultaneous satisfiability (ticket's audit requirement): `E = univ`, `A = 0`,
  `c = 0` — `v 0 = 0` (all coefficients vanish since `lin` is linear and `A=0`), hypothesis
  `step·0 ≤ 0` holds with equality, `Pg`-a.e. the linear part is the constant `0`, degenerate but
  true. **And** a non-trivial witness: `A := fun _ => E_{11}` (constant, hence filt-`k`-measurable
  for every `k`; needs `d.Idx N` nonempty, true since `d.L N ≥ 3` and `d.W_pos`), `E := univ`,
  `c := step s t K N * gvar d ⟨N,(0:ZMod (d.L N)),(0:ZMod (d.L N)),(0,by omega),true⟩` — wait, `Idx N
  = ZMod (d.L N) × Fin (d.W N)`; any fixed index `i₀ : d.Idx N` works, so
  `c := step s t K N * gvar d ⟨N,i₀,i₀,true⟩` with `i₀` the (nonempty, since `d.L N ≥ 3`) default
  index — genuinely non-degenerate whenever `Sblk (d.L N)(d.W N) i₀ i₀ > 0` and `step s t K N ≥ 0`
  (both standing assumptions of the paper's grid, s ≤ t). This matches the acceptance criterion's
  requested witness shape (`E=univ`, `A=0`, `c=0`, plus one nonzero `A`).

Verdict: **PASS**, mathematically sound and non-vacuous. Lean cost is high (a genuine
finite-linear-form-in-a-Gaussian-band-matrix construction); see "Open issues" below for how much of
it is actually discharged in this pass.

## (T3) `condExp_linear_eq_zero` — math preflight: **PASS**

Under the same hypotheses as (T2) plus integrability, `(Pg d)[same variable | filt d k] =ᵐ 0`.
This is the mean-zero half of the same Gaussian fact used for (T2) (a centred Gaussian has mean
`0`), or directly an instance of (T1) with `F(y,x) := √Δ·lin y (Xmat d N x)` (linear, hence
`∫ F(y,x) dP(x) = 0` because `lin y ∘ Xmat d N` is a finite real-linear form in independent centred
coordinates, so its integral against `P d` is `0` by centring + linearity of the integral, no need
for the full Gaussian-law identification). Quantifiers, dependencies, non-vacuity: identical to
(T2). Verdict: **PASS**, and in fact easier than (T2) once (T1) and the linearity fact for `lin`
are in place (mean-zero is linearity + centring, not the full Gaussian-law computation).

## Lean status of this pass

Implemented in `RBM1D/Gauss/GridMarkov.lean` (325 lines), all under `RBM.Gauss.Grid`. No
`sorry`/`admit`/`axiom`.

* **(T1) `condExp_freeze`** — done, exactly as specified in the ticket.
* **(T3) `condExp_linear_eq_zero`** — done. Signature: `A : Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ`
  filt-`k`-measurable, `E ∈ filt d k`, plus **integrability of the un-truncated linear functional**
  `fun ω => √(step s t K N) · lin N (A ω) (Xmat d N (ω (k+1)))` (this is the natural reading of the
  ticket's "hypotheses of (T2) plus integrability": it is what makes (T1) applicable, and it is
  *stronger* than integrability of the `E`-truncated variable, which follows from it via
  `Integrable.indicator`, so nothing needed for the conclusion is lost). Proved via (T1) applied to
  the identity, `map_lin_Xmat`'s mean-zero corollary `integral_lin_Xmat`, and pulling the
  `filt d k`-measurable indicator of `E` out of the conditional expectation
  (`condExp_mul_of_stronglyMeasurable_left`).
* **(T2) `hasCondSubgaussianMGF_linear`** — math preflight PASS (argued above), **not completed in
  Lean this pass**. What is done and reusable: `lin`, `coordFinset`, the linear-decomposition
  lemma `lin_Xmat_eq_sum`, the variance `v` and its Gaussian-law identification `map_lin_Xmat`
  (for a *fixed* matrix `A`, `y ↦ lin N A (Xmat d N y)` is `gaussianReal 0 (v N A)` under `P d` —
  this already gives the *exact* conditional variance formula the audit asks to sanity check),
  plus `integral_lin_Xmat` (its mean is `0`). What remains: substituting
  `A' := Set.piecewise E A 0` (uniformly satisfying `Δ·v(A'ω) ≤ c` for *every* `ω`, not just
  `ω ∈ E`, which removes the indicator from the target variable entirely: `X = fun ω => √Δ·lin N
  (A'ω)(Xmat d N (ω(k+1)))` identically), then building `Kernel.HasSubgaussianMGF` from: (i)
  integrability of `exp(t·X)` for every `t`, via the unconditional Tonelli identity
  `RBM.Gauss.lintegral_indep_pair` (already in the repo, unrelated to this ticket) applied to
  `U := (fun ω => ω (k+1))`, `V := A'`, dominated a.e. w.r.t. `(Pg d).map A'` by the constant
  `exp(c·t²/2)` (using that `Δ·v(A'ω) ≤ c` holds for *every* `ω`, hence `(Pg d).map A'`-a.e.); (ii)
  the a.e.-in-`condExpKernel` mgf bound, via the same `condExp_ae_eq_trim_integral_condExpKernel`
  bridge used by the existing `actualPrefix_increment_hasCondSubgaussianMGF` pattern
  (`Gauss/PermutationFourierDoobCondMGF.lean:72`), replacing its Hoeffding step with
  `ProbabilityTheory.mgf_gaussianReal` applied through `map_lin_Xmat`. This is a genuine further
  construction (condExpKernel plumbing), comparable in size to what is already in this file; not
  attempted further in this pass to keep the delivered material fully checked.

## Declarations, build, axioms

File: `RBM1D/Gauss/GridMarkov.lean`.

```
$ lake build RBM1D.Gauss.GridMarkov
...
Build completed successfully (3708 jobs).
```
(no warnings or errors from `GridMarkov.lean` itself; only pre-existing lint warnings from files
it imports, unrelated to this ticket).

`#print axioms` on every new public declaration (`condExp_freeze`, `lin`, `coordFinset`,
`mem_coordFinset`, `lin_Xmat_eq_sum`, `v`, `v_nonneg`, `map_lin_Xmat`, `integral_lin_Xmat`,
`condExp_linear_eq_zero`) lists only `propext`, `Classical.choice`, `Quot.sound`.

## Key lemmas used

* T1481 (`GridPath.lean`): `filt`, `Ωg`, `Pg`, `P`, `indep_incr`, `map_incr`.
* Mathlib: `Indep_iff`, `Measure.prod_eq`, `IndepFun.map_prod_eq_prod_map_map`, `integral_prod`,
  `integral_map`, `ae_eq_condExp_of_forall_setIntegral_eq`, `condExp_mul_of_stronglyMeasurable_left`
  (T1, T3); `gaussianReal`, `integral_id_gaussianReal`, `Matrix.trace_add`/`trace_smul`,
  `Complex.re_sum`, `StandardBorelSpace.pi_countable` (T2/T3 groundwork).
* Repo (pre-existing, unrelated to this ticket): `RBM.Gauss.map_sum_const_mul_coord` and
  `RBM.Gauss.linVar` (`Gauss/LinearForm.lean`) — the "finite real-linear combination of the
  independent coordinates is Gaussian with the weighted-sum variance" fact this ticket's `v` and
  `map_lin_Xmat` are built on.

## Open issues

* (T2) preflight PASS but not completed in Lean this pass (see "Lean status" above for exactly
  what remains and the intended route). No hypothesis was weakened, no signature changed to get
  here; the file only contains what type-checks.
* The standard-Borel hypothesis on `β` in (T1) is unused by the proof (noted above); kept for
  fidelity to the ticket text. A local bridging instance `StandardBorelSpace (Matrix (d.Idx N)
  (d.Idx N) ℂ)` was added (`instStandardBorelSpaceMatrix`, private) since Mathlib's
  `Matrix.instMeasurableSpace` does not automatically unify with its own `Pi`-type
  `StandardBorelSpace` instance (the `Matrix` wrapper is a `def`, not `abbrev`).
* T3's integrability hypothesis is stated as integrability of the un-truncated linear functional
  rather than the literal `E`-truncated variable named in the ticket's target; see "Lean status"
  above for why this is the natural, non-weakening reading of "plus integrability".

## Continuation pass

Prover model: claude-sonnet-5

Target: (T2) `hasCondSubgaussianMGF_linear` only. (T1) `condExp_freeze` and (T3)
`condExp_linear_eq_zero` were already committed on `t/T1482` and were **not touched** (verified by
`git diff --stat` before committing: the diff is a pure addition after T3's proof, no lines inside
T1/T3 changed).

Math preflight for (T2) was already marked **PASS** in the section above (no change to that
verdict); this pass only had to write the Lean.

### Route taken (as specified by the dispatcher)

* `A' := fun ω => if ω ∈ E then A ω else 0` (the `E`-piecewise truncation), so the target variable
  `E.indicator (fun ω => √Δ · lin N (A ω) (Xmat d N (ω (k+1))))` is definitionally equal (via a
  `by_cases ω ∈ E` case split, using `lin N 0 X = 0`, new lemma `lin_zero`) to the un-truncated
  `fun ω => √Δ · lin N (A' ω) (Xmat d N (ω (k+1)))` — this removes the indicator from the target
  entirely, as the route anticipated.
* The deterministic bound `step s t K N · v N (A ω) ≤ c` for `ω ∈ E` (hypothesis) extends to
  `step s t K N · v N (A' ω) ≤ c` for **every** `ω` (new lemma `v_zero : v N 0 = 0`, plus `hc : 0 ≤
  c` for the `ω ∉ E` branch), and then to `(√Δ)² · v N (A' ω) ≤ c` for every `ω` regardless of the
  sign of `Δ = step s t K N` (a `by_cases 0 ≤ Δ` split using `Real.sq_sqrt`/`Real.sqrt_eq_zero_of_
  nonpos`, so the statement needs no added hypothesis `s N ≤ t N`).
* Unconditional integrability of `exp (r · X)` (new private lemma `integrable_exp_mul_X`): Tonelli
  via `RBM.Gauss.lintegral_indep_pair` applied to `U := fun ω => ω (k+1)` and `V := A'`, using
  `map_incr` to identify `(Pg d).map U = P d`. The inner integral (over the independent increment,
  for a *fixed* direction `y`) is computed **exactly** as the Gaussian mgf `exp (v N y · (r√Δ)² /
  2)` via two new private lemmas `mgf_lin_Xmat` (the mgf of the fixed-direction frozen linear
  functional, via `map_lin_Xmat` + `ProbabilityTheory.mgf_gaussianReal`) and
  `integrable_exp_lin_Xmat` (the real-valued integrability needed for `ofReal_integral_eq_
  lintegral_ofReal`, pulled back from `integrable_exp_mul_gaussianReal` along `map_lin_Xmat`). The
  bound `(√Δ)² · v N (A' ω) ≤ c`, holding for *every* `ω`, is converted into an a.e.-in-`(Pg
  d).map A'` statement via `MeasureTheory.ae_map_iff` (new private lemma `measurable_v` supplies
  the needed measurability of `y ↦ v N y`), then the outer lintegral is bounded using `lintegral_
  mono_ae` + `lintegral_const` + `prob_le_one`.
* The a.e. conditional mgf identity (new private lemma `condMGF_le`, for a *fixed* real `r`): apply
  `condExp_freeze` (T1) with `Y := A'` and `F(y,x) := exp (r · (√Δ · lin N y (Xmat d N x)))`
  (jointly measurable, integrable by `integrable_exp_mul_X`) to get the a.e.-in-`Pg d` identity of
  `(Pg d)[exp(r·X) | filt d k]` with `fun ω => exp (v N (A' ω) · (r√Δ)² / 2)`; transport this to
  `(Pg d).trim hm` via `StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`; bridge to the
  `condExpKernel` fiber integral via `condExp_ae_eq_trim_integral_condExpKernel`; conclude
  `mgf X (condExpKernel (Pg d) (filt d k) ω) r ≤ exp (c r² / 2)` a.e. from the pointwise bound.
* Assembly: `Kernel.HasSubgaussianMGF.of_rat` (the Mathlib constructor that swaps `∀ᵐ` and `∀ t`
  via the countable-rational + continuity trick, avoiding a genuine uncountable swap) with `h_int
  := integrable_exp_mul_X` (via `condExpKernel_comp_trim` to identify `κ ∘ₘ ν = Pg d`) and `h_mgf
  := fun q => condMGF_le hA'meas hc hAle2 (q : ℝ)`. The final `HasCondSubgaussianMGF` goal is
  unfolded to `Kernel.HasSubgaussianMGF` via `change` (matching the `Kernel.HasSubgaussianMGF`
  target used by the existing `actualPrefix_increment_hasCondSubgaussianMGF` precedent).

### A genuine Lean pitfall found and fixed (recorded for future reference)

Several intermediate lemmas (`Measurable (fun x => lin N A (Xmat d N x))` etc.) were first written
by discharging the goal with `(measurable_lin_uncurry N).comp h` for a suitable `h`, relying on
Lean's elaborator to check the resulting composed function is *definitionally* equal to the
literal goal. This reproducibly caused **deterministic timeouts at `whnf`/`isDefEq`** (200000
heartbeats) during `lake build`, with the timeout attributed to the declaration's docstring/start
line rather than the actual expensive tactic. The fix (matching the pattern already used
successfully elsewhere in this file, e.g. the pre-existing `integral_lin_Xmat`'s `hmeas`): first
`rw` the goal into the explicit double-`Finset.sum` form via `lin_eq_sum`, so measurability is then
built from elementary `Matrix`/`Xmat` entry projections directly, never asking Lean to verify a
nontrivial defeq between a `.comp`-composed term and the original `lin N _ (Xmat d N _)`-shaped
goal. Applied at three sites: `measurable_lin_Xmat`, and two internal `have`s inside
`integrable_exp_mul_X` (`hFmeas`'s inner sum-measurability and `hXmeas`'s `h1`).

### Lean status of this pass

Implemented entirely in `RBM1D/Gauss/GridMarkov.lean` (append-only; T1/T3 untouched), still under
`RBM.Gauss.Grid`. New declarations: `lin_zero`, `v_zero`, `measurable_lin_left`, `v_eq_sum`,
`measurable_v`, `measurable_lin_Xmat`, `mgf_lin_Xmat`, `integrable_exp_lin_Xmat` (all `private`);
`integrable_exp_mul_X`, `condMGF_le` (`private`, inside a local `section MGFBound`); and the public
**`hasCondSubgaussianMGF_linear`** (T2), matching the ticket's signature exactly (`A` filt-`k`-
measurable, `E` filt-`k`-measurable, `c : ℝ` with `hc : 0 ≤ c`, `hbound : ∀ ω ∈ E, step s t K N · v
N (A ω) ≤ c`, conclusion `HasCondSubgaussianMGF (filt d k) ((filt d).le k) (...) ⟨c, hc⟩ (Pg d)`).
No `sorry`/`admit`/`axiom`.

```
$ lake build RBM1D.Gauss.GridMarkov
...
Build completed successfully (3708 jobs).
```
Only warnings from this file: one benign `linter.unusedVariables` note that `integrable_exp_mul_X`
does not use its own `hc` hypothesis (true — that lemma's inner `nlinarith` only needs `hAle2` and
`sq_nonneg r`, not `c ≥ 0` itself; the hypothesis is kept for signature-shape consistency with the
public theorem and is genuinely used at the call site `condMGF_le`/`integrable_exp_mul_X hc hAle2
...`'s sibling uses of `c`). No warnings or errors specific to logic; no `sorry`/`admit`/`axiom`.

`#print axioms RBM.Gauss.Grid.hasCondSubgaussianMGF_linear` (via `lake env lean` on a throwaway
file importing the module):
```
'RBM.Gauss.Grid.hasCondSubgaussianMGF_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Key lemmas used (T2, this pass)

* This ticket, already committed: `condExp_freeze` (T1).
* Repo (pre-existing): `RBM.Gauss.map_sum_const_mul_coord`/`RBM.Gauss.linVar` (via `map_lin_Xmat`,
  already committed with T2's groundwork); `RBM.Gauss.lintegral_indep_pair`
  (`Gauss/LinearForm.lean:243`); T1481's `indep_incr`, `map_incr`.
* Mathlib: `ProbabilityTheory.mgf_gaussianReal`, `integrable_exp_mul_gaussianReal`
  (`Probability/Distributions/Gaussian/Real.lean`); `ProbabilityTheory.Kernel.HasSubgaussianMGF.
  of_rat`, `ProbabilityTheory.condExpKernel_comp_trim`,
  `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel` (`Probability/Kernel/Condexp.lean`,
  `Probability/Moments/SubGaussian.lean`); `MeasureTheory.ae_map_iff`;
  `ofReal_integral_eq_lintegral_ofReal`; `StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`.

### Open issues (this pass)

* None outstanding for (T2): all three ticket targets (T1)–(T3) are now committed on `t/T1482`,
  each type-checking with `lake build RBM1D.Gauss.GridMarkov`, no `sorry`/`admit`/`axiom`, printed
  axioms limited to `propext`/`Classical.choice`/`Quot.sound`.
* The two pre-existing open issues noted above (T1's unused `StandardBorelSpace β` hypothesis, and
  T3's integrability hypothesis stated on the un-truncated variable) still stand as documented;
  neither was touched or affected by this pass.
