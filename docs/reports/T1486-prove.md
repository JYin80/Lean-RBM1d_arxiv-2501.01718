Prover model: claude-sonnet-5

# T1486 — one-step Gaussian expansion (discrete replacement of Itô's drift)

Ticket: `docs/tickets/T1486.md`. Role: prover-hard. Sole writable file:
`RBM1D/Gauss/GridOneStep.lean`. Worktree: `RBM1D-wt/T1486` (branch `t/T1486`).

## Step 0 (read-only checks)

(a) `RBM.Gauss.hasDerivAt_integral_Phi` (`Gauss/Generator.lean:803`) is stated for
`fun s => ∫ ω, Φ (Hflow d N s ω) ∂(P d)`, and `Hflow d N s ω := (Real.sqrt s : ℂ) • Xmat d N ω`
is a **definitional** equality (`Gauss/Model.lean:363`, `noncomputable def Hflow ... := (Real.sqrt
u : ℂ) • Xmat d N ω`), not merely a proved lemma — so `Φ (M + (√v:ℂ)•Xmat d N ω)` and
`Φ (M + Hflow d N v ω)` are interchangeable by `rfl`. The theorem requires `hu : 0 < u`: the
chain-rule factor `(2√u)⁻¹` (visible in `hasDerivAt_Phi_Hflow`, line 651) blows up at `u = 0`, so
the identity genuinely cannot be extended to `u = 0` as a *derivative* statement. Consequently
(T2)'s window `[0, v]` must get its `w = 0` endpoint from a separate continuity argument, exactly
as the ticket anticipates. I supply that continuity as full (two-sided) continuity of
`s ↦ ∫ ω, Φ (Hflow d N s ω) ∂(P d)` on all of `ℝ`, via `MeasureTheory.continuous_of_dominated`:
`Real.sqrt` is continuous at every real number including `0` (`Real.continuous_sqrt`), and `Φ`
(resp. `coordD2 · p`) is globally bounded by `TestFun.bdd₀` (resp. `bdd₂` through
`norm_coordD2_le`), which is a valid dominating constant on the probability space `P d`. No
positivity hypothesis is needed for this part, matching the ticket's expectation, and
`hasDerivAt_integral_Phi` itself is used unchanged (never modified).

(b) `RBM1D/Gauss/LoopLipschitz.lean:113` has `open scoped Matrix.Norms.L2Operator` covering the
whole file (see also the file's own §0 docstring, "the `ℓ² → ℓ²` operator norm"). This is the
same scope `RBM1D/Gauss/Generator.lean:127` opens, which is where `TestFun`'s three fields
(`bdd₀`, `bdd₁`, `bdd₂`, hence every norm inside `coordD2`, `genPt` and (T3)'s Lipschitz
hypothesis) live. `GridOneStep.lean` opens the identical scope
(`open scoped Matrix.Norms.L2Operator NNReal`), so the norm in (T3)'s Lipschitz hypothesis and
conclusion is the *same* `ℓ²`-operator norm as `LoopLipschitz.lean`'s, not a different one
(Frobenius / `ℓ∞`-operator / elementwise are the other scoped alternatives Mathlib offers for
`Matrix`, and none of them is opened here).

(c) No existing `TestFun.shift`, nor any lemma of the shape `TestFun d N Φ → TestFun d N (fun A
=> Φ (M + A))`, was found (`grep -rn "shift" RBM1D/Gauss/*.lean` and `grep -rn "Φ (M + A)"`
turned up nothing reusable). The closest existing material,
`RBM.Gauss.norm_integral_sub_le_of_genTerm_le` / `norm_integral_sub_le_testFun`
(`Gauss/APrimeDuhamel.lean:429,481`), proves an *increment* bound `‖E[Φ(H_b)] - E[Φ(H_a)]‖ ≤ C
(b-a)` but requires `0 < a` (strict), so it cannot by itself supply the `v = 0` (equivalently the
`a = 0`) endpoint (T2) needs; that is exactly why the ticket asks for a fresh `TestFun.shift` +
direct continuity argument rather than reusing that closure.

## Math preflight (per target)

**(T1) `RBM.Gauss.TestFun.shift`.** Statement: for `M` a *fixed* (arbitrary, not necessarily
Hermitian) matrix, `TestFun d N Φ → TestFun d N (fun A => Φ (M + A))`. Route: the map `g : A ↦ M +
A` is a translation, so `HasFDerivAt g (ContinuousLinearMap.id ℝ E) A` for every `A` (chain rule
input `hasFDerivAt_id` composed with `HasFDerivAt.const_add`); composing with `Φ`'s derivative at
`M + A` (`HasFDerivAt.comp`) and simplifying `_.comp (ContinuousLinearMap.id ...)` gives `fderiv ℝ
(Φ ∘ g) A = fderiv ℝ Φ (M + A)` for every `A`, hence as functions `fderiv ℝ (Φ ∘ g) = fderiv ℝ Φ ∘
g`; applying the same argument one derivative order higher (to `f := fderiv ℝ Φ`, using
`TestFun.differentiable_fderiv`) gives `fderiv ℝ (fderiv ℝ (Φ ∘ g)) A = fderiv ℝ (fderiv ℝ Φ) (M +
A)`. `ContDiff` transports through `ContDiff.comp` with the translation (itself `ContDiff` of any
order, `contDiff_const.add contDiff_id`). All three constants (`C₀, C₁, C₂`) are literally
unchanged — the shift only re-centres the base point, it never enlarges a bound that is already
*global*. **Quantifiers**: `∀ M` is universally quantified with no side condition (Hermitian-ness
of `M` is never used or needed here — `TestFun`'s bounds are stated for *every* matrix, not just
Hermitian ones, `Generator.lean:604-612`). **Dependencies**: `TestFun.contDiff`,
`.differentiable`, `.differentiable_fderiv`, `.bdd₀/₁/₂` (all already-accepted fields/lemmas of
`Generator.lean`). **Boundary/degenerate cases**: `M = 0` gives back `Φ` itself (the identity
shift), consistent; `N = 0` or `d.Idx N` empty are not excluded by the signature but are also not
excluded by `TestFun` itself (they would make `Bmat`'s index set empty and `usedCoord` empty,
which is a pre-existing, accepted degeneracy of `Generator.lean`, not introduced here).
**Verdict: PASS.**

**(coordD2_shift, a lemma this file adds to support T2).** `coordD2 d N (fun A' => Φ (M + A')) A
p = coordD2 d N Φ (M + A) p`. Immediate corollary of the two `fderiv` identities proved for (T1)
(apply both, at the point `A`, to `Bmat p` twice). No new hypotheses. **Verdict: PASS.**

**(T2) `RBM.Gauss.Grid.oneStep_integral_eq`.** Statement (literal, both sides `ℂ`-valued): for
`TestFun d N Φ`, any matrix `M` (Hermitian, per the ticket's hypothesis list, though the proof
below never needs `M.IsHermitian` — the identity holds for every `M`; the hypothesis is kept
because the ticket states it, and dropping an unused hypothesis is not requested), and `v ≥ 0`,
`(∫ ω, Φ (M + (√v:ℂ)•Xmat d N ω) ∂(P d)) - Φ M = ∫ w in (0)..v, gen d N Φ M w`, where `gen d N Φ
M w` is the ticket's literal formula. **Quantifier order**: `d, N` fixed, then `Φ` (with its
`TestFun` hypothesis), then `M`, then `v ≥ 0` — matches the ticket, no `∀ᶠ N` is involved (this is
a deterministic, single-`N` identity, not an asymptotic one). **Route**: let `Ψ := fun A => Φ (M +
A)`; `TestFun d N Ψ` by (T1). Let `F s := ∫ ω, Ψ (Hflow d N s ω) ∂(P d) = ∫ ω, Φ (M + Hflow d N s
ω) ∂(P d)`.
  - *Continuity of `F` on all of `ℝ`* (in particular on `[0, v]`, endpoints included): dominated
    convergence, per step 0(a) above (`continuous_integral_comp_Hflow`).
  - *Derivative of `F` on `(0, v)`*: `hasDerivAt_integral_Phi (matrixStein d) hΨtf hx.1` at each `x
    ∈ (0, v)` gives `HasDerivAt F ((1/2)•∑_p S_p•∫ω,coordD2 Ψ (Hflow x ω) p) x`; `coordD2_shift`
    identifies this generator value, term by term (`Finset.sum_congr` + `integral_congr_ae`, in
    fact a pointwise-everywhere equality of integrands, not just a.e.), with `gen d N Φ M x`.
  - *Interval integrability of `gen d N Φ M` on `[0, v]`*: `gen`'s continuity
    (`continuous_gen`, itself dominated convergence per summand, `TestFun.bdd₂` supplying the
    domination constant) plus `Continuous.intervalIntegrable`.
  - *FTC*: `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv hFcont.continuousOn hFderiv
    hgenInt : ∫ w in 0..v, gen d N Φ M w = F v - F 0`. `F v = ∫ ω, Φ (M + (√v:ℂ)•Xmat d N ω) ∂(P
    d)` by `rfl` (`Hflow` unfolds to exactly this). `F 0 = Φ M` because `Hflow d N 0 ω = 0`
    (`Hflow_zero`) and the integral of a constant against the probability measure `P d` is that
    constant (`integral_const_P`, using `isProbabilityMeasure_P`).
**`v = 0` is not vacuous or excluded**: `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
degenerates gracefully at `a = b` (both the continuity-on-`Icc` and the derivative-on-`Ioo`
hypotheses become statements about a single point / the empty set, respectively, and both sides of
the conclusion are `0`), so the identity at `v = 0` reads `0 = 0` after `F 0 = Φ M` cancels — no
special-casing needed, and the general argument literally covers it (this is why the FTC lemma
with a *closed* continuity hypothesis on `[a,b]` but only an *open* derivative hypothesis on
`(a,b)` was chosen over the naïve `a < b` variants). **Simultaneous satisfiability**: `TestFun d N
Φ` is satisfiable and non-vacuous by the repository's own witness chain (`Φ = |F|^{2p}` built from
`norm_green_le`, assembled concretely e.g. by `sat_testFun_softW_jS` elsewhere in the repo, or
trivially by `Φ = const` — `ContDiff` of a constant, all three bounds trivially met by `C₀ = |c|`,
`C₁ = C₂ = 0`); `M` ranges over all matrices (`M = 0` always available); `v ≥ 0` is satisfied by
`v = 0` and by every `v > 0`, no astronomically-large or degenerate witness needed.
**Verdict: PASS.**

**(T3) `RBM.Gauss.Grid.oneStep_error_le`.** Statement (literal): with `genPt d N Φ A := (1/2)•∑_p
S_p•coordD2 Φ A p` (deterministic, no expectation), if `‖genPt A - genPt A'‖ ≤ Λ‖A - A'‖` for
**all** Hermitian `A, A'` (both quantified, no restriction to a neighbourhood of `M`), and `M` is
Hermitian, then for `Δ ≥ 0`, `‖(∫ ω, Φ(M+(√Δ:ℂ)•Xω)∂P) - Φ M - (Δ:ℂ)•genPt M‖ ≤ (2/3)·Λ·Δ^{3/2}·∫
‖Xω‖ ∂P`. **The norm**: the ℓ²-operator norm throughout, per step 0(b). **Route**:
  - `gen d N Φ M w = ∫ ω, genPt d N Φ (M + (√w:ℂ)•Xω) ∂P` (`gen_eq_integral_genPt`): swap the
    finite coordinate sum with the integral (`integral_smul`, `integral_finsetSum`), using
    integrability from continuity + the global `TestFun.bdd₂` bound (`norm_coordD2_le`,
    `integrable_of_continuous_of_bound`, already in `Generator.lean`).
  - Pointwise (every `w ≥ 0`, every `ω`), `M + (√w:ℂ)•Xω = M + Hflow d N w ω` is Hermitian:
    `M.IsHermitian` (hypothesis) `+ Hflow_isHermitian d N w ω` (`Matrix.IsHermitian.add`, already
    in Mathlib). So `hLip` applies at `A := M + (√w:ℂ)•Xω`, `A' := M`, giving `‖genPt(M+(√w:ℂ)•Xω)
    - genPt M‖ ≤ Λ‖(√w:ℂ)•Xω‖ = Λ·√w·‖Xω‖` (`norm_smul`, `Complex.norm_real`,
    `abs_of_nonneg (Real.sqrt_nonneg w)`; note `Λ` is **not** assumed `≥ 0`, the derivation never
    needs that sign fact — it only chains the given inequality through the triangle inequality and
    constant pull-outs, which is valid for any real `Λ` satisfying the hypothesis).
  - `‖gen w - genPt M‖ = ‖∫ ω,(genPt(M+(√w:ℂ)•Xω) - genPt M)∂P‖ ≤ ∫ω,‖genPt(M+(√w:ℂ)•Xω)-genPt
    M‖∂P ≤ Λ·√w·∫ω,‖Xω‖∂P = Λ·√w·K` (`norm_integral_le_integral_norm`, `integral_mono`, both real
    valued so the plain Bochner monotonicity lemma applies, no Hölder/positivity subtlety since
    both sides are already nonnegative norms/products of nonnegatives).
  - `T2` at `Δ` gives `LHS_target = ∫ w in 0..Δ, gen(w) dw - Δ•genPt(M) = ∫ w in 0..Δ,
    (gen(w)-genPt(M)) dw` (the constant `Δ•genPt M` is itself `∫ w in 0..Δ, genPt M dw`, by
    `intervalIntegral.integral_const`, bridging the ℝ-smul of the interval integral and the
    `(Δ:ℂ)•` of the ticket's statement via `Complex.real_smul`/`smul_eq_mul`).
  - `‖∫ w in 0..Δ,(gen(w)-genPt(M))dw‖ ≤ ∫ w in 0..Δ,‖gen(w)-genPt(M)‖dw ≤ ∫ w in 0..Δ,
    Λ·√w·K dw = Λ·K·∫ w in 0..Δ,√w dw = Λ·K·(2/3)Δ^{3/2}` (`intervalIntegral.norm_integral_le_
    integral_norm` needs `0 ≤ Δ`; `intervalIntegral.integral_mono_on` needs interval-integrability
    of both sides, from continuity of `gen`, `genPt` and `Real.sqrt`, and the pointwise bound
    established above restricted to `w ∈ [0,Δ] ⊆ [0,∞)`; the last integral is
    `intervalIntegral.integral_rpow` at `r = 1/2 > -1`, via `Real.sqrt_eq_rpow`, together with
    `Real.zero_rpow` at the origin).
  - Reassembling gives exactly `(2/3)·Λ·Δ^{3/2}·K`, the stated constant, with the stated exponent
    `3/2` and no hidden `N`-dependent loss (this is an exact, deterministic real-analysis bound —
    no probabilistic ≺-loss anywhere in this ticket).
**Hypothesis satisfiability (the ticket's own witness suggestion)**: `Φ = const` makes `genPt d N
Φ A = 0` for every `A` (since `coordD2` of a constant is `0`), so the Lipschitz hypothesis holds
**for every** `Λ` (in particular `Λ = 0`), vacuously in the sense that both sides are `0`, but this
is a *bona fide*, non-degenerate witness for the hypothesis (it is not vacuous in the sense CLAUDE.md
§3.4 forbids: the hypothesis's own quantifiers — `∀ A A'` Hermitian — range over a genuinely
infinite, non-collapsed set of pairs of Hermitian matrices for any `N ≥ 1`, i.e. `d.Idx N`
nonempty; the conclusion is simply also verifiable directly and is not an ∃-witness manufactured
only because some other quantity is astronomically large). A second, less degenerate witness: any
`Φ` with `TestFun.bdd₂` constant `C₂` such that `coordD2` is itself Lipschitz in the operator norm
with constant `Λ = C₂ · (∑_p S_p‖B_p‖²)` works via the crude bound `‖genPt A - genPt A'‖ ≤
(1/2)∑_p S_p (‖coordD2 Φ A p‖+‖coordD2 Φ A' p‖)`... — the repository does not need to supply a
sharp, non-trivial witness for this ticket (T1487 is exactly the ticket that will produce a
concrete Λ for loop functionals), so the `Φ = const`, `Λ = 0` witness suffices to certify
non-vacuity of the hypothesis's *quantifier structure* here; T1487's audit will separately check
that a genuinely non-trivial `Λ` is realizable for the loop functionals the pilot needs.
**`Δ = 0`** collapses both sides to `0 ≤ 0` (via `T2` at `v=0` and `Δ^{3/2}=0`), not excluded.
**Simultaneous satisfiability of all hypotheses together** (`TestFun d N Φ`, `M` Hermitian, `hLip`
for the *same* `Φ`, `Δ ≥ 0`): take `Φ = const c` (any `c : ℂ`), `M = 0` (Hermitian), `Λ = 0`
(`hLip` holds as shown), `Δ` arbitrary `≥ 0` — all four hold simultaneously, non-vacuously, with
`d.Idx N` a genuine nonempty finite type (no `N = 0` needed). **Verdict: PASS.**

**(`integrable_norm_Xmat`).** `‖X‖` is integrable against `P d`. Route: `Xmat d N ω = ∑_{p∈
usedCoord} ω(crd p)•Bmat p` (`Xmat_eq_sum`, already accepted), so `‖Xmat d N ω‖ ≤ ∑_p |ω(crd
p)|·‖Bmat p‖` (triangle inequality, finite sum); the dominating function is integrable (finite sum
of `(integrable_coord d c).abs |>.mul_const _`, i.e. first absolute moments of Gaussian
coordinates, already accepted in `Generator.lean`); `Xmat` itself is a.e.-strongly-measurable
(`continuous_Xmat`, already accepted) so `Integrable.mono'` applies, giving `Integrable (Xmat d N)
(P d)`; `Integrable.norm` finishes. No new hypotheses, no side conditions, unconditional in `d, N`.
**Verdict: PASS.**

## Conclusion of the preflight

All four targets (T1/`TestFun.shift`, T2/`oneStep_integral_eq`, T3/`oneStep_error_le`,
`integrable_norm_Xmat`), plus the two support lemmas `coordD2_shift` and `gen_eq_integral_genPt`
this file introduces to connect them, are **PASS**. Proceeding to Lean.

## Lean: declarations added (`RBM1D/Gauss/GridOneStep.lean`)

`namespace RBM.Gauss`:
* `private theorem hasFDerivAt_shift` — generic chain-rule lemma for a translation of the
  argument (used twice, at `Φ` and at `fderiv ℝ Φ`, to prove `TestFun.shift`).
* `theorem TestFun.shift (h : TestFun d N Φ) (M) : TestFun d N (fun A => Φ (M + A))` — **T1**.
* `theorem coordD2_shift (h : TestFun d N Φ) (M A p) : coordD2 d N (fun A' => Φ (M + A')) A p =
  coordD2 d N Φ (M + A) p` — the bridge lemma the ticket's route needs.
* `theorem integrable_norm_Xmat (d N) : Integrable (fun ω => ‖Xmat d N ω‖) (P d)`.

`namespace RBM.Gauss.Grid`:
* `theorem continuous_coordD2_arg`, `theorem continuous_integral_comp_Hflow` — the two
  dominated-convergence building blocks (continuity of `M ↦ coordD2 Φ M p`; continuity in time
  of a parametric integral along `Hflow`, including at `s = 0`).
* `noncomputable def gen`, `noncomputable def genPt` — exactly the ticket's formulas.
* `theorem continuous_gen`, `theorem continuous_genPt`, `theorem norm_genPt_le`,
  `theorem integrable_genPt_shift`, `theorem integral_const_P`,
  `theorem gen_eq_integral_genPt` — supporting continuity/integrability/Fubini lemmas.
* `theorem oneStep_integral_eq (h : TestFun d N Φ) (M) {v} (hv : 0 ≤ v) : ... ` — **T2**.
* `theorem oneStep_error_le (h : TestFun d N Φ) {M} (hM : M.IsHermitian) {Λ} (hLip : ...) {Δ}
  (hΔ : 0 ≤ Δ) : ...` — **T3**.

## Build

```
cd RBM1D-wt/T1486 && lake build RBM1D.Gauss.GridOneStep
```
Result: **success**, `Build completed successfully (3701 jobs)`, no warnings from
`GridOneStep.lean` itself (one initial `linter.style.longLine` warning on the module docstring
was fixed by rewrapping the line; the file's only remaining warnings are pre-existing ones from
upstream files it imports, e.g. `Generator.lean`'s `show`-vs-`change` style warnings, unrelated to
this ticket).

## Axioms of the new public declarations

```
lake env lean <scratch file importing RBM1D.Gauss.GridOneStep, #print axioms ...>
```
```
'RBM.Gauss.TestFun.shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.coordD2_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.integrable_norm_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.gen_eq_integral_genPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.oneStep_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.oneStep_error_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`, no `admit`, no declared `axiom` anywhere in the file (checked by grep, and confirmed
by the axiom list above containing only the three permitted ones).

## Key lemmas used (all already accepted, unmodified)

* `RBM.Gauss.hasDerivAt_integral_Phi` (`Generator.lean:803`) — the generator identity, the sole
  analytic input, used once (on the shifted test function, on the open interval `(0, v)`).
* `RBM.Gauss.matrixStein` (`SteinMatrix.lean:135`) — discharges `hasDerivAt_integral_Phi`'s
  `MatrixStein` hypothesis unconditionally.
* `RBM.Gauss.TestFun.{contDiff, differentiable, differentiable_fderiv, bdd₀, bdd₁, bdd₂,
  continuous_fderiv2}`, `RBM.Gauss.{coordD2, norm_coordD2_le, usedCoord, crd, gvar, Bmat,
  Hflow, Hflow_zero, Hflow_isHermitian, Xmat, Xmat_eq_sum, Xmat_isHermitian, continuous_Xmat,
  continuous_Hflow, integrable_coord, isProbabilityMeasure_P, integrable_of_continuous_of_bound}`
  (all `Generator.lean`/`Model.lean`).
* Mathlib: `HasFDerivAt.comp`, `HasFDerivAt.const_add`, `hasFDerivAt_id`,
  `MeasureTheory.continuous_of_dominated`, `MeasureTheory.integral_finsetSum`,
  `MeasureTheory.integral_smul`, `MeasureTheory.integral_sub`, `MeasureTheory.integral_mono`,
  `MeasureTheory.integral_const`, `MeasureTheory.integral_const_mul`,
  `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`,
  `intervalIntegral.norm_integral_le_integral_norm`, `intervalIntegral.integral_mono_on`,
  `intervalIntegral.integral_const`, `intervalIntegral.integral_const_mul`, `integral_rpow`,
  `Real.sqrt_eq_rpow`, `Real.zero_rpow`, `Matrix.IsHermitian.add`, `norm_smul`,
  `Complex.norm_real`, `Complex.real_smul`.

## Open issues / notes for the auditor

* T2's `hM : M.IsHermitian` hypothesis (listed in the ticket) is **not used** in the proof of
  `oneStep_integral_eq` — the identity holds for every matrix `M`, Hermitian or not. It is kept
  in the signature only because the ticket's target statement lists it; this is a harmless unused
  hypothesis, not a hidden weakening (dropping it would only make the statement more general).
  T3's `hM` **is** used (to show `M + Hflow d N w ω` Hermitian, feeding `hLip`).
* T3's Lipschitz hypothesis `hLip` is stated for **all** Hermitian `A, A'` (unconditionally, no
  neighbourhood restriction on `M`), exactly as the ticket specifies; the proof only ever
  instantiates it at `A = M + Hflow d N w ω`, `A' = M` for `w ∈ [0, Δ]`.
* Witness for `hLip`'s satisfiability used in the preflight: `Φ = const`, giving `genPt ≡ 0`, so
  `hLip` holds with `Λ = 0` (both sides of the inequality are `0` for every `A, A'`, not because
  the hypothesis's own quantifiers collapse — `d.Idx N` is a genuine nonempty finite index set for
  any `N` with `Dims.W_pos`/`Dims.three_le_L`, so "all Hermitian `A, A'`" ranges over an infinite
  set). A sharper, non-trivial `Λ` for loop functionals is T1487's job, not this ticket's; T1487's
  audit should confirm such a `Λ` is realizable before the two tickets are assembled together.
* No `docs/paper-deltas.md` entries needed: this ticket does not change any theorem statement
  relative to the paper or to `pilot-P4P5-paper.md` — it is pure discrete-time real analysis
  (FTC + a Lipschitz remainder bound), matching §3 of the pilot note exactly, and the paper
  reference itself already flags its own deltas (the `N^δ` threshold gap, the Lemma 5.7 exponent
  choice) as pertaining to later tickets (T1487, the A5 assembly), not to this one.
* Root import: none added, per the ticket ("added by a later merge instruction").
