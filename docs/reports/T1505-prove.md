Prover model: claude-sonnet-5

# T1505 — the pathwise Z/Y decomposition of one grid step

Ticket: `docs/tickets/T1505.md`. Sole writable file: `RBM1D/Gauss/GridStepDecomp.lean`
(worktree `../RBM1D-wt/T1505`). Required reading only: CLAUDE.md §3;
`docs/supervisor/2026-09-25-2045.md` §2; `RBM1D/Gauss/GridMarkov.lean`; `RBM1D/Gauss/LoopC2.lean`
(statements); `RBM1D/Gauss/MomentGronwall.lean` (`wirtFirst`, `coordD1`, `quadVar`); plus, as
step-0 read-only checks of already-live definitions used by those files, `RBM1D/Gauss/Generator.lean`
(the actual `def`s of `coordD1`, `usedCoord`, `Bmat`, `TestFun`, `hasFDerivAt_fderiv_apply`) and
`RBM1D/Gauss/LoopC2.lean` (`norm_fderiv2_apply_le`).

Note on continuation: on starting this ticket, the worktree already contained a substantial
untracked draft of `GridStepDecomp.lean` (T1 `lin_eq_fderiv` and T2 `stepDecomp`, ~880 lines,
uncommitted, no prior report) from an earlier, evidently interrupted, run of this same ticket.
I re-derived the math preflight below from scratch against the ticket text and the required
reading, checked the existing T1/T2 Lean against it, and then completed T3/T4 on top of it.

## Math preflight (before any new Lean)

### (T1) `lin_eq_fderiv`

Statement required: for `TestFun`-class `Φ` and Hermitian `M`, `(fderiv ℝ Φ M X).re = lin N
(gradMat Φ M) X` for Hermitian `X` (and `.im`), with `gradMat` built from `wirtFirst`/`coordD1`.

- Hypotheses vs. paper: this is the real part of the standard complex Wirtinger identity
  `dΦ_M(X) = Σ_{ij} ∂_{M_ij}Φ · X_ij` restricted to the Hermitian directions read off by
  `Bmat`/`usedCoord`; `gradMat Φ M := (wirtFirst d N Φ M)ᵀ` is exactly the matrix making
  `Matrix.trace (gradMat Φ M * X) = fderiv ℝ Φ M X` (pilot P4/P5 §4). No paper formula number is
  attached to this specific lemma (it is internal calculus machinery feeding (T2)); it is a
  faithful transcription of the definitions in `Gauss/MomentGronwall.lean`/`Gauss/Generator.lean`.
- Quantifier order: `∀ Φ M X` (all universally quantified, `TestFun`/Hermitian hypotheses first) —
  matches the ticket, no `∀ᶠ N` involved (this is a pointwise algebraic identity, no asymptotics).
- Dependencies: only `wirtFirst`, `coordD1`, `usedCoord`, `Bmat`, `TestFun` (`Generator.lean`,
  `MomentGronwall.lean`), already-accepted definitions, not fresh axioms.
- Boundary cases: `d.Idx N` possibly a small/degenerate index type — the proof (`herm_eq_sum_Bmat`
  + `coordD1_eq_trace_gradMat_Bmat`) is by induction on `usedCoord d N` as a `Finset`, correct
  (vacuously, for the empty case) even if `d.Idx N` is empty or a singleton.
- Simultaneous satisfiability: `TestFun d N Φ` together with `M.IsHermitian`, `X.IsHermitian` is
  satisfied non-vacuously by e.g. `Φ ≡ 0` (trivially) or, non-degenerately, by any of the already
  accepted `BddC2C`/`TestFun` witnesses built from bounded resolvent factors elsewhere in the
  repository (`Gauss/LoopC2.lean`, `Gauss/Generator.lean`); the Hermitian condition on `M`, `X` is
  satisfied by e.g. `M = X = 0`, non-degenerately by any nonzero Hermitian matrix.
- **Verdict: PASS.**

### (T2) `stepDecomp`

Statement required: pathwise decomposition `ξ b ω = Z b ω + Y b ω` of one grid step, with
`Ab`/`Z` exactly of the `√Δ · lin N A X` form `filt d j`-measurable, `Y`'s pathwise bound
`O(Δ‖X‖²) + its conditional mean`, and `E[Y b | F_j] = 0` a.e.

- Modelling choice recorded (already flagged in the file's docstring, and repeated here for the
  dispatcher/auditor): the ticket's formula `Z b ω = √Δ·lin N (Ab ω) (Xmat...)` is stated as an
  identity, but the *raw* complex first-order Taylor term `Σ_a U(b,a)·fderiv(Φ a)(H_j ω)(X)` only
  has this exact real form if (i) each `Φ a` is real-valued on the Hermitian submanifold and (ii)
  `U` has real entries; otherwise an uncancelled imaginary linear part survives and only a weaker
  `O(√Δ‖X‖)` bound would be provable for `Y`, not the ticket's stated `O(Δ‖X‖²)`. Both (i) and
  (ii) match the documented downstream instantiation (`Φ a` a real `(L−K)_{u,(+,−),a}`-type
  combination, `U := Uker`, a real backward kernel) and are jointly, non-vacuously satisfiable
  (e.g. `Φ a M := (Matrix.trace (M * M)).re` is real-valued everywhere, `TestFun`-compatible in
  form, and `U := 0` or `U := 1` are real; the actually-intended witnesses are the already-accepted
  bounded real test functions from `LoopC2.lean`/`Generator.lean`). This is a genuine but harmless
  strengthening of the ticket's implicit hypotheses (CLAUDE.md §3.4/§3.7): tagged for the
  dispatcher as a temporary `T1505a` `docs/paper-deltas.md` entry (I cannot edit that file myself;
  ticket's sole writable file is `GridStepDecomp.lean`).
- Hypotheses vs. paper: `hΦ` (`TestFun`), `hReal` (real on Hermitian submanifold, the delta above),
  `hC₂` (uniform bound on `D²Φ_a`, matches `BddC2C`'s `C₂`/T133), `hΔ : 0 ≤ step s t K N` (a grid
  step size is a length, non-negative — a true, harmless side-condition already used pervasively
  elsewhere, e.g. `GridOneStep.lean`), `hIntReal` (integrability of the real linear part, needed to
  legitimately split off a conditional expectation of `Z`, discharged downstream once `Z` is shown
  bounded, as `Z` is a bounded linear functional of a Gaussian increment).
- Quantifier order: `∀ d s t K N j Φ hΦ hReal C₂ hC₂ hΔ U b hIntReal` — all fixed parameters before
  any asymptotic statement; there is no `∀ᶠ N` in this ticket (single grid step, deterministic `N`
  throughout), matching the ticket's scope.
- Dependencies: `condExp_linear_eq_zero`, `condExp_freeze` (T1482, `GridMarkov.lean`, merged);
  `norm_fderiv2_apply_le` (`LoopC2.lean`, live, T133-descended); `TestFun`/`coordD1`/`wirtFirst`
  (`Generator.lean`/`MomentGronwall.lean`, live). No archived or unaccepted material used.
- Boundary cases: `j = 0` (the earliest step) is a valid instance, no special-casing needed;
  `step s t K N = 0` is explicitly allowed (`hΔ` only requires `≥ 0`, not `> 0`), and is not
  vacuous — the identity, measurability and (degenerate, zero) `Y`-bound all still hold, checked
  by inspection of the proof (no division by `Δ` anywhere in `stepDecomp`'s own statement).
- Simultaneous satisfiability: witnessed non-degenerately as above (real `TestFun`-class `Φ`, real
  `U`, any Hermitian-preserving grid state `H_j ω`, `Δ ≥ 0` including `Δ > 0`); no astronomically
  large parameter is required.
- **Verdict: PASS**, modelling choice (`hReal`, real `U`) flagged as delta `T1505a`.

### (T3) `stepDecomp_Y_sq`

Statement required: `∫‖Y b‖² ≤ C₂²·Δ²·∫‖Xmat‖⁴·4` (or the explicit constant that comes out),
with integrability/`MemLp 4` facts for `Xmat`.

- Route: from (T2)'s a.e. pathwise bound `‖Y b ω‖ ≤ g ω + E[g|F_j] ω` with `g ω := (Σ_a|U(b,a)|)·
  ((C₂/2)·Δ)·‖X(ω(j+1))‖²`, square (`(x+y)² ≤ 2x²+2y²`, valid for all reals, no sign hypothesis
  needed once `‖Y‖≤(g+E[g|F_j])` forces `g+E[g|F_j] ≥ 0`), then bound `E[g|F_j]²` by the
  conditional Jensen inequality at the convex map `x ↦ x²` (Mathlib's `ConvexOn.map_condExp_le_univ`,
  `MeasureTheory.Function.ConditionalExpectation.CondJensen`, an already-accepted general-purpose
  Mathlib result, not project-internal, not archived) by `E[g²|F_j]`, then integrate using the
  tower property `integral_condExp` to identify `∫E[g²|F_j]` with `∫g²`. `∫g²` is computed in
  closed form from `‖X(ω(j+1))‖⁴`'s integrability, which is the fourth moment of a single sample
  of `Xmat`, pulled back along the (independent) increment map — the direct fourth-power analogue
  of the already-accepted `integrable_norm_Xmat_pow`/`integrable_normSq_incr` machinery in
  `Gauss/OpNorm.lean`/this file (no new probabilistic input, pure real-analysis bookkeeping).
- Hypotheses: identical to (T2)'s (`hΦ, hReal, hC₂, hΔ, hIntReal`), nothing added — the statement
  is a corollary of (T2) plus elementary integral calculus.
- Quantifier order: unchanged from (T2); a single explicit constant, no new asymptotic content.
- Dependencies: `stepY_norm_le_ae` ((T2)'s own internal a.e. bound), `integrable_norm_Xmat_pow`
  (`OpNorm.lean`, already accepted, feeds T1505's own new `integrable_normPow4_incr`),
  `ConvexOn.map_condExp_le_univ`/`integral_condExp`/`integrable_condExp` (Mathlib, unconditionally
  accepted background library, not a project claim).
- Boundary cases: `Δ = 0` collapses the bound to `0 ≤ 0` (still true, not vacuous: the inequality
  direction is preserved, `4·(...)²·0²·∫‖X‖⁴ = 0` and `∫‖Y‖² = 0` a.e. since `Y = 0` a.e. when
  `Δ = 0`, consistent).
- **Verdict: PASS.**

### (T4) `stepDecomp_Z_subG`

Statement required: `Z b` satisfies the hypotheses of `hasCondSubgaussianMGF_linear` (T1482) with
`c := Δ·v N (Ab ω)` pointwise, and so on any `F_j`-event `E` where `Δ·v N (Ab ω) ≤ c` deterministically.

- This is definitionally almost a restatement: `hasCondSubgaussianMGF_linear` (`GridMarkov.lean:564`,
  merged, T1482) already consumes exactly a `filt d k`-measurable direction `A`, an `E`, a
  deterministic `c ≥ 0` with `∀ ω ∈ E, Δ·v N (A ω) ≤ c`, and concludes
  `HasCondSubgaussianMGF` for `fun ω => E.indicator (fun ω => √Δ·lin N (A ω) (Xmat...)) ω`. Since
  `stepZ` is *by definition* `√Δ·lin N (Ab ω) (Xmat...)`, and `Ab` is `filt d j`-measurable
  (`measurable_Ab`, proved for (T2)), (T4) is exactly `hasCondSubgaussianMGF_linear` instantiated
  at `A := Ab`, unfolded through `stepZ`'s definition. No new mathematical content, no new
  hypotheses beyond (T2)'s `Ab`-measurability and the deterministic bound the ticket itself states
  as an input (`hbound`).
- Quantifier order / dependencies / boundary cases: inherited verbatim from
  `hasCondSubgaussianMGF_linear` (T1482, already merged and audited); `c = 0` is an allowed,
  non-vacuous boundary case there (forces `A ≡ 0` on `E`, still a valid sub-Gaussian statement
  with variance proxy 0).
- Simultaneous satisfiability: `E := Set.univ`, `hE := MeasurableSet.univ`, any `filt d j`-
  measurable `Ab`, `c := step s t K N · sSup (v N ∘ Ab)`-type bound (or simply `c` large enough,
  non-degenerate since `v N ∘ Ab` is a fixed real-valued function of a `filt d j`-measurable
  argument, not identically forced to some absurd value).
- **Verdict: PASS.**

## Step 0 (read-only checks, per the ticket)

- `wirtFirst`/`coordD1` (`Gauss/MomentGronwall.lean:333`, `Gauss/Generator.lean:592`): Wirtinger
  derivative pair, `coordD1 Φ M p := fderiv ℝ Φ M (Bmat p)`, `wirtFirst` the half-sum/difference
  combination at `(i,j,true/false)`; `gradMat` here is exactly their matrix transpose. Confirmed
  by direct reading, matches the file's `coordD1_eq_trace_gradMat_Bmat`.
- `BddC2C`/`bddC2C_loopObs` (`Gauss/LoopC2.lean`): read only as the *source* of the `C₀,C₁,C₂`
  constants a downstream ticket will plug into `hC₁`/`hC₂` here; this file does not re-derive them
  (per the ticket, "not needed" beyond `norm_fderiv2_apply_le`, which is used).
- `hasCondSubgaussianMGF_linear`/`condExp_linear_eq_zero` (`Gauss/GridMarkov.lean`, T1482, merged):
  used exactly as stated (T4 above; T2's `condExp_stepZ_eq_zero` uses `condExp_linear_eq_zero`).
- `Kval` (deterministic drift correction): does not appear anywhere in `Z`/`Y`/`ξ` as defined —
  confirmed: `stepXi`/`stepZ`/`stepY`/`Ab` never reference `Kval`; it cancels identically between
  `(L−K)_{u_{j+1}}(H_{j+1})` and its own conditional mean at the level *upstream* of this ticket
  (the ticket's `Φ` is understood as already the `(L−K)` combination), consistent with the
  ticket's own Step-0 note.

## Result

All four targets: **PASS**. Proceeding to Lean (T1, T2 already present from the earlier
interrupted run, re-checked above; T3, T4 added).

## Lean: declarations added/completed

All in `RBM1D/Gauss/GridStepDecomp.lean` (worktree `../RBM1D-wt/T1505`), namespace
`RBM.Gauss.Grid`.

- `gradMat`, `hermCoord`, `herm_eq_sum_Bmat`, `fderiv_eq_trace_gradMat` (private/internal helpers)
  and **`lin_eq_fderiv`** (**T1**) and `lin_eq_fderiv_im` — already present from the earlier
  interrupted run, re-verified against the preflight above, left unchanged apart from the fixes
  below.
- `Ab`, `stepZ`, `stepXi`, `stepY` (definitions), `measurable_Ab`, `sum_fderiv_eq_stepZ`,
  `H_succ_eq`, `Rlabel`, `norm_Rlabel_le`, `norm_Rlabel_sum_le`, `integrable_Rlabel_sum`,
  `condExp_stepZ_eq_zero`, `g_eq_pointwise`, `measurable_h0`, `integrable_h0`,
  `integrable_stepZ_complex`, `stepXi_eq_ae`, `stepY_eq_ae`, `stepY_norm_le_ae`, and
  **`stepDecomp`** (**T2**) — already present from the earlier run; fixed three genuine bugs that
  had never been build-checked (see below).
- **New this session**: `integrable_normPow4_incr` (fourth-moment analogue of
  `integrable_normSq_incr`), **`stepDecomp_Y_sq`** (**T3**), **`stepDecomp_Z_subG`** (**T4**).

### Bugs found and fixed in the pre-existing (uncommitted, never-built) T1/T2 code

1. `norm_condExp_le` (used twice in `stepY_norm_le_ae`) resolved, via the file's `open ... RBM`,
   to the unrelated `RBM.Green.EntryBound.norm_condExp_le` (a different lemma about a spectral
   parameter `‖ξ‖ ≤ 1`) instead of the intended (root-namespace) Mathlib
   `norm_condExp_le : (‖μ[f|m]·‖) ≤ᵐ[μ] μ[(‖f·‖)|m]`. Fixed by qualifying with `_root_.`; one
   call-site was also used as if it were a pointwise application of an a.e. statement to a point
   (`norm_condExp_le R ω`, which does not typecheck — `≤ᵐ[μ]` is `Filter.Eventually`, not a
   function), fixed by folding it into the surrounding `filter_upwards`.
2. `have hcondRnorm : (fun ω => ‖R ω‖) ≤ᵐ[Pg d] (Pg d)[fun ω => ‖R ω‖ | filt d j] := norm_condExp_le R`
   in `stepY_norm_le_ae`: this ascribed statement (`‖R‖ ≤ᵐ E[‖R‖|F]`, a pointwise bound by an
   average) is false in general and is not what `norm_condExp_le` proves; it was also *dead code*
   (never used in the rest of the proof, which only needs `‖E[R|F]‖ ≤ᵐ E[‖R‖|F]`, the correct
   statement `norm_condExp_le` gives). Deleted.
3. `condExp_sub hRint integrable_condExp (filt d j)` and
   `condExp_of_stronglyMeasurable ((filt d).le j) stronglyMeasurable_condExp integrable_condExp`
   inside `stepDecomp`'s fourth conjunct (`E[Y|F_j] = 0`): `integrable_condExp`'s implicit
   arguments (`f`, `m`) could not be synthesized in that position (no expected type flows
   backwards into a bare `have ... := term` with no ascription), a `rw` then failed because the
   goal's condExp argument was a lambda `fun ω => Σ_a ... - E[R|F_j] ω`, not the closed term
   `R - E[R|F_j]` used by the lemma. Fixed by supplying `integrable_condExp (f := R) (m := filt d j)`
   explicitly, replacing the strongly-measurable route by the cleaner tower-property idempotency
   `condExp_condExp_of_le (le_refl (filt d j)) ((filt d).le j)` for `E[E[R|F_j]|F_j] = E[R|F_j]`,
   and inserting an explicit pointwise identity (`hfe`, by `Pi.sub_apply`) between the goal's
   lambda form and the closed-subtraction form the lemmas produce.
4. Two `whnf`/`isDefEq` **kernel timeouts** (declaration-level, `stepY_norm_le_ae` and
   `stepDecomp_Y_sq`, even at `maxHeartbeats 4000000`, 20× default): traced to the `show
   <explicit-form>` idiom used to peel back a `set`-introduced local `g`/`R` — `show` forces a
   defeq check that (for these particular `Finset.sum`/matrix-operator-norm-laden bodies) is
   catastrophically expensive once repeated by `ring`/`nlinarith`'s own atom-matching. Replaced
   `show <explicit form>; ...` by `rw [hgdef]; ...` (propositional rewriting via the `set ... with
   hgdef` equation, no defeq unfolding) throughout; kept an explicit constant argument to
   `Integrable.const_mul` instead of `_` for the same reason. This alone fixed the timeouts (build
   time: 4–5s); the `maxHeartbeats 4000000 in` overrides were kept as a documented safety margin
   (`set_option linter.style.maxHeartbeats` requires and got an inline reason comment) since these
   four declarations remain the heaviest in the file.

None of these fixes touched the *statements* of (T1)/(T2); they are proof-term-level repairs of
a draft that had never actually been built.

## Build

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1505 && lake build RBM1D.Gauss.GridStepDecomp
```
Result: **success**, 3731/3731 jobs, no errors (only pre-existing style-linter warnings inherited
from `show`-vs-`change` and unused-`simp`-argument lints already present before this ticket, plus
the two new `set_option linter.style.maxHeartbeats` notices for the documented overrides).

## Axioms

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1505
# scratch file, deleted immediately after
cat > RBM1D/Gauss/T1505Axcheck.lean <<'EOF'
import RBM1D.Gauss.GridStepDecomp
#print axioms RBM.Gauss.Grid.lin_eq_fderiv
#print axioms RBM.Gauss.Grid.stepDecomp
#print axioms RBM.Gauss.Grid.stepDecomp_Y_sq
#print axioms RBM.Gauss.Grid.stepDecomp_Z_subG
EOF
lake env lean RBM1D/Gauss/T1505Axcheck.lean
rm RBM1D/Gauss/T1505Axcheck.lean
```
Output (all four): `depends on axioms: [propext, Classical.choice, Quot.sound]` — no `sorry`,
`admit`, or new/declared axiom.

## Key lemmas relied on

- `wirtFirst`, `coordD1`, `usedCoord`, `Bmat`, `TestFun` (`Gauss/MomentGronwall.lean`,
  `Gauss/Generator.lean`).
- `norm_fderiv2_apply_le`, `hasFDerivAt_fderiv_apply` (`Gauss/LoopC2.lean`, `Gauss/Generator.lean`).
- `hasCondSubgaussianMGF_linear`, `condExp_linear_eq_zero`, `condExp_freeze`, `lin`, `v`, `map_incr`
  (`Gauss/GridMarkov.lean`, T1482, merged).
- `integrable_norm_Xmat_pow` (`Gauss/OpNorm.lean`), reused (at `p := 2`) for the new
  `integrable_normPow4_incr`.
- Mathlib: `ConvexOn.map_condExp_le_univ`/`Even.convexOn_pow`
  (`Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen`,
  `Mathlib.Analysis.Convex.Mul`, both newly imported by this file), `condExp_condExp_of_le`,
  `integral_condExp`, `integrable_condExp`, `integral_mono_of_nonneg`, `pow_le_pow_left₀`.

## Open issues (for the dispatcher)

1. **`docs/paper-deltas.md` entry needed (`T1505a`)**: (T2)'s `stepDecomp` (and hence (T3)/(T4))
   carries two hypotheses not spelled out verbatim in the ticket's prose — `hReal : ∀ a A,
   A.IsHermitian → (Φ a A).im = 0` (each `Φ a` real-valued on the Hermitian submanifold) and `U`
   typed `LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ` (a *real* backward kernel, not complex). These
   are necessary for `Z` to be *exactly* the stated real-linear form (not merely an upper bound of
   it); they match the ticket's own documented downstream instantiation (`Φ a` a real `(L−K)`-type
   combination, `U := Uker`). I cannot append to `docs/paper-deltas.md` myself (outside this
   ticket's sole writable file); the docstring at the top of `GridStepDecomp.lean` already records
   this in full for whoever adds the entry.
2. Per §2 of `docs/supervisor/2026-09-25-2045.md`, the drift-algebra half of the bridge (item (d),
   the discrete analogue of (5.19)/(5.20)) is explicitly **not** part of this ticket (it is
   T1506's job); `stepDecomp`'s `Y` is only the Taylor-remainder martingale difference, with no
   drift term, exactly as scoped.
3. Downstream note (not a defect here, just a heads-up for the ticket that instantiates these
   lemmas): per the supervisor note, (T1)'s sibling `stepDecomp_Z_subG`'s *sup-norm* deterministic
   bound `c` is adequate for (T2)/(T3)-style `O(Δ)`/`O(Δ²)` remainder control but — per the
   supervisor's finding on T1504 (T1) — is *not* by itself adequate for the label-weighted Azuma
   argument that closes (2.76)/(5.47); that requires the "fixed target `k`, label-weighted
   `c_j^{(k,a)}`" variant recorded there, not a new concern for T1505.
