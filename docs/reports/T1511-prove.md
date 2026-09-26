Prover model: claude-sonnet-5

# T1511 — net lift of (2.76) uniformly in `u ∈ [s_N, t_N]`, Gaussian model

## Math preflight (before any Lean)

Targets, per the ticket:

**(T1) `RBM.Gauss.Grid.etaT_inv_le_of_hreg`.** Statement vs paper: this is a pure consequence of
step2's own regularity gain `hreg` (`N^c(η_s/η_t)^{30} ≤ scale(t)`) plus the band's dimension
relation `W·L ≤ N` (`Band.dim`, eventual). Hypotheses: `0 < c`, `hs0`, `hst`, `ht1`, `hreg`, and —
not listed explicitly in the ticket's one-line hypothesis summary but mathematically
indispensable and always available at every call site (`step2`'s own `hE : |E| < 2`, needed for
`mE_im_pos`/positivity of `etaT`) — `hE : |E| < 2`. This is a delta from the ticket's literal
hypothesis list, not from the paper; recorded below. Quantifier order: `∀ N` inside `∀ᶠ`, all
fixed parameters (`E, s, t, c`) universally quantified before the `∀ᶠ N`, matching the paper's
convention. Dependencies: only `Band.dim`, `etaT_pos_of_lt_one'`, `etaT_le_of_le`, `Real.one_le_rpow`
— all already-accepted deterministic facts. Boundary cases: `N` large only (`∀ᶠ`), no `N = 0`
issue. Verdict: **PASS**.

**(T2) `RBM.Gauss.Grid.h276_of_pointwise`.** Statement vs the second conjunct of `Step2.step2`
(`Hierarchy/Step2.lean:2054–2066`): identical up to the packaging via `netLift_of_relaxed`, with
`B := band d`, `X := sample d`, `B.P := P d`. Hypotheses: `hE`, `hs0`, `hst`, `ht1`, `hc0`, `hreg`
(all from `step2`'s own hypothesis list, reused verbatim) plus `hpt`, the ticket's pointwise (in
every time sequence) `StochDom` bound — exactly the shape `Step2.step2`'s own conclusion has after
reindexing along a sequence, so it is not a new, unmotivated hypothesis (satisfiability witness
below). Quantifier order: `∀ D, 0 < D → …` outside the `StochDom`'s own `∀ τ, ∀ D', ∀ᶠ N`, matching
`step2`. Dependencies: `Step1Hyp.netLift_of_relaxed`, `Step1Hyp.highProb_norm_Xmat_le`,
`Lemma514Holder.hKb_flow`/`norm_lkT_flow_sub_le`/`abs_scale_sub_le`, `abs_ellHat_sub_le`,
`abs_etaT_sub_le`, `one_le_ellHat`, `two_mul_zdist_le` — all Step 1 / fixed-time / deterministic,
none from `Gauss/APrime*` or `EarlyQVRateEv` (checked by import: this file imports only
`RBM1D.Gauss.Lemma514Holder`, and no identifier from an `APrime*` file is referenced in the new
code; the transitive import graph does reach `APrimeGeneralMovingCarrierCore` through
`Lemma41FlowGauss`, but nothing from it is *used*).

Step 0 checks:
- `netLift_of_relaxed` needs `hT : 0 < T` and `hlen : ∀ N, t N − s N ≤ T`. Since `hs0 N : 0 ≤ s N`
  and `ht1 N : t N < 1`, `t N − s N ≤ t N < 1`, so `T := 1` works unconditionally — **not** a
  blocking obstacle (this is exactly the case flagged as a possible blocker in the ticket; it
  resolves in the ticket's favor).
- `TimeIcc s t N` is nonempty because `hst N : s N ≤ t N` is supplied to every call.
- Hypotheses simultaneous satisfiability: `hpt` is *implied* by `Step2.step2`'s own second
  conjunct for any `d, E, s, t` where `step2`'s hypotheses hold (a nondegenerate witness — not a
  vacuous one, since `Step2.step2`'s hypotheses are exactly `Dims`'s own regime, already used
  throughout the accepted code). Concretely: `step2`'s second conjunct is
  `∀ D, 0 < D → StochDom (P d) (fun N p ω => lkErr E N p.1 ω (pmLoop p.2.1 p.2.2)) (fun N p _ =>
  bnd …)`; for a *fixed* sequence `u`, precomposing with `q ↦ (u N, q)` gives exactly `hpt`'s
  per-`u` statement, and this precomposition step is free (the bad event only shrinks under a
  fixed choice of the time coordinate — `StochDom.reindex_fst`, `≤ 3` lines, `measure_mono` on the
  witness map `q ↦ (u N, q)`). I checked this compiles as a standalone example (not part of the
  committed file, since it needs `RBM1D.Hierarchy.Step2` which the sole writable file must not
  import) in a throw-away scratch file, then deleted it; see "Witness" below for the exact
  statement checked.
- `A`, `B₀` are fixed once `D` is fixed (`A := 4*D + 40`, `B₀ := D + 2`), no `N`-dependence in
  either — verified by construction (both are `have`s computed from `D` alone before any
  `filter_upwards`).
Verdict: **PASS**.

Exact ticket-vs-Lean deltas (`docs/paper-deltas.md`-worthy, tag `T1511a` for the dispatcher to
number): (1) T1 also takes `hE : |E| < 2`, needed for `mE_im_pos`/`etaT` positivity and monotonicity,
not listed in the ticket's abbreviated hypothesis summary but present at every actual call site.
(2) The route uses `A := 4*D + 40` (D-dependent, uniformly dominating every exponent constraint
found while writing the estimate) rather than the ticket's illustrative `4(B₀+C+4)`; both are
"fixed per `D`", the acceptance criterion the auditor checks.

## Lean

File: `RBM1D/Gauss/GridNetLift.lean` (new). Namespace `RBM.Gauss.Grid`.

Declarations added:
- `eventually_mul_rpow_le_mul_rpow`, `sqrt_abs_sub_le_rpow`, `abs_exp_neg_sub_exp_neg_le`,
  `sqrt_rpow_eq`, `inv_le_const_mul_inv_of_le_const_mul`, `idx_mySig`, `lkErr_eq_norm_lkT` —
  generic helpers (rpow-exponent arithmetic, the 1-Lipschitz bound `|e^{-x}-e^{-y}| ≤ |x-y|` for
  `x,y ≥ 0`, and the bridge `Sample.lkErr` ↔ `SumZeroDyn.lkT` at the charge vector `(+,-)`).
- `etaT_inv_le_of_hreg` — **(T1)**.
- `h276_of_pointwise` — **(T2)**.

Build: `cd /Users/junyin/Lean_proof/RBM1D-wt/T1511 && lake build RBM1D.Gauss.GridNetLift` →
`Build completed successfully (3781 jobs)`, 0 errors. Remaining warnings are only the pre-existing
codebase style ones (`show` used for a definitional unfold instead of `change`, and a small number
of >100-character lines), matching the style already present throughout `Lemma514Holder.lean`
etc.

Axioms (checked via a temporary `#print axioms` appended then removed before commit):
```
'RBM.Gauss.Grid.etaT_inv_le_of_hreg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.h276_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Syntactic match with `step2` (checked via a temporary scratch file `GridNetLiftCheck.lean`,
compiled then deleted — it is not part of the commit since the ticket's sole writable file is
`GridNetLift.lean`):
```lean
example (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : …) (hpt : …) :
    ∀ D : ℝ, 0 < D → StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  h276_of_pointwise d hE hs0 hst ht1 hc0 hreg hpt
```
type-checks against `(Step2.step2 …).2`'s literal type.

Witness (`hpt` is implied by `step2`, checked in the same scratch file, then deleted):
```lean
theorem StochDom.reindex_fst {U V : ℕ → Type*} {Ωx} [MeasurableSpace Ωx] {Px : Measure Ωx}
    {f g : ∀ N, U N × V N → Ωx → ℝ} (u : ∀ N, U N) (h : StochDom Px f g) :
    StochDom Px (fun N q ω => f N (u N, q) ω) (fun N q ω => g N (u N, q) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω; obtain ⟨q, hq⟩ := hω; exact ⟨(u N, q), hq⟩

example (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (Hy : Hyp (sample d) E s t) (h1 : Step1.Hyp (sample d) E s t) (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : …) :
    ∀ D : ℝ, 0 < D → ∀ u : ∀ N, RBM.TimeIcc s t N, StochDom (P d) (fun N p ω => …) (fun N p _ => …) :=
  fun D hD u => StochDom.reindex_fst u ((step2 (sample d) hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg).2 D hD)
```
Both examples compiled with 0 errors.

## Key lemmas used (route actually taken)

**(T1).** `η_s ≥ η_t > 0` (`etaT_le_of_le`, `etaT_pos_of_lt_one'`), so `(η_s/η_t)^{30} ≥ 1`
(`one_le_pow₀`); `scale(t) ≤ W·L·η_t ≤ N·η_t` (`min_le_right` for `ell ≤ L`, `Band.dim` for
`W·L ≤ N`); combine with `hreg` and `1 ≤ N^c` (`Real.one_le_rpow`) to get `1 ≤ N·η_t`, i.e.
`η_t^{-1} ≤ N`.

**(T2).** For each fixed `D`, set `A := 4D + 40`, `B₀ := D + 2`. Apply
`Step1Hyp.netLift_of_relaxed` with `T := 1`, `Ξ_N := {‖X_N‖ ≤ N}` (`highProb_norm_Xmat_le`),
`ξ = ξ'`, `ζ = ζ'` both the family from `hpt`/the goal (supplying `hpt D hD0` both as `hrel` and as
the "unused" argument the returned `NetLift` term consumes — `ξ = ξ'`, `ζ = ζ'` are stated as
*explicit* named arguments in the final `exact`, because otherwise the higher-order-unification
pattern `ξ' N (u N, v) ω` under the nested `∀ u, ∀ N` binders is not a Miller pattern and Lean
cannot solve for `ξ'`/`ζ'` from `hrel`'s type alone).

- `hlow`: `(η_s/η_u)^4 ≥ 1` (monotonicity), `scale(u)⁻¹^2 ≥ N^{-2}` (`scale(u) ≤ N`, same route as
  T1), `decayProf ≥ W^{-D} ≥ N^{-D}` (`Real.rpow_le_rpow` + `inv_anti₀`); product `≥ N^{-(D+2)}`.
- `hclose`, first half (the lkErr additive bound, target `N^{-(D+4)}`): bridge `lkErr` to
  `SumZeroDyn.lkT` at the charge vector `mySig := ![true,false]` (`idx_mySig`, `lkErr_eq_norm_lkT`,
  proved the same way as the committed `Step2.idx_sigPM`/`norm_lk_eq` but *not* reusing them, to
  avoid any dependency on `Gauss/APrimeSmoothPrefixCanonicalCore.lean`); `norm_sub_norm_le`; the
  modulus `norm_lkT_flow_sub_le` (`n = 2`) with `Bk := N^3` from `hKb_flow` (`c := 1`, `m := 2`,
  fed by T1); crude polynomial envelope `Const(N) ≤ 8·N^8` (`‖X‖+1 ≤ 2N` on `Ξ`, `W, L ≤ N`
  from `Band.dim`); `√|u-u'| ≤ N^{-A/2}`; `8·N^8·N^{-A/2} ≤ N^{-(D+4)}` once `A > 2D + 24`.
- `hclose`, second half (`bnd(u') ≤ 2·bnd(u)`), three factors each shown `≤ (11/10)×` the
  corresponding factor at `u` (so the total is `≤ (11/10)^7·bnd(u) ≤ 2·bnd(u)`,
  `(11/10)^7 ≈ 1.9487 < 2` checked by `norm_num`):
  - η: `abs_etaT_sub_le` (Lipschitz-1) + `η_u, η_{u'} ≥ N^{-1}` (T1 + monotonicity); needs
    `A > 1`.
  - scale: `abs_scale_sub_le` (Hölder-1/2, constant `≤ 2N^2` using `(1-t_N)^{-1} ≤ N` — itself
    from T1 via `etaT_le`) + `scale(u), scale(u') ≥ N^{-1}`; needs `A > 6`.
  - decayProf: the `W^{-D}` summand is literally the same on both sides; the `exp` summand's
    modulus is proved via `|√(z/ℓ_u) − √(z/ℓ_{u'})| ≤ (1/√2)·N^{1-A/4}` (from `ℓ ≥ 1`,
    `abs_ellHat_sub_le`, `abs_sqrt_sub_sqrt_le`, `zdist ≤ L/2 ≤ N/2`) and the new 1-Lipschitz fact
    `abs_exp_neg_sub_exp_neg_le` for `t ↦ e^{-t}` on `t ≥ 0` (proved from
    `Real.add_one_le_exp`/`Real.exp_le_one_iff`, no new dependency); needs `A > 4D + 4`.
  All four exponent thresholds are dominated by `A := 4D + 40`, verified via the single generic
  helper `eventually_mul_rpow_le_mul_rpow`.

## Open issues

- None blocking. The two ticket-vs-Lean deltas above (extra `hE` hypothesis on T1; the concrete
  value of `A`) should be recorded by the dispatcher under a temporary tag (e.g. `T1511a`) in
  `docs/paper-deltas.md`.
- The file sets `set_option maxHeartbeats 4000000` (needed once, for the large `hclose` proof
  term); this is local to `GridNetLift.lean` and does not affect other modules.
