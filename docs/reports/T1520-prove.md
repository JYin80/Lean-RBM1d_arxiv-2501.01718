Prover model: claude-opus-5-5

# T1520 — grid bootstrap (R4c-2a), repair round 1 (amended (T3)/(T4))

Repair of the RETURN in `docs/reports/T1520-audit.md` (branch `t/T1520` at `651f006`). The
ticket's amend note (top of `docs/tickets/T1520.md`, after T1519-amend-1) supersedes (T3) and
(T4). (T1), (T2) and the old (T3)/(T4) stay as they are (audit: PASS against the original spec;
the amend note keeps the old `GridPointwise`); the repair only **adds** declarations.

## Math preflight for the amended targets (written 2026-09-26 11:03 UTC, before any new Lean)

Materials: the ticket and its amend note; the audit report; `CLAUDE.md` §3;
`Gauss/Step2Gauss.lean` (`GridPointwise`, `lkErrMat`, `stochDom_grid_iff_flow`, `hpt_of_grid`,
`step2_gauss_of_pointwise`, `step2_gauss_of_grid`, the non-vacuity `example`);
`Gauss/GridStop.lean` (`firstHit`, `firstHit_le`, `lt_firstHit_imp`, `lt_min_firstHit_imp`);
`Gauss/GridPath.lean` (`map_H_eq`, `time_last`); `Defs/StochDom.lean` (`StochDom`, `badSet`,
`HighProb`); T1519-amend-1 and T1519's branch `GridGoodEvent.lean` lines 56–120 (read-only, to
see which stopping time (T6′) exposes).

Paper anchor: (2.76) (the `lk` bound, the second conjunct of Step 2's conclusion), obtained in
§5.3 by the stopping-time bootstrap (5.43)–(5.47) with `J*` of (5.29) and the threshold
`thr = N^δ (η_s/η_u)⁴`.

### (T3′a) `GridPointwise' d E s t` (definition)

Statement (amend note, δ₀ binder per the audit's clarification):
`∀ D > 0, ∀ u : ∀ N, TimeIcc s t N, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ D₁ > 0, ∃ K : ℕ → ℕ,
(∀ N, K N ≠ 0) ∧ (∃ C ≥ 0, ∀ᶠ N, (K N + 1 : ℝ) ≤ N^C) ∧
∀ᶠ N, Pg {ω | ∃ p, N^δ · ζ_D(N,p) < lkErrMat d E N (u N) (H_{K N} ω) (pmLoop p)} ≤ ofReal (N^{-D₁})`,
with `ζ_D(N,p) := (η_s/η_{u N})⁴ · scale⁻¹² · decayProf N (u N) D p.1 p.2` — literally the
`ζ` of T1517's `GridPointwise`/`hpt`, and the bad set is literally `badSet` at exponent `δ` (the
same strict `<` as `StochDom`). Quantifier order: `D, u` fixed first; `δ₀` depends on `(D, u)`
only; `K` (and `C`) may depend on `(D, u, δ, D₁)` — exactly the relaxation the amend note allows
(K after D₁, as T1519 (T6′) needs). The label set `ZMod (d.L N)²` and the window are T1517's.
It is a definition, so no PASS/FAIL beyond faithfulness; its non-vacuity is checked below.
**PASS.**

### (T3′b) `hpt_of_gridPointwise'`

Target: `GridPointwise' d E s t` (with `hs0 : ∀ N, 0 ≤ s N`) ⇒ h276's `hpt`, i.e. exactly the
`hpt` binder of T1517's `step2_gauss_of_pointwise`:
`∀ D > 0, ∀ u, StochDom (P d) (fun N p ω => (sample d).lkErr E N (u N) ω (pmLoop p.1 p.2)) ζ_D`.
Proof check. Fix `D, u`; get `δ₀`. For StochDom's `τ > 0, D₁ > 0` set `δ := min τ δ₀ ∈ (0, δ₀]`
and get `K, hK0, C, hbad` from `GridPointwise'` at `(δ, D₁)`. For each `N ≥ 1` in the eventual
set:
- `badSet_flow(τ, N) ⊆ badSet_flow(δ, N)` because `N^δ ≤ N^τ` (`N ≥ 1`, `δ ≤ τ`) and
  `ζ_D ≥ 0` (even power, inverse square, `decayProf ≥ 0`);
- `P(badSet_flow(δ, N)) = Pg(badSet_grid(δ, N))` — **for this single N**: both sets are
  preimages of the same measurable matrix set `S_N = ⋃_p {M | N^δ ζ < lkErrMat M}` under
  `Hflow d N (u N)` resp. `H d s u K N (K N)`, and
  `(Pg d).map (H … (K N)) = (P d).map (Hflow d N (time … (K N)))` (`map_H_eq`, needs
  `0 ≤ s N ≤ u N`, `K N ≠ 0`), with `time … (K N) = u N` (`time_last`). The flow event does not
  involve `K`, so the `(δ, D₁)`-dependence of `K` disappears here; this is why K(δ, D₁) is
  harmless.
- Hence `P(badSet_flow(τ, N)) ≤ ofReal(N^{-D₁})`.
Hypotheses: only `hs0` (for `map_H_eq`); `s N ≤ u N` comes from `TimeIcc`. No new hypothesis.
Boundary: `N = 0` never used (all eventual); `D > 0` arbitrary. Dependencies: `map_H_eq`,
`time_last`, `measurable_lkErrMat`, `H_measurable_filt`, `measurable_H` — all merged (T1507,
T1517 and earlier). The one-time law identity is used only for a one-time event at fixed `N`
(CLAUDE.md §3.5 is respected: no stopped-path identity is inferred). **PASS.**

### (T3′c) `step2_gauss_of_gridPointwise'`

`step2_gauss_of_pointwise d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg (hpt_of_gridPointwise' …)`,
with hypotheses and conclusion copied verbatim from T1517's `step2_gauss_of_grid` (whose
conclusion was checked there to be syntactically `Step2.step2`'s at `X := sample d`), `hgp`
replaced by `GridPointwise'`. **PASS.**

### Non-vacuity of `GridPointwise'` (gate §3.4)

`GridPointwise ⇒ GridPointwise'` (take `δ₀ := 1`, and for every `(δ, D₁)` the same `K, C`; the
event bound is StochDom's at `τ := δ`, `D := D₁`, since the bad set is literally `badSet … δ N`).
Together with T1517's compiled example (`step2`'s own second conjunct ⇒ `GridPointwise`, via
`precomp_param` and `stochDom_grid_iff_flow` at `K := 1`), `GridPointwise'` follows from Step 2's
conclusion (2.76) for `sample d`, with the full label set and step2's own window. Will be
compiled as the lemma `gridPointwise'_of_gridPointwise` plus an `example` from (2.76). No
astronomically large parameter: `K ≡ 1`, `C = 1`, `δ₀ = 1`. **PASS.**

### (T4′) `endpoint_of_bootstrap'` (bootstrap only at the random target)

Which stopping time: **no `gridTau` exists on `main`**; T1519's branch (unmerged, T1519 (T1),
kept by amend-1) defines
`gridTau … N ω := min (firstHit (fun j ω => jSMat d E D N u_j (H_j ω) − thr E s δ N u_j) 0 (K N) ω)
(firstHit (fun j ω => (goodSet …(u_j)…)ᶜ.indicator 1 (H_j ω)) (1/2) (K N) ω)`.
I cannot import that file (sole-writable-file rule, not merged), so (T4′) is stated for **the
min of two `firstHit`s** with first process literally `jSMat(u_j, H_j) − thr(u_j)` at level `0`
and a **generic second process** `J' : ℕ → Ωg d → ℝ` at level `θ'`; with
`J' := goodSet-indicator`, `θ' := 1/2` and grid endpoint `fun N => (u N : ℝ)`, the stopping time
in (T4′) is definitionally T1519's `gridTau`.
Statement: `hK0 : ∀ N, K N ≠ 0`, `u`, `G : ℕ → Set (Ωg d)`, `hG : HighProb (Pg d) G`, and for
every `N` and `ω ∈ G N`:
- `hgood : ∀ j ≤ K N, J' j ω < θ'` (G makes the good set hold at every `j`);
- `hat : jSMat(u_τ, H_τ ω) < thr(u_τ)` at `τ := τ(ω)` (the bootstrap step at the random target
  only).
Conclusion: `HighProb (Pg d) {ω | τ ω = K N ∧ jSMat(u N, H_{K N} ω) < thr(u N)}` (`u_{K N} = u N`
by `time_last`). A deterministic per-ω core `min_firstHit_eq_of_at` is also stated.
Proof check (per ω ∈ G N): let `a := firstHit (J − thr) 0 K ω`, `b := firstHit J' θ' K ω`.
`b = K` by `firstHit_eq_of_below` and `hgood`. So `τ = min a K = a` (`a ≤ K`, `firstHit_le`). If
`a < K`, `hittingBtwn_mem_set_of_hittingBtwn_lt` gives `0 ≤ J_a − thr_a`, i.e. `J_a ≥ thr_a`,
contradicting `hat` (τ = a). So `a = K`, `τ = K`, and `hat` at `τ = K` plus `time_last` gives the
endpoint bound. No induction over k; no union over k.
Satisfiability: the hypotheses are strictly weaker than the old (T4)'s (the all-k bootstrap on G
plus `hgood` gives `J_j < thr_j` for all `j ≤ K`, in particular at `τ`); a compiled `example`
will show "old hypotheses + `hgood` ⇒ new `hat`". `G` is a generic `HighProb` family (supplied by
T1518 (T3) + T1519 (T6′) in R4c-2b); `K N ≠ 0` keeps the grid nondegenerate. Boundary `K N = 0`
excluded by `hK0`; `τ = 0` is allowed and handled (then `a = 0 < K` is refuted by `hat`).
**PASS.**

### Old targets

(T1), (T2), old (T3) `gridPointwise_of_endpoint`, old (T4) `endpoint_of_bootstrap`: unchanged,
audit PASS (against the original spec), kept as extra lemmas per the repair instruction.

### Paper deltas

None. K(δ, D₁) in `GridPointwise'` is a grid-only artifact; it does not reach the flow
statement `hpt`/(2.76), which has no K. (T4′) uses the stopping time of (5.43)-type exactly as
the paper's bootstrap does (the step bound only at the stopping time).

## Overall preflight verdict: PASS for (T3′a), (T3′b), (T3′c), (T4′).

## Declarations (file `RBM1D/Gauss/GridBootstrap.lean`, namespace `RBM.Gauss.Grid`)

New in this repair (commit `0fc3fd3` on `t/T1520`, on top of `651f006`):
- `GridPointwise'` (def): amended (T3′). The binder is `∃ δ₀ > 0` right after `∀ u`, before `∀ δ ∈ (0, δ₀]`. It is followed by `∀ D₁ > 0, ∃ K`, then `K N ≠ 0`, `∃ C ≥ 0, ∀ᶠ N, K N + 1 ≤ N^C`, and `∀ᶠ N, Pg(bad_{δ,D}) ≤ ofReal(N^{-D₁})`.
- `pg_bad_eq_flow`: the per-N equality of the grid and flow bad-set probabilities (`map_H_eq` at `k = K N` together with `time_last`).
- `hpt_of_gridPointwise'`: its conclusion is literally the `hpt` binder of T1517's `step2_gauss_of_pointwise`. It uses `δ := min τ δ₀` and `N^δ ≤ N^τ`.
- `step2_gauss_of_gridPointwise'`: defined as `step2_gauss_of_pointwise ∘ hpt_of_gridPointwise'`. Its hypotheses and conclusion are copied verbatim from T1517's `step2_gauss_of_grid`, so the conclusion is `Step2.step2`'s.
- `gridPointwise'_of_gridPointwise`: the non-vacuity lemma. A compiled `example` derives `GridPointwise'` from step2's own (2.76) for `sample d`, using `K ≡ 1`, `C = 1`, `δ₀ = 1`.
- `min_firstHit_eq_of_at`: the deterministic core of (T4′).
- `endpoint_of_bootstrap'`: amended (T4′). Its hypothesis is imposed only at the random target τ; its conclusion is `HighProb {τ = K N ∧ jSMat(u N, H_{K N}) < thr(u N)}`. A compiled `example` shows that the old (T4) hypotheses imply the new `hat`.

Kept unchanged (audit PASS against the original spec): `below_of_bootstrap`, `firstHit_eq_of_below`, `min_firstHit_eq_of_below` (T1), `lk_le_of_jS` (T2), `gridPointwise_of_endpoint` (old T3), and `endpoint_of_bootstrap` (old T4).

**(T4′) firstHit route used: the min of two `firstHit`s.**
- The first process is literally `j ↦ jSMat(u_j, H_j) − thr(u_j)` at level 0.
- The second process is a generic `J' N` at level `θ'`.
- `main` has no `gridTau`. T1519's `gridTau` (on branch `t/T1519`, not merged) has exactly this shape.
- A scratch check (not committed) compiles `rfl` between a verbatim copy of T1519's `gridTau` at endpoint `fun N => (u N : ℝ)` and (T4′)'s τ with `J' N j := 1_{goodSet(u_j)ᶜ}(H_j)` and `θ' := 1/2`. So R4c-2b can instantiate (T4′) with `gridTau` directly.

## Build

`cd /Users/junyin/Lean_proof/RBM1D-wt/T1520 && lake build RBM1D.Gauss.GridBootstrap` finished with **Build completed successfully (3895 jobs)**. The only local warnings are the two already recorded by the audit: the unused `hM` and the deprecated `Set.mem_setOf_eq`, both in old code.

## Axioms

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 13 public declarations: the six old ones and `GridPointwise'`, `pg_bad_eq_flow`, `hpt_of_gridPointwise'`, `step2_gauss_of_gridPointwise'`, `gridPointwise'_of_gridPointwise`, `min_firstHit_eq_of_at`, `endpoint_of_bootstrap'`. The file contains no `sorry`/`admit`/`axiom`/`opaque`/`unsafe`.

## Key lemmas used (new part)

- `Grid.map_H_eq` and `Grid.time_last`.
- `Grid.H_measurable_filt`, `RBM.measurable_H`, `measurable_lkErrMat` and `Measure.map_apply`.
- `Real.rpow_le_rpow_of_exponent_le`.
- T1517's `step2_gauss_of_pointwise` and `stochDom_grid_iff_flow`, the latter used only in the non-vacuity example.
- `firstHit_eq_of_below`, `firstHit_le`, `MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt` and `HighProb.mono`.

## Open issues

- (T4′) takes a generic second process `J'`, so it can be instantiated with `gridTau`. It does not import T1519's `GridGoodEvent.lean`, which is unmerged and outside the sole writable file. The `gridTau` instantiation belongs to R4c-2b.
- `HighProb G` and the `hat`/`hgood` hypotheses of (T4′) are to be supplied by T1518 (T3) and T1519 (T6′) in R4c-2b. `GridPointwise'`'s K(δ, D₁) matches T1519 (T6′), where K is chosen after D₁.
- There are no paper deltas: K(δ, D₁) is a grid-only artifact and does not appear in `hpt`/(2.76).
