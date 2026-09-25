Auditor model: claude-opus-5-5[1m]

# T1507 audit: J* on the grid (`jSMat`) and matrix-set forms of σ's inputs

Audited: branch `t/T1507` at `cb56d87`, checked out in a fresh detached worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1507-audit` (not the prover's worktree). `GridJStar` was not in
the cloned cache, so it was compiled from scratch. Audit date (UTC): 2026-09-25 22:00.
Diff vs `main`: exactly one added file, `RBM1D/Gauss/GridJStar.lean` (the sole writable file). No
existing file or frozen signature touched.

## Overall verdict: PASS

## 0. Preflight
`docs/reports/T1507-prove.md` §1 contains a math preflight for T1–T4, each marked PASS and written
before the Lean (§2–§3 come after). The first line is `Prover model: claude-sonnet-5`. Criterion met.

## 1. Per-target checks

### (T1) `jSMat`, `jS_eq_jSMat`: PASS
- `jSMat d E D N u M := Step2.jStar (d.L N) (fun a => ‖gloop (d.L N) (d.W N) M (zt E u) (LoopData.idx (sigPM,a)) - (band d).Kval E N u (LoopData.idx (sigPM,a))‖) (d.W N) ((band d).ell N u) (etaT E u) D`.
- `Step2.jS X E D N u ω := jStar (B.L N) (fun a => ‖lk X E N u ω a‖) (B.W N) (B.ell N u) (etaT E u) D`, where `lk = X.Lval … - B.Kval …` and `Sample.Lval` is `gloop` on `X.H N u ω`.
  `jSMat` is the same term with `X.H N u ω` replaced by `M`: same `jStar`, same `sigPM`, same
  `Kval`/`ell`/`etaT`/`D`, same `sup'` and tail weight. It is not a re-derived or different formula.
- `jS_eq_jSMat : Step2.jS (sample d) E D N u ω = jSMat d E D N u (Hflow d N u ω)` is proved by
  `rfl`, and it compiles. So `jSMat` is literally `jS` evaluated through the matrix (acceptance
  criterion met). There are no hypotheses, so no vacuity question arises.

### (T2) `measurable_jSMat`: PASS
- The statement `Measurable (jSMat d E D N u)` is global on `Matrix (d.Idx N) (d.Idx N) ℂ`, with no
  Hermitian or invertibility restriction. This is the exact form needed by
  `isStoppingTime_firstHit_grid` (`hF : ∀ j, Measurable (F j)` with
  `F j : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ`). The intended use is `F j := jSMat d E D N (time s t K N j)`.
- Chain: `measurable_green_matrix` comes from `Gauss.measurable_matrix_inv_apply`, which is
  measurable everywhere (via adjugate/`Ring.inverse`) and does not rely on continuity at singular
  matrices. That result feeds `Gsig`, then a `gloopProd` foldr induction, then `gloop` (trace as a
  finite sum), then `Finset.measurable_sup'`, then `+ 1`. The rewrite `heq` to the `sup'` form is
  checked by `rfl` after `Finset.sup'_apply`. The step is sound.

### (T3) `jS_grid_law`: PASS
- Statement: for every `k`, `(Pg d).map (jSMat … (time s t K N k) ∘ H d s t K N k) = (P d).map (Step2.jS (sample d) … (time s t K N k))`.
  The hypotheses are exactly those of `map_H_eq` (`0 ≤ s N`, `s N ≤ t N`, `K N ≠ 0`), and they are
  satisfiable (e.g. `s N = 0`, `t N = 1/2`, `K N = N+1`).
- Proof: `jS_eq_jSMat`, then two `Measure.map_map` steps (measurability of `H` comes from
  `H_measurable_filt` and `filt.le`, and that of `Hflow` from `measurable_H`), then
  `map_H_eq s t K N k`. **It uses only the one-time law identity `map_H_eq` at a single grid time.**
  It makes no claim about joint laws across times and no stopped-path identity (CLAUDE.md §3.5
  respected). Acceptance criterion met.

### (T4) matrix-set forms, (2.73) and (5.57): PASS (for the two items attempted; the rest is open as the ticket allows)
- `eq273Set d E N n u ℓs τ` equals `{M | ∀ v : LoopData (d.L N) n, ‖gloop … M (zt E u) v.idx‖ ≤ N^τ (ℓ_u/ℓs)^{n-1} A_u^{-(n-1)}}`.
  This is `Step1.apriori`'s (2.73) bound (`(B.ell N u / B.ell N (s N))^(n-1) * (B.scale E N u)⁻¹^(n-1)`)
  with the `StochDom` N^τ factor made explicit, and the flow statement instantiates
  `ℓs := ell N (s N)` as in the paper. It holds for all `n ≥ 1`, which includes the "length ≤ 6"
  case the ticket needs.
- `eq557Set` is, word for word, the inner inequality of `Gauss.Step2.highProb_eq557_col` (T1492,
  merged) with `Hflow d N u ω` replaced by `M`. This is the T1492 form, which is what the ticket asks for.
- Measurability: both sets are finite intersections of `measurableSet_le` sets built from
  `measurable_gloop_matrix` / `measurable_green_matrix`. The guard `p.1 = y` is handled by an
  if-then-univ intersection. Sound.
- `highProb_flow_eq273/557` restate the accepted continuum-uniform flow results through `.mono`.
  They add no hypotheses beyond those of `Step1.apriori`/`step1Hyp_gauss_of_scale''` and
  `highProb_eq557_col`, which were accepted and shown satisfiable before.
- Generic transfer `highProb_grid_of_flow` works as follows. For each `k ≤ K N` (`Fin (K N + 1)`),
  the continuum event is restricted to the single time `u_k ∈ [s N, t N]`, using `mem_Icc_time`,
  which is proved for all `k ≤ K N` including `k = K N`, where `time_last` gives `u_k = t N`. That
  single-time complement probability is then transferred exactly (as an equality) through
  `Measure.map_apply` and `map_H_eq`. The `K N + 1` events are combined with `HighProb.biInter`, a
  union bound. So this transfer also uses **only single-time laws**. Simultaneity across grid times
  costs a polynomial union bound and is not derived from any joint-law claim.
- The union over `k ≤ K` is present, as the ticket requires.
- Left open, and stated as open in the prove report (allowed by the ticket): bare (4.2) and (5.31)
  matrix sets.

## 2. Vacuity, hidden hypotheses, cycles
- The only new hypotheses are `hK0 : ∀ N, K N ≠ 0` and
  `hKcard : ∀ᶠ N, ((K N + 1 : ℕ) : ℝ) ≤ N^C` with `0 ≤ C`. They concern only the auxiliary grid
  size, and they are needed for the union bound. **Compiled witness** (audit scratch file, run with
  `lake env lean` against the audit worktree): with `K N := N + 1` and `C := 2`, `hKcard` holds
  eventually (`N ≥ 3`), and `hK0` holds by `Nat.succ_ne_zero`. This `K` is independent of
  `E, s, t, κ, c`, so it can be combined with any existing satisfiability witness for the T1492 /
  Step-1 hypothesis list. The witness does not rely on anything being astronomically large.
- No `N = 0`, empty-index or collapsed-window loophole: `Fin (K N + 1)` contains both `k = 0` (time
  `s N`) and `k = K N` (time `t N`). The flow side quantifies over the full `TimeIcc s t N`.
- No structure-field smuggling (no new structures) and no `sorry`/`admit`/`axiom`.
- Dependencies: T1481 (`ef7f0e4`), T1489 (`e6b6894`) and T1492 (`a443cce`) are merged. The other
  imports (`APrimeSmoothPrefixCanonicalCore`, `Defs.MatrixMeasurable`, `Step1`, `StochDom`) are
  accepted modules that the root reaches. No cycle: the new file imports only accepted modules, and
  nothing imports it.
- Parameter order: all fixed parameters (`κ, E, s, t, c, K, C, n, τ`) come before the `HighProb`
  (`∀ D, ∀ᶠ N`) quantifier. This is correct.

## 3. Builds and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridJStar`: `Build completed successfully (3891 jobs)`, with no errors.
- `lake build RBM1D`: `Build completed successfully (9652 jobs)`, with no errors. On the branch,
  `GridJStar` is not yet root-imported; per the ticket, the root import is added at merge. The
  module build above compiles it together with all its dependencies.
- I ran `#print axioms` on `jSMat`, `jS_eq_jSMat`, `measurable_jSMat`, `jS_grid_law`,
  `mem_Icc_time`, `highProb_grid_of_flow`, `measurableSet_eq273Set`, `highProb_flow_eq273`,
  `highProb_grid_eq273`, `measurableSet_eq557Set`, `highProb_flow_eq557`, `highProb_grid_eq557` and
  `measurable_gloop_matrix`. Each printed `[propext, Classical.choice, Quot.sound]` and nothing else.
- A grep of the new file for `sorry|admit|axiom` returns nothing.

## 4. Remarks (non-blocking)
- `hKcard` is a Lean-side grid parameter hypothesis. The paper has no grid, so this is not a change
  to a paper statement. If the dispatcher wants a paper-delta line recording the grid union bound,
  it can be appended at merge; the prover was not allowed to touch `docs/paper-deltas.md`.
- `measurableSet_setOf_forall_imp` carries unused instance arguments (lint only).
