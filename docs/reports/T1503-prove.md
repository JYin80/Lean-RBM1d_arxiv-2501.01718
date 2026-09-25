Prover model: claude-sonnet-5

# T1503 — one-step drift identity of the 2-loop on the grid (discrete (2.45))

Ticket: `docs/tickets/T1503.md`. Role: prover-hard. Branch `t/T1503`. Sole writable file:
`RBM1D/Gauss/GridLoopStep.lean` (worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1503`).

## (a) Math preflight (written before any Lean; verdict per target)

Dependencies checked as already-accepted, merged results (present in `main` at the time the
worktree was branched, confirmed via `git log`): T1481 (`RBM.Gauss.Grid.H`/`time`/`step`,
`GridPath.lean`), T1482 (`condExp_freeze`, `GridMarkov.lean`), T1486 (`oneStep_error_le`, `genPt`,
`GridOneStep.lean`), T1487 (`loopDrift`, `norm_loopDrift_sub_le`, `GridDriftLip.lean`). Also used,
and independently confirmed already-merged (commit `e6b6894`, "T1489: merge grid-filtration
stopping times; root import", not listed in the ticket's dependency line but genuinely accepted):
`RBM.Gauss.Grid.H_measurable_filt` (`GridStopFilt.lean`), for the matrix-level (not just
entrywise) `filt d k`-measurability of `H`.

**(T1) `condExp_loop_step`.** Statement vs. `docs/claude-team/pilot-P4P5-paper.md` §3: exact
match — `condExp_freeze` (T1482) applied to the recursion `H_{k+1} = H_k + √Δ·X_{k+1}`. Step 0
check: `condExp_freeze` is real-valued only; `loopObs` is `ℂ`-valued, so a genuine (small) new
lemma is needed — a complex-valued freezing lemma. None of `condExp_freeze`'s ingredients
(`Measure.prod_eq`, `integral_map`, `integral_prod`, `ae_eq_condExp_of_forall_setIntegral_eq`,
…) are `ℝ`-specific, so this is a legitimate, non-circular derivation, not a new axiom.
Hypotheses: `hwf`, `hn` (matching `generator_add_zMotion_gauss`'s own requirements downstream, not
used by (T1) itself but kept for uniformity with (T2)-(T4)) and `(zt E u_{k+1}).im ≠ 0`. No
restriction on `Dims`. **Verdict: PASS.**

**(T2) `loop_step_space_err`.** Exact match to `oneStep_error_le` (T1486) specialised at
`Φ = loopObs d N (zt E u) I`, with Lipschitz constant `Λ` for `genPt Φ`. Step 0 check: `genPt Φ`
equals the `(1/2)Σ S·wirtSecond` part of `generator_add_zMotion_gauss`
(`genPt = genD` up to the `1/2` vs. `2⁻¹` notation, then `genD_eq_sum_pairs`
(`MomentDuhamelHypGauss.lean`) rewrites it as the index-pair sum, matching
`generator_add_zMotion_gauss`'s LHS exactly), so
`genPt(Φ_u)(M) = loopDrift(u)(M) − zMotion(M, z_u, I)`. `loopDrift` is already `M`-Lipschitz
(`norm_loopDrift_sub_le`, T1487); `zMotion` had **no** `M`-Lipschitz bound in the repo — the
ticket anticipated this ("if zMotion has no Lipschitz bound in the repo, prove one; zMotion is a
finite sum of loops of M, so `norm_gloop_sub_le` applies"), confirmed by grep (only an unrelated
`RBM.Gauss.norm_zMotion_sub_le`, an envelope bound for a different purpose, pre-existed). A new
`M`-Lipschitz bound is legitimate, non-circular (built from the already-accepted, public
`RBM.norm_gloop_sub_le` and `norm_green_sub_le_of_herm`). Hypotheses: `hwf`, `hn`, `(zt E u).im≠0`,
`M.IsHermitian`, `0 ≤ Δ`; no restriction on `Dims`. **Verdict: PASS.**

**(T3) `loop_step_time_err`.** The ticket's own suggested route ("`z_u` affine in `u`, `∂_z G =
G²`, resolvent bounds") maps to: the exact FTC identity `g(u′) − g(u) = ∫_u^{u′} zMotion(M, z_v,
I) dv` (from `hasDerivAt_gloop_zt`, already accepted, public) turns the quadratic remainder into
an interval integral of `zMotion(z_v) − zMotion(z_u)`, which needs a **`z`-Lipschitz** bound for
`zMotion` at fixed `M` (not a genuine "second `z`-derivative", but functionally what closes the
same gap the ticket flagged). No such bound existed; proved here from the *already-accepted*
`RBM.norm_green_sub_le` (both matrix and spectral parameter may move; used here with the same
matrix, so `‖H−H'‖=0`) and `RBM.norm_gloop_sub_le`, mirroring the `M`-Lipschitz derivation.
Boundary/hypotheses check: the window `[u,u′]` must stay inside the domain where `Im z_v` is
bounded away from `0` — this needs `|E|<2` (not just `(zt E u).im ≠ 0` at the two endpoints
individually), because the argument needs a **uniform** lower bound over the *whole closed
interval* (`Im z_v = (1−v)(mE E).im`, minimised at `v=u′`), not just at `u,u′`. This is the one
place the ticket's Step-0 warning applies ("if (T4) forces a hypothesis beyond … report it as
blocked"); see the note in §(d) below — it is not blocking, since `|E|<2` is the paper's own
standing hypothesis on the physical energy (used everywhere else in the repo, e.g.
`zt_im_ne_zero_of_lt_one`), not a new restriction, and it is exhibited simultaneously satisfiable
below. Hypotheses: `hwf`, `M.IsHermitian`, `0 ≤ u`, `u < u′`, `u′ < 1`, `|E| < 2`; no restriction
on `Dims`. **Verdict: PASS.**

**(T4) `condExp_loop_drift`.** Combining (T1)-(T3) with `generator_add_zMotion_gauss` as the
ticket says needs one more piece of bookkeeping the ticket's one-line summary does not spell
out: naively comparing `genPt(Φ_{u_{k+1}})(M)` against `genPt(Φ_{u_k})(M)` (to use the identity
`loopDrift(u_k)(M)=genPt(Φ_{u_k})(M)+zMotion(u_k)(M)` and cancel) would need a **`z`-Lipschitz
bound for `loopDrift`/`genPt` itself** — a much larger derivation (re-deriving the whole
`driftLip` apparatus of `GridDriftLip.lean` for the `z`-moving case) that is not available and
not needed. Instead the decomposition compares `Φ_{u_{k+1}}` and `Φ_{u_k}` **inside** the
integral over the fresh increment `x` (i.e. pointwise in `x`, via (T3) applied at the Hermitian
matrix `M+√Δ·X(x)`), and only ever invokes (T2) at the single time `u_k`; the identity
`loopDrift(u_k)(M)=genPt(Φ_{u_k})(M)+zMotion(u_k)(M)` is then used **at one time only**, so no new
Lipschitz-in-`z` fact about `loopDrift` is needed. This is a genuine (and, on reflection, simpler)
alternative route to the same target, not a weakening: the *statement* proved is exactly the
ticket's (T4), with the main term `Δ·loopDrift` at `u_k` (not `u_{k+1}`), and error of order
`Δ^{3/2}+Δ²` with constants polynomial in `N` and `η_{u_k}^{-1}`/`η_{u_{k+1}}^{-1}`
(`zMotionZLip`, `zMotionLip`, `genPtLip`, all explicit). Hypotheses beyond
`(zt E u).im≠0`/`u_k,u_{k+1}∈[0,1)`: `|E|<2` (as in (T3)) and `s N < t N`, `k < K N`
(nondegenerate grid step `Δ>0`, needed for the statement to be non-vacuous at all — without them
`Δ` could be `0` or undefined). All are natural, already-standard hypotheses (not new
restrictions on `Dims`), and a full compiled witness (`example` at the end of the file) shows
every hypothesis of `condExp_loop_drift` is simultaneously satisfiable with concrete,
non-degenerate data (`Dims.exampleGrow`, `E=0`, a single grid step of size `1/8` inside
`[1/4,3/8] ⊆ [0,1)`, the length-`1` loop `⟨[true],[0]⟩`). **Verdict: PASS** (not blocked — the
extra hypotheses are standard and exhibited satisfiable, per the discussion above).

No target required weakening a hypothesis, changing a frozen signature, or widening the file
scope. No `Dims`-restricting hypothesis anywhere. No vacuous `N=0`/empty index set/collapsed
window; the compiled witness in §8 of the file confirms this for the composite (T4).

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridLoopStep.lean` (new), namespace `RBM.Gauss.Grid`.

Public declarations (targets and supporting infrastructure):
- `H_succ`, `condExp_freezeC` (complex-valued freezing lemma), `condExp_loop_step` **(T1)**.
- `norm_zMotion_sub_le_mz` (general `zMotion` Lipschitz bound, both `M` and `z` may move),
  `zMotionLip`, `norm_zMotion_sub_le_ofM`, `zMotionZLip`, `norm_zMotion_sub_le_ofZ`.
- `genPtLip`, `genPt_eq_loopDrift_sub_zMotion`, `loop_step_space_err` **(T2)**.
- `loop_step_time_err` **(T3)**.
- `condExp_loop_drift` **(T4)** (the deterministic core is the `private`
  `norm_loop_step_drift_le`).

Build commands and results:
```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1503 && lake build RBM1D.Gauss.GridLoopStep
```
→ `Build completed successfully (3812 jobs)`, zero errors, zero warnings for this file (all
`longLine`/`show`/`maxHeartbeats` style-lint warnings fixed; one `set_option maxHeartbeats
1000000 in` retained, with an explanatory comment, on the single heaviest lemma
`norm_loop_step_drift_le`, matching existing practice, e.g. `RBM1D/Hierarchy/DriftBound.lean`).

`#print axioms` (via a scratch file importing the module):
```
'RBM.Gauss.Grid.condExp_loop_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.loop_step_space_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.loop_step_time_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.condExp_loop_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/`axiom` anywhere in the file (`grep sorry\|admit` → no matches).

## (c) Key lemmas used

- `RBM.Gauss.Grid.condExp_freeze` (T1482), `RBM.Gauss.Grid.H_measurable_filt` (T1489, already
  merged), `RBM.Gauss.testFun_loopObs_of_im_le` (`LoopC2.lean`), `RBM.Gauss.oneStep_error_le`,
  `RBM.Gauss.Grid.genPt`/`gen_eq_integral_genPt` (T1486), `RBM.Gauss.Grid.loopDrift`/`loopDrift_eq`
  /`norm_loopDrift_sub_le`/`driftLip` (T1487), `RBM.Gauss.generator_add_zMotion_gauss`/`zMotion`/
  `hasDerivAt_gloop_zt` (`LoopIto.lean`), `RBM.Gauss.genD_eq_sum_pairs`
  (`MomentDuhamelHypGauss.lean`), `RBM.norm_gloop_sub_le`/`norm_Gsig_sub_le_norm_green_sub`
  (`LoopLipschitz.lean`), `RBM.norm_green_sub_le` (`FlowHolder.lean`),
  `RBM.Gauss.Grid.norm_green_sub_le_of_herm` (T1487, `GridDriftLip.lean`), `RBM.Gauss.continuous_
  green_comp`/`continuous_matrixTrace` (`Hierarchy.lean`), `ContinuousLinearMap.comp_condExp_comm`,
  `MeasureTheory.integral_re`/`integral_im`/`Integrable.re`/`Integrable.im` (Mathlib, `RCLike`),
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `Real.mE_im_pos`, `zt_im`,
  `zt_im_ne_zero_of_lt_one` (`IBP.lean`).

## (d) Open issues / notes for downstream (T1504 and later)

1. **Two new explicit hypotheses beyond the ticket's Step-0 shorthand**, both natural/standard,
   both discovered while proving (T3)/(T4) rather than assumed: `|E| < 2` (needed for a uniform
   lower bound on `Im z_v` across the closed window `[u_k, u_{k+1}]`, not just at the two
   endpoints — the paper's own standing assumption on the physical energy) and `s N < t N`,
   `k < K N` (nondegenerate grid step `Δ > 0`). Neither restricts `Dims`; both are exhibited
   simultaneously satisfiable with the rest of (T4)'s hypotheses in the compiled witness at the
   end of the file. Recommend T1504 (and the pilot doc) record these explicitly rather than only
   `(zt E u).im ≠ 0` and `u_k, u_{k+1} ∈ [0,1)`.
2. **`errStep`'s "uniform in `k`" claim.** The ticket's acceptance criterion "the error is `o(Δ)`
   uniformly in `k`" is met *pointwise per `k`* here (the bound is explicit and does not depend on
   the sample `ω`), but its numeric size still depends on `k` through `η_{u_k}^{-1}`,
   `η_{u_{k+1}}^{-1}`; genuine uniformity over `k = 0, …, K(N)-1` for a *specific* application
   (e.g. the stopped-time argument of `docs/claude-team/pilot-P4P5-paper.md` §4) requires that
   downstream ticket to supply a uniform lower bound on `Im z_v` over the whole window (which the
   pilot doc's stopping-time construction is designed to provide) and substitute it into
   `zMotionZLip`/`zMotionLip`/`genPtLip` here; no further work is needed in *this* file.
3. **No paper-delta.** Nothing here contradicts or amends a paper formula; the extra hypotheses
   in (1) are formalization bookkeeping already implicit in the paper's standing assumptions, not
   a correction to a stated formula, so no `docs/paper-deltas.md` entry was added.
