Auditor model: claude-opus-5-5[1m]

# T1503 audit: one-step drift identity of the 2-loop on the grid (discrete (2.45))

Ticket: `docs/tickets/T1503.md`. Prove report: `docs/reports/T1503-prove.md`. Branch `t/T1503` @ `adc04a6`.
Audit worktree (fresh, detached at `adc04a6`, no cached `GridLoopStep` artifacts): `/Users/junyin/Lean_proof/RBM1D-wt/T1503-audit`.
Diff vs `main`: exactly one new file, `RBM1D/Gauss/GridLoopStep.lean` (938 lines). Its imports are unchanged between the branch base `752dd76` and current `main` (`ab5d007` only adds new files).

**Overall verdict: PASS** (T1–T4 all PASS).

## 0. Process checks
- The prove report's section (a) is a math preflight, with a verdict per target (T1–T4 all PASS), and it comes before the Lean sections (b)–(d). First line reads `Prover model: claude-sonnet-5`.
- Sole writable file respected: `git diff --stat main...t/T1503` shows only `RBM1D/Gauss/GridLoopStep.lean`. No frozen signature was touched, and no root import was added (that happens at merge).
- `grep sorry|admit|axiom` on the file: no matches.

## 1. Build and axioms (run in the audit worktree)
- `lake build RBM1D.Gauss.GridLoopStep`: `Build completed successfully (3812 jobs)`. The module was compiled from scratch and emitted no warnings (on the rebuild it was not in the "Replayed with warnings" list).
- `lake build RBM1D`: `Build completed successfully (9649 jobs)`. On the branch the root does not yet import the module, because the import is added at merge. Current `main` changed no dependency of the module, so the post-merge root build carries no extra risk.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all of the following: `H_succ`, `condExp_freezeC`, `condExp_loop_step`, `norm_zMotion_sub_le_mz`, `norm_zMotion_sub_le_ofM`, `norm_zMotion_sub_le_ofZ`, `genPt_eq_loopDrift_sub_zMotion`, `loop_step_space_err`, `loop_step_time_err`, `condExp_loop_drift`.

## 2. Dependencies
All dependencies are merged results that are ancestors of the branch:
- T1481: `H`, `time`, `step`
- T1482: `condExp_freeze`
- T1486: `oneStep_error_le`, `genPt`
- T1487: `loopDrift`, `norm_loopDrift_sub_le`, `driftLip`, `norm_green_sub_le_of_herm`
- T1489: `H_measurable_filt`. Commit `e6b6894` is an ancestor and the module is root-imported. It is not named in the ticket's dependency line, but it is accepted.
- `generator_add_zMotion_gauss`, `hasDerivAt_gloop_zt`, `zMotion` (`LoopIto`)
- `genD_eq_sum_pairs` (`MomentDuhamelHypGauss`)
- `norm_gloop_sub_le` (`LoopLipschitz`)
- `norm_green_sub_le` (`FlowHolder`)
- `zt_im`, `mE_im_pos`, `zt_im_ne_zero_of_lt_one`

There is no cycle: the new file imports only existing modules.

The new helper `condExp_freezeC` (the complex version of the freezing lemma) is derived from the real `condExp_freeze` applied to the real and imaginary parts. It uses `ContinuousLinearMap.comp_condExp_comm` and `integral_re`/`integral_im`. The proof is legitimate and contains no hidden assumption.

## 3. Per-target statement check

Notation used below: `u_k = time s t K N k = s N + k·Δ` and `Δ = step s t K N = (t N − s N)/K N`. `H k = √(s N)·X_0 + √Δ·Σ_{i=1}^k X_i`, so `Var H_k = u_k`, which matches pilot §2. The spectral parameter is `zt E u = E + (1−u)·mE E`, and `(zt E u).im = (1−u)·Im mE E` (paper z_u).

### (T1) `condExp_loop_step` — PASS
- Statement: `(Pg d)[Φ_{u_{k+1}}∘H_{k+1} | filt d k] =ᵐ ∫ x, Φ_{u_{k+1}}(H_k ω + Hflow d N Δ x) dP`.
- `Hflow d N Δ x` is by definition `(√Δ:ℂ) • Xmat d N x`, so this is exactly the ticket's formula.
- Hypotheses are `I.WF`, `1 ≤ I.a.length` and `(zt E u_{k+1}).im ≠ 0`. These are exactly what makes `Φ` a `TestFun`.
- The hypothesis `k < K N` is not needed, so the statement is more general than the ticket asks.

### (T2) `loop_step_space_err` — PASS
- Statement: for Hermitian `M` and `0 ≤ Δ`, `‖∫Φ_u(M+√Δ X) − Φ_u(M) − Δ·genPt Φ_u M‖ ≤ (2/3)·genPtLip(L,W,n,η_u,mSigma E)·Δ^{3/2}·∫‖X‖dP`.
- The constant is explicit: `genPtLip = driftLip + zMotionLip`, both closed forms polynomial in `L`, `W`, `n` and `(1+η⁻¹)`, `η⁻¹`.
- There are no existentials over constants.
- `genPt_eq_loopDrift_sub_zMotion` identifies `genPt` with the `(1/2)Σ S·wirtSecond` part of `generator_add_zMotion_gauss`, as the ticket requires.

### (T3) `loop_step_time_err` — PASS
- Statement: for Hermitian `M` and `0 ≤ u < u' < 1`, `‖Φ_{u'}(M) − Φ_u(M) − (u'−u)·zMotion(M, z_u, I)‖ ≤ zMotionZLip(L,W,n,(1−u')·Im mE,mSigma E)·‖mE E‖·(u'−u)²/2`.
- `(1−u')·Im mE = η_{u'}`, and the constant is polynomial in `η_{u'}⁻¹`, `L` and `W`. This matches the ticket.
- The extra hypothesis `|E| < 2` is not a real restriction:
  - `mE E = (−E + √(4−E²)·i)/2`, so `(zt E u).im ≠ 0` already forces `|E| < 2`. I compiled `example (h : (zt E u).im ≠ 0) : |E| < 2` in scratch and it passes.
  - Without some such hypothesis the ticket's `η_{u'}` would be `0`.

### (T4) `condExp_loop_drift` — PASS
- Statement: for `k < K N`, a.e. `ω`, `‖E[Φ_{u_{k+1}}∘H_{k+1} | filt k] ω − Φ_{u_k}(H_k ω) − Δ·loopDrift E u_k I (H_k ω)‖ ≤ errStep`.
- `errStep = zMotionZLip(η_{u_{k+1}})·‖mE E‖·Δ²/2 + (zMotionLip(η_{u_k}) + (2/3)·genPtLip(η_{u_k}))·Δ^{3/2}·∫‖X‖dP`.
- errStep is explicit, deterministic (independent of `ω`) and of order `Δ^{3/2} + Δ²`.
- Hypotheses beyond the ticket's list (`(zt E u).im ≠ 0`, `u_k, u_{k+1} ∈ [0,1)`, `k < K N`):
  - `|E| < 2` is implied by `hzk`; see (T3).
  - `s N < t N` is forced. If `s N > t N`, then `√Δ = 0` in Lean and `u_{k+1} < u_k`, so the left side is about `−Δ·genPt`, which is not `o(Δ)`. The case `s N = t N` is a trivial degenerate case. Both are part of the grid setup (pilot §2).
  - Neither hypothesis restricts `Dims`, so this does not trigger the ticket's "blocked" clause.

**Acceptance criteria:**
- (T4)'s main term is `Δ · loopDrift` at `u_k`, not at `u_{k+1}`: **yes**. It is `(step s t K N : ℂ) • loopDrift E (time s t K N k) I (H d s t K N k ω)`.
- The error is `o(Δ)` uniformly in `k`: **yes**.
  - Every constant is a polynomial with nonnegative coefficients in `η⁻¹`, where `η` is `η_{u_k}` or `η_{u_{k+1}}`. So it is nonincreasing in `η`.
  - For all `k < K N` we have `η_{u_k} ≥ η_{u_{k+1}} ≥ (1 − t N)·Im mE E > 0`, using `u_{k+1} ≤ t N < 1`.
  - Hence `errStep ≤ C(N, (1−t N)·Im mE)·(Δ² + Δ^{3/2}·∫‖X‖)`, with one `k`-independent constant.
  - Therefore `errStep/Δ = O(Δ^{1/2}) → 0` as `K N → ∞`.
- No hypothesis restricts `Dims`: **yes**. `d : Dims` is arbitrary in every statement.
- Constants explicit with no existentials, names (T1)–(T4) as specified, first report line `Prover model: …`: **yes**.

## 4. Vacuity and satisfiability
- The prover's in-file witness uses `Dims.exampleGrow`, `N = 0` and a length-1 loop. It is valid, but it is a special case.
- I compiled a stronger witness in scratch (not committed). For **arbitrary** `d : Dims`, **every** `N`, **every** `k < K N = N+1`, `s ≡ 1/4`, `t ≡ 1/2`, `E = 1`, and the 2-loop `I = ⟨[true,false],[a,b]⟩` (σ = (+,−), arbitrary `a, b`), all hypotheses of `condExp_loop_drift` hold at once. It compiles with no errors.
- This rules out every loophole the audit looks for: no `N = 0` dependence, no empty index set, no collapsed window (`Δ = 1/(4(N+1)) > 0`), and no astronomically large parameter.
- The conclusion does not hold trivially: the main term and the conditional expectation are genuine, and the bound is finite.
- There is no hidden hypothesis in a structure field. `TestFun` is only produced internally from `testFun_loopObs_of_im_le`.

## 5. Notes (non-blocking)
1. The constant `∫‖Xmat d N ω‖ dP` comes from the accepted `oneStep_error_le` (T1486). It is deterministic and independent of `k`, but it has no closed-form polynomial-in-`N` bound in this file. A downstream ticket that needs the explicit `N^C` should supply that bound; for example, operator norm ≤ Frobenius norm plus the second moment.
2. The statements are for a general well-formed loop `I` with `1 ≤ length`. The ticket's 2-loop with σ = (+,−) is the special case, so the general statement implies the ticket's target.
3. The remainder is `Δ^{3/2}`, not the `Δ²` that the fourth-order Taylor route in pilot §3 would give. The ticket explicitly allows `Δ^{3/2} + Δ²`. Summed over `K` steps it is `(t−s)·Δ^{1/2}·C`, which is still `o(1)`. T1504 should use this rate.
4. The prover's "|E| < 2 is an extra hypothesis" note in (d)1 is overcautious, since `|E| < 2` follows from `(zt E u).im ≠ 0`. No paper-delta is needed.
