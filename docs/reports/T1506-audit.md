Auditor model: claude-opus-5-5[1m]

# T1506 re-audit — GridDriftAlgebra (discrete (5.19)/(5.20)), after repair adding (T4)

Audited commit: `b57d39d` on `t/T1506` (parent `dc1d19f` = merge of `main` b74a55e; (T1)-(T3) from `fc4d6a4`). Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1506-audit2`. It is fresh, detached at b57d39d, and has an APFS clone of the main build cache. It is neither the repairer's worktree nor the first audit's. Audit time: 2026-09-26 00:47 UTC.

## Overall verdict: PASS

(T1), (T2), (T3): PASS, with no regression. (T4): PASS.

## Gates

- Diff: `git diff --stat main...t/T1506` and `git diff --stat main t/T1506` both show only `RBM1D/Gauss/GridDriftAlgebra.lean` (+1086). `main` = b74a55e is the merge base, so nothing else in the tree differs. No frozen signature is touched. The only new import is `RBM1D.Gauss.GridLoopStep` (T1503, merged 2b49f8f, already imported by the root at `RBM1D.lean:529`).
- Regression check (T1)-(T3): `git diff fc4d6a4 b57d39d -- RBM1D/Gauss/GridDriftAlgebra.lean` has three hunks. They are the new import, the module docstring's (T4) bullet (the only two removed lines), and the append after the old line 678 (`end T3`). The (T1)-(T3) statements and proofs are byte-identical to the version PASSed in the first audit.
- `grep sorry|admit|axiom|native_decide|implemented_by|extern` in the file: none.
- `lake build RBM1D.Gauss.GridDriftAlgebra`: the module's .olean was absent from the cloned cache, so it was compiled from scratch (`Built RBM1D.Gauss.GridDriftAlgebra`). Result: `Build completed successfully (3813 jobs)`, exit 0, 0 errors. There are only the pre-existing (T1)-(T3) linter warnings (`show` at 111/459/479, unused `hM`/`hz` at 66, an unexecuted `first` at 268).
- `lake build RBM1D`: `Build completed successfully (9657 jobs)`, exit 0. The root does not import this module yet (that happens at merge).
- Axioms (my scratch file outside the tree, importing `RBM1D` and `RBM1D.Gauss.GridDriftAlgebra`, run with `lake env lean`): `discrete_hierarchy_step`, `discrete_hierarchy_step_unif`, `stepErr_le_unif`, `loopDrift_sub_K_deriv`, `K_step`, `Uker_step`, `norm_Kv_le`, `norm_Lval_le`, `norm_xiOf_pm_le`, `zMotionLip_anti`, `zMotionZLip_anti`, `genPtLip_anti` each give `[propext, Classical.choice, Quot.sound]`.
- Name clashes: the same scratch file elaborates with no errors. I also grepped the whole main tree for the new names (`ofFn_two'`, `stepErr`, `stepErrC1/C2`, `norm_Kv_le`, `norm_Lval_le`, `norm_xiOf_pm_le`, `*_anti`, `discrete_hierarchy_step`) outside this file: none are defined elsewhere.
- Math preflight: the prove report §(a) has a (T4) preflight, timestamped 00:34 UTC and marked as written before any (T4) Lean. The (T4) commit b57d39d is at 00:43 UTC. (T1)-(T3) keep the original preflight.

## (T1) `loopDrift_sub_K_deriv`, (T2) `K_step`, (T3) `Uker_step` — PASS (unchanged)

The declarations are identical to fc4d6a4. The first audit's findings stand:
- (T1): the Θ-part is literally `ThetaOp (B.L N) (xiOf (mSigma E) ![true,false]) u (L_u(M) − K_u)`, the same `ξ` that `Uker` uses.
- (T2): `errK = |μ|³ W⁻¹ (1−u'|μ|)⁻¹ (1−u|μ|)⁻²` is explicit.
- (T3): `errU = 3(1−u_{j+1})⁻²` is explicit. The n = 2 scope follows from the ticket's own notation.

## (T4) `discrete_hierarchy_step` — PASS

**Statement vs ticket.** Let `A_k(ω) := fun v => Lval B E N u_k (H_k ω) v − Kv B E N u_k v` on `LoopArg (B.L N) 2`. The conclusion is: for a.e. `ω ∂ Pg B.toDims`, for all `a`,
`‖E[A_{k+1}(a) | filt k](ω) − Uker (B.L N) ξ u_k u_{k+1} (A_k ω) a − Δ·(eGterm … (H_k ω) (zt E u_k) ⟨+-,a⟩ + primBil (gloop−K_{u_k}) (gloop−K_{u_k}) ⟨+-,a⟩)‖ ≤ stepErr B E N u_k u_{k+1} Δ`.
- This is exactly the ticket's `E[A_{j+1}|F_j] − U A_j = Δ(EG + quad)(H_j) + R_j` with `‖R_j‖_∞ ≤ errStep'`. The `∀ a` inside the a.e. set gives the sup norm over labels.
- EG-part and quad-part are literally the (T1) terms at `M = H_k ω`, `u = u_k`.
- `ξ = xiOf (mSigma E) ![true,false]` is the same as in (T1).
- The Θ-part is absorbed exactly into `Uker`. The proof cancels it by `linear_combination Δ * (T1)`, so it is not merely bounded.
- There is no `hstep`. T1503's `condExp_loop_drift` is applied directly (proof line 878), so the ticket's "hstep verbatim" criterion is moot.

**Hypotheses: only `|E| < 2`, `s N < t N`, `k < K N`, `0 ≤ u_k`, `u_{k+1} < 1`.** I checked the claimed removals against the compiled proof. They are derivations inside the proof, not assertions:
- `hzk`, `hzk1`: `zt_im_ne_zero_of_lt_one hEb huk_lt` / `… hEb hu1` (`Gauss/IBP.lean:227`, hypotheses only `|E|<2`, `t<1`). `u_k < 1` follows from `u_k ≤ u_{k+1}`, since `Δ > 0` from `hst`, `hk`.
- `hwf`: `rfl` for `I = ⟨[true,false], ofFn a⟩`.
- `hn`: `List.length_ofFn`.
- Integrability of `loopObs(z_{u_{k+1}}) I ∘ H_{k+1}` is derived, not assumed. It uses `testFun_loopObs_of_im_le` for boundedness and continuity, `H_measurable_filt` + `(filt d).le` for measurability, and then `memLp_top_of_bound … |>.integrable`. This is the same route as `condExp_loop_step`'s `hIntTarget`.
- `loopObs = gloop` on `H_{k+1} ω'` via `loopObs_of_isHermitian (H_isHermitian …)`.
- The (T1)/(T2) Theta-invertibility conditions `‖u_k μ‖ < 1` and `‖u_{k+1} μ‖ < 1` are derived from `norm_mSigma` (`|μ| = 1`) and `u < 1`.
- (T3)'s `‖ξ_i‖ ≤ 1` comes from `norm_xiOf_pm_le`, and its sup bound `M_k` from the deterministic lemmas `norm_Lval_le` (via `norm_gloop_le_of_le_abs_im`, Hermitian `H_k ω`) and `norm_Kv_le` (entry ≤ ℓ^∞ row sum, then `norm_Theta_le`).

So no hypothesis was silently added, and the hypothesis list is a strict subset of `condExp_loop_drift`'s. `B : Band Ω'` is arbitrary. Its structure fields are the paper's standing assumptions ((2.2), `N ≍ WL`) and play no role in the proof beyond `three_le_L` and `W_pos`. `Band` is inhabited (`RBM.Gauss.band d`, `Gauss/Model.lean:388`).

**Error term.** `stepErr` (line 779) is a closed-form real expression in `(B.L N, B.W N, E, u_k, u_{k+1}, Δ, ∫‖Xmat B.toDims N‖ dP)`. It does not depend on `ω`, so it is deterministic. It is the sum of:
- `condExp_loop_drift`'s right-hand side at `I.σ.length = 2`, i.e. `O(Δ²) + O(Δ^{3/2})`. It is literally T1503's constant: (T4) sits in a namespace block that opens only `Matrix.Norms.L2Operator`, so `‖Xmat‖` is the same norm as in T1503. `he1` is obtained from T1503's `h1` by `rw`+`exact`, which confirms this.
- The (T2) remainder `W⁻¹(1−u_{k+1})⁻¹(1−u_k)⁻² Δ²`.
- The (T3) remainder `3(1−u_{k+1})⁻² Δ² M_k`, with `M_k = |Im z_{u_k}|⁻² W⁻¹ + W⁻¹(1−u_k)⁻¹`.

The first audit's required ingredients are all present: integrability via the `hIntTarget` route, a deterministic `M` via the gloop and Theta bounds, and an explicit `O(Δ^{3/2}+Δ²)` error.

**Uniform-in-k form (`stepErr_le_unif`, `discrete_hierarchy_step_unif`).** On `u_k ≤ u_{k+1} ≤ 1−δ`, `δ > 0`, `Δ ≥ 0`: `stepErr ≤ stepErrC1·Δ² + stepErrC2·Δ^{3/2}`.
- `stepErrC1 B E N δ` and `stepErrC2 B E N δ` depend only on `B.L N`, `B.W N`, `E`, `δ` (through `η_δ = δ·Im m(E) > 0`, via `mE_im_pos`) and `∫‖Xmat B.toDims N‖`. They do not depend on `k`, `s`, `t` or `K`.
- Monotonicity of T1503's constants in `η` is proved (`*_anti`, by `gcongr` on the definitions, which are products of nonnegative factors with `η⁻¹` powers).
- The bound applies `|Im z_{u_k}| = (1−u_k) Im m ≥ η_δ` and `(1−u_{k+1}) Im m ≥ η_δ`.
- Hence `R_k/Δ ≤ C₁Δ + C₂Δ^{1/2} → 0` as `Δ → 0`, uniformly in `k`. The sum over `K` steps is `≤ (t−s)(C₁Δ + C₂Δ^{1/2})`. This is the acceptance criterion "R_j is o(Δ) uniformly in j", as a compiled statement.

**N-growth of the constants (open issue 3 in the prove report) is acceptable scope, not a defect.**
- The constants grow polynomially in `L`, `W` (`driftLip ∝ L⁴W³…`, `zMotionLip ∝ L²W²…`) and through `∫‖Xmat‖`, all at fixed `N`. They are inherited verbatim from T1503 (T4), which passed its audit with the same constants.
- The grid size `K : ℕ → ℕ` is a free parameter. Choosing `K N` large relative to any polynomial in `N` makes `(t−s)(C₁Δ + C₂Δ^{1/2}) → 0`. The ticket asks for uniformity in `j`, not in `N`.
- Tracking the N-dependence is the concern of the downstream assembly (T1505/T1504-amend-1/5.21). It needs no new input here.

**Satisfiability witness (checked independently, in my scratch file).**
- The in-file `example` (line 1073) proves every hypothesis of both (T4) theorems, plus `0 < step`, for `s ≡ 1/4`, `t ≡ 1/2`, `K ≡ 2`, `N = k = 0`, `E = 0`, `δ = 5/8`. That gives `Δ = 1/8`, `u₀ = 1/4`, `u₁ = 3/8 = 1 − δ`.
- I also applied the theorems themselves, which leaves no gap between the witness and the signatures:
  - `discrete_hierarchy_step (band Dims.exampleGrow) (fun _ => 1/4) (fun _ => 1/2) (fun _ => 2) 0 0 0 …` elaborates.
  - The same for `discrete_hierarchy_step_unif` with `δ := 5/8`.
  - As a generic-N instance, `discrete_hierarchy_step (band Dims.exampleGrow) (fun _ => 0) (fun _ => 1/2) (fun _ => 10) 7 3 1 …` (`N = 7`, `k = 3`, `E = 1`) elaborates.
- Vacuity checks:
  - `N` is free and nothing depends on `N = 0`.
  - `LoopArg (B.L N) 2` is nonempty (`L ≥ 3`).
  - `Δ > 0` is derived, so the window never collapses.
  - `E` ranges over the whole bulk `|E| < 2`.
  - No quantity has to be astronomically large.

**Dependencies.** All are already accepted:
- `condExp_loop_drift`, `testFun_loopObs_of_im_le`, `H_measurable_filt`, `H_isHermitian`, `loopObs_of_isHermitian`, `zMotionLip`/`zMotionZLip`/`genPtLip` (T1503 / T1481 grid model, merged).
- `norm_gloop_le_of_le_abs_im`, `norm_Theta_le`, `norm_mSigma`, `zt_im`, `mE_im_pos`, `zt_im_ne_zero_of_lt_one` (in main).
- (T1)-(T3) of this file (PASS).

There is no cycle, since no module on main imports this file.

## Scope notes (not defects; for the dispatcher)

1. This is the grid-model bridge (`Pg`, `H`, `filt` of T1481/T1503), one step, `σ = (+,−)` 2-loop, `|E| < 2`, arbitrary `B`. This is the ticket's specified setting. Per CLAUDE.md §3.5 it is the discrete realization of (5.19)/(5.20), not the paper's continuous-time Brownian statement.
2. The repairer suggests a `docs/paper-deltas.md` entry recording that (5.19)/(5.20) are realized on the grid with error `O(Δ^{3/2})`. That file is outside the repairer's writable scope, and none was appended. Recommended at merge: the dispatcher assigns a number.
3. (T3) is n = 2 and (T1) keeps the unused `hM`/`hz`, as accepted in the first audit.

## Required for resubmission

None.
