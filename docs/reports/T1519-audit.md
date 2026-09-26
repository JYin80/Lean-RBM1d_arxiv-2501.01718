Auditor model: claude-opus-5-5[1m]

# T1519 audit (re-audit after repair, against docs/tickets/T1519-amend-1.md)

Branch `t/T1519` (commits `04d312a`, `d6116e3`), audited in a fresh worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1519-audit` (detached at `d6116e3`; no stale GridGoodEvent build
artifacts were present, so the module was compiled from scratch). The prover worktree was not used.
Report audited: `docs/reports/T1519-prove.md`.

**Overall verdict: PASS.**

## Scope / hygiene

- `git diff --stat main...t/T1519`: one file, `RBM1D/Gauss/GridGoodEvent.lean` (+2268). No other source,
  no root `RBM1D.lean`, no frozen signature touched. Branch base `db76845`; `main` has since added only new
  files (GridStepBound, GridBootstrap, Steps12Gauss) and three root import lines, none of which this file
  imports; all 7 imports (GridGoodSet, GridExpansion, GridQVForm, GridQVStep, GridQVSum, GridDuhamelTail,
  GridNetLift) are root-imported on `main` and identical on the branch -> dependencies are accepted results only.
- `grep sorry|admit|axiom|native_decide|implemented_by|unsafe|opaque`: none. One
  `set_option maxHeartbeats 1000000 in` on `xZ_le_azumaMm` (commented), harmless.
- `lake build RBM1D.Gauss.GridGoodEvent`: `Built RBM1D.Gauss.GridGoodEvent`, `Build completed successfully
  (3959 jobs)`, 0 errors, 0 warnings in the file. 71 `#print axioms` lines, all exactly
  `[propext, Classical.choice, Quot.sound]`.
- `lake build RBM1D`: `Build completed successfully (9666 jobs)`, 0 errors; root axiom audit "21092 declarations
  in `RBM`, all within [propext, Classical.choice, Quot.sound]". (The branch root does not import the new module;
  the module build above is what covers it.)

## Math preflight (item 1)

`T1519-prove.md` contains a per-target preflight section "Preflight for the amended targets
(T1519-amend-1), written before any new Lean", with PASS for (T3'), (T4'), (T6') and the Step-0 interface
checks, placed before section (b) Lean. PASS.

## (T1), (T2), (T5): unchanged

`git diff 04d312a d6116e3`: 9 removed lines, all module-docstring / section-header / docstring text
(relabelling the original-(T3) negation as a counterexample); one added import (GridNetLift). No statement or
proof of `gridTau`, `isStoppingTime_gridTau`, `lt_gridTau_measurableSet`, `lt_gridTau_imp`, `gridTau_le`,
`thr_le_sqrtN`, `Qprime`, `cZ`, `hsubG_gridTau`, `hsubG_gridTau_hyps_witness`, `initSet`,
`highProb_init_grid` changed. PASS (unchanged, as the amend requires).
`not_highProb_azuma_grid_literal(')` remain but are clearly labelled "counterexample to the superseded
original (T3) spec, not part of the (T3') API", which the amend allows.

## (T3') `highProb_azuma_grid'` -- PASS

Statement (line 907): hypotheses `|E|<2`, `0 ≤ s ≤ t < 1`, gained hreg `N^c R^30 ≤ scale(t)`, `0<δ≤c/24`,
`0≤D`, `s≤u≤t`, `K N ≠ 0`, `∀ᶠ N, K N+1 ≤ N^C`, free `Cc Cx`; conclusion
`HighProb (Pg d) {ω | ∀ k ≤ K N, ∀ a, ‖(Σ_{j<min k τ} Uker 1 u_{j+1} u_k Zvec_{j+1} ω) a‖ < xZ … N k a}`
with `xZ = N^{δ/16}·√(4 Σ_{j<k} cZ k a j + N^{-Cx})` (line 835) -- exactly the amended threshold with the floor
inside the root. Fixed parameters precede the `HighProb` (i.e. `∀ D', ∀ᶠ N`).

Independent boundary check (attempted counterexamples):
- k = 0: the sum is over `range (min 0 τ) = ∅`, LHS `= 0`; `xZ 0 a = N^{δ/16}√(0 + N^{-Cx}) > 0` for `N ≥ 1`
  for every real `Cx` (`xZ_pos`). The event is true at k = 0; no `0 < 0` trap. The original defect is gone.
- Δ = 0 (`u N = s N`): `Zvec (j+1) = stepZ … = √Δ·lin(…) = 0` (`Zvec_succ_eq_zero_of_step`, via `simp [stepZ]`
  with `step = 0`), so every Uker image is 0 and every sum is 0 < xZ; the proof shows the complement is empty.
  True, not vacuous.
- Δ > 0, k ≥ 1: `Σ_{j<k} cZ ≥ ΔN^{-Cc} > 0`, `xZ² = N^{δ/8}(4Σ + N^{-Cx}) ≥ N^{δ/8}·4Σ`, per-(k,a) tail
  `≤ 4e^{-N^{δ/8}}`, union over `K·L² ≤ N^{C+2}` pairs, super-polynomial -> `HighProb` for all `D'`. Correct.
- Large/negative `Cc` or `Cx` only loosen the event; the consumer uses `Cc = Cx = 2D+2` (= the ticket's
  `C_x ≥ 2D+2`). No counterexample found.

Deterministic consequence `xZ_le_azumaMm` (line 1218): `∀ᶠ N, ∀ k ≤ K N, ∀ a, xZ ≤ azumaMm·(R_k²+1)·T_{u_k}(a)`
with explicit `azumaMm = N^{δ/16}√(4ξ²(2 qvSumConst N^{τ₁+δ/64}+2)+5)`, under `Cond272`, `2ε≤δ`, `60≤D`,
`Δ ≤ N^{-(D+10)}`, `2D ≤ Cc, Cx`; `azumaMm_le`: `Mm ≤ N^{δ/8}` for `τ₁ ≤ δ/32`. Matches the ticket's
"keep `x k a ≤ Mm (R_k²+1) T_{u_k}(a)`".

## (T4') `cheb_grid_at_tau` -- PASS

`CK D D₁ := D₁ + 2D + 80`, `gridK D D₁ N := max 1 ⌈N^{CK}⌉₊` (agrees with `⌈N^{C_K}⌉` for `N ≥ 1`; the `max 1`
only fixes `N = 0`). `C_K` is explicit and depends only on `D, D₁` (a fortiori only on `D, D₁, E, c`); it does
**not** depend on `δ` or on any good-set parameter. The eventual threshold in `N` depends on `E, s, t, c`
(through `etaT_inv_le_of_hreg`), not on `C_K`.
Statement (line 1730): fixed parameters, then `∀ D₁ > 0, ∀ᶠ N`, with `K = gridK D D₁`, `τ = gridTau … K`:
`Pg {ω | ∃ a, T_{u_{τω}}(a) ≤ ‖(Σ_{j<τω} Uker 1 u_{j+1} u_{τω} Yvec_{j+1} ω) a‖} ≤ N^{-D₁}` -- the ticket's
formula verbatim, at the single random target `u_τ`.
No union over k: the proof makes one call to `stopped_duhamel_cheb_tail` (GridDuhamelTail:448), whose only
union is over labels `b` (factor `L^n`, n = 2); its hypotheses are at the fixed target `t = u_K = u N` for
`j < K`, and `Σ_{j<K} e_j ≤ 2^{22}N^{19}Δ·(KΔ) ≤ 2^{22}N^{19}Δ`, giving `≤ 2^{26}N^{2D+21-CK} ≤ N^{-D₁}`.
Inputs (`stepY_ukerMat_eq_Uker_ae`, `Φgrid_bdd2`, row sum `≤ (1-u_{j+1})/(1-u N) ≤ η_t^{-1} ≤ N`,
`∫‖X‖⁴ ≤ 3·#Idx`, mean zero via `{j<τ} ∈ F_j`) are accepted T1504/T1505/T1511/T1516 results.
Boundary: `τω = 0` gives an empty sum, `0 < T`, consistent. Nondegenerate (Δ > 0 when `s N < u N`).

## (T6') `goodEvent_grid`, `goodEvent_grid_imp` -- PASS

`goodEventGrid` = (T3' event, ∀ k ≤ K) ∩ (∀ a, Y-sum at τ < T_{u_τ}(a), i.e. the (T4') event fails) ∩
(∀ k ≤ K, H_k ∈ G(u_k)) ∩ (T5 event) -- the ticket's four pieces.
`goodEvent_grid` (line 2005): step2's hypothesis list (`κ>0`, `|E|≤2-κ`, `hB : BoundsCore`, `hs0/hst/ht1`,
`Cond272`, `c>0`, gained hreg) + `0<δ≤c/24`, `60≤D`, positive good-set parameters, `s≤u≤t`; conclusion
`∀ D₁ > 0, ∀ᶠ N, Pg (goodEventGrid … (gridK D (D₁+1)) (2D+2) (2D+2) N)ᶜ ≤ N^{-D₁}`. K is chosen **after** D₁
(`gridK D (D₁+1)`), independent of ω. The HighProb pieces (T3', T1513 `highProb_grid_goodSet`, T5) are applied
with the polynomial K (`gridK_card_le`); only (T4') at `D₁+1` sets K; `2N^{-(D₁+1)} ≤ N^{-D₁}` for `N ≥ 2`.
`goodEvent_grid_imp` (line 2091): delivers, at `k = τ(ω)`, `hinit` (Mi = N^{δ/16}), `hZ` (Mm = azumaMm) and `hY`,
plus `J<thr ∧ H_j ∈ G` for `j < τω`, `H_j ∈ G` for `j ≤ K`, `J_0 < thr(u_0)`, and T1518 (T3)'s side conditions
`1 ≤ K`, `Δ ≤ N^{-(2D+76)}`, `0 ≤ Mm ≤ N^{δ/8}`. I compared with `grid_step_bound` in `main`'s
`GridStepBound.lean` (lines 784-795): the `hinit`, `hZ`, `hY` shapes match literally with `t := u`, `k := τ ω`.

## Vacuity / hidden hypotheses / cycles (item 3)

- `goodEvent_grid_params_witness` (compiled) satisfies all non-`BoundsCore` hypotheses jointly: `E = 0`,
  `s = 0`, `t N = 1-(N+1)^{-1/200}` (so `η_s/η_t = (N+1)^{1/200} → ∞`), `c = 1/4`, `δ = 1/96`, `D = 60`,
  `τ₁ = δ/32`, `ε = δ/2`, `u := t` with `s N < u N` for `N ≥ 1` (genuine window, Δ > 0). `BoundsCore` is step2's
  own (Step 1) hypothesis, not new. No structure field smuggles a hypothesis; no witness relies on an
  astronomically large quantity (`K = ⌈N^{C_K}⌉` is polynomial, as the amend explicitly permits).
- The good event is not vacuous: `goodEvent_grid` shows its complement has probability `≤ N^{-D₁} < 1`
  eventually, so it is eventually nonempty; `goodEvent_grid_imp` is therefore not a statement about ∅.
- No circular dependency (imports are merged upstream modules only).

## Notes for the dispatcher (non-blocking)

1. Paper delta not yet recorded (outside the repairer's file scope): on the grid, `K = ⌈N^{D₁+2D+80}⌉` depends
   on the target exponent `D₁`, and the remainder `Y` is controlled only at the stopping index by Chebyshev
   (polynomial rate). Suggested temporary tag `T1519a` in `docs/paper-deltas.md`.
2. Downstream (T1520 / R4c-2b) must take `K` from `gridK D (D₁+1)`, the grid used by `goodEvent_grid`.
3. Audit worktree left at `/Users/junyin/Lean_proof/RBM1D-wt/T1519-audit` (detached; no edits).
