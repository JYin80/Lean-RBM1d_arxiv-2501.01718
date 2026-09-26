Auditor model: claude-opus-5-5[1m]

# T1518 audit: grid `step_bound`, `phi_arith'`, `grid_thr_improve`

- Branch `t/T1518` @ `2299c17`. The diff against its base `db76845` adds one file: `RBM1D/Gauss/GridStepBound.lean` (1273 lines). No other file is touched, so no frozen signature is affected. `main` has since gained `e1905b6` (T1521, `Gauss/Steps12Gauss.lean`), which declares nothing in `RBM.Gauss.Grid`, so the names cannot clash.
- Fresh audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1518-audit` (detached at `2299c17`). This is not the prover's worktree. The build cache was an APFS clone, and the GridStepBound artifacts were absent before the build.
- Ticket: `docs/tickets/T1518.md`. Supervisor note: `docs/supervisor/2026-09-26-0048.md` §1, §1c, §1g, §3. Prove report: `docs/reports/T1518-prove.md`.

## Summary verdict
- (T1) `grid_step_bound`: **PASS**
- (T2) `phi_arith'`: **PASS**
- (T3) `grid_thr_improve` (+ `grid_phi_premises`): **PASS**
- Two statement differences are carried forward for the dispatcher (see "Deviations"). Neither is a defect.

## Build and axioms (run in the audit worktree)
- `lake build RBM1D.Gauss.GridStepBound`:
  - output `✔ [3911/3911] Built RBM1D.Gauss.GridStepBound`, `Build completed successfully (3911 jobs)`;
  - 0 errors, and no warnings in this file.
- `lake build RBM1D`: `Build completed successfully (9666 jobs)`, 0 errors. The root import is not yet on the branch; it is added at merge.
- Scratch file with `import RBM1D` + `import RBM1D.Gauss.GridStepBound` (tests coexistence with the root):
  - it elaborates;
  - `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for `grid_step_bound`, `grid_step_bound_core`, `phi_arith'`, `qGrid_le`, `grid_phi_premises`, `grid_thr_improve`, `rsum_le`, `drift_sum_le`, `stepErr_sum_le`, `jSMat_le_of_Agrid`.
- grep for `sorry` / `admit` / `axiom` / `native_decide` / `implemented_by` / `extern`: none.

## Math preflight
- The prove report §(a) contains a per-target preflight, (T1)/(T2)/(T3) all PASS, stamped 2026-09-26 10:13 UTC.
- The branch commit is 10:34:03 UTC, so the preflight was written before the Lean.

## (T1) `grid_step_bound` — PASS

### Statement vs ticket
- `hexp` is, character for character, the body of `grid_expansion_all'` (T1516, GridExpansion.lean:928) instantiated at `ω, k`:
  - term order: initial, Z, Y, `Δ•D`, R;
  - same `Uker … (u_{j+1}) (u_k)`.
- `hinit` is `Mi · T_{u_0}`.
- `hdrift` goes through `driftCoef`, which is literally `e·Λ(u)²·(36·(η_u⁻¹·A_u⁻¹) + W L W^{-D}) + Mg·(η_u⁻¹·(q_u + (A_u⁻¹)^{1/3}·Λ(u)³))` with `u = u_j`, times `T_{u_j}`. This is the ticket's heG shape.
- `qGrid = (4 N^ζ ℓ_u/ℓ_s)³ + 1`, as the ticket specifies.
- `hZ` is `Mm(R_k²+1)T_{u_k}`, `hY` is `T_{u_k}`, and `hRstep` is `stepErr(u_j,u_{j+1},Δ)` (T1506). All match.
- The conclusion `‖A_k a‖ ≤ phiG(u_k)·T_{u_k}(a)` is written out:
  - `phiG` is `Step2.phi` (Step2.lean:709) verbatim, except that `(ℓ_v/ℓ_s)²` is replaced by `qGrid`, plus `+ 1 + 1`;
  - I compared the two definitions term by term.
- Quantifier order: everything is fixed (`N`, `k ≤ K N`, `ω`). The statement is deterministic and pathwise.

### Drift weight: R²/m with η paired, not R³ (arithmetic redone)
- The η-pairing:
  - `η_{u_j}⁻¹ w_j² = (1-u_{j+1})² / (m(1-u_j)(1-u_k)²)`;
  - since `(1-u_{j+1})² ≤ (1-u_j)²`, this is `≤ (1-u_j)/(m(1-u_k)²) ≤ (1-s)/(m(1-u_k)²)`.
- The time sum: `Σ_{j<k} Δ(·) ≤ kΔ·(1-s)/(m(1-u_k)²) = (u_k-s)(1-s)/(m(1-u_k)²) ≤ (1-s)²/(m(1-u_k)²) = R_k²/m`.
  - By contrast, `sup_j η_{u_j}⁻¹ × length` would give `(1-s)R²/(m(1-u_k)) = R³/m`.
- In Lean:
  - `eta_inv_mul_weight_le` proves the pairing per term, directly on `(etaT E u_j)⁻¹ * ((1-u_{j+1})/(1-u_k))²`;
  - `drift_sum_le.hS1` sums it to `m⁻¹ R²`;
  - `hterm` keeps `η_{u_j}⁻¹` inside the sum; the monotone quantities `Λ`, `A⁻¹`, `A^{-1/3}`, `q` are moved to `u_k` via `thr_mono`, `scale_inv_mono`, `qGrid_mono`;
  - the ε-part uses `hS2 : Σ Δ w_j² ≤ R²`.
- The resulting coefficients `36 m⁻¹R²A⁻¹`, `R²ε`, `Mg m⁻¹R²(q + A^{-1/3}Λ³)` are exactly `Step2.phi`'s. There is no R³ anywhere.

### hFwd: enlarged r, not `_half`
- `rsum_le` sets `r j := if j < k then ((1-s)/(1-t))² · stepErr_j else 0`.
- `hR` holds because `C ≥ 1`.
- `hFwd` comes from `norm_Uker_fwd_le` → `norm_Uker_apply_le`, with row constant `1 + (u_k-u_{j+1})/(1-u_k) = (1-u_{j+1})/(1-u_k) ≤ (1-s)/(1-t)`. This gives `≤ C² stepErr_j = r_j ≤ 4 r_j`.
- The theorem applied is `stopped_duhamel_det_bound` (GridDuhamelTail.lean:662), which requires `ht1 : t < 1`. The `_half` variant (`:735`, `t ≤ 1/2`) is not referenced; the only occurrences of `_half` in the file are in comments.
- This matches supervisor §1c: the conclusion `4ⁿ Cⁿ Σ r_j` with n = 2 is `16 C² Σ stepErr_j`.

### C_R is explicit
- `stepErr_sum_le` gives `Σ_{j<k} stepErr_j ≤ 2¹⁷N¹⁵Δ^{1/2}`. It uses `stepErr_le_unif` with `δ' = 1-t`, `kΔ ≤ 1`, `Δ ≤ 1`, and `stepErrC_le`.
- `stepErrC_le` rests on the Lipschitz bounds `zMotionLip ≤ 48N⁷`, `zMotionZLip ≤ 192N⁷`, `driftLip ≤ 27648N¹⁴`, and `∫‖X‖ ≤ 1 + LW ≤ 2N`. All are proved from `η_t⁻¹ ≤ N` and `WL ≤ N`.
- `C = (1-s)/(1-t) ≤ η_t⁻¹ ≤ N`.
- So the R-sum is `≤ 2²¹N¹⁷Δ^{1/2} ≤ N³⁸·N^{-(D+38)} = N^{-D} ≤ W^{-D} ≤ T_{u_k}` under `hΔR : Δ ≤ N^{-(2D+76)}`, i.e. `C_R = 2D+76`.

### Initial term
- `Step2.norm_Uker_le_of_tail` from `u_0 = s` to `u_k`, with `flowScale_antitoneOn` and `etaT_ratio`, gives `Mi R² Ξ T_{u_k}`.

### Side hypotheses beyond the ticket's list
- `hW : e ≤ W` (as in `step_bound`), `hN2 : 2 ≤ N`, `hWL : W·L ≤ N`, `hηt : η_t⁻¹ ≤ N`, `hD0 : 0 ≤ D`, `hMi, hMg ≥ 0`, and the grid bookkeeping `0 ≤ s ≤ t < 1`, `1 ≤ K N`, `k ≤ K N`.
- All are deterministic, all are the ingredients the ticket names for `C_R`, and all are discharged in (T3).

### Vacuity, witness, boundary cases
- Compiled witness (end of file) for `grid_step_bound_core`:
  - parameters: `band Dims.example`, `N = 30` (`W = 10`, `L = 3`), `E = 0` (`m = 1`), `s = 0`, `t = 1/2`, `K = 30⁷⁶`, `k = 2`, `D = 0`, `Mi = Mg = Mm = 1`;
  - data: nonzero initial tail profile (`≠ 0` proved), drift vectors exactly at `driftCoef·T`, Z and Y exactly at their bounds (`Ys ≠ 0` proved), `Rv ≡ stepErr_j`, and `Ak` defined by the expansion identity;
  - every hypothesis is discharged, and the core theorem is applied.
- The witness uses `D = 0`. To exclude a `D`-degenerate loophole, I re-compiled the same witness in a scratch file with `D = 64` (the (T3) regime), `K = 30²⁰⁴`, `hΔR : Δ ≤ 30^{-204}`. It elaborates with no errors; a sanity-injected false line did produce an error.
- `K` is astronomically large only because the ticket mandates `Δ ≤ N^{-C_R}`. This is a grid-resolution requirement on a free parameter; no estimate is satisfiable merely because a quantity is huge.
- Abstract core vs genuine instance:
  - (T1) is the core specialised to `Agrid/Zvec/Yvec/Dgrid/Rgrid`;
  - `hexp` holds a.e. by `grid_expansion_all'` (T1516, merged);
  - `hinit`, `hdrift`, `hZ`, `hY` are good-event hypotheses on genuine random objects, supplied by R4c and T1515. They cannot be witnessed deterministically. This is the same pattern as `Step2.step_bound`, and it is acceptable here.
- Boundary cases:
  - `k = 0`: all sums empty;
  - `s = t`: `Δ = 0`, and `hΔR` is trivial;
  - `N = 0, 1` are excluded by `hN2`;
  - `t < 1` rules out a collapsed window, and `u_k → 1` is controlled by `hηt`.
- No circularity: all dependencies are merged (T1504, T1506, T1510, T1511, T1516, Step2/Step3).

## (T2) `phi_arith'` — PASS
- Hypotheses are identical to `Step2.phi_arith`, except `hq : q ≤ R^{(3:ℝ)/2}`.
- The conclusion is literally `… ≤ Step2.cStep m * x ^ 2 * R ^ 4`, with the same left-hand side as `phi_arith`.
- Arithmetic redone:
  - only term t4 changes: `Ξ·x m⁻¹R²q ≤ x·x m⁻¹R²·R^{3/2} = m⁻¹x²R^{7/2} ≤ m⁻¹x²R⁴`, because `R ≥ 1`;
  - Lean proves the slightly coarser `q ≤ R^{3/2} ≤ R²` (`rpow_le_rpow_of_exponent_le`), so t4 is `≤ m⁻¹x²R⁴` directly;
  - the constant budget `4 + e + (36e+2)/m` is unchanged. The t4 bound is the same `m⁻¹x²R⁴` that `phi_arith` used after `R³ ≤ R⁴`.
- The proof additionally handles `Ξ < 0` (not needed, but harmless).
- `qGrid_le`: `q_u ≤ 65 N^{3ζ} R_u^{3/2}` (`ζ ≥ 0`, `N ≥ 1`). It uses `Step3.ellHat_le_sqrt_mul` (`ℓ_u/ℓ_s ≤ √R`) and `64N^{3ζ}y³ + 1 ≤ 65N^{3ζ}R^{3/2}`. Correct.
- In (T3), the `65N^{3ζ}` factor is carried in the Mg slot through `65N^{3ζ}Mg ≤ x` and `q' = q/(65N^{3ζ}) ≤ R^{3/2}`, as the ticket requires.

## (T3) `grid_phi_premises`, `grid_thr_improve` — PASS
- Global hypotheses: `|E| < 2`, `0 ≤ s ≤ t < 1` for all N, `hreg` ((2.72) with gain `N^c`, the same form as `Step2.eventually_step_facts`), `0 < δ ≤ 1`, `24δ ≤ c`, `64 ≤ D`, `0 ≤ ζ`. The fixed parameters come before `∀ᶠ N`.
- Inside the `∀ᶠ N`, everything is uniform in `Mi, Mg, Mm`, `k ≤ K N` and `ω`.
- The premises are proved, not assumed. `grid_phi_premises` derives eventually:
  - `e ≤ W`, `1 ≤ x`, `cStep + 2 < x⁶`, `Ξ ≤ x`, `2 ≤ N`, `WL ≤ N` (`B.dim`), `η_t⁻¹ ≤ N` (T1511 `etaT_inv_le_of_hreg`);
  - for all `v ∈ [s N, t N]`: `x¹⁷R¹⁰ ≤ A_v`, `A_v^{-1/3}x²⁴R¹⁰ ≤ 1`, `εx¹⁷R¹⁰ ≤ 1`;
  - sources: `Step2.eventually_step_facts` (with `D ≥ 60`, implied by `D ≥ 64`) and `eventually_le_rpow`.
- Since `u_k ∈ [s,t]`, the scale premises apply at every grid time.
- What remains as hypotheses inside `∀ᶠ N`:
  - the random-layer constants `Mi, Mm ≤ x` and `65N^{3ζ}Mg ≤ x` (the ticket's intent);
  - `1 ≤ K N` and `hΔR` (the ticket says to add `hΔR` as a hypothesis);
  - (T1)'s random hypotheses.
- Arithmetic:
  - `jSMat ≤ phiG + 1` via `jSMat_le_of_Agrid` (`Step2.jStar_le` plus the index identity, which checks by `rfl`/unfold);
  - `phiG + 1 ≤ LHS(phi_arith') + 2 ≤ cStep x²R⁴ + 2`;
  - `cStep x²R⁴ + 2 ≤ (cStep+2)x²R⁴ < x⁶·x²R⁴ = x⁸R⁴ = thr(u_k)`, since `thr = N^δR⁴` and `N^δ = x⁸`. Checked.
- Satisfiability: the global hypotheses are those already used by the merged `step2`, plus `ζ ≥ 0` and `D ≥ 64`. The antecedents inside `∀ᶠ N` are satisfiable (e.g. `K N ≥ N^{2D+76}`, `Mg = 0` or `Mg ≤ x/(65N^{3ζ})`), and the random ones hold on the good event.

## Deviations for the dispatcher (not defects)
1. **`Φg` carries `+2`, not the ticket's `+1`.**
   - The ticket's own `hY` has coefficient `1`, so the Y-sum costs one `T_{u_k}` and the R-sum another.
   - With the ticket's hypotheses, `+1` does not follow from the five-term triangle inequality. `+2` is the correct consequence.
   - Downstream, (T3) reads `cStep x²R⁴ + 2 < Λ(u_k)`, and the threshold improvement is unaffected.
2. **Extra deterministic side hypotheses in (T1)** (`hηt`, `hWL : WL ≤ N` rather than `W ≤ N`, `hN2`, `hD0`, grid bookkeeping), and `C_R = 2D+76`. All are discharged in (T3).
3. **Paper-delta entry.** The prover proposes an entry tagged `T1518a` in its report §(d)4 but did not write it, because of the sole-writable-file rule. It should be appended to `docs/paper-deltas.md` at merge, covering: the grid step bound with `+2`, the `q_u` slot, and `Δ ≤ N^{-(2D+76)}`.

No `RETURN` items.
