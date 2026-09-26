Auditor model: claude-opus-5-5

# T1515 audit (amend-1 repair, option (d): the (5.54) residue confined to the near band)

- **Ticket:** `docs/tickets/T1515-amend-1.md`. It supersedes the (T1)/(T3)/(T4) details of `docs/tickets/T1515.md`.
- **Repair report:** `docs/reports/T1515-prove.md` (first line `Prover model: claude-opus-5-5`).
- **Branch and worktree:** `t/T1515` at `8081f0b`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1515`.
- **Prior audit:** BLOCKED at (T4), on the premise `L·ρ_j·W^D ≤ 1`. This report replaces it.
- **Audit date:** 2026-09-26, about 11:20 UTC.

## Overall verdict: PASS

| Target | Verdict |
|---|---|
| (R1) `eG_le'` | PASS |
| (R2) primed chain up to `eGpm_le_rhs535_of_jG_mat'` | PASS |
| (R3) `rhs535'_le_mul_tailT` (with `_near` and `DriftPt.resCoef_le`), explicit `D₀ = 8 + 2ζ` | PASS |
| (T2) `eGterm_eq_eGpm` | PASS (unchanged) |
| (T3′) `drift_point_le'`, `drift_point_le_blk'` | PASS: a generic-`J` conditional adapter, as (T3) was |
| (T4′) `drift_time_sum_le'`, `drift_time_sum_le_rescaled'` | PASS, with `e = 2` |
| (T5) `drift_point_le_heG` (+ `mgDrift_le`, `Dgrid_eq_drift`, `drift_point_le_heG_scalars`) | PASS: conditional on T1501's per-matrix inputs at `ℓ_s'`; see Notes N1 and N2 |

## 0. Process checks

- **Math preflight comes before the Lean.**
  - Report section (a) is stamped 2026-09-26 10:40 UTC. It gives a PASS for every target.
  - The first Lean commit of the repair is `b33539e` at 10:59 UTC, after the merge base `7ebd401` (10:06 UTC).
- **Scope of the diff.**
  - `git diff --stat main...t/T1515` lists only `RBM1D/Gauss/GridDriftPoint.lean` (+3237). The file is new relative to `main`.
  - Against the repair base, `git diff 7ebd401 8081f0b` gives +1974 / −5. All 5 removed lines are docstring lines.
  - The code of `eGterm_eq_eGpm`, `drift_point_le`, `quadGlue_pm_eq_eLL_mat` and `eGpm_le_rhs535_of_jG_mat` is unchanged. These are the parts that passed before.
- **Other files.** T1513 (`Gauss/GridGoodSet.lean`) has no diff against `main`, and neither does any other file. No frozen signature was touched.
- **Forbidden tokens.** `grep -nE "sorry|admit|^\s*axiom|native_decide|implemented_by|@\[extern"` on the file finds nothing.

## 1. Statement against the paper

Paper text used: `docs/claude-team/verify-d/paper-p56-62.txt`, pp. 59–61.
- (5.53)–(5.55) handle the near case `|a₁−a₂| ≤ ℓ*_u`. Within it:
  - (5.53) covers `|b−a₁| ≤ ℓ**_u`;
  - (5.54) covers the complementary `b`-range, and gives the negligible residue;
  - (5.55) closes the near case ("This implies that (5.35) holds for |a₁−a₂| ≤ ℓ*_u").
- The far case `|a₁−a₂| ≥ ℓ*_u` is (5.56)–(5.63). Every bound there carries `T_{u,D}(|a₁−a₂|)`, and there is no additive residue.
- So putting the residue only on the near band matches the paper's own bookkeeping. No new paper-delta is needed. T215a (entry 148) becomes "eliminated by (d)"; that edit is the dispatcher's.

### (R1) `eG_le'`: PASS

- **Hypotheses.** Compared token by token with `Lemma57.eG_le` (`Hierarchy/Lemma57.lean:1116`): same list, same order.
- **Conclusion.** It equals `eG_le`'s, except that the residue `κ₁(ℓ_uη_u)⁻¹Lρ` is multiplied by `if zdist(a₁−a₂) ≤ ellStar W ℓu then 1 else 0`.
- **Proof structure.** The proof splits on the indicator (`split_ifs`):
  - **near** (`d ≤ ℓ*_u`, equality included): uses `Lemma57.eG_near_le` together with the fact that the far bracket is `≥ 0`;
  - **far** (`d > ℓ*_u`): uses `Lemma57.eG_far_le` with `hd.le`, then `ring`. `h554` is not used, and neither `ρ` nor the residue appears; both are `·0`.
- The ticket's check "(R1)'s far branch has no residue" holds.

### (R2) primed chain: PASS

- **`eG_le_reduced_of_schwarz'`.** Same hypotheses as `Lemma57.eG_le_reduced_of_schwarz`. It applies `eG_le'` with `κ₁ = r` and `κ₂ = √r·A^{-1/2}`. `hD` turns `L√(W^{-D})/ℓ_u` into at most `A⁻¹`, which gives 169. The residue carries the indicator.
- **`eG_le_reduced'`.** Discharges (5.58) with the public `Lemma57.gloop_h558a'` and `gloop_h558b'`.
- **`eGpm_le_reduced'`.** Uses `EGDef.norm_eGpm_le` and `hκ`, then applies `eG_le_reduced'` at `(a₂, a₁)`.
- **`rhs535'`.** It is literally `Step2FarInputs.rhs535` (`Step2FarInputs.lean:994`) with the additive term `ℓu/ℓs·(ℓuηu)⁻¹·Lr·ρ` multiplied by `if d ≤ ellStar Wr ℓu then 1 else 0`. Also, `rhs535'_le_rhs535` holds.
- **`eGpm_le_rhs535'`.** Its hypothesis list is identical to the frozen `eGpm_le_rhs535` (`:1116`).
- **`eGpm_le_rhs535_of_jG_mat'`.** Its hypotheses are identical to those of the PASSed (T1). It takes `Gm := gmBlkM` and discharges `h560` with `norm_gloop_three_le_gmBlkM`, so no `h560` hypothesis remains.

### (R3) absorption arithmetic: PASS, explicit `D₀ = 8 + 2ζ`

**`rhs535'_le_mul_tailT_near`** (any `ρ ≥ 0`, no smallness hypothesis):
- On the near band, `Lemma57.inv_sq_le_tailT` gives `1 ≤ e^λ A² T(d)`, so the residue becomes `c_ρ · 1(near) · T(d)`, where `c_ρ = r(ℓη)⁻¹Lρ·e^λA²`.
- Off the band both sides are equal, closed by `ring`.

**`DriftPt.resCoef_le`.** I re-derived the chain by hand.
- Inserting `ρ ≤ 2η⁻¹JW^{-D}` and cancelling (`field_simp`): `c_ρ ≤ 2 (rℓ) L J e^λ W² W^{-D}`.
- Bound each factor:
  - `rℓ ≤ gℓ² ≤ 4W^{2ζ}W²`;
  - `L ≤ W`, `J ≤ W`;
  - `e^λ ≤ W` (`exp_log_rpow_le_self`: `W ≥ 8` gives `log W ≥ 1`, so `(log W)^{3/4} ≤ log W`).
- Collect powers: `c_ρ ≤ 8W^7·W^{2ζ−D} ≤ 8W^{-1} ≤ 1 ≤ η⁻¹`, using `D ≥ 8+2ζ` and `η ≤ 1`.
- Every step is correct.

**`rhs535'_le_mul_tailT`.** The residue enters the near slot as `(cNear r³ + 1)·1(near)`, exactly as the ticket asks. It uses T1513's `ρ` at the **same** `D`, and `D₀ = 8 + 2ζ` is explicit in the signature (`hD : 8 + 2 * ζ ≤ D`). The old `rhs535_le_mul_tailT` is kept; it is not frozen, since the file has never been merged.

### (T2): PASS (unchanged; byte-identical code)

### (T3′) `drift_point_le'` / `drift_point_le_blk'`: PASS

- **Hypotheses.** The signatures differ from `drift_point_le` / `drift_point_le_blk` only in the conclusion; I checked this with `diff`. There is no new hypothesis and no smallness assumption on `ρ`.
- **Coefficient.** `mdr'` is `mdr` with the `ρ`-piece `r(ℓη)⁻¹LρW^D` replaced by `c_ρ = r(ℓη)⁻¹Lρ e^λ A²`. Both indicators are coarsened to 1 (`coarsen_ind`), so `mdr'` does not depend on `b`.
- **Route.** The EG part goes through `eGpm_le_rhs535'`, i.e. through `rhs535'`. Nothing uses the old far-pair residue.
- **Status.** It stays a generic-`J` conditional adapter, like (T3).

### (T4′) `drift_time_sum_le'` / `drift_time_sum_le_rescaled'`: PASS, with `e = 2`

- **Per-time premises.** They are `1 ≤ J_j ≤ N^{2ε}thr(u_j)` and `ρ_j ≤ 2η_{u_j}⁻¹J_jW^{-D}`. This is exactly T1513's `rho554_le_two_mul_rpow` shape, at the same `D`.
  - The premise `LρW^D ≤ 1` is gone.
  - The premise `1 ≤ ℓ_s` is gone: `ℓ_s := ℓ_{sN}` is used directly.
  - `0 ≤ ρ_j` is not required.
- **Fixed parameters.** `drift_time_sum_le'` needs `D ≥ 8`; `drift_time_sum_le_rescaled'` needs `ζ ≥ 0` and `D ≥ 8+2ζ`.
  - In `drift_time_sum_le_of'` / `mdr'_mul_le`, `J ≤ W` is derived from `hreg`, via `J ≤ x²R⁴ ≤ x^{24}R^{30} ≤ A_t ≤ A_w ≤ W`.
- **Conclusions.**
  - `drift_time_sum_le'`: `driftSumConst E · N^κ · ((η_s/η_{u_k})² + 1)`, so the exponent is `e = 2`. The η-paired shape is kept: `Σ Δ·η_{u_j}⁻¹·((1−u_{j+1})/(1−u_k))²`, then `R²/m`.
  - `drift_time_sum_le_rescaled'`: `driftSumConst E · (4N^ζ)³ · N^κ · (R² + 1)`.
- **Constant.** Inside the bracket the constant is `274·N^κ`, because the `ρ`-piece is the `+1` inside `170 = 169 + 1`. REFEREE-d's 275 counts the `ρ`-piece separately. Both fit under 300, so there is no discrepancy in the stated constant.
- **Old theorem.** `drift_time_sum_le`'s docstring now says "Superseded by (T4′) `drift_time_sum_le'`; its `LρW^D ≤ 1` premise is unsatisfiable with T1513's ρ", as the ticket requires.

### (T5) `drift_point_le_heG`: PASS

**Conclusion against T1518 (T1) `hdrift`** (ticket text: `(exp 1·Λ²·(36η⁻¹A⁻¹+ε) + Mg·η⁻¹·(q_u + A^{-1/3}Λ³))·T_u(b)`):
- `Λ = Step2.thr E s δ N u` and `A = B.scale E N u`;
- `ε = W·L·W^{-D}`;
- `q_u = (4N^ζ·(ℓ_u/ℓ_{sN}))³ + 1`;
- `Mg = mgDrift B ζ N`;
- `T_u(b) = Step2.tT B E N D u (zdist(b 0 − b 1))`.

This matches the ticket formula term for term.

**Choice of `ℓ_s` in `q_u`.** The merged T1518 (`main`, `Gauss/GridStepBound.lean:55`) defines `qGrid B s ζ N u = (4*N^ζ*B.ell N u / B.ell N (s N))^3 + 1`, i.e. `ℓ_s = ℓ_{sN} = B.ell N (s N)`. This is the same choice the prover made. The prover's remark that T1518 "does not name it" refers to the ticket text only; T1518's Lean agrees with the prover's choice.

**Lean form against the merged `driftCoef`.** The merged `driftCoef` differs from (T5)'s coefficient only by associativity: `Mg * (η⁻¹ * (…))` against `Mg * η⁻¹ * (…)`, and `4N^ζ·ℓ_u/ℓ_s` against `4N^ζ·(ℓ_u/ℓ_s)`. I compiled the equality `coef_eq` (see section 4); it is `unfold driftCoef qGrid; ring`. The left side of (T5) is `Dgrid` by `Dgrid_eq_drift` (`rfl`), and the matrix `H B.toDims s t K N j ω` is Hermitian by `H_isHermitian`. So T1518's `hdrift` follows from (T5) by a one-line rewrite (Note N1).

**How `h554` is supplied.** `h554` is derived inside the proof, not assumed:
- `mem_h554Set_of_isHermitian` gives it with `ρ = rho554(jGMat M)`; it needs `1 ≤ log W`, which follows from `W ≥ 8`;
- then `ρ ≤ rho554(N^{2ε}Λ) ≤ 2η⁻¹N^{2ε}ΛW^{-D}`, by `rho554_mono` and `rho554_le_two_mul_rpow` with `hlog : 2D² ≤ log W` and `1 ≤ A_u`;
- `h531` and `h42` come from `hjG` through the `jGMat` corollaries.

**`Mg` bound.** `mgDrift_le` gives, for every `κ > 0` and `ζ ≥ 0`, eventually `mgDrift ≤ 2752·N^{κ+3ζ}`; in fact the proof gives `N^{κ+2ζ}`. The bound is explicit, and `Mg` depends only on `(B, ζ, N)`.

**Conditionality.** (T5) is conditional on T1501's per-matrix inputs at `ℓ_s' = ℓ_{sN}/(4N^ζ)`: `h273`, `h557C`, `h557R`, `hone`, `hκ`. R4c must supply these from T1513's `goodSet`. As the prover's report says, this is a conditional adapter at the level of these inputs. It is not a special case: `N`, `u ∈ [sN, 1)`, `D`, `E` and `M` are all general.

## 2. Vacuity, hidden hypotheses, cycles

- **Hidden hypotheses.** None. No structure fields are used. `mgDrift` and `mdr'` are plain definitions.
- **`hjS`.** It is stated against `jSMat`, which is `RBM.Step2.jStar` (`GridJStar.lean:121`). It is not `EarlyQVRateEv.jStar`.
- **Excluded dependencies.** Nothing uses `eGpm_le_rhs535_of_jS`, `EarlyQVRateEv`, or an assumed `h560`: in the `_blk'` chain, `h560` is discharged.
- **Copied T1513 private lemmas** (DECISIONS §10b question). The copies are:
  - `one_le_jGMat'`;
  - `gmBlkM_mul_swap_le_gsqBlkM`;
  - `gsqBlkM_le_jGMat_mul_tailT`;
  - plus the definition `gsqBlkM`, identified with T1513's `jGMat` body by `jGMat_eq := rfl`.

  They depend only on `jGMat`, `gmBlkM` (a `Gsig` block maximum), `SB` and `tailT`. They are deterministic, fixed-matrix facts.
  - They do not depend on `jStar`, `EarlyQVRateEv.jStar`, `h560` or `eGpm_le_rhs535_of_jS`.
  - T1513 is a merged true-path ticket, not an A′ result, so §10b's A′-reuse restriction does not even apply. Even if it did, these would qualify as deterministic.
  - The copies are reported as such in the report. **No violation.**
- **Other A′-era dependencies.** These are `APrimeJG.norm_Gsig_eq_green_or_swap` and `gmBlk_*`. They sit in the previously PASSed (T1) part, are deterministic, and are unchanged.
- **Cycles.** None: the new file imports only merged modules, `GridGoodSet` (T1513) and `GridExpansion` (T1516).
- **Loopholes** (`N = 0`, empty index set, collapsed window, astronomically large quantity):
  - (T5) assumes `1 ≤ N` and `0 ≤ sN ≤ u < 1`;
  - `B.L N ≥ 3` (`B.three_le_L`), so the index set is not empty;
  - the absorption uses only `W ≥ 8` and `D ≥ 8+2ζ`, not a large free constant;
  - `J ≤ W` is proved, not assumed. In (T4′) it comes from `hreg`; in (T5) from `hJA` together with `A_u ≤ W` (`scale_le_W`).

## 3. Boundary cases

- **`d = ℓ*_u`.** This counts as near, because the indicator is `d ≤ ellStar`. There `rhs535' = rhs535`; I compiled this example.
  - `eG_le'` uses `eG_near_le` there, whose hypothesis is `d ≤ ℓ*`.
  - `inv_sq_le_tailT` also needs only `d ≤ ℓ*`.
- **`d > ℓ*_u` (far band).** `rhs535'` equals exactly `η⁻¹(cFar(…) + 169(…))·T(d)`, with no residue and no near term; I compiled this example with `simp [not_le.2 hd]`. `eG_le'`'s far branch uses `eG_far_le` with `ℓ* ≤ d`.
- **`ρ = 0`.** It is admissible everywhere: `hρ0 : 0 ≤ ρ`, and (T4′) needs no lower bound. The bounds simply lose the residue term.
- **`u → 1`.** The bounds hold for every `u < 1`; `η_u > 0` by `etaT_pos_of_lt_one'`.

## 4. Satisfiability witnesses (compiled by the auditor)

I wrote a scratch file, `AuditT1515.lean`, outside the repo in the session scratchpad, and ran it with `lake env lean` in the worktree. It gave no errors and no warnings.

1. **`joint_scalar_witness`** (for every band `B`). There exist `E, s, t, c, δ, ε, ζ = 1, D` with:
   - `|E| < 2`;
   - a genuine window `s N < t N` for `N ≥ 1`, `t N < 1`;
   - `hreg` holding eventually;
   - `0 < δ ≤ c/24`, `0 ≤ ε`, `2ε ≤ δ`;
   - `0 < ζ` and `8 + 2ζ ≤ D` (`D ≥ 60`);
   - and, eventually in `N`, all scalar premises of (T5): `1 ≤ N`, `8 ≤ W`, `L ≤ W`, `N ≤ W²`, `2D² ≤ log W`, `sN < tN`, and uniformly for `u ∈ [sN, tN]` both `N^{2ε}thr(u) ≤ A_u` and `hDreg`.

   Source: T1508's merged `qv_time_sum_le_hyps_witness` (`E = 0`, `s = 0`, `t N = 1 − (N+1)^{-1/200}`, `ε = δ/2 > 0`) combined with the prover's `drift_point_le_heG_scalars`. The witness is not degenerate: `N` goes to infinity, the window is non-empty, `ε > 0` and `ζ > 0`. The same data covers the fixed-parameter premises of (T4′) and (T4′)-rescaled.
2. **`rho_premise_from_T1513`.** On the good event `jGMat M ≤ J`, T1513's actual producer `rho554(jGMat M)` satisfies (T4′)'s per-time premise `ρ ≤ 2η⁻¹JW^{-D}`, given `1 ≤ A_u` and `2D² ≤ log W`. So (T4′) is compatible with the real `h554` producer, not only with the prover's extreme witness `drift_time_sum_inputs_witness'` (`J = N^{2ε}thr`, `ρ = 2η⁻¹JW^{-D} > 0`). That witness also compiles and is not degenerate.
3. **`coef_eq`.** (T5)'s coefficient equals a verbatim copy of T1518's merged `driftCoef B E s δ D ζ (mgDrift B ζ N) N u` (and `qGrid`), by `unfold; ring`.
4. **Per-matrix inputs of (T5)/(T3′).** `h273`, `h557C/R`, `hone`/`hκ` at `ℓ_s'`, `hjS`, `hjG`: these are membership in T1513's `goodSet` components (`eq273Set`, `eq557Set`, `honeSet`, `qvSet ∩ jgSet`).
   - They are unchanged from (T3), apart from the weaker scale `ℓ_s'`, and are not new hypotheses of this repair.
   - `honeSet`'s `κ = 2N^{ζCtr}ℓ_u/ℓ_s` gives `hκ` whenever `ζCtr ≤ ζ`.
   - A compiled witness for a concrete matrix is not provided; it is R4c's responsibility. This is recorded as the conditional-adapter status, not as a defect.

## 5. Build and axioms (run by the auditor)

- `cd /Users/junyin/Lean_proof/RBM1D-wt/T1515 && lake build RBM1D.Gauss.GridDriftPoint` gives `Build completed successfully (3951 jobs).` No error lines, and no warning lines from `GridDriftPoint.lean`.
- `lake build RBM1D` in the worktree gives `Build completed successfully (9666 jobs).` The branch's root does not import the new module yet; the root import is added at merge.
- **Merge safety.** `main` has moved on (T1518 `GridStepBound`, T1520 `GridBootstrap`, T1521 `Steps12Gauss`). None of the 67 declaration names of `GridDriftPoint.lean` occurs in those files, so no name clash is expected at merge.
- **Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of the following:
  - (R1)–(R3): `eG_le'`, `eG_le_reduced_of_schwarz'`, `eG_le_reduced'`, `eGpm_le_reduced'`, `rhs535'_le_rhs535`, `eGpm_le_rhs535'`, `eGpm_le_rhs535_of_jG_mat'`, `rhs535'_le_mul_tailT_near`, `DriftPt.resCoef_le`, `rhs535'_le_mul_tailT`;
  - (T3′), (T4′): `drift_point_le'`, `drift_point_le_blk'`, `drift_time_sum_le_of'`, `drift_time_sum_le_scale'`, `drift_time_sum_le'`, `drift_time_sum_le_rescaled'`, `drift_time_sum_inputs_witness'`;
  - (T5) and the `jGMat` corollaries: `DriftPt.one_le_jGMat'`, `DriftPt.two_loop_re_le_jGMat`, `DriftPt.gmBlkM_le_sqrt_jGMat`, `mgDrift_le`, `drift_point_le_heG`, `Dgrid_eq_drift`, `drift_point_le_heG_scalars`;
  - kept from before: `eGterm_eq_eGpm`, `drift_time_sum_le`;
  - the auditor's own lemmas: `coef_eq`, `joint_scalar_witness`, `rho_premise_from_T1513`.

## 6. Notes (none blocks the PASS)

- **N1 (T5 against the merged `driftCoef`).** They agree only up to `ring` (associativity). At the R4c or merge stage, feeding (T5) into `grid_step_bound`'s `hdrift` needs `rw [Dgrid_eq_drift]` plus `unfold driftCoef qGrid; ring`, as in the auditor's `coef_eq`. A one-line corollary stated directly in `driftCoef` form could be added when R4c is written. The prover could not see `driftCoef`: T1518 merged at 10:40 UTC, after the branch base `7ebd401`.
- **N2 (exponent budget downstream).** T1518's `grid_step_bound` needs `65·N^{3ζ}·Mg ≤ N^{δ/8}`.
  - With `mgDrift ≤ 2752·N^{κ+2ζ}` (what the proof gives), this needs `κ + 5ζ < δ/8`, **strictly**, so that the constant `65·2752` is absorbed.
  - With the stated `N^{κ+3ζ}` it needs `κ + 6ζ < δ/8`.
  - The supervisor's "`κ, ζ ≤ δ/48`" sits exactly at the boundary for the stated form. R4c should take `ζ ≤ δ/48` and `κ < δ/48` strictly, or use the sharper `N^{κ+2ζ}`.
  - This is a note for the dispatcher and R4c. It is not a T1515 defect.
- **N3 (paper-deltas).** No new entry is needed. T215a (entry 148) should be marked "eliminated by (d)" (dispatcher).
