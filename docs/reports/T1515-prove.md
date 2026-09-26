Prover model: claude-opus-5-5

# T1515 (amend-1): the (5.54) residue confined to the near band; (R1)-(R3), (T3'), (T4'), (T5)

Ticket: `docs/tickets/T1515-amend-1.md` (supersedes the (T1)/(T3)/(T4) details of
`docs/tickets/T1515.md`). Returning audit: `docs/reports/T1515-audit.md` (BLOCKED at (T4): the
premise `L·ρ_j·W^D ≤ 1` cannot hold with T1513's `rho554` at the same `D`). Worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1515`, branch `t/T1515`, starting from `7ebd401` (current `main`
already merged in; T1513, T1514, T1516, T1517 available). Sole writable file
`RBM1D/Gauss/GridDriftPoint.lean`. Repairer, dispatcher-authorized option (d)
(`docs/claude-team/verify-d/REFEREE-d.md`). This is a restart of a stopped instance that had
written no Lean. This report replaces the previous one in place.

## (a) Math preflight (written 2026-09-26 10:40 UTC, before any Lean of this repair)

### Audit defect addressed

The re-audit's only blocking defect is (T4)'s premise `L ρ_j W^D ≤ 1`. With T1513's
`ρ = rho554(J) ≥ η⁻¹ W^{-D}` it forces `L η⁻¹ ≤ 1`, which is false. The defect comes from
upstream:
- `Lemma57.eG_le` adds the (5.54) residue `κ₁ (ℓ_u η_u)⁻¹ L ρ` on **both** branches.
- Its far branch (`eG_far_le`) never uses `h554` or `ρ`; its signature has neither.
- `rhs535` inherited the far-pair residue, and `rhs535_le_mul_tailT` absorbed it against the floor
  `T ≥ W^{-D}`, at the cost of a factor `W^D`.

Fix (d):
- multiply the residue by the near indicator `ind := 1(d ≤ ℓ*_u)`;
- absorb it on the near band against `T_{u,D}(d) ≥ A_u⁻² e^{-λ}`, `λ = (log W)^{3/4}`
  (`Lemma57.inv_sq_le_tailT`), at the cost of `A_u² e^λ` instead of `W^D`.

### Paper check

- Paper p.59: "consider first `|a₁-a₂| ≤ ℓ*_u`". There (5.53) handles `|b-a₁| ≤ ℓ**_u`, (5.54) the
  complementary `b`-range, and (5.55) closes the near case.
- The far case `|a₁-a₂| ≥ ℓ*_u` uses (5.56)-(5.63), all multiplied by `T_{u,D}(|a₁-a₂|)`, with no
  additive residue.
- So `rhs535'` follows the paper's bookkeeping, and no new paper-delta is needed. T215a
  (entry 148) becomes "eliminated by (d)"; that edit is the dispatcher's.

### (R1) `eG_le'`: PASS

- **Statement.** Hypotheses literally those of `Lemma57.eG_le`. The conclusion is `eG_le`'s,
  with the residue `κ₁(ℓη)⁻¹Lρ` multiplied by `ind`.
- **Near branch (`ind = 1`).** `eG_near_le` gives `EG ≤ η⁻¹κ₁ cNear r² T + κ₁(ℓη)⁻¹Lρ`. The far
  bracket is `≥ 0`, so adding it keeps the bound.
- **Far branch (`ind = 0`).** `eG_far_le` gives `EG ≤ η⁻¹κ₁(cFar Jκ₂ + J^{3/2}(…))T`. The near term
  and the residue are both multiplied by `0`, and `h554` is not used.
- **Boundary.** `d = ℓ*_u` counts as near, as in `eG_le` and `eG_near_le`.
- **Dependencies** (public, merged): `Lemma57.eG_near_le`, `Lemma57.eG_far_le`,
  `cNear_nonneg`, `cFar_nonneg`.

### (R2) The primed chain: PASS

1. `eG_le_reduced_of_schwarz'`: the proof of `Lemma57.eG_le_reduced_of_schwarz`, re-run on
   `eG_le'`, with `κ₁ = r`, `κ₂ = √r A^{-1/2}`, and `hD` giving `L√(W^{-D})/ℓ_u ≤ A⁻¹`. The residue
   `r(ℓη)⁻¹Lρ·ind` passes through unchanged.
2. `eG_le_reduced'` (gloop form): (5.58) is discharged by the public `Lemma57.gloop_h558a'` and
   `gloop_h558b'`.
3. `eGpm_le_reduced'`: the public `EGDef.norm_eGpm_le` plus `hκ` give `hEG`; then
   `eG_le_reduced'` is applied at `(a₂, a₁)`.
4. `rhs535' Wr Lr ℓu ℓs ηu D J ρ d` is `rhs535` with its additive term `ℓu/ℓs·(ℓuηu)⁻¹·Lr·ρ`
   multiplied by `if d ≤ ellStar Wr ℓu then 1 else 0`.
5. `eGpm_le_rhs535'` is the frozen `eGpm_le_rhs535`'s statement with `rhs535'` in place of `rhs535`.
6. `eGpm_le_rhs535_of_jG_mat'` has the same hypotheses as the PASSed (T1): `Gm := gmBlkM`, and
   `h560` discharged by `norm_gloop_three_le_gmBlkM`.

All primed lemmas live in `RBM.Gauss.Grid`, the sole writable file. No private lemma is needed
for (R1)/(R2).

### (R3) `rhs535'_le_mul_tailT` and the absorption arithmetic: PASS

**(i) Generic step, any `ρ ≥ 0`, no smallness hypothesis** (`rhs535'_le_mul_tailT_near`).
- On `ind = 1`, `inv_sq_le_tailT` (which needs only `W ≥ 1`, `ℓ_u > 0`, `d ≤ ℓ*_u`) gives
  `1 ≤ A² e^λ T(d)`.
- Hence `rhs535' ≤ (η⁻¹(cNear r³ ind + cFar r^{3/2}A^{-1/2}J + 169 r A⁻¹J^{3/2}) + c_ρ·ind)·T(d)`,
  with `c_ρ := r (ℓ_u η_u)⁻¹ L ρ · (e^λ A²)`.
- On `ind = 0` the residue is `0`.

**(ii) Absorption, a scalar lemma** (`DriftPt.resCoef_le`).
- Hypotheses:
  - `8 ≤ W`, `0 < ℓ_u`, `0 < ℓ_s`, `0 < η ≤ 1`;
  - `0 ≤ ρ ≤ 2η⁻¹JW^{-D}` (T1513's `rho554_le_two_mul_rpow`, at the **same** `D`);
  - `0 ≤ J ≤ W`, `ℓ_u ≤ L ≤ W`;
  - `r ≤ g ℓ_u` with `0 ≤ g ≤ 4W^{2ζ}`, `0 ≤ ζ`;
  - `D ≥ D₀ := 8 + 2ζ`.
- Derivation. Since `(ℓη)⁻¹ (Wℓη)² = W²ℓη`, and using `η⁻¹ · η = 1`,
  `c_ρ ≤ r L · 2η⁻¹JW^{-D} · W²ℓη · e^λ = 2 (rℓ) L J e^λ W^{2-D}`.
- Estimate each factor:
  - `rℓ ≤ gℓ² ≤ 4W^{2ζ}W²`;
  - `L ≤ W`, `J ≤ W`;
  - `e^λ ≤ W`, because `log W ≥ 1` gives `(log W)^{3/4} ≤ log W`.
- Hence `c_ρ ≤ 8 W^{2ζ+7-D} ≤ 8W^{-1} ≤ 1 ≤ η⁻¹`.
- So `rhs535' ≤ η⁻¹((cNear r³ + 1)·ind + cFar(…) + 169(…))·T(d)`: the residue moves into the near
  slot as `+1`, as the ticket asks.

**(iii) Where the scalar hypotheses come from.**
- `r ≤ gℓ_u`:
  - with `ℓ_s = ℓ_{sN} ≥ 1`, take `g = 1`, and `1 ≤ 4W^0`;
  - with `ℓ_s' = ℓ_{sN}/(4N^ζ)`, take `g = 4N^ζ ≤ 4W^{2ζ}` (`N ≤ W²`).
- `L ≤ W`: from `WL ≤ N ≤ W²`.
- `η ≤ 1`: `η = (1-u) Im m`.
- `J ≤ W`:
  - in (T4') it follows from `J ≤ x²R_w⁴ ≤ x^{24}R_w^{30} ≤ A_w` (`hreg`) and `A_w = Wℓ_wη_w ≤ W`,
    because `ℓ_w√(1-w) = min(1, L√(1-w)) ≤ 1` and `m ≤ 1`;
  - in (T5) it is the stated premise `J ≤ A_u`.
- The constants match REFEREE-d Q3 (`D₀ = 8`, and `8 + 2ζ` with `ℓ_s'`). The project uses `D ≥ 60`.

### (T2): PASS (unchanged, kept byte-identical)

### (T3') `drift_point_le'` (+ `drift_point_le_blk'`): PASS

- (T3) with `rhs535'`. The hypotheses are exactly those of `drift_point_le` (generic `J`, `Gm`,
  `h560`, `hGm`), resp. of `drift_point_le_blk` (`Gm := gmBlkM`). **No new hypothesis.**
- The coefficient `mdr'` is `mdr` with the `ρ`-piece `r(ℓη)⁻¹LρW^D` replaced by
  `c_ρ = r(ℓη)⁻¹Lρ(e^λA²)`.
- Both indicators are coarsened to `1`, so `mdr'` does not depend on `b`.
- The quadratic part is unchanged.

### (T4') `drift_time_sum_le'` and `drift_time_sum_le_rescaled'`: PASS

**Per-time inputs** (for `j < k`):
- `1 ≤ J_j ≤ N^{2ε} thr(u_j)`;
- `0 ≤ ρ_j ≤ 2 η_{u_j}⁻¹ J_j W^{-D}`, exactly T1513's output shape.

**Fixed parameters:** `D ≥ 8`, resp. `ζ ≥ 0` and `D ≥ 8 + 2ζ`. There is no `LρW^D ≤ 1` and no
`hℓs1`.

**Per-summand bound** (`DriftPt.mdr'_core`, `mdr'_mul_le`), with `g ≥ 1`, `r := ℓ_w/ℓ_s`,
`r√a ≤ g√c₀`, and `ρ̃ := r/g` (so `ρ̃² ≤ R_w`, `ρ̃ ≤ R_w`):
- near: `η_w⁻¹ cNear r³ p ≤ g³ cNear c₀^{3/2}/(m b² √a)`, from `r²a ≤ g²c₀`, `r√a ≤ g√c₀` and the
  pairing `η_w⁻¹ p ≤ a/(mb²)`; then telescoped (`Σ Δ/√(1-u_j) ≤ 2√c₀`);
- far `cFar`: `r³J² ≤ g³A ≤ (g³)²A`, hence `r√rA^{-1/2}J ≤ g³`;
- far `169`: `rJ² ≤ gA`, hence `≤ 169g`;
- `ρ`-piece: `c_ρ ≤ η_w⁻¹` by (R3)(ii), then the pairing gives `≤ a/(mb²)`;
- quadratic pieces unchanged.

**Sum:** `≤ g³(2cNear + cFar + 170 + 36e) m⁻¹ R² + e(WL)²W^{-D}`.
- **Exponent `e = 2`.** Every `η_{u_j}⁻¹` stays paired with its own propagator factor.
- For `g = 1`: `≤ (300/m) N^κ (R² + 1)`. The internal bracket stays `274·N^κ`; REFEREE-d's `275`
  counts the `ρ`-piece separately. Both fit `300`.
- For `g = 4N^ζ`: `≤ (300/m)(4N^ζ)³ N^κ (R² + 1) = 64·(300/m) N^{κ+3ζ}(R² + 1)`.

**Satisfiability.**
- The extreme choice `J_j = N^{2ε}thr(u_j)`, `ρ_j = 2η_{u_j}⁻¹J_jW^{-D} > 0` satisfies the
  per-time premises (compiled witness).
- The fixed-parameter premises `hreg`, `δ ≤ c/24`, `2ε ≤ δ`, `D ≥ 60` are T1508's merged
  `qv_time_sum_le_hyps_witness` (cited).

### (T5) `drift_point_le_heG`: PASS

**Target** (T1518 (T1) `hdrift`, literally):
`‖D b‖ ≤ (exp 1·Λ²·(36 η⁻¹A⁻¹ + WLW^{-D}) + Mg·η⁻¹·(q_u + A^{-1/3}Λ³))·T_u(b)`, where
- `Λ = thr E s δ N u`, `A = B.scale E N u`;
- `q_u = (4N^ζ·(ℓ_u/ℓ_{sN}))³ + 1`;
- `T_u(b) = tT B E N D u (zdist(b 0 - b 1))`;
- `A^{-1/3}` is written `A⁻¹ ^ ((1:ℝ)/3)`, the spelling of `Lemma57.inv_sqrt_le_rpow_third`;
- the left side is written with `List.ofFn b`, as in `Dgrid`.

**Route.**
1. Apply (T3') with `ℓ_s' := ℓ_{sN}/(4N^ζ)`, so that `r' = 4N^ζ r`.
2. Take `J := N^{2ε} Λ ≥ 1`.
3. Get `h531`/`h42` from `jGMat(M) ≤ J` by a matrix-level `jGMat` corollary. T1513's
   `gsqBlkMat`/`gmBlkMat` and their lemmas are `private`, so I define `gsqBlkM` with the same body,
   prove `jGMat = 1 + sup'(gsqBlkM/T)` by `rfl`, and copy the short proofs (reported as copies).
4. Take `ρ := rho554(jGMat M)`. `h554` holds for **every** Hermitian `M`
   (`mem_h554Set_of_isHermitian`, which needs `1 ≤ log W`). Then
   `ρ ≤ rho554(J) ≤ 2η⁻¹JW^{-D}` (`rho554_mono`, `rho554_le_two_mul_rpow`, which need
   `2D² ≤ log W` and `1 ≤ A`).

**Coefficient bound.** Let `g = 4N^ζ`, `r = ℓ_u/ℓ_{sN} ≥ 1`, `r² ≤ R` (`ell_mul_sqrt_le`),
`Λ = xR⁴`, `x = N^δ`, `J ≤ N^{2ε}Λ ≤ xΛ`.
- near plus residue: `cNear(W,ℓ_u) r'³ + 1 ≤ (cNear(W,1) + 1) q_u` (`c_ρ ≤ η⁻¹` by (R3));
- `cFar` piece:
  - `r'√r' ≤ g² r√r` and `A^{-1/2} ≤ A^{-1/3}`;
  - `(r√rJ)² = r³J² ≤ R²x²Λ² ≤ Λ⁶`, since `R²x² ≤ Λ⁴ = x⁴R^{16}`;
- `169` piece:
  - `r' ≤ g² r` and `A⁻¹ ≤ A^{-1/3}`;
  - `(rJ√J)² = r²J³ ≤ Rx³Λ³ ≤ Λ⁶`, since `Rx³ ≤ Λ³`.

**Constant.** `Mg := (4N^ζ)²(cNear(W,1) + cFar(W,1) + 170)` depends only on `N`, `W` and `ζ`, not
on `u`, `M` or `b`. Eventually `cNear(W,1), cFar(W,1) ≤ N^κ`, so
`Mg ≤ 2752 N^{κ+2ζ} ≤ 2752 N^{κ+3ζ}` (compiled lemma).

**Scalar premises of (T5):**
- `|E| < 2`, `1 ≤ N`, `0 ≤ s N ≤ u < 1`;
- `0 ≤ δ`, `2ε ≤ δ`, `0 ≤ ζ`, `8 + 2ζ ≤ D`;
- `8 ≤ W`, `L ≤ W`, `N ≤ W²`, `2D² ≤ log W`;
- `1 ≤ A_u`, `N^{2ε}Λ ≤ A_u`;
- `hD : L√(W^{-D}) ≤ ℓ_u A⁻¹`.

All of these hold eventually, uniformly in `u ∈ [s N, t N]`, under `hreg` at `t` with `24δ ≤ c`,
`D ≥ 8 + 2ζ` (compiled lemma planned):
- `A_u ≥ A_t ≥ x^{24}R_t^{30} ≥ x²R_u⁴·N^{2ε}/N^{δ}` gives `N^{2ε}Λ ≤ A_u`, and also `1 ≤ A_u`;
- `hD` needs only `D ≥ 4`, `L ≤ W` and `η ≤ 1`.

**Per-matrix premises** of (T3') (`h273`, `h557C/R`, `hone`/`hκ`, at `ℓ_s'`) remain hypotheses;
R4c supplies them from T1513's `goodSet`. `jSMat ≤ Λ` and `jGMat ≤ N^{2ε}Λ` are the good-event
bounds. A grid corollary states the same with `Dgrid B E s T K N j ω b` on the left.

**Caveat.** (T5) is conditional on those per-matrix premises. It is the general-`N`, general-`u`,
general-`D` statement, not a special case.

### Verdict of preflight

(R1) PASS, (R2) PASS, (R3) PASS (explicit `D₀ = 8 + 2ζ`), (T2) PASS (unchanged), (T3') PASS,
(T4') PASS (`e = 2`), (T5) PASS.

## (b) Declarations, build, axioms (written 2026-09-26 11:13 UTC)

- **Branch and commits.** Branch `t/T1515`: `7ebd401` (merge of main), then `b33539e`,
  `1947bc6`, `b000ee2`, `304d304` (WIP) and the final commit `8081f0b`.
- **Scope.** `git diff --stat 7ebd401` lists only `RBM1D/Gauss/GridDriftPoint.lean`
  (+1974 / −5). The 5 removed lines are docstring lines only. T1513 and every frozen file are
  untouched.
- **Imports added:** `RBM1D.Gauss.GridGoodSet` (T1513: `jGMat`, `rho554`, `mem_h554Set_…`) and
  `RBM1D.Gauss.GridExpansion` (T1516: `Dgrid`). Both are merged.

All new declarations are in `namespace RBM.Gauss.Grid`, file
`/Users/junyin/Lean_proof/RBM1D-wt/T1515/RBM1D/Gauss/GridDriftPoint.lean`.

**(R1)**
- `eG_le'`: same hypotheses as `Lemma57.eG_le`. The residue is `κ₁(ℓη)⁻¹Lρ · ind`, with
  `ind = if zdist(a₁-a₂) ≤ ℓ*_u then 1 else 0`.
  - Near branch: `Lemma57.eG_near_le`.
  - Far branch: `Lemma57.eG_far_le`, closed by `ring`. Both the near term and the residue are
    `· 0` there, and `h554` is unused in that branch.

**(R2)**
- `eG_le_reduced_of_schwarz'`, `eG_le_reduced'` (gloop form, (5.58) via
  `Lemma57.gloop_h558a'`/`b'`), `eGpm_le_reduced'` (via `EGDef.norm_eGpm_le`).
- `rhs535'` (def) and `rhs535'_le_rhs535`.
- `eGpm_le_rhs535'`: the frozen `eGpm_le_rhs535`'s hypotheses, with conclusion `rhs535'`.
- `eGpm_le_rhs535_of_jG_mat'`: (T1)'s hypotheses. `Gm := gmBlkM`, and `h560` is discharged.
- No private lemma was needed in (R1)/(R2). The proofs of `eG_le`, `eG_le_reduced_of_schwarz`,
  `eG_le_reduced` and `eGpm_le_reduced` are re-run here as proofs of the primed statements.

**(R3)**
- `rhs535'_le_mul_tailT_near`: generic, any `ρ ≥ 0`, no smallness hypothesis.
- `DriftPt.exp_log_rpow_le_self`: `W ≥ 8 → e^{(log W)^{3/4}} ≤ W`.
- `DriftPt.resCoef_le`: the absorption arithmetic, `c_ρ ≤ η⁻¹`.
  - Hypotheses: `8 ≤ W`, `0 < ℓ_u`, `0 < ℓ_s`, `0 < η ≤ 1`, `ρ ≤ 2η⁻¹JW^{-D}`, `0 ≤ J ≤ W`,
    `ℓ_u ≤ L ≤ W`, `ℓ_u/ℓ_s ≤ gℓ_u`, `g ≤ 4W^{2ζ}`, `8 + 2ζ ≤ D`.
  - Chain: `c_ρ ≤ 2(rℓ)LJeW^{2-D} ≤ 8W^7·W^{2ζ-D} ≤ 8/W ≤ 1 ≤ η⁻¹`.
- `DriftPt.coarsen_ind`.
- `rhs535'_le_mul_tailT`: conclusion
  `η⁻¹((cNear r³ + 1)·ind + cFar(…) + 169(…))·T(d)`, **explicit `D₀ = 8 + 2ζ`**.
- The old `rhs535_le_mul_tailT` is kept; its docstring says "superseded by (R3)".

**(T3')**
- `mdr'` (def): `mdr` with the `ρ`-piece replaced by `c_ρ = r(ℓη)⁻¹Lρ(e^λA²)`.
- `drift_point_le'`: exactly `drift_point_le`'s hypotheses (generic `J`, `Gm`, `h560`, `hGm`),
  conclusion `mdr' … * tT`.
- `drift_point_le_blk'`: the same with `Gm := gmBlkM`.

**(T4')**
- `DriftPt.ell_mul_sqrt_le_one`.
- `DriftPt.mdr'_core`: scalar, with scale factor `g`. It has no `hℓs1`/`1 ≤ ℓs` premise; the
  residue enters through `hres ≤ (am)⁻¹`.
- `DriftPt.mdr'_mul_le`: per summand. `J ≤ W` is derived from `hreg`, via `J ≤ x^{24}R^{30} ≤ A_w`
  and `A_w ≤ W`.
- `drift_time_sum_le_of'`: deterministic core, bound
  `g³(2cN + cF + 170 + 36e)m⁻¹R² + e(WL)²W^{-D}`.
- `drift_time_sum_le_scale'`: eventual form for a scale family `(ℓsF, gF)`.
- **`drift_time_sum_le'`** (`ℓ_s = ℓ_{s N}`, `D ≥ 8`):
  - per-time premises `1 ≤ J_j ≤ N^{2ε}thr(u_j)` and `ρ_j ≤ 2η_{u_j}⁻¹J_jW^{-D}`;
  - conclusion `≤ driftSumConst E · N^κ · ((η_s/η_{u_k})² + 1)`, so **exponent 2** and constant
    `300/Im m`, as in (T4);
  - no `LρW^D ≤ 1`, no `0 ≤ ρ_j`, no `1 ≤ ℓ_s` premise.
- **`drift_time_sum_le_rescaled'`** (`ℓ_s' = ℓ_{s N}/(4N^ζ)`, `0 ≤ ζ`, `D ≥ 8 + 2ζ`):
  conclusion `≤ driftSumConst E · (4N^ζ)³ · N^κ · (R² + 1)`.
- `DriftPt.natCast_rpow_le_W_rpow`.
- `drift_time_sum_inputs_witness'`: compiled witness. The extreme choice `J = N^{2ε}thr(u)`,
  `ρ = 2η⁻¹JW^{-D} > 0` satisfies all per-time premises.
- The old `drift_time_sum_le` is kept. Its docstring says "Superseded by (T4')
  `drift_time_sum_le'`; its `LρW^D ≤ 1` premise is unsatisfiable with T1513's ρ".

**(T5)**
- `jGMat` corollary:
  - `DriftPt.gsqBlkM` (def, T1513's private `gsqBlkMat` body with `gmBlkM`);
  - `DriftPt.jGMat_eq` (`rfl`);
  - `DriftPt.gsqBlkM_nonneg`;
  - `DriftPt.one_le_jGMat'`, `DriftPt.gmBlkM_mul_swap_le_gsqBlkM` and
    `DriftPt.gsqBlkM_le_jGMat_mul_tailT`, which are **copies** of T1513's private
    `one_le_jGMat`, `gmBlkMat_mul_swap_le_gsqBlkMat` and `gsqBlkMat_le_jGMat_mul_tailT`;
  - `DriftPt.two_loop_re_le_jGMat` (`h531` with `J = jGMat`) and `DriftPt.gmBlkM_le_sqrt_jGMat`
    (`h42`).
- `DriftPt.scale_le_W`: `0 ≤ u < 1 → A_u ≤ W`.
- `DriftPt.heG_coef_le`: the scalar core.
- `mgDrift B ζ N := (4N^ζ)²(cNear(W,1) + cFar(W,1) + 170)`, and
  `mgDrift_le : ∀ κ > 0, ζ ≥ 0, ∀ᶠ N, mgDrift ≤ 2752·N^{κ+3ζ}`.
- **`drift_point_le_heG`**. Its conclusion is, literally:
  ```
  ‖eGterm … ⟨[true,false], List.ofFn b⟩ + primBil … ⟨[true,false], List.ofFn b⟩‖ ≤
    (exp 1 * thr E s δ N u ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹)
        + W * L * W ^ (-D))
      + mgDrift B ζ N * (etaT E u)⁻¹ *
        (((4 * N ^ ζ * (B.ell N u / B.ell N (s N))) ^ 3 + 1)
          + (B.scale E N u)⁻¹ ^ ((1:ℝ)/3) * thr E s δ N u ^ 3))
    * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1))
  ```
  This is T1518 (T1)'s `hdrift` with `Λ = thr`, `A = B.scale`, `ε = WLW^{-D}`,
  `q_u = (4N^ζ ℓ_u/ℓ_{s N})³ + 1`, `Mg = mgDrift`, `T_u(b) = tT … (zdist(b 0 - b 1))`.
  - Good-event hypotheses: `hjS : jSMat B.toDims E D N u M ≤ thr` and
    `hjG : jGMat B.toDims E N u ℓ_u η_u D M ≤ N^{2ε} thr`.
  - Per-matrix inputs at `ℓ_s' = ℓ_{s N}/(4N^ζ)`: `h273`, `h557C`, `h557R`, `hone`, `hκ`.
  - Scalar facts: `|E| < 2`, `1 ≤ N`, `0 ≤ s N ≤ u < 1`, `0 ≤ δ`, `0 ≤ ε`, `2ε ≤ δ`, `0 ≤ ζ`,
    `8 + 2ζ ≤ D`, `8 ≤ W`, `L ≤ W`, `N ≤ W²`, `2D² ≤ log W`, `N^{2ε}thr ≤ A_u`, `hDreg`.
  - `h554` is **not** a hypothesis. It comes from T1513's `mem_h554Set_of_isHermitian`, with
    `ρ = rho554(jGMat M) ≤ 2η⁻¹N^{2ε}thr·W^{-D}` (`rho554_mono`, `rho554_le_two_mul_rpow`).
- `Dgrid_eq_drift` (`rfl`): `Dgrid B E s t K N j ω b` is (T5)'s left side at `M := H B.toDims s t
  K N j ω` and `u := time s t K N j`.
- `drift_point_le_heG_scalars` (satisfiability): under `hreg` (gain `c`), `0 ≤ δ ≤ c/24`,
  `2ε ≤ δ` and `D ≥ 4`, the following hold eventually:
  - `1 ≤ N`, `8 ≤ W`, `L ≤ W`, `N ≤ W²`, `2D² ≤ log W`;
  - uniformly in `u ∈ [s N, t N]`: `N^{2ε}thr(u) ≤ A_u` and `L√(W^{-D}) ≤ ℓ_u A_u⁻¹`.

  Together with fixed `ζ ≥ 0`, `D ≥ 8 + 2ζ` (e.g. `D = 60`), these are all the scalar premises of
  (T5).

**(T2)** `eGterm_eq_eGpm` is byte-identical to before.

**Build**
- `cd /Users/junyin/Lean_proof/RBM1D-wt/T1515 && lake build RBM1D.Gauss.GridDriftPoint` gives
  `Build completed successfully (3951 jobs).`
- No warning or error lines come from `GridDriftPoint.lean` (two over-long docstring lines were
  fixed).
- `grep sorry|admit|^axiom` finds nothing.

**Axioms.** `#print axioms` (via `lake env lean` on a scratch file) was run on 42 declarations:
all new public declarations above, plus `eGterm_eq_eGpm` and `drift_time_sum_le`. Every one gives
`[propext, Classical.choice, Quot.sound]`.

**Name clashes.** None, checked by grepping all of `RBM1D/`. The only same-named declaration is
`scale_le_W`, and it is `private` in a different namespace (`Lemma514OneLoopSharp`).

## (c) Key lemmas used

- **Paper-side, merged:** `Lemma57.eG_near_le`, `Lemma57.eG_far_le`, `Lemma57.inv_sq_le_tailT`,
  `Lemma57.gloop_h558a'`/`b'`, `EGDef.norm_eGpm_le`, `Lemma57.inv_sqrt_le_rpow_third`,
  `Lemma57.inv_le_rpow_third`, `Lemma57.sqrt_le_self`.
- **T1513:** `jGMat`, `rho554`, `rho554_mono`, `rho554_le_two_mul_rpow`,
  `mem_h554Set_of_isHermitian`.
- **This file:** `ell_mul_sqrt_le`, `sum_step_div_sqrt_le`, `eventually_cNear_cFar_le`,
  `eventually_sq_WL_rpow_le`.
- **Elsewhere:** `flowScale_antitoneOn`, `Step2.norm_eLL_le`, `Step2.etaT_ratio`.

## (d) Open issues and notes for the auditor

1. **(R1) far branch.** The far branch has no residue: its proof is `eG_far_le` followed by
   `ring`, and the residue term is `κ₁(ℓη)⁻¹Lρ·0`.
2. **(R3) arithmetic.** `D₀ = 8 + 2ζ` (and `8` for `ℓ_s = ℓ_{s N}`, i.e. `g = 1`, `ζ = 0`).
   - It uses `J ≤ W`, not `J ≤ W²`. In (T4') this is proved from `hreg`; in (T5) it follows from
     the premise `N^{2ε}thr ≤ A_u` and `A_u ≤ W`.
   - It uses `e^{(log W)^{3/4}} ≤ W` for `W ≥ 8`, a deterministic fact rather than an eventual
     lemma.
3. **Constant in (T4').** The internal bracket is `274·N^κ` (the `ρ`-piece is the `+1` in `170`).
   REFEREE-d's `275` counts it separately. The stated constant `300/Im m` is unchanged.
4. **(T5) conventions.** `ℓ_s` in `q_u` is `ℓ_{s N} = B.ell N (s N)`; T1518 does not name it.
   `A^{-1/3}` is spelled `(B.scale E N u)⁻¹ ^ ((1:ℝ)/3)`. The left side uses `List.ofFn b`, as
   `Dgrid` does.
5. **(T5) is conditional.** It is conditional on the per-matrix premises `h273`, `h557C/R`,
   `hone`/`hκ` at `ℓ_s'`. R4c must supply these from T1513's `goodSet` (`eq273Set`, `eq557Set`,
   `honeSet`). `honeSet`'s `κ = 2N^{ζCtr}ℓ_u/ℓ_s` gives `hκ` when `ζCtr ≤ ζ`. It is not a
   special-case statement: `N`, `u ∈ [s N, 1)`, `D`, `E` and `M` are all general.
6. **Correction to the (a) text.** In the (T5) satisfiability line, read
   `N^{2ε}Λ ≤ xΛ = x²R_u⁴ ≤ x^{24}R_t^{30} ≤ N^c R_t^{30} ≤ A_t ≤ A_u`. That is what
   `drift_point_le_heG_scalars` proves.
7. **Paper-deltas.** No new paper-delta is proposed. Confining the residue to the near band
   returns the Lean to the paper (p.59). T215a (entry 148) should be marked "eliminated by (d)"
   by the dispatcher.
8. **Shared scratchpad.** The session scratchpad is shared: another agent overwrote my scratch
   file mid-run. All work was redone directly in the worktree file. The committed file is the one
   built and audited above.
