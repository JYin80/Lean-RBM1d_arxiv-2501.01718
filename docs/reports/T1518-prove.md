Prover model: claude-opus-5-5

# T1518 — prove report: the grid `step_bound`, `phi_arith'`, `grid_thr_improve`

Ticket: `docs/tickets/T1518.md`. Worktree `../RBM1D-wt/T1518`, branch `t/T1518`.
Sole writable file: `RBM1D/Gauss/GridStepBound.lean`.
No returning audit report exists for T1518 (fresh first pass).

## (a) Math preflight (written before any Lean, 2026-09-26 10:13 UTC)

Notation as in the ticket: `u_j = time s t K N j`, `Δ = step s t K N = (t-s)/K`,
`R_k = η_s/η_{u_k} = (1-s)/(1-u_k)` (`etaT_ratio`), `m = Im m_E ∈ (0,1]`,
`Λ(u) = thr E s δ N u = N^δ R_u⁴`, `A_u = scale E N u = W ℓ_u η_u`, `ε = W L W^{-D}`,
`q_u = (4N^ζ ℓ_u/ℓ_s)³ + 1`, `Ξ = xiK L W m`, `T_u(b) = tT B E N D u (zdist (b0-b1))`.

### Step 0 read-only checks (done)
- `Step2.step_bound` (Step2.lean:724): initial term via `norm_Uker_flow`, drift per-time
  `K * Ξ * T_v` with `c = m⁻¹(1-s)/(1-v)²` from `hr2 : η_u⁻¹ r_u² ≤ c` (η paired with the
  propagator), then `c·(v-s) ≤ m⁻¹R²` (`hc`). `phi` (:709), `phi_arith` (:933), `cStep` (:926).
- `step2`'s discharge of `phi_arith`'s premises: `eventually_step_facts` (Step2.lean:1078), from
  `hreg` (2.72 with gain `N^c`), `δ ≤ 1`, `24δ ≤ c`, `D ≥ 60`, uniformly in `v ∈ TimeIcc s t N`;
  `jS_highProb` gets `q ≤ R` from `Step3.ellHat_le_sqrt_mul` (`ℓ_v/ℓ_s ≤ √R`).
- T1510 `weighted_duhamel_sum_le` (per-time profile bound `M_j T_{u_j}` → `Σ Δ M_j w_j² Ξ T_{u_k}`,
  `w_j = (1-u_{j+1})/(1-u_k)`), side condition `hAuv` = `flowScale_antitoneOn`.
- T1504 `stopped_duhamel_det_bound` (GridDuhamelTail:662): conclusion `2ⁿ(2ⁿ Σ_{j<K} r_j)`,
  hypotheses `hr0 : ∀ j, 0 ≤ r j`, guarded `hR`, guarded `hFwd ≤ 2ⁿ r_j`. `norm_Uker_apply_le`
  (Kernel.lean:256): `‖U A a‖ ≤ Cⁿ M` if the edge row sums are `≤ C`.
- T1506 `stepErr` (GridDriftAlgebra:779) and `stepErr_le_unif` (:980):
  `stepErr ≤ C₁(δ')Δ² + C₂(δ')Δ^{3/2}` on `u_{j+1} ≤ 1-δ'`; `C₁, C₂` explicit in
  `L, W, (δ'm)⁻¹, δ'⁻¹, ‖m_E‖ = 1, ∫‖X‖`.
- T1516 `grid_expansion_all'`, `Agrid`, `Dgrid`, `Rgrid`, `Zvec`, `Yvec` (statements).
- T1511 `etaT_inv_le_of_hreg` (GridNetLift:86): eventually `η_{t_N}⁻¹ ≤ N`.
- `jSMat` (GridJStar:121) is `Step2.jStar` of `a ↦ ‖gloop(H) - Kval‖` at `LoopData.idx (sigPM,a)`;
  this equals `‖Agrid k ω a‖` (index identity of `lkFun_eq_Lval_sub_Kv`). `jStar_le`: pointwise
  `f ≤ c T` gives `jStar ≤ c + 1`.

### (T1) `RBM.Gauss.Grid.grid_step_bound` — PASS (with two documented statement points)

Paper: (5.39)–(5.41) + (5.45) of `paper/250520-YinJun-v2.pdf`, discrete (grid) form of
`Step2.step_bound`. Deterministic, fixed `N, ω, k ≤ K N`.

Five terms (expansion identity = conclusion of `grid_expansion_all'` at `ω, k`):
1. Initial: `Step2.norm_Uker_le_of_tail` (the kernel estimate behind `norm_Uker_flow`, stated
   directly for `ξ ≡ 1`) with `u = u_0 = s`, `v = u_k`: `≤ Mi R_k² Ξ T_{u_k}(a)`.
2. Drift: `weighted_duhamel_sum_le` with `M_j = coef(u_j)`, then **η paired**:
   `η_{u_j}⁻¹ w_j² = (1-u_{j+1})²/(m(1-u_j)(1-u_k)²) ≤ (1-u_j)/(m(1-u_k)²)` (as
   `1-u_{j+1} ≤ 1-u_j`), so `Σ_{j<k} Δ η_{u_j}⁻¹ w_j² ≤ (kΔ)(1-s)/(m(1-u_k)²)
   ≤ (1-s)²/(m(1-u_k)²) = R_k²/m` (using `kΔ = u_k - s ≤ 1 - s`). The ε-part has no η:
   `Σ Δ w_j² ≤ kΔ R_k² ≤ R_k²`. Monotonicity in `u` (for `u_j ≤ u_k < 1`): `Λ` increasing
   (`R_u` increasing), `A_u⁻¹` and `A_u^{-1/3}` increasing (`flowScale_antitoneOn`), `q_u`
   increasing (`ellHat_mono`, `4N^ζ ≥ 0`). Total drift weight: `Ξ(eΛ²(36 m⁻¹R²A⁻¹ + R²ε)
   + Mg m⁻¹R²(q + A^{-1/3}Λ³))` evaluated at `u_k` — **R²/m, not R³** (no `sup × length`
   on `η_u⁻¹`).
3. Z: hypothesis `hZ` (`≤ Mm(R²+1)T_{u_k}`). 4. Y: hypothesis `hY` (`≤ T_{u_k}`).
5. R-sum: `stopped_duhamel_det_bound` with `Ω' = Unit`, `τ ≡ k`, `K := k`, `t := u_k`, `n = 2`,
   `ξ ≡ 1`, and **enlarged r**: `r'_j = C² stepErr_j` for `j < k` (`0` otherwise), `C = (1-s)/(1-t)`.
   `hr0`: `stepErr_j ≥ ‖R_j b‖ ≥ 0` for `j<k` (from `hRstep`). `hR`: `‖R_j‖ ≤ stepErr_j ≤ r'_j`
   (`C ≥ 1`). `hFwd`: `norm_Uker_apply_le` with row bound `1 + (u_k-u_{j+1})/(1-u_k)
   = (1-u_{j+1})/(1-u_k) ≤ C`, giving `‖U R_j‖ ≤ C² stepErr_j = r'_j ≤ 4 r'_j`. **Not** the
   `_half` variant. Result: `≤ 16 C² Σ_{j<k} stepErr_j`.
   Smallness (`C_R` explicit): with `δ' = 1-t`, `η = δ'm = η_t`, hypotheses `η_t⁻¹ ≤ N`,
   `W L ≤ N`, `N ≥ 2`, `‖m_σ‖ = ‖m_E‖ = 1`, `∫‖X‖ ≤ 1 + E Tr X² = 1 + LW ≤ 2N`
   (`integral_frobSq_Xmat_one`), one gets `δ'⁻¹ ≤ η⁻¹ ≤ N`, `C ≤ N` and
   `zMotionLip ≤ 48N⁷`, `zMotionZLip ≤ 192N⁷`, `driftLip ≤ 27648N¹⁴`, hence
   `C₁ ≤ 103N⁷`, `C₂ ≤ 37024N¹⁵`, `C₁+C₂ ≤ 2¹⁷N¹⁵`. With `kΔ ≤ 1`, `Δ ≤ 1`:
   `Σ_{j<k} stepErr_j ≤ (C₁+C₂)Δ^{1/2}`, so the R-sum `≤ 2²¹N¹⁷Δ^{1/2} ≤ N³⁸Δ^{1/2}`.
   Hypothesis `hΔR : Δ ≤ N^{-(2D+76)}` (i.e. `C_R = 2D + 76`) gives `≤ N^{-D} ≤ W^{-D} ≤ T_{u_k}(a)`
   (`D ≥ 0`, `1 ≤ W ≤ N`).

Statement points (not weakenings; recorded for the auditor):
- **Φg carries `+ 2`, not `+ 1`.** The ticket's `hY` has coefficient exactly `1` (not `Mm`), so
  the Y-sum contributes one `T_{u_k}` and the R-sum another. `Φg` = `Step2.phi`'s expression at
  `v = u_k` (with `q_{u_k}` in the `q` slot) `+ 1 (Y) + 1 (R)`. The ticket's "+1 for the R-sum"
  omits Y's unit coefficient; with only `+1`, the bound does not follow from the listed hypotheses
  by the five-term triangle inequality (Y and R each contribute one `T_{u_k}`). Downstream effect:
  (T3)'s bound becomes `cStep x²R⁴ + 2`, still `< x⁸R⁴` eventually.
- **Side hypotheses of (T1)** needed to make `C_R` explicit, exactly the ingredients the ticket
  names ("`η_t⁻¹ ≤ N` (T1511 (T1)) and `W ≤ N`"): `hηt : η_{t_N}⁻¹ ≤ N`, `hWL : W L ≤ N`,
  `hN2 : 2 ≤ N`, `hD0 : 0 ≤ D`; plus the grid bookkeeping `0 ≤ s ≤ t < 1`, `1 ≤ K N`, `k ≤ K N`,
  `exp 1 ≤ W` (as in `step_bound`), `0 ≤ Mi, Mg`. All of them are **discharged eventually in
  (T3)** (from `hreg`, `B.dim`, `eventually_step_facts`), not assumed there.
- `q_u` slot: `hdrift` is the ticket's shape with `q_{u_j} = (4N^ζℓ_{u_j}/ℓ_s)³ + 1`.

Boundary cases: `k = 0` (all sums empty; bound is `Mi Ξ + ...`, fine); `s = t` (`Δ = 0`,
`u_j ≡ s`); `u_k → 1` handled by `η_t⁻¹ ≤ N`. Quantifier order: fixed `N`, then `k`, `ω`.
Dependencies all merged (T1504, T1506, T1510, T1511, T1516, Step2).

Satisfiability: (T1) is proved from a deterministic core `grid_step_bound_core` over abstract
vectors (the Agrid instance is a specialisation). A compiled nondegenerate witness for the core
is planned on `band Dims.«example»` at `N = 30` (`W = 10 ≥ e`, `WL = 30 ≤ N`), `E = 0` (`m = 1`),
`s = 0`, `t = 1/2` (`η_t⁻¹ = 2 ≤ 30`), `K = 30⁷⁶` (so `Δ ≤ 30^{-76}`, `D = 0`), `k = 2`, with
nonzero initial vector (exact tail profile), nonzero drift vectors (exact `coef·T` shape), nonzero
Z- and Y-sums at the bound, and all hypotheses holding. The random hypotheses of (T1) at the
genuine `Agrid` instance (Azuma/Chebyshev events) cannot be witnessed deterministically; they hold
on the good event of R4c.

### (T2) `RBM.Gauss.Grid.phi_arith'` — PASS

Same statement as `Step2.phi_arith` with `hq : q ≤ R^{3/2}` (rpow) instead of `q ≤ R`, and the
**same conclusion `≤ cStep m · x² R⁴`**. Only term t4 changes:
`Ξ · x m⁻¹ R² q ≤ x · x m⁻¹ R² R^{3/2} = m⁻¹ x² R^{7/2} ≤ m⁻¹ x² R⁴` since `R ≥ 1` and
`3/2 ≤ 2` (`R^{3/2} ≤ R²`). The other six terms are verbatim. Hence the conclusion is unchanged
(supervisor 0048 §1g: `R^{3.5} ≤ R⁴`) — checked, PASS.
`65N^{3ζ}` carried in Mg: `q_u ≤ 64 N^{3ζ}(ℓ_u/ℓ_s)³ + 1 ≤ 64N^{3ζ}R^{3/2} + 1 ≤ 65N^{3ζ}R^{3/2}`
(`ℓ_u/ℓ_s ≤ √R` by `Step3.ellHat_le_sqrt_mul`; `N^{3ζ}R^{3/2} ≥ 1` for `ζ ≥ 0`, `N ≥ 1`). Then
`Mg(q + αΛ³) ≤ (65N^{3ζ}Mg)(q/(65N^{3ζ}) + αΛ³)` and `q/(65N^{3ζ}) ≤ R^{3/2}`; so
`phi_arith'` is applied with Mg-slot `x ≥ 65N^{3ζ}Mg` and q-slot `q/(65N^{3ζ})`. A lemma
`qGrid_le` states the `65N^{3ζ}R^{3/2}` bound.

### (T3) `RBM.Gauss.Grid.grid_thr_improve` (+ `grid_phi_premises`) — PASS

Hypotheses (global): `|E| < 2`, `0 ≤ s N ≤ t N < 1` for all `N`, `hreg` (2.72 with gain `N^c`,
`c > 0`), `0 < δ ≤ 1`, `24δ ≤ c`, `64 ≤ D`, `0 ≤ ζ`. Conclusion: `∀ᶠ N`, for all `Mi, Mg, Mm`
with `0 ≤ Mi, Mg`, `Mi ≤ x`, `65N^{3ζ}Mg ≤ x`, `Mm ≤ x` (`x = N^{δ/8}`), all `k ≤ K N`
(`1 ≤ K N`, `hΔR`), all `ω` satisfying (T1)'s random hypotheses:
`jSMat B.toDims E D N u_k (H_k ω) ≤ cStep m x² R_k⁴ + 2` and `cStep m x² R_k⁴ + 2 < Λ(u_k)`.
- `grid_phi_premises` proves eventually, uniformly in `v ∈ [s N, t N]` (hence in `k`, since
  `u_k ∈ [s,t]`): `exp 1 ≤ W`, `1 ≤ x`, `cStep + 2 < x⁶`, `Ξ ≤ x`, `2 ≤ N`, `WL ≤ N`,
  `η_t⁻¹ ≤ N`, and `x¹⁷R¹⁰ ≤ A_v`, `A_v^{-1/3}x²⁴R¹⁰ ≤ 1`, `ε x¹⁷R¹⁰ ≤ 1` — by reusing
  `Step2.eventually_step_facts` (needs `D ≥ 60`, implied by `D ≥ 64`), `eventually_le_rpow`,
  `B.dim`, and `etaT_inv_le_of_hreg`. **Not assumed.**
- `Mi, Mg, Mm ≤ x` are the random-layer constants (supplied by R4c; `Mg` with the `65N^{3ζ}`
  factor merged, needs `κ, ζ ≤ δ/48` upstream) — these are the only phi premises that remain
  hypotheses, as in the ticket.
- Arithmetic: `jSMat ≤ Φg + 1` (`jStar_le`), `Φg + 1 ≤ LHS(phi_arith') + 2 ≤ cStep x²R⁴ + 2`;
  `cStep x²R⁴ + 2 < x⁸R⁴ = Λ(u_k)` because `x²R⁴ ≥ 1` and `x⁶ > cStep + 2`.
Satisfiability of (T3)'s hypotheses: those of `step2`/`eventually_step_facts` (already used by
the merged Step 2), plus `ζ ≥ 0`, `Mg ≤ x/(65N^{3ζ})` (e.g. `Mg = 0`, or `Mg ≤ N^{δ/16}/65` with
`ζ ≤ δ/48`), and (T1)'s random hypotheses on the good event.

Verdict: (T1) PASS, (T2) PASS, (T3) PASS. Proceeding to Lean.

## (b) Declarations, build, axioms (Lean written after the preflight; finished 2026-09-26 10:34 UTC)

File: `RBM1D/Gauss/GridStepBound.lean` (1273 lines), namespace `RBM.Gauss.Grid`.
Branch `t/T1518`, commit `2299c17` ("T1518: grid step_bound, phi_arith', grid_thr_improve").
No `sorry` / `admit` / `axiom`.

Targets:
- (T1) `grid_step_bound` — hypotheses exactly as in the ticket (`hexp` = `grid_expansion_all'`
  instantiated at `ω, k`; `hinit`; `hdrift` in the heG shape via `driftCoef`; `hZ`; `hY`;
  `hRstep` with `stepErr`), plus the side conditions listed in (a) (`hΔR : step ≤ N^{-(2D+76)}`,
  `hηt`, `hWL`, `hN2`, `hW`, `hD0`, `hMi`, `hMg`, grid bookkeeping). Conclusion
  `∀ a, ‖Agrid … k ω a‖ ≤ phiG … (time s t K N k) * tT … (time s t K N k) (zdist (a0-a1))`.
  `phiG` (written out) = `Mi R² Ξ + Ξ(eΛ²(36m⁻¹R²A⁻¹ + R²ε) + Mg m⁻¹R²(q + A^{-1/3}Λ³))
  + Mm(R²+1) + 1 + 1` at `v = u_k`.
  Abstract core: `grid_step_bound_core` (same hypotheses over abstract vectors `A0 Ak Zs Ys Dv Rv`).
- (T2) `phi_arith'` — `hq : q ≤ R ^ ((3:ℝ)/2)`, conclusion `≤ Step2.cStep m * x^2 * R^4`
  (unchanged). `qGrid_le : qGrid B s ζ N u ≤ 65 * N^(3ζ) * R_u^(3/2)`.
- (T3) `grid_thr_improve` — global hypotheses `hE, hs0, hst, ht1, hc0, hreg, 0<δ≤1, 24δ≤c,
  64≤D, 0≤ζ`; conclusion `∀ᶠ N, ∀ Mi Mg Mm, 0≤Mi → 0≤Mg → Mi≤x → 65N^{3ζ}Mg≤x → Mm≤x →
  1≤K N → hΔR → ∀ k ≤ K N, ∀ ω, [T1 random hyps] → jSMat B.toDims E D N u_k (H … k ω)
  ≤ cStep m x² R_k⁴ + 2 ∧ cStep m x² R_k⁴ + 2 < thr E s δ N u_k` (`x = N^{δ/8}`).
  `grid_phi_premises` proves the phi premises and (T1)'s side conditions eventually.

Supporting public lemmas: `qGrid`, `driftCoef`, `phiG` (defs); `step_nonneg'`, `time_eq`,
`time_succ'`, `time_mono'`, `K_mul_step`, `mul_step_le`, `time_le_t`, `s_le_time`, `thr_nonneg`,
`thr_mono`, `scale_inv_mono`, `qGrid_mono`, `qGrid_nonneg`, `driftCoef_nonneg`,
`eta_inv_mul_weight_le` (the η-pairing), `drift_sum_le`, `integral_norm_Xmat_le`,
`zMotionLip_le`, `zMotionZLip_le`, `driftLip_le`, `stepErrC_le`, `stepErr_sum_le`,
`norm_Uker_fwd_le`, `rsum_le`, `jSMat_le_of_Agrid`, `stepErr_nonneg`; witness `example`.

Build:
- `cd /Users/junyin/Lean_proof/RBM1D-wt/T1518 && lake build RBM1D.Gauss.GridStepBound` →
  `✔ Built RBM1D.Gauss.GridStepBound`, `Build completed successfully (3911 jobs)`, 0 errors,
  0 warnings in this file.
- Name-clash check against the root: a scratch file `import RBM1D` + `import
  RBM1D.Gauss.GridStepBound` elaborates without error (root import to be added at merge).

`#print axioms` (all `[propext, Classical.choice, Quot.sound]`): `grid_step_bound`,
`grid_step_bound_core`, `phi_arith'`, `qGrid_le`, `grid_phi_premises`, `grid_thr_improve`,
`drift_sum_le`, `rsum_le`, `stepErr_sum_le`, `jSMat_le_of_Agrid`, `stepErr_nonneg`.

Witness (compiled, end of file): `band Dims.«example»`, `N = 30` (`W = 10`, `L = 3`), `E = 0`
(`Im m = 1`), `s = 0`, `t = 1/2`, `K = 30⁷⁶`, `k = 2`, `D = 0`, `δ = 1`, `ζ = 0`,
`Mi = Mg = Mm = 1`; `A0` = exact tail profile (proved `≠ 0`), `Dv j = driftCoef·T_{u_j}`,
`Zs`, `Ys` exactly at their bounds (`Ys ≠ 0` proved), `Rv j ≡ stepErr_j`, `Ak` defined by the
expansion identity; `hW, hWL, hηt, hΔR` verified numerically; `grid_step_bound_core` applied.

## (c) Key lemmas used

`Step2.norm_Uker_le_of_tail`, `Step2.etaT_ratio`, `Step2.etaT_eq`, `Step2.thr`, `Step2.xiK_nonneg`,
`Step2.jStar_le`, `Step2.phi_arith` (structure copied), `Step2.cStep`,
`Step2.eventually_step_facts`, `Step2.natCast_rpow_pow`; T1510 `weighted_duhamel_sum_le`;
T1504 `stopped_duhamel_det_bound`, `norm_Uker_apply_le`; T1506 `stepErr`, `stepErr_le_unif`,
`stepErrC1/C2`; T1511 `etaT_inv_le_of_hreg`; T1516 `Agrid`, `Dgrid`, `Rgrid`, `Zvec`, `Yvec`;
`jSMat`; `flowScale_antitoneOn`, `Step3.ellHat_mono`, `Step3.ellHat_le_sqrt_mul`,
`integral_frobSq_Xmat_one`, `l2_opNorm_sq_le_frobSq`, `norm_mSigma`, `norm_mE`, `eventually_le_rpow`.

Auditor checkpoints:
- η pairing: `eta_inv_mul_weight_le` then `drift_sum_le`'s `hS1 : Σ Δ η_{u_j}⁻¹ w_j² ≤ m⁻¹R²`;
  no `sup η⁻¹ × length` anywhere; drift weight `R²/m`.
- `hFwd`: `rsum_le` builds `r j = if j < k then ((1-s)/(1-t))² stepErr_j else 0` and proves
  `hFwd` by `norm_Uker_fwd_le` (row bound `(1-u_{j+1})/(1-u_k) ≤ (1-s)/(1-t)`); the `_half`
  variant is not used.
- `phi_arith'` conclusion is literally `Step2.cStep m * x ^ 2 * R ^ 4`.
- (T3) premises: `grid_phi_premises` derives `exp 1 ≤ W`, `1 ≤ x`, `cStep+2 < x⁶`, `Ξ ≤ x`,
  `2 ≤ N`, `WL ≤ N`, `η_t⁻¹ ≤ N` and the three scale inequalities for all `v ∈ [s,t]` from
  `hreg`, `δ ≤ c/24`, `D ≥ 64` (via `eventually_step_facts` with `D ≥ 60`).

## (d) Open issues

1. **`+2` instead of `+1`** in `Φg` / (T3) (see (a)): forced by `hY`'s unit coefficient. If the
   dispatcher wants `+1`, `hY` would need a coefficient absorbed elsewhere; not changed here.
2. **Side hypotheses of (T1)** (`hηt`, `hWL`, `hN2`, `hD0`, `hK1`, grid bookkeeping) are not in
   the ticket's literal hypothesis list but are the ingredients the ticket names for `C_R`; all
   are discharged eventually in (T3). `C_R = 2D + 76` (crude but explicit).
3. **Random hypotheses** (`hexp` a.e., `hinit`, `hdrift`, `hZ`, `hY`, `hRstep` a.e.) are, by
   design, not witnessed at the genuine `Agrid` instance; the compiled witness is for the abstract
   core with genuine nonzero data. They must be supplied on the good event by R4c. `hdrift`'s
   producer (T1515 (T3), ρ question) and `Mg`'s bound `65N^{3ζ}Mg ≤ x` (needs `κ, ζ ≤ δ/48`
   upstream) are downstream obligations.
4. **Proposed paper-delta entry (T1518a)** — not written (sole writable file rule): "Grid
   step bound (5.39)–(5.41),(5.45) at grid times: bound `Φg = phi(q ↦ q_u, (5.54) residue r³
   with ℓ_s/(4N^ζ)) + 2`, with the Y/R terms of the discrete Duhamel expansion each costing one
   `T_{u_k}`; the grid refinement requires `Δ ≤ N^{-(2D+76)}`."
5. Special cases: none used; statements are for general `B, E, s, t, K, N, k, ω`.

Verdict: (T1) PASS, (T2) PASS, (T3) PASS; module builds.
