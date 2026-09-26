Prover model: claude-opus-5-5

# T1524 — prove report (R4c-2b: Step 2 closes)

Ticket: `docs/tickets/T1524.md`. Worktree `../RBM1D-wt/T1524`, branch `t/T1524`, sole writable file
`RBM1D/Gauss/Step2Close.lean`. No returning audit report exists for T1524 (first pass).

## (a) Math preflight (written before any Lean)

### Step 0: merged statements read (line numbers on `main` @ ce3a0d2)

| Item | Location | Shape used |
|---|---|---|
| T1519 `gridTau`, `lt_gridTau_imp`, `gridTau_le` | `Gauss/GridGoodEvent.lean:74, 119, 133` | `gridTau = min (firstHit (J-thr) 0 K) (firstHit 1_{goodSetᶜ} (1/2) K)` |
| T1519 `highProb_init_grid` (T5) | `GridGoodEvent.lean:240` | `‖A_0 b‖ ≤ N^{δ/16} T_{u_0}(b)`, `J_0 < thr(u_0)` |
| T1519 `CK`, `gridK`, `gridK_card_le` | `GridGoodEvent.lean:1648, 1651, 1676` | `K = max 1 ⌈N^{D₁+2D+80}⌉`, `K+1 ≤ N^{CK+2}` |
| T1519 `goodEventGrid`, `goodEvent_grid` (T6′) | `GridGoodEvent.lean:1978, 2005` | `∀ D₁>0, ∀ᶠ N, Pg (goodEventGrid … (gridK D (D₁+1)) (2D+2) (2D+2) N)ᶜ ≤ N^{-D₁}`; needs `δ ≤ c/24`, `60 ≤ D`, `τ₁ ε ζCtr τ3 τ57 > 0`, `Cond272`, `s ≤ u ≤ t` |
| T1519 `goodEvent_grid_imp` (T6′) | `GridGoodEvent.lean:2091` | eventually: `1 ≤ K`, `Δ ≤ N^{-(2D+76)}`, `0 ≤ Mm ≤ N^{δ/8}` (`Mm = azumaMm`); on the event: `hinit` (`Mi = N^{δ/16}`), `hZ`, `hY` at `k = τ ω`, `J_j < thr ∧ H_j ∈ goodSet` for `j < τ`, goodSet for all `j ≤ K`, `J_0 < thr(u_0)`; needs `τ₁ ≤ δ/32`, `0 ≤ ε`, `2ε ≤ δ` |
| T1515 `drift_point_le_heG` (T5) | `Gauss/GridDriftPoint.lean:2973` | per-matrix inputs `h273, h557C, h557R, hone, hκ, hjS, hjG`; scalars `D ≥ 8+2ζ`, `W ≥ 8`, `L ≤ W`, `N ≤ W²`, `2D² ≤ log W`, `hJA`, `hDreg` |
| T1515 `mgDrift`, `mgDrift_le`, `Dgrid_eq_drift`, `drift_point_le_heG_scalars` | `GridDriftPoint.lean:2928, 2932, 3132, 3149` | `Mg ≤ 2752 N^{κ+3ζ}`; scalars eventually, uniformly in `v ∈ [s N, t N]` |
| T1518 `driftCoef`, `qGrid` | `Gauss/GridStepBound.lean:60, 56` | |
| T1518 `grid_phi_premises`, `grid_thr_improve` (T3) | `GridStepBound.lean:961, 993` | one sequence `t` is both the grid endpoint and `hreg`'s time; needs `δ ≤ 1`, `24δ ≤ c`, `64 ≤ D`, `0 ≤ ζ`; conclusion `J_k ≤ cStep x²R⁴+2 < thr(u_k)` |
| T1516 `grid_expansion_all'`, `condExp_A_succ`, `Agrid/Dgrid/Rgrid` | `Gauss/GridExpansion.lean:928, 292, 266–289` | both need `s N < t N` **strictly** |
| T1520 `GridPointwise'`, `hpt_of_gridPointwise'`, `step2_gauss_of_gridPointwise'`, `min_firstHit_eq_of_at`, `lk_le_of_jS` | `Gauss/GridBootstrap.lean:226, 277, 309, 367, 80` | as ticket |
| T1521 `Steps12`, `steps12_gauss_of_grid` | `Gauss/Steps12Gauss.lean:45, 102` | uses `GridPointwise` (unprimed) |
| `Step2.step2` | `Hierarchy/Step2.lean:2050–2072` | hypotheses `hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg` |
| T1513 `goodSet` components | `Gauss/GridGoodSet.lean:722`, `GridJStar.lean:256, 328`, `GridGoodSet.lean:484, 688` | `eq273Set`, `eq557Set` (**column only**), `jgSet`, `honeSet` |

### Interface mismatches (found before writing Lean) and their bridges

1. **Grid endpoint vs `hreg`'s time in T1518.** `grid_thr_improve`/`grid_phi_premises` take one
   sequence `t` that is both the grid endpoint (`time s t K N`) and the time in `hreg`. Our grid
   endpoint is `u N ∈ [s N, t N]`. Bridge (proved lemma `hreg_endpoint`): `R_u ≤ R_t`
   (`etaT_ratio`) and `A_t ≤ A_u` (`flowScale_antitoneOn`) give
   `N^c R_u^{30} ≤ N^c R_t^{30} ≤ A_t ≤ A_u`; `s ≤ u`, `u < 1` from `TimeIcc`. Pure inequality, no
   new hypothesis.
2. **Strict window in T1516.** `grid_expansion_all'` and `condExp_A_succ` require `s N < u N`;
   `TimeIcc s t N` allows `u N = s N`. Bridge: per-`N` case split. If `u N = s N` then `Δ = 0`,
   so `time k = s N` and `H_k = H_0` for all `k` (definition `GridPath.lean:65`), and T1519 (T5)'s
   `J_0 < thr(u_0)` (a component of `goodEventGrid`) is the needed `J_τ < thr(u_τ)` directly; if
   `s N < u N` the T1518 route below applies.
3. **Row form of (5.57) missing from the good event.** `drift_point_le_heG` needs `h557R` (row
   orientation), but T1513's `goodSet` contains only `eq557Set` (column orientation), so T1519
   (T6′) does not supply `h557R`. Bridge: an extra grid `HighProb` event from the merged
   `Gauss.Step2.highProb_eq557_colRow` (T1492, `Gauss/Step2Eq557.lean:178`, second conjunct),
   restricted to `[s, u]` (`highProb_flow_restrict`, `GridGoodSet.lean:854`) and transferred to the
   grid (`highProb_grid_of_flow`, `GridJStar.lean:214`). To keep the total at `N^{-D₁}`, T1519
   (T6′) is used at `D₁ + 1`, so `K := gridK D' (D₁ + 2)`, and the row event at `D₁ + 1`.
4. **Good-set constants vs T1515's per-matrix inputs** (`ℓ_s' = ℓ_{s N}/(4N^ζ)` in T1515):
   `eq273Set` gives `N^{τ3} (ℓ_u/ℓ_s)² A_u^{-2}` vs `h273`'s `(4N^ζ ℓ_u/ℓ_s)² A_u^{-2}`;
   `eq557Set` gives `N^{τ57} √(ℓ_u/ℓ_s) A_u^{-1/2}` vs `√(4N^ζ ℓ_u/ℓ_s) A_u^{-1/2}`;
   `honeSet` gives `N^{ζCtr}·2(ℓ_u/ℓ_s)·A_u^{-1}` vs `κ A_u^{-1}` with `2κ ≤ 4N^ζ ℓ_u/ℓ_s`.
   Bridge: choose `τ3 = ζCtr = ζ`, `τ57 = ζ/2`, `κ := 2 N^ζ ℓ_u/ℓ_s` (equality in `hκ`), and use
   `N ≥ 1`. The `(+,+,…)` loop of `h273` is `LoopData.idx (![false,true,true], ![y,c,x])`.
   `hjG` from `jgSet` (`jGMat ≤ N^{2ε} jSMat`) and `jSMat < thr` (for `j < τ`).
5. **Drift coefficient shape.** T1515's (T5) coefficient is `… + Mg * η⁻¹ * ((4N^ζ(ℓ_u/ℓ_s))³+1 + …)`,
   T1518's `driftCoef` is `… + Mg * (η⁻¹ * (qGrid + …))` with `qGrid = (4N^ζ ℓ_u/ℓ_s)³+1`.
   Equal by `ring` (associativity, `mul_div_assoc`); bridged by lemma `heG_coef_eq_driftCoef`.
6. **Loss order.** T1519 needs `D ≥ 60`, T1518 `D ≥ 64`, T1515 `D ≥ 8+2ζ`, T1520 `lk_le_of_jS`
   `D + 4 ≤ D'`: `D' := max (D + 4) 64` meets all.
7. **`Mg` budget.** T1518 needs `65 N^{3ζ} Mg ≤ N^{δ/8}`; with `ζ = δ/96` and `mgDrift_le` at
   `κ' = δ/32`: `65·2752 N^{δ/32+δ/16+δ/32}·… ` precisely `65 N^{3ζ}·2752 N^{κ'+3ζ} = 178880 N^{3δ/32}
   ≤ N^{δ/8}` once `N^{δ/32} ≥ 178880` (eventually).
8. **T1521 uses unprimed `GridPointwise`.** (T3) restates `steps12_gauss_of_grid`'s proof with
   `step2_gauss` (no `hgp`).
9. **`Step1.Hyp`.** `step2_gauss` drops both `Hy` and `h1 : Step1.Hyp` (the latter is
   discharged inside T1517's `step2_gauss_of_pointwise`). The (T4) `example` carries `h1` as an
   unused binder so that its hypothesis list is literally step2's minus `Hy`.

No mismatch is a mathematical obstacle; all are bridged by proved lemmas inside the sole file.

### Parameters (all fixed before `N`, none depends on `ω`)

For given `D > 0`, `u`: `D' := max(D+4, 64)`, `δ₀ := min(c/24, 1)`. For `δ ∈ (0, δ₀]`, `D₁ > 0`:
`ζ := δ/96`, `ε := δ/4`, `τ₁ := δ/32`, `ζCtr := τ3 := ζ`, `τ57 := ζ/2`, `κ' := δ/32`,
`K := gridK D' (D₁+2)` (depends only on `D, D₁`), `C := CK D' (D₁+2) + 2`.
Simultaneous satisfiability of the parameter constraints: `δ ≤ c/24`, `24δ ≤ c`, `δ ≤ 1`
(from `δ ≤ δ₀`); `τ₁ ≤ δ/32` (equality); `0 < ε`, `2ε = δ/2 ≤ δ`; `ζ ≥ 0`; `D' ≥ 64 ≥ 8 + 2ζ`
(`ζ ≤ 1/96`); all good-set parameters `> 0` since `δ > 0`; `κ' + 6ζ = 3δ/32 < δ/8`.

### Per target

- **(T1) `RBM.Gauss.Grid.gridPointwise'_gauss` — PASS.** Statement: step2's hypotheses minus
  `Hy`, `h1` ⟹ `GridPointwise' d E s t`. Route as in the ticket, with bridges 1–7. On
  `G N := goodEventGrid ∩ row-event ∩ {expansion + Rgrid a.e. set}`, at `k := gridTau ω`:
  `J_τ < thr(u_τ)` (T1518 (T3) if `s N < u N`; T1519 (T5) if `u N = s N`); `min_firstHit_eq_of_at`
  (hgood from the goodSet-at-all-`j ≤ K` component) gives `τ = K`, so `J_K < thr(u N)`
  (`time_last`); `lk_le_of_jS` (with `1 ≤ A_u ≤ W²` from `flow_crude` + `eventually_le_W_sq`)
  gives the `lkErrMat` bound, so bad set `⊆ (G N)ᶜ`, and
  `Pg (G N)ᶜ ≤ N^{-(D₁+1)} + N^{-(D₁+1)} + 0 ≤ N^{-D₁}` for `N ≥ 2`. Dependencies are all merged
  (T1492, T1513, T1515, T1516, T1518, T1519, T1520). Boundary cases: `u N = s N` handled
  (bridge 2); `s N = 0` allowed (`H_0 = 0`, all lemmas take `0 ≤ s`); `N` small excluded by `∀ᶠ`.
  No new hypothesis.
- **(T2) `RBM.Gauss.step2_gauss` — PASS.** `step2_gauss_of_gridPointwise' … (T1)`. Hypotheses:
  `hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg` — step2's minus `Hy` and `h1`; no new hypothesis, so no
  new satisfiability witness is needed. No `Hy`/`Step2.Hyp` enters through any dependency: T1517
  `step2_gauss_of_pointwise` (`Step2Gauss.lean:186`) uses `Grid.h276_of_pointwise`,
  `step1Hyp_gauss_of_scale''`, `Step1.weakLaw`, `Step2.localLaw`; T1520 (T3′) uses T1517 only.
- **(T3) `RBM.Gauss.steps12_gauss` — PASS.** `steps12_gauss_of_grid`'s proof with
  `step2_gauss` in place of `step2_gauss_of_grid`.
- **(T4) audit `example` — PASS.** Conclusion type written out as `Step2.step2`'s at
  `X := sample d`, `B := band d`; hypothesis list = step2's minus `Hy` (`h1` unused);
  `#print axioms step2_gauss`.

## (b) Declarations, build, axioms

File `RBM1D/Gauss/Step2Close.lean` (branch `t/T1524`, commit `6f56b8c`). Root import not added
(at merge, per ticket).

Public declarations:
- namespace `RBM.Gauss.Grid`: `hreg_endpoint`, `time_eq_time_zero_of_eq`, `H_eq_H_zero_of_eq`,
  `rowSet`, `measurableSet_rowSet`, `highProb_grid_rowSet`, `heG_coef_eq_driftCoef`,
  `mgDrift_nonneg`, `drift_of_goodSet`, `GridAE`, `ae_gridAE`, **`gridPointwise'_gauss` (T1)**;
- namespace `RBM.Gauss`: **`step2_gauss` (T2)**, **`steps12_gauss` (T3)**;
- two `example`s (T4): (a) step2's hypothesis list minus `Hy` (`h1` kept, unused) ⟹ step2's
  conclusion written out at `B := band d`, `X := sample d`; (b) the conclusion type is
  `type_of% (Step2.step2 (sample d) hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg)` (the binder `Hy`
  only names the type; the proof term is `step2_gauss …`, which mentions neither `Hy` nor `h1`).

Signature of (T2) (as printed by `#check`):
`step2_gauss (d) {κ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E} (hEκ : |E| ≤ 2 - κ) {s t}
(hB : BoundsCore (sample d) E s) (hs0) (hst) (ht1) {c} (hc0 : 0 < c) (hreg : ∀ᶠ N, N^c (η_s/η_t)^30 ≤ A_t)`
⟹ `Step2.step2`'s two conjuncts for `sample d`. No `Hy`, no `Step1.Hyp`, no new hypothesis.

Build:
`cd /Users/junyin/Lean_proof/RBM1D-wt/T1524 && lake build RBM1D.Gauss.Step2Close` —
`Build completed successfully (3966 jobs)`. One linter warning: `hκ1` is unused in
`gridPointwise'_gauss` (kept because the ticket fixes (T1)'s hypothesis list to step2's).

Axioms (`#print axioms`, in-file): every declaration above, including `gridPointwise'_gauss`,
`step2_gauss`, `steps12_gauss`, depends on `[propext, Classical.choice, Quot.sound]` only.
No `sorry`/`admit`/`axiom` in the file.

`Hy`-freeness, traced (not name-matched): a metaprogram (scratch file, not committed) collected
the transitive closure of constants used by the type and value of `step2_gauss` (4966 constants),
`steps12_gauss` (4412), `gridPointwise'_gauss` (4984) and searched it for `RBM.Step2.Hyp*`,
`RBM.Step2.step2`, `RBM.Step2.aprioriDecay`: **no hits**. `Step1.Hyp` occurs only as a
constructed value (`step1Hyp_gauss_of_scale''`), never as a hypothesis.

Parameter audit: `D' = max(D+4,64)`, `δ₀ = min(c/24,1)`; `ζ = ζCtr = τ3 = δ/96`, `τ57 = ζ/2`,
`ε = δ/4`, `τ₁ = δ/32`, `K = gridK D' (D₁+2) = max 1 ⌈N^{D₁+2+2D'+80}⌉` (depends only on
`D, D₁`), `C = CK D' (D₁+2) + 2`. All fixed after `(D, u, δ, D₁)` and before `∀ᶠ N`; none
depends on `ω`.

## (c) Key lemmas used

- T1519: `goodEvent_grid` (at `D₁+1`), `goodEvent_grid_imp` (at `D₁+1`), `gridTau_le`,
  `gridK_ne_zero`, `gridK_card_le`, `CK`.
- T1518: `grid_thr_improve` (with endpoint `u`, via `hreg_endpoint`), `driftCoef`, `qGrid`.
- T1515: `drift_point_le_heG`, `drift_point_le_heG_scalars`, `mgDrift_le`.
- T1516: `grid_expansion_all'`, `condExp_A_succ` (via `ae_gridAE`).
- T1520: `min_firstHit_eq_of_at`, `lk_le_of_jS`, `step2_gauss_of_gridPointwise'`.
- T1492/T1513: `Gauss.Step2.highProb_eq557_colRow`, `highProb_flow_restrict`,
  `highProb_grid_of_flow`, `goodSet` components.
- T1521 route for (T3): `step1Hyp_gauss_of_scale''`, `Step1.apriori`, `Step1.weakLaw`.
- Scalars: `Step2.cond272_of_strict`, `Step2.eventually_R4_le_scale`, `SumZeroDyn.flow_crude`,
  `Step2.eventually_le_W_sq`, `flowScale_antitoneOn`, `Step2.etaT_ratio`.

## (d) Open issues

- Interface mismatches 1–9 of §(a) were all bridged inside the sole file; none required a new
  hypothesis or a change to a merged file. The row form of (5.57) (mismatch 3) is an extra
  high-probability event not listed in the ticket's `G N`; it costs one unit of `D₁` in `K`
  (`gridK D' (D₁+2)` instead of `gridK D' (D₁+1)`).
- `step2_gauss` is the general statement (general `Dims`, `E`, windows `s ≤ t < 1`, all `D > 0`);
  it is not a special case. No Lean/paper statement difference, so no `paper-deltas` entry.
- Root import and root axiom audit: at merge (hub).
