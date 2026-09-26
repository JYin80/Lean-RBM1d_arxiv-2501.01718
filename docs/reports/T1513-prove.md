Prover model: claude-opus-5-5[1m]

# T1513 — good set G_j of σ, as matrix sets, and its HighProb on the grid

This report was rewritten by the **repairer** (claude-opus-5-5[1m]) after the audit RETURN
(`docs/reports/T1513-audit.md`). The only returned piece was the (5.54) input: `h554Set` and
`highProb_flow_h554Set`. `goodSet`, `highProb_flow_goodSet` and `highProb_grid_goodSet` were
returned only because they contain it.
- **Part R** below is the repair: a new math preflight for (T2)(c)/(T3)(c) `h554`, written before
  any Lean, then the Lean results.
- **Part O** keeps the original prover's (claude-sonnet-5) preflight for the unchanged targets
  (T1, T2(a),(b), `honeSet`, T3(a),(b),(d), T4) verbatim. The audit accepted them. The
  superseded `h554` paragraphs of Part O are marked as such.

---

# Part R — repair of (T2)(c) `h554Set` / (T3)(c) `highProb_flow_h554Set`

## R.1 Math preflight (written before any Lean)

### What T1501 consumes

`RBM.Step2FarInputs.eGpm_le_rhs535_of_jG` (`Hierarchy/Step2FarInputsJG.lean:170`) is stated for
fixed `a₁ a₂` and has
```
(h554 : ∀ b, Lemma57.ellStarStar W ℓu < zdist (a₂ - b) →
   ‖gloop L W (X.H N u ω) (zt E u) ⟨[false,true,true],[a₂,b,a₁]⟩‖ ≤ ρ)
(hρ : 0 ≤ ρ)
```
Here `ρ` is a single real for the fixed `ω` (independent of `b`). It enters the conclusion only
through the additive residue `ℓu/ℓs · (ℓu ηu)⁻¹ · L · ρ` of `rhs535`
(`Step2FarInputs.lean:994`). The `J` inside `rhs535` is `jG` at the same `(ℓu, ηu, D')`.

### The defect being repaired (audit, confirmed)

The old bound was `ρ_old = ηu⁻² · √(J · T_D(ℓ**))`. It capped two of the three (5.60) factors at
`ηu⁻¹`, so only one factor decays. Its size is about `ηu⁻² √J W^{-D/2}`, which is only half the
`W^{-D}` floor.

### The audit's fix, checked, and one further sharpening

The audit proposes a split on `|a₁-a₂| ≥ ℓ*/2`. I checked it, and it is correct: it gives
`ρ' = ηu⁻¹ · J · √(T_D(ℓ**) · T_D(ℓ*/2))`.

**However, `ρ'` is *not* of size `W^{-D}`.** By (5.27),
`T_D(ℓ) = A⁻² exp(-√(ℓ/ℓu)) + W^{-D}`, with `A = W ℓu ηu`.
- `T_D(ℓ**) = A⁻² exp(-(log W)^{3/2}) + W^{-D}`. This is `≤ 2W^{-D}` eventually.
- `T_D(ℓ*/2) = A⁻² exp(-(log W)^{3/4}/√2) + W^{-D}`. Its stretched-exponential part is
  `W^{-(log W)^{-1/4}/√2}`, which is larger than every `W^{-ε}`.

So `√(T_D(ℓ**) T_D(ℓ*/2)) ≈ W^{-D/2} · A⁻¹ exp(-(log W)^{3/4}/(2√2))`. The audit's `ρ'` has a
`W^{-D}` *lower* bound, but its actual size is still about `W^{-D/2}`. Divided by `W^{-D}`, this
again leaves a factor of about `W^{D/2}`, which is the same downstream defect.

**Sharper split (used here).** Write `d₂b = zdist(a₂-b)`, `d₂₁ = zdist(a₂-a₁)` and
`d₁b = zdist(a₁-b)`.
- The triangle inequality on `ZMod L`: `a₂ - b = (a₂-a₁) + (a₁-b)`, and `RBM.zdist_add_le` gives
  `d₂b ≤ d₂₁ + d₁b`.
- With `d₂b > ℓ**`, **one of `d₂₁`, `d₁b` is `≥ ℓ**/2`, not just `≥ ℓ*/2`**:
  - Case A: `ℓ**/2 ≤ d₂₁`. Then `G(a₂,a₁)` is the second far factor.
  - Case B: `d₂₁ < ℓ**/2`. Then `d₁b ≥ d₂b - d₂₁ > ℓ**/2`, and `G(a₁,b)` is the second far factor.
- In both cases the (5.60) product `G(a₂,b) G(a₁,b) G(a₂,a₁)` (`norm_gloop_three_le_gmBlkMat`,
  the deterministic (5.60)) has two factors at distance `≥ ℓ**/2 ≥ ℓ*/2`. The far-entry lemma
  `gmBlkMat_le_sqrt_jGMat_tail` (needs distance `≥ ℓ*/2`) applies to both. The third factor gets
  the operator-norm cap `gmBlkMat_le_inv_etaT` (`≤ ηu⁻¹`).
- `tailT_antitone` (needs `ℓu > 0`) turns the distances into the fixed lengths `ℓ**` and `ℓ**/2`.
  Then `√(J T₁) · √(J T₂) = J √(T₁ T₂)`.

**New bound.**
```
rho554 d E N u D J := (etaT E u)⁻¹ * J * √(T_D(ℓ**_u) * T_D(ℓ**_u / 2))
```
with `T_D = tailT (W N) (ℓ_u) (etaT E u) D`, `ℓ_u = (band d).ell N u`,
`ℓ**_u = Lemma57.ellStarStar (W N) ℓ_u`. `h554Set` is evaluated at `J := jGMat … M`.
- **At least as sharp as the audit's `ρ'`.** When `log W ≥ 1` we have `ℓ**/2 ≥ ℓ*/2`, so
  `T_D(ℓ**/2) ≤ T_D(ℓ*/2)` and therefore `rho554 ≤ ρ'`, pointwise.
- **Genuinely of size `W^{-D}`.** `T_D(ℓ**/2) = A⁻² exp(-(log W)^{3/2}/√2) + W^{-D}`. If
  `1 ≤ A`, `0 ≤ D` and `2D² ≤ log W`, then `exp(-(log W)^{3/2}/√2) ≤ exp(-D log W) = W^{-D}`. The
  reason: `(D log W)² ≤ (log W)³/2` exactly when `2D² ≤ log W`. Hence `T_D(ℓ**/2) ≤ 2W^{-D}`.
  Also `T_D(ℓ**) ≤ T_D(ℓ**/2)`. Together:
  `rho554 d E N u D J ≤ 2 · ηu⁻¹ · J · W^{-D}` (Lean: `rho554_le_two_mul_rpow`, deterministic).
  - For fixed `D`, `2D² ≤ log W` holds eventually in `N`, because `W → ∞` (`eventually_le_W`).
    This is the paper's asymptotic regime: (5.54) is "stretched-exponentially small up to
    `W^{-D}`".
  - The threshold is large for `D ≥ 60` (`W ≥ e^{7200}`). It is **not** a hypothesis of any
    target in this ticket. It is only a hypothesis of the separate size lemma handed to T1515.
- **Floor.** `rho554 ≥ ηu⁻¹ J W^{-D}`, by `rpow_neg_le_tailT`. So `W^{-D}` is both the floor and
  the size, up to the factor `2ηu⁻¹J`.
- **Loses only one `ηu⁻¹`.**

### Secondary audit note (deterministic parametrization)

I took option 1 of the audit. `rho554 d E N u D J` is a public `def`, an explicit deterministic
function of `(E, N, u, D, J)` alone. `h554Set` uses it at `J := jGMat d E N u ℓ_u η_u D M`, and
the docstring says so. `rho554` is linear and monotone in `J` (`rho554_mono`). So on
`jgSet ∩ {jSMat ≤ thr}`, T1515 can replace `J` by the deterministic cap `N^{2ε} · thr`
(`jgSet` gives `jGMat ≤ N^{2ε} jSMat`).

### Residue handed to T1515 (candidate `docs/paper-deltas.md` entry, tag `T1513a`)

On `h554Set`, apply `rho554_le_two_mul_rpow`, then cap `J ≤ J_cap := N^{2ε}·thr` using `jgSet`
and the jS threshold. T1501's residue is then
```
ℓu/ℓs · (ℓu ηu)⁻¹ · L · ρ  ≤  2 · (ℓu/ℓs) · ℓu⁻¹ · ηu⁻² · L · J_cap · W^{-D}   (= poly(N) · W^{-D}).
```
This is **not** the "one unit `≤ W^{-D}`" that delta #148 (`hrem` of `rhs535_far_le`) assumed.
- **It is intrinsic to any `J`-based route.** Every far entry is bounded by `√(J T_D)`, and
  `T_D ≥ W^{-D}`. So any `ρ` obtained this way satisfies `ρ ≥ ηu⁻¹ J W^{-D}`. The residue is then
  `≥ (ℓu/ℓs) L ℓu⁻¹ ηu⁻² J W^{-D} > W^{-D}`, because `L ≥ ℓu`, `ηu ≤ 1` and `J ≥ 1`. No repair of
  T1513 alone can give one unit **at the same `D`** as `J` and `T` in `rhs535`.
- **T1515 does not need one unit.** Its ticket, (T3) route, says: "`ρ ≤ W^{-D}·(…)` suffices".
  So this is **not BLOCKED**. There are two ways to use it:
  1. **Additive constant.** `rhs535 ≤ (M_gf + K_ρ) · T_D` with
     `K_ρ := 2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L J_cap`.
     Caveat for T1515 (T4): `K_ρ` is `poly(N)`, not `N^{O(ε)}`. It is larger than `M_gf` by
     roughly `L/(ℓu ηu)`. So it may not fit T1515 (T4)'s `Cdr · N^κ` budget.
  2. **Fixed `D`-shift (recommended).** Pick `D₀` with `W^{D₀} ≥ 2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L J_cap`
     eventually. `D₀` is a fixed constant, because the right side is `≤ N^{p}` for an explicit
     `p` and `N ≤ W²` eventually (`Step2.eventually_le_W_sq`); so `D₀ = 2p` works. Then use
     `goodSet` and T1501 at `D_G := D_T + D₀`, and read the result with `T_{D_T}`:
     - `T_{D_G} ≤ T_{D_T}`;
     - the residue is `≤ poly(N) W^{-D_G} ≤ W^{-D_T} ≤ T_{D_T}`, which is exactly one unit;
     - so `‖D b‖ ≤ (M_gf(J_{D_G}) + 1) T_{D_T}(b)`.
     The cost is a fixed shift of `D`. This is the paper's usual "`D` arbitrary, `W^{-D}·poly(N)`
     negligible" convention, made explicit.
  The dispatcher should choose between 1 and 2 when finalizing T1515.

### Hypotheses, boundary cases, satisfiability

- **`h554Set` membership.** `h554Set d E N u D` contains every Hermitian `M` provided:
  - `|E| < 2` and `u < 1` (so `etaT E u > 0`, for the `ηu⁻¹` cap);
  - `1 ≤ log W` (so `ℓ* ≤ ℓ**`), which holds once `W ≥ 3 > e`;
  - `ℓ_u > 0` (for `tailT_antitone`); `ℓ_u ≥ 1` holds for `0 ≤ u < 1`.
  All of these are deterministic and hold eventually for every flow time `u ∈ [s N, t N]`. The
  set is gated by `M.IsHermitian →`, exactly as before; `Hflow` is always Hermitian.
- **Producer.** Deterministic, as before: `HighProb.of_eventually_univ`, eventually in `N`
  (`eventually_le_W d 3`). This is honest. The paper's (5.54) is a deterministic consequence of
  (5.60) and the `J`-bounds; the probabilistic content sits in `jgSet` and the jS threshold.
- **Boundary cases.**
  - If no `b` has `d₂b > ℓ**` (small `L`), the statement is vacuous for that `a₂`, but still a
    true set membership. There is no `N = 0` or empty-index loophole in the HighProb statement.
  - Case A/B covers `a₁ = a₂` (then `d₂₁ = 0`, Case B, `d₁b = d₂b > ℓ**`) and `a₁ = b`
    (then Case A, since `d₂₁ = d₂b > ℓ**/2`).
- **Satisfiability.** No new probabilistic hypothesis. `highProb_flow_h554Set` keeps its old
  signature (`|E| < 2`, `0 ≤ s`, `t < 1`, `D`). The downstream hypotheses remain the Step-1
  bundle, whose nondegenerate witness is the one already recorded (`Dims.exampleGrow`, `E = 0`,
  `s = 0`, suitable `t < 1`).
  - The size lemma `rho554_le_two_mul_rpow` has these deterministic hypotheses:
    `1 ≤ W ℓ_u η_u`, `0 ≤ D`, `2D² ≤ log W`, `0 < ℓ_u`, `|E| < 2`, `u < 1`, `0 ≤ J`.
  - They are jointly satisfiable: take `W` large, `ℓ_u = 1`, `η_u ∈ (0,1]` with `W η_u ≥ 1`,
    `D = 60`, `log W ≥ 7200`. They hold eventually along the Step-1 witness, because
    `1 ≤ A` follows from `hreg` and `W → ∞`.
  - The large threshold is flagged above (it is `2D²`, a consequence of the stretched exponent
    `3/2` of `ℓ**`).
- **Dependencies.** Only deterministic facts that are already in the file, or already merged:
  `Lemma57.norm_gloop_three_le` via `norm_gloop_three_le_gmBlkMat`, `gmBlkMat_le_sqrt_jGMat_tail`,
  `gmBlkMat_le_inv_etaT`, `tailT_antitone`, `rpow_neg_le_tailT`, `RBM.zdist_add_le`. There is no
  `jStar` / `EarlyQVRateEv.jStar` and no `h560` / `eGpm_le_rhs535_of_jS`.

### Verdict (repair targets)

- (T2)(c) `h554Set` with `ρ = rho554(E,N,u,D; J := jGMat M)`: **PASS**.
- (T3)(c) `highProb_flow_h554Set` (deterministic, two-far-factor split at `ℓ**/2`): **PASS**.
- (T2)(d) / (T3)(d) / (T4) re-composition: **PASS**. The signatures of `h554Set`,
  `highProb_flow_h554Set`, `goodSet`, `highProb_flow_goodSet` and `highProb_grid_goodSet` are
  unchanged.
- Residue for T1515: `poly(N) · W^{-D}` (explicitly `2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L J · W^{-D}`), not one
  unit. This is not a blocker (T1515's ticket asks only `ρ ≤ W^{-D}·(…)`). The `D`-shift gives
  one unit if needed. Recorded as candidate delta `T1513a`.

## R.2 Lean (repair)

- File: `RBM1D/Gauss/GridGoodSet.lean`, the sole writable file, in worktree
  `/Users/junyin/Lean_proof/RBM1D-wt/T1513`, branch `t/T1513`.
- Commit: `f3dcee0` ("T1513: repair h554Set - two-far-factor (5.54) bound rho554 with W^{-D}
  size"), on top of the original `f31217d`.
- Changes: only the `h554` section and the module docstring. `jGMat`, `qvSet`, `jgSet`,
  `honeSet`, the other producers and the private mirror lemmas are untouched.

### Declarations (namespace `RBM.Gauss.Grid`)

New, public:
- `rho554 (E) (N) (u D J : ℝ) : ℝ := (etaT E u)⁻¹ * J * √(tailT W ℓ_u η_u D ℓ** * tailT W ℓ_u η_u D (ℓ**/2))`.
  This is the explicit deterministic `ρ` of the (5.54) input.
- `rho554_mono` (`0 < etaT E u`, `J ≤ J'` ⟹ `rho554 … J ≤ rho554 … J'`). This lets T1515 replace
  `J` by the cap from `jgSet ∩ {jSMat ≤ thr}`.
- `rho554_le_two_mul_rpow`: from `0 < etaT E u`, `0 < ℓ_u`, `1 ≤ W ℓ_u η_u`,
  `2 D² ≤ log W` and `0 ≤ J`, conclude `rho554 … J ≤ 2 (etaT E u)⁻¹ J W^{-D}`. This is the
  genuine `W^{-D}` size. The preflight also listed `0 ≤ D`; the proof does not need it, so it was
  dropped, which makes the lemma strictly stronger.
- `mem_h554Set_of_isHermitian`: from `|E| < 2`, `u < 1`, `0 < ℓ_u`, `1 ≤ log W` and
  `M.IsHermitian`, conclude `M ∈ h554Set d E N u D`. This is the deterministic (5.54) via the
  two-far-factor split at `ℓ**/2`, for all `a₁, a₂`.

Changed statement (same name and same parameters `(E N u D)`):
- `h554Set`: the right side is now `rho554 d E N u D (jGMat d E N u ℓ_u η_u D M)`.

Unchanged signatures, re-proved:
- `measurableSet_h554Set`;
- `highProb_flow_h554Set`: now a one-line application of `mem_h554Set_of_isHermitian`, after the
  same eventual facts `W ≥ 3 ⟹ log W ≥ 1`, and `ℓ_u ≥ 1`.

Unchanged, re-checked by the build: `goodSet`, `measurableSet_goodSet`,
`highProb_flow_goodSet`, `highProb_grid_goodSet`.

New private helper: `sqrt_mul_sqrt_mul_eq` (`√(J T₁) √(J T₂) = J √(T₁ T₂)`).

### Build and axioms

- `cd /Users/junyin/Lean_proof/RBM1D-wt/T1513 && lake build RBM1D.Gauss.GridGoodSet` gives
  **`Build completed successfully (3937 jobs)`**. There are no errors; the only warnings are
  linter/style warnings.
- There is no `sorry`, `admit` or `axiom` in the file (checked by grep).
- `#print axioms` was run with `lake env lean` on a scratchpad file outside the worktree. All 24
  public declarations give `[propext, Classical.choice, Quot.sound]`:
  - T1: `jGMat`, `measurable_jGMat`, `jG_eq_jGMat`;
  - T2 sets: `qvSet`, `measurableSet_qvSet`, `jgSet`, `measurableSet_jgSet`;
  - the (5.54) piece: `rho554`, `rho554_mono`, `rho554_le_two_mul_rpow`, `h554Set`,
    `measurableSet_h554Set`, `mem_h554Set_of_isHermitian`;
  - the remaining sets: `honeSet`, `measurableSet_honeSet`, `goodSet`, `measurableSet_goodSet`;
  - T3/T4: `highProb_flow_qvSet`, `highProb_flow_jgSet`, `highProb_flow_h554Set`,
    `highProb_flow_honeSet`, `highProb_flow_goodSet`, `highProb_flow_restrict`,
    `highProb_grid_goodSet`.
- I did not run the root `lake build RBM1D`: the module is not imported at the root until merge,
  and no other file changed.

### Key lemmas used

- `norm_gloop_three_le_gmBlkMat`, i.e. (5.60) via `Lemma57.norm_gloop_three_le`;
- `gmBlkMat_le_sqrt_jGMat_tail` (far entry `≤ √(J T)`, needs distance `≥ ℓ*/2`);
- `gmBlkMat_le_inv_etaT` (`RBM.norm_Gsig_le`);
- `ellStar_le_ellStarStar`;
- `RBM.zdist_add_le` (the triangle inequality on `ZMod L`);
- `tailT_antitone`, `tailT_nonneg`;
- `Real.rpow_def_of_pos`, `Real.le_sqrt_of_sq_le`, `inv_le_one_of_one_le₀`.

## R.3 Open issues / notes for the dispatcher and T1515

1. **Candidate paper-delta `T1513a`: the residue size T1515 actually gets.** This is not written
   to `docs/paper-deltas.md`, which is outside my scope.
   - On `h554Set ∩ jgSet ∩ {jSMat ≤ thr}`, with `2D² ≤ log W` (eventual in `N`), T1501's (5.35)
     residue is
     `ℓu/ℓs · (ℓu ηu)⁻¹ · L · ρ ≤ 2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L · N^{2ε} thr · W^{-D}`. That is
     `poly(N) · W^{-D}`, **not** the one unit `≤ W^{-D}` assumed in delta #148 / `hrem` of
     `rhs535_far_le`.
   - One unit at the **same** `D` is impossible along any `J`-based route, because
     `ρ ≥ ηu⁻¹ J W^{-D}` is forced by `T_D ≥ W^{-D}` (see R.1).
   - T1515's ticket asks only `ρ ≤ W^{-D}·(…)`, so this is not a blocker. T1515 has two options:
     - (1) carry the additive `K_ρ = 2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L J_cap` into `Mdr`. `K_ρ` is `poly(N)`,
       which may break (T4)'s `N^κ` budget.
     - (2, recommended) use `goodSet` and T1501 at `D_G = D_T + D₀`, with a fixed `D₀` such that
       `W^{D₀} ≥ K_ρ` eventually (possible since `N ≤ W²` eventually). Then read the bound with
       `T_{D_T} ≥ T_{D_G}`; the residue is exactly one unit of `W^{-D_T}`.
2. **Correction to the audit's `ρ'`.** The audit's split at `ℓ*/2` gives
   `ρ' = ηu⁻¹ J √(T(ℓ**) T(ℓ*/2))`. Its size is still about `W^{-D/2}`, because
   `T(ℓ*/2) ≈ A⁻² exp(-(log W)^{3/4}/√2)` is not polynomially small in `W`. `rho554` splits at
   `ℓ**/2` instead, which the triangle inequality also allows. It is `≤ ρ'` pointwise and is
   genuinely `≤ 2ηu⁻¹ J W^{-D}`.
3. **Size threshold.** `rho554_le_two_mul_rpow` needs `2D² ≤ log W`, i.e. `W ≥ e^{7200}` at
   `D = 60`. This holds eventually for fixed `D` (the paper's asymptotic regime, (5.54)), but it
   is astronomically large. It is a hypothesis only of this separate size lemma, never of a set,
   a producer or `goodSet`.
4. **Carried over from the audit, for T1515:** `honeSet`'s `κ = 2 N^{ζCtr} (ℓu/ℓs)` requires T1501
   to be applied with `ℓs' = ℓs/(4 N^{ζCtr})`, because `hκ` fails at `ℓs` itself.
5. **Satisfiability.** No new probabilistic hypothesis. `highProb_flow_h554Set` keeps its old
   signature. The Step-1 witness recorded in Part O / the audit still applies.

---

# Part O — original preflight for the unchanged targets (claude-sonnet-5; accepted by the audit)

## Math preflight (before any Lean)

Sources read: `RBM1D/Gauss/GridJStar.lean` (jSMat, eq273Set, eq557Set, highProb_grid_of_flow),
`RBM1D/Gauss/Step2QVEvent.lean` (T1497, `highProb_quadVar_diagShape_of_jS`),
`RBM1D/Gauss/Step2JGle.lean` (T1502, `highProb_jG_le_jS`),
`RBM1D/Hierarchy/Step2FarInputsJG.lean` lines 150–221 (T1501, `eGpm_le_rhs535_of_jG`, and the
underlying `RBM.Step2FarInputs.eGpm_le_rhs535`/`eGpm_le_reduced` signature for `h554`'s exact
role), `RBM1D/Gauss/APrimeJG.lean` (`jG`, `gmBlk`, `gsqBlk`, and their algebraic lemmas),
`RBM1D/Gauss/APrimeGeneralMovingCarrierCore.lean` (the `def jG/gmBlk/gsqBlk` bodies),
`RBM1D/Gauss/APrimeGeneralMovingDriftSourceGeneralDims.lean` (`pointwise_source_package`,
`pointwise_near_source_bound`, `pointwise_far_source_bound` — where `h554`/`hone` actually get
used in the paper's argument), `RBM1D/Gauss/APrimeDriftNearTriple.lean`
(`gaussian_three_near_far_le`, `gmBlk_comm`, `gmBlk_le_sqrt_jG_tail`),
`RBM1D/Gauss/APrimeAllTimeOneLoopGeneralDims.lean` (`centeredEvent`, `highProb_centeredEvent`,
`qExt`), `RBM1D/Gauss/APrimeCenteredModulusGeneralDims.lean` (`centeredTrace`),
`RBM1D/Gauss/EarlyQVRate.lean` (`quadVar_lkFun_eq_quadVar_loopObs`,
`coordD1_lkFun_eq` — the Hermitian-only bridge from the raw `lkFun` to the globally-regular
`loopObs`), `RBM1D/Gauss/LoopC2.lean` (`testFun_loopObs_of_im_le`, giving `TestFun` for
`loopObs`, globally, whenever `z.im ≠ 0`), `RBM1D/Gauss/TestFunHerm.lean` (explicit statement
that the *raw*, unregularised `lkFun`/`gloop` is **not** globally `TestFun`: the resolvent is
discontinuous off the Hermitian set), `docs/DECISIONS.md` §10b, `docs/supervisor/2026-09-26-0048.md`
§1e/§2.

### Step 0 (§10b reuse-rule check for T3(c), done first as instructed)

Candidates named by the ticket:
- `Gauss/APrimeGeneralMovingDriftSourceGeneralDims.lean:75,141,362,477` (`commonEvent`,
  `pointwise_source_package`, `pointwise_far_source_bound`, `pointwise_near_source_bound`).
- `APrimeDriftNearTriple.gaussian_three_near_far_le`.

Grep of `jStar`/`h560` in the whole dependency closure of these files
(`APrimeGeneralMovingDriftSourceGeneralDims.lean`, `APrimeJG.lean`,
`APrimeAllTimeOneLoopGeneralDims.lean`, `APrimeDriftNearTriple.lean`,
`APrimeCenteredModulusGeneralDims.lean`): the only two hits are (i) a docstring in
`APrimeJG.lean` explicitly stating this file's whole purpose is to **avoid**
`EarlyQVRateEv.jStar`, and (ii) a **local `have h560 : ...`** inside
`APrimeGeneralMovingDriftSourceGeneralDims.lean:465`, which is a `rename`-collision on the label
`h560` for the *(5.60) deterministic fact itself* (`∀ b, L3 b ≤ Gm a2 b * Gm a1 b * Gm a2 a1`,
proved unconditionally, no assumption), **not** the suspect hypothesis
`RBM.Step2FarInputs.eGpm_le_rhs535_of_jS`'s `h560` assumption flagged in §10b. Neither candidate
goes through `jStar`/`EarlyQVRateEv.jStar` or through `eGpm_le_rhs535_of_jS`/its `h560`
hypothesis. **Verdict: both candidates pass Step 0.** Both are stated for arbitrary `d : Dims`
(not `Dims.exampleGrow`), and both are pointwise/continuum-uniform-in-`u` (no dependence on a
frozen `exampleGrow`-only object).

Refinement found during the preflight: `gaussian_three_near_far_le` requires an extra hypothesis
`hnear : zdist(a₂-a₁) ≤ ellStar(...)` (it is literally the deterministic fact used **inside**
`pointwise_near_source_bound`, the *near-`a₁,a₂`* branch of (5.35); the far branch,
`pointwise_far_source_bound`, uses a different deterministic chain, `h560`+`h531`+`h42`, not
`h554`). Since T1501's own `h554` hypothesis is asked **unconditionally in `a₁,a₂`** (see
`Step2FarInputs.eGpm_le_rhs535`'s signature, `Hierarchy/Step2FarInputs.lean:1124`), a matrix set
built only from the near case would be **narrower than what T1501 needs**. The preflight
therefore uses a *different*, fully general (`∀ a₁ a₂`) deterministic chain instead, built from
already-proved, Sample-independent building blocks: `Lemma57.norm_gloop_three_le` (h560, no
Hermitian/Sample dependence — a pure algebraic fact about a matrix `M`),
`RBM.norm_Gsig_le` (needs `M.IsHermitian`, direct on `M`, not through `Sample`) for the crude cap
`gmBlk ≤ (etaT)⁻¹`, and `APrimeJG`'s definitional facts `gsqBlk_le_jG_mul_tailT`/
`gmBlk_mul_swap_le_gsqBlk` (pure `Finset.sup'` algebra, no Hermitian needed) together with
`tailT_antitone` to convert the "very far" hypothesis `ellStarStar < zdist` into the "far"
hypothesis `ellStar/2 ≤ zdist` these need. All of these take a matrix `M` (with, at most, an
explicit `M.IsHermitian` hypothesis) directly — none of them are tied to a `Sample`, so they
transplant verbatim to matrix-set language. **This is the producer actually used below for
`h554Set`; it needs its own from-scratch matrix-level lemmas (mirrors of `gmBlk`/`gsqBlk`'s
algebra), listed in the Lean section.**

### T1 (`jGMat`, `measurable_jGMat`, `jG_eq_jGMat`)

`jG`/`gmBlk`/`gsqBlk` (`APrimeGeneralMovingCarrierCore.lean:138-160`) are functions of a matrix
`X.H N u ω` only through that one argument (no other `ω`-dependence, no Hermitian hypothesis
used in their *definitions*, only `Finset.sup'`s of `‖Gsig M z ...‖`). Exactly as `jSMat` mirrors
`Step2.jS`, defining `gmBlkMat`/`gsqBlkMat`/`jGMat` by literally substituting `M` for `X.H N u ω`
throughout reproduces the same term up to the rewrite `(sample d).H N u ω = Hflow d N u ω`
(`Gauss.sample_H`, `rfl`) and `(band d).W N = d.W N`/`(band d).L N = d.L N`/`(band d).W_pos N =
d.W_pos N` (all `rfl`, since `band d`'s fields are literally assigned from `d`'s,
`Model.lean:388-398`). So `jG_eq_jGMat` closes by `rfl`, exactly as `jS_eq_jSMat` does.
Measurability is the same `Finset.sup'`-of-measurable-pieces argument as `measurable_jSMat`,
using `measurable_Gsig_matrix` (already proved, `GridJStar.lean:68`) in place of
`measurable_gloop_matrix`. **PASS.**

### T2(a) `qvSet` — the hard target

`quadVar (band d).toDims N (fun M' => lkFun ... M' sigPM a) M` involves `coordD1`, i.e.
`fderiv ℝ (lkFun ...) M`. `TestFunHerm.lean`'s docstring is explicit that the *raw* `lkFun`
(`gloop`, unregularised) is **not** `TestFun` on the whole matrix space: the resolvent is
discontinuous at singular non-Hermitian points, so a naive "prove `Measurable (quadVar ∘ lkFun)`
on all of `Matrix (d.Idx N) (d.Idx N) ℂ`" by continuity is **false** as stated. However:
`EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs` proves, **at every Hermitian `M`** (and
`(zt E u).im ≠ 0`), that `quadVar(lkFun) M = quadVar(loopObs) M`, where `loopObs = gloop ∘
hermCLM` is the Hermitian regularisation; and `LoopC2.testFun_loopObs_of_im_le` proves
`TestFun d N (loopObs d N z I)` **globally** (every `M`, Hermitian or not) whenever `z.im ≠ 0`
and `I.WF` (`LoopData.idx_wf`, unconditional) and `1 ≤ I.a.length` (here `= 2`). Since `Hflow d N
u ω` is *always* Hermitian (`Hflow_isHermitian`), the two facts combine cleanly: define

```
qvVal d E N u a M := if hM : M.IsHermitian then
    quadVar (band d).toDims N (fun M' => lkFun (band d) E N u M' sigPM a) M
  else 0
```

Then (i) `qvVal ... (Hflow d N u ω) = quadVar(lkFun)(Hflow d N u ω)` **exactly** (literal `dif_pos`
unfolding, no approximation — this is the term T1497 is about), and (ii) `qvVal` is globally
measurable because it equals `fun M => if M.IsHermitian then quadVar(loopObs) M else 0`
pointwise (via the equality lemma inside the `IsHermitian` branch), and `quadVar(loopObs)` is
globally *continuous* (a finite sum of `‖coordD1 (loopObs) M q‖²`, each continuous via a new
one-line `continuous_coordD1_arg` mirroring `GridOneStep.continuous_coordD2_arg`, one derivative
level down), and `{M | M.IsHermitian}` is closed (`{M | Mᴴ = M}`, `isClosed_eq` of two
continuous maps), hence measurable. This needs one new elementary continuity lemma
(`continuous_coordD1_arg`) that does not exist yet (only the `coordD2` version does), proved by
the identical one-liner one derivative level down; everything else (`TestFun`, the equality
lemma) is already committed. **PASS, with the qualification that `qvSet`'s defining predicate
uses the helper `qvVal` (not a bare inlined `quadVar(lkFun)`) for measurability; `qvVal` agrees
with `quadVar(lkFun)` exactly on the Hermitian set, which is all `Hflow` ever produces — recorded
as a delta below, not a change of mathematical content on the only matrices this set is ever
evaluated at.**

### T2(b) `jgSet`

`{M | jGMat ... M ≤ N^{2ε} · jSMat ... M}`. Both sides already measurable (T1, and
`measurable_jSMat` from `GridJStar.lean`). **PASS.**

### T2(c) `h554Set`, `honeSet`

`hone`: `pointwise_source_package`'s local `hone` (line 206) is definitionally
`APrimeCenteredModulusGeneralDims.centeredTrace`, and `hcoef` (lines 220-232) computes exactly
`csrc = κ·(W·ℓu·ηu)⁻¹` with `κ := 2·N^ζCtr·(ℓu/ℓs)` (a function of `(E,N,u,ℓs,ζCtr)` only, no `M`
dependence — matches "κ given as an explicit deterministic function"). The flow producer is
`APrimeAllTimeOneLoopGeneralDims.highProb_centeredEvent`(+`qExt_eq_q`), general `Dims`, no
`jStar`/`h560`. **PASS.**

**[SUPERSEDED by Part R — the bound below was returned by the audit.]** `h554`: per Step 0 above, using the general (`∀ a₁ a₂`) crude chain instead of the near-only
`gaussian_three_near_far_le`. All ingredients (`Lemma57.norm_gloop_three_le`, `RBM.norm_Gsig_le`,
`APrimeJG.gsqBlk_le_jG_mul_tailT`/`gmBlk_mul_swap_le_gsqBlk`'s *statements*, `tailT_antitone`,
`Real.rpow_le_rpow_of_exponent_le` for `ellStar ≤ ellStarStar`) are already-proved, Dims/Band-
generic, Sample-independent facts; the new work is re-deriving their `gmBlk`/`gsqBlk` analogues
at the bare-matrix level (`gmBlkMat`, `gsqBlkMat`, needed anyway for T1's `jGMat`) plus the four
short algebraic mirrors (`norm_Gsig_le_gmBlkMat`, `gmBlkMat_comm` [needs `M.IsHermitian`, via
`APrimeJG.norm_Gsig_eq_green_or_swap`, which already takes `M` directly, not a `Sample`],
`gsqBlkMat_le_jGMat_mul_tailT`, `gmBlkMat_le_sqrt_jGMat_tail`, `gmBlkMat_le_inv_etaT` [needs
`M.IsHermitian`, via `RBM.norm_Gsig_le`, again already stated for a bare Hermitian matrix]). The
resulting deterministic bound is **true for every `ω`** (indeed every Hermitian `M`), so its
"flow producer" is not a genuine probability statement — it is discharged by
`HighProb.of_eventually_univ`, already in `Defs/StochDom.lean`. Gated behind `M.IsHermitian → …`
at the top of `h554Set`'s defining predicate (harmless off the only matrices `Hflow` ever
produces, needed only so the *set* is well-defined without invoking `Sample`). **PASS.**

### T3(a),(b),(d)

`highProb_quadVar_diagShape_of_jS` (T1497) and `highProb_jG_le_jS` (T1502) are *already*
continuum-uniform (`∀ u : TimeIcc s t N`) statements for arbitrary `d : Dims`, and neither
mentions `jStar`/`h560`/`EarlyQVRateEv`. Transfer to `Hflow ∈ qvSet`/`jgSet` is the rewrite
`jS_eq_jSMat`/`jG_eq_jGMat` (`rfl`) plus, for `qvSet`, the `dif_pos (Hflow_isHermitian ...)`
unfolding noted above. `HighProb.inter`, applied four/six times with a small set-level gluing
lemma (`∀u, ω∈A(u)) ∧ (∀u, ω∈B(u)) ↔ ∀u, ω∈(A(u)∩B(u))`), assembles (a)-(c) with the already-
committed `eq273Set`/`eq557Set` flow producers (`highProb_flow_eq273`/`highProb_flow_eq557`,
`n := 3` for the former) into one `HighProb` statement about `goodSet`. **PASS.**

### T4

`highProb_grid_of_flow` (`GridJStar.lean:214`) is exactly the tool, generic in the matrix-set
family `S`. The "window restriction" is the stated one-line monotonicity fact (`TimeIcc s u N →
TimeIcc s t N` coercion when `u N ≤ t N`, since `Set.Icc (s N) (u N) ⊆ Set.Icc (s N) (t N)`).
**PASS**, modulo the (large, but mechanical) task of threading through the union of hypotheses
that T1497/T1502/`highProb_centeredEvent`/`highProb_flow_eq273`/`highProb_flow_eq557` each already
require (Step-1 hypotheses, `hreg`, `D ≥ 60`, per the ticket).

### Simultaneous satisfiability

All hypotheses reduce to the Step-1 hypothesis bundle already discharged (and shown
simultaneously satisfiable) by T1497/T1502/T1507/`highProb_centeredEvent`: `hκ : 0 < κ`,
`hE : |E| ≤ 2-κ`, `hB : BoundsCore`, `hs0/hst/ht1 : 0 ≤ s ≤ t < 1`, `hcond : Cond272`,
`hc0/hreg`, `D ≥ 60`. `Dims.exampleGrow` under `E = 0`, `s ≡ 0`, suitable `t`, is the
already-exhibited nondegenerate witness (T1481 pilot, reused verbatim by T1497/T1501/T1502);
none of the new hypotheses here (`M.IsHermitian` gates, `hlogW`-type facts) are new *assumptions*
on the probability space — they are either always true (`Hflow` is Hermitian) or already-derived
eventual facts (`(band d).eventually_le_W`).

## Verdict

T1: PASS. T2(a)-(d): PASS (qvSet needs the `qvVal`/Hermitian-gate construction, recorded as a
minor implementation delta, not a weakening of the target — see the module docstring).
T3(a),(b),(d): PASS. T3(c) [`h554` part SUPERSEDED by Part R]: PASS, using the general (`∀a₁,a₂`) crude-bound producer instead of
the near-only `gaussian_three_near_far_le` (documented above; neither producer goes through
`jStar`/`h560`). T4: PASS.

