Auditor model: claude-opus-5-5[1m]

# T1513 re-audit (after repair): the good set G_j of sigma as matrix sets, and its HighProb on the grid

Branch `t/T1513` at commit `f3dcee0`. This is the repair commit on top of `f31217d`. The merge-base diff against `main` touches one file only: `RBM1D/Gauss/GridGoodSet.lean` (+885 lines).

Audit worktree: a fresh one, `/Users/junyin/Lean_proof/RBM1D-wt/T1513-audit2` (detached at `f3dcee0`). I did not use the repairer's worktree or the earlier audit worktree. The build cache is a `cp -c` clone of main's `.lake/build`. That clone had no `GridGoodSet` olean, so the module was compiled from source.

This audit replaces the earlier RETURN (commit `f31217d`). I did not take either the earlier audit or the repairer's report on trust.

**Overall verdict: PASS.** All four targets (T1)-(T4) are delivered, including the repaired (5.54) piece.

The question of how T1515 uses the residue is a dispatcher decision (section 5). It does not block this ticket.

## 1. Builds, axioms, forbidden tokens, scope

- `lake build RBM1D.Gauss.GridGoodSet` (audit worktree): `Built RBM1D.Gauss.GridGoodSet`, `Build completed successfully (3937 jobs)`. No errors; only linter/style warnings.
- `lake build RBM1D`: `Build completed successfully (9659 jobs)`. The module is not yet imported at the root; the import is added at merge, per the ticket.
- Merge compatibility:
  - Since the branch base `6415b0f`, `main` has only added files (`GridNetLift`, `GridQVForm`, `GridQVSum`, plus root imports). No dependency of this module changed.
  - None of the new files declares any of this module's public names, so adding the root import at merge will not clash.
- `#print axioms` for all 24 public declarations gives `[propext, Classical.choice, Quot.sound]`, 24 out of 24:
  - T1: `jGMat`, `measurable_jGMat`, `jG_eq_jGMat`;
  - T2: `qvSet`, `jgSet`, `rho554`, `rho554_mono`, `rho554_le_two_mul_rpow`, `h554Set`, `mem_h554Set_of_isHermitian`, `honeSet`, `goodSet`, and every `measurableSet_*` lemma;
  - T3/T4: the five `highProb_flow_*` lemmas, `highProb_flow_restrict` and `highProb_grid_goodSet`.
- The file contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern`.
- No other file changed, so no frozen signature was touched.
- The repair diff (`f31217d..f3dcee0`) touches only the module docstring and the `h554` section:
  - new: `rho554`, `rho554_mono`, `rho554_le_two_mul_rpow`, the private helper `sqrt_mul_sqrt_mul_eq`, and `mem_h554Set_of_isHermitian`;
  - changed: the right-hand side of `h554Set`;
  - re-proved: `measurable_h554RHS` and `highProb_flow_h554Set`.
- The following are byte-identical to the version the earlier audit accepted: `jGMat`, `qvSet`/`qvVal`, `jgSet`, `honeSet`, `goodSet`, `highProb_flow_{qv,jg,hone,goodSet}Set`, `highProb_flow_restrict`, `highProb_grid_goodSet`, and the private mirror lemmas.
- Math preflight:
  - The prove report's Part R.1 ("Math preflight (written before any Lean)") is a PASS preflight for the repaired piece. It comes before the Lean section R.2.
  - Part O keeps the original preflight for the unchanged targets.
  - The first line is `Prover model: claude-opus-5-5[1m]`.

## 2. Arithmetic checks, redone from the definitions

The definitions are:
- `tailT W ℓu ηu D ℓ = ((W ℓu ηu)^2)⁻¹ · exp(-√(ℓ/ℓu)) + W^(-D)`, in `Analysis/StretchedExp.lean:281`;
- `ellStar W ℓu = (log W)^(3/2) · ℓu`, in `StretchedExp.lean:290`;
- `Lemma57.ellStarStar W ℓu = (log W)^3 · ℓu`, in `Hierarchy/Lemma57.lean:610`.

Write `A = W ℓu ηu`.

### 2a. The earlier audit's suggested fix rho' was wrong; the repairer is right

The quantity in question is `T_D(ℓ*/2)`:
- `√((ℓ*/2)/ℓu) = (log W)^{3/4}/√2`, so `T_D(ℓ*/2) = A⁻² exp(-(log W)^{3/4}/√2) + W^{-D}`.
- `exp(-(log W)^{3/4}/√2) = W^{-(log W)^{-1/4}/√2}`. This decays more slowly than every fixed power `W^{-ε}`.
- `A ≤ W · L · 1 ≤ N`, so `A⁻²` is at most polynomially small, with a degree that does not depend on `D`.
- Hence `T_D(ℓ*/2)` is **not** `O(poly · W^{-D})` for large `D`.

Consequence for the earlier suggestion `rho' = ηu⁻¹ J √(T_D(ℓ**) T_D(ℓ*/2))`:
- Its size is about `ηu⁻¹ J · W^{-D/2} · A⁻¹ · W^{-o(1)}`.
- Divided by `W^{-D}`, this leaves a factor of about `W^{D/2}/A`. For `D ≥ 60` and `N ≤ W²`, that is at least `W^{28}`.
- This is the same kind of defect the earlier audit raised against the original bound. The earlier audit wrote that rho' has "a W^{-D} floor ... That is the (5.54) size up to polynomial factors". That is incorrect: `W^{-D}` is only a *lower* bound for rho', not its size.
- **The earlier audit's suggested repair was itself flawed.** The repairer was right to reject it.

### 2b. The triangle-inequality split, and whether the Lean implements it faithfully

The mathematics:
- `zdist(a₂-b) ≤ zdist(a₂-a₁) + zdist(a₁-b)`.
- If `zdist(a₂-b) > ℓ**`, then `max(zdist(a₂-a₁), zdist(a₁-b)) > ℓ**/2`. So at least one of the two is `≥ ℓ**/2`.

The Lean (`mem_h554Set_of_isHermitian`):
- `htri` comes from `RBM.zdist_add_le (d.L N) (a₂ - a₁) (a₁ - b)` (`Defs/Dist.lean:33`) after rewriting `a₂ - a₁ + (a₁ - b) = a₂ - b`.
- It then case-splits with `by_cases hA : Lss/2 ≤ zdist(a₂-a₁)`:
  - **Case A:** `G(a₂,a₁)` gets the far bound `√(J·T(Lss/2))`, and `G(a₁,b)` gets the cap `ηu⁻¹`.
  - **Case B:** from `¬hA` and `htri` it derives `Lss/2 ≤ zdist(a₁-b)` by `linarith`. Then `G(a₁,b)` gets the far bound and `G(a₂,a₁)` gets the cap.
- In both cases `G(a₂,b)` gets `√(J·T(Lss))` from `hb`.
- The far bound `hfar` applies `gmBlkMat_le_sqrt_jGMat_tail`, which needs `ℓ*/2 ≤ dist`. The inputs are:
  - `ℓ*/2 ≤ ℓ**/2` (from `ellStar_le_ellStarStar`, using `log W ≥ 1`, and `ℓ* ≥ 0`);
  - then `tailT_antitone` to replace the actual distance by the fixed lengths `Lss` or `Lss/2`.
- The three-factor bound is `norm_gloop_three_le_gmBlkMat`: the (5.60) product `G(a₂,b) G(a₁,b) G(a₂,a₁)`, taken from `Lemma57.norm_gloop_three_le`.
- The final identity `√(J T₁)√(J T₂) η⁻¹ = rho554` is the helper `sqrt_mul_sqrt_mul_eq`.

The split is exactly the claimed one, for all `a₁`, `a₂`, `b`. The degenerate cases work: `a₁ = a₂` falls in Case B, and `a₁ = b` falls in Case A.

### 2c. `rho554_le_two_mul_rpow`: rho554 is genuinely O(W^{-D})

The hypotheses are `2D² ≤ log W`, `A ≥ 1`, `ℓu > 0`, `ηu > 0` and `J ≥ 0`. The argument:
1. `(ℓ**/2)/ℓu = (log W)³/2`, so the exponent is `-(log W)^{3/2}/√2`.
2. `D·log W ≤ (log W)^{3/2}/√2` holds exactly when `D²(log W)² ≤ (log W)³/2`, i.e. when `2D² ≤ log W`. (For `D < 0` it is trivial.)
3. Therefore `exp(-(log W)^{3/2}/√2) ≤ W^{-D}`.
4. With `A⁻² ≤ 1`, this gives `T_D(ℓ**/2) ≤ 2W^{-D}`.
5. `T_D(ℓ**) ≤ T_D(ℓ**/2)` by antitonicity, so `√(T_D(ℓ**) T_D(ℓ**/2)) ≤ T_D(ℓ**/2)`.
6. Hence `rho554 ≤ 2 ηu⁻¹ J W^{-D}`.

The Lean follows exactly these steps (`hin`, `hle`, `hexp`, `hAinv`, `hT2`, `hsq`) and compiles.

Two-sided size:
- There is a matching lower bound `rho554 ≥ ηu⁻¹ J W^{-D}`, from `rpow_neg_le_tailT`.
- So rho554 is of size `W^{-D}` up to the factor `2ηu⁻¹J`.
- It is pointwise `≤` the earlier rho' once `log W ≥ 1`.

The threshold `2D² ≤ log W`:
- At `D = 60` it means `W ≥ e^{7200}`.
- This is the natural threshold for comparing `exp(-c(log W)^{3/2})` with `W^{-D}`; the stretched-exponential comparison forces it.
- For fixed `D` it holds eventually in `N`, with `D` fixed before `∀ᶠ N`, which is the paper's parameter order.
- It appears only in the separate size lemma handed to T1515. It is not a hypothesis of any set, producer, `goodSet` or (T4).
- So it is not a satisfiability loophole: no ticket target depends on it, and the eventual-in-N asymptotics are what the paper asserts for (5.54).
- T1515 must discharge it via `eventually_le_W`.

## 3. Per target

### (T1) `jGMat`, `measurable_jGMat`, `jG_eq_jGMat`: PASS (unchanged)
- `jG_eq_jGMat` holds by `rfl`.
- Measurability uses the `Finset.sup'` / `measurable_Gsig_matrix` pattern.

### (T2)(a) `qvSet`: PASS (unchanged)
- The event is T1497's verbatim, with the harmless gates `u < 1` and `M.IsHermitian`.
- Measurability is genuine: `qvVal` agrees with `quadVar(loopObs)` on the closed Hermitian set, and `quadVar(loopObs)` is continuous.

### (T2)(b) `jgSet`: PASS (unchanged)
- This is T1502's event with the same `D` and `ε`.

### (T2)(c) `h554Set`: PASS
- The set is `{M | M.IsHermitian → ∀ a₁ a₂ b, ℓ**_u < zdist(a₂-b) → ‖gloop … M (zt E u) ⟨[false,true,true],[a₂,b,a₁]⟩‖ ≤ rho554 d E N u D (jGMat d E N u ℓ_u η_u D M)}`.
- It matches T1501's `h554` (`Hierarchy/Step2FarInputsJG.lean:176`) exactly: same loop word, same argument order `[a₂,b,a₁]`, same `ℓ**` at `B.ell N u`, same spectral parameter `zt E u`.
- T1501 needs, for fixed `ω`, one real `ρ ≥ 0` that works for all `b`. Evaluating `rho554` at `J = jGMat(Hflow…)` gives exactly that. `rho554 ≥ 0` because `J ≥ 1`.
- The `J` here is `jGMat` at `(ℓ_u, η_u, D)`. That is the same `(ℓu, ηu, D')` at which T1501's `rhs535` carries `APrimeJG.jG` (by `jG_eq_jGMat`), provided `D' = D`.
- `rho554` is an explicit deterministic function of `(E, N, u, D, J)`.
- `rho554_mono` lets T1515 replace `J` by the deterministic cap `N^{2ε}·thr` available on `jgSet ∩ {jSMat ≤ thr}`. This settles the earlier audit's secondary note.
- `measurableSet_h554Set`: the right-hand side is (constant)·`jGMat`·(constant), and `jGMat` is measurable. PASS.

### (T2)(c) `honeSet`: PASS (unchanged), with a caveat carried forward for T1515
- `κ = 2 N^{ζCtr} ℓu/ℓs` is deterministic, and the producer is `highProb_centeredEvent` + `qExt_eq_q`.
- T1501's `hκ : 2κ ≤ ℓu/ℓs` fails at the same `ℓs`. T1515 must apply T1501 with `ℓs' = ℓs/(4N^{ζCtr})`. I checked that all other T1501 hypotheses only weaken or stay true under this rescaling: `h273`, `h557C/R` and `hr` have right-hand sides that are monotone in `ℓu/ℓs`.
- The cost is an `N^{O(ζ)}` factor. This is inherent to the (4.2) producer and is not a T1513 defect.

### (T2)(d) `goodSet`, `measurableSet_goodSet`: PASS
- It is the six-way intersection `qvSet ∩ jgSet ∩ h554Set ∩ honeSet ∩ eq273Set(n=3) ∩ eq557Set`, with the new `h554Set`.
- Measurability needs `|E| < 2`, which every caller has.

### (T3)(a), (b), (d): PASS (unchanged)
- `highProb_flow_goodSet` combines the six producers with `HighProb.inter`. `h3 := highProb_flow_h554Set d hE2 hs0 ht1 D` has the same `D` as the other pieces.
- The hypotheses are the Step-1 bundle, `hreg`, `60 ≤ D`, and positivity of `τ, ε, ζCtr, τ3, τ57`.

### (T3)(c) `highProb_flow_h554Set`: PASS
- It is deterministic: `HighProb.of_eventually_univ` applied to `eventually_le_W d 3`. That gives `log W ≥ 1`, and together with `ℓ_u ≥ 1` (`one_le_ellHat_of_nonneg`) and `Hflow_isHermitian` it calls `mem_h554Set_of_isHermitian`.
- This is honest: the probabilistic content of (5.54) sits in `jgSet` and the jS threshold, through `J`.
- The signature is unchanged.

### (T4) `highProb_flow_restrict`, `highProb_grid_goodSet`: PASS
- It is stated for an arbitrary endpoint sequence `u : ℕ → ℝ` with `s N ≤ u N ≤ t N`, `K N ≠ 0`, `C ≥ 0` and eventually `K N + 1 ≤ N^C`.
- The route is `highProb_flow_restrict` (a genuine monotonicity lemma), then `highProb_grid_of_flow` with `t := u`, using measurability of every `goodSet` slice.
- Nothing is specialised to one cell, `E = 0`, fixed `D` or `exampleGrow`.

## 4. Vacuity, hidden hypotheses, cycles, dependencies

- **No new probabilistic hypotheses.** The hypotheses are exactly the Step-1 bundle already used by T1497, T1502 and T1507. The nondegenerate witness is the recorded one: `Dims.exampleGrow`, `E = 0`, `s = 0`, a suitable `t < 1` (T1481 pilot), with `K N = N + 1` and `C = 2`.
- **`h554Set` is eventually the whole Hermitian set.** This is a true deterministic theorem, not vacuity. Its bound is nontrivial (`rho554 ≥ ηu⁻¹ J W^{-D} > 0`), and it becomes small only through `J`, which T1515 caps using `jgSet` and the threshold.
- **No loopholes.** There is no `N = 0`, empty-index or collapsed-window loophole: the conclusions are eventual HighProb statements over the non-empty `Fin (K N + 1)`.
- **No hidden hypotheses.** Both gates (`u < 1`, `M.IsHermitian`) always hold where the sets are evaluated. There are no structure-field hypotheses.
- **No cycles.**
- **Dependencies.** All are merged: T1497, T1501, T1502, T1507, `highProb_centeredEvent`, `Lemma57.norm_gloop_three_le`, `tailT_antitone`, `rpow_neg_le_tailT`, `zdist_add_le`.
- **DECISIONS §10b.** The repair adds no new producer dependency. The earlier audit's constant-closure check (no `EarlyQVRateEv.jStar`, no `h560` / `eGpm_le_rhs535_of_jS`) still applies. The repaired proof uses only in-file private lemmas and the merged facts listed above; I checked the diff directly.

## 5. Decision point for the dispatcher (not decided here)

**The claim.** Along this route, T1501's (5.35) residue `(ℓu/ℓs)(ℓu ηu)⁻¹ L ρ` becomes, on `h554Set ∩ jgSet ∩ {jSMat ≤ thr}` with `2D² ≤ log W`,
`≤ 2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L · J_cap · W^{-D}`, where `J_cap = N^{2ε} thr`.
That is `poly(N) · W^{-D}`. It is **not** the "one unit `≤ W^{-D}`" that paper-delta #148 assumed (`hrem` of `rhs535_far_le`).

**Is it true that one unit at the same `D` is impossible through `J`? Verified, with one qualification.**
- Any bound built from far-entry estimates `≤ √(J·T_D(dist))` satisfies `T_D ≥ W^{-D}`. So the two far factors contribute at least `J·W^{-D}`.
- The third factor may be a near or diagonal Green-function entry, which is of order 1. No bound on it can beat `O(1)`; the `ηu⁻¹` cap is sharp up to `ηu`.
- Hence the residue is at least about `(ℓu/ℓs)(L/ℓu) ηu⁻¹ J W^{-D}`. Using `hr: ℓu/ℓs ≥ 1`, `L ≥ ℓu`, `J ≥ 1`, this is at least `W^{-D}`, and it is `≫ W^{-D}` whenever `L/(ℓu ηu) ≫ 1`, which is the regime of interest.
- **Qualification:** this is a statement about bounds routed through `J` and `T_D` at the *same* `D`. It does not say the true size of the far 3-loop cannot be smaller.
- Delta #148's "cost zero" is therefore over-optimistic at the same `D`. This candidate delta (tag `T1513a` in the prove report) still has to be entered into `docs/paper-deltas.md` by the dispatcher.

**Options offered by the repairer, recorded verbatim and not chosen here:**
1. **Additive.** Carry `K_ρ = 2 (ℓu/ℓs) ℓu⁻¹ ηu⁻² L J_cap` into T1515's constant. `K_ρ` is `poly(N)`, not `N^{O(ε)}`, so it may break T1515 (T4)'s `Cdr·N^κ` budget.
2. **D-shift.** Use `goodSet` and T1501 at `D_G = D_T + D₀`, with a fixed `D₀` such that `W^{D₀} ≥ K_ρ` eventually (`N ≤ W²` eventually). Then read the bound through `T_{D_T} ≥ T_{D_G}`, which leaves exactly one unit of `W^{-D_T}`.
   - My check of feasibility only: `goodSet` requires `60 ≤ D`, which `D_G` satisfies.
   - The `J` in `rhs535` is then `J_{D_G}`, so T1515 needs its `J`-cap at `D_G`, where `jgSet` and the threshold provide it.

T1515's own ticket asks only for "ρ ≤ W^{-D}·(…)", and `rho554_le_two_mul_rpow` delivers that. So this choice does not block T1513. It must be settled when T1515 is finalised.

## 6. Verdict

| Target | Verdict |
|---|---|
| (T1) `jGMat`, `measurable_jGMat`, `jG_eq_jGMat` | PASS |
| (T2)(a) `qvSet` | PASS |
| (T2)(b) `jgSet` | PASS |
| (T2)(c) `h554Set` (`rho554`) | PASS |
| (T2)(c) `honeSet` (κ caveat for T1515) | PASS |
| (T2)(d) `goodSet` | PASS |
| (T3)(a)-(d) | PASS |
| (T4) `highProb_flow_restrict`, `highProb_grid_goodSet` | PASS |

**Ticket verdict: PASS.**

Notes carried to the dispatcher and T1515:
- the decision point in section 5;
- the candidate delta `T1513a`;
- the `honeSet` rescaling `ℓs' = ℓs/(4N^{ζCtr})`;
- the eventual hypothesis `2D² ≤ log W` of the size lemma.

The earlier audit's suggested rho' was mathematically flawed (section 2a). The repairer's `rho554` is the correct fix.
