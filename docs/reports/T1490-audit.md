Auditor model: claude-opus-5-5[1m]

# T1490 audit: one-step conditional variance (the discrete (5.25))

Audited: branch `t/T1490` at `30183c8`, in a detached audit worktree `RBM1D-wt/T1490-audit`. The diff against `main` is one new file, `RBM1D/Gauss/GridOneStepVar.lean` (473 lines). `RBM1D.lean` and all other files are untouched. The branch base is `2d74056`. `GridOneStep.lean`, `MomentGronwall.lean` and `Generator.lean` have not changed between that base and current `main`. Audit time: 2026-09-25T19:16Z.

## Verdicts

| Target | Verdict |
|---|---|
| `RBM.Gauss.TestFun.normSq` (Step 0 (b) helper) | PASS |
| (T1) `RBM.Gauss.Grid.genPt_normSq` | PASS |
| (T2) `RBM.Gauss.Grid.oneStep_var_le` | PASS |

## 1. Math preflight
Section (a) of `docs/reports/T1490-prove.md` records a math preflight PASS for T1 and T2. It was written before the Lean and includes the Step 0 checks (a)–(c). It also flags the one departure from the ticket's proof sketch: a case split at `Δ = 1`, needed because `oneStep_error_le` holds for every `Δ ≥ 0`. This changes the proof only, not the statement.

## 2. Statement vs source and ticket
- Source: `pilot-P4P5-paper.md` §4 gives `v_j = Δ·Σ_α S_α|∂_α f|² + O(·)`, the (5.22)/(5.25) integrand.
- **T1.** `genPt d N (fun A => ((‖Φ A‖^2:ℝ):ℂ)) M = ((2 * (conj (Φ M) * genPt d N Φ M).re + quadVar d N Φ M : ℝ) : ℂ)`.
  - The only hypothesis is `TestFun d N Φ`, and `M` is arbitrary.
  - This is exactly the ticket's formula. The function is coerced to `ℂ`, as the ticket's Step 0 (b) allows.
- **T2.** Everything the ticket asks for is in the statement:
  - hypotheses: `TestFun d N Φ`, `M.IsHermitian`, `0 ≤ Δ`, and the T1486 (T3) Lipschitz hypothesis, in the same form as `oneStep_error_le`, for `Φ` (constant `Λ₁`) and for `‖Φ‖²` (constant `Λ₂`);
  - `Var` is literally `∫ ‖Φ(M+√Δ X) − ∫ Φ(M+√Δ X)‖² dP`;
  - the main term is exactly `Δ * quadVar d N Φ M`. This is `RBM.Gauss.quadVar` (`MomentGronwall.lean:349`), the only `quadVar` definition in the repo, and `secondOrder_eq_quadVar` identifies it with the (5.25) integrand `quadVarPairs`;
  - the error is `C_var * (Δ^(3/2:ℝ) + Δ^2)` with `C_var = (2/3)Λ₂K + (4/3)BΛ₁K + 2G² + 2((2/3)Λ₁K)² + 4B²`, where `K = ∫‖Xmat d N ω‖ dP`. The constant is written out in the statement, with no existential.
  - Fixed parameters come before `Δ`. The statement is deterministic with a single `N`, so there is no `∀ᶠ N` to order.
- **Minor deviation (non-blocking).** The ticket asks for `‖Φ‖ ≤ B` and `‖genPt Φ ·‖ ≤ G` on Hermitian matrices. The Lean asks for them for all `A`.
  - This does not shrink the class of admissible `Φ`: `TestFun.bdd₀` is already a global bound, and `genPt` is globally bounded through `TestFun.bdd₂`.
  - For loop observables, `bddC2C_loopObs` gives global constants.
  - The only cost is that `B` and `G` must be global bounds. The difference is between the Lean and the ticket, not the paper, so no paper-delta is needed.

## 3. Vacuity, hidden hypotheses, cycles
- No structure fields are introduced and no hypothesis is hidden. The hypothesis `hLip2` is not an extra restriction on `Φ`: by T1, `genPt(‖Φ‖²) = 2Re(Φ̄·genPt Φ) + quadVar Φ`, which is Lipschitz on Hermitian matrices given `hLip1`, `B`, `G` and `TestFun`. It only adds a constant.
- `Λ₁` and `Λ₂` are not assumed nonnegative. The proof *derives* `Λ₁K ≥ 0` and `Λ₂K ≥ 0` by applying `oneStep_error_le` at `Δ' = 1`. That is legitimate: it adds no assumption.
- Boundary cases:
  - At `Δ = 0` both sides are `0`.
  - Large `Δ` is covered correctly: the bound `‖S‖ ≤ 2B` handles `Δ ≥ 1`, so there is no hidden `Δ ≤ 1`.
  - There is no index set that can be empty and no window that can collapse.
- **Compiled nondegenerate witness.** A scratch file outside the repo (`W1490.lean`, run with `lake env lean` in the audit worktree; no source edited) defines `Φe A = exp(i·ℓ(A))` for any real continuous linear functional `ℓ` on matrices. It reuses the T1486 audit witness and proves:
  - `TestFun d N Φe`, with `‖Φe‖ ≡ 1`;
  - `genPt Φe = c·Φe` and `‖Φe A − Φe A'‖ ≤ ‖Lℓ‖‖A−A'‖`, so `Λ₁ = ‖c‖‖Lℓ‖`;
  - `‖Φe‖² ≡ 1`, so `genPt(‖Φe‖²) ≡ 0` and `Λ₂ = 0` holds exactly, not vacuously;
  - `B = 1` and `G = ‖c‖`;
  - `quadVar d N Φe M = Σ_q S_q·ℓ(B_q)²`, which is strictly positive whenever `ℓ(B_q) ≠ 0` for some used coordinate.
  - `wit_T1490` then instantiates `oneStep_var_le` for every Hermitian `M` and every `Δ ≥ 0`.
  - `#print axioms RBM.Gauss.Grid.wit_T1490` gives `[propext, Classical.choice, Quot.sound]`.
  - `Φe` is non-constant, every constant is ordinary and finite, and the main term is nonzero.
- **Loop-observable instance (the ticket's requested check).**
  - `B` and `G` are available: `bddC2C_loopObs` / `bddC2_loopObs` (`LoopC2.lean:510/534`) give global `BddC2`/`TestFun` bounds, so `B` directly and `G` through `bdd₂`.
  - `Λ₁` is not available as a compiled result. T1487's `norm_loopDrift_sub_le` bounds the Lipschitz constant of `loopDrift = eGterm + primRhs`. By `generator_add_zMotion_gauss` (`LoopIto.lean:2580`), `loopDrift` equals `(1/2)Σ S·wirtSecond(loopObs) + zMotion`, not `genPt(loopObs)` alone.
  - A compiled `Λ₁` for `genPt(loopObs)` therefore still needs (i) a Lipschitz bound for `zMotion` on Hermitian matrices and (ii) a bridge from `genPt` to the `wirtSecond` form. `Λ₂` then follows from T1 plus the `bdd₂`-Lipschitz property of `coordD1`.
  - Mathematically both steps are routine: the resolvent is smooth and bounded when `Im z ≠ 0`. But they are downstream A5-assembly bookkeeping. They are not a defect of T1490's generic targets, whose hypotheses are shown satisfiable above. **Flag for the dispatcher:** the A5 assembly must supply (i) and (ii).
- No cycle: T1490 depends only on `GridOneStep.lean` (T1486, merged) and `MomentGronwall.lean`/`Generator.lean` (committed). Neither of them imports T1490.

## 4. Dependencies
All are accepted and on `main`:
- T1486 and the generator bookkeeping: `oneStep_error_le`, `genPt`;
- moment-function lemmas: `momentFun_eq`, `ofReal_genMomentPt`, `coordD2_momentFun_ofReal`, `sum_gvar_re_coordD2`, `mul_conj_eq`, `add_conj_mul`, `TestFun.of_bddC2`, `genD`, `quadVar`;
- probability and matrix basics: `isProbabilityMeasure_P`, `continuous_Xmat`, `integrable_of_continuous_of_bound`;
- Mathlib.

## 5. Builds and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridOneStepVar`: Build completed successfully (3706 jobs). No errors. All printed warnings come from pre-existing files; none come from `GridOneStepVar.lean`.
- `lake build RBM1D`: Build completed successfully (9636 jobs). The ticket says "Root import: none", so the root does not yet import the new module.
- `#print axioms` for `TestFun.normSq`, `Grid.genPt_normSq` and `Grid.oneStep_var_le`: `[propext, Classical.choice, Quot.sound]` each.
- `grep` finds no `sorry`, `admit` or `axiom` in the file.
- Frozen signatures are untouched: only a new file was added.
