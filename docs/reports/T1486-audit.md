Auditor model: claude-opus-5-5[1m]

# T1486 audit — one-step Gaussian expansion

Branch `t/T1486` at `2695068`; audit worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1486-audit` (detached at `2695068`, because the branch is checked out in the prover worktree). `git diff main...t/T1486`: exactly one new file, `RBM1D/Gauss/GridOneStep.lean` (+411). No existing file is touched, so no frozen signature changes. (The two-dot diff against the current `main` also shows GridAzuma/GridPath/T1481/T1484 files as deleted. That only happens because the branch was cut before those merges. The merge must bring in only `GridOneStep.lean`.)

**Overall verdict: PASS** (all four targets).

## 1. Math preflight
`docs/reports/T1486-prove.md` has a per-target math preflight (T1, T2, T3, `integrable_norm_Xmat`, and the support lemmas `coordD2_shift` / `gen_eq_integral_genPt`). Every target is marked PASS, and the preflight comes before the Lean section. Step 0 (a)–(c) is also answered. OK.

## 2. Statement vs ticket / source

| Target | Lean signature (as compiled) | vs ticket | Verdict |
|---|---|---|---|
| T1 `RBM.Gauss.TestFun.shift` | `(h : TestFun d N Φ) (M) : TestFun d N (fun A => Φ (M + A))` | exact; `M` arbitrary | PASS |
| T2 `RBM.Gauss.Grid.oneStep_integral_eq` | `(h : TestFun d N Φ) (M) {v} (hv : 0 ≤ v) : (∫ ω, Φ (M + (√v:ℂ)•Xmat d N ω) ∂P d) - Φ M = ∫ w in 0..v, gen d N Φ M w` | the ticket's formula; `gen` is literally the ticket's definition; `v = 0` is included | PASS (see note a) |
| T3 `RBM.Gauss.Grid.oneStep_error_le` | `(h : TestFun) (hM : M.IsHermitian) (hLip : ∀ A A', A.IsHermitian → A'.IsHermitian → ‖genPt A - genPt A'‖ ≤ Λ*‖A-A'‖) (hΔ : 0 ≤ Δ) : ‖E Φ(M+√Δ X) - Φ M - (Δ:ℂ)•genPt M‖ ≤ (2/3)*Λ*Δ^(3/2:ℝ)*∫‖Xmat‖ ∂P d` | exact; `genPt` is literally the ticket's definition; explicit constant `2/3`; exponent `3/2` | PASS |
| `RBM.Gauss.integrable_norm_Xmat` | `(d N) : Integrable (fun ω => ‖Xmat d N ω‖) (P d)` | unconditional | PASS |

**Norm.** The file has `open scoped Matrix.Norms.L2Operator` (line 84). That is the same scope as `Generator.lean:127` (where the `TestFun` bounds are stated) and `LoopLipschitz.lean:113/119` (the file of `norm_gloop_sub_le`). So the matrix norm in `hLip`, in `‖A - A'‖` and in `‖Xmat‖` is the ℓ²→ℓ² operator norm the ticket requires. OK.

**Notes (not defects):**
- (a) The ticket's T2 says "a Hermitian `M`", but the Lean T2 has no Hermitian hypothesis. This makes the statement strictly more general, and it implies the ticket form. The prove report's "Open issues" item says `hM` is "kept in the signature". That is wrong about the compiled code, but it is only a report inaccuracy.
- (b) The pilot note `docs/claude-team/pilot-P4P5-paper.md` §3 plans a 4th-order Taylor step with an `O(Δ²N^C)` remainder. The ticket replaces this with the generator identity plus FTC, which gives `O(Δ^{3/2})` per step. Over `K = (t−s)/Δ` steps this sums to `O((t−s)·Λ·E‖X‖·Δ^{1/2})`. That is still negligible for `Δ = N^{-C}` with large `C`. The ticket sanctions this route. It is not a change to a paper statement, so no paper-delta entry is needed from this ticket. The A5 assembly must budget `Δ^{1/2}`, not `Δ`.
- (c) Downstream warning for T1487 and A5, not a defect here. `TestFun` requires *global* bounds over all complex matrices, including non-Hermitian ones. The raw loop functional `L(H) = tr ∏ G(H)` is not globally bounded off the Hermitian set. T3's `hLip` is only required on Hermitian matrices, but the `TestFun d N Φ` hypothesis is global. So plugging loop functionals into T2/T3 needs a cutoff or extension that is a `TestFun`. T1487 or A5 must supply it.
- (d) The prove report's first line says `Prover model: claude-sonnet-5`, but the ticket's role is `prover-hard`. This is a process note for the dispatcher. It does not affect the mathematics.

## 3. Vacuity / hidden hypotheses / cycles
- No structure fields are introduced. `gen` and `genPt` are plain definitions, identical to the ticket text. No hypothesis is smuggled in.
- `hasDerivAt_integral_Phi` needs `0 < u`. It is used only on `Ioo 0 v`. The closed endpoint `0` comes from `continuous_integral_comp_Hflow` (dominated convergence with the constant bound from `TestFun.bdd₀`), which holds for every `s : ℝ`. FTC is applied with `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (continuity on `Icc`, derivative on `Ioo`), so `v = 0` is covered and not excluded. `F 0 = Φ M` follows from `Hflow_zero` and `P d` being a probability measure.
- In T3, `Λ` is not assumed nonnegative. That is harmless: the proof only chains the hypothesis. `Δ = 0` is allowed, and both sides are `0`.
- **Compiled nondegenerate witness for T3's hypotheses** (scratch file outside the repo, `lake env lean` in the audit worktree; no source was edited). For any real continuous linear functional `ℓ` on matrices, let `L := I • (ofRealCLM ∘L ℓ)` and `Φe A := exp (L A)`. I proved:
  - `TestFun d N Φe`, with constants `1, ‖L‖, ‖L‖²`;
  - `genPt d N Φe A = c · Φe A`, where `c = ½ Σ_{p∈usedCoord} S_p · L(B_p)²`;
  - `‖Φe A − Φe A'‖ ≤ ‖L‖‖A − A'‖`;
  - hence `hLip` holds with `Λ = ‖c‖·‖L‖`;
  - and `oneStep_error_le` then instantiates for every Hermitian `M` and every `Δ ≥ 0`.

  `#print axioms` on the witness theorem shows `[propext, Classical.choice, Quot.sound]`. This `Φ` is non-constant, and `Λ` is an ordinary finite constant: there is no collapsed index set and no astronomically large quantity. The ticket's `Φ = const` case is `ℓ = 0`.
- Dependencies are only accepted, committed declarations, all on `main`: `hasDerivAt_integral_Phi`, `matrixStein`, `TestFun` and its lemmas, `coordD2`, `norm_coordD2_le`, `usedCoord`, `Hflow`, `Hflow_zero`, `Hflow_isHermitian`, `Xmat_eq_sum`, `continuous_Xmat`, `continuous_Hflow`, `integrable_coord`, `integrable_of_continuous_of_bound`, `isProbabilityMeasure_P`, plus Mathlib. None of them depends on T1486, so there is no cycle.

## 4. Build and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridOneStep`: `Build completed successfully (3701 jobs)`, no errors, no warnings from `GridOneStep.lean`.
- `lake build RBM1D`: `Build completed successfully (9633 jobs)`. The branch root does not import the new module, as the ticket says ("Root import: none").
- `#print axioms`:
  - `TestFun.shift`, `coordD2_shift`, `integrable_norm_Xmat`, `Grid.oneStep_integral_eq`, `Grid.oneStep_error_le`: each `[propext, Classical.choice, Quot.sound]`.
- `grep` finds no `sorry`, `admit` or `axiom` in the file, and no `set_option`. The one `private` lemma (`hasFDerivAt_shift`) is an auxiliary chain-rule lemma.

## Verdicts
- T1 `TestFun.shift`: PASS
- T2 `oneStep_integral_eq`: PASS
- T3 `oneStep_error_le`: PASS
- `integrable_norm_Xmat`: PASS
