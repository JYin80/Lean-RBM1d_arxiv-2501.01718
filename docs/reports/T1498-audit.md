Auditor model: claude-opus-5-5[1m]

# T1498 audit: M7b, (5.36) for `EEpath` off the diagonal `a' ≠ a`

Branch `t/T1498`, head `53e6498` (parent `a443cce` = current `main`). Diff vs `main`: one added file, `RBM1D/Gauss/EEOffDiagBound.lean` (342 lines). Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1498-audit` (detached at `53e6498`; its file is byte-identical to the prover worktree's). No source was edited.

## Target (T1) `RBM.Gauss.norm_EEpath_offDiag_le`: **PASS**

### 1. Math preflight
`docs/reports/T1498-prove.md` §0 (Step 0 `#check`s) and §(a) contain a math preflight with verdict PASS. The report says it was written before the Lean. Step 0 records the exact statement of `tailT_sub_le`.

### 2. Statement vs ticket / T1488 §3 M7b / paper
Compared against the actual Lean sources, not the report:
- `RBM.tailT_sub_le` (Analysis/StretchedExp.lean:337): `tailT W ℓu ηu D (ℓ - C * ellStar W ℓu) ≤ exp (√C * log W ^ (3/4)) * tailT W ℓu ηu D ℓ`, with `1 ≤ W`, `0 < ℓu`, `0 ≤ C`. Applied at constant `2*C` (proof line 173), this gives exactly the loss `Real.exp (√(2 * C) * Real.log (B.W N) ^ (3/4 : ℝ))` in the conclusion. **The loss factor matches `tailT_sub_le` exactly.**
- Widened indicator. The proof derives `dist ≤ dist' + 2C·ellStar` from `hdisp 0`, `hdisp 1` and `zdist_add_le` twice plus the pre-existing `zdist_neg`. So `dist' ≤ 4ℓ*_u` implies `dist ≤ (4+2C)ℓ*_u`, and the conclusion's `if dist ≤ (4 + 2 * C) * ellStar Wr ℓu` is exactly the threshold this displacement gives. The constant `2C` is the same one fed to `tailT_sub_le`. **Matches.**
- Hypotheses vs `EEDef.ee_le_EEpath_sym` (Hierarchy/EEDef.lean:1294):
  - Every hypothesis is present with the same type, except `hc0`/`hc1`. The two `ee_le_EEpath_sym` calls discharge those by `simp`, using `leftArg_append`/`rightArg_append`.
  - `h273`/`h564` are given at `Fin.append a a` and, as `h273'`/`h564'`, at `Fin.append a' a'`, with one common `ρ`.
  - `h564'` uses `a' 0`, which is `lab₁ (Fin.append a' a')`.
  - Then `{C : ℝ} (hC : 0 ≤ C)` and `hdisp : ∀ i, zdist (a i - a' i) ≤ C * ellStar Wr ℓu`, covering both labels.
- Conclusion. It is character-for-character the T1488 §3 M7b display, with `dist` and `T` taken at `a` (`a 0 - a 1`).
- Argument and quantifier order are the same as `ee_le_EEpath_sym`. The statement is deterministic and per-ω, with no `∀ᶠ N`, so there is no parameter-order issue.
- **No hidden hypotheses on `C`.** The only hypotheses mentioning `C` are `hC` and `hdisp`. `C` is an implicit real, and there is no structure argument.
- Optional reduced variant `norm_EEpath_offDiag_le_reduced`: not produced. The ticket makes it optional, so this is not a defect.
- Relation to the paper. Paper (5.33) assumes `max_i |a_i − a'_i| ≤ ℓ*_t` and (5.36) is normalised by `T_{t,D}`. The Lean statement is the general-`C` form at time `u` (`T_{u,D}`, `ℓ*_u`). The paper's hypothesis corresponds to `C = ℓ_t/ℓ_u`. The Lean version therefore carries an explicit loss `exp(√(2C)(log W)^{3/4})` and the wider near window `(4+2C)ℓ*_u`, where the paper absorbs these with `≺`.
  - This is the M7b target as the ticket specifies it. The ticket and T1488 §3 explicitly leave open whether the loss is harmless for the application's `C`.
  - Paper-delta #113 ① (general `a'` goes through (5.32)) and ⑥ (`T_u` vs `T_t`) already cover the substance.
  - Recommendation for the dispatcher, not a RETURN: append a temporary-tag delta `T1498a` that records the explicit loss and the widened window. The prover could not write `docs/paper-deltas.md`, because the ticket forbids touching any other file.

### 3. Vacuity / satisfiability
**Compiled witness.** The scratch file `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM1D/c89db6b5-4fbc-4b34-995c-1e741f3b37d2/scratchpad/Wit.lean` is outside the repository. It was checked with `lake env lean` in the audit worktree: rc 0, no errors. It proves theorem `wit`:
- Setting: an **arbitrary** `X, E, N, u, ω, σ` and **arbitrary, possibly distinct, `a a'`**, with `1 ≤ ℓu`, `0 < ηu` and `2 ≤ W`.
- Claim: there exist `ℓs, J, Gm, Gsq, Smax, ρ, C` satisfying every hypothesis of `norm_EEpath_offDiag_le` at once: `hℓs, hJ, hρ, hGm0, hGm, hGsq0, hGsq2, hrow, hSmax, h273, h273', h564, h564', h42sq, hC, hdisp`.
- The witness values:
  - `Gm ≡ Σ‖Gsig‖` and `Gsq ≡ Gm²`;
  - `J = Gm²/W^{-D} + 1`, using `tailT ≥ W^{-D}`;
  - `Smax = Σ‖gloop‖`;
  - `ρ = Σ_b eeL6(a,a) + Σ_b eeL6(a',a')`;
  - `ℓs = ℓu/R` with `R^5·A^{-5} ≥ ρ`;
  - `C = (zdist(a0−a'0) + zdist(a1−a'1))/ellStar`.
- So the hypothesis set is never empty and is not restricted to `a = a'`. The prover's own witness (`a' := a`, `C := 0`) is correct but degenerate. The compiled one is nondegenerate.
- About the large free parameters in the witness (`J`, `ρ`, `1/ℓs`): this is a per-ω deterministic lemma with the same free-parameter hypotheses as the accepted `ee_le_EEpath_sym`. The conclusion scales honestly with them, so no witness-by-huge-quantity loophole is introduced. Their probabilistic size is a downstream (A5) matter.
- **Boundary cases.**
  - `C = 0` forces `a = a'` on both labels. The result then reduces to the diagonal bound with loss 1 and window `4ℓ*_u`. It is consistent and not vacuous.
  - `W = 1` gives `ellStar = 0`, so `hdisp` forces `a = a'`. This is harmless, since `W ≥ 2` in every real regime, and the witness above needs only `W ≥ 2` for `a ≠ a'`.
  - No `N = 0`, empty-index or collapsed-window loophole: `NeZero (B.L N)` comes from `Band`, and `1 ≤ W` from `EEDef.one_le_W`.
- **No circularity.** The file imports only `Hierarchy.EEDef` and `Gauss.EEOffDiag`.

### 4. Dependencies
Every dependency is already accepted and on `main`:
- `EEDef.ee_le_EEpath_sym` (T156/T167/T190);
- `Gauss.norm_EEpath_offDiag_sq_le` (T1494, merged in `3a25907`), whose signature has no hypotheses;
- `tailT_sub_le`, `tailT_antitone`, `tailT_nonneg`, `ellStar` (StretchedExp);
- `zdist_add_le` (Defs/Dist.lean:33) and `zdist_neg` (Defs/Sums.lean:48);
- `leftArg_append`/`rightArg_append`, `cNear2_nonneg`/`cFar2_nonneg`, `one_le_W`.

### 5. Build / axioms / forbidden tokens
- `lake build RBM1D.Gauss.EEOffDiagBound` (audit worktree): `Built RBM1D.Gauss.EEOffDiagBound`, `Build completed successfully (3732 jobs)`.
- `lake env lean RBM1D/Gauss/EEOffDiagBound.lean`: rc 0, with no errors or warnings from the file.
- `lake build RBM1D` (audit worktree): `Build completed successfully (9646 jobs)`, rc 0. The root axiom audit reports "20724 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]". The new module is not yet root-imported; that is added at merge.
- `#print axioms RBM.Gauss.norm_EEpath_offDiag_le`: `[propext, Classical.choice, Quot.sound]`.
- `#print axioms RBM.zdist_sub_le_disp_add`: `[propext, Quot.sound]`.
- `grep` finds no `sorry`, `admit`, `axiom`, `set_option` or `native_decide` in the file.
- Only the new file is added, so no frozen signature is touched.
- Name-clash check: `RBM.zdist_sub_le_disp_add` does not exist elsewhere in the main worktree, including untracked files. `ellStar_nonneg'` is `private`.

### Minor, non-blocking
- The module docstring (line 25) says `zdist_neg` is "proved here as `RBM.zdist_neg`". In fact it is the pre-existing `Defs/Sums.lean:48`, as the prove report correctly says. The docstring is inaccurate; the code is fine.
- The prove report's claim "taking `C` to be the max … always works" needs `ellStar > 0`, i.e. `W ≥ 2`.

## Verdict
(T1) `RBM.Gauss.norm_EEpath_offDiag_le`: **PASS**.
