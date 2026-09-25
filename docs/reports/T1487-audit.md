Auditor model: claude-opus-5-5[1m]

# T1487 audit — deterministic Lipschitz bound for the loop drift

Audited commit: `a34ca1f` (branch `t/T1487`; audit worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1487-audit`,
detached at that commit because `t/T1487` is checked out in the prover worktree).
Diff vs `main`: exactly one new file, `RBM1D/Gauss/GridDriftLip.lean` (+613). No other file touched;
no frozen signature changed; no root import (ticket: "Root import: none").

## Overall verdict: PASS (T1, T2, T3 all PASS)

## Per-check findings

1. **Math preflight.** `docs/reports/T1487-prove.md` §(a) contains a per-target preflight (T1/T2/T3 PASS,
   Step 0 findings on `eGterm`, `primRhs`, norm, existing resolvent lemma) placed before the Lean section §(b). OK.

2. **Statement vs target.**
   - (T1) `loopDrift E u I M := eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M (zt E u)) I`
     — literally the ticket's formula. Independently checked by compiling
     `example … : (1/2:ℝ) • ∑∑ Sblk • wirtSecond … + zMotion … = Grid.loopDrift E u I M := generator_add_zMotion_gauss hz M hM I hwf hn`
     (accepted by the elaborator without any unfolding), so `loopDrift` is definitionally the RHS of
     `generator_add_zMotion_gauss` (`Gauss/LoopIto.lean:2580`). PASS.
   - (T2) `norm_loopDrift_sub_le {E u} (hz : (zt E u).im ≠ 0) {M₁ M₂} (hM₁ hM₂ : IsHermitian) {I} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
     ‖loopDrift E u I M₁ - loopDrift E u I M₂‖ ≤ driftLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E) * ‖M₁ - M₂‖`.
     Hypotheses exactly those of the ticket (same as `generator_add_zMotion_gauss`); η = `|(zt E u).im|` as specified;
     no extra hypothesis. Deterministic per-`N` statement; the ticket asks for no `∀ᶠ N`. PASS.
   - `driftLip L W n η m := 4·L⁴·W³·n²·(n+1)·((1+η⁻¹) + max‖m true‖‖m false‖)²·(1+η⁻¹)^{2(n+1)}·η⁻²` — explicit closed form,
     a `def` (no existential), no dependence on `M₁, M₂`. Polynomial in `L, W, η⁻¹, ‖m‖`; in `n` it contains the factor
     `(1+η⁻¹)^{2(n+1)}`, i.e. exponential in the loop length `n` for fixed η. This is the unavoidable loop-length growth
     already present in the accepted `norm_gloop_sub_le` (`K^{σ.length}`) and in the ticket's own suggested bound
     `|L| ≤ L·W·K^n`; for a fixed loop index (fixed `n`, as in all uses) it is polynomial in `L, W, η⁻¹, ‖mSigma E‖`. Accepted
     as meeting the ticket (the ticket prescribes the `K^n` route). Not sharp; not required.
   - (T3) `norm_green_sub_le_of_herm {M₁ M₂ : Matrix (d.Idx N) (d.Idx N) ℂ} (hM₁ hM₂) {z} (hz : z.im ≠ 0) :
     ‖green M₁ z - green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖` — exactly the ticket statement. Prover's Step 0 found only the
     two-parameter `RBM.norm_green_sub_le` (`Gauss/FlowHolder.lean:71`), not this shape; proved fresh from it plus
     `RBM.Gauss.norm_green_le`. PASS.
   - Norm: file uses `open scoped Matrix.Norms.L2Operator`, same as `LoopLipschitz.lean` (l.113/119); T2 internally
     calls `norm_gloop_sub_le` (l.404) with the T3 bound, so norms match by type-checking. OK.

3. **Vacuity / hidden hypotheses / cycles.** The results are plain inequalities with no structure-bundled hypotheses.
   Compiled witnesses: `(zt 0 0).im ≠ 0` (via `zt_im`, `mE_im`), `LoopIdx ⟨[true],[0]⟩` over `ZMod 3` is `WF` with
   `1 ≤ a.length`; Hermitian `M₁, M₂` arbitrary (e.g. `0` and any nonzero Hermitian). `L ≥ 3` comes from
   `Dims.three_le_L`, so no empty-index or `N = 0` loophole; `η > 0` from `hz`. The constant is finite for every
   admissible input, so the bound is not trivially true. No circular dependency (new leaf module).

4. **Dependencies.** `generator_add_zMotion_gauss`, `eGterm` (`Gauss/Hierarchy.lean`), `primRhs` (`Loop/Primitive.lean`),
   `norm_gloop_sub_le`, `norm_gloopProd_le_pow`, `norm_Gsig_*`, `norm_green_le`, `norm_green_sub_le`, `norm_mul_mul_sub_le`,
   `norm_SB_apply_le`, `norm_Eblk_le_one''`, `LoopIdx` cut/glue length/WF lemmas — all committed on `main`
   (`LoopIto`, `FlowHolder`, `Hierarchy`, `Generator` in root `RBM1D.lean`; `LoopLipschitz` tracked and imported by
   rooted modules). No uncommitted file imported.

5. **Build / axioms.**
   - `lake build RBM1D.Gauss.GridDriftLip`: `Build completed successfully (3784 jobs)`.
   - `lake build RBM1D`: `Build completed successfully (9633 jobs)` (module not in root, per ticket).
   - `#print axioms` for `norm_green_sub_le_of_herm`, `loopDrift`, `loopDrift_eq`, `driftLip`, `norm_loopDrift_sub_le`:
     `[propext, Classical.choice, Quot.sound]` only.
   - grep: no `sorry` / `admit` / `axiom` in the file.

## Notes (non-blocking)
- `driftLip` is exponential in `n` through `(1+η⁻¹)^{2(n+1)}` (see item 2); downstream users (T1486 (T3)) should apply
  it at fixed loop length, where it is polynomial in `L, W, η⁻¹`.
- No paper-delta entry is needed: this is an internal deterministic auxiliary, not a restatement of a paper formula.
- The prove report header says `Prover model: claude-sonnet-5`; recorded only for the dispatcher.
