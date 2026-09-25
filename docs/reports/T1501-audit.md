Auditor model: claude-opus-5-5[1m]

# T1501 audit: (5.35) far-field bound without `h560` (T1499 Option B)

Date: 2026-09-25 (UTC). Branch `t/T1501` @ `ab7fbdd` (base `752dd76`). The branch changes one file: `RBM1D/Hierarchy/Step2FarInputsJG.lean` (new, +295). Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1501-audit`. It is a fresh detached checkout with an APFS-cloned cache. I did not reuse the prover's worktree. No source was edited.

## Verdicts

| Target | Verdict |
|---|---|
| (T1) `RBM.Step2FarInputs.eGpm_le_rhs535_of_jG` | **PASS** |
| (T2, optional) `RBM.Step2FarInputs.rhs535_mul_J_le` | **PASS** |

**Ticket T1501: PASS.**

## 1. Math preflight
`docs/reports/T1501-prove.md` §(a) gives a math preflight PASS for both targets. It is timestamped 20:48Z, before the branch commit at 20:52Z. The report's first line is `Prover model: claude-sonnet-5[1m]`.

## 2. Statement vs ticket and paper
- **(T1) hypotheses.** I compared the signature with `eGpm_le_rhs535_of_jS` (Step2FarInputs.lean:2224) hypothesis by hypothesis. The new theorem has exactly the old list minus `hK` and `h560`, in the same order and with the same binders:
  - fixed band/scale parameters `hL hW hℓu hℓs hηu hA hr hD`;
  - then `a₁ a₂ {ρ κ} hρ h273 h554 h557C h557R hone hκ`.
  - No hypothesis was added. Nothing is packed into a structure field.
- **(T1) conclusion.** `rhs535 W L ℓ_u ℓs η_u D' (APrimeJG.jG X E N u ω ℓ_u η_u D') ρ (zdist (a₁-a₂))`. This is what the ticket asks for, and it is T1499 Option B verbatim.
- **Proof route.** The proof is the frozen, accepted `eGpm_le_rhs535` with `J := jG` and `Gm := gmBlk`. This matches the paper's route (p.62, (5.60) then (5.61)):
  - (5.60) is proved for every `b`, deterministically, by the private helper `norm_gloop_three_le_gmBlk'`.
  - The (4.2)/(5.31) half is used only on far pairs: `h531` comes from `two_loop_re_le_gsqBlk'` composed with `gsqBlk_le_jG_mul_tailT`, and `h42` from `gmBlk_le_sqrt_jG_tail`.
  - `hJ` is `one_le_jG`.
- **(T2).** `rhs535 … (c²J) … ≤ c³ · rhs535 … J …` for `c ≥ 1`. The hypotheses are sign conditions only. The degrees in `J` are 0, 1 and 3/2, as the ticket describes.
- **Paper comparison (non-blocking).** The paper's (5.35) is a `≺` bound in `J*_{u,D}` ((5.28)–(5.29)). The Lean conclusion is deterministic, per sample, and uses the block-level Green quantity `jG`. In the paper, `jG ≺ J*` is absorbed silently in (5.61) via (4.2). In Lean it is a separate step: `jG ≤ N^{2ε} jS` w.h.p., which T1499 N1/N2 identifies as its own ticket. The frozen `rhs535` also keeps the (2.73)-reduced shape-2 exponents rather than the literal (5.35) exponents; that was accepted earlier. The ticket forbade touching any file other than the Lean file, so no delta was appended. **Recommendation to the dispatcher:** add a `T1501a` paper-delta entry: "(5.35) with `J := jG` (block Green maxima), deterministic; `jG ≲ J*` deferred."

## 3. Vacuity, hidden hypotheses, cycles
- **Compiled satisfiability witness** (`scratch_audit/Sat.lean` in the audit worktree, `lake env lean` rc 0, no errors). This replaces the prover's claim that "T1488/T1496 already exhibited a witness". That claim is inaccurate: T1496's witness covers only the real-sign lemma `rhs535_div_le`.
  - The theorem is `AuditT1501.sat`. For **every** `B`, `X : Sample B`, `E N u ω`, `a₁ a₂` with `2 ≤ W`, `1 ≤ ℓ_u`, `0 < η_u`, `1 ≤ Wℓ_uη_u`, there exist `ℓs D' ρ κ` such that all of the following hold simultaneously: `0<ℓs`, `hr`, `hD`, `hρ`, `h273`, `h554`, `h557C`, `h557R`, `hone`, `hκ`.
  - Choice of parameters: `ρ := Σ_b ‖L3‖`, `κ := A·Σ_{σ,b}‖tr‖`, `ℓs := ℓ_u/R` with `R := 1 + A²S3 + A(SC+SR)² + 2κ`, and `D' ∈ ℕ` large.
  - `hL` holds automatically (`B.three_le_L`). The remaining conditions `hW hℓu hηu hA` are band/scale properties inherited verbatim from the frozen `eGpm_le_rhs535`, which is Step-1 regime `Wℓη ≥ N^c`.
- **Limit of the witness.** It makes `ℓ_u/ℓs` large, so it only proves the hypotheses are not logically empty. The paper-regime satisfiability (`ℓs = ℓ(s)`) rests on (2.73), (5.54), (5.57) and (2.74). Those are the same Step-1 inputs as in the accepted frozen `eGpm_le_rhs535` and `eGpm_le_rhs535_of_jS`. T1501's hypothesis set is a **strict subset** of theirs, so it adds no new vacuity risk.
- **Boundary cases.** There is no `N = 0`, empty-index or collapsed-window loophole: `L ≥ 3` and `W ≥ 1` hold structurally. `a₁ = a₂` is allowed, as in `eGpm_le_rhs535`. `jG ≥ 1` holds unconditionally, so `J` is never degenerate. `jG` is the actual per-sample quantity, not a free parameter.
- **Forbidden inputs (acceptance criterion 1).** I scanned the transitive constant closure of both theorems with a meta command (`scratch_audit/Deps.lean`), about 43.6k constants for (T1). It contains **no** constant whose name includes `eGpm_le_rhs535_of_jS`, `h535_of_jS`, `gmOfJS`, `APrimeFirstCellEGFar`, `exampleGrow`, `Dims` or `sorryAx`. `h560` appears only as the argument slot of `eGpm_le_rhs535`, filled by the helper. It is never a hypothesis. No cycle: the file imports only `RBM1D.Gauss.APrimeDriftNearTriple`.

## 4. Dependencies / DECISIONS §10b (acceptance criterion 2)
- The direct RBM dependencies are all committed on `main`. I checked each with `#check` and all are generic in `{B : Band Ω}`:
  - `APrimeJG.{gmBlk, gsqBlk, jG, one_le_jG, gsqBlk_le_jG_mul_tailT, norm_Gsig_le_gmBlk, gmBlk_mul_swap_le_gsqBlk, gmBlk_nonneg}`;
  - `APrimeDriftNearTriple.{gmBlk_comm, gmBlk_le_sqrt_jG_tail}`;
  - `Lemma57.{norm_gloop_three_le, sum_blkW_normSq, sum_blkW, blkW_nonneg}`;
  - `Step2FarInputs.{eGpm_le_rhs535, rhs535}`.
- These lemmas are deterministic and per-sample. Their hypotheses are only `0 < W` and the far-pair distance, so they are trivially satisfiable. None of them involves smooth-prefix weights, and none is valid only for `exampleGrow`.
- **§10b holds.** The prover correctly found that `APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk` and `two_loop_re_le_gsqBlk` are `exampleGrow`-scoped (file-local `private abbrev B := Gauss.band Dims.exampleGrow`). The prover did not reuse them. Instead it re-derived both for general `B` from generic sublemmas, which is what T1499-audit N1 prescribes, so the ticket's "stop if exampleGrow-only" clause was not triggered for any declaration actually used. The dependency scan above confirms this independently.

## 5. Build, axioms, forbidden tokens
- `lake build RBM1D.Hierarchy.Step2FarInputsJG`: Build completed successfully (3846 jobs). I deleted any stale artifacts first. Only lint/deprecation warnings (`Try this`, `<;>`, `if_neg` deprecated).
- `lake build RBM1D` on the branch: Build completed successfully (9649 jobs).
- A scratch file importing both `RBM1D` and the new module elaborates with no name clash. `git grep` on current `main` (`1158e42`) finds no clash with the four new names either.
- `#print axioms`:
  - `eGpm_le_rhs535_of_jG`: `[propext, Classical.choice, Quot.sound]`
  - `rhs535_mul_J_le`: `[propext, Classical.choice, Quot.sound]`
- No `sorry`, `admit` or `axiom` in the file. No frozen signature was touched: it is a new file, and `Step2FarInputs.lean` is unchanged.

## 6. Notes for the dispatcher (non-blocking)
1. Add paper-delta `T1501a` (see §2).
2. The prover's report attributes a joint witness to T1488/T1496; that attribution is incorrect. This audit's compiled `AuditT1501.sat` supplies the witness instead.
3. Follow-up worth considering, as the prover suggests: promote the two general-`B` helpers (now `private`) to public lemmas, so the `h535_of_jG` wrapper and M4 can cite them.
