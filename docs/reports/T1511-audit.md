Auditor model: claude-opus-5-5[1m]

# T1511 audit: net lift of (2.76) uniformly in u, Gaussian model

Date (UTC): 2026-09-26T01:33Z. Branch `t/T1511` @ 34bb90f. Fresh audit worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1511-audit2`. I did not reuse the prover's worktree, and the
cache had no `GridNetLift` artefact. Diff vs merge-base: exactly one new file,
`RBM1D/Gauss/GridNetLift.lean` (+659). No other source changed, so no frozen signature was touched.

**Overall verdict: PASS** (T1 PASS, T2 PASS)

## 1. Math preflight
`docs/reports/T1511-prove.md` has a "Math preflight (before any Lean)" section with PASS for
(T1) and (T2). It is the first section, above the Lean section. Observation (not a defect for this
ticket): the section also contains text written after the Lean was done (for example "checked this
compiles", "verified by construction"). So it was edited after the Lean work. The mathematical
route it records matches the ticket.

## 2. Statement vs ticket / paper

**(T1) `RBM.Gauss.Grid.etaT_inv_le_of_hreg`.** Hypotheses: `hE : |E| < 2`, `hs0`, `hst`, `ht1`,
`0 < c`, and `hreg`. `hreg` is copied verbatim from `step2`, with `B := band d`. Conclusion:
`∀ᶠ N, (etaT E (t N))⁻¹ ≤ N`, as in the ticket.
- Delta: the extra hypothesis `hE`. It is needed for positivity and monotonicity of `etaT`, and
  `step2` supplies it at every call site (`|E| ≤ 2-κ`). The prover reported it as `T1511a`. This
  is acceptable.
- `hs0` is unused (linter warning). This is harmless and matches the ticket's hypothesis list.
- Fixed parameters `d, E, s, t, c` are bound before `∀ᶠ N`.

**(T2) `RBM.Gauss.Grid.h276_of_pointwise`.** Hypotheses: `hE, hs0, hst, ht1, hc0, hreg` (as in
step2) and `hpt`. `hpt` is exactly the ticket's formula: `∀ D > 0, ∀ u : ∀ N, TimeIcc s t N,
StochDom (P d) (lkErr at u N, pmLoop p.1 p.2) (bnd at u N)`. It uses `RBM.pmLoop` from
`Flow/Hypotheses.lean:148`, the same `pmLoop` that step2 uses. The conclusion is step2's second
conjunct.

Compiled syntactic-match check (scratch file, not committed). `h := RBM.Step2.step2 (sample d)
hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg`. Results:
- (a) The ticket's form compiles: `example … : ∀ D, 0 < D → StochDom (band d).P (…) (…) :=
  h276_of_pointwise d (by linarith) hs0 hst ht1 hc0 hreg hpt`.
- (b) `have h2 : type_of% h.2 := by rw [band_P]; with_reducible exact h276_of_pointwise …`
  compiles. The converse direction (`h.2` into the type of `h276_of_pointwise …`) also compiles.
- (c) Without the `rw [band_P]`, the reducible-only check fails. So the one syntactic difference is
  that step2 has `(band d).P` where T2 has `P d`. The ticket prescribes `B.P := P d`, and
  `band_P : (band d).P = P d` is `rfl`. Plain `exact` and term-mode use therefore accept T2's
  conclusion as step2's second conjunct. The final packaging can use it verbatim.

Quantifier order: `∀ D, 0 < D →` sits outside `StochDom`, and `StochDom` carries its own `∀ τ, ∀ D',
∀ᶠ N`, exactly as in step2. Dims, energies, windows `[s N, t N]`, loops `ZMod L × ZMod L` and the
exponents `4, 2, D` in `bnd` are unchanged.

## 3. Vacuity, hidden hypotheses, cycles, boundary cases
- **Witness for `hpt`** (a compiled example in the scratch file): for any `d, E, s, t, κ` with step2's
  hypotheses `Hy, h1, hB, hs0, hst, ht1, hc0, hreg`, `fun D hD u => auditReindexFst u ((step2
  (sample d) …).2 D hD)` has exactly `hpt`'s type. `auditReindexFst` is a 5-line `measure_mono`
  reindexing along `q ↦ (u N, q)`. So `hpt` is implied by step2's own conclusion, as the ticket
  requires. `hpt` is by design the (2.76) bound at each fixed time sequence. The upstream grid
  stopping argument plus `map_H_eq` supplies it.
- **No hidden hypotheses.** Every hypothesis is visible in the signature. There are no structure
  fields and no new classes. `netLift_of_relaxed` is used with `ξ = ξ'` and `ζ = ζ'`, and `hpt D hD0`
  is fed both as `hrel` and as the `NetLift` premise. That is legitimate.
- **Window.** `T := 1`, and `hlen : t N − s N ≤ 1` follows from `hs0` and `ht1` for every N. The
  window is not collapsed by any hypothesis. `s`, `t` are arbitrary with `0 ≤ s ≤ t < 1`. There is no
  `N = 0` loophole: every bound is under `∀ᶠ N` together with `eventually_ge_atTop 1`.
- **Exponents fixed per D.** `A := 4*D + 40` is a `set` taken right after `intro D`, before any
  filter. `B₀ = D + 2` enters as `hlow : N^(-(D+2)) ≤ bnd` and as the `hclose` slack
  `N^(-((D+2)+2))`. Neither depends on N.
  - The four gap lemmas `eventually_mul_rpow_le_mul_rpow` have constant exponents: `-A` vs `-1`,
    `2-A/2` vs `-1`, `1-A/4` vs `-D`, and `8-A/2` vs `-(D+4)`. Their multiplicative constants
    (`1, 2, √(1/2), 8`, and `1/10`) are also fixed.
  - The only N-dependent quantities are the moduli (`Bk := N^3` from `hKb_flow`, fed by T1, and a
    constant `≤ 8N^8`). These are compared against `N^{-A/2}`, which is legitimate polynomial
    bookkeeping. There is no astronomically-large-quantity witness.
- **Cycles and reuse.** A transitive constant walk (meta script over the environment) found 0
  constants with `APrime` or `EarlyQV` in the name, for both T1 and T2.
  - The file imports only `RBM1D.Gauss.Lemma514Holder`, not `Hierarchy.Step2`.
  - The `pmLoop` ↔ `lkT` bridge is reproved locally (`idx_mySig`, `lkErr_eq_norm_lkT`).
  - Dependencies are committed Step 1 / deterministic results only: `netLift_of_relaxed`,
    `highProb_norm_Xmat_le`, `hKb_flow`, `norm_lkT_flow_sub_le`, `abs_scale_sub_le`,
    `abs_etaT_sub_le`, `abs_ellHat_sub_le`, and `Band.dim`. This complies with DECISIONS §10b.

## 4. Build and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridNetLift`: GridNetLift was rebuilt from scratch (59 s). Result:
  `Build completed successfully (3781 jobs)`, exit 0, no errors. The warnings are style only:
  docstring placement, unscoped `maxHeartbeats 4000000`, `show`, line length, and the unused `hs0`.
- `lake build RBM1D`: `Build completed successfully (9657 jobs)`, exit 0. The root does not import
  the new file yet; that is planned for merge.
- Scratch check: `import RBM1D` plus `import RBM1D.Gauss.GridNetLift` compiled with no
  duplicate-declaration errors. Current `main` has only added files since the branch base. None of
  them defines any of the 9 new names in `RBM.Gauss.Grid`. The new `RBM.Gauss.Grid.abs_exp_neg_sub_exp_neg_le`
  and the existing `RBM.abs_exp_neg_sub_exp_neg_le` (LoopLipschitz) have different full names.
- `#print axioms`: `etaT_inv_le_of_hreg` and `h276_of_pointwise` both depend on `[propext,
  Classical.choice, Quot.sound]` only.
- `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`: none in the file.

## 5. Acceptance criteria
- (T1) and (T2) have the ticket's names, with no sorry, admit or axiom: yes.
- The prove report's first line is `Prover model: claude-sonnet-5`: yes.
- T2's conclusion is step2's second conjunct: yes. The `example … := h276_of_pointwise …` compiles
  against `type_of% (step2 …).2`. The only syntactic difference is `P d` vs `(band d).P`. They are
  `rfl`-equal, and the ticket prescribes `P d`.
- The one-line `step2 … → hpt` witness compiles: yes.
- A and B₀ are fixed per D, with no N-dependence in the exponents: yes.

## Notes for the dispatcher (non-blocking)
- The paper-delta `T1511a` should be recorded: T1 also takes `hE`, and the concrete `A = 4D + 40`
  replaces the ticket's illustrative `4(B₀ + C + 4)`.
- The file-level `set_option maxHeartbeats 4000000` is unscoped (linter warning). It could be
  scoped with `set_option … in` at merge or in a follow-up. It is not a soundness issue.
