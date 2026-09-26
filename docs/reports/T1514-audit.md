Auditor model: claude-opus-5-5[1m]

# T1514 audit (re-audit after repair) — R3a: single-label QV on the good set with the one-step time shift

Date: 2026-09-26T02:07Z. Branch `t/T1514` at `97a181d` (repair commit on top of `fbf7e5c`).

**Worktrees.** Neither is the repairer's worktree `RBM1D-wt/T1514`.

| Worktree | Contents | Used for |
|---|---|---|
| `/Users/junyin/Lean_proof/RBM1D-wt/T1514-audit3` | detached at `97a181d` | the ticket's own builds |
| `/Users/junyin/Lean_proof/RBM1D-wt/T1514-audit3m` | current `main` `3ef3996`, plus `GridQVStep.lean` checked out from `97a181d` | merge simulation, cross-module checks |

**Diff scope.** `git diff --name-only main...t/T1514` lists only `RBM1D/Gauss/GridQVStep.lean`. `RBM1D.lean` is untouched, so no frozen signature is affected.

## Overall verdict: PASS

| Target | Verdict |
|---|---|
| (T1) | PASS |
| (T2) | PASS |
| (T3) | PASS |

Both defects from the previous audit (RETURN) are fixed, and nothing else changed.

## Repair diff (`fbf7e5c..97a181d`, read in full: +13/−10, one file)

1. `quadVar_step_le`: `(hΔ : 0 < Δ)` became `(hΔ : 0 ≤ Δ)`. No other binder changed, the conclusion did not change, and the proof body did not change.
2. `nearEpsilon_mono_J`: `private` was dropped and the docstring was updated. The statement is byte-identical.
3. `diagShape'_le_sum` is now the public `diagShape'_le_dropIndicator`. The statement is byte-identical. Its one use inside the file (in the proof of (T3)) was renamed to match.
4. The private `diagFarRate_mono_J` now has `hSmax` renamed to `_hSmax`, which clears the linter warning.
5. Header docstring edits.
6. Two new `#print axioms` lines.

There is no hunk in (T1) (`qvTimeShiftConst`, `qvTimeShiftConst_nonneg`, `sqrt_quadVar_time_shift`), in any private helper of §0–§3, or in `diagShape'_mono_J`.

## Gate checks

1. **Math preflight.** `T1514-prove.md` begins with the math preflight (PASS for T1/T2/T3), placed before the Lean section. The repair section updates the text of the `Δ = 0` boundary case and marks the correction as a correction. OK.
2. **Builds.**
   - Worktree `T1514-audit3`. GridQVStep build products were absent from the cloned cache, so the module was built from scratch.
     - `lake build RBM1D.Gauss.GridQVStep`: `Build completed successfully (3844 jobs)`. There are no warnings or errors in `GridQVStep.lean`.
     - `lake build RBM1D`: `Build completed successfully (9659 jobs)`.
   - Merge simulation (`T1514-audit3m`, current `main` plus the file).
     - Building the modules GridQVStep, GridQVForm, GridQVSum, GridNetLift and Step2QVEvent together: `Build completed successfully (3936 jobs)`.
     - `lake build RBM1D`: `Build completed successfully (9662 jobs)`.
3. **Name clashes.** A scratch file imports `RBM1D` (root) and `RBM1D.Gauss.GridQVStep` together. It elaborates with 0 errors. So the newly public names do not clash with anything in the `RBM.Gauss.Grid` namespace on current `main`, including T1508, T1511 and T1512, which were merged after this branch's base.
4. **Axioms.** All five `#print axioms` lines in the file print `[propext, Classical.choice, Quot.sound]`:
   - `sqrt_quadVar_time_shift`
   - `diagShape'_mono_J`
   - `nearEpsilon_mono_J`
   - `diagShape'_le_dropIndicator`
   - `quadVar_step_le`

   The scratch file's own `#print axioms RBM.Gauss.Grid.quadVar_step_le` prints the same list.
5. **No escape hatches.** The file has no `sorry`, `admit` or `axiom`. The only grep hit is the docstring sentence on line 40.
6. **Dependencies.** Unchanged from the previous audit. All are merged on `main`:
   - `EarlyQVRate.coordD1_lkFun_eq`
   - `coordD1_loopObs_eq`
   - `green_sub_eq`, `norm_green_le`, `norm_zt_sub`
   - `sqrt_wsum_add_le`
   - `tailT_mono_time` (T1510)
   - `rpow_neg_le_tailT`, `Cutoff.one_le_rpow_mul_tailT_sq`
   - `Lemma57.cNear2_nonneg`, `Lemma57.cFar2_nonneg`
   - `EarlyQVRateEv.sDet_nonneg`

   There is no cycle.

## (T1) `RBM.Gauss.Grid.sqrt_quadVar_time_shift` — PASS

- **Unchanged.** The repair diff has no hunk in §1–§3 or in the (T1) theorem.
- **Signature.** The re-`#check`ed signature is
  `|E|<2 → 0≤u → u≤u' → u'<1 → M.IsHermitian → ∀ a, √quadVar(lkFun … u' …) M ≤ √quadVar(lkFun … u …) M + qvTimeShiftConst d N E u' * (u'−u)`.
  Both sides use the same `M`, and the hypotheses are exactly the ticket's.
- **`Csh`.** `Csh = 16·√2·card(d.Idx N)²·(1+η_{u'}⁻¹)⁶` is explicit, nonnegative and polynomial.
- **Witness.** `E=0, u=0, u'=1/2, M=0`.

The previous PASS stands.

## (T2) `diagShape'_mono_J`, `nearEpsilon_mono_J`, `diagShape'_le_dropIndicator` — PASS

- **Public and callable.** All three are public. They resolve by `#check` from an external file that imports the module.
- **`diagShape'_mono_J`.** Unchanged. Its hypotheses are `0<ℓu, 0<ηu, 1≤W, 0≤J≤J', 0≤Smax`.
- **`nearEpsilon_mono_J`.** Signature: `0≤W → 0≤L → 0≤J → J≤J' → nearEpsilon W L ℓu ηu D J ≤ nearEpsilon W L ℓu ηu D J'`. This is the ticket's "and so is the nearEpsilon term". The hypotheses are satisfiable, e.g. `W=L=1, J=0, J'=1`.
- **`diagShape'_le_dropIndicator`.** Signature: `1≤W → 0<ℓu → 0<ℓs → 0<ηu → 0≤ε → diagShape' … J Smax ε b ≤ (diagNearRate … + 2ε + diagFarRate … J Smax)·tailT(…, zdist(b0−b1))²`. This is the ticket's "dropping the indicator". The hypotheses are satisfiable at every window point.
- **Rename.** The rename from `diagShape'_le_sum` is safe. The old name was private, so it could not have had outside users. `git grep` on `main` finds no consumer of either name. The ticket does not fix a name for this sub-statement.

## (T3) `RBM.Gauss.Grid.quadVar_step_le` — PASS

**Statement.** The re-`#check`ed binders are:
- `|E|<2`, `0≤uj`, **`0≤Δ`**, `uj+Δ<1`;
- `0≤D`, `0<ℓs`, `0≤J'`, `J'≤J`;
- `M.IsHermitian`;
- `hqv` at `uj` with cap `J'`.

The conclusion, with `Q'` written out literally, is unchanged:
`2N^τ(diagNearRate + 2·nearEpsilon(…J) + diagFarRate(…J, sDet uj)) + 2·Csh²·Δ²·W^{2D}`, all times `tailT(…ell(uj+Δ), etaT E (uj+Δ)…)²`.
It now matches the ticket's `u_j ≤ u_{j+1} = u_j + Δ < 1` exactly.

**`Δ = 0` is handled correctly.** I re-read the proof body:
- `hΔ` is consumed only by `linarith` in `huu' : uj ≤ uj + Δ` (and in `huj1`).
- Δ appears elsewhere only in these places:
  - `uj + Δ − uj = Δ` (by `ring`);
  - `Csh * Δ` and `(Csh*Δ)²`;
  - the nonnegativity `0 ≤ 2·Csh²·Δ²` (by `positivity`, which holds for any real Δ).
- There is no division by Δ, no `Δ⁻¹`, and no strict inequality that needs `Δ ≠ 0`.
- (T1) is called with `u ≤ u'`, which holds at equality.
- `tailT_mono_time` takes `u ≤ v`.

A compiled scratch example (E) instantiates `quadVar_step_le` with `Δ := 0` (`hΔ := le_rfl`), and it elaborates.

**Re-confirmed compiled checks.** These ran in the merge-simulation worktree, via `lake env lean` on the session scratchpad file `AuditT1514b.lean` (outside the repository), with 0 errors. The scratch file is last audit's file with the hypothesis updated to `0 ≤ Δ`, plus the new checks (E)/(F).
- **(A) T1512 (T3) shape.** The output of `quadVar_step_le` closes `GridQVForm`'s `v_Ab_le` `hqv` shape at source time `u := uj+Δ` by `exact`, with:
  - `Φ a := lkFun … (uj+Δ) … a`;
  - `W := (band d).W N`;
  - `m := (mE E).im`;
  - `Q := Q'`.

  The match is definitional. It uses `ell ≡ ellHat (d.L N) (w:ℂ)` and `etaT E w ≡ (1−w)·(mE E).im`.
- **(B) T1508 amend-1.** The bracket in `Q'`, taken at `ℓs := ell(s N)` and `J := qvJ E s δ ε N uj`, equals `Grid.Qd (band d) E s δ ε D N uj` by `rfl`.
- **(C) T1497.** The pointwise conclusion of `highProb_quadVar_diagShape_of_jS` (with `(band d).toDims`) is accepted verbatim as `hqv`, with `ℓs := ell(s N)` and `J' := jG …`.
- **(D) Nondegenerate simultaneous witness.** Take:
  - `d := Dims.exampleGrow`, `N ≥ 2`;
  - `E = 0`, `uj = 0`, `D = 64`, `ℓs = 1`, `J' = J = 1`, `M = 0`.

  The compiled example proves `∃ τ, ∀ a, hqv`, with `τ := logb N (1 + Σ_a quadVar_a / diagShape'_a)`. The key fact is `diagShape' > 0`. With `Δ = 1/4` (or `Δ = 0`), the remaining hypotheses are immediate. The weakening to `0 ≤ Δ` only enlarges the admissible set.
- **(E) `Δ = 0` instance.** Compiles (see above).
- **(F) Public helpers.** `nearEpsilon_mono_J` and `diagShape'_le_dropIndicator` resolve from outside the file.

**Other vacuity checks.** There is no `N = 0` loophole, no empty index set and no collapsed window. There is no hidden structure field: all time and window data come from `band d`. There is no "astronomically large" witness beyond the existential `τ` noted in (D). In the intended use, `τ` is the small exponent supplied with high probability by T1497 (check C).

**Minor, no action required.** `_hD0 : 0 ≤ D` is unused but harmless, because R4 takes `D ≥ 64`.

## Conclusion

T1514: PASS for (T1), (T2) and (T3). It is ready to merge as the single file `RBM1D/Gauss/GridQVStep.lean`, with the root import added at merge.
