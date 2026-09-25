Prover model: claude-sonnet-5

# T1498: M7b, (5.36) for `EEpath` off the diagonal `a' ≠ a`

## 0. Step 0 (read-only checks)

`#check`-ed (via `lake env lean` on a scratch file importing `RBM1D`, and by reading the
sources) before writing any Lean:

- `RBM.tailT_sub_le` (`Analysis/StretchedExp.lean:337`):
  `theorem tailT_sub_le (hW : 1 ≤ W) (hℓu : 0 < ℓu) {C : ℝ} (hC : 0 ≤ C) (ℓ : ℝ) : tailT W ℓu ηu D (ℓ - C * ellStar W ℓu) ≤ exp (√C * log W ^ (3/4:ℝ)) * tailT W ℓu ηu D ℓ`.
  This is **exactly** the shape the ticket assumes: at loss constant `C`, the loss factor is
  `exp (√C · (log W)^{3/4})`. No difference from the ticket's description. Consequently, at
  `C := 2 * C` (the ticket's `C`), the loss is `exp (√(2*C) · (log W)^{3/4})`, exactly the
  displayed conclusion.
- `RBM.tailT_antitone` (`:307`): `Antitone (tailT W ℓu ηu D)` given `0 < ℓu`. Used together
  with `tailT_sub_le` to bound `tailT dist'` by `tailT (dist - 2C·ellStar)` then by
  `exp(...) · tailT dist`.
- `RBM.zdist_add_le` (`Defs/Dist.lean:33`): `zdist L (u+v) ≤ zdist L u + zdist L v` (ℕ-valued).
  `RBM.zdist_neg` (`Defs/Sums.lean:48`, **pre-existing**, not written by this ticket):
  `zdist L (-u) = zdist L u`. Both used for the displacement triangle inequality
  `zdist(a₀-a₁) ≤ zdist(a₀-a'₀) + zdist(a'₀-a'₁) + zdist(a₁-a'₁)`.
- `RBM.EEDef.ee_le_EEpath_sym` (`Hierarchy/EEDef.lean:1294`): confirmed the exact hypothesis
  list and conclusion quoted in `docs/reports/T1488-prove.md` §3 M7b (hypotheses `hℓu, hℓs,
  hηu, hJ, hc0, hc1, hρ, hGm0, hGm, hGsq0, hGsq2, hrow, hSmax, h273, h564, h42sq`; conclusion
  `ηu⁻¹·(cNear2·r⁵·1(dist≤4ℓ*_u) + cFar2·(2J)²·(A·2√Smax) + 72·(2J)³·A⁻¹)·T(dist)² +
  (W·L·ρ + 2·W·L·W^{-D}·(2J)³·T(dist)²)`).
- `RBM.Gauss.norm_EEpath_offDiag_sq_le` (`Gauss/EEOffDiag.lean`, T1494, merged): confirmed
  `‖EEpath (Fin.append a a')‖² ≤ ‖EEpath (Fin.append a a)‖ · ‖EEpath (Fin.append a' a')‖`, no
  hypotheses beyond the arguments themselves (Cauchy–Schwarz for the Gram kernel `eeTens`).
- Also `#check`-ed `EEBridge.leftArg_append`/`rightArg_append` (`@[simp]`, give `leftArg
  (Fin.append a a') = a`, `rightArg (Fin.append a a') = a'`), `EEDef.lab₁`/`lab₂` (`leftArg c
  0`/`leftArg c 1`), `Lemma57.cNear2_nonneg`, `Lemma57.cFar2_nonneg`, `EEDef.one_le_W`.

No difference from the ticket's description was found; every route step (`zdist_add_le`,
`tailT_antitone`, `tailT_sub_le` at constant `2C`, then M7a) matches verbatim.

## (a) Math preflight verdict

**PASS** for the sole target (T1): `RBM.Gauss.norm_EEpath_offDiag_le`.

- **Statement vs paper/prior report.** The target is exactly M7b of
  `docs/reports/T1488-prove.md` §3 (audited PASS): hypotheses = all hypotheses of
  `EEDef.ee_le_EEpath_sym` except `hc0`/`hc1`, plus `h273`/`h564` supplied at both
  `c := Fin.append a a` and `c := Fin.append a' a'` with one common `ρ`, plus
  `{C : ℝ} (hC : 0 ≤ C)` and `hdisp : ∀ i, zdist (a i - a' i) ≤ C * ellStar Wr ℓu`. Conclusion:
  the displayed bound with loss `exp(√(2C)·(log Wr)^{3/4})` and widened indicator
  `dist ≤ (4+2C)·ellStar Wr ℓu`. I copied the conclusion literally from the report (§3, M7b)
  and cross-checked every subterm against `ee_le_EEpath_sym`'s own conclusion (Step 0).
- **Hypotheses / quantifier order.** `X E N u ω σ a a'` are universally quantified before the
  numeric parameters `ℓu ℓs ηu D J`, matching `ee_le_EEpath_sym`'s order (no fixed-parameter
  reordering). `C` and `hdisp` are additional, appearing after the shared hypotheses, as the
  ticket specifies. No hypothesis was added beyond what the ticket lists, and none of
  `ee_le_EEpath_sym`'s hypotheses were dropped except `hc0`/`hc1` (justified below).
- **Dependencies already accepted.** `ee_le_EEpath_sym` (T156/T167, merged, audited PASS per
  T1488), `norm_EEpath_offDiag_sq_le` (T1494, merged), `tailT_sub_le`/`tailT_antitone`/`ellStar`
  (pre-existing, `Analysis/StretchedExp.lean`), `zdist_add_le`/`zdist_neg` (pre-existing,
  `Defs/Dist.lean`, `Defs/Sums.lean`).
- **Boundary cases.** `C = 0`: `hdisp` forces `zdist(a i - a' i) = 0` for `i = 0,1`, i.e. `a`
  and `a'` agree on both labels (since `zdist` is `0` iff the argument is `0` — `zdist`'s
  codomain is `ℕ` and `ellStar ≥ 0`, so `C·ellStar = 0` forces `zdist = 0`); the bound then
  degenerates to (an upper bound for) the already-known `a' = a` case, with loss factor `1`
  and no widening — consistent, not vacuous.
- **Simultaneous satisfiability (nondegenerate witness).** Take `a' := a` and `C := 0`. Then
  `hdisp i : zdist (a i - a i) = zdist 0 = 0 ≤ 0 = 0 · ellStar Wr ℓu` holds by `zdist_zero`;
  `h273' = h273`, `h564' = h564` literally (since `a' = a`), so the whole hypothesis list
  collapses to exactly the hypothesis list of `ee_le_EEpath_sym` at `c := Fin.append a a`
  (`hc0`/`hc1` hold automatically at `a' = a` via `leftArg_append`/`rightArg_append`, so
  dropping them loses nothing at this witness). That list's simultaneous satisfiability was
  already established when `ee_le_EEpath_sym` (T156/T167) was audited PASS — this ticket does
  not need to re-derive it, only to confirm the added hypotheses (`C ≥ 0`, `hdisp`) do not
  make the total set empty, which the `a' = a, C = 0` witness shows. For `a' ≠ a` and `C > 0`
  the same base witness with `hdisp` relaxed (any `C` large enough that
  `zdist(a i - a' i) ≤ C · ellStar` for the two labels) remains satisfiable; taking `C` to be
  the max of the two (finite, since `zdist` and `ellStar > 0` are finite reals) always works,
  so the hypothesis set is nondegenerate for every choice of `a, a'` and not merely for
  `a = a'`.
- **`hc0`/`hc1` correctly dropped.** They are not silently omitted: at both call sites
  `c := Fin.append a a` and `c := Fin.append a' a'` they hold automatically (proved by `simp`
  using `leftArg_append`/`rightArg_append`, both giving `a 0` resp. `a' 0`), so their absence
  from the new theorem's hypothesis list does not weaken anything; they simply become internal
  lemmas of the proof instead of hypotheses, exactly as intended for the *matched* sub-cases
  `(a,a)` and `(a',a')` that feed the Cauchy–Schwarz step.
- **No hidden hypothesis on `C`.** The bound holds for every `C ≥ 0`; larger `C` only weakens
  the bound (bigger loss, wider indicator), it is never vacuous or false. Whether a given
  application's `C` (`ℓ_v/ℓ_u` per T1488 §3's discussion) keeps the loss harmless is explicitly
  left open, as the ticket instructs.

**Verdict: PASS.** Lean written after this preflight.

## (b) Declarations added, build, axioms

File: `RBM1D/Gauss/EEOffDiagBound.lean` (sole writable file).

Declarations:
- `RBM.zdist_sub_le_disp_add` (`{L} [NeZero L] (a a' : LoopArg L (0+2))`): the ℕ-valued
  displacement triangle inequality `zdist(a 0 - a 1) ≤ zdist(a 0 - a' 0) + zdist(a' 0 - a' 1)
  + zdist(a 1 - a' 1)`, from `zdist_add_le` (twice) and the pre-existing `zdist_neg`.
- `RBM.Gauss.ellStar_nonneg'` (`private`): `0 ≤ ellStar W ℓu` given `1 ≤ W`, `0 < ℓu`.
- `RBM.Gauss.le_sqrt_mul_add_of_sq_le_mul` (`private`): the isolated real-number fact
  `v² ≤ (x+y)(L2·x+y) ∧ x,y ≥ 0 ∧ 1 ≤ L2 ⟹ v ≤ √L2·(x+y)`, used for the final
  Cauchy–Schwarz-to-bound step.
- **`RBM.Gauss.norm_EEpath_offDiag_le`** — target **(T1)**, the M7b bound verbatim (statement
  reproduced in §(a) above; see the file for the full signature). No `norm_EEpath_offDiag_
  le_reduced` variant was written: the ticket makes that variant optional ("may replace... if
  you do this"), and M7b's own spec (T1488 §3) calls for `ee_le_EEpath_sym`, which I used
  directly, so the reduced replacement was not needed.

Build:
```
lake build RBM1D.Gauss.EEOffDiagBound
```
Result: **success** (`Built RBM1D.Gauss.EEOffDiagBound`), no warnings from the new file. All
warnings in the build log are from pre-existing files upstream in the import chain
(`SumZeroDyn.lean`, `Dynamics.lean`, `Decay.lean`, `EEBridge.lean`), unrelated to this ticket.

Axioms (via `lake env lean` on a scratch file `import RBM1D.Gauss.EEOffDiagBound`):
```
#print axioms RBM.Gauss.norm_EEpath_offDiag_le
  ↦ [propext, Classical.choice, Quot.sound]
#print axioms RBM.zdist_sub_le_disp_add
  ↦ [propext, Quot.sound]
```
Only the three allowed axioms. No `sorry`, `admit`, or declared `axiom` anywhere in the file
(checked by `grep`).

## (c) Key lemmas used

`EEDef.ee_le_EEpath_sym` (applied at both `Fin.append a a` and `Fin.append a' a'`),
`Gauss.norm_EEpath_offDiag_sq_le` (M7a, T1494), `tailT_antitone`, `tailT_sub_le`,
`zdist_add_le`, `zdist_neg` (pre-existing), `EEBridge.leftArg_append`/`rightArg_append`,
`EEDef.lab₁`/`lab₂`, `Lemma57.cNear2_nonneg`/`cFar2_nonneg`, `EEDef.one_le_W`.

## (d) Open issues

- None specific to this ticket. As T1488 §3 already notes and this ticket does not decide:
  whether the loss factor `exp(√(2C)(log W)^{3/4})` and the widened indicator threshold
  `(4+2C)ℓ*_u` are harmless depends on the size of `C` in the eventual application to (5.42)
  (`C = ℓ_v/ℓ_u` for the later time `v` supplying the displacement, per T1488 §3's discussion
  of `Step3.ellHat_mono`/`Step2FarMart.ellStar_mono_time`); that bookkeeping is for A5.
- No paper-delta needed: the Lean statement matches the ticket/T1488 §3 M7b target verbatim,
  and Step 0 confirmed `tailT_sub_le`'s loss factor matches the ticket's assumed shape exactly
  (no discrepancy to record).
