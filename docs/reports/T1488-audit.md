Auditor model: claude-opus-5-5[1m]

# T1488 re-audit 2 (revision 3 of the prove report): read-only inventory of the discrete Step 2 inputs

Ticket: `docs/tickets/T1488.md` (report only; no Lean, no branch commits, no module to build).
Report audited: `docs/reports/T1488-prove.md`, revision 3 (second repair cycle, answering D7 and D8 of the previous audit).

**Verdict: PASS.** D7 and D8 are fixed. All citations newly introduced for them exist at the claimed file:line, and I `#check`-ed them. M7b's exponent and constant match what `tailT_sub_le` proves. The report's correction of my previous audit (`ℓ*_t ≤ ℓ*_u` is backwards) is right. I found no regression in the rows and targets that were not changed.

## 1. First line of the report

The first line is, verbatim: `Prover model: claude-opus-5-5[1m]`

I checked the raw bytes with `od -c`: `P r o v e r   m o d e l :   c l a u d e - o p u s - 5 - 5 [ 1 m ] \n`. There is no BOM, no ESC byte, no trailing whitespace and no stray character. `[1m]` is part of the model id, not an ANSI escape.

## 2. Gates for a report-only ticket

- **Math preflight.** Section (a) gives PASS for the inventory target, placed before the tables. There is no Lean target, so no Lean preflight applies.
- **Lean statement, vacuity, build, axioms.** Not applicable, because no `.lean` file was written. `git diff --stat main -- RBM1D` is empty for tracked files. The untracked `.lean` files in `RBM1D/Gauss/` are neither cited by T1488 nor attributable to it.
- **Sole writable file.** Only `docs/reports/T1488-prove.md` was written.

## 3. D7 (row A3): fixed

I verified all six citations myself: file:line by `grep -n` on the keyword line, the statements by reading them, and the names by `#check` (section 6).

| Declaration | Claimed | Verified | Statement agrees with report |
|---|---|---|---|
| `RBM.Gauss.stochDom_ldeRow` | Gauss/LDEHyp.lean:221 | yes | `hLrow` for `Hflow d N u ω`. Hypotheses are only `0 ≤ u`, `u ≤ 1`, `z.im ≠ 0`, for every `d`. |
| `RBM.Gauss.stochDom_ldeCol` | Gauss/LDEHyp.lean:246 | yes | `hLcol`, with the same hypotheses. |
| `RBM.Gauss.entry_bound_gauss` | Gauss/EntryBoundGauss.lean:42 | yes | Hypotheses: `0 ≤ u ≤ 1`, `z.im ≠ 0`, `‖m‖ = 1`, `0 ≤ δ N`, `0 < c₀`, `∀ᶠ N, δ N ≤ N^{-c₀}`. It has no large-deviation hypothesis; its body is `entry_bound_stochDom` fed by `stochDom_ldeRow`/`_ldeCol`. |
| `RBM.Gauss.diag_bound_gauss` | Gauss/EntryBoundGauss.lean:61 | yes | Stated at `z = zt E t`, `m = mE E`. Hypotheses: `0 < κ ≤ 1`, `|E| ≤ 2−κ`, `0 ≤ t < 1`, plus the δ conditions. It uses `stochDom_ldeQuad` and `stochDom_normSq_Hflow_diag`. |
| `RBM.Gauss.stochDom_ldeRow_flow` | Gauss/LDEFlow.lean:421 | yes | Indexed by `TimeIcc s t N × OffPair`. Assumes `hΞ : HighProb Ξ` and `hclose : LDENetClose d E s t Ξ δ`. |
| `RBM.Gauss.stochDom_ldeCol_flow` | Gauss/LDEFlow.lean:442 | yes | Same shape as the row version, also conditional on `LDENetClose`. |

- `import RBM1D.Gauss.EntryBoundGauss` is at RBM1D.lean:144, as the report says.
- The row now has three correct parts:
  - the fixed-time unfloored (4.2)/(4.3) are discharged for every `d`;
  - the fixed time is one real constant independent of `N`, so it does not cover an `N`-dependent grid or a family of times;
  - the time-uniform unfloored form is conditional on `LDENetClose`, and the time-uniform floored form is discharged.
- The row's Unif. u and Dims cells agree with these three parts.

## 4. D8 (target M7): fixed

**M7a (Cauchy–Schwarz) is correct, and it needs no extra hypothesis.** I checked the definitional chain:
- `MomentDuhamel.EEpath` (Gauss/MomentDuhamel.lean:404) is `eeFun B E N u (X.H N u ω) σ c`.
- `eeFun` (Gauss/MomentDuhamelEEFunCore.lean:23) is `EEBridge.eeArg B.toDims N (zt E u) M σ c`.
- `eeArg_append` (Hierarchy/EEBridgeArgCore.lean:55) turns this into `eeTens (toIdx σ a) (toIdx σ a')`.
- `eeTens` (Gauss/DischargeBDG.lean:334) is `∑_{k<I.length} eeEdge`, and `eeEdge` (:328) is `∑_{i,j} emartEdge I k i j · conj(emartEdge I' k i j)`.
- So `eeTens I I'` is the Hermitian inner product `⟨v(I), v(I')⟩` over `(k, i, j)`. For `a` and `a'` of the same length the index ranges agree.
- `|⟨v,w⟩|² ≤ ⟨v,v⟩⟨w,w⟩` then gives M7a as stated. The diagonal values are nonnegative reals, so `‖·‖` equals the value.

**M7b is a precise Lean-shaped target, with an explicit loss.**
- **Right side.** Its right side is exactly the right side of `ee_le_EEpath_sym` (EEDef.lean:1294, re-read), with two changes: the near indicator is widened to `(4+2C)·ellStar`, and the whole expression is multiplied by `exp(√(2C)·log W^{3/4})`. The remainders `Wr·Lr·ρ + 2·Wr·Lr·Wr^{-D}(2J)³T²` are written out.
- **Distance.** In `ee_le_EEpath_sym` the distance is `zdist(lab₁ c − lab₂ c)`. Since `lab₁ c = leftArg c 0` and `lab₂ c = leftArg c 1` (EEDef.lean:317/320), `c = Fin.append a a` gives `zdist(a 0 − a 1)`, which is the M7b `dist`.
- **Hypotheses.** `hGm`, `hGsq*`, `hrow`, `hSmax` and `h42sq` do not mention `c`. `h273` and `h564` do, and M7b correctly requires them at both diagonal arguments. `hc0`/`hc1` hold there by `leftArg_append`/`rightArg_append` (EEBridgeArgCore.lean:35/38).
- **Exponent and constant.** `tailT_sub_le` (Analysis/StretchedExp.lean:337), as printed by `#check`, is `1 ≤ W → 0 < ℓu → 0 ≤ C → tailT W ℓu ηu D (ℓ − C·ellStar W ℓu) ≤ exp(√C · log W^{3/4}) · tailT W ℓu ηu D ℓ`. The steps are:
  - Assume `zdist(a i − a' i) ≤ C·ℓ*_u` for `i = 0, 1`.
  - `zdist_add_le` (Defs/Dist.lean:33) and `zdist_neg` (Defs/Sums.lean:48) give `dist ≤ dist' + 2C·ℓ*_u`.
  - `tailT_antitone` (:307) and `tailT_sub_le` at constant `2C ≥ 0` then give `T(dist') ≤ exp(√(2C)·log W^{3/4})·T(dist)`.
  - The factor `e^{λ}` with `λ = √(2C)(log W)^{3/4}` is therefore exactly what the cited lemma yields. The side conditions `1 ≤ W` and `0 < ℓu` follow from `one_le_W` and `hℓu : 1 ≤ ℓu`.
- **Combination step.** With `x = K̄T² ≥ 0` (using `cNear2_nonneg`, `cFar2_nonneg`, `J ≥ 1`, `A > 0`) and `y = Wr·Lr·ρ ≥ 0`, we have `R(a,a) ≤ x + y` and `R(a',a') ≤ e^{2λ}x + y`. Then `(x+y)(e^{2λ}x+y) ≤ e^{2λ}(x+y)²`, and M7a closes the bound with factor `e^{λ}`. The argument is sound.
- **Loss and satisfiability.** The report states plainly that the loss is `W^{o(1)}` only if `C = o((log W)^{1/2})`, and leaves the value of `C` to A5. That is honest and adequate for an inventory. `hdisp` is satisfiable nondegenerately for any `C > 0`; `C = 0` forces `a' = a`.
- **Estimate.** The estimate of 1–2 tickets (M7a ½–1, M7b about 1) is plausible.

## 5. Correction of my previous audit: confirmed

My previous D8 text said to fix `C` by "`max_i |a_i − a'_i| ≤ ℓ*_t ≤ ℓ*_u`". For `u ≤ t` that inequality is backwards.
- `Step3.ellHat_mono` (Flow/FlowFamiliesCore.lean:29) states `s ≤ t → t < 1 → ellHat L s ≤ ellHat L t`, because `ellHat L x = min(1/√(1−x), L)`.
- `Step2FarMart.ellStar_mono_time` (Hierarchy/Step2FarMart.lean:328) states `w ≤ v → v < 1 → ellStar W (B.ell N w) ≤ ellStar W (B.ell N v)`.
- So `ℓ*_u ≤ ℓ*_t`, and a displacement on scale `ℓ*_t` corresponds to `C = ℓ_t/ℓ_u ≥ 1`, as the report says.
- The error was in my audit's suggested wording, not in the prover's report. It does not affect the RETURN reasons of the previous audit, which concerned M7's lack of precision and its `1 + o(1)` claim.

## 6. Citation checks

- **`#check`.** One scratch file outside the repo (`import RBM1D`), run with `lake env lean` in the main worktree: rc 0, no error, no unknown identifier, no `sorry`. It covered 24 names:
  - `stochDom_ldeRow`, `stochDom_ldeCol`, `entry_bound_gauss`, `diag_bound_gauss`, `stochDom_ldeRow_flow`, `stochDom_ldeCol_flow`;
  - `tailT_sub_le`, `tailT_antitone`, `ellStar`;
  - `EEDef.ee_le_EEpath_sym`, `MomentDuhamel.EEpath`, `Gauss.eeTens`, `Gauss.eeEdge`;
  - `EEBridge.eeArg_append`, `leftArg_append`, `rightArg_append`, `zdist_add_le`;
  - `Step3.ellHat_mono`, `Step2FarMart.ellStar_mono_time`;
  - `Lemma57.cNear2`, `Lemma57.cFar2`;
  - `entry_bound_stochDom`, `diag_bound_stochDom`, `EEUker.quadVar_qUkerObsT_le_norm_QQ_eeFun'`.
- **Regression spot-check on the current `main` (e6b6894), by file:line keyword match.** All 12 match:

| Declaration | File:line |
|---|---|
| `step1Hyp_gauss_of_scale''` | EntryBoundTime:654 |
| `ee_le_sym` | Lemma57:2661 |
| `eG_le_reduced` | Lemma57:1463 |
| `eGpm_le_rhs535_of_jS` | Step2FarInputs:2224 |
| `jStar` | EarlyQVRateEv:146 |
| `entry_bound_stochDom` | EntryBound:1512 |
| `entry_bound_stochDom_floor_idx` | EntryBoundFloor:730 |
| `stochDom_ldeRow_flow_floor` | LDENetClose:747 |
| `norm_Theta_le_of_ellStar` | Step2:1830 |
| `norm_Uker_tail_le_ellStar` | KernelDecay:2314 |
| `BoundsCore.decay` | Hypotheses:278 |
| `ee_le_paper_EEpath_sym` | EEDef:1359 |

The earlier audits checked more than 50 other citations.

## 7. Completeness and regressions

- Table A (A1–A5), Table B (B1–B3) and table 2b have every cell filled, with no placeholder.
- Rows A1, A2, A4, A5, B1–B3 and 2b, and targets M1–M6, are unchanged in substance from revision 2, which the previous audit accepted.
- Every missing row points to a precise target in M1–M7. The total estimate is 9–12 tickets.
- A minor point carried over from the previous audit, not a RETURN reason: §3 lists `Cond272` among the "Step-1 hypotheses". The cited witness `eventually_commonEvent_nonempty` uses `Cond272Reg`, which is `Cond272` plus `hreg`; the content is equivalent.
- Open issue 1 (`jStar` is not the paper's J; paper-delta candidate `T1488a`) and open issue 2 (a suspected unsatisfiable `h560` in `eGpm_le_rhs535_of_jS`, not compiled) remain flagged for the dispatcher.

## 8. Verdict

**PASS.** The inventory is complete, every citation checked exists at its file:line, and every missing statement is precise enough to become a ticket target.
