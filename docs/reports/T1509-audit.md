Auditor model: claude-opus-5-5[1m]

# T1509 — audit report

Branch `t/T1509` (commit 40fb9f2), audited in a fresh worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1509-audit2` (not the prover's worktree). Diff vs `main`:
exactly one added file, `RBM1D/Gauss/GridQVConv.lean` (the sole writable file). No other file
touched; no frozen signature changed.

Sources checked: ticket `docs/tickets/T1509.md`; supervisor `docs/supervisor/2026-09-25-2045.md` §3 (ii);
signatures of `Step2.norm_Uker_le_of_tail` (`Hierarchy/Step2.lean:448`), `Uker`/`Uker_apply`,
`edgeKer`/`edgeKer_eq` (`Hierarchy/Kernel.lean`), `ellHat` (`Propagator/Decay.lean:480`),
`tailT`/`tailT_pos` (`Analysis/StretchedExp.lean`), M7a `Gauss.norm_EEpath_offDiag_sq_le`
(`Gauss/EEOffDiag.lean:146`).

## 1. Math preflight
`docs/reports/T1509-prove.md` §(a) contains a math preflight per target, both PASS, written before
the Lean section. OK.

## 2. Target (T1) `RBM.Gauss.Grid.Uker_one_nonneg` — PASS
Statement: `3 ≤ L`, `0 ≤ u`, `u ≤ v`, `v < 1`, `a b : LoopArg L 2` ⟹
`∃ r ≥ 0, ∏ i : Fin 2, edgeKer L 1 u v (a i) (b i) = (r : ℂ)`.
Since `Uker L ξ s t A a = ∑ b, (∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A b` (`Uker_apply`, rfl),
with `ξ = fun _ => 1` this product is exactly the kernel entry of `Uker L (fun _ => 1) u v`. Window
`0 ≤ u ≤ v < 1` is the ticket's; `hL : 3 ≤ L` is the standing hypothesis of `edgeKer_eq`/`Theta_eq_tsum`.
Proof follows the ticket route (edgeKer_eq → 1 + (v−u)·SB·Θ_v; Θ_v via Neumann series, entrywise
nonnegative-real). Boundary `u = v` is allowed and harmless.
Note (non-blocking): the ticket's "Consequently `‖(Uker … A) b‖ ≤ (Uker … ‖A‖) b`" is not exported as a
separate public lemma; its content is realized by the private helper `sum_edgeProd_mul_ofReal_norm_eq`
(an exact equality for nonnegative real weights) and is a two-line corollary of (T1) + `norm_sum_le`.
The acceptance criteria name only (T1)–(T2), so this is not a defect.

## 3. Target (T2) `RBM.Gauss.Grid.qv_conv_le` — PASS
Hypotheses: exactly those of `norm_Uker_le_of_tail` (`hL, hm0, hm1, hu0, huv, hv0, hv1, hW : exp 1 ≤ W,
hAuv`) plus `hQ : 0 ≤ Q`, `R ≥ 0`, `hR : R a ≤ Q · tailT W ℓ̂(u) ((1−u)m) D (dist a)²`,
`hEE : ‖EE a a'‖ ≤ √(R a)·√(R a')`. Conclusion:
`‖∑_{a,a'} K(b,a)·conj K(b,a')·EE a a'‖ ≤ (√Q · ((1−u)/(1−v))² · xiK L W m · tailT W ℓ̂(v) ((1−v)m) D (dist b))²`
with `K(b,a) = ∏ i, edgeKer L 1 u v (b i) (a i)` — the kernel of `Uker … u v` at row `b`, and
`dist x = zdist L (x 0 − x 1)`. This matches the ticket formula verbatim (r = (1−u)/(1−v), same tail
profiles at u and v, same `m`, `D`, `W`).
- **No loss factor**: the right side is exactly `(M · r² · xiK · T_v)²` with `M = √Q`, i.e. the square
  of the `norm_Uker_le_of_tail` bound. No `e^λ`, no widened indicator, no extra constant. The only
  `W^{o(1)}` factor is `xiK`, inherited from the accepted dependency and explicitly part of the ticket's
  target (it encodes the paper's near-diagonal `1(|a₁−a₂| ≤ ℓ*)` term, per supervisor §3 (ii)).
- **M7a only, not M7b**: M7a gives `‖EE(a,a')‖² ≤ ‖EE(a,a)‖·‖EE(a',a')‖`; with `R a := ‖EE(a,a)‖` this
  yields exactly `hEE` (after `Real.sqrt`), so the hypothesis shape is what M7a delivers. The file
  imports only `RBM1D.Hierarchy.Step2`; the M7b module `RBM1D.Gauss.EEOffDiagBound` (T1498) is imported
  by no file under `RBM1D/`, so it is not in the import closure. No M7b-shaped hypothesis appears.
- Parameter order: deterministic lemma, no `N`; all parameters fixed. OK.
- Redundancies (harmless): `hv0` follows from `hu0, huv`; `_hR0` is unused (kept as the ticket's
  hypothesis). Neither restricts the statement.
- σ = (+,−) ↔ ξ ≡ 1, n = 2: this is the scope of the dependency, accepted by the supervisor note.

## 4. Vacuity / satisfiability
`hAuv` is not a hidden restriction: `ellHat L v = min((1−v)^{-1/2}, L)` for real `v ∈ [0,1)`, so
`ellHat(v)(1−v) = min((1−v)^{1/2}, L(1−v))` is nonincreasing, hence `hAuv` holds for every
`0 ≤ u ≤ v < 1`, `m > 0`, `W > 0`. Compiled nondegenerate witness (scratch file, `lake env lean` in the
audit worktree, no errors): `L = 3, m = 1, u = 0, v = 1/2, W = e, D = 1, Q = 1`,
`R a = tailT_u(dist a)² > 0` (via `tailT_pos`), `EE a a' = √(R a)·√(R a')` (nonzero, `hEE` with
equality), with `hAuv` proved at these values; `qv_conv_le` applies. No `N = 0`, empty index set,
collapsed window, or astronomically large quantity needed (`u < v` strictly, `W = e`). No structure
fields, no circularity (depends only on committed `Step2`/`Kernel`/`Propagator` lemmas).

## 5. Dependencies
`norm_Uker_le_of_tail`, `Uker_apply`, `edgeKer_eq`, `Theta_eq_tsum`, `summable_norm_pow`,
`norm_entry_le_norm`, `SB_apply`/`sbKernel`, `tailT_nonneg` — all committed on `main`. M7a (T1494,
merged) is used through its hypothesis shape only. OK.

## 6. Build and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridQVConv`: success (3749 jobs), 0 errors, no warnings in GridQVConv.
- `lake build RBM1D`: success (9655 jobs), 0 errors (root import of GridQVConv is added at merge).
- `#print axioms` for `RBM.Gauss.Grid.Uker_one_nonneg` and `RBM.Gauss.Grid.qv_conv_le`:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`admit`/`axiom`/`native_decide` in the file.

## 7. Acceptance criteria
- (T1)–(T2) with the ticket names: yes.
- No `sorry`/`admit`/`axiom`: yes.
- First report line `Prover model: <id>`: yes (`claude-sonnet-5`).
- (T2) no loss factor, M7a only, hypotheses satisfiable: yes (§3, §4).

## Open notes (non-blocking)
- The supervisor §3 steps (i) (matrix identity for the conditional variance) and (iii) (discrete
  Riemann sum (5.44)) are outside this ticket and remain open.
- No new Lean/paper difference is introduced by this file beyond those already carried by
  `norm_Uker_le_of_tail` (ξ ≡ 1 / n = 2 scope, `xiK` factor); no paper-deltas entry needed.

## Verdict
(T1) PASS. (T2) PASS. **T1509: PASS.**
