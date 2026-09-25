Auditor model: claude-opus-5-5[1m]
Audited against: `docs/tickets/T1504-amend-1.md` (targets (T1′), (T1″), (T2), (T3) with the guarded hypothesis), with the acceptance criteria of `docs/tickets/T1504.md` applied to them as amend-1 directs. The original T1504.md target (T1) is not an acceptance target; the prior RETURN (commit d1c2e95) was audited against the original spec by mistake.

# T1504 re-audit after repair: stopped Duhamel martingale tail bounds

Branch `t/T1504`, commit `b1d4b49`. Fresh audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1504-audit2`, a detached checkout. Neither the repairer's worktree `RBM1D-wt/T1504` nor the earlier `RBM1D-wt/T1504-audit` was reused. No stale `GridDuhamelTail` artifact was in the copied cache, so the module was compiled from scratch.

**Overall verdict: PASS.** (T1′) PASS, (T1″) PASS (non-vacuous reading; adjudication below), (T2) PASS, (T3) PASS (a conditional adapter for `t > 1/2`, as disclosed).

## Build, axioms, scope

- `lake build RBM1D.Gauss.GridDuhamelTail`: Build completed successfully (3711 jobs). The only warning in this file is `hR` not referenced (line 666, (T3)), which is documented.
- `lake build RBM1D`: Build completed successfully (9649 jobs), no errors. The root import is added at merge.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 9 public declarations: `stoppedEdge_apply`, `stopped_duhamel_azuma_tail_fixed`, `stopped_duhamel_azuma_union`, `stopped_duhamel_azuma_tail`, `stopped_duhamel_cheb_tail`, `stopped_duhamel_det_bound`, `norm_Uker_fwd_le_of_le_half`, `hFwd_of_le_half`, `stopped_duhamel_det_bound_half`.
- No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern` (grep).
- `git diff --stat $(merge-base) b1d4b49` touches only `RBM1D/Gauss/GridDuhamelTail.lean` (new file, +1055). No frozen signature is touched.
- No file in `RBM1D/` or `RBM1D.lean` other than this one references the module or `stopped_duhamel_azuma_tail`.

## Math preflight

`docs/reports/T1504-prove.md` §(a) is a math preflight written before the new Lean. It gives a PASS verdict and reasons for each amend-1 target, and flags the (T1″) `k = 0` issue explicitly. Present.

## Dependencies

- `azuma_complex` (T1484), `sum_stopped` (GridStop), `norm_Uker_back_le` (T1500), `norm_Uker_apply_le`, `Uker_comp` and `Uker_apply` (Kernel), `UkerHom_apply` (T1485). All are merged and accepted.
- The rest is Mathlib.
- No cycle.
- The original (T1) is used only by its own witness `example`.

## (T1′) `stopped_duhamel_azuma_tail_fixed`: PASS

**Statement vs amend-1.** Fixed `k` and `a`. `c : ℕ → LoopArg L n → ℕ → ℝ≥0` is a parameter independent of `ω`, so it is deterministic and may depend on `(k, a)`.

- **Hypothesis.** For `j < k`, the re/im of `{ω' | j < τ ω'}.indicator (fun ω' => Uker L ξ (u (j+1)) (u k) (Z (j+1) ω') a) ω` are `HasCondSubgaussianMGF (ℱ j) (ℱ.le j) · (c k a j) μ`.
- **Conclusion.** `μ.real {x ≤ ‖(∑ j ∈ range (min k (τ ω)), U (j+1) k (Z (j+1) ω)) a‖} ≤ 4 * exp (-x^2 / (4 * ∑ j ∈ range k, c k a j))` for `0 ≤ x`. This is exactly the amend formula.
- **Setting hypotheses.** Only `{j < τ} ∈ ℱ j` and adaptedness of `Z` are used; these are part of the T1504 setting. The unused setting hypotheses (`k ≤ K`, `‖ξ‖ ≤ 1`, monotone `u`) are dropped, which generalises the statement.
- **No `U⁻¹`.** Confirmed from the proof (lines 328-334): it is `stopped_sum_apply_eq` (`sum_stopped`) and then `azuma_complex` on the prepended family. There is no backward factorisation, no `norm_Uker_back_le` and no label union.
- **Boundary cases.** `k = 0` and `Σc = 0` give a right-hand side of `4` under `a/0 = 0`, which is true. This convention is written into the amend formula itself, and it only weakens the degenerate `Σc = 0` case.
- **Witness.** Nonzero Gaussian. The model is `Ω' = ℝ`, `μ = gaussianReal 0 1`, `ℱ 0 = ⊥`, `ℱ (i+1) = borel`, `n = 0`, `τ ≡ 1`, `Z 1 ω = ω`, `c ≡ 1`. The example applies the theorem, discharges `hsubG` through a proved conditional sub-Gaussian lemma given `⊥`, and yields `γ{x ≤ |ω|} ≤ 4 e^{-x²/4}`. This is a genuinely informative Gaussian tail, below 1 for large `x`. A `Z = 0` witness is also compiled.

## (T1″) `stopped_duhamel_azuma_union`: PASS

**Adjudication of the `k = 0` deviation.** I verified the repairer's claim independently.

1. **The literal form is vacuous.** In the literal amend statement the RHS is summed over `k ∈ range (K+1)`. At `k = 0` the inner constant sum is empty, and `a/0 = 0` gives `4 * exp 0 = 4`, so the `k = 0` block contributes `4 L^n ≥ 4`. The compiled `example` (lines 1023-1041) proves `μ.real S ≤ literal RHS` for every probability measure, every set `S` and all `L, n, K, c, x`. It needs no hypothesis on `τ`, `Z` or `ℱ`. I checked that the proof uses only `Finset.sum_range_succ'`, `div_zero`, `card_loopArg_eq`, positivity and `measureReal_le_one`, and nothing about the data. Accepting the literal form would therefore accept a theorem with no content. That is exactly what CLAUDE.md §3.4 forbids.
2. **The proved form keeps the event and implies the literal form.**
   - The event `{∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ range (min k (τ ω)), U (j+1) k (Z (j+1) ω)) a‖}` is kept verbatim, including `k = 0`.
   - The RHS is `∑ k ∈ Icc 1 K, ∑ a, 4 exp(-(x k a)^2/(4 Σ_{j<k} c k a j))`. It is at most the literal RHS, because the dropped block is nonnegative.
   - All `hsubG` hypotheses have the amend's shape, for all `k ≤ K`, all `a` and all `j < k`.
3. **The added hypothesis `hx0 : ∀ a, 0 < x 0 a` is necessary and costs nothing.**
   - Without it the Icc form is false. Take `K = 0` and `x 0 a = 0`: the event is the whole space (`0 ≤ ‖0‖`), while the RHS is the empty sum `0`.
   - It is exactly the condition under which the paper's own `k = 0` term, read in real arithmetic as `4 exp(-x²/0⁺) = 0`, vanishes, and under which the `k = 0` event is empty.
   - Downstream thresholds are positive, of `N^ε` scale.
   - `hx` for `k = 0` is then redundant but harmless.
4. **The proved form is non-vacuous.** The compiled `K = 1` Gaussian example applies the theorem and yields `γ{x ≤ |ω|} ≤ 4 e^{-x²/4}` for `x > 0`, which is below 1 for large `x`.
5. **Intent is preserved.** On `{τ = k}` the `k`-th sum is the stopped linear Duhamel term at `u_τ`. The `k = 0` case (`τ = 0`) contributes the zero vector, which exceeds no positive threshold. So the proved form carries the whole mathematical content the amend needs for the (2.76) route.

**Decision.** The proved statement is the paper-convention reading of `Σ_{k ≤ K}`, with Lean's `/0` artefact removed. It is strictly stronger than the literal Lean transcription, and the literal transcription is demonstrably content-free. No reading of the literal form could serve a consumer. This is the vacuity avoidance required by §3.4 rather than a change of target, so I do not require dispatcher sign-off for acceptance. PASS.

**Recommendation (non-blocking).** The dispatcher may record this in `docs/paper-deltas.md`, together with (T2) `x > 0` and the (T3) `hFwd` hypothesis. These are Lean-vs-ticket precisions that change no paper statement.

## (T2) `stopped_duhamel_cheb_tail`: PASS

**Statement.** The content is the one audited before. The RHS is `L^n * (Σ_{j<K} e j) / x^2`, over the full horizon, with deterministic `e : ℕ → ℝ` and union factor `L^n`.

**Changes since the prior audit.**
- All five hypotheses (`hYmeanRe/Im`, `hYmemLpRe/Im`, `hYbound`) now state the stopped indicator inline.
- The unused `he0` was dropped, which generalises the statement.
- `0 < x` is kept. It is necessary, since at `x = 0` the RHS is `0`.

**Witnesses.**
- `Y = 0` covers all five hypotheses (`e ≡ 0`).
- A nonzero Gaussian example (`e ≡ 1`) discharges all five hypotheses:
  - the conditional mean given `⊥` via `condExp_bot` and `integral_id_gaussianReal`;
  - `MemLp 2` via `memLp_id_gaussianReal'`;
  - `∫ω² = 1` via `variance_id_gaussianReal`.

  It yields `γ{x ≤ |ω|} ≤ 1/x²`.

## (T3) `stopped_duhamel_det_bound`: PASS (conditional adapter for t > 1/2)

**Statement vs amend-1.**
- `R : ℕ → Ω' → V`.
- The hypothesis is exactly `hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j`, which carries the `j < τ ω` guard.
- Conclusion, for all `ω, a`: `‖(∑ j ∈ range (τ ω), U (j+1) (τ ω) (R j ω)) a‖ ≤ 2^n * (2^n * ∑ j ∈ range K, r j)`. This is the T1504.md constant, over the full horizon.
- The docstring states "for the O(Δ^{3/2}) errors only, **not for the drift**".

**`hFwd`.** `hFwd` is guarded the same way. Its use is allowed by T1504.md Step 0 ("state it as a hypothesis with a satisfiability witness"). The proof uses `hFwd`, not `hR`, and the docstring discloses that (T3) is a conditional adapter. The reason is correct: the forward row bound `1 + (t-s)‖ξ‖/(1-t‖ξ‖)` is unbounded as `t‖ξ‖ → 1⁻`.

**Nondegenerate witness (prior defect 3).**
- `norm_Uker_fwd_le_of_le_half` holds for any `ξ` with `‖ξ i‖ ≤ 1` and `0 ≤ s ≤ t ≤ 1/2`. It gives `‖Uker s t A a‖ ≤ 2^n M` via `norm_Uker_apply_le` with `C = 2`.
- The arithmetic is correct: `‖tξ‖ ≤ 1/2` gives `(1-‖tξ‖)⁻¹ ≤ 2`, and `‖(s-t)ξ‖ ≤ 1/2`, so `C ≤ 1 + (1/2)·2 = 2`.
- `hFwd_of_le_half` turns the guarded `hR` into the guarded `hFwd` for any grid with `u K = t ≤ 1/2`.
- `stopped_duhamel_det_bound_half` is (T3) without `hFwd` in that regime.
- The concrete example uses `n = 1`, `ξ = 1` (`Uker` is not the identity), `u 1 = 1/4 < t = 1/2` and `R ≡ 1`.

For `t ∈ (1/2, 1)` with general `ξ`, downstream must still discharge `hFwd` from the specific remainder. This is disclosed and is not a defect under Step 0.

## Prior "Required fixes"

1. **Nonzero Gaussian witnesses: fixed.** They are compiled for (T1′), (T1″), (T1) and (T2), and each applies the theorem itself. The (T2) `Y = 0` witness now covers all five hypotheses.
2. **`stoppedEdge`: fixed.** Every public signature states the indicator inline. `stoppedEdge` is now a public `noncomputable def` with docstring, and `stoppedEdge_apply` is an `rfl` unfolding lemma.
3. **`hFwd` for general ξ: fixed** (see (T3)).

## Other amend-1 checks

- (T1′) uses no `U⁻¹`: confirmed.
- `c k a j` is deterministic: confirmed from its type.
- (T3) carries the `j < τ ω` guard: confirmed.
- **Original (T1).** `stopped_duhamel_azuma_tail` is kept. Its docstring says "Sup-norm; does not suffice for (2.76), see supervisor 2026-09-25-2045 §1. No consumer may use it." No declaration consumes it; only its witness `example` does. Its signature changed only by inlining the indicator.
- **Vacuity/loopholes.**
  - No `N = 0` or empty-index loophole beyond the (T1″) `k = 0` artefact, which was removed as above.
  - No structure-field hypotheses.
  - No astronomically large witness: every witness uses unit constants.
  - `L ≥ 3` and `‖ξ‖ ≤ 1` are satisfiable.
- **Lint (non-blocking).** The file ends with `#print axioms` lines. Remove them at merge if repo convention requires it.

## Verdicts

| Target | Verdict |
|---|---|
| (T1′) `stopped_duhamel_azuma_tail_fixed` | PASS |
| (T1″) `stopped_duhamel_azuma_union` | PASS (Icc 1 K + `hx0` form accepted; the literal form is compiled-vacuous) |
| (T2) `stopped_duhamel_cheb_tail` | PASS |
| (T3) `stopped_duhamel_det_bound` | PASS (conditional on `hFwd` for t > 1/2; discharged for t ≤ 1/2) |
