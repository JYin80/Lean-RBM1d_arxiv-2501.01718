Prover model: claude-sonnet-5

# T1510 — weighted Duhamel sum for the drift terms, (5.39)–(5.41) on the grid

Ticket `docs/tickets/T1510.md`. Worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1510`. Sole
writable file `RBM1D/Gauss/GridDriftSum.lean`.

## (a) Math preflight (written before any Lean)

Sole source: paper (5.39)–(5.41), p. 57. Dependency accepted: `RBM.Step2.norm_Uker_le_of_tail`
(`Hierarchy/Step2.lean:448`, committed). T1508 was still `state: proving` (not merged) when this
ticket was executed, so its (T1) `tailT_mono_time` is reproved locally, cited as such.

**Step 0 checks.**
* `norm_Uker_le_of_tail` (`RBM.Step2.norm_Uker_le_of_tail`, `Hierarchy/Step2.lean:448`): for
  `σ = (+,-)` (`ξ = fun _ => 1`, `n = 2`), `3 ≤ L`, `0 < m ≤ 1`, `0 ≤ u ≤ v < 1`, `exp 1 ≤ W`,
  `hAuv : W·ℓ̂(v)·((1-v)m) ≤ W·ℓ̂(u)·((1-u)m)` (the side condition, a genuine hypothesis of the
  lemma, not derived inside it), and `‖A b‖ ≤ M·T_{u,D}(‖b₀-b₁‖)`, concludes
  `‖Uker(u,v)(A) a‖ ≤ M·((1-u)/(1-v))²·xiK L W m·T_{v,D}(‖a₀-a₁‖)`. `m` is the raw scalar in
  `η_x := (1-x)m` (not a wrapped `etaT`/Sample quantity) — the lemma and hence this ticket's
  targets are purely deterministic, matching the ticket's own characterisation of (T1)/(T2) as
  "a deterministic statement".
* `xiK` (`RBM.Step2.xiK`, line 433) is the `W^{o(1)}` factor; `tailT` (`RBM.tailT`,
  `Analysis/StretchedExp.lean:281`) is `((Wℓη)²)⁻¹ exp(-√(d/ℓ)_+) + W^{-D}`; `ellHat`
  (`RBM.ellHat`, `Propagator/Decay.lean:480`) is `min(1/√|1-ξ|, L)`, with
  `ellHat_ofReal L (ht1 : t<1) : ellHat L (t:ℂ) = min(1/√(1-t), L)`
  (`Propagator/Decay.lean:482`) and `Step3.ellHat_mono` (`Flow/FlowFamiliesCore.lean:29`) giving
  monotonicity in real time. In this ticket `ℓ_u`/`η_u` are exactly `ellHat L (u:ℂ)` and
  `(1-u)*m`, matching `norm_Uker_le_of_tail`'s own notation; there is no separate `etaT`/Sample
  wrapper to reconcile (the Sample-level `etaT (E,t) = (1-t)(mE E).im`, `Loop/Ward.lean:48`, is
  not used at this deterministic layer).

**T1 (`weighted_duhamel_sum_le`).** Statement vs paper: matches the ticket's transcription of
(5.39)–(5.41) verbatim (hypothesis, conclusion, route). Hypotheses: `3 ≤ L`, `0<m≤1`, grid
`u:ℕ→ℝ` with `u 0 ≥ 0` and `u` non-decreasing step-by-step, `u k < 1`, `exp 1 ≤ W`, `Δ ≥ 0`,
`M_j ≥ 0`, `hA` (label-weighted bound on `A_j` against the `T_{u_j}` profile, for `j<k`), `hAuv`
(the side condition of `norm_Uker_le_of_tail`, at the pair `(u_{j+1}, u_k)`, for `j<k`).
Quantifier order: all deterministic parameters first, then the finite grid data, matching the
ticket (no `∀ᶠ N` here — the target is deterministic, not asymptotic). Dependencies: only
`norm_Uker_le_of_tail` (committed) and the two structural, unconditional facts
`Step3.ellHat_mono` and `ellHat_mul_one_sub_antitone` (proved in this file, not a hypothesis).
Boundary cases: `k = 0` gives an empty sum on both sides (`0 ≤ 0 · tailT(...)`), not vacuous in a
bad sense — the statement is true and non-trivial for `k=0` trivially and for `k≥1` genuinely
(see Witness below). Simultaneous satisfiability: **the potentially dangerous hypothesis is
`hAuv`.** Preflight check: is `hAuv` ever unsatisfiable together with `hA`, or satisfiable only
degenerately? Answer: **no** — `hAuv` at the pair `(u_{j+1}, u_k)` is a *consequence* of
`u_{j+1} ≤ u_k` (which itself follows from `u` being monotone step-by-step, an already-assumed
hypothesis) together with the purely structural fact that `x ↦ ℓ̂(x)·(1-x)` is non-increasing on
`[0,1)` (proved below as `ellHat_mul_one_sub_antitone`, from the identity
`ℓ̂(x)(1-x) = min(√(1-x), L(1-x))`, itself a `min` of two manifestly non-increasing functions of
`x`). So `hAuv` is *never* an extra restriction beyond monotonicity of the grid, and `hA` can
always be met with equality by a genuine non-zero `A_j` (e.g. `A_j b := tailT(...)`, since
`tailT` is always strictly positive, `tailT_pos`). A compiled witness for a one-step, non-zero
instance is included in the file (`section Witness`). **Verdict: PASS.**

**T2 (`weighted_duhamel_sum_stopped`).** Same statement with `k` replaced by `min k (τ ω)` per
`ω : Ω'` (`τ : Ω' → ℕ` an arbitrary function, not assumed measurable/a stopping time — this is a
*pointwise* deterministic corollary, exactly as the ticket specifies: "the same with `k`
replaced by `min k (τ ω)` per `ω`"), with the hypotheses on `A`/`M` required only for `j < τ ω`.
This is immediate from (T1) applied at `k' := min k (τ ω)`, because `j < k' ⟹ j < τ ω` (as
`k' ≤ τ ω`), so the (T1)-hypotheses at `k'` are implied by the (T2)-hypotheses (restricted to
`j < τ ω`). No new mathematical content, no new satisfiability risk beyond (T1)'s.
**Verdict: PASS.**

**Route confirmation.** As directed: apply `norm_Uker_le_of_tail` termwise (`u := u_{j+1}`,
`v := u_k`), after bridging each `A_j`'s bound at profile `u_j` up to profile `u_{j+1}` via
`tailT_mono_time` (T1508 (T1), reproved locally because T1508 was not yet merged; cited as
such), then sum with the triangle inequality (`Δ ≥ 0`) and factor the common `T_{u_k}` profile
out of the finite sum. The conclusion keeps the `T_{u_k}(dist a)` *profile*
(`tailT W (ellHat L (u k:ℂ)) ((1-u k)*m) D (zdist L (a 0 - a 1))`), not a sup-norm — the
T1504 (T3) sup-norm route is not used anywhere in this file.

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridDriftSum.lean` (only writable file touched).

* `RBM.Gauss.Grid.tailT_mono_time` — bridging lemma (T1508 (T1), reproved locally).
* `RBM.Gauss.Grid.weighted_duhamel_sum_le` — (T1).
* `RBM.Gauss.Grid.weighted_duhamel_sum_stopped` — (T2).
* private helper `RBM.Gauss.Grid.ellHat_mul_one_sub_antitone` (structural monotonicity used by
  `tailT_mono_time`).
* `section Witness`: a compiled, non-degenerate (non-zero `A`) instance of (T1)'s hypotheses.

Build:
```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1510 && lake build RBM1D.Gauss.GridDriftSum
```
Result: `Build completed successfully (3749 jobs)`, 0 errors.

Axioms (`lake env lean` on a scratch file `import RBM1D.Gauss.GridDriftSum` +
`#print axioms ...`, then removed):
```
'RBM.Gauss.Grid.tailT_mono_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.weighted_duhamel_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.weighted_duhamel_sum_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`, `admit`, or declared `axiom` in the file (checked by grep).

## (c) Key lemmas used

* `RBM.Step2.norm_Uker_le_of_tail` (committed; the label-weighted kernel estimate).
* `RBM.Step3.ellHat_mono` (`ℓ̂` non-decreasing in time).
* `RBM.ellHat_ofReal`, `RBM.one_le_ellHat_of_nonneg`, `RBM.tailT_nonneg`, `RBM.tailT_pos`.
* `min_mul_of_nonneg`, `one_div_le_one_div_of_le`, `div_le_div_of_nonneg_left`,
  `Real.sqrt_le_sqrt`, `Real.div_sqrt`, `Complex.real_smul` (Mathlib).

## (d) Open issues

* T1508 was still unmerged (`state: proving`) at the time of this ticket; once it merges, the
  hub may replace the locally-reproved `tailT_mono_time` here with an import of T1508's, or
  leave both (they are the same statement up to the exact hypothesis list — T1508's may drop the
  explicit `W>0`/`d≥0` in favour of different side hypotheses; the auditor should check they
  agree before any such consolidation, but this is not required for T1510's own acceptance).
* The stopped version (T2) is intentionally pointwise per `ω` (no measurability / stopping-time
  structure), exactly matching the ticket's request; the probabilistic assembly (measurability
  of `τ`, `{j<τ}∈ℱ_j`, etc.) is out of scope here and belongs to the downstream assembly ticket
  that consumes (T2).
