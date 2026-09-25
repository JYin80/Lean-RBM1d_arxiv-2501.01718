Prover model: claude-opus-5-5[1m]

# T1504 prove report (repairer, after audit RETURN; spec = T1504-amend-1)

Tickets: `docs/tickets/T1504.md` + `docs/tickets/T1504-amend-1.md` (the amend supersedes target
(T1); (T2), (T3) keep their content, (T3) with the guarded hypothesis). Returning audit:
`docs/reports/T1504-audit.md` (RETURN; defects 1-3 below). Sole writable file:
`RBM1D/Gauss/GridDuhamelTail.lean` (worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1504`, branch
`t/T1504`). The prior prover's work (commit `d1c2e95`, model claude-sonnet-5) is kept and extended.

## (a) Math preflight (written before any new Lean)

### Audit defects to address

1. No compiled nonzero Gaussian witness for the Azuma family and (T2); the (T2) `Y = 0` witness
   covered only the real mean and the real `MemLp`. Plan: a trivial-filtration Gaussian model
   `Ω' = ℝ`, `μ = gaussianReal 0 1`, `ℱ 0 = ⊥`, `ℱ (i+1) = borel ℝ`, `n = 0` (so `LoopArg L 0` is a
   singleton and `Uker` is the identity), `τ ≡ 1`, `Z 1 ω = const ω`, `c ≡ 1`, `e ≡ 1`. The conditional
   sub-Gaussian property given `⊥` is proved from `condExp_bot` + `condExp_ae_eq_trim_integral_condExpKernel`
   + `mgf_id_gaussianReal`. Each witness applies the target theorem and yields a genuine Gaussian
   tail bound (`γ{x ≤ |ω|} ≤ 4 e^{-x²/4}`, resp. `≤ 1/x²`). The `Y = 0` witness is extended to all
   five (T2) hypotheses.
2. Private `stoppedEdge` in public signatures. Plan: every public signature states the indicator
   expression `{ω' | j < τ ω'}.indicator (fun ω' => Uker L ξ (u (j+1)) (target) (Z (j+1) ω') b) ω`
   inline; `stoppedEdge` is made public anyway with a `stoppedEdge_apply` unfolding lemma.
3. The (T3) `hFwd` witness was only `ξ = 0`. Plan: a public lemma deriving the guarded `hFwd` from
   the guarded `hR` for arbitrary `ξ` with `‖ξ i‖ ≤ 1` and `0 ≤ u 0 ≤ … ≤ u K = t ≤ 1/2`, via
   `norm_Uker_apply_le` with `C = 2`; plus the corollary (T3) without `hFwd` in that regime.

### (T1′) `stopped_duhamel_azuma_tail_fixed`: PASS

Statement (amend-1): fixed `k`, label `a`, deterministic `c : ℕ → LoopArg L n → ℕ → ℝ≥0`; for every
`j < k`, re/im of `W_j := {j<τ}.indicator ((U (j+1) k) Z_{j+1}) a` (with `U j k = Uker L ξ (u j) (u k)`)
are `HasCondSubgaussianMGF (ℱ j) … (c k a j)`; then for `x ≥ 0`,
`μ.real {x ≤ ‖(Σ_{j<min k τ} U (j+1) k Z_{j+1}) a‖} ≤ 4 exp(-x²/(4 Σ_{j<k} c k a j))`.

- Proof: `sum_stopped` (GridStop) gives `(Σ_{j<min k τ ω} U(j+1)k Z_{j+1} ω) a = Σ_{j<k} W_j ω`
  exactly; `W_j` is `ℱ (j+1)`-strongly measurable (from `{j<τ} ∈ ℱ j ⊆ ℱ (j+1)`, `Z (j+1)` adapted,
  `A ↦ Uker … A a` continuous linear); prepend a zero term (param 0, unconditional) to fit
  `azuma_complex` (T1484) whose index 0 is unconditional; apply it with `n = k+1`. No `U⁻¹`, no
  label union, no factorisation.
- Hypotheses needed: only `hτmeas` (stopping-time events `{j < τ} ∈ ℱ j`), `hZ` (adaptedness),
  `hsubG`, `x ≥ 0`, `[StandardBorelSpace Ω']` (inherited from `azuma_complex`). The amend's
  setting `k ≤ K`, `‖ξ i‖ ≤ 1`, monotone `u` with `u K = t < 1` is not needed for this statement:
  `Uker` is a total function of its complex times. Dropping unused setting hypotheses
  generalises; nothing is weakened. `x ≥ 0` is necessary (for `x < 0` the LHS is 1 while the RHS
  tends to 0 when `Σc > 0`).
- Quantifier order: all fixed parameters (`k, a, c, x`) are universally quantified before the
  measure statement; `c` does not depend on `ω`.
- Boundary cases: `k = 0` (empty sum; RHS is `4 exp(-x²/0) = 4` under Lean's `a/0 = 0`, true);
  `Σc = 0` (hypotheses force `W_j = 0` a.s.; RHS = 4, true); `x = 0` (RHS ≥ 1 unless Σc = 0 where it
  is 4; true).
- Satisfiability: nonzero Gaussian witness above (`k = 1`, one label, `c = 1`); in the paper's
  application the constants are the frozen-linear-functional variances of T1482's
  `hasCondSubgaussianMGF_linear` (indicator-truncated, deterministic `c`), which have exactly
  this shape per target `(k,a)`.
- Dependencies: `azuma_complex` (T1484), `sum_stopped` (GridStop), `Uker_apply` (Kernel). All
  accepted.

### (T1″) `stopped_duhamel_azuma_union`: PASS for the non-vacuous form; the literal form is vacuous

Literal amend statement: `hsubG` for all `k ≤ K`, all `a`, all `j < k`; thresholds `x k a`;
`μ.real {∃ k ≤ K, ∃ a, x k a ≤ ‖(Σ_{j<min k τ} U(j+1)k Z_{j+1}) a‖}
 ≤ Σ_{k ≤ K} Σ_a 4 exp(-(x k a)²/(4 Σ_{j<k} c k a j))`.

**Boundary-case defect in the literal form.** The index `k = 0` is always in `k ≤ K`. For it the
inner sum `Σ_{j<0} c 0 a j` is `0`, and under Lean's `a / 0 = 0` its summand is
`4 exp(-(x 0 a)²/0) = 4 exp 0 = 4`. So the literal right-hand side is always at least `4`, while
the left-hand side is a probability (at most 1). Read literally in Lean, the statement is
**trivially true for every input**, i.e. vacuous. In the paper's convention the `k = 0` summand is
`4 exp(-∞) = 0` for `x 0 a > 0`, and the `k = 0` event `{x 0 a ≤ ‖0‖}` is empty.
Compiled negative check: an `example` in the file shows that the literal RHS is `≥ 1` for all
data.

**Form proved under the ticket's name (non-vacuous, no weakening).** Keep the event exactly as in
the amend (`∃ k ≤ K, ∃ a, …`). The RHS drops only the `k = 0` summand:
`Σ_{k ∈ Finset.Icc 1 K} Σ_a 4 exp(-(x k a)²/(4 Σ_{j<k} c k a j))`. Hypotheses:
`hx : ∀ k ≤ K, ∀ a, 0 ≤ x k a` and `hx0 : ∀ a, 0 < x 0 a`. The second is exactly what makes the
paper's `k = 0` summand zero, and it is needed: with `x 0 a = 0` the event is everything, and the
Icc-sum can be below 1. The new RHS is `≤` the literal one, so this form implies the literal
statement. Downstream thresholds are positive (`N^ε`-scale), so `hx0` costs nothing there.
- Proof: the `k = 0` part of the event is empty (`‖0‖ = 0 < x 0 a`). The rest is
  `⋃_{k ∈ Icc 1 K} ⋃_a E_{k,a}`. Apply the finite union bound (`measureReal_biUnion_finset_le`,
  `measureReal_iUnion_fintype_le`), then (T1′) for each `(k,a)`.
- Boundary: for `K = 0` the event is empty and the RHS is the empty sum `0`, so the statement
  holds. The Icc-form theorem stays non-vacuous (the nonzero Gaussian witness gives
  `≤ 4 e^{-x²/4}` for `K = 1`).
- On `{τ = k}` the `k`-term is the linear Duhamel term at `u_τ` (`min k τ = τ`). That is the use
  the amend intends; the Lean statement makes no further claim.
- The dispatcher should confirm this reading of "Σ_{k ≤ K}" (flagged under open issues).

### (T2) `stopped_duhamel_cheb_tail`: PASS (content unchanged)

Only change: the five hypotheses state the indicator expression inline (defect 2). `0 < x` kept
(necessary: at `x = 0` the RHS is 0 in Lean, LHS is 1). New witnesses: `Y = 0` with all five
hypotheses; nonzero Gaussian (`e ≡ 1`; conditional mean `E[ω | ⊥] = ∫ ω dγ = 0`, `MemLp 2` from
`memLp_id_gaussianReal`, `∫ ω² dγ = 1` from `variance_id_gaussianReal`).

### (T3) `stopped_duhamel_det_bound`: PASS (content unchanged, stopped form, guarded hypothesis)

Amend requires `hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j`, so (T3) is stated on the stopped sum
with `R : ℕ → Ω' → V`, `τ ≤ K`: for all `ω a`,
`‖(Σ_{j<τ ω} U(j+1)(τ ω) (R j ω)) a‖ ≤ 2^n (2^n Σ_{j<K} r j)` (deterministic RHS, full horizon).
The forward-kernel hypothesis `hFwd` is guarded identically:
`∀ j ω, j < τ ω → ∀ a, ‖Uker L ξ (u (j+1)) t (R j ω) a‖ ≤ 2^n r j` (only indices `j < τ ω` enter
the sum, so an unguarded `hFwd` would constrain irrelevant `R j ω`).
- Proof: back factorisation `U(j+1)(τω) = Uker t (u (τω)) ∘ Uker (u(j+1)) t` (`Uker_comp`, times in
  `[0,t]`, `t < 1`, `‖ξ‖ ≤ 1`); inner sum `≤ Σ_{j<τω} 2^n r j ≤ 2^n Σ_{j<K} r j` (`r ≥ 0`, `τ ≤ K`);
  outer factor `2^n` from `norm_Uker_back_le` (T1500).
- `hR` is not used by the core proof (as in the audited version): `hFwd` carries the forward
  bound. Reason (Step 0, unchanged): the forward row bound `1 + (t-s)‖ξ‖/(1-t‖ξ‖)` is unbounded as
  `t‖ξ‖ → 1⁻`, so `hR` cannot imply `hFwd` for general `t < 1`. (T3) is a conditional adapter in
  that sense; the docstring says so, and that (T3) is for the O(Δ^{3/2}) errors only, not for the
  drift.
- Nondegenerate witness (defect 3): for `t ≤ 1/2`, any `ξ` with `‖ξ i‖ ≤ 1`, `0 ≤ s = u(j+1) ≤ t`:
  `‖tξ_i‖ ≤ t < 1` and `1 + ‖(s-t)ξ_i‖(1-‖tξ_i‖)⁻¹ ≤ 1 + (t-s)/(1-t) ≤ 1 + (1/2)/(1/2) = 2`, so
  `norm_Uker_apply_le` with `C = 2`, `M = r j` gives `hFwd` from `hR`. Compiled as a public lemma
  plus the corollary `stopped_duhamel_det_bound_half` (no `hFwd`).
- Boundary: `τ ω = 0` (empty sum; RHS ≥ 0 since `r ≥ 0`); `K = 0`.

### (T1) `stopped_duhamel_azuma_tail` (original, kept): unchanged proof

Kept under its name, docstring marked "sup-norm; does not suffice for (2.76), see supervisor
2026-09-25-2045 §1"; no new code consumes it. Signature changed only by inlining the indicator
(defect 2). Nonzero Gaussian witness added.

### Paper-delta note (no entry written; the dispatcher decides)

Lean-level precisions, no change to a paper statement: (T2) requires `x > 0`; (T3) takes the
forward-kernel bound as a guarded hypothesis `hFwd` (discharged from `hR` for `t ≤ 1/2`);
(T1′)/(T1″) drop setting hypotheses that are not needed.

## (b) Declarations, file, build, axioms

File: `RBM1D/Gauss/GridDuhamelTail.lean` (worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1504`,
branch `t/T1504`, commit `b1d4b49` on top of `d1c2e95`). No other file was touched.

Public declarations (namespace `RBM.Gauss.Grid`):
- `stopped_duhamel_azuma_tail_fixed` (T1′). Hypotheses: `hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}`,
  `hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i)`, fixed `k`, `a`, deterministic
  `c : ℕ → LoopArg L n → ℕ → ℝ≥0`, and for `j < k` the re/im of
  `{ω' | j < τ ω'}.indicator (fun ω' => Uker L ξ (u (j+1)) (u k) (Z (j+1) ω') a) ω` are
  `HasCondSubgaussianMGF (ℱ j) (ℱ.le j) · (c k a j) μ`; `0 ≤ x`. Conclusion:
  `μ.real {ω | x ≤ ‖(∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j+1)) (u k) (Z (j+1) ω)) a‖} ≤ 4 * exp (-x^2 / (4 * ∑ j ∈ range k, c k a j))`.
  No `U⁻¹`, no factorisation, no label union.
- `stopped_duhamel_azuma_union` (T1″). The same `hτmeas`, `hZ`; `hsubG` for all `k ≤ K`, all `a`, all `j < k`;
  `hx : ∀ k ≤ K, ∀ a, 0 ≤ x k a`; `hx0 : ∀ a, 0 < x 0 a`. Conclusion:
  `μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ range (min k (τ ω)), U (j+1) k (Z (j+1) ω)) a‖} ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a, 4 * exp (-(x k a)^2 / (4 * ∑ j ∈ range k, c k a j))`.
  This deviates from the literal amend statement (see (a) and (d)).
- `stopped_duhamel_cheb_tail` (T2). Content is unchanged. The five hypotheses now state the indicator inline.
- `stopped_duhamel_det_bound` (T3), in stopped form:
  - `τ ≤ K` and `R : ℕ → Ω' → V`;
  - `hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j`;
  - `hFwd : ∀ j ω, j < τ ω → ∀ a, ‖Uker L ξ (u (j+1)) t (R j ω) a‖ ≤ 2^n * r j`;
  - conclusion, for all `ω a`: `‖(∑ j ∈ range (τ ω), Uker L ξ (u (j+1)) (u (τ ω)) (R j ω)) a‖ ≤ 2^n * (2^n * ∑ j ∈ range K, r j)`.

  The docstring says it is for the O(Δ^{3/2}) errors only, not for the drift. The proof does not use `hR`, so the linter reports it as unused. This is documented: `hFwd` carries the forward bound.
- `norm_Uker_fwd_le_of_le_half`: for `0 ≤ s ≤ t ≤ 1/2`, `‖ξ i‖ ≤ 1` and `‖A ·‖ ≤ M`, we get `‖Uker L ξ s t A a‖ ≤ 2^n M`.
- `hFwd_of_le_half`: the guarded `hR` implies the guarded `hFwd` when `u K = t ≤ 1/2`, for any `ξ` with `‖ξ i‖ ≤ 1`.
- `stopped_duhamel_det_bound_half`: (T3) for `t ≤ 1/2` without `hFwd`.
- `stopped_duhamel_azuma_tail`: the original (T1). Its docstring is marked "Sup-norm; does not suffice for (2.76), see
  supervisor 2026-09-25-2045 §1. No consumer may use it." Its hypothesis now states the indicator inline, and its proof is re-routed through the shared private helper `azuma_stoppedEdge`.
- `stoppedEdge` (now public) and `stoppedEdge_apply` (`rfl` unfolding lemma).

Witness `example`s (section `Witness`, all compiled):
- `Z = 0` for the (T1′)/(T1″)/(T1) hypothesis shape, with `c = 0` and arbitrary `Ω', μ, ℱ, L, n, ξ, u, τ, k, a`.
- `Y = 0` for all five (T2) hypotheses (`e ≡ 0`).
- Nonzero Gaussian model: `Ω' = ℝ`, `μ = gaussianReal 0 1`, `ℱ 0 = ⊥`, `ℱ (i+1) = borel`, `L = 3`, `n = 0`,
  `τ ≡ 1`, `Z (i+1) ω = ω`. Each example applies the target theorem and discharges every hypothesis:
  - (T1′) gives `γ{x ≤ |ω|} ≤ 4 e^{-x²/4}`;
  - (T1″) with `K = 1` gives the same;
  - the original (T1) gives the same;
  - (T2) with `e ≡ 1` gives `γ{x ≤ |ω|} ≤ 1/x²`. All five hypotheses are discharged: the conditional mean via `condExp_bot`
    and `integral_id_gaussianReal`, `MemLp 2` via `memLp_id_gaussianReal'`, and `∫ω² = 1` via
    `variance_id_gaussianReal`.

  The conditional sub-Gaussian property given `⊥` is proved (private `hasCondSubgaussianMGF_bot`) from
  `Kernel.HasSubgaussianMGF.of_rat`, `condExp_ae_eq_trim_integral_condExpKernel` and `condExp_bot`.
- (T3) `hFwd`, nondegenerate: `n = 1`, `ξ = 1`, `u j = min j 2 / 4` (`u 1 = 1/4 < t = 1/2`), `K = 2`, `τ ≡ 2`,
  `R ≡ 1`, `r ≡ 1`.
- Vacuity of the literal (T1″): for every probability measure, every set `S` and all data,
  `μ.real S ≤ ∑_{k ∈ range (K+1)} ∑_a 4 exp(-(x k a)²/(4 Σ_{j<k} c k a j))`.

Build commands and results:
- `cd /Users/junyin/Lean_proof/RBM1D-wt/T1504 && lake build RBM1D.Gauss.GridDuhamelTail`: Build completed
  successfully (3711 jobs). The only warning in this file is the unused `hR` in (T3).
- `lake build RBM1D`: Build completed successfully (9649 jobs). The module is not yet imported by the root; the import is added at merge.
- `lake env lean` on a scratch file with `import RBM1D` + `import RBM1D.Gauss.GridDuhamelTail`: no errors, so there are no
  name clashes with the root. The private helper was renamed `card_loopArg_eq` to avoid confusion with `RBM.card_loopArg`.

`#print axioms` (in the file) gives `[propext, Classical.choice, Quot.sound]` for each of:
`stoppedEdge_apply`, `stopped_duhamel_azuma_tail_fixed`, `stopped_duhamel_azuma_union`,
`stopped_duhamel_azuma_tail`, `stopped_duhamel_cheb_tail`, `stopped_duhamel_det_bound`,
`norm_Uker_fwd_le_of_le_half`, `hFwd_of_le_half`, `stopped_duhamel_det_bound_half`.
There is no `sorry`, `admit` or `axiom` in the file.

## (c) Key lemmas used

- `azuma_complex`, `martingale_sq_eq_sum` (T1484, GridAzuma).
- `sum_stopped` (GridStop).
- `norm_Uker_back_le` (T1500).
- `norm_Uker_apply_le`, `Uker_comp`, `Uker_apply` (Hierarchy/Kernel).
- `UkerHom_apply` (T1485).
- Mathlib: `measureReal_biUnion_finset_le`, `measureReal_iUnion_fintype_le`,
  `martingale_of_condExp_sub_eq_zero_nat`, `mul_meas_ge_le_integral_of_nonneg`, `Kernel.HasSubgaussianMGF.of_rat`,
  `condExp_bot`, `condExp_ae_eq_trim_integral_condExpKernel`, `condExpKernel_comp_trim`, `mgf_id_gaussianReal`,
  `integrable_exp_mul_gaussianReal`, `integral_id_gaussianReal`, `variance_id_gaussianReal`, `variance_eq_integral`,
  `memLp_id_gaussianReal'`.

## (d) Open issues

1. **(T1″) literal form is vacuous in Lean; a non-vacuous form was proved under the ticket's name.** The
   amend's `Σ_{k ≤ K}` includes `k = 0`. There the constant sum is empty, and `a / 0 = 0` makes that summand `4`, so
   the literal RHS is always at least 4. A compiled `example` shows this. The proved statement keeps the amend's event
   (`∃ k ≤ K`), sums the RHS over `Icc 1 K`, and adds `hx0 : ∀ a, 0 < x 0 a`. That hypothesis is exactly the paper's
   condition for the `k = 0` summand to be `0`, and it is necessary for the Icc form. The new statement implies the
   literal one. The dispatcher should confirm this reading, and decide whether it needs a `docs/paper-deltas.md` entry (none was written).
2. **(T3) is a conditional adapter.** `hR` is unused by the core proof. For general `t < 1`, `hFwd` does not follow
   from `hR`: the forward row bound blows up as `t‖ξ‖ → 1⁻`. It does follow for `t ≤ 1/2`
   (`hFwd_of_le_half`, `stopped_duhamel_det_bound_half`). Downstream uses with `t > 1/2` must discharge `hFwd` from the
   specific remainder. (T3) is stated with `R` depending on `ω` and the guard `j < τ ω`, as amend-1 requires; the
   earlier fixed-`k`, deterministic-`R` form was replaced.
3. (T1′)/(T1″) take no `k ≤ K`, `‖ξ‖ ≤ 1`, or monotone-`u` hypotheses. The statement is purely probabilistic and does not need them. This is a
   generalisation, not a weakening.
4. Lean-level precisions for possible paper-delta entries (the dispatcher decides): (T2) needs `x > 0`; (T3) takes the
   guarded forward-kernel hypothesis; (T1″) sums over `Icc 1 K` and needs `x 0 a > 0`.
5. The original (T1) is kept only as history. No declaration in this file consumes it; only its witness `example`
   references it.

Verdict: (T1′) PASS, (T1″) PASS in the non-vacuous form (literal form flagged as vacuous, open issue 1), (T2) PASS,
(T3) PASS (guarded; conditional on `hFwd` for `t > 1/2`). Audit defects 1–3 addressed.
