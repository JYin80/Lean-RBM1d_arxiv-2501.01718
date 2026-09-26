Prover model: claude-sonnet-5

# T1509 — prove report

## (a) Math preflight (before any Lean)

**Target (T1) `RBM.Gauss.Grid.Uker_one_nonneg`.**
Claim: for `0 ≤ u ≤ v < 1`, every kernel entry `∏_{i:Fin 2} edgeKer L 1 u v (a i) (b i)` of
`Uker L (fun _ => 1) u v` is a nonnegative real (embedded in `ℂ`).

- Route (already-accepted dependencies only): `edgeKer_eq` (`Hierarchy/Kernel.lean:107`,
  committed) gives, for `ξ = 1`, `s = u`, `t = v`,
  `edgeKer L 1 u v = 1 - (u - v) • (SB L * Theta L v) = 1 + (v - u) • (SB L * Theta L v)`.
  Since `u ≤ v`, `v - u ≥ 0`. `SB L` has entries `0` or `1/3` (`sbKernel`, `Defs/Block.lean`,
  committed) — real and `≥ 0`. `Theta L (v:ℂ) = ∑' k, ((v:ℂ) • SB L)^k` for real `v ∈ [0,1)`
  (`Theta_eq_tsum`, `Propagator/Basic.lean:201`, committed): a termwise-nonnegative-real
  series (each `(v•SB)^k` entry is a finite sum of products of nonnegative reals, `v ≥ 0`),
  hence its entrywise sum is a nonnegative real (using that entry-evaluation commutes with
  the matrix `tsum` via `Pi.tsum_apply`, and `Complex.ofReal_tsum` to pull the cast out).
  `SB * Theta` is then entrywise nonnegative-real (finite sum of products), and so is
  `1 + (v-u) • (SB*Theta v)` (identity matrix entries are `0` or `1`, plus a nonnegative-real
  scalar times a nonnegative-real matrix). The `n = 2` product over `Fin 2` of two
  nonnegative reals is a nonnegative real.
- Hypotheses (`0 ≤ u`, `u ≤ v`, `v < 1`) are exactly the paper's window and are jointly
  satisfiable non-vacuously, e.g. `u = 0, v = 1/2`.
- No new hypothesis, no loss factor, no widened indicator: this is an exact identity, not an
  inequality with slack. **PASS.**

**Target (T2) `RBM.Gauss.Grid.qv_conv_le`.**
Claim (paraphrased from the ticket): under the hypotheses of `norm_Uker_le_of_tail`
(`Hierarchy/Step2.lean:448`, committed: `hL`, `hm0`, `hm1`, `hu0`, `huv`, `hv0`, `hv1`, `hW`,
`hAuv`), plus `Q ≥ 0`, `R : LoopArg L 2 → ℝ` with `0 ≤ R a` and
`R a ≤ Q · (tailT W ℓ_u η_u D (dist a))²` for all `a`, and `EE : LoopArg L 2 → LoopArg L 2 → ℂ`
with `‖EE a a'‖ ≤ √(R a) · √(R a')` (the M7a shape delivered by
`norm_EEpath_offDiag_sq_le`, `Gauss/EEOffDiag.lean:146`, after `Real.sqrt`), the quadratic form
`‖∑_{a,a'} K(b,a)·conj K(b,a')·EE a a'‖ ≤ (√Q · r² · xiK L W m · tailT W ℓ_v η_v D (dist b))²`,
`r = (1-u)/(1-v)`.

- Order of quantifiers: `L, m, u, v, W, D, Q, R, EE` are all fixed parameters before the
  (single, fixed) conclusion at a fixed `b`; no `∀ᶠ N` appears anywhere in this purely
  algebraic/deterministic lemma (there is no `N` in scope) — nothing is dropped or reordered
  relative to the ticket.
- Route: triangle inequality (`‖∑∑ K(b,a) conj(K(b,a')) EE(a,a')‖ ≤ ∑∑ ‖K(b,a)‖‖K(b,a')‖‖EE(a,a')‖`),
  then `hEE` termwise, then factor the double sum as `(∑_a ‖K(b,a)‖√(R a))²`
  (`Fintype.sum_mul_sum`). Using (T1) (`K(b,a)` is a nonnegative real) and `√(R a) ≥ 0`,
  `∑_a ‖K(b,a)‖√(R a) = ‖Uker L (fun _=>1) u v (fun a => (√(R a):ℂ)) b‖` exactly (each summand
  of the defining sum of `Uker … b` is itself a nonnegative real equal to its own norm).
  Then `norm_Uker_le_of_tail` bounds this norm by `√Q · r² · xiK L W m · tailT_v(dist b)`,
  using `‖(√(R a):ℂ)‖ = √(R a) ≤ √Q · tailT_u(dist a)` (from `R a ≤ Q·tailT_u(dist a)²`,
  `Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `Real.sqrt_sq`, `tailT_nonneg`). Finally
  `pow_le_pow_left₀` squares the inequality (both sides nonnegative).
- Dependencies used: `norm_Uker_le_of_tail` (committed, Step2.lean:448) and the M7a shape
  (T1494, merged) via its abstracted hypothesis `hEE`; **no** M7b input; matches the ticket's
  requirement.
- No loss factor beyond what `norm_Uker_le_of_tail` itself already carries (`xiK`, which is
  the accepted `W^{o(1)}` factor of the *dependency*, not something (T2) adds): the (T2) proof
  adds no `e^λ`, no widened indicator (`1(dist ≤ …)`) anywhere; it is pure triangle inequality
  + Cauchy–Schwarz-shape hypothesis + the already-accepted kernel bound.
- Satisfiability (non-vacuous, no astronomically large witness needed): `L = 3`, `m = 1/2`,
  `u = 0`, `v = 1/2`, `W = e`, `D = 1`, `Q = 0`, `R ≡ 0`, `EE ≡ 0` satisfies every hypothesis
  (`hAuv` becomes `e·ℓ̂(v)·(1-v)m ≤ e·ℓ̂(u)·(1-u)m`, checked by `ellHat` monotonicity in the
  proof of `norm_Uker_le_of_tail` itself — reusing an already-accepted witness shape from that
  theorem's own use sites) — and none of `L, W, u, v` need to be taken absurdly large; `Q`
  need not be positive for the statement to be meaningful (a positive-`Q`, nonzero-`EE`
  instance is equally satisfiable by taking `R a := Q · tailT_u(dist a)²` with equality and
  `EE ≡ 0`).
- **PASS.**

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridQVConv.lean` (sole writable file), namespace `RBM.Gauss.Grid`.

Public declarations (exactly the two ticket names):
* `RBM.Gauss.Grid.Uker_one_nonneg`
* `RBM.Gauss.Grid.qv_conv_le`

Private helper declarations (same file, not exported): `IsRealNonneg` and its algebra
(`ofNonneg`, `add`, `mul`, `sum`, `prod`, `tsum`, `norm_eq`, `eq_ofReal_re`, `re_nonneg`),
`SB_isRealNonneg`, `SBpow_isRealNonneg`, `theta_entries_summable`, `theta_apply_eq_tsum`,
`Theta_real_isRealNonneg`, `SB_mul_Theta_real_isRealNonneg`, `edgeKer_one_isRealNonneg`,
`sum_edgeProd_mul_ofReal_norm_eq`.

Build:
```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1509 && lake build RBM1D.Gauss.GridQVConv
```
Result: **0 errors** (see below for the exact log excerpt).

Axioms (`#print axioms RBM.Gauss.Grid.Uker_one_nonneg` and
`#print axioms RBM.Gauss.Grid.qv_conv_le`): only `propext`, `Classical.choice`, `Quot.sound`.

## (c) Key lemmas used

* `edgeKer_eq`, `Theta_eq_tsum`, `sbKernel`/`SB_apply`, `norm_entry_le_norm`,
  `summable_norm_pow` (all `Propagator/Basic.lean`, `Propagator/Bounds.lean`, `Defs/Block.lean`,
  committed).
* `norm_Uker_le_of_tail`, `tailT_nonneg`, `Uker_apply` (`Hierarchy/Step2.lean`,
  `Hierarchy/Kernel.lean`, committed).
* `Fintype.sum_mul_sum`, `pow_le_pow_left₀`, `Complex.ofReal_tsum`, `Complex.ofReal_sum`,
  `Complex.norm_of_nonneg`, `Finset.sum_induction`, `Finset.prod_induction` (Mathlib).

## (d) Open issues

* None for the two named targets. The supervisor note `docs/supervisor/2026-09-25-2045.md`
  §3(ii) also lists two further steps ((5.42)'s matrix identity vs `quadVar_qUkerObsT_le_norm_QQ_eeFun'`,
  and the discrete Riemann-sum time integral (iii)) that are out of scope for this ticket
  (not among its two named targets) and are left for the tickets the supervisor recommends.
