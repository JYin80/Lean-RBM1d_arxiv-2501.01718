Prover model: claude-opus-5-5

# T1522 — Lemma 7.3 (7.14)/(7.16), pointwise, packaged as `RBM.Gauss.Q716`

## Step 0 (read-only checks)

* `Uker`, `edgeKer`, `edgeKer_eq`, `Theta`, `xiOf`, `mSigma`, `norm_Uker_apply_le` —
  `RBM1D/Hierarchy/Kernel.lean` (confirmed at the cited lines; `Uker` is (5.17), `xiOf` is
  `ξ_i = m(σ_i)m(σ_{i+1})` with **cyclic** `i + 1 : Fin n`).
* Θ decay/max bounds — `RBM1D/Propagator/Decay.lean` (`norm_theta_apply_le_rho_pow`,
  `theta_apply_closed_form`, `ellHat`, `ellHat_zero`, block form via `Theta`/`SB`).
* `ellHat`, `etaT` — `Propagator/Decay.lean` (`ellHat`), `Loop/Ward.lean` (`etaT E t = (1-t)·Im mE`).
  `SumZero`/`FastDecay` — `Hierarchy/SumZero.lean` (`SumZero`), `Hierarchy/KernelDecay.lean`
  (`FastDecay`, `SumZeroAt`); witnesses `sumZero_witTensor`, `fastDecay_witTensor` —
  `Gauss/Lemma514Q716.lean:605,624`.

## §10b reuse check

Tracing "the pointwise kernel lemmas underneath `momNorm_Uker_sumZero_scale_le`"
(`Gauss/Lemma514Q716.lean:346`) leads to `SumZeroDyn.norm_Uker_sumZero_scale_le`/`_le'`
(`Hierarchy/SumZeroDyn.lean:1258,1302`), whose proof is exactly
`RBM.norm_Uker_fastDecay_le_sumZero` (`Hierarchy/KernelDecay.lean:1489`), and its `_sigma`
specialisation `norm_Uker_fastDecay_le_sumZero_sigma` (line 1615) for the paper's charge
`ξ = xiOf (mSigma E) σ`. Symmetrically, the Case‑1 lemmas underneath
`Lemma514NonAlt.momNorm_Uker_short_*` trace back to `norm_Uker_fastDecay_le_short`
(line 1350) and its `_sigma` form `norm_Uker_fastDecay_le_of_eq` (line 1599). The general
(7.14) bound is `norm_Uker_fastDecay_le` (line 1304).

**These are already exactly Lemma 7.3, (7.14) and Case 1/Case 2 of (7.16)**, committed to
`main` since **T51+T55** ("Lemmas 7.2/7.3 (evolution kernel on fast-decay tensors)",
commit `7669a0b`), long predating this ticket, and already recorded as an accepted
paper‑delta:

> `docs/paper-deltas.md` **#35** (row "Lemma 7.2、7.3 (7.2)(7.13)–(7.24)"): the paper's
> `W^{C_nτ}`/`W^{-D+C_n}` are replaced in Lean by a free parameter `K ≥ 1` (`= W^τ`) and an
> explicit `δ ≥ 0` (`= W^{-D}`); all constants (`cKer`, `cKerShort`, `cKerSumZero`,
> `cKerSumZeroErr`) are explicit functions of `n` only (`cKerShort` also of a fixed bulk gap
> κ); marked **更强/另证** ("stronger / alternative proof"), i.e. already reviewed and
> accepted.

Their dependency closure is purely deterministic complex/real analysis on `Matrix (ZMod L)
(ZMod L) ℂ` and `LoopArg L n → ℂ` — no `Ω`, no `jStar`, no `h560`, no probability space at
all (`Hierarchy/KernelDecay.lean` imports only `Hierarchy.Kernel`, `Propagator.DiffComplex`,
`Propagator.Edges`, `Analysis.StretchedExp`). **Reuse verdict: safe**, exactly as the ticket's
§10b anticipates.

Consequently `Q716Pointwise.lean` is a **thin repackaging** of these lemmas under the
ticket's requested names, plus two satisfiability witnesses (built from the already‑existing,
already‑audited `Gauss.witTensor` family, `Gauss/Lemma514Q716.lean:547-656`).

## Math preflight

### (T1) `uker_decay_le` — (7.14)

Paper statement (p.79, (7.13)-(7.14)): for `A : Z_L^n → ℂ`, `n ≥ 2`, `(τ,D)`-decaying at `s`
(max pairwise `zdist ≥ ℓ_sW^τ ⇒ |A_a| ≤ W^{-D}`), and `0 ≤ s ≤ t < 1`,
`|(U_{s,t,σ}∘A)_a| ≤ C_nW^{C_nτ}‖A‖_max·(ℓ_t/ℓ_s)·(ℓ_sη_s/ℓ_tη_t)^n + W^{-D+C_n}`.

* Hypotheses vs. formula: matches; quantifier order `∀ n ≥ 2, ∀ s ≤ t, ∀ E, ∀ σ, ∀ A decaying
  ⇒ bound` is preserved (all fixed parameters before the bound).
* Dependencies: `norm_Uker_fastDecay_le` (`KernelDecay.lean:1304`) — already accepted,
  deterministic, `n`-only constant `cKer n`.
* Boundary cases: `s = t` (ratio `= 1`, bound reduces to `‖A‖_max` term only, consistent with
  `Uker_self`); `n` small (`n=1` allowed by the Lean lemma, a strict generalisation of the
  paper's `n≥2`, not a weakening).
* **One genuine paper/Lean difference** (already `docs/paper-deltas.md` #35, not new): the
  literal paper error term `W^{-D+C_n}` has **no** `η_s/η_t` factor, while the Lean bound's
  error term is `((1-s)/(1-t))^n·δ = (η_s/η_t)^n·W^{-D}`. A literal transcription with a pure
  `W^{-D+C_n}` error (independent of `s,t`) is **false** as a pointwise statement for
  arbitrary `s ≤ t < 1`: e.g. the constant tensor `A ≡ δ` is trivially `(ℓ,δ)`-fast-decaying
  and bounded by `M = δ`, and for real `ξᵢ = 1` (`σ` with real `m`-products) the exact value
  `(U∘A)_a = δ·((1-s)/(1-t))^n` is unbounded as `t → 1⁻` with `s, δ, W, D, n` fixed — no
  constant `C_n` depending only on `n` (or `W`) can dominate it. This is the Step‑0 failure
  pattern (`no_const_hkerC_on_gridS`) **applied to the literal paper wording**, not to the
  quantity the route actually needs: the already-accepted Lean form keeps the `η`‑ratio
  explicit (exactly as `ℓ_t/ℓ_s` and `(ℓ_sη_s/ℓ_tη_t)^n` are explicit on the main term), which
  is what downstream tickets (`momNorm_Uker_sumZero_scale_le` et al.) actually consume. I keep
  this accepted form (not the literal transcription) under the requested name; the delta is
  already on record (#35), so no new entry is required.
* Witness: not separately required by the ticket for (T1); the (T2)/(T3) witnesses below also
  instantiate (T1)'s hypotheses non‑vacuously (same tensor, `σ` unconstrained).

**Verdict: PASS** (repackage `norm_Uker_fastDecay_le` under the requested name and the
paper's charge `ξ = xiOf (mSigma E) σ`).

### (T2) `uker_decay_le_nonAlt` — (7.16) Case 1

Paper: `σ_k = σ_{k-1}` for some `k` (equivalently, after re-indexing, `σ_k = σ_{k+1}`,
cyclic) ⇒ the `ℓ_t/ℓ_s` factor disappears. Reason given: `ξ_k = m²`, row sum `O(1)`.

* Cyclic reading: `xiOf`'s `i + 1 : Fin n` wraps automatically (`ZMod`-style `Fin n`
  addition), matching the plan's confirmation (`G1c-plan-paper.md` §3 point 3: "Θ_{t,σ} 的边
  是 m_km_{k+1}，且 m_{n+1}=m_1").
* Dependencies: `norm_Uker_fastDecay_le_of_eq` (`KernelDecay.lean:1599`), which needs a fixed
  bulk gap `κ` with `0 < κ ≤ 1`, `|E| ≤ 2-κ` (the "row sum `O(1)`" claim is uniform in `t`
  only away from the spectral edge; taking `κ := min(2-|E|, 1) > 0` for any `|E| < 2` recovers
  exactly the ticket's `|E| < 2` hypothesis, at the cost of `C_n` depending on this fixed `κ`
  in addition to `n` — allowed: κ is a function of the fixed parameter `E`, not of `N, W, L,
  s, t`).
* Exponent check (Step‑0 failure signal): the bound's exponent is `n` throughout (`K^n`,
  ratio `^n`), **not** `n-1` — failure signal does **not** trigger.
* Witness (`uker_decay_le_nonAlt_satisfiable`): `σ ≡ true` (genuinely non-alternating: `σ_0 =
  σ_1`), `A = Gauss.witTensor L 0 1` (nonzero, `Gauss.witTensor_ne_zero`), bounded by `1`
  (`Gauss.norm_witTensor_le`), `(ellHat·2, 0)`-fast-decaying (`Gauss.fastDecay_witTensor`) —
  all four hold simultaneously and non-vacuously.

**Verdict: PASS.**

### (T3) `uker_decay_le_sumZero` — (7.16) Case 2

Paper: `Σ_{a_2,…,a_n}A_a = 0 ∀a_1` (7.15) ⇒ same improved bound, no alternation hypothesis on
`σ` needed. Matches `SumZeroAt L 0 A` (`0 : Fin n` is the paper's `a_1`, comment at
`KernelDecay.lean:311-314` confirms this convention) exactly.

* Dependencies: `norm_Uker_fastDecay_le_sumZero_sigma` (`KernelDecay.lean:1615`), needs
  `n ≥ 2` (matches paper exactly, no relaxation needed here since the Lean lemma itself
  requires `2 ≤ n`), `0 < |ξᵢ| ≤ 1` (met by `xiOf_mSigma_ne_zero`, `norm_xiOf_mSigma` for
  `|E| ≤ 2`).
* Exponent check: main term exponent `n` (`K^{2n}`, ratio `^n`) — matches paper's (7.16) form
  (only the `K`-power differs from Case 1/T̲1, `K^{2n}` vs `K^n`, both being `W^{C_nτ}` under
  the accepted `K = W^τ` identification, `docs/paper-deltas.md` #35).
  No `n-1` collapse.
* Error term: same accepted-delta discrepancy as (T1) (η‑ratio kept explicit instead of a
  literal `W^{-D+C_n}`), for the same reason (falsifiable otherwise); already covered by
  paper-delta #35.
* Witness (`uker_decay_le_sumZero_satisfiable`): the same `Gauss.witTensor L 0 1` — nonzero,
  bounded, fast-decaying (as above) **and** sum-zero (`Gauss.sumZero_witTensor` +
  `SumZeroDyn.sumZeroAt_zero_of_sumZero`, converting the paper's "sum-zero at every
  coordinate" witness to "sum-zero at coordinate `0`"). Four hypotheses simultaneously
  satisfiable by one concrete nonzero tensor.

**Verdict: PASS.**

### (T4) `uker_preserves_decay` (optional)

Lemma 5.9's remark after (5.75): `A` `(τ,D)`-decaying at `s` ⇒ `U_{s,t,σ}∘A` is
`(2τ, D-C_n)`-decaying at `t`. No existing Lean lemma of this shape was found anywhere in the
worktree (`grep` for `preserves_decay`/`FastDecay.*Uker` turned up only unrelated event-layer
material in `Gauss/FastDecayFlow.lean`). This is genuine new work, not a repackaging, and the
ticket marks it optional ("if time allows"); the release condition for the audit stage only
requires (T1)-(T3) and a successful build. **Not attempted** — left as an open issue below,
not a blocker for this ticket's release.

## Overall verdict

(T1) PASS · (T2) PASS · (T3) PASS · (T4) not attempted (optional, no failure signal
triggered on the mandatory targets).

## Declarations added

File `RBM1D/Gauss/Q716Pointwise.lean` (namespace `RBM.Gauss.Q716`), only writable file:

* `uker_decay_le` — (T1)/(7.14).
* `uker_decay_le_nonAlt` — (T2)/(7.16) Case 1.
* `uker_decay_le_sumZero` — (T3)/(7.16) Case 2.
* `uker_decay_le_nonAlt_satisfiable`, `uker_decay_le_sumZero_satisfiable` — nondegenerate
  satisfiability witnesses (σ ≡ true resp. `Gauss.witTensor L 0 1`).

No `sorry`, `admit`, or declared `axiom`.

## Build

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1522 && lake build RBM1D.Gauss.Q716Pointwise
```
Result: `✔ Built RBM1D.Gauss.Q716Pointwise` (3777/3777 jobs, whole-project build; no
warnings attributed to this file — all warnings printed belong to pre-existing files).

## Axioms

```
#print axioms RBM.Gauss.Q716.uker_decay_le
#print axioms RBM.Gauss.Q716.uker_decay_le_nonAlt
#print axioms RBM.Gauss.Q716.uker_decay_le_sumZero
#print axioms RBM.Gauss.Q716.uker_decay_le_nonAlt_satisfiable
#print axioms RBM.Gauss.Q716.uker_decay_le_sumZero_satisfiable
```
All five: `[propext, Classical.choice, Quot.sound]` only.

## Key lemmas used

* `RBM.norm_Uker_fastDecay_le`, `norm_Uker_fastDecay_le_of_eq`,
  `norm_Uker_fastDecay_le_sumZero_sigma` (`Hierarchy/KernelDecay.lean`) — the pointwise
  engine, T51+T55, unchanged.
* `RBM.norm_xiOf_mSigma`, `xiOf_mSigma_ne_zero` (`Hierarchy/KernelDecay.lean:1570,1574`) —
  `|ξᵢ| = 1`, `ξᵢ ≠ 0` for the paper's charge.
* `RBM.Gauss.witTensor`, `witTensor_ne_zero`, `norm_witTensor_le`, `fastDecay_witTensor`,
  `sumZero_witTensor` (`Gauss/Lemma514Q716.lean`) — the witness tensor.
* `RBM.SumZeroDyn.sumZeroAt_zero_of_sumZero` (`Hierarchy/SumZeroDyn.lean:101`) — converts
  `Gauss.witTensor`'s "sum-zero at every coordinate" to `SumZeroAt L 0`.
* `RBM.ellHat_zero` (`Propagator/Decay.lean:496`) — `ellHat L 0 = 1`, used to instantiate
  the witnesses' fast-decay radius at `s = 0`.

## Open issues

* (T4) `uker_preserves_decay` (Lemma 5.9, remark after (5.75)) is genuine new work with no
  existing Lean counterpart found; not attempted (optional per the ticket, not required by
  the release condition).
* The paper's literal `W^{-D+C_n}` error term (no `η_s/η_t` factor) is not what is proved;
  the accepted, already-on-record replacement `((1-s)/(1-t))^n · δ` is used instead (see
  math preflight above and `docs/paper-deltas.md` #35). No new paper-delta entry was needed
  since #35 already covers exactly this discrepancy for Lemma 7.3 in general.
* `uker_decay_le_nonAlt`'s constant depends on the fixed bulk gap `κ = min(2-|E|,1)` in
  addition to `n` (via `cKerShort n √κ`); this is a dependence on the fixed parameter `E`,
  not on `N, W, L, s, t`, and is inherited unchanged from `norm_Uker_fastDecay_le_of_eq`.
