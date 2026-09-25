Prover model: claude-sonnet-5

# T1487 — deterministic Lipschitz bound for the loop drift (pilot P4/P5)

Branch: `t/T1487`. Sole writable file: `RBM1D/Gauss/GridDriftLip.lean`.

## (a) Math preflight (per target)

Read: `CLAUDE.md` §3; `RBM1D/Gauss/LoopIto.lean` (module doc, `generator_add_zMotion`,
`generator_add_zMotion_gauss`, `eGterm`, `zMotion`); `RBM1D/Gauss/LoopLipschitz.lean` §1–2;
`docs/claude-team/pilot-P4P5-paper.md` §2–3; plus the definitions listed in the ticket's step 0
(`eGterm` in `Gauss/Hierarchy.lean`, `primRhs`/`primInit` in `Loop/Primitive.lean`, `gloop`/`Gsig`
in `Loop/GLoop.lean`, `mSigma`/`zt` in `Defs/Semicircle.lean`, `LoopIdx.cutGlue`/`cutGlueL`/
`cutGlueR` and their length/WF lemmas in `Loop/Index.lean`).

**Step 0 findings.**
- `eGterm L W m M z I` sums, for `k ∈ Icc 1 I.length`, a trace term
  `Tr((G(σ_k) − m(σ_k)·1)·E_a)` against `SB·L_{...}` at `I.cutGlue k b`; every summand is a
  finite combination of loops/resolvent entries of the *current* matrix `M` only — no term
  outside the loop vocabulary, so the ticket's "blocked if `eGterm` contains a non-loop term"
  clause does not trigger.
- The matrix norm used throughout `LoopLipschitz.lean` (`norm_gloop_sub_le`,
  `norm_Gsig_le_of_green`, …) is the `ℓ²`-operator norm, `open scoped Matrix.Norms.L2Operator`;
  (T2)/(T3) use exactly this norm (same `open scoped`), matching the ticket's requirement (b).
- `grep green_sub / resolvent` (ticket step 0 (c)): no existing `‖green M₁ z − green M₂ z‖ ≤
  |z.im|⁻¹² ‖M₁ − M₂‖` lemma; `RBM.norm_green_sub_le` (`Gauss/FlowHolder.lean`) gives the
  two-parameter form `‖G_u−G_v‖ ≤ ‖G_u‖·(‖H−H'‖+|z−z'|)·‖G_v‖`; specializing `z=z'` and combining
  with `RBM.Gauss.norm_green_le` (`‖G‖ ≤ η⁻¹` for Hermitian `M`, `η ≤ |z.im|`) gives T3.
- `I.cutGlue k b` (used inside `eGterm`, `1 ≤ k ≤ I.length`) has length exactly `I.length + 1`
  (`RBM.LoopIdx.length_cutGlue`, `WF.cutGlue`); `I.cutGlueL k l a`, `I.cutGlueR k l b` (used
  inside `primRhs`, `1 ≤ k < l ≤ I.length`) have length `≤ I.length`
  (`length_cutGlueL_le`/`length_cutGlueR_le`, `WF.cutGlueL`/`WF.cutGlueR`). So every sub-loop
  reachable from `eGterm`/`primRhs (gloop ·)` at `I` has `.σ.length ≤ I.σ.length + 1` once
  `I.WF` holds — this is the deterministic "one slot longer" envelope the module docstring of
  `LoopIto.lean` already flags for `norm_zMotion_le`, and it is what lets a single pair of
  constants dominate every term of both sums.

**(T1) `loopDrift`.** Ticket's formula
`eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N)
M (zt E u)) I` is *literally* the right-hand side of `generator_add_zMotion_gauss`
(`Gauss/LoopIto.lean:2580`, checked by direct comparison of the two terms, and by the `rfl`
lemma `loopDrift_eq` added alongside it). No hidden hypothesis, no existential; a plain
definition. **PASS.**

**(T2) `norm_loopDrift_sub_le`.** Hypotheses as stated: `(zt E u).im ≠ 0`, `η := |(zt E u).im|`,
`M₁ M₂` Hermitian, `I.WF`, `1 ≤ I.a.length`. Quantifier order: `E u` first (implicit, universally
quantified ahead of the matrices, matching the paper's parameter order — `E`, `u` fix the
spectral parameter, `M₁, M₂` are the varying matrix argument); no `∀ᶠ N` here since (T2) is a
purely deterministic, per-`N` statement (the ticket does not ask for an asymptotic-in-`N`
form). Dependencies used — `generator_add_zMotion_gauss`, `eGterm`, `primRhs`, `norm_gloop_sub_le`
— are all already-accepted, committed results (no new hypothesis added to any of them).
Boundary/vacuity check: `I.a.length = 0` is excluded by `1 ≤ I.a.length`; `L = 0` or `W = 0` are
excluded by the ambient `[NeZero L] [NeZero W]` instances on `Dims` (`d.three_le_L N : 3 ≤ d.L N`
gives `L ≠ 0` automatically, and `d.W_pos N` gives `W ≠ 0`); `η = 0` is excluded by
`(zt E u).im ≠ 0`. Simultaneous satisfiability: `Dims.exampleGrow` (used elsewhere in the repo,
e.g. `RBM.hsep_exampleGrow`) together with any `E, u` with `(zt E u).im ≠ 0` (an open, nonempty
condition on `u` since `zt E u = E + (1-u)·mE E}` and `mE E` has nonzero imaginary part for
`|E| < 2`) and any Hermitian `M₁ ≠ M₂` gives a genuine, non-degenerate witness — the bound is not
vacuously true only because no matrices/`N` satisfy the hypotheses. `driftLip` is an explicit,
non-existential closed-form expression
`4·L⁴·W³·n²·(n+1)·(K+‖m‖)²·K^{2(n+1)}·η⁻²` with `K := 1+η⁻¹`, `‖m‖ := max‖m true‖‖m false‖`,
`n := I.σ.length` — polynomial in `L, W, n, η⁻¹, ‖mSigma E‖` as required, no dependence on `M₁,
M₂` beyond the separate `‖M₁ − M₂‖` factor, matching `norm_gloop_sub_le`'s own norm convention.
**PASS**, with the route: `norm_mul_mul_sub_le` (`(A₁−A₂)SB₁ + A₂S(B₁−B₂)`, already in
`Loop/Unique.lean`) telescopes every `A·SB·B` summand of `eGterm`/`primRhs`; `norm_gloop_sub_le`
supplies the loop-difference factor; the resolvent-difference bound feeding it is (T3).

**(T3) `norm_green_sub_le_of_herm`.** Statement as given in the ticket. Route as in step 0 above.
No existing lemma of this exact shape (checked, see step 0), so it is proved fresh. **PASS.**

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridDriftLip.lean` (namespace `RBM.Gauss.Grid`).

Public declarations (targets):
- `norm_green_sub_le_of_herm` (T3), l. 71.
- `loopDrift` (T1, `noncomputable def`), l. 254; `loopDrift_eq` (the `rfl` check that it is
  literally the right-hand side of `generator_add_zMotion_gauss`), l. 260.
- `driftLip` (`noncomputable def`, the explicit constant), l. 268.
- `norm_loopDrift_sub_le` (T2), l. 605.

Private helpers (same file, not part of the ticket's named targets, all `private`):
`norm_green_sub_le_of_herm'` (generic core of T3, avoids unifying `d.Idx N` against `ZMod L ×
Fin W` for existential `d, N` — see open issue below), `real_mul_pow_le_of_le`,
`norm_gloop_le_of_herm`, `norm_sum_sub_le`, `norm_primRhs_sub_le`, `norm_eGtermSum_sub_le`,
`traceEnv_le`, `traceDiff_le`, `gloopEnv_le`, `gloopDiff_le`, `norm_loopDrift_sub_le_aux` (the
fully generic `L W : ℕ` core of T2; the public `norm_loopDrift_sub_le` is a two-line wrapper
instantiating it at `L := d.L N`, `W := d.W N`).

Build:
```
cd RBM1D-wt/T1487 && lake build RBM1D.Gauss.GridDriftLip
```
Result: `Build completed successfully (3784 jobs)` — module compiles in ≈3s once fixed (see open
issue). Only style-linter warnings remain (`show` tactic style, matching dozens of pre-existing
uses of the same pattern elsewhere in the repo); no errors, no `sorry`/`admit`/`axiom`.

Axioms (`lake env lean` on a throwaway file `import RBM1D.Gauss.GridDriftLip; #print axioms ...`):
```
'RBM.Gauss.Grid.norm_green_sub_le_of_herm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.loopDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.loopDrift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.driftLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.norm_loopDrift_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms.

## (c) Key lemmas used

`RBM.Gauss.generator_add_zMotion_gauss`, `RBM.Gauss.eGterm`, `RBM.primRhs`, `RBM.gloop`,
`RBM.Gsig`, `RBM.green`, `RBM.Gauss.norm_green_le`, `RBM.norm_green_sub_le`,
`RBM.norm_Gsig_le_of_green`, `RBM.norm_Gsig_sub_le_norm_green_sub`, `RBM.norm_gloopProd_le_pow`,
`RBM.norm_gloop_sub_le`, `RBM.norm_trace_le_card_mul`, `RBM.norm_mul_mul_sub_le`,
`RBM.norm_SB_apply_le`, `RBM.norm_Eblk_le_one''`, `RBM.LoopIdx.WF.cutGlue`/`cutGlueL`/`cutGlueR`,
`RBM.LoopIdx.length_cutGlue`/`length_cutGlueL_le`/`length_cutGlueR_le`/`two_le_length_cutGlueL`/
`two_le_length_cutGlueR`, `RBM.Gauss.Dims.three_le_L`.

## (d) Open issues / notes for the auditor

1. **The dominant debugging finding, worth recording for future tickets.** `norm_green_sub_le_of_herm`
   (T3) was first written directly for `M₁ M₂ : Matrix (d.Idx N) (d.Idx N) ℂ` (matching the
   ticket's literal wording) and then *called from* the fully generic `L W : ℕ` core of T2
   (needed so the `eGterm`/`primRhs` sum bookkeeping is a clean induction on abstract `L, W`
   rather than repeatedly fighting `Dims`). Calling a `{d : Dims} {N : ℕ}`-parameterized lemma
   whose statement contains `Matrix (d.Idx N) (d.Idx N) ℂ` from a context with only abstract
   `L W : ℕ` forces Lean to solve `d.Idx N =?= ZMod L × Fin W` for *some* `d, N` — an
   unconstrained higher-order unification problem that is not obviously unsolvable to the
   elaborator and triggers a real (up to several-minutes, heartbeat-limited) `whnf` runaway
   rather than a clean failure. Root-caused by bisection (replacing successive suffixes of the
   main proof with `sorry` until the failure moved past a two-line block). Fixed by factoring
   T3 into a `private` fully generic core `norm_green_sub_le_of_herm'` (over `{n : Type*}
   [Fintype n] [DecidableEq n] [Nonempty n]`) and making the public, `Dims`-tied
   `norm_green_sub_le_of_herm` a one-line wrapper; the generic core is what the generic T2 core
   actually calls. No other lemma used in this file has this shape (`norm_green_le`,
   `norm_green_sub_le`, `norm_gloop_sub_le`, etc. are all already stated generically), so this
   was an isolated, self-inflicted issue, not a defect in existing infrastructure.
2. `driftLip`'s constant is intentionally not sharp (e.g. it uses the crude bound `‖Tr(X)‖ ≤
   (dim)·‖X‖_op` and a single uniform exponent `K^{2(n+1)}` for both the length-`(n+1)` and
   length-`≤ n` sub-loops); the ticket only asks for an explicit polynomial bound, not an
   optimal one, and this is recorded in the module docstring.
3. `hn : 1 ≤ I.a.length` and `hL3`/`NeZero` are the only hypotheses used to derive the bound;
   nothing beyond the ticket's stated hypotheses was added.
