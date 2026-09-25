Prover model: claude-sonnet-5

# T1495 — M1: the initial condition `J*_{s,D} ≺ 1` (§5.3, from (2.68)/(2.69))

## 0. Required reading

`CLAUDE.md` §3; `docs/reports/T1488-prove.md` row A5 (§1) and M1 (§3); the definitions of
`jS`, `lk`, `tT`, `jStar` in `RBM1D/Gauss/APrimeSmoothPrefixCanonicalCore.lean` and their use in
`RBM1D/Hierarchy/Step2.lean` (`jS_highProb`, its inline `hinit`, `jStar_le`, `decayProf_le_tT`,
`BoundsCore.decay`).

## Step 0 (read-only checks)

* `jS X E D N u ω := jStar (B.L N) (fun a => ‖lk X E N u ω a‖) (B.W N) (B.ell N u) (etaT E u) D`
  (`Gauss/APrimeSmoothPrefixCanonicalCore.lean:96-99`), and
  `jStar L f W ℓu ηu D := (⨆' a, f a / tailT W ℓu ηu D (zdist L (a0-a1))) + 1` (:79-82).
* `jStar_le (hW : 0 < W) {c} (hc : ∀ a, f a ≤ c * tailT W ℓu ηu D (zdist L (a0-a1))) : jStar L f W ℓu ηu D ≤ c + 1`
  (`Hierarchy/Step2.lean:166-173`).
* `decayProf_le_tT {E N u D} (hA : 1 ≤ B.scale E N u) (a b) : (B.scale E N u)⁻¹^2 * B.decayProf N u D a b ≤ tT B E N D u (zdist (B.L N) (a-b))`
  (`Hierarchy/Step2.lean:1258-1270`), from (2.69)'s tail-function form.
* `BoundsCore.decay : ∀ D>0, StochDom B.P (fun N a ω => X.lkErr E N (s N) ω (pmLoop a.1 a.2)) (fun N a _ => (B.scale E N (s N))⁻¹^2 * B.decayProf N (s N) D a.1 a.2)`
  (`Flow/Hypotheses.lean:278-280`) — this is (2.69) = (2.63).
* The inline `hinit` inside the proof of `jS_highProb` (`Hierarchy/Step2.lean:1320-1324`):
  ```
  have hinit : ∀ b : LoopArg (B.L N) 2,
      ‖lk X E N (s N) ω b‖ ≤ x * tT B E N D (s N) (zdist (B.L N) (b 0 - b 1)) := by
    intro b
    rw [norm_lk_eq]
    exact (h1 (b 0, b 1)).trans (mul_le_mul_of_nonneg_left (decayProf_le_tT hAs _ _) hx0)
  ```
  where `h1` is the good event of `(hB.decay D hD0).highProb hτ` at `x = N^(δ/8)`, and `hAs : 1 ≤ B.scale E N (s N)`
  is a deterministic fact obtained upstream (from `eventually_step_facts`, itself from `hE, hs0, hst, ht1, hc0, hreg`).

**Confirmation**: `hinit` is exactly the per-`ω` bound `‖lk X E N (s N) ω b‖ ≤ c · T_{s,D}(‖b0-b1‖)`
with `c = N^(δ/8)`, obtained from `BoundsCore.decay`'s high-probability event (at exponent `δ/8`) composed
with `decayProf_le_tT` (which needs exactly `1 ≤ B.scale E N (s N)`, i.e. the ticket's `hAs`). This is
precisely the hypothesis and the bound named by M1's sources. `jS_highProb` does not use `hinit` alone to
conclude a `jS`-bound directly (it feeds `hinit` into `step_bound`, a much larger pathwise argument for the
*flow* estimate (5.21)); but M1 only asks for the **initial-time** conclusion `J*_{s,D} ≺ 1`, which is a
direct consequence of `hinit`'s bound (at whatever exponent `τ/2 > 0` the ambient `StochDom` definition
requires) composed with `jStar_le` (`Hierarchy/Step2.lean:166`, already-accepted, purely deterministic
arithmetic: `f a ≤ c·T(...)` for all `a` implies `jStar ≤ c+1`).

No extra hypothesis beyond M1's list is needed: `jStar_le` needs only `0 < B.W N` (from `Band.W_pos`,
already available with no extra hypothesis), and the exponent bookkeeping `N^(τ/2)+1 ≤ N^τ` (eventually in
`N`, for any fixed `τ>0`) is elementary and already available as `RBM.eventually_le_rpow` /
`RBM.UnifDetDom.rpow_half_mul_rpow_half` in `Defs/Domination.lean`, used throughout `Defs/StochDom.lean` for
exactly this kind of "absorb the +1" step (e.g. `StochDom.const_mul_right`, `StochDom.of_subset_union`).

**Step 0 verdict: no obstacle.** The definitions match exactly; no extra hypothesis is needed; proceed.

## 1. Math preflight

**Target (T1) `RBM.Step2.stochDom_jS_init`.**

Statement (matching the ticket and M1 verbatim):
```
theorem stochDom_jS_init (X : Sample B) {E : ℝ} {s : ℕ → ℝ} (hB : BoundsCore X E s)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hs1 : ∀ N, s N < 1)
    (hAs : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (s N)) :
    ∀ D : ℝ, 0 < D →
      StochDom B.P (fun N (_ : Unit) ω => jS X E D N (s N) ω) (fun _ _ _ => 1)
```

* **Formula vs. paper**: this is exactly (2.68)/(2.69)'s consequence `J*_{s,D} ≺ 1` used at the start of the
  Step-2 stopping-time argument (§5.3), as identified and audited PASS in `docs/reports/T1488-prove.md` row
  A5 / M1. No paper formula number changes; the constant bound `1` (not `N^ε`) is literal, matching the
  `≺` definition itself (which already carries the `N^τ` factor via `StochDom`'s universal `τ`).
* **Hypotheses**: exactly the ticket's five: `BoundsCore X E s`, `|E| < 2`, `∀ N, 0 ≤ s N`, `∀ N, s N < 1`,
  `∀ᶠ N, 1 ≤ B.scale E N (s N)`. No hypothesis is added, dropped, weakened, or strengthened relative to M1.
  (`hE` and `hs1` are not needed by *this* proof's arithmetic — `jS` is a plain real-valued function of `E,
  s N` regardless of sign/range — but they are part of M1's named signature and are kept verbatim so the
  declaration matches M1 and downstream callers exactly.)
* **Quantifier order**: fixed parameters (`X, E, s`) then the hypotheses, then `∀ D > 0` the conclusion,
  matching the paper's "fix all parameters, then let `N → ∞`" order and matching M1 literally.
* **Dependencies**: `BoundsCore.decay` (`Flow/Hypotheses.lean`, committed, accepted as (2.69)),
  `decayProf_le_tT`, `jStar_le`, `norm_lk_eq` (all `Hierarchy/Step2.lean`, committed), and the generic
  `StochDom`/`HighProb` API of `Defs/StochDom.lean` and `Hierarchy/SumZeroDyn.lean`
  (`SumZeroDyn.stochDom_of_good`), all already accepted/committed. No new axiom, no forward reference to an
  unproved result.
* **Boundary cases**: `D` ranges over all `D > 0` (not just `D ≥ 60` as `jS_highProb` needs for the flow
  argument) — `jStar_le`/`decayProf_le_tT` impose no lower bound on `D` beyond `D > 0`, so M1's `∀ D > 0` is
  correctly the full range, no vacuous restriction. `τ` in the `StochDom` definition ranges over all `τ > 0`;
  the proof uses `τ/2 > 0` internally (valid since `τ > 0`), and the arithmetic step `N^(τ/2)+1 ≤ N^τ`
  eventually in `N` is exactly the standard "absorb a `+1`" pattern already used in this codebase (no new
  loss beyond what `≺`'s own `∀τ>0` already allows for). No `N = 0` case: `atTop`-eventual statements never
  need `N=0`; `B.L N ≥ 3` (`Band.three_le_L`) rules out an empty loop-index type, so `jStar`'s `sup'` over
  `Finset.univ_nonempty` is never over an empty set (no `T164/T169`-style vacuity).
* **Simultaneous satisfiability of hypotheses**: `BoundsCore X E s` together with `|E|<2`, `hs0`, `hs1`,
  `hAs` is exactly the hypothesis bundle already used (as a strict *sub*list, with additional hypotheses
  `hst, ht1, hB(BoundsCore), hc0, hreg,...`) inside the already-accepted, already-building
  `RBM.Step2.jS_highProb` (`Hierarchy/Step2.lean:1293`), where the corresponding `hAs`-fact is *derived*
  (not assumed) from `hE, hs0, hst, ht1, hc0, hreg` via `eventually_step_facts`; taking `hAs` here as a
  direct hypothesis only weakens what is demanded upstream, and a witness bundle exists structurally: at
  `t = 0`, `H_0 = 0` (`Sample.H_zero`) forces `X.lkErr E N 0 ω = 0` identically (`Lval`/`Kval` both reduce to
  the same tree value at `t=0` since `zt E 0 = E` degenerately and the Green's function of `H=0` is
  explicit), so `BoundsCore X E (fun _ => 0)` is the trivial (zero) instance of Definition 2.1(ii)'s
  deterministic-domination-implies-stochastic-domination route (`StochDom.of_unifDetDom` with `f ≡ 0`); and
  `B.scale E N 0 = W N · ℓ_0(N) · η(E,0) ≥ W N · 1 · Im m^{(E)} → ∞` (`Band.bandwidth`, `one_le_ellHat`,
  `mE_im_pos`), so `hAs` holds eventually for `s ≡ 0`, `|E|<2` arbitrary in `(-2,2)`. This is not
  astronomically large or degenerate: it is the paper's own base case for the induction that Step 2 starts
  from (§5.3's `s` is the start-of-cell time, and (2.68)–(2.70) at `s=0` are the trivial statements that seed
  Theorem 2.21's induction, per the file's own §62 remark on p. 25"Steps 1–5 propagate" `BoundsCore`).
  I did not additionally *construct* this witness in Lean for this ticket (M1 is stated conditionally, and
  the ticket does not ask for an existence lemma); I record the argument here per gate 4 for the auditor.

**Verdict: PASS.** No obstacle found; the target is provable from already-accepted material with exactly
M1's hypotheses, no widening, no vacuity.

## 2. Lean

### Declarations added (`RBM1D/Hierarchy/Step2Init.lean`)

* `RBM.Step2.stochDom_jS_init` — (T1), stated and proved as above.

### Proof sketch

For `τ > 0`, take the good event `G` of `(hB.decay D hD0).highProb (half_pos hτ)` (exponent `τ/2`). On
`G N` (and using `hAs` at that `N`), for every `b : LoopArg (B.L N) 2`,
`‖lk X E N (s N) ω b‖ = X.lkErr E N (s N) ω (pmLoop (b0) (b1))` (`norm_lk_eq`)
`≤ N^(τ/2) · ((B.scale E N (s N))⁻¹² · B.decayProf N (s N) D (b0) (b1))` (the good event)
`≤ N^(τ/2) · tT B E N D (s N) (zdist (B.L N) (b0-b1))` (`decayProf_le_tT`, using `hAs`).
By `jStar_le` (`0 < B.W N` from `Band.W_pos`), `jS X E D N (s N) ω ≤ N^(τ/2) + 1`. Eventually in `N`,
`2 ≤ N^(τ/2)` (`eventually_le_rpow 2 (half_pos hτ)`), so `N^(τ/2)+1 ≤ 2·N^(τ/2) ≤ N^(τ/2)·N^(τ/2) = N^τ`
(`UnifDetDom.rpow_half_mul_rpow_half`). This is exactly `jS X E D N (s N) ω ≤ N^τ · 1`, closing
`SumZeroDyn.stochDom_of_good`'s obligation.

### Build

```
lake build RBM1D.Hierarchy.Step2Init
```
Result: **succeeded** (3749/3749 jobs, "Build completed successfully"). Only lint warnings: the
mandatory `unusedVariables` warnings for `hE`, `hs0`, `hs1` (kept, unused by this proof's arithmetic,
but required verbatim by M1's named signature and by downstream callers), and a pre-existing
`style.show` warning also present upstream in `Hierarchy/Step2.lean:1341` (harmless linter note, not
an error).

### Axioms

```
$ lake env lean /tmp/axcheck.lean   # `import RBM1D.Hierarchy.Step2Init; #print axioms RBM.Step2.stochDom_jS_init`
'RBM.Step2.stochDom_jS_init' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three permitted axioms.

### Key lemmas used

`RBM.BoundsCore.decay`, `RBM.StochDom.highProb`, `RBM.SumZeroDyn.stochDom_of_good`,
`RBM.Step2.decayProf_le_tT`, `RBM.Step2.norm_lk_eq`, `RBM.Step2.jStar_le`, `RBM.eventually_le_rpow`,
`RBM.UnifDetDom.rpow_half_mul_rpow_half`, `RBM.Band.W_pos`.

### Open issues

None for this target. (The satisfiability witness sketched in §1 is not constructed in Lean here; it is
outside the ticket's scope, which is repackaging only.)
