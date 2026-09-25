Prover model: claude-sonnet-5

# T1500 — quantitative max-norm bound for the backward evolution kernel

## Math preflight (before any Lean)

Sole source consulted per ticket: `RBM1D/Hierarchy/Kernel.lean:90–240` (as read in the T1500
worktree) and `RBM1D/Gauss/GridDuhamel.lean`, `RBM1D/Gauss/GridPath.lean` (imported from
`Uker_factor`'s file and T1481's file). `docs/claude-team/pilot-P4P5-paper.md` §9 is the
narrative source for the repair; the actual algebraic facts used below are all already-proved
Lean lemmas in `Kernel.lean` (`edgeKer_eq`, `sum_norm_edgeKer_row_le`, `norm_Uker_apply_le`,
`Theta_commute_SB` — the last only used transitively inside those lemmas, not directly).

### Setup: which direction is "backward"

`Uker_factor` (`RBM1D/Gauss/GridDuhamel.lean:148`) states the explicit two-sided inverse of
`Uker L ξ (u k) t` is `Uker L ξ t (u k)` — i.e. the *back* kernel has the **large** time first
and the **small** time second, in the argument order of `RBM.Uker`/`RBM.edgeKer` (`edgeKer L ξ s
t = (1 - s·ξ • SB) * Theta L (t·ξ)`, so "back" means `s := t_big`, `t := u_small` in that
signature). This matches the ticket's display `edgeKer L ξ t u = 1 − (t−u)·ξ·(SB·Theta(uξ))`,
which is exactly `edgeKer_eq` instantiated at `s := t, t := u` (using the *lemma's* own `s,t`
names, not the ticket's).

### (T1) `RBM.sum_norm_edgeKer_back_row_le`

Statement to prove: for `3 ≤ L`, real `0 ≤ u ≤ t < 1`, `‖ξ‖ ≤ 1`:
`∑ c, ‖edgeKer L ξ t u x c‖ ≤ 1 + (t−u)‖ξ‖(1−u‖ξ‖)⁻¹ ≤ 2`.

- **Statement vs. paper/Lean source.** `sum_norm_edgeKer_row_le L hL (ht : ‖t*ξ‖<1) a : ∑ b,
  ‖edgeKer L ξ s t a b‖ ≤ 1 + ‖(s-t)*ξ‖*(1-‖t*ξ‖)⁻¹` (Kernel.lean:144). Instantiating the
  lemma's `s := t_ticket`, `t := u_ticket` (both cast `ℝ → ℂ`) reproduces exactly the ticket's
  displayed inequality, provided the hypothesis `‖(u:ℂ)*ξ‖ < 1` holds and provided the complex
  norms `‖((t:ℂ)-(u:ℂ))*ξ‖`, `‖(u:ℂ)*ξ‖` are rewritten to the real quantities `(t-u)‖ξ‖`,
  `u‖ξ‖` (valid since `t-u ≥ 0` and `u ≥ 0`, using `Complex.norm_real` and `norm_mul`).
- **Hypotheses / dependencies.** `hL : 3 ≤ L` and `ht : ‖t_ticket*ξ‖ < 1`
  (i.e. here `‖(u:ℂ)*ξ‖<1`) are exactly what `sum_norm_edgeKer_row_le` demands; both are
  already-accepted (committed) lemmas of `Kernel.lean`. No new hypothesis class is introduced.
- **Deriving `‖(u:ℂ)*ξ‖ < 1`.** `‖(u:ℂ)*ξ‖ = u‖ξ‖ ≤ u·1 = u ≤ t < 1` (uses `0 ≤ u`, `‖ξ‖ ≤ 1`,
  `u ≤ t`, `t < 1`). Non-vacuous: e.g. `u = 0`, `t = 1/2`, `ξ = 1` satisfies every hypothesis
  strictly.
- **The "≤ 2" half, and Step 0's request.** Need
  `(t-u)‖ξ‖(1-u‖ξ‖)⁻¹ ≤ 1`, i.e. (since `1-u‖ξ‖>0`, shown above) `(t-u)‖ξ‖ ≤ 1-u‖ξ‖`, i.e.
  `t‖ξ‖ ≤ 1`. Since `‖ξ‖ ≤ 1` and `t < 1`: `t‖ξ‖ ≤ t·1 = t < 1 ≤ 1`. So the inequality holds
  with strict room to spare on the *entire* stated hypothesis range, **including the boundary
  `‖ξ‖ = 1` exactly** (Step 0's specific worry): at `‖ξ‖=1` the bound becomes
  `t‖ξ‖ = t < 1`, still `< 1`, so `t‖ξ‖ ≤ 1` holds with slack `1-t > 0`. **Conclusion of Step
  0: the constant `2` does *not* fail at `‖ξ‖ = 1`; it is confirmed, not falsified.** (It is
  only approached, in the limit `t → 1⁻`, `‖ξ‖ → 1`, `u → 0`, never exceeded, because the
  ticket's own hypothesis is the *strict* `t < 1`, not `t ≤ 1`.) No alternate constant is
  needed.
- **Quantifier order / boundary cases.** `u = t` (degenerate window): bound becomes
  `1 + 0·(...)⁻¹ = 1 ≤ 2`, fine (no `0/0` since `(1-u‖ξ‖)⁻¹` is finite as `u‖ξ‖ < 1`). `u = 0`:
  bound is `1 + t‖ξ‖ ≤ 1 + t < 2`. `ξ = 0`: bound is exactly `1 ≤ 2`.
- **Simultaneous satisfiability witness.** `L = 3`, `u = 0`, `t = 1/2`, `ξ = 1`: all
  hypotheses (`3≤L`, `0≤u≤t<1`, `‖ξ‖≤1`) hold with strict inequalities throughout (not an
  `N=0`/empty/collapsed-window degeneracy).
- **Verdict: PASS.**

### (T2) `RBM.norm_Uker_back_le`

Statement: for `n` edges with every `‖ξ i‖ ≤ 1`, `0 ≤ u ≤ t < 1`: `∀ A a, ‖Uker L ξ t u A a‖ ≤
2^n * M` whenever `∀ b, ‖A b‖ ≤ M` (`0 ≤ M`).

- **Statement vs. Lean source.** This is `norm_Uker_apply_le` (Kernel.lean:256) instantiated
  at `s := (t_ticket:ℂ)`, `t := (u_ticket:ℂ)`, `C := 2`, with `ht := (∀ i, ‖(u:ℂ)*ξ i‖<1)`
  (proved per-edge exactly as in (T1)) and `hC := (∀ i, 1+‖((t:ℂ)-(u:ℂ))*ξ i‖(1-‖(u:ℂ)*ξ
  i‖)⁻¹ ≤ 2)` (the per-edge instance of (T1)'s second inequality). `norm_Uker_apply_le` is
  already-accepted/committed; no new analytic content beyond (T1), only bookkeeping the
  `n`-fold product.
- **Uniformity in `u` — the point of the ticket.** The constant `C = 2` in
  `norm_Uker_apply_le`'s conclusion `‖Uker L ξ s t A a‖ ≤ C^n * M` does not depend on `u`
  (`t_ticket` in the lemma's naming) at all — it is fixed at `2` for *every* `u ∈ [0,t]` by
  (T1)'s uniform bound. In particular there is no hidden `(1-u)⁻¹` or `(1-t)⁻¹` factor: the
  only place a `(1-·)⁻¹` appears is `(1-u‖ξ‖)⁻¹` in the *intermediate* expression, which (T1)
  already discharges into the `u`-free constant `2` before it ever reaches (T2)'s statement.
- **Hypotheses satisfiable simultaneously.** `n = 1`, `ξ = fun _ => (1:ℂ)`, `L = 3`, `u = 0`,
  `t = 1/2`, `M = 1`, `A = fun _ => (1:ℂ)`: gives `‖ξ 0‖ = 1 ≤ 1`, `‖A b‖ = 1 ≤ M = 1`, and a
  non-trivial conclusion `‖Uker L ξ t u A a‖ ≤ 2`.
- **Boundary `n = 0`:** `LoopArg L 0 = (Fin 0 → ZMod L)` is a one-point type (the empty
  function); `Uker` reduces to `A` itself times the empty product `= 1`; bound `2^0*M = M`,
  consistent and non-vacuous (`Uker L ξ t u A a = A a` in this case, `‖A a‖ ≤ M` by `hA`).
- **Verdict: PASS.**

### (T3) grid-time corollary

Statement: the bound of (T2) at `u = Gauss.Grid.time s t K N k` (T1481's `time`, merged in
`RBM1D/Gauss/GridPath.lean`) for `k ≤ K N`, matching the direction `Uker ξ t (time …)` used by
`Uker_factor`'s explicit inverse.

- **Reduction to (T2).** Only additional fact needed: `0 ≤ time s t K N k ≤ t N` given `0 ≤ s
  N`, `s N ≤ t N`, `K N ≠ 0`, `k ≤ K N`. Proof: `step s t K N = (t N - s N)/K N ≥ 0`
  (numerator and denominator nonneg, `K N > 0` from `K N ≠ 0`); `time = s N + k·step ≥ s N ≥
  0`; and `k ≤ K N ⟹ k·step ≤ K N·step = t N - s N` (using `mul_div_cancel₀`, the identity
  already used by `GridPath.lean`'s own `time_last`), so `time ≤ s N + (t N - s N) = t N`. This
  is pure real arithmetic from already-accepted (merged) definitions `time`, `step`; no new
  hypothesis beyond what (T2) already required plus the grid's own well-formedness conditions
  (`K N ≠ 0`, `s N ≤ t N`, `s N ≥ 0`) which are exactly `map_H_eq`'s own hypotheses in
  `GridPath.lean`, i.e. already the conditions under which `time` is meaningful in this repo.
- **`k = 0` boundary:** `time … 0 = s N` (`time_zero`), giving `u = s N ≥ 0`; `k = K N`
  boundary: `time … (K N) = t N` (`time_last`), giving `u = t N = t` — the *degenerate* window
  `u = t`, already checked non-problematic in (T1)/(T2) (bound reduces to `1`, resp. still
  `2^n`).
- **Simultaneous satisfiability witness.** `s = fun _ => (0:ℝ)`, `t = fun _ => (1/2 : ℝ)`, `K =
  fun _ => 1`, `N` arbitrary, `k = 0` or `k = 1`: `K N ≠ 0`, `0 ≤ s N = 0 ≤ t N = 1/2 < 1`, `k ≤
  K N`. Non-degenerate.
- **Verdict: PASS.**

## Summary of preflight verdicts

| Target | Verdict |
|---|---|
| T1 `sum_norm_edgeKer_back_row_le` | PASS |
| T2 `norm_Uker_back_le` | PASS |
| T3 `norm_Uker_back_grid_le` | PASS |

Step 0 explicit answer: **the constant `2` does not fail at `‖ξ‖ = 1`** — it holds (with room
to spare, since the ticket's hypothesis is `t < 1` strictly) at every point of the stated
hypothesis set, including `‖ξ‖ = 1` exactly. No alternate constant is required or used.

## Lean

See declarations below, file `RBM1D/Hierarchy/UkerBackBound.lean`.

### Declarations added

- `RBM.sum_norm_edgeKer_back_row_le` (T1)
- `RBM.norm_Uker_back_le` (T2)
- `RBM.norm_Uker_back_grid_le` (T3)
- private helpers: `RBM.norm_real_mul`, `RBM.back_bound_real`, `RBM.grid_time_mem`

### Build

```
lake build RBM1D.Hierarchy.UkerBackBound
```
Result: `Build completed successfully (3703 jobs)` — `✔ Built RBM1D.Hierarchy.UkerBackBound`.
No `sorry`/`admit`/`axiom` in the new file (checked with `grep`). All lint warnings emitted by
this build come from pre-existing files (`GridPath.lean`, `KBound.lean`, `Model.lean`), not from
`UkerBackBound.lean`.

### Axioms

```
#print axioms RBM.sum_norm_edgeKer_back_row_le
#print axioms RBM.norm_Uker_back_le
#print axioms RBM.norm_Uker_back_grid_le
```
All three: `depends on axioms: [propext, Classical.choice, Quot.sound]` — the allowed set only.

### Key lemmas used

- `RBM.sum_norm_edgeKer_row_le`, `RBM.edgeKer_eq` (`Kernel.lean`)
- `RBM.norm_Uker_apply_le` (`Kernel.lean`, Lemma 7.1)
- `RBM.Gauss.Grid.time`, `.step`, `.time_zero`, `.time_last` (`GridPath.lean`, T1481, merged)
- `Complex.norm_real`, `mul_le_of_le_one_right`, `div_le_one`, `mul_div_cancel₀` (Mathlib)

### Open issues

None found in preflight. `Uker_factor` itself (T1485) is not invoked by the Lean proofs — only
its *direction convention* (`Uker ξ t u_k` as the back kernel) is used to fix the argument order
of the theorems here; the ticket does not ask this file to re-derive `Uker_factor`.
