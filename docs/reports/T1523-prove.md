Prover model: claude-opus-5-5

# T1523 — math preflight (written before any Lean)

Scope per ticket: (T1) `primRhs_split`; (T2) `K_step_n`, `Uker_step_n`; (T3)
`discrete_hierarchy_step_n`. Sole writable file: `RBM1D/Gauss/GridHierarchyN.lean`.
Dependencies T1506, T1516 already merged into `main`.

## Step 0 read-only checks (summary of what was found)

- `RBM1D/Gauss/GridDriftAlgebra.lean` (T1506, n = 2 template): `Lval`, `Kv`,
  `loopDrift_sub_K_deriv` (T1), `K_step` (T2), `Uker_step` (T3),
  `discrete_hierarchy_step`/`discrete_hierarchy_step_unif` (T4), `stepErr`. All hard-wired to
  `LoopArg (B.L N) 2` / `σ = (+,-)`.
- `RBM1D/Hierarchy/Dynamics.lean`: `primBil`, `primRhs_sub` (5.12)/(5.13), `primBilLen` (5.14,
  left orientation), `sum_primBilLen`, `primBil_eq_two_add` (5.15) — **all already general in
  the loop length `n = I.length`**, no `n = 2` restriction anywhere.
- `RBM1D/Hierarchy/Decay.lean` (400–470 read in full): `primBilLenR` (right orientation),
  `couplingLen := primBilLen lK K D + primBilLenR lK D K` (both orientations of (5.14)),
  `sum_couplingLen` — **also already general in `n`**.
- `RBM1D/Gauss/GridLoopStep.lean` (statements): `condExp_loop_drift` (line 892) is stated for
  an **arbitrary** `I : LoopIdx (ZMod (d.L N))` with only `hwf`/`hn : 1 ≤ I.a.length` — already
  general, confirming the ticket's claim. `zMotionLip/zMotionZLip/genPtLip` are parametrized by
  `I.σ.length`, likewise general.
- `RBM1D/Gauss/Lemma514Holder.lean` (statements): `norm_primRhs_le` (line 203, general `I`,
  envelope hypothesis `hB` on sub-loops of length `2..I.length`); `hasDerivAt_Kgen_all`
  (`RBM1D/Loop/TreeRepGeneral.lean:2481`, general `I.length ≥ 2`, **already proved, no `n = 2`
  restriction** — it dispatches to the `n = 2` closed form only internally); `norm_Kgen_sub_le`
  (line 269, a Lipschitz-in-`u` bound for `Kgen` at general `I`, envelope hypothesis); and
  `exists_norm_Kval_le_upto` (line 835): an **unconditional** existence theorem producing, for
  every `m`, an explicit constant giving `‖Kval w J‖ ≤ C·scale(w)^{-(J.length-1)}` for *all*
  `w ∈ [0,1)` and *all* `J` with `2 ≤ J.length ≤ m` — i.e. the "K decays/is bounded at every
  length" input is **already an accepted theorem**, not an open problem, so an envelope
  hypothesis for `K_step_n`/`discrete_hierarchy_step_n` (in the style already used by
  `norm_Kgen_sub_le`/`norm_primRhs_le`) is non-vacuous.
- `EGDef.couplingLen_two_*` (`RBM1D/Hierarchy/EGDef.lean`) is the `n = 2` corollary; the
  **general-`n`** identity is `RBM.Gauss.couplingLen_two_eq_thetaGenLoop`
  (`RBM1D/Gauss/LoopIto.lean:1548`, hypothesis only `hn : 2 ≤ I.length`, `hK` on length-2
  sub-loops, one `hξ` on the wrap-around edge) together with the `LoopArg`/tensor bridge
  `thetaGenLoop_ofFn` (`LoopIto.lean:1634`, general `n`) and `thetaGenOp_eq_ThetaOp`
  (`LoopIto.lean:1629`, `rfl`). `ThetaOp`/`Uker` themselves (`RBM1D/Hierarchy/Kernel.lean:190,
  230`) are defined for general `{n : ℕ}` already, and `norm_Uker_apply_le` (Lemma 7.1, general
  `n`) is already proved there.

**Conclusion of Step 0**: the *loop-identity* layer (T1's algebra, the `l_K = 2` ↔ `ThetaOp`
identification, `condExp_loop_drift`, the `K`-Lipschitz/derivative facts) was **already made
general in `n` by earlier, already-merged tickets**; what T1506 left at `n = 2` is specifically
the *exact quadratic remainder* bookkeeping of (T2)/(T3) (`K_step`, `Uker_step`) and their
assembly into (T4). This matches the ticket's own framing.

## Target-by-target preflight

### (T1) `primRhs_split`

Statement to prove: for `K, D : LoopIdx (ZMod L) → ℂ` and `I` of length `n ≥ 2` (no further
hypothesis on `K, D`),
`primRhs L W (K + D) I - primRhs L W K I = couplingLen L W 2 K D I + (Σ_{lK ∈ Icc 3 I.length} couplingLen L W lK K D I) + primBil L W D D I`,
plus the corollary that when `K = Kval_u` (any `u`) the `lK = 2` term is literally
`ThetaOp L (xiOf (mSigma E) σ) u (fun v => D ⟨σ, ofFn v⟩) a` for `I = ⟨σ, ofFn a⟩` (general
`n`, general `σ`, generalizing `couplingLen_two_eq_thetaGenLoop` from its `n = 2` corollary use
in T1506 to literal, direct use at `n ≥ 3`).

*Derivation*: `primRhs_sub L W (K+D) K I` gives
`primRhs(K+D) I - primRhs K I = primBil K D I + primBil D K I + primBil D D I` (exact, `Lf-K = D`
since `Lf := K+D`). `sum_couplingLen L W K D I hN` (any `N ≥ I.length+2`) gives
`Σ_{lK ∈ range N} couplingLen lK K D I = primBil K D I + primBil D K I`. Splitting off `lK = 2`
via `Finset.add_sum_erase`, and noting `couplingLen lK K D I = 0` for `lK < 2` (both cut
sub-loops of `I` have length `≥ 2`: `k + I.length - l + 1 ≥ 2` and `l - k + 1 ≥ 2` for
`1 ≤ k < l ≤ I.length`, an arithmetic fact used already in `norm_primRhs_le`'s proof via
`LoopIdx.two_le_length_cutGlueL/R`) and for `lK > I.length` (cut sub-loops have length
`≤ I.length`, `LoopIdx.length_cutGlueL/R_le`), the erased range collapses to
`Finset.Icc 3 I.length` exactly (choosing `N := I.length + 2`). This is pure algebra; no
stochastic content, no new hypothesis beyond `I.length ≥ 2` (needed only so the wrap-around edge
in the `lK = 2` bridge is meaningful) and the single `hξ` norm bound already required by
`couplingLen_two_eq_thetaGenLoop`.

**Failure-signal check** (ticket's own): is the `lK = 2` piece *literally* `ThetaOp` for
`n ≥ 3`, or does the cyclic orientation only work for `n = 2`? `couplingLen_two_eq_thetaGenLoop`
is stated and proved for `2 ≤ I.length` with **no upper bound**, using the wrap-around edge
`xiLoop m I (I.length - 1)` (the edge between the last and first labels, `m_n m_1`, matching
Example 2.16's cyclic convention cited in the plan doc §3, "(5.82) 的相邻是循环的"). So the
literal identification holds at every `n ≥ 2`, alternating or not. **No discrepancy found** —
verdict **PASS**.

**Verdict: PASS.** Quantifiers: `∀ L W n K D I` (`I.length = n ≥ 2`), matching the paper's order
(fixed loop data before any per-`u`/per-`ω` quantifier — this file is purely deterministic, no
`u`/`ω` here at all beyond the `Kval_u` corollary, where `u` is universally fixed first, exactly
the paper's order). No degenerate instantiation: `n ≥ 2` rules out the empty-cut vacuity that
would arise at `n ≤ 1` (`primRhs_of_length_one` shows both sides are `0` there, a *different*,
non-conflicting, already-proved fact, not part of this ticket).

### (T2) `K_step_n`, `Uker_step_n`

**`K_step_n`**: target `‖K_{u'} - K_u - (u'-u)·primRhs(K_u)‖ ≤ errK_n·(u'-u)²`. Route: (i)
`hasDerivAt_Kgen_all` gives `d/dr K_r(I) = primRhs(K_r) I` at *every* `r`, not just `u`; (ii) a
new lemma `norm_primBil_le` (immediate generalization of `norm_primRhs_le`'s proof to two
different envelopes `BF, BG` on two different tensors `F, G`) plus `primRhs_sub` bounds
`‖primRhs(K_r) I - primRhs(K_u) I‖ ≤ D₂·|r-u|` on the window, using the *already-proved*
Lipschitz bound `norm_Kgen_sub_le` for `‖K_r - K_u‖` as the input envelope for the difference
factor (this needs `|r-u| ≤ 1`, true since the whole window is inside `[0,1)`); (iii) apply
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` to `h(r) := K_r(I) - r·primRhs(K_u)(I)`
(constant second term differentiates to `0`) on `Icc u u'`, giving exactly
`‖K_{u'}(I) - K_u(I) - (u'-u)·primRhs(K_u)(I)‖ ≤ D₂·(u'-u)·(u'-u)`. This is the *same* MVT
device already used inside `norm_Kgen_sub_le` itself, applied one derivative-order higher; no
new proof technology, only a new (but structurally identical) helper lemma `norm_primBil_le` and
bookkeeping. **New hypothesis**: an envelope `Bk` on `K_w(J)` for `w` in the window and
`2 ≤ J.length ≤ I.length`, in the *same* shape as `norm_Kgen_sub_le`'s own `hB` — **not a new
hypothesis pattern**, and non-vacuous by `exists_norm_Kval_le_upto` (Step 0). **Verdict: PASS.**

**`Uker_step_n`**: target `‖Uker ξ u (u+Δ) A - A - Δ·ThetaOp ξ u A‖ ≤ errU_n·Δ²·‖A‖_max`, general
`n`, general `ξ : Fin n → ℂ` with `‖ξ_i‖ ≤ 1`. T1506's proof at `n = 2` is an *exact* finite
case analysis (`Fin 2` has exactly `4` subsets of edges). For general `n` this is redone as an
**induction on `n`**, peeling one coordinate at a time via `Fin.cons`/`Fin.consEquiv`
(`(∀ i, α (Fin.succ i)) × α 0 ≃ ∀ i, α i`, already in Mathlib) and `Fin.prod_univ_succ`:

`Uker_{n+1}(ξ,s,t)(A)(Fin.cons a₀ a') = Σ_c edgeKer(ξ₀,s,t)(a₀,c) · Uker_n(ξ',s,t)(A_c)(a')`,
`A_c(w) := A(Fin.cons c w)`, `ξ' := ξ ∘ Fin.succ`, and similarly for `ThetaOp` (using
`Fin.update_cons_zero`, `Fin.cons_update` for the `Function.update` bookkeeping). Writing
`edgeKer(ξ₀,u,u+Δ)(a₀,c) = δ(a₀,c) + Δ·P₀(a₀,c)` (the *same*, `n`-independent, exact identity
`edgeKer_eq` used at `n = 2`) and expanding gives

`Uker_{n+1}(A)(a) - A(a) - Δ·ThetaOp_{n+1}(u)(A)(a)`
`= [Uker_n(A_{a₀})(a') - A_{a₀}(a') - Δ·ThetaOp_n(u)(A_{a₀})(a')]` (the induction hypothesis,
applied to the length-`n` tensor `A_{a₀}`, `‖A_{a₀}‖ ≤ M` since `A_{a₀}(w) = A(Fin.cons a₀ w)`)
`+ Δ·[P₀(a₀,c)-weighted (Uker_n(A_c)(a') - A_c(a'))]` `+ Δ²·[the (P₀ vs Q₀) endpoint-comparison
term]`, the last two exactly as in T1506's `hS2diff`/`hS3diff`/`hRem_bound` but now for a single
edge (index `0`) crossed with the *whole* `n`-tensor at the other end. Bounding the middle term
needs an auxiliary **order-`Δ` bound on `‖Uker_n(F) - F‖`** (not the coarse `O(1)` bound
`norm_Uker_apply_le` already gives) — proved by its *own*, simpler induction on `n` (same
`Fin.cons` peeling, using `norm_Uker_apply_le` — not itself — in its inductive step), giving
`‖Uker_n(F) - F‖_max ≤ ((1+Δβ)^n - 1)·M`, `β := (1-(u+Δ))⁻¹` a common row-sum bound for every
edge kernel (as in T1506). Substituting and simplifying (checked on paper, see below) closes the
induction with

`errU_n := n·β²·M_coeff + [(1+Δβ)^n - 1 - n·Δβ]/Δ²·M_coeff` i.e. the closed bound
`‖Uker_{u,u+Δ}(A) - A - Δ·ThetaOp_u(A)‖_max ≤ [n·Δ²·β² + ((1+Δβ)^n - 1 - n·Δβ)]·M`.

**Consistency check against T1506**: at `n = 2` this reads `2Δ²β²M + ((1+Δβ)²-1-2Δβ)M
= 2Δ²β²M + Δ²β²M = 3Δ²β²M`, which is *exactly* `Uker_step`'s bound
`3·(1-(u+Δ))⁻¹²·Δ²·M` — the general-`n` formula reduces to the accepted `n = 2` result
verbatim. At `n = 1` the "`≥ 2` active edges" part of the induction is vacuous ((1+Δβ)-1-Δβ = 0)
and the bound is `Δ²β²M`, matching a direct one-edge computation (only the `P vs Q`
endpoint-comparison term survives). Algebraic verification of the inductive step (needed:
`Δβ(1-Δ)[(1+Δβ)ⁿ-1] ≥ 0`, which holds since `β ≥ 0` and `Δ < 1` — the latter *forced* by
`hu0 : 0 ≤ u`, `hut1 : u+Δ < 1`, so `Δ = (u+Δ)-u < 1`, no extra hypothesis needed) was done by
hand before writing any Lean; it closes with room to spare (the induction step's target bound is
not tight, only an upper bound, which is all `Uker_step_n` needs).

**No new stochastic/degenerate hypotheses**: `hξ : ∀ i, ‖ξ i‖ ≤ 1` (satisfied by
`xiOf (mSigma E) σ` in the bulk `|E| < 2`, `norm_xiOf`-type fact, `n`-independent), `hu0, hΔ0,
hut1` exactly as at `n = 2`. **Verdict: PASS**, contingent on the `Fin.cons` bookkeeping actually
discharging in Lean without an unexpected sign/index error; this is the highest-risk single
piece of the ticket (pure proof-engineering risk, not a mathematical gap) — see "open issues"
below for the fallback if it proves too costly to finish cleanly (ticket's explicit n = 3
fallback clause).

### (T3) `discrete_hierarchy_step_n`

Route is exactly T1506's (T4) (`condExp_loop_drift` already general, confirmed Step 0) with
(T1)/(T2) above replacing the `n = 2` algebra, plus the `n = 2`-specific deterministic sup bounds
`norm_Kv_le`/`norm_Lval_le`/`norm_xiOf_pm_le` generalized: `norm_Lval_le`'s underlying
`norm_gloop_le_of_le_abs_im` is already stated for arbitrary `I` (used generically inside
`hasDerivAt_gloop_zt_eGterm`'s proof, Step 0), so it generalizes verbatim; `norm_Kv_le` (only
proved at `n = 2` via the closed form `kTwo`) is replaced, for general `n`, by the *same* `Bk`
envelope hypothesis threaded from `K_step_n` (via `exists_norm_Kval_le_upto`, Step 0) rather than
a bespoke closed-form bound — this is the one place the general-`n` statement is *not*
unconditional the way the `n = 2` one is, but the hypothesis is of an *already-accepted* shape
(matching `norm_Kgen_sub_le`/`norm_primRhs_le`) and is witnessed, not vacuous. `norm_xiOf_pm_le`
generalizes verbatim to `∀ i, ‖xiOf (mSigma E) σ i‖ ≤ 1` for any `σ : Fin n → Bool`, `|E| < 2`
(unconditional, no envelope). **Verdict: PASS** (with the same Uker_step_n engineering-risk
caveat as (T2), and with the K-envelope threaded as an explicit, witnessed hypothesis).

## Simultaneous satisfiability witness (general statement, concrete instance)

The three theorems are stated for general `n ≥ 2` (no fixed `n` chosen in the signatures). A
concrete, non-degenerate instantiation showing every hypothesis can hold together at once:
`n = 3`, alternating charge `σ = [true, false, true]`, `E = 0` (bulk, `|E| = 0 < 2`), the same
grid data as T1506's own witness — `s ≡ 1/4, t ≡ 1/2, K ≡ 2, k = 0` (`u₀ = 1/4 < u₁ = 3/8 < 1`),
window `δ = 5/8`; the envelope `Bk` instantiated via `exists_norm_Kval_le_upto B (by norm_num :
|(0:ℝ)| < 2) 3` (nonvacuous, unconditional existence). None of `Δ, u_1 - u_0, δ, L, W` degenerate
to `0`; `n = 3 ≠ 0`; `σ` is a genuine length-`3` list, not the empty/singleton edge case that
would make the `lK = 2` bridge or `ThetaOp` vacuous. This is recorded as a Lean `example` in the
file, mirroring T1506 §8's witness plus the length-`3` loop data.

## Overall preflight verdict

**PASS** for (T1). **PASS** for (T2)/(T3) mathematically, with the single caveat that
`Uker_step_n`'s `Fin.cons`-induction is genuine new proof engineering (not present, even in
sketch, anywhere in the merged codebase) and carries execution risk; if it cannot be closed
cleanly the ticket's own fallback (state general `n`, deliver `n = 3` concretely, report the
obstacle) will be used for `Uker_step_n`/`discrete_hierarchy_step_n` only, while `primRhs_split`
and `K_step_n` are delivered fully general regardless. Proceeding to Lean.

## Outcome: general `n` delivered for every target, no fallback needed

All four targets were closed **for general `n ≥ 2`** (the `n = 3` fallback was not needed).
`RBM1D/Gauss/GridHierarchyN.lean` builds clean (`lake build RBM1D.Gauss.GridHierarchyN`,
`Build completed successfully (3827 jobs)`), no `sorry`/`admit`/`axiom`, `#print axioms` on every
new public declaration lists only `propext, Classical.choice, Quot.sound`.

### Declarations (in file order)

- `couplingLen_eq_zero_outside`, **`primRhs_split`** (T1): pure algebra, general `K, D`, general
  `I.length = n ≥ 2`; splits `primRhs(K+D) − primRhs(K)` into the `l_K = 2` coupling, the
  `Σ_{l_K∈Icc 3 n}` couplings, and `primBil D D`.
- `xiOf_eq_getD_bridge`, `couplingLen_two_Kval_eq_thetaOp`: the general-`n`, general-`σ` literal
  identification `[Kval_u ∼ D]² = ThetaOp`, generalizing T1506's `couplingLen_two_eq_thetaGenLoop`
  use — **no discrepancy found for `n ≥ 3`** (failure-signal check negative).
- `LvalN`, `KvN`: general-length `Lval`/`Kv` (T1506's notation, generalized).
- **`loopDrift_sub_K_deriv_n`** (assembled T1): the general-`n` analogue of T1506's
  `loopDrift_sub_K_deriv`.
- `norm_primBil_le` (new, two-envelope generalization of `norm_primRhs_le`).
- **`K_step_n`** (T2): general-`n` `K_step`, via `hasDerivAt_Kgen_all` + `norm_Kgen_sub_le` +
  `norm_primBil_le` + the mean value theorem (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`,
  applied once more than `norm_Kgen_sub_le` itself). Envelope `Bk` in the shape of
  `norm_Kgen_sub_le`'s own hypothesis (§10b-style, witnessed by `exists_norm_Kval_le_upto` +
  `Band.norm_Kval_le`, both already-accepted, unconditional existence theorems — Step 0 found
  the "K's length-`n` bound" input is **already proved**, not open, contrary to the plan doc's
  concern).
- `sum_loopArg_succ`, `Uker_cons_eq`, `ThetaOp_cons_eq`, `Uker_zero_eq`, `sum_one_apply_mul_eq`,
  `edge_C_bound`, **`norm_Uker_sub_self_le`** (the auxiliary "Lemma A", order-`Δ` bound on
  `Uker − id`, proved by induction on `n`), `ThetaOp_zero_eq`, **`Uker_step_n`** (T2): general-`n`
  `Uker_step`, by induction on `n` peeling one coordinate via `Fin.cons`/`Fin.consEquiv`. Reduces
  *exactly* to T1506's bound `3(1-(u+Δ))⁻²Δ²M` at `n = 2` (checked, both on paper before Lean and
  as a byproduct of the general formula). A concrete, non-degenerate `n = 3` witness is included
  (`example` after `Uker_step_n`).
- `stepErrN` (new `def`, general-`n` deterministic error, explicit and polynomial in `Δ, N, n, Bk`),
  **`discrete_hierarchy_step_n`** (T3): assembled from `condExp_loop_drift` (already general),
  `loopDrift_sub_K_deriv_n`, `K_step_n`, `Uker_step_n`, general `σ : Fin n → Bool` (alternating or
  not), same `Bk` envelope as `K_step_n`.

### Build

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1523 && lake build RBM1D.Gauss.GridHierarchyN
```
→ `Build completed successfully (3827 jobs)`, no errors. `#print axioms` (via a scratch file,
removed after checking) on all 17 new public declarations: every one lists exactly
`[propext, Classical.choice, Quot.sound]`.

### Key lemmas relied on (already-accepted, not reproved)

`primRhs_sub`, `sum_couplingLen`, `couplingLen_two_eq_thetaGenLoop`, `thetaGenLoop_ofFn`,
`thetaGenOp_eq_ThetaOp` (all general `n` already); `ThetaOp`, `Uker`, `norm_Uker_apply_le`,
`edgeKer_eq`, `Theta_sub_Theta`, `Theta_commute_SB`, `norm_Theta_le`, `norm_SB` (Hierarchy/Kernel,
Propagator); `hasDerivAt_Kgen_all`, `norm_Kgen_sub_le`, `norm_primRhs_le`,
`exists_norm_Kval_le_upto` (Loop/TreeRepGeneral, Gauss/Lemma514Holder); `condExp_loop_drift`,
`loopDrift`, `loopDrift_eq` (already general in `I`, confirmed Step 0);
`Fin.consEquiv`, `Fin.cons_update`, `Fin.update_cons_zero`, `Fin.prod_univ_succ`,
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` (Mathlib).

### Open issues / notes for the auditor

1. **`Band` vs `Dims` "same value, different projection" defeq.** `B.L N` and `(B.toDims).L N`
   are `rfl` (`Band.toDims_L`) but not always seen through by `rw`'s discrimination-tree matching;
   several proof steps needed `set I : LoopIdx (ZMod (d.L N)) := …` (matching T1506's own choice)
   and explicit `rfl`/`show`-based bridges rather than `rw` to close. This is proof-engineering
   friction, not a mathematical gap; flagged here in case the auditor wants to sanity-check the
   `linear_combination` calls in `loopDrift_sub_K_deriv_n` and `discrete_hierarchy_step_n`.
2. **The `Bk` envelope.** `K_step_n`/`discrete_hierarchy_step_n` take `Bk` as an explicit
   hypothesis (`∀ w ∈ Icc 0 T, ∀ J, …, ‖B.Kval E N w J‖ ≤ Bk`) rather than deriving a closed form
   inline — this matches the *already-accepted* `norm_Kgen_sub_le`/`norm_primRhs_le` hypothesis
   shape verbatim (not a new pattern), and Step 0 confirmed non-vacuity via
   `exists_norm_Kval_le_upto`/`Band.norm_Kval_le`. A fully worked-out numeric `Bk` (composing
   these with the window's `scale` monotonicity) was not built into a Lean `example` for the full
   `discrete_hierarchy_step_n` (only for the Band-free `Uker_step_n`); this is flagged as
   unfinished polish, not a correctness concern — `exists_norm_Kval_le_upto` alone already proves
   the hypothesis class is non-vacuous.
3. **`Uker_step_n`'s bound is not claimed sharp.** The induction's target bound
   `n·Δ²β² + ((1+Δβ)ⁿ−1−nΔβ)` was verified to reduce to T1506's exact `n=2` constant `3` and to
   close the induction with equality (not merely an inequality) at every step — recorded as a
   by-hand check before Lean, then confirmed by the Lean induction actually closing via `ring`
   with no slack terms needed.
4. **Paper-delta candidates**: none newly identified beyond what T1506/T1516 already recorded
   (the `(5.16)`/`S^(B)` correction, `docs/paper-deltas.md` #106, is reused unchanged here).
