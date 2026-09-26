Auditor model: claude-opus-5-5[1m]

# T1516 audit (re-audit after repair): grid Duhamel expansion of A_k (Z/Y/drift/R split)

Audited: branch `t/T1516` @ edb89af, on top of the previously audited 7cc0dda, whose base is 3ef3996.
- Diff vs merge base: only `RBM1D/Gauss/GridExpansion.lean` (+950), which is the sole writable file.
- Diff 7cc0dda..edb89af: one hunk, inserted after `end Expansion`. It has zero `-` lines, so it is purely additive.
- Fresh audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1516-audit2`, detached at edb89af. It is not the repairer's worktree. It got a CoW copy of the main build cache that had no GridExpansion artifacts, so the module was compiled from scratch.

## Overall verdict: PASS

The previous RETURN (the Z/Y sums had the kernel folded into the label weight) is fixed by the primed successors `grid_expansion'` and `grid_expansion_all'`. In those, the Z and Y sums are `Uker(u_{j+1},u_k)` applied to the k-independent vectors `Zvec (j+1) ω` and `Yvec (j+1) ω`. All four sums now literally have their consumers' input shapes. T0-T4 are byte-for-byte unchanged.

## Gates

| Check | Result |
|---|---|
| Math preflight PASS before Lean | PASS. The original preflight is unchanged. The new "Repair preflight (written before any repair Lean)" (R1-R3) comes before the "Repair: Lean" section, and each item has a verdict and a witness. |
| `lake build RBM1D.Gauss.GridExpansion` (fresh worktree) | PASS: `Build completed successfully (3817 jobs)`; no errors. |
| `lake build RBM1D` (branch root; the import is added at merge) | PASS: `Build completed successfully (9662 jobs)`. |
| `#print axioms` | PASS. Each of the following prints `[propext, Classical.choice, Quot.sound]`: lkFun_eq_Lval_sub_Kv, Uker_eq_sum_ukerMat, ukerMat_nonneg, Φgrid_im_eq_zero, Φgrid_testFun, condExp_A_succ, grid_expansion, grid_expansion_all, gridDelta, stepZ_eq_sum_gridDelta, stepZ_ukerMat_eq_Uker, stepXi_eq_sum_gridDelta_ae, stepY_eq_sum_gridDelta_ae, stepY_ukerMat_eq_Uker_ae, Zvec_succ, Yvec_succ, grid_expansion', grid_expansion_all'. |
| sorry / admit / axiom / opaque / extern / implemented_by | none (grep) |
| Frozen signatures | untouched. T0-T4 are unchanged, and nothing outside the file changed. |
| Name clashes with current `main` (199bf1d) | none. None of the new public names is declared on main. The repairer's `lin_Ab_eq_sum'` is private and distinct from T1505's private `lin_Ab_eq_sum`. |
| Dependencies | All merged. The repair adds only T1505 `Ab`/`lin`/`stepZ`/`stepXi`/`stepY`/`integrable_Phi_H`, `Dims.three_le_L`, and Mathlib `condExp_finsetSum`/`condExp_smul`/`ae_all_iff`, plus this file's own T1/`Φgrid_testFun`/`grid_expansion`. No cycle: `grid_expansion'` is proved from `grid_expansion` and the bridge, and the bridge does not use either expansion. |

## Per target

**(T0), (T1), (T2): PASS, unchanged.** The repair diff is purely additive, so the prior PASS findings stand verbatim. See the previous audit's reasoning: T0 is a definitional identity; T1 is the ticket's `ukerMat` with the harmless `3 ≤ L`, `0≤u≤v<1` on the sum identity; T2 is `discrete_hierarchy_step` with ξ≡1 and R named by subtraction.

**(T3) `grid_expansion`, (T4) `grid_expansion_all`: PASS as intermediate lemmas, unchanged.** Their statements, hypotheses and quantifiers are exactly as audited before. They are still the ticket-named declarations. The consumer-shaped form is delivered by their primed successors below, which have the same hypotheses. This follows CLAUDE.md §3.2: the unprimed statements are not changed, and primed successors are added.

**hReal / hΦ / hC2 / hIntReal: still discharged, not assumed.** This is unchanged from the previous audit.

## Repair declarations

**`stepZ_eq_sum_gridDelta` and `stepZ_ukerMat_eq_Uker` (R1): PASS. This is genuine pointwise linearity, not circular.**
- Definitions: `Ab U b ω = Σ_a (U b a:ℂ) • gradMat (Φ a) (H_j ω)` and `stepZ = √Δ · lin N (Ab …) X`, where `lin N A X = (trace(A X)).re`.
- The private `lin_Ab_eq_sum'` unfolds `lin`/`Ab` and uses `Matrix.sum_mul`, `trace_sum`, `smul_mul`, `trace_smul`, `Complex.re_sum` and `re((r:ℂ)z) = r·re z`. This proves `lin(Ab U b) X = Σ_a U b a · lin(gradMat(Φ a)(H_j)) X` for an arbitrary real `U`.
- The private `stepZ_gridDelta` collapses the sum at `U = δ` with `Finset.sum_eq_single`.
- `stepZ_ukerMat_eq_Uker` then rewrites with T1 `Uker_eq_sum_ukerMat`. Its hypotheses are `0≤v≤w<1`, plus `3 ≤ d.L N` from `Dims.three_le_L`.
- The identity holds for every ω, with no a.e. qualifier and no hidden hypothesis. The statement is exactly the fix item 1 from the previous audit.

**`stepXi_eq_sum_gridDelta_ae`, `stepY_eq_sum_gridDelta_ae` and `stepY_ukerMat_eq_Uker_ae` (R2): PASS.**
- The a.e. identity is derived from conditional-expectation linearity. `condExp_finsetSum` is applied with the per-label integrability `(integrable_Phi_H … (hΦ a)).const_mul (U b a)`; this is T1505's `integrable_Phi_H`, which is exactly the integrability source the ticket's route names. `condExp_smul` is then applied per label.
- The per-label a.e. sets are combined with `ae_all_iff` over the finite label type. The b-quantifier is likewise combined by `ae_all_iff`, so there is one null set for all `b`.
- `stepY` follows from `stepY = stepXi − stepZ` together with R1's pointwise identity.
- The extra hypothesis `hΦ : ∀ a, TestFun d N (Φ a)` is appropriate: without integrability, Mathlib's condExp is 0 and linearity can fail.

**`hΦ` is discharged internally: confirmed.** The private `grid_ZY_bridge_ae` builds `hΦtf := fun a => Φgrid_testFun B hEb N hu1j1 a`.
- It gets `u_{j+1} < 1` from `time_mono` and `time_last` (`u_{j+1} ≤ u_k ≤ u_{K N} = t N < 1`).
- It gets `0 ≤ u_{j+1}` from `time_zero` and `0 ≤ s N`.
- `#check @grid_expansion_all'` shows the hypothesis list `|E|<2, 0≤s N, s N<t N, t N<1, 1≤K N`. This is identical to T4, with no `hΦ`, `TestFun` or integrability hypothesis.

**`Zvec` / `Yvec`: PASS. They are k-independent.** From `#check`: `Zvec, Yvec : (B : Band Ω') → ℝ → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℕ) → (N : ℕ) → ℕ → Ωg B.toDims → LoopArg (B.L N) 2 → ℂ`.
- The arguments are B, E, s, t, K, N, the step index i, ω and the label.
- There is no target-index argument, and the body `stepZ/stepY … (i-1) (Φgrid B E N (time s t K N i)) (gridDelta (B.L N)) a ω` does not mention k.
- `Zvec_succ` and `Yvec_succ` (`rfl`) show that `Zvec (j+1) ω a = stepZ j (Φgrid u_{j+1}) δ a ω`. These are the same T1505 `stepZ`/`stepY` objects, with the same `Φgrid u_{j+1}`.

**(T3′) `grid_expansion'` and (T4′) `grid_expansion_all'`: PASS.**
- Hypotheses: the same as T3/T4.
- Proof: `grid_expansion` is combined with the per-`j` bridge. The a.e. set runs over all `j`, and the case `j ≥ k` is trivial via `ae_all_iff`. Then `Finset.sum_apply`, `Pi.smul_apply` and `Complex.real_smul` are used.
- T4′ quantifier: `∀ᵐ ω, ∀ k ≤ K N, ∀ b, …`. One null set covers all `k ≤ K N` and all labels.
- Boundary case `k=0`: the sums are empty, as in T3.
- Witness (nondegenerate): E=0, s N=0, t N=1/2, K N=2, k∈{0,1,2}.

## Shape table: all four sums vs the consumers on `main` (redone independently)

| T3′/T4′ sum (target index k) | Consumer conclusion (verbatim from main) | Instantiation | Match |
|---|---|---|---|
| Z: `(Σ_{j∈range k} Uker (B.L N) (fun _=>1) (time(j+1):ℂ) (time k:ℂ) (Zvec B E s t K N (j+1) ω)) b` | `stopped_duhamel_azuma_tail` (T1′): `‖(∑ j ∈ range (τ ω), Uker L ξ (u (j+1)) (u (τ ω)) (Z (j+1) ω)) a‖` with `Z : ℕ → Ω' → LoopArg L n → ℂ` | L=B.L N, n=2, ξ=fun _=>1, u=time s t K N, Z=Zvec B E s t K N, k:=τ ω ≤ K N (covered by T4′) | Yes, literal |
| Z (fixed-k variant) | `stopped_duhamel_azuma_tail_fixed` (T1″): `‖(∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j+1)) (u k) (Z (j+1) ω)) a‖`, with one Z for all k | the same Z. On `{k ≤ τ ω}`, `min k (τ ω) = k`, which gives the T4′ sum at index k. Because Zvec is k-independent, the union over k in T1″ is legitimate. | Yes. The only step is rewriting the range bound `min k τ = k`; kernel and times are literal. |
| Y: `(Σ_{j∈range k} Uker … (time(j+1)) (time k) (Yvec B E s t K N (j+1) ω)) b` | `stopped_duhamel_cheb_tail` (T2): `‖(∑ j ∈ range (τ ω), Uker L ξ (u (j+1)) (u (τ ω)) (Y (j+1) ω)) a‖` | Y=Yvec B E s t K N, k:=τ ω | Yes, literal |
| Drift: `(Σ_{j∈range k} step s t K N • Uker … (time(j+1)) (time k) (Dgrid B E s t K N j ω)) b` | `weighted_duhamel_sum_stopped` (T1510): `‖(∑ j ∈ range (min k (τ ω)), Δ • Uker L (fun _=>1) (u (j+1)) (u (min k (τ ω))) (A j)) a‖`, with `Δ : ℝ`, `A : ℕ → LoopArg L 2 → ℂ` | Δ=step s t K N (ℝ), A=fun j => Dgrid B E s t K N j ω, T4′ at index min k (τ ω) ≤ K N | Yes, literal (ℝ-smul on `LoopArg → ℂ` on both sides) |
| R: `(Σ_{j∈range k} Uker … (time(j+1)) (time k) (Rgrid B E s t K N j ω)) b` | `stopped_duhamel_det_bound` (T1504 T3): `‖(∑ j ∈ range (τ ω), Uker L ξ (u (j+1)) (u (τ ω)) (R j ω)) a‖`, with `R : ℕ → Ω' → LoopArg L n → ℂ` | R=Rgrid B E s t K N (type `ℕ → Ωg → LoopArg → ℂ`), k:=τ ω | Yes, literal |

The repairer's shape claims are confirmed for all four sums.

## Advisory notes (not defects; for downstream R4b/R4c)

1. **Adaptedness at `i = 0`.** T1504's `hZ`/`hY` require `∀ i, StronglyMeasurable[ℱ i] (Z i)` for every `i`, including `i = 0`.
   - `Zvec 0 = stepZ 0 (Φgrid u_0) δ` (via `0-1 = 0`) involves `Xmat(ω 1)`, so it is presumably ℱ_1-measurable but not ℱ_0-measurable.
   - Only `Z (j+1)` enters the sums, so downstream can pass `fun i => if i = 0 then 0 else Zvec … i` (and the same for Yvec) without changing any sum.
   - Adaptedness is outside this ticket's targets, as the repairer notes.
2. Downstream must use the same `Φgrid` convention (loopObs − Kv), as noted in the previous audit.
3. The candidate paper-delta entry `T1516a`, which the repairer appended to `docs/paper-deltas.md`, is outside this audit's scope and is ignored.

## Summary

T0, T1, T2, T3, T4 (unchanged) and the repair targets R1, R2, T3′, T4′: PASS. The module and root builds pass in a fresh worktree, the axioms are standard, the diff is confined to the sole writable file, and there are no hidden hypotheses. The Z/Y vectors are k-independent, and all four sums literally match the input shapes of T1504 (T1′/T1″/T2/T3) and T1510.
