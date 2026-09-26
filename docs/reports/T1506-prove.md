Prover model: claude-opus-5-5[1m]

(Repairer stage after audit RETURN. (T1)-(T3) and their preflight below are by the original prover,
claude-sonnet-5, accepted by the audit and unchanged. (T4) is by this repairer.)

# T1506 — GridDriftAlgebra (5.19)/(5.20) discrete drift algebra

## (a) Math preflight (written before any Lean)

Sole writable file: `RBM1D/Gauss/GridDriftAlgebra.lean`. Targets (T1)-(T4) per the ticket.

### (T1) `loopDrift_sub_K_deriv`

Statement checked: for Hermitian `M`, `σ=(+,-)`, `loopDrift E u I M − primRhs(K_u) I` splits into
`ThetaOp`-part + `eGterm`-part + `primBil(D,D)`-part, `D := gloop(...) − K_u`.

- `loopDrift E u I M = eGterm(...) I + primRhs(gloop(...)) I` (`RBM.Gauss.Grid.loopDrift_eq`, T1487,
  merged) — dependency accepted.
- `primRhs_sub` (`Hierarchy/Dynamics.lean:69`, accepted, no hypotheses beyond `NeZero L`) gives
  `primRhs(gloop) I − primRhs(K_u) I = primBil(K_u,D) I + primBil(D,K_u) I + primBil(D,D) I`.
- At `I.length = 2` (our `σ=(+,-)` 2-loop), `primBil(K_u,D) I + primBil(D,K_u) I` is the *whole*
  `l_K`-coupling `Decay.couplingLen L W 2 K_u D I` (`RBM.EGDef.couplingLen_two_of_len_two`, already
  in the repo, no new hypothesis). By (5.19) (`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`, already a
  theorem, accepted) that coupling equals `thetaGenLoop (mSigma E) u D I`, under hypotheses
  `hK` (K_u agrees with `kTwo` at length 2 — an identity, `Band.Kval`/`Kgen_two`, always true), `I.WF`
  (rfl for our concrete `I`), `2 ≤ I.length` (`rfl`, `=2`), and `‖u·ξ(I.length−1)‖<1` i.e.
  `‖u·(mSigma E false * mSigma E true)‖<1` — this is a genuine, satisfiable side hypothesis
  (nonvacuous for `u∈[0,1)` since `|mSigma E s|≤1` typically, and even at `|mSigma E s|=1` any
  `u<1` works), added to the statement as `hxi2`.
- `thetaGenLoop_ofFn` + `thetaGenOp_eq_ThetaOp` (both already theorems in `Gauss/LoopIto.lean`, the
  latter literally `rfl`) rewrite `thetaGenLoop (mSigma E) u D I` as
  `ThetaOp L (xiOf (mSigma E) ![true,false]) u (fun v => D⟨σ,ofFn v⟩) a`, matching the `LoopArg`
  representation the ticket asks for.
- Quantifier order: `∀ B,E,N,u,M` (Hermitian, `z`-nondegenerate) `→ (identity)`; matches paper order,
  no `∀ᶠ N` needed (this is a pointwise algebraic identity, not asymptotic).
- Dependencies used (`primRhs_sub`, `loopDrift_eq`, `couplingLen_two_of_len_two`,
  `couplingLen_two_eq_thetaGenLoop`, `thetaGenLoop_ofFn`, `thetaGenOp_eq_ThetaOp`, `Kgen_two`) are all
  already-accepted (merged / already in the checked-out tree) theorems, not new axioms.
- Boundary cases: `u=0` is fine (`hxi2` reduces to `0<1`, always true); no divide-by-zero; `E` is a
  free real parameter, nothing forces it into a degenerate range.
- Witness for simultaneous satisfiability: `E:=0`, `u:=0`, `M:=0` gives `mSigma 0 s = ±i` (unit
  circle), `hxi2` becomes `‖0‖<1` (true), `(zt 0 0).im = Im(mE 0) ≠ 0` typically true (semicircle at
  `E=0` has nonzero imaginary part) — nonvacuous, not an "astronomically large parameter" trick.

**Verdict (T1): PASS.**

### (T2) `K_step`

`‖K_{u'} − K_u − (u'−u)·primRhs(K_u)‖ ≤ errK·(u'−u)²`. At length-2, `K_v⟨σ,(a,b)⟩ = kTwo(...) v
= W⁻¹μ·Theta(vμ)(a,b)` with `μ:=m(σ₁)m(σ₂)` **independent of `v`**. Using the *exact* resolvent
identity `Theta_sub_Theta` (`Propagator/Deriv.lean:51`, already a theorem, no new axiom) **twice**
gives an *exact* closed form (not just a bound):
`K_{u'} I − K_u I − (u'−u)·primRhs(K_u) I = (u'−u)²·μ³/W·(Theta(u'μ)·SB·Theta(uμ)·SB·Theta(uμ))(a,b)`,
whence `errK` is explicit via `norm_Theta_le` (`Propagator/Bounds.lean:49`) and an entry-le-row-sum
step (`Finset.single_le_sum` on `sum_norm_row_le`, `Hierarchy/Kernel.lean:86`). Hypothesis needed:
`‖u'·μ‖<1` (matches `hasDerivAt_Kval_two`'s own hypothesis style, T1487/EGDef precedent); together
with `0≤u≤u'` this *also* gives `‖u·μ‖<1` (real-scalar monotonicity of `‖·‖` on `u,u'≥0`), so no
second hypothesis is needed. Nonvacuous: `u=u'=0` gives `‖0‖<1`, always satisfiable; `u<u'<1`,
`μ` any unit-circle value, is the generic case used throughout the repo (`mSigma`).

**Verdict (T2): PASS.**

### (T3) `Uker_step`

Restricted to `n=2` (the ticket's own scope: "`L_u(M)` is the vector of 2-loops"; T1's target and
T4's vector `A_j` are both 2-loops, so `Uker`/`ThetaOp` are only ever needed at `n=2` here — this is
recorded as the scope, not a weakening of a stated general-`n` claim: the ticket's own T1/T4 never
require `n≠2`). Plan: split the `Fin 2 → ZMod L` sum into a double sum (`piFinTwoEquiv` +
`Fintype.sum_prod_type`, standard, used identically for `ℝ` in `Hierarchy/KernelDecay.lean:1746-1749`
— reused here for `ℂ`), then use the *exact* identity `edgeKer_eq` (`Hierarchy/Kernel.lean:107`,
already a theorem) entrywise to expand each of the two edge factors as `δ + Δ·(edge kernel at the
endpoint u_{j+1})`, giving an *exact* quadratic remainder (only one term survives at `n=2`, no
approximation). The ticket's stated base point for the linear term is `u_j` (not the endpoint
`u_{j+1}` that `edgeKer_eq` naturally produces); moving the base point costs one more *exact*
application of `Theta_sub_Theta`, contributing an extra exact `Δ²`-order term. Both remainder pieces
are bounded via `norm_Theta_le`/`norm_SB`/submultiplicativity, using `‖ξ_i‖≤1`, `0≤u`, `u+Δ<1`
(nonvacuous: e.g. `ξ=1`, `u=0`, `Δ<1`, matches the paper's `σ=(+,-)` case `xiOf (mSigma E)`). No new
axiom; `errU` fully explicit (`3·(1−(u+Δ))⁻²`, see report §b for the exact constant obtained).

**Verdict (T3): PASS.**

### (T4) `discrete_hierarchy_step` — repair stage (written 2026-09-26 00:34 UTC, before any T4 Lean)

This section replaces the original prover's BLOCKED (T4) preflight. It addresses the three
counter-findings of `docs/reports/T1506-audit.md` (RETURN, 00:14 UTC):

- **T1503 is merged.** `RBM.Gauss.Grid.condExp_loop_drift` (`Gauss/GridLoopStep.lean:892`, main
  commit 2b49f8f, audit PASS) has been merged locally into `t/T1506` (merge of `main` at b74a55e).
  It is used directly, so no `hstep` hypothesis is needed.
- **Integrability is not a missing input.** `Φ_{u_{k+1}} ∘ H_{k+1}` is measurable
  (`H_measurable_filt` + `(filt d).le`, then the continuity of `loopObs` from
  `testFun_loopObs_of_im_le`) and bounded (`TestFun.bdd₀`). So it is integrable, following exactly
  `condExp_loop_step`'s `hIntTarget` (`GridLoopStep.lean:321-325`). That helper is `private`, so its
  two lines (`memLp_top_of_bound … |>.integrable`) are reproduced here. The only input used is
  `(zt E u_{k+1}).im ≠ 0`, which follows from `|E| < 2` and `u_{k+1} < 1` (`zt_im_ne_zero_of_lt_one`).
- **The sup bound on `A_k` is deterministic.** For every `ω` and every label `b`:
  `‖A_k(b)‖ ≤ ‖gloop(H_k ω)(z_{u_k})⟨+-,b⟩‖ + ‖K_{u_k}(b)‖ ≤ |Im z_{u_k}|⁻² W⁻¹ + W⁻¹(1 − u_k)⁻¹ =: M_k`.
  The first term uses `norm_gloop_le_of_le_abs_im` (the lemma behind `norm_loopObs_le`) with
  `H_isHermitian`. The second uses `K_u(b) = W⁻¹ μ Θ(uμ)(b₀,b₁)` with `‖μ‖ = 1` (`norm_mSigma`,
  `|E| ≤ 2`), entry ≤ `ℓ^∞` operator norm, and `norm_Theta_le`.

**Statement (Lean form).** Let `B : Band Ω` and `d := B.toDims`. Take the grid `s t K`, `N k`,
`E`, and write `u_k = time s t K N k`, `Δ = step s t K N`, `A_k(ω) := fun v => Lval B E N u_k (H_k ω) v − Kv B E N u_k v`
on `LoopArg (B.L N) 2`, `ξ := xiOf (mSigma E) ![true,false]`. Hypotheses: `|E| < 2`,
`s N < t N`, `k < K N`, `0 ≤ u_k`, `u_{k+1} < 1`. These are exactly `condExp_loop_drift`'s
hypotheses minus `hzk, hzk1` (derived) and `hwf, hn` (automatic for the 2-loop). Conclusion:
`∀ᵐ ω ∂ Pg d, ∀ a, ‖(Pg d)[fun ω' => A_{k+1}(ω') a | filt d k] ω − Uker (B.L N) ξ u_k u_{k+1} (A_k ω) a
 − Δ·(eGterm … (H_k ω) (zt E u_k) ⟨+-,a⟩ + primBil (gloop−K_{u_k}) (gloop−K_{u_k}) ⟨+-,a⟩)‖ ≤ errStep'`.
Here `errStep' = e₁ + W⁻¹(1−u_{k+1})⁻¹(1−u_k)⁻²Δ² + 3(1−u_{k+1})⁻²Δ²·M_k`, and `e₁` is
`condExp_loop_drift`'s explicit right-hand side at `I.σ.length = 2`:
`zMotionZLip(…,(1−u_{k+1})Im m)·|m|·Δ²/2 + (zMotionLip(…,|Im z_{u_k}|) + ⅔ genPtLip(…,|Im z_{u_k}|))·Δ^{3/2}·∫‖X‖`.
This is the ticket's `E[A_{j+1}|F_j] − U(A_j) = Δ(EG + quad)(H_j) + R_j`, with `‖R_j‖_∞ ≤ errStep'`.
The sup norm over labels is the `∀ a` bound. The Θ-part is not visible in the statement because it
is absorbed exactly into `Uker`. That is the point of (T1) and (T3).

**Derivation (sign-checked).** Fix `ω` in the a.e. set of `condExp_loop_drift` (intersected over the
finitely many labels, `ae_all_iff`) and fix `a`. Set `I = ⟨[+,−], ofFn a⟩`, `L_k := gloop(H_kω)(z_{u_k})I = A_k(a) + K_k(a)`.
1. `A_{k+1}(ω')(a) = loopObs(z_{u_{k+1}}) I (H_{k+1}ω') − K_{k+1}(a)`, because `H_{k+1}ω'` is
   Hermitian (`loopObs_of_isHermitian`). By `condExp_sub` (integrability above plus a constant) and
   `condExp_const`: `E[A_{k+1}(a)|F_k] =ᵐ c − K_{k+1}(a)` with `c := E[Φ_{k+1}∘H_{k+1}|F_k]`.
2. T1503: `e₁' := c − L_k − Δ·loopDrift(u_k,I,H_kω)` has `‖e₁'‖ ≤ e₁` a.e.
3. (T1) at `M = H_kω`, `u = u_k` (`hxi2`: `u_k·|μ| = u_k < 1`):
   `loopDrift = primRhs(K_k)I + Θ_{u_k}(A_k)(a) + EG + quad`.
4. (T2) with `(s1,s2) = (+,−)`, `u = u_k`, `u' = u_{k+1}`, so `u'−u = Δ`:
   `e₂ := K_{k+1}(a) − K_k(a) − Δ·primRhs(K_k)I`, with `‖e₂‖ ≤ W⁻¹(1−u_{k+1})⁻¹(1−u_k)⁻²Δ²`.
5. (T3) with `A = A_k(ω)`, `M = M_k`, `u = u_k`, `u+Δ = u_{k+1}`, `‖ξ_i‖ = 1`:
   `e₃ := Uker(A_k)(a) − A_k(a) − Δ·Θ_{u_k}(A_k)(a)`, with `‖e₃‖ ≤ 3(1−u_{k+1})⁻²Δ²M_k`.
6. `Q := (c − K_{k+1}) − Uker(A_k)(a) − Δ(EG+quad)`. Substituting 2–5:
   `Q = e₁' − e₂ − e₃ + [L_k − K_k − A_k(a)] + Δ[loopDrift − primRhs(K_k) − Θ(A_k) − EG − quad] = e₁' − e₂ − e₃`.
   Both brackets vanish, the first by definition and the second by (T1). Hence `‖Q‖ ≤ errStep'`.

**Order and uniformity in `j`.** `Δ > 0` follows from `s < t`, `k < K`. `e₁ = O(Δ²) + O(Δ^{3/2})`, and the
other two terms are `O(Δ²)`, so `R_j = O(Δ^{3/2})`. For uniformity, assume `u_{k+1} ≤ 1 − δ` with
`δ > 0`. Then `(1−u_k)⁻¹, (1−u_{k+1})⁻¹ ≤ δ⁻¹`, and `|Im z_{u_k}|, (1−u_{k+1}) Im m ≥ η_δ := δ·Im m^{(E)} > 0`.
`zMotionLip`, `zMotionZLip`, `genPtLip` (= `driftLip + zMotionLip`) are monotone non-increasing in
`η` (products of non-negative factors with `η⁻¹` in numerators). So
`errStep' ≤ C₁(δ)Δ² + C₂(δ)Δ^{3/2}`, where `C₁, C₂` depend only on `(L, W, E, δ, ∫‖X‖)` and not on
`k`. A second theorem `discrete_hierarchy_step_unif` states this with explicit `C₁, C₂`.

**Hypotheses and witness.** No hypothesis is added beyond `condExp_loop_drift`'s, and two of those
(`hzk`, `hzk1`) are removed as derivable. The grid hypotheses do not involve `B`. They are
satisfied non-degenerately by `s ≡ 1/4`, `t ≡ 1/2`, `K ≡ 2`, `N = k = 0`, `E = 0`, which gives
`Δ = 1/8` and `u_0 = 1/4`, `u_1 = 3/8 < 1`. This is T1503 §8's witness, re-compiled here as an
`example`. For `_unif`, `δ = 5/8` also satisfies `u_1 ≤ 1 − δ`. There is no `N = 0`-vacuity: `N`
is a free parameter, the statement holds for every `N`, and the witness instantiates `N = 0` only
because the grid hypotheses are independent of `N`. No empty index set occurs (`LoopArg (B.L N) 2`
is nonempty, `L ≥ 3`) and no window collapses (`Δ > 0`).

**Boundary cases.** `u_k = 0` is allowed. `u_{k+1} → 1` makes the constants blow up, as in the
paper, where the stopped hierarchy is run on `u ≤ 1 − δ`. `E` is restricted to `|E| < 2`, the
bulk, as in T1503.

**Dependencies (all accepted/merged):** `condExp_loop_drift` (T1503), `loopDrift_sub_K_deriv`,
`K_step`, `Uker_step` (T1506 (T1)-(T3), audit PASS), `norm_gloop_le_of_le_abs_im`,
`norm_Theta_le`, `norm_mSigma`, `zt_im`, `mE_im_pos`, `zt_im_ne_zero_of_lt_one`, `H_isHermitian`,
`H_measurable_filt`, `testFun_loopObs_of_im_le`, `loopObs_of_isHermitian`, and Mathlib
`condExp_sub`, `condExp_const`, `ae_all_iff`. There is no cycle: nothing imported depends on this
file.

**Norm-scope note.** This file opens `Matrix.Norms.Operator` (`ℓ^∞` operator norm, used by
`norm_Theta_le`), but `condExp_loop_drift`'s `∫‖Xmat‖` uses `Matrix.Norms.L2Operator`. (T4) is
therefore stated in a separate namespace block that opens only `L2Operator`, so the constant is
literally T1503's. The Θ-bounds are proved beforehand in the `Operator` block as scalar statements.

**Verdict (T4): PASS.**

Step 0 checks done: `primRhs`, `primBil`, `primRhs_sub`, `hasDerivAt_Kval_two`, `ThetaOp`,
`edgeKer_eq`, `loopDrift_eq`, `F_eq_eGpm_add_quadGlue` all read; (5.19) already exists as
`RBM.Gauss.couplingLen_two_eq_thetaGenLoop` (`Gauss/LoopIto.lean:1548`), confirmed via
`thetaGenOp_eq_ThetaOp` (`rfl`) that it is literally about `RBM.ThetaOp`.

## (b) Declarations, file, build

File: `RBM1D/Gauss/GridDriftAlgebra.lean`, the sole writable file, in worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1506`, branch `t/T1506`.

Branch history:
- `fc4d6a4` is the original (T1)-(T3).
- `dc1d19f` merges local `main` (b74a55e) into `t/T1506`. The merge only brings in main's files,
  and there were no conflicts.
- `b57d39d` is (T4), this repair.

`git diff --stat main...t/T1506` shows only `RBM1D/Gauss/GridDriftAlgebra.lean`. The new import is
`RBM1D.Gauss.GridLoopStep`. (T1)-(T3) (lines 1-681 of the previous version) are unchanged apart
from the module docstring's (T4) bullet.

Declarations (unchanged from the accepted stage):
- `Lval` and `Kv` (notation).
- `loopDrift_sub_K_deriv` **(T1)**, line 65.
- `K_step` **(T2)**, line 159.
- `Uker_step` **(T3)**, line 325.
- The private helpers `theta_SB_theta_entry`, `sum_LoopArg_two`, `row_bound_edge`.

New declarations (T4 stage). Section `T4Aux` (`ℓ^∞` operator-norm scope):
- `ofFn_two'` (692): `List.ofFn a = [a 0, a 1]` on `Fin 2`.
- `norm_Kv_le` (696): `‖K_u(b)‖ ≤ W⁻¹(1-u)⁻¹` for `|E| < 2` and `0 ≤ u < 1`.
- `norm_Lval_le` (720): `‖L_u(M)(b)‖ ≤ η⁻² W⁻¹` for Hermitian `M` and `η ≤ |Im z_u|`.
- `norm_xiOf_pm_le` (729): `‖xiOf (mSigma E) ![+,-] i‖ ≤ 1`.
- `zMotionLip_anti`, `zMotionZLip_anti`, `genPtLip_anti` (735-751): T1503's constants are
  non-increasing in `η`.

Section `T4` (a separate `namespace` block opening only `Matrix.Norms.L2Operator`, so that
`∫ ‖Xmat‖` is literally T1503's constant):
- `stepErr B E N u_k u_{k+1} Δ` (779) is the explicit `errStep'`:
  `condExp_loop_drift`'s right-hand side at a 2-loop, plus `W⁻¹(1-u_{k+1})⁻¹(1-u_k)⁻²Δ²`, plus
  `3(1-u_{k+1})⁻²Δ²·(|Im z_{u_k}|⁻²W⁻¹ + W⁻¹(1-u_k)⁻¹)`.
- **`discrete_hierarchy_step` (T4)** (795). Hypotheses: `|E| < 2`, `s N < t N`, `k < K N`,
  `0 ≤ u_k`, `u_{k+1} < 1`. The conclusion is:
  ```
  ∀ᵐ ω ∂ Pg B.toDims, ∀ a : LoopArg (B.L N) 2,
    ‖(Pg B.toDims)[fun ω' => Lval B E N u_{k+1} (H … (k+1) ω') a − Kv B E N u_{k+1} a | filt B.toDims k] ω
      − Uker (B.L N) (xiOf (mSigma E) ![true,false]) u_k u_{k+1} (fun v => Lval B E N u_k (H … k ω) v − Kv B E N u_k v) a
      − Δ * (eGterm … (H … k ω) (zt E u_k) ⟨[+,−],ofFn a⟩
             + primBil (gloop … (H … k ω) (zt E u_k) − B.Kval E N u_k) (same) ⟨[+,−],ofFn a⟩)‖
    ≤ stepErr B E N u_k u_{k+1} Δ
  ```
- `stepErrC1`, `stepErrC2` (966, 973) are the `k`-independent coefficients, with
  `η_δ = δ·Im m^{(E)}`.
- `stepErr_le_unif` (980): for `u_k ≤ u_{k+1} ≤ 1-δ`, `0 < δ` and `0 ≤ Δ`,
  `stepErr ≤ C₁(δ)Δ² + C₂(δ)Δ^{3/2}`.
- **`discrete_hierarchy_step_unif`** (1037): (T4) with the right-hand side
  `C₁(δ)Δ² + C₂(δ)Δ^{3/2}`, under `0 < δ` and `u_{k+1} ≤ 1-δ` (which replaces `u_{k+1} < 1`).
  This makes "`R_j = o(Δ)` uniformly in `j`" a compiled statement.
- `example` (1073) is the satisfiability witness. It is compiled and has no `sorry`. It takes
  `s ≡ 1/4`, `t ≡ 1/2`, `K ≡ 2`, `N = k = 0`, `E = 0`, `δ = 5/8`, and checks all hypotheses of both
  theorems together with `0 < step`.

Builds (in the worktree):
- `lake build RBM1D.Gauss.GridDriftAlgebra` gives `Build completed successfully (3813 jobs)`.
  The only warnings are linter warnings: the pre-existing (T1)-(T3) `show`/unused-variable/`first`
  ones.
- `lake build RBM1D` gives `Build completed successfully (9657 jobs)`, with root axiom audit
  "20833 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]". The root does
  not import this module yet; that happens at merge.
- A scratch file importing both `RBM1D` and `RBM1D.Gauss.GridDriftAlgebra` elaborates, so there is
  no name clash with the root.
- `grep sorry|admit|^axiom` finds nothing.

`#print axioms` (scratch file outside the tree, `lake env lean`):
```
discrete_hierarchy_step        [propext, Classical.choice, Quot.sound]
discrete_hierarchy_step_unif   [propext, Classical.choice, Quot.sound]
stepErr_le_unif                [propext, Classical.choice, Quot.sound]
norm_Kv_le / norm_Lval_le / norm_xiOf_pm_le       [propext, Classical.choice, Quot.sound]
zMotionLip_anti / zMotionZLip_anti / genPtLip_anti [propext, Classical.choice, Quot.sound]
stepErr                        [propext, Classical.choice, Quot.sound]
ofFn_two'                      [propext, Quot.sound]
loopDrift_sub_K_deriv / K_step / Uker_step        [propext, Classical.choice, Quot.sound]
```

## (c) Key lemmas used

- (T1)-(T3): as in the original report: `primRhs_sub`, `couplingLen_two_of_len_two`,
  `couplingLen_two_eq_thetaGenLoop` (5.19), `thetaGenLoop_ofFn`, `thetaGenOp_eq_ThetaOp`,
  `loopDrift_eq`, `Kgen_two`, `Theta_sub_Theta`, `Theta_commute_SB`, `norm_Theta_le`, `norm_SB`,
  `sum_norm_row_le`, `edgeKer_eq` (5.18), `Uker_apply`.
- (T4):
  - T1503 `RBM.Gauss.Grid.condExp_loop_drift`, used directly.
  - Integrability follows `condExp_loop_step`'s `hIntTarget`: `testFun_loopObs_of_im_le`,
    `TestFun.bdd₀`, `H_measurable_filt`, `(filt d).le`, `memLp_top_of_bound`.
  - Mathlib `condExp_sub`, `condExp_const`, `ae_all_iff`.
  - `loopObs_of_isHermitian`, `H_isHermitian`.
  - `norm_gloop_le_of_le_abs_im` (the bound behind `norm_loopObs_le`), `norm_Theta_le`,
    `norm_mSigma`, `zt_im`, `mE_im_pos`, `zt_im_ne_zero_of_lt_one`.
  - (T1), (T2), (T3) of this file.

  The final identity is `linear_combination Δ * (T1)`, which gives `Q = e₁ − e₂ − e₃` exactly.

## (d) Open issues

1. The audit's three counter-findings were all confirmed. T1503 is merged and used directly.
   Integrability is derived and is not a hypothesis. The sup bound `M_k` is deterministic. No
   `hstep` and no extra hypothesis were added. The hypothesis list is `condExp_loop_drift`'s minus
   `hzk`/`hzk1` (derived from `|E| < 2`, `u_{k+1} < 1`) and minus `hwf`/`hn` (automatic for the
   2-loop).
2. Scope. The result is the `σ = (+,-)` 2-loop, `|E| < 2`, one grid step, on the grid model
   `Pg`/`H` of T1481/T1503, which is the setting the ticket specifies. It is the discrete bridge
   the ticket asks for, not the paper's continuous-time Brownian statement (CLAUDE.md §3.5). There
   is no special `Dims` (arbitrary `B : Band`), no fixed `D`, and no `E = 0` restriction. The
   dispatcher may want a `docs/paper-deltas.md` entry noting that (5.19)/(5.20) are realized on the
   grid, with the error `O(Δ^{3/2})`. This file is outside my writable scope, so none was appended.
3. `stepErr` contains `∫ ‖Xmat d N‖ dP` (L² operator norm). This is a finite deterministic
   constant, depending on `N`, inherited verbatim from T1503. Its `N`-growth is T1503's concern and
   is not addressed here.
4. (T1)-(T3) scope notes from the original report still apply: (T3) is `n = 2`, and (T1) keeps the
   unused `hM`, `hz`.
