Auditor model: claude-opus-5-5

# T1523 audit: general-n grid hierarchy step

Branch `t/T1523` @ `2254d8b`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1523`.
`git diff main...t/T1523 --name-only`: only `RBM1D/Gauss/GridHierarchyN.lean`, a new file of 1235 lines. That is the ticket's sole writable file. No frozen signature is touched and no existing file is edited.

## Overall verdict: PASS (T1, T2, T3)

## Gates

| Check | Result |
|---|---|
| Math preflight PASS written before the Lean | yes, `T1523-prove.md` §"math preflight (written before any Lean)"; the outcome section is appended after it |
| `lake build RBM1D.Gauss.GridHierarchyN` (audit worktree) | success (3827 jobs); lint warnings only (`show`, deprecated `if_neg`/`push_neg`, line length, unused `hM`/`hz` in `loopDrift_sub_K_deriv_n`) |
| `lake build RBM1D` (audit worktree; the root does not import the module yet) | `Build completed successfully (9668 jobs)` |
| Root-adjacent check: a scratch file importing both `RBM1D` and `RBM1D.Gauss.GridHierarchyN` | compiles, so there are no name clashes when the import is added at merge |
| `sorry`/`admit`/`axiom`/`native_decide`/`set_option` in the file | none |
| `#print axioms` on all 18 public declarations (17 theorems plus `stepErrN`) | each lists only `[propext, Classical.choice, Quot.sound]` |
| Dependencies | only merged code: `GridDriftAlgebra` (T1506), `Lemma514Holder`, `LoopIto.couplingLen_two_eq_thetaGenLoop`/`thetaGenLoop_ofFn`/`thetaGenOp_eq_ThetaOp`, `GridLoopStep.condExp_loop_drift`, `Hierarchy.Dynamics`/`Decay`/`Kernel`, `TreeRepGeneral.hasDerivAt_Kgen_all`. Nothing imports the new file, so there is no cycle. |

## (T1) `primRhs_split` and `couplingLen_two_Kval_eq_thetaOp` — PASS

- **Statement.** For all `L, W, K, D` and every `I` with `2 ≤ I.length`:
  `primRhs(K+D) I − primRhs K I = couplingLen 2 K D I + Σ_{lK ∈ Icc 3 I.length} couplingLen lK K D I + primBil D D I`.
  - `couplingLen lK = primBilLen lK K D + primBilLenR lK D K`. These are both orientations of (5.14), with the `K` piece of length `lK`.
  - Together with `primRhs_sub` ((5.12)/(5.13)) and `sum_couplingLen`, this is exactly the ticket's (T1) display.
  - The index range `Icc 3 n` is exact: `couplingLen_eq_zero_outside` shows the vanishing for `lK < 2` and for `lK > n`.
  - The only hypothesis is `2 ≤ I.length`. There are no hidden hypotheses on `K` or `D`.
- **`[K∼D]^2 = ThetaOp` is literal for n ≥ 3 (checked).** `couplingLen_two_Kval_eq_thetaOp` concludes, for every `n ≥ 2` and every `σ : Fin n → Bool`:
  `couplingLen 2 (Kval_u) D ⟨ofFn σ, ofFn a⟩ = ThetaOp (B.L N) (xiOf (mSigma E) σ) u (fun v => D ⟨ofFn σ, ofFn v⟩) a`.
  - The right-hand side is the Kernel.lean `ThetaOp` itself. It includes the `S^(B)` correction, paper-delta #106, which predates this ticket.
  - `xiOf m σ i = m(σ i)·m(σ(i+1))` uses `Fin n` addition, so the edge is cyclic (`m_n m_1`), matching Definition 5.2 and (2.57).
  - The bridge `xiOf_eq_getD_bridge` identifies `thetaGenLoop`'s `getD ((i+1) % n)` coefficient with `xiOf` for every `i`. It uses no `n = 2` special casing.
  - There is no orientation discrepancy, so the ticket's failure signal is negative.
  - The side hypothesis `‖u·xiLoop(n−1)‖ < 1` holds automatically for `0 ≤ u < 1`, `|E| < 2`, because `‖mSigma‖ = 1`.
- **`loopDrift_sub_K_deriv_n`** assembles T1 into the ticket's drift split:
  `loopDrift − primRhs(K_u) = ThetaOp_σ(A) + Σ_{lK≥3}[K∼A]^{lK} + eGterm + primBil(A,A)`, with `A = gloop − Kval`.
  The unused `hM`/`hz` are extra, satisfiable hypotheses. They are harmless.

## (T2) `K_step_n`, `Uker_step_n` — PASS

- **`K_step_n`.**
  - It holds for general `Kgen L W m` with `‖m s‖ ≤ 1`, every `I` with `WF` and `2 ≤ I.length`, and `u ≤ u'` in `[0,T]`, `T < 1`. This is a strict generalisation of `Kval`.
  - Bound: `(2·c·Bk·D1 + c·D1²)·(u'−u)²`, where `c = W n² L` and `D1 = c·Bk²`. The constant is explicit and polynomial in `W, L, n, Bk`.
  - New hypothesis: the envelope `hBk : ∀ w ∈ [0,T], ∀ J WF, 2 ≤ |J| ≤ |I| → ‖Kgen w J‖ ≤ Bk`. It has the same shape as the accepted `norm_Kgen_sub_le` and `norm_primRhs_le`.
  - The hypothesis is satisfiable. The auditor compiled `exists_Bk` (below) from the accepted `exists_norm_Kval_le_upto`, `one_le_ellHat` and `mE_im_pos`: `Bk = C·max(1, ((1−T)·Im m)⁻¹)^n` is finite.
- **`Uker_step_n`.**
  - It holds for every `n`, every `ξ` with `‖ξ_i‖ ≤ 1`, and `0 ≤ u`, `0 ≤ Δ`, `u+Δ < 1`, `‖A‖_max ≤ M`.
  - Bound: `[n·Δ²β² + ((1+Δβ)^n − 1 − nΔβ)]·M`, with `β = (1−(u+Δ))⁻¹`. The proof is a genuine induction on `n` via `Fin.cons`.
  - The bound is O(Δ²) and explicit, because `(1+x)^n − 1 − nx ≤ C(n,2)·x²·(1+x)^{n−2}`.
  - It is not written as a literal `errU_n·Δ²·M` factorisation, but it is equivalent. It reduces exactly to T1506's `3β²Δ²M` at `n = 2`.
  - Hypotheses are trivially satisfiable (for example `ξ ≡ 1/2`, `u = 1/4`, `Δ = 1/8`).
  - Weakness: the in-file `example` only asserts that numbers satisfying the hypotheses exist. It never invokes the theorem.

## (T3) `discrete_hierarchy_step_n` — PASS

- **Statement.** For every `n ≥ 2`, every `σ : Fin n → Bool` (alternating or not), every grid step `k < K N`, and a.e. `ω`, for all `a`:
  `‖E[A_{k+1} | F_k] − Uker(ξ_σ, u_k, u_{k+1}) A_k − Δ·(eGterm + Σ_{lK∈Icc 3 n}[K∼A]^{lK} + primBil(A,A))(H_k)‖ ≤ stepErrN`.
  - This is the ticket's (T3), with `A_j = LvalN − KvN` at `(u_j, H_j)`.
  - The quantifier order is correct: the fixed data `B, s, t, K, N, k, E, n, σ, Bk` come first, then `∀ᵐ ω`, then `∀ a`. There is no `∀ᶠ N` at this level.
- **(T3) holds for every σ (checked).** `σ` is an arbitrary `Fin n → Bool`, and every ingredient is σ-generic:
  - `xiOf` is bounded by 1 for any σ (proved inline);
  - `condExp_loop_drift` is general in `I`;
  - `couplingLen_two_Kval_eq_thetaOp` holds for any σ.
  The auditor's witness below uses a non-alternating σ.
- **`stepErrN` is explicit and polynomial (checked).** It is a closed-form `def` with no existential:
  - the T1503 remainder `zMotionZLip·‖m‖·Δ²/2 + (zMotionLip + (2/3)·genPtLip)·Δ^{3/2}·∫‖X‖` (same as T1506);
  - plus the `K_step_n` constant times `Δ²`;
  - plus the `Uker_step_n` factor times `M_k = |Im z_{u_k}|^{−n}·W^{−(n−1)} + Bk`.
  So `stepErrN = O(Δ^{3/2} + Δ²)·poly(W, L, n, Bk, |Im z|⁻¹, (1−u_{k+1})⁻¹)`.
- **Difference from the n = 2 T1506 result (not a defect, recorded).** Two hypotheses are added:
  - `hBk`: the Kval envelope on `[0, u_{k+1}]`, lengths `2..n`. It replaces T1506's closed-form `norm_Kv_le`, which exists only at `n = 2`. It is satisfiable (`exists_Bk`). `Bk` is a free parameter, so downstream sharp use must instantiate it with the paper's `K` bound, `‖K‖ ≲ (Wℓη)^{-(|J|-1)}` via `exists_norm_Kval_le_upto`. As stated, the theorem loses nothing for any choice of `Bk`.
  - `hξ`: this is redundant. It follows from `hu0`, `hu1` and `|E| < 2`, as the witness discharges it.
- **Vacuity and boundary cases.**
  - `hk` and `hst` force `Δ > 0`.
  - `B.L N ≥ 3` and `W N ≥ 1` hold for every `N`, so there is no `N = 0` or empty-index loophole.
  - At `n = 2`, `Icc 3 2 = ∅`, so the statement agrees with T1506 (T4).
  - There is no smuggling through structure fields: `Band` is the accepted structure and is unchanged.

## Nondegenerate n = 3 witness (compiled by the auditor)

The scratch file is `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM1D/c89db6b5-4fbc-4b34-995c-1e741f3b37d2/scratchpad/T1523audit.lean`. It was compiled with `lake env lean` in the audit worktree: no errors, and every axiom set is standard. It is not part of the delivery.

1. `T1523Audit.exists_Bk`: for any `B`, `|E| < 2`, `N`, `0 ≤ T < 1` and `n`, there exists `Bk ≥ 0` satisfying `hBk`.
2. An `example` applies `discrete_hierarchy_step_n` with:
   - `n = 3`, non-alternating `σ = ![true, true, false]`, `E = 0`;
   - `s ≡ 1/4`, `t ≡ 1/2`, `K ≡ 2`, `k = 0`, so `u₀ = 1/4`, `u₁ = 3/8`, `Δ = 1/8`;
   - arbitrary `B` and `N`.

   Every hypothesis is discharged, including `hξ`, which follows from `norm_mSigma`. The theorem's full conclusion is obtained.

Recommendation, not blocking: the in-file n = 3 `example` covers only `Uker_step_n`'s hypotheses, and trivially. At merge, the dispatcher may wish to have an `exists_Bk`-style witness added to the module.

## Paper deltas

No new Lean-versus-paper difference. The `S^(B)` in `ThetaOp` is the existing #106. The `Bk` envelope is a hypothesis of an already-accepted shape, and its satisfiability is proved above.
