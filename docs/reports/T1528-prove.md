Prover model: claude-opus-5-5

Ticket: T1528, repair per `docs/tickets/T1528-amend-1.md` (G1c Step 3, pilot P3a: complex Z/Y decomposition and the E⊗E tensor).
Worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1528`, branch `t/T1528` (repair starts from `522190c`).
Sole writable file: `RBM1D/Gauss/GridStepDecompC.lean`, plus the T1528a row of `docs/paper-deltas.md` (CLAUDE.md §3.7).
Repair started 2026-09-26T16:30Z (UTC).

Inputs read: amend-1 ticket, original ticket, audit `docs/reports/T1528-audit.md` (all sections), the
current file, `GridQVForm.lean` (`vB`, `vB_self`, `v_sum_eq`, `abs_vB_le`), `GridMarkov.lean` (`lin`, `v`,
`coordFinset`, `v_nonneg`), `Model.lean` (`gvar`, `Xentry`), `Generator.lean` (`TestFun`,
`gvar_crd_diag_exact`), `GridStepDecomp.lean` (`stepDecomp_Y_sq`), paper pp.54–55, (5.20)–(5.25).

## Audit defects addressed

| Audit item | Resolution in this repair |
|---|---|
| T3 BLOCKED (complex-coefficient identity false for real `v`) | Replaced by (T3′) per the dispatcher: `vC`, `eeHerm`, Hermitian identity for complex weights |
| T3 report item (relation to (5.23)/(5.25) missing) | Section "eeHerm and the paper's E⊗E" below |
| T4 RETURN (scalar `q` special case) | Replaced by (T4′): `TestFun` finite-sum / linear-combination closure, pilot for arbitrary `Q` |
| T1528a paper-delta wording | Revised: the obstruction applies to the real `v` only; with `vC` a single Hermitian tensor exists |
| Optional N1 (`stepDecompC_Y_sq`, redundant `hIntRe`/`hIntIm`) | Attempted, see (N1) |

## Math preflight (written before any Lean change of this repair)

Notation. `X_c := Xmat d N (Pi.single c 1)` for a raw coordinate `c ∈ coordFinset N`; `t_c(A) := tr(A·X_c) ∈ ℂ`.
By definition `lin N A X_c = Re t_c(A)` and `v N A = Σ_{c ∈ coordFinset N} gvar(c)·(Re t_c(A))²` (`linVar`).
`lin_neg_I_smul_eq_im` (already in the file) gives `lin N ((-I)•A) X_c = Im t_c(A)`.

### (T3′) Hermitian E⊗E tensor

1. `vC N A := v N A + v N ((-I)•A)`.
   `vC_eq_sum_abs_sq`: `vC N A = Σ_{c ∈ coordFinset N} gvar(c)·‖t_c(A)‖²`.
   Proof: termwise `gvar·(Re t)² + gvar·(Im t)² = gvar·‖t‖²` (`Complex.sq_norm`, `Complex.normSq_apply`). PASS.
2. Generic sesquilinear form on matrices, `vH N A A' := Σ_c (gvar c : ℂ)·t_c(A)·conj(t_c(A'))`.
   Then `eeHerm Φ b b' M := vH N (gradMat (Φ b) M) (gradMat (Φ b') M)`.
   The conjugation is on the **second** slot `b'`. This is the dispatcher's definition verbatim (A_b := gradMat(Φ_b)(M)).
   - `vH` is ℂ-linear in the first argument and conjugate-linear in the second, because `t_c` is ℂ-linear
     (`Matrix.sum_mul`, `trace_sum`, `smul_mul`, `trace_smul`) and `conj` is additive and multiplicative.
   - `(vC N A : ℂ) = vH N A A`, since `t·conj t = (‖t‖² : ℂ)` (`Complex.mul_conj`, `Complex.normSq_eq_norm_sq`).
3. `vC_sum_eq_eeHerm`: `(vC N (Σ_b c_b•A_b) : ℂ) = Σ_b Σ_b' c_b·conj(c_b')·eeHerm b b'`, for complex `c : ι → ℂ`
   and `[Fintype ι]`. Proof: item 2 plus bilinear expansion and finite sum swaps. The coefficient `conj(c_b')` sits
   on the same slot as the conjugated factor `conj t_c(A_b')`, so the conjugation slot is consistent. PASS.
   Sanity check against the audit's counterexample: for one label with `c ∈ {1, i}`, the identity gives
   `vC(iA) = |i|²·vC(A) = vC(A)`. That is true, because `vC(iA) = v(iA) + v(A)` and `v(-i·iA) = v(A)`. So there is
   no conflict with `v_ne_v_smul_I`, which concerns `v`, not `vC`.
4. `eeHerm_conj_symm`: `eeHerm b' b = conj(eeHerm b b')`. Termwise, `conj(g·t·conj s) = g·s·conj t` for real `g`. PASS.
   **Ticket-typo note.** The amend text reads "eeHerm b' b = conj(eeHerm b b)". Read literally, with `b b` on the
   right, that is false in general: it would force `eeHerm b' b` to be real and independent of `b'`. The audit's own
   statement (`T_{b',b} = conj T_{b,b'}`) is the intended Hermitian symmetry, and that is what is proved.
5. `abs_eeHerm_le`: `‖eeHerm b b'‖² ≤ (eeHerm b b).re·(eeHerm b' b').re`.
   Companions: `eeHerm_self : eeHerm b b = (vC N A_b : ℂ)`, which makes the diagonal real, and
   `0 ≤ (eeHerm b b).re` (from `vC ≥ 0`), which makes it nonnegative.
   Proof: `‖Σ g t conj s‖ ≤ Σ g‖t‖‖s‖ = Σ (√g‖t‖)(√g‖s‖)`, then finite Cauchy–Schwarz
   (`Finset.sum_mul_sq_le_sq_mul_sq`); square both sides, which are nonnegative. PASS.
6. `v_le_vC : v N A ≤ vC N A` and `v_neg_I_le_vC : v N ((-I)•A) ≤ vC N A`, both from `v_nonneg`. PASS.
   Consequence (already consumable by `stepDecompC_ZC_subG`): a single bound `Δ·vC N (AbC ω) ≤ c` on `E` gives both
   `hboundRe` and `hboundIm` with the same `c`, which is the common `c` `azuma_complex` needs. A packaged corollary
   `stepDecompC_ZC_subG_vC` is added. It has one hypothesis on `vC` and no new hypotheses.
7. `vC_sum_le` (Minkowski / supervisor C5 paired form):
   `vC N (Σ_b w_b•A_b) ≤ (Σ_b ‖w_b‖)²·max_b vC N (A_b)`, with `max_b := ⨆ b, vC N (A b)` over a `Fintype`.
   For empty `ι`, `⨆ = 0` and the left side is `vC 0 = 0`, so the statement still holds.
   It comes from `vC_sum_le_of_le`: `(∀ b, vC(A_b) ≤ C) → vC(Σ w_b A_b) ≤ (Σ‖w_b‖)²·C`.
   Proof: by item 3, `vC(Σ w A) = ‖(vC : ℂ)‖ ≤ Σ Σ ‖w_b‖‖w_b'‖‖T_{bb'}‖`. By item 5 and the hypothesis,
   `‖T_{bb'}‖² ≤ C²` with `C ≥ vC(A_b) ≥ 0`, so `‖T_{bb'}‖ ≤ C`. PASS.
   Extra (not required, mirrors the Schwarz step of (5.25) exactly): `vC_sum_le_card`:
   `vC(Σ_{k ∈ s} B_k) ≤ #s·Σ_{k ∈ s} vC(B_k)`, via `‖Σ z‖ ≤ Σ‖z‖` and `sq_sum_le_card_mul_sum_sq`. PASS.
8. Kept unchanged, as the ticket requires: `eeTensor`, `v_sum_eq_eeTensor`, `abs_eeTensor_le`, `v_ne_v_smul_I`,
   `not_exists_eeTensor_const_of_smul`. Only the section docstring is updated.

Hypotheses and satisfiability (T3′). None of the targets has a hypothesis beyond `[Fintype ι]`, except
`vC_sum_le_of_le`, where `C` can be taken as `max_b vC(A_b)`. No vacuity issue arises.
Nondegeneracy: `vC N (single i i 1) ≥ v N (single i i 1) = 1/(3W) > 0` (`v_ne_v_smul_I`'s computation), so the
diagonal of `eeHerm` is not identically zero.
Dependencies: `GridQVForm`, `GridMarkov`, `GridStepDecomp` (all merged). No cycle.

### eeHerm and the paper's E⊗E ((5.22)/(5.23)/(5.25)): conventions and factors

- **Coordinates.** `gvar(c)` is `S_ij` on a diagonal coordinate and `S_ij/2` on each of the Re/Im coordinates of an
  off-diagonal pair `i<j` (`Model.lean`, so that `E|X_ij|² = S_ij`). For `i<j`, `X_{(i,j,true)} = E_ij + E_ji` and
  `X_{(i,j,false)} = iE_ij − iE_ji`. Diagonal false-tag coordinates and reversed-key coordinates give `X_c = 0`, so
  they contribute nothing.
- **Derivatives.** For `A = gradMat Φ M` and a Hermitian direction `X_c`, `t_c(A) = DΦ(M)[X_c]`
  (`fderiv_eq_trace_gradMat`). Write `∂_ij` for the entrywise derivative (the paper's `∂_{(H)_ij}`, where `H_ij`
  and `H_ji` are independent variables). Then
  `DΦ[E_ij+E_ji] = ∂_ijΦ + ∂_jiΦ` and `DΦ[iE_ij−iE_ji] = i(∂_ijΦ − ∂_jiΦ)`.
  Summing the two off-diagonal coordinates with weight `S_ij/2`:
  `(S_ij/2)[(p+q)conj(p'+q') + (p−q)conj(p'−q')] = S_ij(p·conj p' + q·conj q')`,
  where `p = ∂_ijΦ_b`, `q = ∂_jiΦ_b`, and primes denote `Φ_b'`.
  Hence (mathematical identification, not a Lean statement of this ticket):
  `eeHerm_{b,b'} = Σ_{α=(i,j)} S_α·∂_αΦ_b(M)·conj(∂_αΦ_b'(M))`, the sum running over **ordered** pairs `α`.
  In the paper's notation this is `Σ_α E^{(M)}_b(α)·conj(E^{(M)}_{b'}(α))` with `E^{(M)}(α) = S_α^{1/2}∂_α L`
  (paper, proof of Lemma 5.5).
- **Conjugation slot.** Paper (5.22)/(5.23) builds `(E⊗E)_{a,a'}` by attaching the cut loop to its
  **complex-conjugate** loop with indices `a'`, and (5.24) puts the conjugate sign vector `σ̄` on the second
  `U`-factor (`U_{u,t,σ̄} = conj U_{u,t,σ}` entrywise). So the paper's tensor is conjugated on the second index `a'`,
  the same slot as `eeHerm`'s `b'`. The contraction `[(U⊗U_σ̄)∘A]_{a,a} = Σ_{b,b'} U_{ab}·conj(U_{ab'})·A_{bb'}` is
  exactly the right side of `vC_sum_eq_eeHerm` with `c_b = U_{ab}`.
- **Edge splitting and the factor `C_n`.** For `Φ_b = (L−K)_{u,σ,b}` (`K` is deterministic), `∂_αΦ_b = Σ_k ∂_α^{(k)}L_b`,
  where the derivative acts on the `k`-th G-edge. Hence
  `eeHerm_{b,b'} = Σ_{k,k'} Σ_α S_α ∂^{(k)}_α L_b·conj(∂^{(k')}_α L_{b'})`.
  The paper's `(E⊗E)^{(k)}` of (5.22) is the **diagonal** `k = k'` block only. The full `eeHerm` includes the
  `k ≠ k'` cross terms.
  - The **first equality** of (5.25), `[∫(U∘E^{(M)})_a]_t = ∫Σ_α|(U∘E^{(M)}(α))_a|²du`, is, per grid step, exactly
    `Δ·vC N (AbC)` = `Δ·Σ_{b,b'} U_{ab} conj(U_{ab'}) eeHerm_{bb'}`. This is `vC_sum_eq_eeHerm` at `c_b = U_{ab}`
    (with `Q` folded into `U` or into `Φ`).
  - The **inequality** in (5.25), where the paper uses "Schwarz" to get `C_n·(U⊗U)∘(E⊗E)`, is `vC_sum_le_card`
    applied to `B_k := Σ_b U_{ab}·gradMat(∂^{(k)}…)`, with `C_n = n`.
  - `vC_sum_le` (the C5 paired form) is the coarser version that bounds by `(Σ|U_{ab}|)²·max_b`.
- **Normalisation of (5.22).** The factor `W·Σ_{b,b'} S^{(B)}_{b,b'} L_{t,σ^{(k)},a^{(k)}}` with block indices `b,b'`
  arises from summing the index-level `Σ_α S_α ∂^{(k)}L·conj ∂^{(k)}L` over `i ∈ block b`, `j ∈ block b'`, using the
  paper's block normalisation `S = S^{(B)}⊗S_W` and the `E_a`/`⟨·⟩` conventions of the loops. This identification
  (the (2n+2)-loop form with `σ^{(k)}, a^{(k)}` of (5.23)) is **not** formalized here; it is P3b (T1529).
- **Time factor.** `vC` is the per-unit-time density: the grid step's conditional variance of `Re Z^C` (resp.
  `Im Z^C`) is `Δ·v(AbC)` (resp. `Δ·v((-I)AbC)`), and their sum is `Δ·vC(AbC)`.
- **Why not `v` alone.** `v` is the conditional variance of the real part only. It is not a Hermitian form under
  complex weights (compiled `v_ne_v_smul_I`), which is the only content left in T1528a.

### (T4′) pilot with a genuine label-space `Q`

- `testFun_sum`: `(∀ i ∈ s, TestFun (Φ i)) → TestFun (fun M => Σ_{i ∈ s} Φ i M)`.
  Proof: `ContDiff.sum`, `norm_sum_le`, `fderiv_sum` (twice, using `differentiable`/`differentiable_fderiv`). PASS.
- `testFun_linComb`: `TestFun (fun M => Σ_i q i * Φ i M)` for any `q : ι → ℂ`, from `testFun_sum` and
  `testFun_const_smul`. PASS.
- `norm_fderiv2_linComb_le`: `(∀ i M, ‖D²Φ_i M‖ ≤ C) → ‖D²(Σ_i q_i Φ_i)(M)‖ ≤ (Σ_i ‖q_i‖)·C`.
  Proof: `D²(Σ q_iΦ_i) = Σ q_i•D²Φ_i`, then the triangle inequality. PASS.
- `pilot_n4_alt_testFun` and `pilot_n4_alt_bdd2`, for **arbitrary** `Q : LoopArg (B.L N) 4 → LoopArg (B.L N) 4 → ℂ`:
  `TestFun (fun M => Σ_{a'} Q a a' * ΦgridG B E N u sigmaAlt4 a' M)`, and `hC₂` with constant
  `(Σ_{a'} ‖Q a a'‖)·(card·(16·(2(1+η⁻¹)³)⁴))`, which is the audit's constant (`16 = 4²`).
  Hypotheses: `|E| < 2`, `u < 1`, `0 < η ≤ |Im zt E u|`. These are the same as `ΦgridG_testFun`/`_bdd2`.
  Witness: `E = 0`, `u = 0`, `η = |Im zt 0 0|`, any `Q`, including the plan's `Q_u = I − ϑ_u P`. PASS.
- The scalar-only `pilot_n4_alt_*` versions are **replaced**: same names, new signatures with `Q`. The branch is not
  merged, so no frozen signature is affected. The scalar case is recovered with `Q a a' := if a' = a then q else 0`.
  The n=3 non-alternating instance is unchanged.

### (N1, optional) integrated L² bound and redundant integrability hypotheses

- `integrable_stepZC_re'` / `integrable_stepZC_im'`: for `TestFun` Φ with uniform `C₂` and `0 ≤ Δ`, both parts are
  integrable. Proof: `stepZC = g − h0 − R` (`g_eq_pointwiseC`), with `g` and `h0` integrable (`integrable_Phi_H`)
  and `R` integrable (`integrable_RlabelC_sum`), then take `.re`/`.im`. This is the audit's
  `audit_integrable_stepZC` route. PASS.
- `stepDecompC_Y_sq`:
  `∫‖Y^C‖² ≤ 4·((Σ_a‖U b a‖)·(C₂/2))²·Δ²·∫‖X_{j+1}‖⁴`.
  It is a port of T1505's `stepDecomp_Y_sq` with `|U|` replaced by `‖U‖`. It uses `stepYC_norm_le_ae` and
  conditional Jensen. There is no `hIntRe`/`hIntIm` hypothesis, because it is discharged by the lemma above. PASS.

## Verdicts (preflight)

| Target | Verdict |
|---|---|
| T1, T2 | unchanged from the audited delivery (audit: PASS) |
| T3′ (`vC`, `vC_eq_sum_abs_sq`, `eeHerm`, `vC_sum_eq_eeHerm`, `eeHerm_conj_symm`, `abs_eeHerm_le`, `v_le_vC`, `v_neg_I_le_vC`, `vC_sum_le`) | PASS (with the `conj(eeHerm b b')` typo correction noted in item 4) |
| T4′ (`testFun_sum`, arbitrary-`Q` n=4 pilot) | PASS |
| N1 (optional) | PASS (attempt) |

## Build (after the Lean changes)

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1528 && lake build RBM1D.Gauss.GridStepDecompC
```
Result: `Build completed successfully (3819 jobs)`. The rebuilt `.olean` is dated after the edit. There are only
linter warnings (`show`, deprecated names), and no errors.
Forbidden tokens: `grep -nE "\bsorry\b|\badmit\b|axiom"` finds nothing in the file.
Commit: `8a4dfe0` on `t/T1528`. It touches only `RBM1D/Gauss/GridStepDecompC.lean`.

Tooling note for the auditor: `lake env lean <file>` needs `-DmaxSynthPendingDepth=3`, the lakefile's `leanOptions`.
Without it, even the pre-repair file fails to elaborate (`NormSMulClass ℂ (… →L[ℝ] …)`) under `lake env lean`.
`lake build` applies the option automatically.

## Declarations added or changed in this repair (namespace `RBM.Gauss.Grid`)

- **T3′:** `vC`, `vC_nonneg`, `v_le_vC`, `v_neg_I_le_vC`, `vC_eq_sum_abs_sq`, `vH`, `vC_eq_vH`,
  `vH_sum`, `vH_conj_symm`, `norm_vH_sq_le`, `eeHerm`, `vC_sum_eq_eeHerm`, `eeHerm_conj_symm`, `eeHerm_self`,
  `eeHerm_self_re_nonneg`, `abs_eeHerm_le`, `vC_sum_le_of_le`, `vC_sum_le`, `vC_sum_le_card`,
  `stepDecompC_ZC_subG_vC`. There is also one private helper, `trace_sum_smul_mul`.
- **T4′:** `fderiv2_sum_eq`, `fderiv2_const_smul_eq`, `testFun_sum`, `testFun_linComb`,
  `norm_fderiv2_linComb_le`. `pilot_n4_alt_testFun` and `pilot_n4_alt_bdd2` are **restated** for arbitrary
  `Q : LoopArg (B.L N) 4 → LoopArg (B.L N) 4 → ℂ`, and the scalar-`q` versions are removed.
- **N1:** `integrable_stepZC_of_testFun`, `integrable_stepZC_re_of_testFun`, `integrable_stepZC_im_of_testFun`,
  `stepDecompC_Y_sq`.
- **Unchanged:** all T1/T2 declarations, `eeTensor`, `v_sum_eq_eeTensor`, `abs_eeTensor_le`, `v_ne_v_smul_I`,
  `not_exists_eeTensor_const_of_smul`, `ΦgridG*`, `testFun_const_smul` (docstring updated only), and
  `pilot_n3_nonAlt_*`.

Exact headline statements (T3′):
- `vC_eq_sum_abs_sq (N) (A) : vC N A = ∑ c ∈ coordFinset N, (gvar d c : ℝ) * ‖Matrix.trace (A * Xmat d N (Pi.single c 1))‖ ^ 2`
- `vC_sum_eq_eeHerm (Φ : ι → Mat → ℂ) (c : ι → ℂ) (M) : (vC N (∑ b, c b • gradMat (Φ b) M) : ℂ) = ∑ b, ∑ b', c b * conj (c b') * eeHerm Φ b b' M`
- `eeHerm_conj_symm : eeHerm Φ b' b M = conj (eeHerm Φ b b' M)`
- `abs_eeHerm_le : ‖eeHerm Φ b b' M‖ ^ 2 ≤ (eeHerm Φ b b M).re * (eeHerm Φ b' b' M).re`, with
  `eeHerm_self_re_nonneg : (eeHerm Φ b b M).im = 0 ∧ 0 ≤ (eeHerm Φ b b M).re`
- `vC_sum_le (A : ι → Mat) (w : ι → ℂ) : vC N (∑ b, w b • A b) ≤ (∑ b, ‖w b‖) ^ 2 * ⨆ b, vC N (A b)`

(T4′):
- `pilot_n4_alt_bdd2 … (Q) (a) (M) : ‖fderiv ℝ (fderiv ℝ (fun M => ∑ a', Q a a' * ΦgridG B E N u sigmaAlt4 a' M)) M‖ ≤ (∑ a', ‖Q a a'‖) * ((Fintype.card (B.toDims.Idx N) : ℝ) * (16 * (2 * (1 + η⁻¹) ^ 3) ^ 4))`

## Axioms

I ran `#print axioms` on all 33 listed public theorems: every new one above, plus `eeTensor`, `v_sum_eq_eeTensor`,
`abs_eeTensor_le`, `stepDecompC` and `stepDecompC_ZC_subG`. Each depends only on
`[propext, Classical.choice, Quot.sound]`.

## Witnesses (compiled in a scratch file, then deleted, not committed)

- `pilot_n4_alt_testFun B (E := 0) (u := 0) (by norm_num) N (by norm_num) Q a` works for an arbitrary `Q`.
- `0 < vC N (Matrix.single i i 1)` holds, proved from `v_ne_v_smul_I`, `v_le_vC`, `v_neg_I_le_vC` and the sign
  invariance of `vC`. So the Hermitian diagonal is nondegenerate.

## Key lemmas used

`lin_neg_I_smul_eq_im` (this file); `v`, `linVar`, `coordFinset`, `v_nonneg` (`GridMarkov`); `gvar` (`Model`);
`Complex.sq_norm`, `Complex.normSq_apply`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Complex.norm_conj`,
`Finset.sum_mul_sq_le_sq_mul_sq`, `sq_sum_le_card_mul_sum_sq`, `pow_le_pow_iff_left₀`, `le_ciSup` (Mathlib);
`fderiv_fun_sum`, `fderiv_const_smul`, `ContDiff.sum`, `norm_sum_le`; `g_eq_pointwiseC`, `integrable_Phi_H`,
`integrable_h0C`, `integrable_RlabelC_sum`, `stepYC_norm_le_ae`, `integrable_normSq_incr`,
`integrable_normPow4_incr`, `ConvexOn.map_condExp_le_univ`, `integral_condExp`.

## paper-deltas

The T1528a row was revised in place, with the same tag and no renumbering. It now says:
- the obstruction concerns only the real `v`;
- with `vC` on the left, the single Hermitian tensor `eeHerm` exists, conjugated on the second slot;
- the relation to (5.22)–(5.25) is as described above.

## Open issues

- The amend text's "eeHerm_conj_symm: eeHerm b' b = conj(eeHerm b b)" is read as `conj(eeHerm b b')`. The literal
  `b b` version is false in general. The proved statement is the Hermitian symmetry stated in the audit.
- The identification `eeHerm_{bb'} = Σ_α S_α ∂_αΦ_b conj(∂_αΦ_b')` is argued in this report but not formalized. So is
  the block-level (2n+2)-loop form of (5.22)/(5.23), including the factor `W·S^{(B)}` and the `σ^{(k)}, a^{(k)}` index
  pattern. Both belong to P3b (T1529).
- `vC_sum_le` uses `⨆ b` for "max_b". For empty `ι` both sides are 0.
- `stepDecompC` keeps its `hIntRe`/`hIntIm` hypotheses unchanged, since the signature is kept. They are now
  dischargeable with `integrable_stepZC_re_of_testFun`/`_im_of_testFun`, and `stepDecompC_Y_sq` does not take them.
- The root import is not added; that happens at merge by the hub.
