Auditor model: claude-opus-5-5

# T1528 re-audit (amend-1): complex Z/Y decomposition, Hermitian E⊗E tensor, arbitrary-Q pilot (G1c pilot P3a)

Audited: branch `t/T1528` at `8a4dfe0`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1528`. The repair commit `8a4dfe0` sits on top of the audited `522190c`. The diff against `main` is still one new file, `RBM1D/Gauss/GridStepDecompC.lean` (1320 lines). No commit on `main` since the branch base `ae718fe` touches this file.
Inputs: `docs/tickets/T1528.md`, `docs/tickets/T1528-amend-1.md`, `docs/reports/T1528-prove.md` (repair), the previous audit, and paper pp. 54–55 ((5.20)–(5.25)).
Audit time: 2026-09-26T16:45Z (UTC).

## Overall verdict: PASS

| Target | Verdict |
|---|---|
| T1 `stepZC`/`stepYC`/`stepDecompC`, `condExp_stepZC_eq_zero`, sub-Gaussian packaging, Y bound | PASS (unchanged; N1 now also closed) |
| T2 complex-kernel linearity | PASS (unchanged) |
| T3′ `vC`, `vC_eq_sum_abs_sq`, `eeHerm`, `vC_sum_eq_eeHerm`, `eeHerm_conj_symm`, `abs_eeHerm_le`, `v_le_vC`, `v_neg_I_le_vC`, `vC_sum_le` (+ kept `eeTensor` family) | PASS |
| T4′ `testFun_sum`, arbitrary-`Q` n=4 alternating pilot, n=3 non-alternating pilot | PASS |
| N1 (optional) `stepDecompC_Y_sq`, integrability discharge | PASS |

## Gate 1: math preflight
The repair report has a "Math preflight (written before any Lean change of this repair)" section. It gives a verdict for each of T3′, T4′ and N1, and it comes before the build section. PASS.

## Gate 5: builds, axioms, forbidden tokens
- `lake build RBM1D.Gauss.GridStepDecompC` in the worktree: `Build completed successfully (3819 jobs)`. I also re-elaborated the file directly from source (`lake env lean -DmaxSynthPendingDepth=3 RBM1D/Gauss/GridStepDecompC.lean`), with no errors.
- `lake build RBM1D` in the worktree: `Build completed successfully (9673 jobs)`. The root import is not added yet; that happens at merge, as the ticket says.
- I ran `#print axioms` myself, in a scratch file outside the repo, on 31 public theorems: every T1/T2/T3/T3′/T4′/N1 headline plus the helpers `vH_sum`, `norm_vH_sq_le`, `vC_sum_le_of_le`, `vC_sum_le_card`, `stepDecompC_ZC_subG_vC`, `testFun_linComb` and `norm_fderiv2_linComb_le`. All of them list only `[propext, Classical.choice, Quot.sound]`.
- There is no `sorry`, `admit` or `axiom` in the file. `hReal` appears only in docstrings. No existing file is edited. The only signatures that changed (`pilot_n4_alt_*`) belong to this unmerged ticket, so no frozen signature is touched.

## Gate 4: dependencies
The imports are unchanged (`GridQVForm`, `GridExpansion`, both merged). The new T3′ code uses only `v`, `linVar`, `coordFinset`, `v_nonneg`, `gvar`, `Xmat`, `gradMat` and the in-file `lin_neg_I_smul_eq_im`. There is no cycle. PASS.

## T1 / T2: spot check
The repair diff leaves every T1/T2 definition and theorem unchanged. The only changes in those sections are module-docstring edits, `open scoped ComplexConjugate`, and new declarations appended after `stepDecompC_ZC_subG`. So the earlier PASS findings still hold: no `hReal`, the compiled specialisation to T1505's `stepDecomp` for real Φ and real `U`, and the compiled n=3 instance. Axioms were re-printed clean.
N1 is now closed. `integrable_stepZC_re_of_testFun`/`_im_of_testFun` discharge `hIntRe`/`hIntIm` under the same `TestFun`/`C₂`/`0 ≤ Δ` hypotheses. `stepDecompC_Y_sq` states `∫‖Y^C‖² ≤ 4((Σ_a‖U b a‖)(C₂/2))²Δ²∫‖X_{j+1}‖⁴` with no integrability hypothesis. This is T1505's `stepDecomp_Y_sq` constant with `|U|` replaced by `‖U‖`. `stepDecompC` itself keeps `hIntRe`/`hIntIm` in its signature, but they are now dischargeable. That is acceptable.

## T3′: statement check

- **`vC N A := v N A + v N ((-I)•A)`.** `vC_eq_sum_abs_sq : vC N A = Σ_{c∈coordFinset N} gvar(c)·‖tr(A·X_c)‖²`, with `X_c := Xmat(single c 1)`. The proof goes termwise through `lin_neg_I_smul_eq_im`, i.e. `Re tr(−iAX) = Im tr(AX)`, then `Re² + Im² = ‖·‖²`. This is exactly the conditional variance of the whole increment: `stepDecompC_ZC_subG` already identifies `v(AbC)` as the Re part and `v((-I)•AbC)` as the Im part. PASS.
- **`eeHerm` and the conjugation slot.** `eeHerm Φ b b' M := vH N (gradMat (Φ b) M) (gradMat (Φ b') M)`, where `vH N A A' := Σ_c (gvar c:ℂ)·tr(A X_c)·conj(tr(A' X_c))`. I checked this by compiling `rfl` against the fully unfolded form `Σ_c gvar·tr(A_b X_c)·conj(tr(A_{b'} X_c))`. **The conjugation is on the second slot `b'`**, as the amend requires.
- **`vC_sum_eq_eeHerm`.** `(vC N (Σ_b c_b • gradMat(Φ_b) M) : ℂ) = Σ_b Σ_{b'} c_b·conj(c_{b'})·eeHerm Φ b b' M` for arbitrary `c : ι → ℂ`, `[Fintype ι]`. The algebra is `vC_eq_vH` (`t·conj t = ‖t‖²`) plus `vH_sum`, which expands both sums using `trace_sum_smul_mul`, `map_sum`, `map_mul` and `Finset.sum_comm`. The conjugated coefficient `conj(c_{b'})` pairs with the conjugated factor `conj tr(A_{b'}X_c)`, so the slots are consistent. I also compiled the identity with genuinely non-real weights (`c = (I, 1)`) to make sure it does not degenerate to real weights. PASS.
- **`eeHerm_conj_symm : eeHerm Φ b' b M = conj (eeHerm Φ b b' M)`.** This is the correct Hermitian symmetry. The amend's literal text `conj(eeHerm b b)` is a typo: read literally it would force every off-diagonal entry to be real and independent of `b'`, which is false. The prover proved the intended statement and flagged the typo. This is non-blocking. PASS.
- **`abs_eeHerm_le : ‖eeHerm b b'‖² ≤ (eeHerm b b).re·(eeHerm b' b').re`.** It comes with `eeHerm_self : eeHerm b b = (vC(gradMat Φ_b M) : ℂ)` and `eeHerm_self_re_nonneg`, which give an imaginary part of 0 and a real part ≥ 0. So the diagonal is real and nonnegative, and the `.re` in the statement loses nothing. The proof is genuine Cauchy–Schwarz: `‖Σ g t conj s‖ ≤ Σ(√g‖t‖)(√g‖s‖)`, then `Finset.sum_mul_sq_le_sq_mul_sq`, with both sums identified with `vC` through `vC_eq_sum_abs_sq`. PASS.
- **`v_le_vC`, `v_neg_I_le_vC`.** Both follow from `v_nonneg` and are stated for arbitrary `A`. `stepDecompC_ZC_subG_vC` turns one hypothesis `Δ·vC(AbC) ≤ c` on an `F_j`-set into both sub-Gaussian conclusions with the same `c`, which is the input form `azuma_complex` needs. PASS.
- **`vC_sum_le : vC(Σ_b w_b•A_b) ≤ (Σ_b‖w_b‖)²·⨆_b vC(A_b)`**, for arbitrary `A : ι → Mat` and `w : ι → ℂ` over a `Fintype ι`. It is proved through `vC_sum_le_of_le`: `‖vH(A_b,A_{b'})‖ ≤ C` from `norm_vH_sq_le`, then the triangle inequality on the expansion. `⨆` over a finite range is a true max (`le_ciSup` with `Set.finite_range`). For empty `ι` both sides are 0. This matches supervisor C5's paired form. PASS.
- **Kept unchanged, as required:** `eeTensor`, `v_sum_eq_eeTensor`, `abs_eeTensor_le`, `v_ne_v_smul_I`, `not_exists_eeTensor_const_of_smul`.
- **Vacuity and nondegeneracy.** No T3′ target has hypotheses beyond `[Fintype ι]`, except `vC_sum_le_of_le`, where `C := max_b vC(A_b)` always works. I compiled `0 < vC N (Matrix.single i i 1)` myself from `v_ne_v_smul_I`, `v_le_vC`, `v_neg_I_le_vC` and evenness of `v`, so the Hermitian diagonal is not identically zero.

**Relation to (5.22)/(5.23)/(5.25).** The amend asks for this as a report item, and the repair report does state it with conventions and factors. I checked it against the paper and `Model.lean`:
- **Coordinates.** `gvar = S_ii` on the diagonal and `S_ij/2` on each of the Re/Im coordinates of a pair `i<j`. For `i<j`, `X_{(i,j,true)} = E_ij+E_ji` and `X_{(i,j,false)} = iE_ij − iE_ji`. This matches `Xentry`. The derivation `(S/2)[(p+q)conj(p'+q') + (p−q)conj(p'−q')] = S(p conj p' + q conj q')` is correct, so `eeHerm_{bb'} = Σ_{α ordered} S_α ∂_αΦ_b·conj(∂_αΦ_{b'})`, which is `Σ_α E^{(M)}_b(α)·conj(E^{(M)}_{b'}(α))` in the notation of the Lemma 5.5 proof (`E^{(M)}(α) = S_α^{1/2}∂_α L`).
- **Conjugation slot.** The paper attaches the complex-conjugate loop with indices `a'` in (5.22) and puts `σ̄` on the second `U` factor in (5.24). So the paper also conjugates the second index, which agrees with `b'`.
- **The (5.25) steps.** The first equality of (5.25), per grid step, is `Δ·vC(AbC)`, which is `vC_sum_eq_eeHerm` at `c_b = U_{ab}`. The report states correctly that the paper's `(E⊗E)^{(k)}` is only the diagonal `k=k'` block of the full `eeHerm`, and that the Schwarz step with `C_n = n` is `vC_sum_le_card`. Both are compiled.
- **What is not formalized.** The identification of `eeHerm` with `Σ_α S_α∂_α∂̄_α` and the block-level (2n+2)-loop form `W·ΣS^{(B)}L_{σ^{(k)},a^{(k)}}` are argued in the report but not formalized. The report says so explicitly and assigns them to P3b (T1529), consistent with the original ticket, which excludes the (2n+2)-loop form. PASS for the report item.

## T4′: statement check
- `testFun_sum` gives closure of `TestFun` under a finite sum over any `Finset`. It covers all four fields: `contDiff`, `bdd₀`, `bdd₁`, and `bdd₂` via `fderiv2_sum_eq`. `testFun_linComb` gives closure under `Σ_i q_i·Φ_i`. `norm_fderiv2_linComb_le` gives `‖D²(Σ q_iΦ_i)‖ ≤ (Σ‖q_i‖)·C`.
- **`Q` is genuinely arbitrary.** In both `pilot_n4_alt_testFun` and `pilot_n4_alt_bdd2`, `Q : LoopArg (B.L N) 4 → LoopArg (B.L N) 4 → ℂ` is an explicit, unconstrained function argument, and the observable is `fun M => Σ_{a'} Q a a' * ΦgridG B E N u sigmaAlt4 a' M`. It is not a scalar in disguise: the sum runs over all `a'`, and nothing restricts `Q` to be diagonal or constant. I compiled the instance with a non-diagonal, non-real `Q` (`if x = y then 1 − I else I/7`) at `E = 0`, `u = 0`.
- **C₂ constant.** The delivered constant is `(Σ_{a'}‖Q a a'‖)·(card(Idx N)·(16·(2(1+η⁻¹)³)⁴))`. This is the previous audit's constant, with `ΦgridG_bdd2`'s `4²` normalised to `16` by `norm_num`. The hypotheses are `|E|<2`, `u<1`, `0<η≤|Im zt E u|`, the same as `ΦgridG_bdd2`. Witness: `E=0`, `u=0`, `η=|Im zt 0 0|`. PASS.
- The n=3 non-alternating instance (`Q := I`, the plan's fallback) is unchanged. PASS.

## paper-deltas T1528a
The row in the main worktree's `docs/paper-deltas.md` (line 307) was revised in place, with the same temporary tag and no renumbering. It now splits into two parts:
- (i) The obstruction applies to the real `v` only.
- (ii) With `vC` on the left, the single Hermitian tensor `eeHerm` exists. It is conjugated on the second slot, and the row lists `eeHerm_conj_symm`, `abs_eeHerm_le`, `vC_sum_le`, `v_le_vC`/`v_neg_I_le_vC`.

The row also records the diagonal-`k` relation to (5.22), the `C_n = n` Schwarz step (`vC_sum_le_card`), and the non-formalized (2n+2)-loop form (P3b). The downstream instruction is to contract against `eeHerm`/`vC`, not against `eeTensor`/`v`. This is consistent with the delivery and with the previous audit's §T3 finding. PASS.

## Boundary and hidden-hypothesis summary
- There are no structure-field hypotheses, no `N = 0` or empty-index loopholes, and no collapsed windows. `N` is arbitrary, and the label sets are `Fintype` loop arguments. The empty-`ι` case of `vC_sum_le` is trivially true (both sides are 0), not a loophole.
- `stepDecompC_ZC_subG_vC` adds only `hΔ : 0 ≤ step`, which is needed to multiply the inequality and is satisfiable.

## Non-blocking notes
1. The amend text contains the typo `conj(eeHerm b b)`. The Lean statement is the correct `conj(eeHerm b b')`. The dispatcher may want to fix the ticket text for the record.
2. The `eeHerm = Σ_α S_α∂_α∂̄_α` identification and the (2n+2)-loop form remain P3b (T1529) inputs, as stated in the report.

## Required actions
None. Ready to merge: one file, `RBM1D/Gauss/GridStepDecompC.lean`, with the root import added at merge. The T1528a row is already revised in the main worktree.
