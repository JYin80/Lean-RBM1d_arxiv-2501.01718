Auditor model: claude-opus-5-5[1m]

# T1482 (amend-1) audit: grid Markov freezing lemma and conditional Gaussian MGF

Branch `t/T1482` at `d5a5741` (commits `8abfa09`, `d5a5741`). Audited in a detached worktree at
`/Users/junyin/Lean_proof/RBM1D-wt/T1482-audit`, because `t/T1482` is still checked out in the
prover worktree. `git diff --stat main...t/T1482` shows one file only: `RBM1D/Gauss/GridMarkov.lean`
(+609, new). No other file is touched, so no frozen signature changed and `RBM1D.lean` is unchanged.
Branch base `ef7f0e4`. `GridPath.lean`, `LinearForm.lean` and `Model.lean` are unchanged between
the base and current `main` (`98f0850`), so the module builds the same way on `main`.

## Verdict summary

| Target | Declaration | Verdict |
|---|---|---|
| (T1) | `RBM.Gauss.Grid.condExp_freeze` | PASS |
| (T2) | `RBM.Gauss.Grid.hasCondSubgaussianMGF_linear` | PASS |
| (T3) | `RBM.Gauss.Grid.condExp_linear_eq_zero` | PASS (with a note on the signature) |

Overall: **PASS**.

## 1. Math preflight

The report `docs/reports/T1482-prove.md` has a math-preflight section with PASS verdicts for
(T1), (T2) and (T3), with reasons. It comes before the "Lean status" sections. Some remarks
inside it were added afterwards ("confirmed by the completed Lean below"). Even so, the argument
and the verdicts are present and complete. The continuation pass keeps the (T2) PASS.

## 2. Statement versus ticket and source

Math source: `docs/claude-team/pilot-P4P5-paper.md` §3–§4. This is the discrete replacement for
the Brownian flow (2.34) used in paper §5.3. In §4 the linear part of ξ_{j+1} is exactly Gaussian
given F_j, with variance Δ·Σ_α S_α|∂_α f|², and the stopped increment has a deterministic
conditional sub-Gaussian constant.

**(T1)** `condExp_freeze {β} [MeasurableSpace β] [StandardBorelSpace β] (k) (hY : Measurable[filt d k] Y)
(hF : Measurable fun p : β × Ω d => F p.1 p.2) (hInt : Integrable (fun ω => F (Y ω) (ω (k+1))) (Pg d)) :
(Pg d)[fun ω => F (Y ω) (ω (k+1)) | filt d k] =ᵐ[Pg d] fun ω => ∫ x, F (Y ω) x ∂(P d)`.
This matches the ticket exactly. The hypotheses are `Y` being `filt d k`-measurable, `F` jointly
measurable, the composite integrable, and `β` standard Borel. The proof does not use
`StandardBorelSpace β`. That only makes the hypothesis superfluous; it is not a vacuity risk. The
proof checks the set-integral identity for every `A ∈ filt d k`. It uses `indep_incr` (T1481):
independence from the whole of `filt d k`. It then applies `Measure.prod_eq` on rectangles and
Fubini, and concludes with `ae_eq_condExp_of_forall_setIntegral_eq`. This is a genuine proof of
the general statement. `Y` ranges over all `filt d k`-measurable maps, not a special case.

**(T2)** The theorem takes `(N k) (hA : Measurable[filt d k] A) (E) (hE : MeasurableSet[filt d k] E) (c : ℝ)
(hc : 0 ≤ c) (hbound : ∀ ω ∈ E, step s t K N * v N (A ω) ≤ c)`. Its conclusion is
`HasCondSubgaussianMGF (filt d k) ((filt d).le k) (fun ω => E.indicator (fun ω => √(step s t K N) *
lin N (A ω) (Xmat d N (ω (k+1)))) ω) ⟨c, hc⟩ (Pg d)`.
- `lin N A X := (trace (A * X)).re`, as in the ticket.
- `v N A := linVar (gvar d) (fun c => lin N A (Xmat d N (Pi.single c 1))) (coordFinset N)`, that
  is, Σ_{c read by Xmat d N} (coefficient of c)²·gvar d c. This is the ticket's explicit formula.
  The coefficient of coordinate `c` is taken as the value of the linear map `y ↦ lin N A (Xmat d N y)`
  at the basis vector `Pi.single c 1`. `lin_Xmat_eq_sum` proves that the map is exactly
  Σ_c y_c·coef_c over the coordinates it reads, so this reading is correct.
- `c` is a fixed real number, the same for every sample, so the sub-Gaussian constant is
  deterministic, as the ticket requires. The bound is pointwise on `E`, as in the ticket. The
  quantifier order has all parameters fixed; the ticket has no `∀ᶠ N`.
- **Im variant.** The ticket says "(and the same with `Im`)". It is not stated as a separate
  declaration, but it follows directly: `lin N ((-I) • A) X = (trace (A * X)).im`, so the
  statement over all `A` covers it. I compiled the corollary `T2_im` (below) by applying the
  theorem to `fun ω => (-I) • A ω`. So the general target is covered. Downstream tickets that
  need the `Im` form literally can use this 3-line corollary.
- The proof is honest. It replaces `A` by `A' := if ω ∈ E then A ω else 0`, which is
  `filt d k`-measurable, and the indicator disappears. Integrability comes from Tonelli across the
  independent pair (`lintegral_indep_pair`), where the inner integral is the exact Gaussian MGF.
  The conditional MGF comes from `condExp_freeze`, bridged through
  `condExp_ae_eq_trim_integral_condExpKernel`, and is assembled with
  `Kernel.HasSubgaussianMGF.of_rat`. If `step < 0`, then `√step = 0` and the claim is trivially
  true. No hypothesis forces this case, so it is not a loophole.

**(T3)** The theorem takes `(N k) (hA : Measurable[filt d k] A) (E) (hE) (hIntG : Integrable (fun ω =>
√(step s t K N) * lin N (A ω) (Xmat d N (ω (k+1)))) (Pg d))` and concludes
`(Pg d)[E.indicator (...) | filt d k] =ᵐ 0`.
- Difference from the ticket's literal wording ("hypotheses of (T2) plus integrability"). The
  Lean statement drops `c`, `hc` and `hbound`. It requires integrability of the *untruncated*
  variable instead of the `E`-truncated one. Neither signature implies the other directly.
  However, the literal ticket form follows from the delivered one by applying it to `A'`
  (piecewise `E`, `A`, `0`). I compiled that derivation as `T3_literal` (below). So the delivered
  theorem is at least as general as the target. It is not a special case and not a conditional
  adapter. The hub/dispatcher should record this as a ticket-versus-Lean signature note. It is not
  a paper delta, because the paper statement is unaffected.

## 3. Vacuity, witnesses, hidden hypotheses, cycles

Checks compiled against the built module. The scratch file is
`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM1D/c89db6b5-4fbc-4b34-995c-1e741f3b37d2/scratchpad/AuditT1482.lean`.
It was run with `lake env lean` in the audit worktree and had no errors. All printed axioms are
`[propext, Classical.choice, Quot.sound]`.
- **`v` is the true variance (ticket's required check).**
  - `v_single_diag`: `v N (single i i 1) = gvar d ⟨N,i,i,true⟩ = S_ii`. The proof shows that
    `lin (E_ii) ∘ Xmat = (· ⟨N,i,i,true⟩)` and compares the variances of the two Gaussian laws,
    `map_lin_Xmat` and `P_map_eval`.
  - `v_single_off`: for `idxKey j < idxKey i`, `v N (single i j 1) = gvar d ⟨N,j,i,true⟩ = S_ji/2`.
    This is Var(Re X_ji), which matches E|X_ji|² = S_ji split equally between the real and
    imaginary parts.
  - In addition, `map_lin_Xmat` proves that for fixed `A` the law of `lin N A ∘ Xmat d N` under
    `P d` is exactly `gaussianReal 0 (v N A)`. So `v` is the exact conditional variance, not just
    an upper bound.
- **(T2) trivial witness:** `E = univ`, `A = 0`, `c = 0` instantiates the theorem (an `example`).
- **(T2) nonzero witness (`nonzero_witness`):** `A ≡ single i0 i0 1` with `i0 = (0, ⟨0, W_pos⟩)`,
  `E = univ`, `s ≡ 0`, `t ≡ 1`, `K ≡ 1` (so Δ = 1), and `c = v N A = S_{i0 i0} > 0`
  (`Sblk_diag_pos`). This works for every `N`, `k` and every `d : Dims`. It is nondegenerate:
  `c > 0` and the variable is a genuine Gaussian with variance `c`. The witness does not rely on
  any quantity being astronomically large.
- (T1) is satisfied by every instance built for (T2)/(T3), for example `Y = A` constant and
  `F = exp(r·√Δ·lin)`.
- (T3) is satisfiable. With constant `A`, the untruncated variable is Gaussian and hence
  integrable (for example, it is implied by `integrable_exp_mul_X`-type bounds).
- There are no `N = 0` or empty-index loopholes. `d.Idx N` is nonempty (`L ≥ 3`, `W > 0`), and
  the statements hold for every `N`, `k`. No hypothesis is hidden in a structure field: the only
  structure is the standing `Dims`. There is no cycle: T2 and T3 use T1 in the same file, and
  otherwise only earlier accepted results.

## 4. Dependencies

These are all accepted and already on `main`:
- T1481 `GridPath.lean` (`filt`, `Ωg`, `Pg`, `step`, `indep_incr`, `map_incr`; merged `ef7f0e4`,
  root import at `RBM1D.lean:511`).
- `RBM1D/Gauss/LinearForm.lean` (`map_sum_const_mul_coord`, `linVar`, `lintegral_indep_pair`; root
  import `RBM1D.lean:228`).
- `Model.lean` (`gvar`, `Xentry`, `Xmat`, `P`, `P_map_eval`).
- Mathlib (`HasCondSubgaussianMGF`, `Kernel.HasSubgaussianMGF.of_rat`, `condExpKernel_comp_trim`,
  `condExp_ae_eq_trim_integral_condExpKernel`, `mgf_gaussianReal`, and others).

No external input beyond these.

## 5. Build and axioms (audit worktree)

- `lake build RBM1D.Gauss.GridMarkov`: `Build completed successfully (3708 jobs)`. The only
  warning from this file is at `GridMarkov.lean:400:78`: unused variable `hc` in the private
  `integrable_exp_mul_X`. It is harmless.
- `lake build RBM1D`: `Build completed successfully (9635 jobs)`. No `sorryAx` appears in either
  log. GridMarkov is not root-imported; the ticket says root import: none.
- `#print axioms` for `condExp_freeze`, `hasCondSubgaussianMGF_linear` and
  `condExp_linear_eq_zero`: `[propext, Classical.choice, Quot.sound]`.
- `grep` finds no `sorry`, `admit` or `axiom` in `GridMarkov.lean`.

## Notes for the dispatcher (not defects)

1. (T3) signature differs from the ticket's literal "(T2) hypotheses + integrability". The
   delivered form implies the literal form (compiled as `T3_literal`).
2. The `Im` variant of (T2) is a 3-line corollary through `-I • A` (compiled as `T2_im`). It is
   not a separate public declaration.
3. `StandardBorelSpace β` in (T1) is unused. It was kept to match the ticket.
