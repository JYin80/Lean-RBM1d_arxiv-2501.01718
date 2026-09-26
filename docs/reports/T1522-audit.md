Auditor model: claude-opus-5-5

# T1522 audit: Lemma 7.3, (7.14)/(7.16), pointwise (`RBM.Gauss.Q716`)

Branch `t/T1522` @ `4424283`, worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1522`, audited 2026-09-26T11:22Z.
Diff against `main`: one added file, `RBM1D/Gauss/Q716Pointwise.lean` (142 lines). This is the ticket's only writable file. No existing file is touched, so no frozen signature is touched.

## Verdicts

| Target | Verdict |
|---|---|
| (T1) `uker_decay_le`, (7.14) | **PASS** |
| (T2) `uker_decay_le_nonAlt`, (7.16) Case 1 | **PASS** |
| (T3) `uker_decay_le_sumZero`, (7.16) Case 2 | **PASS** (see paper-delta follow-up D1(ii)) |
| (T4) `uker_preserves_decay` (optional) | not delivered. The ticket marks it optional, so it has no verdict and does not block. |

**Overall: PASS.** There is one follow-up for the dispatcher: a paper-delta entry (D1 below). The ticket's sole-writable-file rule did not let the prover write that entry, and it does not let me write it either.

## 1. Math preflight
`docs/reports/T1522-prove.md` puts Step 0, the §10b reuse trace and a per-target math preflight (T1/T2/T3 PASS, T4 not attempted) before the Lean sections ("Declarations added", "Build", "Axioms"). Its first line is `Prover model: claude-opus-5-5`. OK.

## 2. Statement vs paper (Lemma 7.3, pp.78–80)
All three theorems are thin wrappers. They specialise the accepted `Hierarchy/KernelDecay.lean` lemmas `norm_Uker_fastDecay_le` (l.1304), `norm_Uker_fastDecay_le_of_eq` (l.1599) and `norm_Uker_fastDecay_le_sumZero_sigma` (l.1615) to `ξ = xiOf (mSigma E) σ`. Those lemmas came from T51+T55 under paper-delta #35: `K = W^τ`, `δ = W^{-D}`, `η_u → 1-u`, `ℓ_u → ellHat`.

- **Hypotheses.** The theorems assume `0 ≤ s ≤ t < 1`, `|E| < 2`, `n ≥ 2` (T1, T3; T2 allows every `n ≥ 1`) and `L ≥ 3`. (7.13) becomes `FastDecay L (ellHat L s * K) δ A`, i.e. `∃ i j, ℓ_s K ≤ zdist(a_i - a_j) ⇒ ‖A a‖ ≤ δ`. That is exactly (7.13) with `W^τ → K` and `W^{-D} → δ`. `‖A‖_max` becomes `∀ b, ‖A b‖ ≤ M`. (7.15) becomes `SumZeroAt L 0 A` (`∀ x, Σ_{b : b_0 = x} A_b = 0`), which is the paper's `∀ a_1` with `0 : Fin n = a_1`. T3 also assumes `0 ≤ t`. That follows from `hs0` and `hst`, so it is redundant and harmless.
- **Main term, T1.** `cKer n · K^n · (ℓ_t/ℓ_s) · ((1-s)ℓ_s/((1-t)ℓ_t))^n · M`. This matches (7.14), since `η_s/η_t = (1-s)/(1-t)`.
- **Main term, T2.** `cKerShort n √κ · K^n · ((1-s)ℓ_s/((1-t)ℓ_t))^n · M`. The exponent is `n` and there is **no `ℓ_t/ℓ_s` factor**, which matches (7.16).
- **Main term, T3.** `cKerSumZero n · K^{2n} · (…)^n · M`. The exponent is `n` and there is **no `ℓ_t/ℓ_s` factor**. `K^{2n}` is still a `W^{C_nτ}` factor (accepted in #35: "Case 2 不要求交替 σ, 代价 K^{2n}"). Case 2 holds for every σ, so it is stronger than the paper's proof, which first reduces to alternating σ.
- **Cyclic reading of σ_{k+1}.** `xiOf m σ i = m(σ i) · m(σ (i+1))` (`Hierarchy/Kernel.lean:186`) uses `i + 1 : Fin n`, which wraps. The T2 hypothesis `σ k = σ (k+1)` in `Fin n` is the paper's `∃ k, σ_k = σ_{k-1}` (1 ≤ k ≤ n, with σ_0 = σ_n) after the shift k ↦ k−1. I compiled a check of the wrap case: σ = (T,F,T) with `k = 2`, where `2 + 1 = 0` in `Fin 3`, instantiates T2. For `n = 1` the hypothesis holds trivially and `ξ = m²`, so the statement stays true. That is a harmless generalisation of the paper's `n ≥ 2`.
- **Constants** (`KernelDecay.lean:1205–1225`). `cKer`, `cKerSumZero` and `cKerSumZeroErr` are functions of `n` alone. They are built from the absolute numerics `cWin`, `cLip`, `cShort`, `cTwo52`, `cZero` and `zetaTwoInt`. `cKerShort n √κ` with `κ = min(2-|E|,1)` also depends on the fixed energy E, through the bulk gap. That dependence is real: `|1 - t m²| → 0` at the spectral edge. None of the constants depends on **N, W, L, s or t**.
- **Error term: difference from the literal paper wording.**
  - The paper writes `W^{-D+C_n}`.
  - T1 and T2 have `((1-s)/(1-t))^n · δ`.
  - T3 has `cKerSumZeroErr n · L^n · ((1-s)/(1-t))^n · δ`.

  These factors are the paper's own proof losses made explicit. In the paper's proof, the far-region sums in (7.22)–(7.24) cost `η_s/η_t` per Ξ factor, and up to `L^{n-1}` summed terms, and both are absorbed into `W^{C_n}`. Under (2.2), `W ≥ N^{1/2+c}`, so `L = N/W ≤ W` and `L^n ≤ W^n`. On the paper's time range `(1-s)/(1-t) ≤ poly(N) ≤ W^{C}`. So with `δ = W^{-D}` and D free, each error term is `≤ W^{-D+C_n}` in the paper's regime. Outside that regime the literal wording is false: the prover's constant-tensor example `A ≡ δ` with real ξ gives `δ((1-s)/(1-t))^n` as t → 1. The explicit form is therefore the correct formalisation. It is **not** an N-dependent constant in the sense of the ticket's failure signal, because the main-term constants do not depend on N.
  - **D1 (documentation defect, not a RETURN).** Paper-delta #35 records `W^{-D} → δ` and "显式常数代 ≺", but it does not list (i) the `((1-s)/(1-t))^n` multiplier on δ, (ii) the `L^n` multiplier on δ in Case 2, (iii) the E-dependence (κ) of the Case 1 constant, or (iv) the Case 1 index shift σ_{k-1} ↔ σ_{k+1}. The prove report says #35 "already covers exactly this discrepancy". That is inaccurate for (i)–(iii), and the report and the module docstring never mention the T3 `L^n` factor. **Dispatcher action:** append a delta tagged `T1522a` that records (i)–(iv). These are exactly the losses a downstream G1c consumer must absorb: it needs `L ≤ W^{O(1)}` and a polynomial bound on `(1-t)^{-1}` wherever it uses the T3 error term.
- **Quantifier order.** The statements are deterministic, with no `∀ᶠ N`. Every parameter is universally quantified before the bound. OK.

## 3. Vacuity, hidden hypotheses, cycles, witnesses
- There is no structure field and no hidden hypothesis. Every hypothesis is visible in the signature: `FastDecay` and `SumZeroAt` are plain `Prop` definitions (`KernelDecay.lean:308,313`).
- **Witnesses.** The prover proved conjunction-style witnesses: `uker_decay_le_nonAlt_satisfiable` (σ ≡ true, n = 2) and `uker_decay_le_sumZero_satisfiable` (`witTensor L 0 1`, nonzero, `‖·‖ ≤ 1`, `(2,0)`-FastDecay, `SumZeroAt L 0`). I also compiled direct instantiations of the theorems themselves (scratch file, not committed):
  - T2 with n = 3, σ = (T,F,T), whose only equal cyclic pair is through the wrap (k = 2); E = 1, s = 0 < t = 1/2, K = 2, A = `witTensor L 1 1`.
  - T3 with n = 4, σ = (T,F,T,F), which is alternating (checked by `decide`: no k has σ k = σ (k+1), so Case 1 does not apply); E = 1/2, s = 0 < t = 1/2, A = `witTensor L 2 1`.

  Both compile. The witness is a nonzero tensor, `L ≥ 3` is arbitrary, the window has radius `2·ellHat` (not collapsed), and no astronomically large quantity is needed.
- **Boundary cases.** At `s = t` all ratios equal 1. The `N = 0` / empty-index loophole does not arise: `L ≥ 3` and `[NeZero n]` are required.
- **Cycles.** The dependency closure contains only already-committed modules.

## 4. Dependencies and the §10b reuse check
I computed the transitive constant closure of all five declarations with a Lean meta script (2367 constants). The `RBM` constants in it come only from `Defs.Dist`, `Defs.Semicircle`, `Defs.Block`, `Propagator.{Basic,Contour,Decay,DecayComplex}`, `Hierarchy.{Kernel,KernelDecay}`, `Gauss.Lemma514Q716` (the witTensor lemmas only) and the new file itself. I searched the closure for names containing `jStar`, `EarlyQVRate`, `h560`, `eGpm_le_rhs535` or `sorryAx`: **none**. Everything reused is deterministic and has constants independent of N, as shown in §2. The reuse is legitimate.

## 5. Build and axioms
- `lake build RBM1D.Gauss.Q716Pointwise`: Build completed successfully (3777 jobs).
- `lake build RBM1D`: Build completed successfully (9668 jobs). The root import is not yet added; it is added at merge.
- `#print axioms` for `uker_decay_le`, `uker_decay_le_nonAlt`, `uker_decay_le_sumZero`, `uker_decay_le_nonAlt_satisfiable` and `uker_decay_le_sumZero_satisfiable`: `[propext, Classical.choice, Quot.sound]` for every one.
- `grep` finds no `sorry`, `admit` or `axiom` in the new file.

## 6. Notes for merge and downstream
- Merge only `RBM1D/Gauss/Q716Pointwise.lean`, and add the root import per the instruction.
- D1: dispatcher paper-delta entry `T1522a` (see §2).
- T4 (`uker_preserves_decay`, Lemma 5.9 remark after (5.75)) has no Lean counterpart yet. If G1c needs it, it needs a separate ticket.
