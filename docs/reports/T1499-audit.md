Auditor model: claude-opus-5-5[1m]

# T1499 audit: is `h560` satisfiable, and what replaces it

Audited: branch `t/T1499`, head `ca712b8`, in the detached audit worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1499-audit`. The branch itself is checked out at `../RBM1D-wt/T1499`.
Prover report: `docs/reports/T1499-prove.md`. Diff vs `main`: exactly one new file,
`RBM1D/Hierarchy/H560Check.lean` (415 lines). No other file was touched, and no frozen signature changed.

## Overall verdict: PASS

| Target | Verdict |
|---|---|
| (T1) verdict on `h560` | PASS |
| (T2) replacement | PASS, with two spec corrections for the follow-up ticket (N1, N2) |
| (T3) compiled obstruction | PASS |

## 1. Preflight

The report's first line is `Prover model: claude-opus-5-5[1m]`. Section (a) has a math preflight for
each target, stamped 2026-09-25T20:20Z. The Lean commit `ca712b8` was made at 20:27:52Z, so the order
is consistent. PASS.

## 2. (T1): statement vs paper, and the Ward argument

Paper, checked against the text of `paper/250520-YinJun-v2.pdf`:
- p. 61 (5.60): the 3-loop is bounded `≺` by the max of the **actual entries** `|G_{x1y}||G_{yx2}||G_{x1x2}|`.
- p. 61 (5.61): the `(J*)^{3/2}(T T T)^{1/2}` bound is stated **only in case (2)**. That is
  `min_i|a_i-b| ≥ ℓ*/2` and `|a1-a2| ≥ ℓ*`, and the proof goes through (5.31), which needs `|a-b| ≥ δℓ*`.
- Case (1) uses (5.56)-(5.59).
- The near-pair case `|a1-a2| ≤ ℓ*` uses (2.73)/(5.53) and (5.54) (p. 60).

The Lean `h560` (Step2FarInputs.lean, `eGpm_le_rhs535_of_jS` and `h535_of_jS`) asks for the case-(2)
bound with `Gm := gmOfJS` for every `b`. In `h535_of_jS` it asks for it for every pair as well,
diagonal included. So the report's diagnosis is correct: wrong domain (D1), and the entry maximum is
replaced by the far-field `√(jS·T)` also where that bound is false (D2). This mismatch is real.

I also confirmed the report's usage claim: `h560` enters `Lemma57.sum_far_le` only through
`Lemma57.case2_pointwise` (Lemma57.lean:506). That lemma requires all three separations `> ℓ*/2`.

Check of `jS ≤ J*`. (5.28)-(5.29) define `J* = max_ℓ max_{|a-b|≥ℓ}|L-K|/T(ℓ) + 1`. `Step2.jStar`
(APrimeSmoothPrefixCanonicalCore.lean:79) divides each pair by `T(zdist)`. Taking `ℓ = |a-b|` gives
`jS ≤ J*`. Correct.

Ward argument, checked by hand and also compiled:
- **Step 1.** `∑_b E_b = W⁻¹·1` and `G⁻G = (G-G⁻)/(2iη)` give `2iη∑_b L3(b,a,a) = W⁻¹(L_{++}-L_{-+})(a,a)`. Correct.
- **Step 2.** Symmetrizing gives `Re(L_{-+}-L_{++})(a,a) = ½W⁻²∑_{p,q∈I_a}|g_pq - conj g_qp|²`. Keep only `p=q` (`4(Im g_pp)²`), then apply Cauchy-Schwarz over the `W` sites of the block: the result is `≥ 2W⁻¹(Im⟨G E_a⟩)²`. Correct.
- **Step 3.** `Lemma57.sum_sqrt_tailT_mul_le` at `a₁=a₂=a` gives the right side. Its leading term is `168 jS^{3/2}/(Wℓ²η²)`. Correct.

Model-level part. This is on paper only, as the report says in (d)1. I rechecked it.
- **Kernel identity.** From (2.57)/(2.58) with `m² = w`, `Re w = 1-2s²`:
  `D(x) = 1/(1-x) - Re(w/(1-wx)) = 2s²(1+x)/((1-x)((1-x)²+4xs²))`. I verified this algebra. `D > 0` on `(-1,1)`, so dropping modes is legitimate.
- **Lower bound on `K`.** `η_u = (1-u)s` (`etaT`, Ward.lean:48). If `ℓ = L`, the `p=0` mode alone gives `(2/5)s³/A`. If `ℓ = (1-u)^{-1/2} < L`, the low modes give `≍ s²ℓ/W ≍ s³/A`. So `K_{+-}-Re K_{++} ≥ c s³ A⁻¹` holds.
- **Conclusion.** With (ii) and (iii), `h560 ⟹ c s³ A ≤ jS + N^ε + 337 jS^{3/2}`; I checked the constant `2·168+1`. (5.47) gives `J* ≺ (η_s/η_u)²`, and (2.72) gives `(η_s/η_u)^{30} ≲ A_u`. Hence `jS^{3/2} ≺ A^{1/10} ≪ A`, and `h560` is false w.h.p. for every `u` in the window.

The answer to the ticket's question ("no, except where `jS^{3/2} ≳ s³A`") is therefore supported:
- rigorously (compiled) in the deterministic regime `(s-κ/A)²Wℓ²η² > 168 jS^{3/2}(1+o(1))`;
- on paper, from (2.58), (2.68), (2.72) and (5.47), in the rest of the window.

The report's correction to the T1488/T1496 heuristic (`b = a₁`, far `a₂`) is plausible. It does not carry
any weight in the verdict, which rests on the Ward sum over diagonal/near instances. Both theorems do
require those instances:
- `h535_of_jS` via `b := ![a,b₁]`, `c := a`;
- `eGpm_le_rhs535_of_jS` via the family of pairs `(a,b₁)` at `b = a`.

## 3. (T3): the Lean file

Builds:
- `lake build RBM1D.Hierarchy.H560Check`: success (3770 jobs). No errors, and no warnings from this file.
- `lake build RBM1D`: success (9646 jobs). The root does not import H560Check yet; the ticket adds that import at merge.
- A scratch file importing both `RBM1D` and `RBM1D.Hierarchy.H560Check` elaborates without error, so there are no name clashes.

Other checks:
- No `sorry`, `admit` or `axiom` in the file.
- `#print axioms` for all 16 public declarations, i.e. the helpers plus `sum_gloop3_ward`, `two_inv_W_mul_sq_im_trace_le_re`, `sq_im_trace_le_sum_norm_gloop3`, `h560_diag_forces`, `sum_gmOfJS_diag_le`, `h535_h560_forces` and `not_h535_h560`, prints exactly `[propext, Classical.choice, Quot.sound]`.

What the file proves, and whether it is what the report claims:
- `sq_im_trace_le_sum_norm_gloop3` and `h560_diag_forces` are unconditional apart from `H` Hermitian and `0 < Im z`. `Gm` is arbitrary. This is the substantive necessary condition, and it cannot be vacuous.
- The instance in `h535_h560_forces` is `h560 ![a,b₁] a`. It unfolds to `‖L3[b₁,a,a]‖ ≤ gm(b₁,a)·gm(a,a)·gm(b₁,a)`, which is the `h535_of_jS` hypothesis verbatim at a fixed `u`. It is also exactly the `eGpm_le_rhs535_of_jS` hypothesis at pair `(a, b₁)`, `b = a`. The extra hypotheses are `hone` at `σ = true` and `hκ`: the first is already assumed by both theorems, and `hκ` is a mild sign condition. So this is a genuine necessary condition, not a weaker statement.
- `not_h535_h560` is the contrapositive under `hgt`. The statement matches the report's claim: `¬h560` in the deterministic regime.
- Nothing here feeds any other theorem.

Satisfiability of `hone ∧ hκ ∧ hgt`. This matters because `not_h535_h560` would be empty if these were
jointly impossible. There is no compiled witness. As the report notes, explicit deterministic `H` give
`jS ≍ A`, and then `hgt` fails. A witness needs the model: (4.5) for `hone`, and (5.47) for small `jS`.
The regime the report exhibits is nondegenerate: `s ≍ 1`, `jS ≤ N^δ`, `Wη ≥ N^{2δ}`, general dimensions,
no `N = 0` or empty window. I accept this for a diagnostic, negative result with no downstream consumer.
The unconditional core does not depend on it. See N3.

## 4. (T2): replacement

`eGpm_le_rhs535` (Step2FarInputs.lean:1116) is sound with an abstract `Gm`. It needs `h42` only on far
pairs, plus `hGm ≥ 0`. I confirmed the report's claim that only the instantiation `Gm := gmOfJS` is at fault.

**Option B, `eGpm_le_rhs535_of_jG`: sound and ticket-ready.** Its hypotheses are a subset of the old ones
(no `hK`, no `h560`), and the proof is deterministic. The three hypotheses of `eGpm_le_rhs535` are
discharged as follows:
- `h42` is `APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail` (general `B`; far pairs).
- `h531`: `re L_{+-}(x,y) ≤ W⁻²∑|G_pq|² ≤ gmBlk(x,y)²`. This is at most `gsqBlk(x,y)` (take `x' = x`, `SB x x ≠ 0`, and `gmBlk` is symmetric), which is at most `jG·T` by `APrimeJG.gsqBlk_le_jG_mul_tailT` (general `B`).
- `hJ` is `APrimeJG.one_le_jG`.

This route has no false hypothesis. It is the paper's own (5.60)→(5.61) order. The remaining obligation,
`jG ≤ N^{2ε}·jS` w.h.p., is a true statement: (4.2) plus (5.30)/(5.31). It is a genuine new ticket.
It does not relocate the `h560` gap, and `entry_bound_gauss`, `tailT_sub_le` and the `APrimeJG*`
infrastructure already exist.

**Option A, `eGpm_le_rhs535_of_jS'` with the case-(2) `h560'` and loss `c³`: sound by construction.**
It checks every hypothesis of `eGpm_le_rhs535` for the patched `Gm`, so it does not depend on how `h560`
is used internally. The `Λ` bookkeeping is correct: every non-case-(2) product is
`≥ Λ·min(Λ,q₀)² ≥ M ≥ ‖L3‖`. At `c = 1` the conclusion is verbatim the old one.

Spec corrections for the follow-up ticket. They do not affect the PASS:
- **N1.** The report cites `norm_gloop_three_le_gmBlk` (APrimeFirstCellEGFar.lean:140) as the `h560` for Option B ("all `b`, no hypothesis"). That lemma is stated only for `B := band Dims.exampleGrow`; the file has `private abbrev d := Dims.exampleGrow`. The general-`d` copy in `APrimeGeneralMovingDriftSourceGeneralDims.lean:245` is `private`. So the Option B ticket must re-derive it for general `B`, from `Lemma57.norm_gloop_three_le` (general) plus `APrimeJG.norm_Gsig_le_gmBlk` (general). That is about 20 lines, and the ticket must not cite the special-case lemma.
- **N2.** In the `hjG` chain, applying (4.2) at a neighbour `x' ∼ x` gives neighbour pairs at distance `≥ d-3`, not `d-2`. This is harmless: `tailT_sub_le` with `C = 3` gives `T(d-3) ≤ e^{√3}T(d)`.

## 5. Other notes

- **N3.** There is no compiled joint-satisfiability witness for `hone ∧ hκ ∧ hgt` (see §3). The model-level refutation is paper-only, as disclosed in report (d)1. If the dispatcher wants that half compiled, the Fourier lower bound on `K_{+-}-Re K_{++}` is about one ticket.
- **N4.** Paper-delta `T1499a` is proposed but not written, because it is outside the sole writable files. It is for the dispatcher to append.
- **N5.** Until a replacement is merged, keep `eGpm_le_rhs535_of_jS` / `h535_of_jS` banned (DECISIONS §10b). The audit supports this: their `h560` is false w.h.p. in the regime of use.
