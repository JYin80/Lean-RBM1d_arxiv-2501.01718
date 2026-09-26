Auditor model: claude-opus-5-5

# T1526 audit — G1c P0(a)(b) judgement report

Audited: `docs/reports/T1526-prove.md` (first pass, written 2026-09-26 12:18 UTC).
Ticket: `docs/tickets/T1526.md`. Audit written 2026-09-26 12:29 UTC.
This audit is the independent review required by supervisor 2026-09-26-1120 condition 1 (§2A).
I re-derived every inequality below from the paper text (`paper/250520-YinJun-v2.pdf`, pp.17–20,
24, 33, 48, 50, 53–54, 63–72, 76, 78–80, extracted with pypdf). I checked the Lean citations by
signature only.

Branch `t/T1526`: no commits and an empty diff against `main`. This is a report-only ticket, so
there is no module to build and no axiom audit. Acceptance format: first line
`Prover model: claude-opus-5-5` — OK. (T1)–(T3) are present and cite the paper by equation and page — OK.

## Verdicts

| Target | Verdict |
|---|---|
| Math preflight / Step 0 (the gap, the Lean usage of `X 2`, the charge symmetries) | PASS |
| P0(a), search for a threshold-free argument | PASS with correction C2 (the conclusion is overstated; this does not affect the result) |
| P0(a), n=2 threshold bootstrap for σ=(+,+)/(−,−) | **PASS** — complete at paper level. No circularity. Every deterministic bound is re-derived below. Correction C1 fixes one Lean citation. |
| P0(b), sharp Ξ^{(L−K)}_{u,1} ≺ 1 for both charges | **PASS** |
| (T3) plan effect, delta wording, estimate | PASS with corrections C3 and C4 (both minor) |

**Overall: PASS.** C1–C4 must go into the PP ticket specs and into the delta entry. None of them
changes the mathematics.

## 1. Step 0 — re-checked

- p.70: "By (2.76), S(m,l,s,u,t) holds for any l and m ≤ 2". (2.76) and (2.69) (p.24) are stated
  for σ=(+,−) only. (5.76) (p.64) defines Ξ^{(L−K)}_{t,m} as max_{σ∈{±}^m}. So the gap is real.
- p.72 (Step 4), "By (2.76) and (4.5) … Ξ_{t,2} ≺ (Wℓ_tη_t)^{1/4}", has the same restriction.
- Lean: `S_all` (Step3.lean:594) takes `h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S m l` and feeds `h12 2 3` to
  `S_of_S` (:502). `xiLK_two_le` (:473) uses `S … 2 3`. Confirmed.
- Charge symmetries, checked by hand:
  - L_{(−,−),(a,b)} = Tr(G*E_aG*E_b) = conj Tr(E_bGE_aG) = conj L_{(+,+),(a,b)}.
  - K_{(−,−)} = W^{-1}m̄²Θ_{tm̄²} = conj K_{(+,+)} by (2.58), since S is real.
  - L_{(−,+),(a,b)} = L_{(+,−),(b,a)} by cyclicity.
  - So (−,−) is deterministically equivalent to (+,+), and (−,+) is covered by (2.76).

## 2. P0(a)

### 2.1 The dispatcher's points (report §1.1)

1. **Ward loop.** Lemma 3.6 (3.12)/(3.13) (p.33) with σ=(+,+,−) gives the stated identity.
   - Rescaled: Ξ_2(+,+) ≤ Ξ_2(−,+) + 2Wη_u·ℓ_uW^τ·Ξ_3A^{-3}·A² = Ξ_2(−,+) + 2W^τΞ_3, using Wℓη = A.
   - (5.78) with n=3, l_K=3 gives the term Ξ_2A^{-3}η^{-1}.
   - Lemma 5.11 Case 1 then gives back C W^{Cτ} log N · Ξ_2 linearly.
   - The coefficient is > 1, so the loop does not contract. Confirmed.
2. **Cauchy–Schwarz.** |G_ijG_ji| ≤ (|G_ij|²+|G_ji|²)/2 gives |L_{++}(a,b)| ≤ max L_{+−}.
   - (5.73) gives max L_{+−} ≺ A_u^{-1}.
   - |K_{++}| ≤ CW^{-1} ≤ CA_u^{-1}, by (2.58) and ℓη ≤ 1.
   - So Ξ_2(+,+) ≺ A_u, and Ξ_2²/A ≺ A_u is critical. Confirmed.
3. (2.68) (p.24) is a max over σ, so Ξ_{s,2}(+,+) ≺ 1. Confirmed.
4. **n=2 hierarchy for σ=(+,+).**
   - In (5.15), Σ_{l_K>2} is empty for n=2.
   - (5.13) with (k,l)=(1,2): by Def. 2.10 items 2–3 (p.17), both cut pieces have length 2 and charges (σ_1,σ_2) = (+,+). This agrees with (2.55) (p.20). So the quadratic term is a self-product.
   - (5.79) at n=2 gives W·ℓ·Ξ_2²A^{-4} = Ξ_2²A^{-3}η^{-1}.
   - Lemma 5.11 (p.65) needs only (5.82). Its proof does not use n ≥ 3. Confirmed.
5. Neither Ψ(2,0) nor the CS bound closes Ξ_2²/A. Confirmed, see 2.2(d).

### 2.2 Threshold-free options (report §1.2)

- (a) An a-priori bound A^{1−c} would self-improve. No such bound exists: it would need 2-loop fluctuation averaging, which the paper does not contain. Agreed.
- (c) The G² = ∂_zG route controls only row sums. Agreed.
- (d) The ladder algebra, re-derived with e = b^{4−k}, A ≥ R²b³:
  - Ψ(2,k−1)²/A ≲ Ψ(2,k) needs e² ≲ b³ + Rbe.
  - This holds for k ≥ 3. It fails for k=2 (b⁴ vs b³(1+R)) and for k=1 (Ψ(2,0)²/A ≈ R²A_u).
  - I also checked that S(2,2) ⇒ S(2,3) works without a threshold, while S(2,1) ⇒ S(2,2) fails. So the ladder cannot start from any available a-priori level. Agreed.
- (e) Use table. I checked (5.92), (5.96)–(5.100) (Q only for n−1 ≥ 3), (5.119) and the Lean `hsmall`/`hquad2`/`S_all`. The linear `max_{k<n}Ξ_k` term forces Ξ_2 ≲ A_s^{1/2}. Agreed.
- **(b) Correction C2, see §5.** The dismissal of linearization plus Grönwall is correct only for the ≺-max-norm linearization.

### 2.3 The bootstrap (report §1.3) — re-derived term by term

Units: J_j = A_{u_j}²·max|(L−K)_{u_j,(+,+)}| = Ξ_2(+,+)(u_j). Threshold θ_j = A_{u_j}^{1/2}. Stopping time τ = min(first hit of J ≥ θ, first failure of the good set). A_u is antitone in u (`flowScale_antitoneOn`), so A_{u_τ} ≤ A_{u_j} for j ≤ τ.

- **(B) Kernel.** For σ=(+,+), both edges have ξ = m² (5.16)/(5.17).
  - By (5.18), each edge factor is I + (t−u)ξSΘ_{tξ}.
  - |1−tm²| ≥ c(κ), so by (2.52) Θ_{tm²} has O_κ(1) ℓ¹ rows. This is p.20 ("short edge … ℓ¹ norm of order one") and p.80 (proof of Case 1: Σ_{b1}|Ξ_1| = O(1)).
  - So Σ_b|U_{u,t,(+,+)}(a,b)| ≤ C_U(κ), with no decay or sum-zero needed. Lean `sum_norm_edgeKer_sub_one_le_short` (KernelDecay.lean:1112; hypotheses hξ ‖ξ‖≤1 and κ ≤ ‖1−tξ‖) fits. Correct.
- **(A) Initial term.** A_{u_τ}²|U A_0| ≤ C_U A_s² max|A_0| = C_U J_0, and J_0 ≺ 1 by (2.68). Correct.
- **(C) Quadratic.**
  - On {j<τ}, the b_1-sum is restricted by length-2 decay (Lemma 5.9, max over σ, p.64) and b_2 by S.
  - |primBil| ≤ C W^τ θ_j² A_{u_j}^{-3}η^{-1} + tail.
  - With θ² = A this gives A_{u_τ}²|·| ≤ C W^τ/η_{u_j}. Correct.
- **(D) E^{(G̃)}.**
  - (2.47) (p.18) has the factor ⟨G̃(σ_k)E_a⟩ for both charges, times the 3-loop G_k^{(b)}∘L of charge (+,+,+).
  - With (G1) Ξ_1 ≤ N^ε, (G2) Ξ^L_3 ≤ N^εR² ((2.73): A²·(ℓ_u/ℓ_s)²A^{-2}) and 3-loop decay, the term is C W^τ N^{2ε} R² A^{-2}η^{-1}.
  - With only Ξ_1 ≺ A^{1/2} one would get R²A^{1/2} log N, which exceeds θ. So the sharp Ξ_1 is necessary. Correct.
- **Time sum.** Σ_jΔ/η_{u_j} ≲ log N, since η_u ∝ (1−u) and 1−t ≥ N^{-C}. Correct.
- **(E) Martingale.**
  - The conditional variance of the linear Gaussian increment at H_j is a PSD form v.
  - Its square root is a seminorm, so v(Σ_b w_bX_b) ≤ (Σ|w_b|)² max_b v(X_b). Only the diagonal (5.22) is needed.
  - At n=2 this is 2n+2 = 6-loops, and (5.81) gives v ≤ C W^τ Ξ^L_6 A^{-4}η^{-1} with Ξ^L_6 ≤ N^εR^5 ((2.73)).
  - So A^4 Σc_j ≲ W^τN^εR^5 log N, and the martingale contribution is ≲ N^ε R^{5/2}. Correct at paper level, because the report defines M_k per fixed target k with c_j summed over j<k and takes a union over k. See C1 for the Lean citation.
- **(F) Second order / remainder.** Polynomially small once K = N^{C(D₁)} is chosen after D₁. Correct. The scaling is spelled out in C4.
- **Closure.**
  - Out ≲ N^{Cε}W^τ log N (1 + R² + R^{5/2}).
  - θ_τ ≥ A_u^{1/2} ≥ R A_s^{3/8} (`Scales.le_A`).
  - R^{3/2} ≤ A_s^{3/16} (R² ≤ A_s^{1/4}, `scale_facts`).
  - So Out < θ_τ once N^{Cε}W^τ log N < A_s^{3/16}, which holds because A_s ≥ A_t ≥ N^c (gained Cond272). Correct.
- **τ = K.**
  - `min_firstHit_eq_of_at` (GridBootstrap.lean:367) matches exactly: hypotheses `hgood` (good set at all j ≤ K) and `hat` (J_τ < θ_τ).
  - No circularity: the bounds at the random target use the good set and the threshold only at indices j < τ. {j<τ} is F_j-measurable. The fresh increment is controlled by the conditional variance at H_j.
  - The τ=0 case is excluded by J_0 ≤ N^ε < θ_0. Correct.
- **Closedness.**
  - The (+,+) n=2 equation involves only (+,+) itself (Θ-term and self-product), 1-loops, (+,+,+) 3-loops and 6-loops. No other 2-loop charge enters, so a single threshold process suffices. (−,−) follows by conjugation. Correct.
- **Output.**
  - 1 + R² + R^{5/2} ≤ 3R^4 ≤ 3A_s^{1/2} ≤ 3Ψ(2,l) for every l, by (5.108) (p.70). This is S(2,l) on (+,+)/(−,−).
  - (+,−)/(−,+): (η_s/η_u)^4 ≤ ((1−s)/(1−t))^4 ≤ A_t^{2/15} ≤ A_s^{1/2} by (2.72). This needs (2.72) itself (report open issue 4). Correct.
- **Dependencies (no cycle).** (G2),(G3) come from Step 1 (2.73). (G4) and P0(b) come from Step 2 ((2.75),(2.76)). No Step-3 output is used.
  - Lean dependencies not yet accepted: T1523 `discrete_hierarchy_step_n` (not found in the tree; the report correctly marks it "still proving"), P4 decay sets, and PP-5/generic P5.
  - These are Lean prerequisites of the PP tickets, not gaps in the paper argument.
- **Vacuity / witness.** The good-set items and the threshold are all satisfied with high probability by accepted Step-1/2 outputs. There is no N=0 or collapsed-window device. K = N^{C} is polynomial, so the union bounds are legitimate.

### 2.4 Lean targets (report §1.4)

PP-1…PP-9 are precise enough to serve as ticket targets. Fixed parameters come before ∀ᶠ N, and K is chosen after D₁. I verified that these cited declarations exist with compatible signatures:
`min_firstHit_eq_of_at`, `uker_decay_le_nonAlt` (hk : σ k = σ (k+1)), `sum_norm_edgeKer_sub_one_le_short`, `norm_Uker_apply_le`, `duhamel_telescope_stopped`, `stopped_duhamel_cheb_tail`, `stopped_duhamel_det_bound`, `azuma_complex`, `grid_expansion_all'`, `isStoppingTime_min_firstHit_grid`, `map_H_eq`, `etaT_inv_le_of_hreg`, `unifDomIcc_of_forall_stochDom`, `unifDomIcc_mul_scale`, `stochDom_timeIcc_of_unifDom_const`, `highProb_grid_of_flow`, `flow_S_one'`, `Gsig_conjTranspose`, `flowScale_antitoneOn`, `stepErr_le_unif`.

## 3. P0(b) — re-checked

- For n=1, K_{u,±,a} = m or m̄ (p.19). So (L−K)_{u,(±),(a)} = ⟨(G−m)E_a⟩ or its conjugate.
- (4.4) holds by (2.75) and A_u ≥ N^c.
- (4.5) (p.48) gives max_a|⟨(G−m)E_a⟩| ≺ max L_{(+,−)}.
- (5.73) (p.63), which uses the K bound (2.58)/(2.52), (2.76) and (2.72), gives max L_{(+,−)} ≺ A_u^{-1}.
- Hence Ξ^{(L−K)}_{u,1} ≺ 1 for both charges. This is exactly the paper's p.65 remark under (5.80) ("with (2.76), Ξ^L_{u,2} ≺ 1").
- (5.80) needs this sharp Ξ_1 at every Duhamel time, i.e. a good-set item at every grid point. Correct.

Lean route:
- `detAvgIBP_stochDom_of_localLaw_complete` (DetAvgIBPFlow.lean:274) has no hypothesis beyond `hll : LocalLawUnifIcc d E u u Ψ` and scalar side conditions. Its conclusion is ‖Tr((G−m)Eblk b)‖ ≺ Ψ².
- `lkErr_one_eq_norm_trace` (Eq45Flow.lean:89) holds for both charges.
- With Ψ = scale^{-1/2} this gives scale·lkErr ≺ 1.
- The paper reads the control from (5.73) (Ψ² = max L_{+−}); Lean reads it from (2.75). The two agree up to W^{-1} ≤ A^{-1}. Acceptable.
- The report's three corrections to T1525 are right:
  - `norm_lkErr_one_le` (StepGlue.lean:125) bounds lkErr by the entry bound c, i.e. only the weak Ξ_1 ≺ A^{1/2};
  - `localLawUnifIcc_of_localLawFlow` (GoodSetFlow.lean:230) needs a singleton-interval restriction, and the `_scales` variant has the wrong (non-tight) Ψ;
  - `highProb_grid_of_flow` needs a continuum-simultaneous input.
- The PP-1 estimate of 1 ticket is plausible.

## 4. (T3)

- The plan consequences are sound: supervisor 1a stands for Lemma 5.14 (n ≥ 3), a new PP block sits upstream of `S_all`, P4 needs the n=2 bounds, and P3 needs the diagonal QV only. So is the independence of P5's statement from PP (the X 2 bounds enter as premises).
- Step 4 remark, checked: (5.125) at n=2 (+,+) is self-quadratic. With the PP output, Ξ_2²/A ≺ R^5/A_u ≤ R³A_s^{-3/4} ≪ 1. Correct.
- Delta T1526a wording: accurate. It states the paper's gap, the (+,−) fix via (2.72), and the (+,+) added argument with the right stopping rule and inputs.
- Estimate arithmetic: 35–45 + 2 + 6–10 = 43–57, and ×1.3 gives ≈ 56–74. Consistent, except for C3.

## 5. Corrections (carry into the PP ticket specs and the delta entry; they do not reopen P0)

- **C1 (Lean citation, needed before PP-7 is specified).**
  - §1.3(E) and PP-7 cite `stopped_duhamel_azuma_tail(_union)` at GridDuhamelTail.lean:394. Line 394 is the original (T1) sup-norm lemma. Its docstring says "does not suffice … No consumer may use it". It sums c_j over all j<K, which gives the endpoint scale A_u^{-2}.
  - At an early τ, A_{u_τ}²/A_u² can reach A_s^{1/2}/R⁴. Under `Scales` alone this breaks the closure when R ≈ 1: one needs A_s^{3/2}R^{5/2}N^ε < A_u², while only A_u² ≥ R⁴A_s^{3/2} is guaranteed.
  - The report's own per-k construction is the correct one. Its Lean form is `stopped_duhamel_azuma_tail_fixed` (:313) plus `stopped_duhamel_azuma_union` (:347), with k-dependent constants c k a j. The name `stopped_duhamel_azuma_tail_union` does not exist.
- **C2 (the threshold-free conclusion is overstated).** The claim that no threshold-free argument exists with the paper's internal tools (§1.2 conclusion, Summary row 1) is too strong. There is a Ward row-sum linearization:
  - Σ_b|L_{++}(a,b)| ≤ ½W^{-1}[Tr(GE_aG*) + Tr(G*E_aG)] = W^{-1}Im Tr(GE_a)/η, and Σ_b|K_{++}(a,b)| ≤ CW^{-1}.
  - So on the good set, |E^{((L−K)×(L−K))}(a)| ≤ (C(κ)/η_u)·max|(L−K)_{++}|. This bound is exact and has no N^ε or W^τ loss.
  - It gives a *linear* pathwise Grönwall with a good-set stopping time only. Its growth factor is ((1−s)/(1−t))^{C(κ)}.
  - This closes when the step ratio (1−s)/(1−t) ≤ N^{δ(κ)} — the only regime used by the proof of Lemmas 2.18–2.20 (p.24, 1−s_k = W^{-kτ'}). It does **not** close under the general (2.72) hypothesis of Theorem 2.21, on which Lean's `Scales`/Cond272 is built: there the factor can be A_t^{C(κ)/30}.
  - So "a threshold is necessary" is correct *for Theorem 2.21 as stated and formalized*. The sentence should be qualified that way.
  - This does not change the plan's cost: the threshold route reuses the T1519/T1520 skeleton. But the supervisor's §4 review should know that a small-step restatement is the alternative.
- **C3 (ticket count).** §1.4 says "Count: 7–11". The components listed there (PP-7 can be 0, PP-5 0–2, PP-6 1–2) add up to 6–10, plus 0–1 for the P4 extension. §T3 and the Summary say 6–10. Use 6–10 (+0–1) throughout.
- **C4 (remainder scaling, PP-7 spec).** "(F) ≤ N^{-1}" must hold after multiplication by A_{u_τ}² ≤ A_s² ≤ N². So the unscaled remainder target is N^{-3}, with K chosen accordingly.
- **C4′ (delta precision, optional).** In T1526a (iii), add that p.72's "Ξ_{t,2} ≺ (Wℓ_tη_t)^{1/4}" for (+,+) follows from the (iii) output and (2.72): R ≤ ((1−s)/(1−t))^{1/2} ≤ A_t^{1/60}, so R^{5/2} ≤ A_t^{1/4}. Alternatively it follows from the Lemma 5.11 (n=2) bound transfer, which gives ≺ 1.

## 6. G1c gate

P0(a) and P0(b) are closed at paper level. S(1,l) and the sharp Ξ_1 follow from (2.75)+(4.5)+(5.73). S(2,l) on (+,−)/(−,+) follows from (2.76)+(2.72). S(2,l) on (+,+)/(−,−) follows from the fully specified n=2 threshold bootstrap, and (−,−) by conjugation.

Supervisor condition 1 (an independent audit of P0) is therefore met. But supervisor §4 still applies: (+,+) *does* need a Step-2-type stopping time. So the supervisor's re-estimate review of this report (with C1–C4 folded in) must happen before any P5 ticket is released.
