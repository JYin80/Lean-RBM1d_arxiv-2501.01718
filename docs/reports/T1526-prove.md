Prover model: claude-opus-5-5

# T1526 — G1c P0(a)(b): S(2,l) on σ=(+,+)/(−,−), and S(1,l) (report only, no Lean)

Ticket: `docs/tickets/T1526.md` (repairer, judgement ticket). Sole writable file: this report.
No returning audit report exists (`docs/reports/T1526-audit.md` absent): first pass.
Written 2026-09-26 12:18 UTC. No `.lean` file was touched; no build was run (none required).

Materials read: `CLAUDE.md` §3; `docs/supervisor/2026-09-26-1120.md`;
`docs/claude-team/g1c-plan/G1c-plan-paper.md`; `docs/reports/T1525-prove.md`; the paper
`paper/250520-YinJun-v2.pdf` (text extracted with pypdf; the PDF page number equals the printed page
number, checked on pp.20–27, 48–80): pp.17–27 (Def. 2.10, (2.44)–(2.82)), pp.32–34 (Lemma 3.6),
pp.48–52 (Lemma 4.1, its proof, Step 1), pp.52–63 (§5.2 and §5.3: (5.10)–(5.73)), pp.63–73
(§5.4–§5.8: (5.74)–(5.136)), pp.74–80 (§6, Lemmas 7.1–7.3). Lean read (statements only):
`Hierarchy/Step3.lean` 1–640, `Loop/Split.lean` 340–375, `Gauss/GridBootstrap.lean` 355–400,
`Gauss/Q716Pointwise.lean` 60–120, `Hierarchy/StepGlue.lean` 120–150, `Gauss/Eq45Flow.lean` 80–110,
`Gauss/DetAvgIBPFlow.lean` 274–300, `Gauss/GoodSetFlow.lean` 215–300, `Flow/Hypotheses.lean` 350–370,
`Gauss/GridJStar.lean` 200–240, `Gauss/Lemma514Moment.lean` 100–160, `Hierarchy/Kernel.lean` 245–275,
`Hierarchy/KernelDecay.lean` 1105–1125, plus `grep` for declaration locations.

Notation: `A_u := Wℓ_uη_u` (decreasing in u), `A_s`, `R := ℓ_t/ℓ_s ≥ 1`, `Ξ_n := Ξ^{(L−K)}_{u,n}`,
`Ξ^L_n := Ξ^{(L)}_{u,n}` ((5.76), p.64). `b := A_s^{1/4}`. `Scales` (Step3.lean:353) gives
`A_u ≤ A_s`, `R²A_s^{3/4} ≤ A_u`, hence `R² ≤ b`, i.e. `R ≤ A_s^{1/8}` (`scale_facts`, Step3.lean:139).

---------------------------------------------------------------------------------------------------

## Summary of verdicts

| Target | Verdict |
|---|---|
| P0(a), threshold-free argument | **FAIL** — none of the five options closes (§1.2); a threshold is needed. |
| P0(a), minimal bootstrap | **PASS (fully specified, paper level)** — an n=2 threshold stopping-time argument on the grid, threshold `θ_j = A_{u_j}^{1/2}` on `Ξ_2(+,+)` only; output `Ξ_2(+,+) ≺ 1 + R² + R^{5/2} ≤ Ψ(2,l)` for every l (§1.3). The Lean side needs 6–10 new tickets (§1.4). |
| P0(b) `Ξ_{u,1} ≺ 1`, both charges | **PASS** — from (4.5)+(5.73) (paper) or (4.5) with control from (2.75) (Lean). T1525's route is confirmed with three corrections (§2). |
| Supervisor 1a (no threshold stopping time) | Stands for Lemma 5.14, n ≥ 3. It does **not** hold for S(2,l) on (+,+)/(−,−). Per supervisor §4 ("if (+,+) needs a Step-2-type stopping-time argument, pause, re-estimate, and request review before dispatching P5"), this report triggers that review. |

---------------------------------------------------------------------------------------------------

## Step 0 (read-only checks)

* **The gap.** p.70: "By (2.76), S(m,l,s,u,t) holds for any l and m ≤ 2." (2.76) (p.24) is stated for
  σ=(+,−) only; so is the hypothesis (2.69) of Theorem 2.21 (p.24). Ξ^{(L−K)}_{u,m} (5.76), p.64, is
  `max_{σ∈{+,−}^m, a}`. The same restriction affects p.72 (Step 4): "By (2.76) and (4.5) for
  (L−K)-loops of length 1 and 2 …, Ξ_{t,1} ≺ 1, Ξ_{t,2} ≺ (Wℓ_tη_t)^{1/4}".
* **Lean.** `Step3.flowXiLK … n = X.xiLK … n = lkMax·scale^n`, `lkMax = ⨆ LoopData (L N) n`,
  `LoopData = (Fin n → Bool) × (Fin n → ZMod L)` (T1525 (I4); Step3.lean:781–865). The raw-loop
  analogue `loopMax` (Loop/Split.lean:350) is `⨆ x : (Fin n → Bool) × (Fin n → ZMod L)`. So `X 2`
  ranges over all four σ. `xiLK_two_le` (Step3.lean:473) turns `S(2,3)` into `X 2 ≺ A_s^{1/2}`;
  `S_of_S` (:502) takes `hS2 : S … 2 3`; `S_all` (:594) takes `h12 : ∀ m l, m ≤ 2 → S m l` and feeds
  `h12 2 3` into every `S_of_S` call (:608).
* **Charge symmetries (used below).** Because G(−) = G(+)* (Hermitian flow; Lean `Gsig_conjTranspose`)
  and S^{(B)} is real symmetric:
  - `L_{(−,−),(a,b)} = conj L_{(+,+),(a,b)}` (Tr(X*) = conj Tr X, then cyclicity), and
    `K_{(−,−)} = conj K_{(+,+)}` by (2.58) (p.20). Hence `|(L−K)_{(−,−),a}| = |(L−K)_{(+,+),a}|`, so
    (−,−) is **deterministically** equivalent to (+,+).
  - `L_{(−,+),(a,b)} = L_{(+,−),(b,a)}` (cyclicity), likewise for K. So (2.76) covers (−,+).

---------------------------------------------------------------------------------------------------

## (T1) P0(a)

### 1.1 The dispatcher's five points, checked independently

1. **Ward loop — CONFIRMED (circular, not contracting).** Lemma 3.6 (3.12)/(3.13), p.33, with
   σ=(+,+,−) (σ_1=+, σ_3=−, so σ^± = (±,+)):
   `Σ_{a_3}L_{(+,+,−),(a_1,a_2,a_3)} = (2Wiη_u)^{-1}(L_{(+,+),(a_1,a_2)} − L_{(−,+),(a_1,a_2)})`, and the
   same for K. Subtracting gives
   `(L−K)_{(+,+),(a_1,a_2)} = (L−K)_{(−,+),(a_1,a_2)} + 2Wiη_u Σ_{a_3}(L−K)_{(+,+,−),(a_1,a_2,a_3)}`.
   With the (u,τ,D)-decay of Lemma 5.9 ((5.75), p.64) the a_3-sum has ≲ ℓ_uW^τ non-negligible terms
   of size ≤ Ξ_3A_u^{-3}, so `Ξ_2(+,+) ≤ Ξ_2(−,+) + 2W^τΞ_3(+,+,−) + W^{-D+C}`. The reverse link:
   Lemma 5.11 at n=3 ((5.83), p.65) contains `max_{k<3}Ξ_k ∋ Ξ_2(+,+)` **linearly**. The source is
   `[K∼(L−K)]^{l_K=3}` ((5.78), p.64). Cutting (+,+,−) at edges 1,2 gives the right piece (σ_1,σ_2) =
   (+,+) (Def. 2.10 item 3, p.17). The coefficient is O(1)·∫_s^t du/η_u ≍ log N. Together
   `x ≤ c + C W^τ log N · x`: the coefficient is > 1, so there is no contraction.
2. **Cauchy–Schwarz a priori bound — CONFIRMED, and it is exactly critical.** Take
   `L_{(+,+),(a,b)} = Σ_{i,j}G_{ij}(E_a)_{jj}G_{ji}(E_b)_{ii}` and weights `E_a(j)E_b(i) ≥ 0`. Then
   `|L_{(+,+),(a,b)}| ≤ (L_{(+,−),(a,b)}L_{(+,−),(b,a)})^{1/2}`, where `L_{(+,−),(a,b)} =
   Σ|G_ij|²E_a(j)E_b(i)` (p.23). (5.73) (p.63) gives `max L_{(+,−)} ≺ A_u^{-1}`. |K_{(+,+)}| ≤ CW^{-1}
   by (2.58), and W^{-1} ≤ A_u^{-1} because ℓ_uη_u ≤ (1−u)^{1/2} ≤ 1. Hence `Ξ_2(+,+) ≺ A_u`. This is
   better than (5.106) by the factor R but still critical: `Ξ_2²/A_u ≺ A_u`.
   (Side remark: CS alone gives `Ξ^L_2(+,+) ≺ 1`, i.e. (2.77) at n=2 for all σ, without S(2,l). But
   `S_of_S` needs S(2,·) at the Ψ-scale, see 1.2(e).)
3. **(2.68) holds for every σ — CONFIRMED.** p.24: `max_{σ,a}|L_{s,σ,a} − K_{s,σ,a}| ≺ A_s^{-n}`. So
   `Ξ_{s,2}(+,+) ≺ 1`.
4. **Lemma 5.11 at n=2, σ=(+,+) — CONFIRMED, and the quadratic term is a self-product.**
   - Lemma 5.11 (p.65) needs only (5.82): σ_k=σ_{k+1} for some k, read cyclically. (+,+) qualifies,
     and nothing in its proof uses n ≥ 3.
   - Which terms appear at n=2: in (5.15) (p.53) the sum Σ_{l_K>2} is empty, since l_K ≤ n = 2. The
     only l_K=2 term is Θ_{t,σ}∘(L−K) ((5.19), p.53), which is absorbed into U.
   - Charges in E^{((L−K)×(L−K))} ((5.13), p.53) for (k,l)=(1,2): the left piece has length
     k+n−l+1 = 2 and the right piece length l−k+1 = 2. Both contain σ_k and σ_l (Def. 2.10 items 2–3,
     p.17, example G^{(a),L}_{3,5}(σ) = (σ_1,σ_2,σ_3,σ_5), G^{(a),R}_{3,5}(σ) = (σ_3,σ_4,σ_5)). So both
     factors are (σ_1,σ_2) = (+,+).
   - A direct Itô computation agrees: the two resolvent derivatives produce ⟨G_1E_{a_1}G_2E_b⟩ and
     ⟨G_2E_{a_2}G_1E_a⟩.
   - Result: the term is `W Σ_{b_1,b_2}(L−K)_{(+,+),(a_1,b_1)}S_{b_1b_2}(L−K)_{(+,+),(b_2,a_2)}`, i.e.
     `Ξ_2(+,+)²/A_u`.
   - Λ := max_u Ξ^L_6 ≺ R^5 by (5.106) (p.69).
5. **Neither Ψ(2,0) nor the CS bound closes Ξ_2²/A — CONFIRMED; the A^{1/2}-threshold bootstrap works —
   CONFIRMED, with one addition.** The closure needs the **sharp** Ξ_1 ≺ 1 (P0(b)); with only Ξ_1 ≺
   A_u^{1/2}, the E^{(G̃)} term is ≍ A_u^{1/2}R² > threshold (see 1.3). Also, the dispatcher's
   "bounded Case-1 kernel" is available in an even simpler form: for σ=(+,+) **both** edges are short
   (ξ_1 = ξ_2 = m²). So `U_{u,t,(+,+)}` is bounded in max→max norm **without** decay or sum-zero
   hypotheses (1.3(B)).

### 1.2 Search for a threshold-free argument (the five options)

(a) **An a-priori bound A^{1−c}, c > 0.**
- It would self-improve: `x_{j+1} = x_j²/A + (terms ≤ R^{5/2})` goes A^{1−c} → A^{1−2c} → … and
  reaches ≤ A_s^{1/2} after ⌈log_2(1/(2c))⌉ bound-transfer steps. Each step is a Lemma-5.11(n=2)
  bound transfer with no threshold. So c > 0 would suffice.
- No such bound exists among the paper's internal tools. The only a-priori bounds on (L−K)_{(+,+)}
  are (5.106) (`A_uR`), CS (`A_u`, point 2) and (2.73) (on L, not L−K).
- Lemma 5.1 / (6.13) (pp.74–76) bounds L at t_2 by loops at t_1 and carries no fluctuation
  information.
- Getting the A^{-1−c} fluctuation size of L_{(+,+)} − K_{(+,+)} statically would need a
  fluctuation-averaging estimate for 2-loops (the analogue of (4.12), p.50, one level up). The paper
  has no such estimate, and CLAUDE.md §3.1 forbids importing one.
- **Does not close.**

(b) **Extra gain from the non-singular propagator ξ = m².**
- (2.52) (p.20) gives `Σ_b|(Θ_{tm²})_{ab}| = O_κ(1)`, because |1−tm²| ≥ c(κ) uniformly in t ∈ [0,1]
  when |E| ≤ 2−κ. Hence `‖U_{u,t,(+,+)}‖_{max→max} ≤ C(κ)` (proof of Lemma 7.3 Case 1, p.80; Lean
  `sum_norm_edgeKer_sub_one_le_short`, KernelDecay.lean:1112).
- Compared with Case 1 of (7.16) this gains (A_t/A_u)², which only improves the time integral: the
  kernel `(A_t/A_u)²/η_u` has ∫_s^t ≤ C instead of log N.
- The inequality becomes `f(t) ≤ c + C sup_{u≤t}f(u)²/A_u`. It closes only if f ≪ A a priori, and
  the best a priori bound is CS, `f ≲ N^εA` (point 2).
- Linearizing `f²/A ≤ N^ε f` and applying Grönwall gives `f ≲ (η_s/η_t)^{C N^ε}` — useless.
- **Does not close.**

(c) **G² = ∂_zG.** `Σ_b L_{(+,+),(a,b)} = W^{-1}⟨G²E_a⟩ = W^{-1}∂_z⟨GE_a⟩`. A Cauchy estimate plus
Ξ_1 ≺ 1 on a z-disc of radius ≍ η_u (itself a local law at non-flow spectral parameters) controls
only the **row sum** `P∘(L−K)_{(+,+)} ≺ ℓ_uA_u^{-2}`, not the pointwise max that (5.79)/`X 2` need.
**Does not close.**

(d) **A different induction order in (5.109).** Put S(2,k)(+,+) inside the ladder, using S(m,k−1).
The self-term requires `Ψ(2,k−1)²/A_u ≲ Ψ(2,k)`. In the variables of `ineq_quad` (Step3.lean:214):
with `e = b^{4−k}`, `Ψ(2,k) = b² + R e` and `Ψ(2,k−1) ≤ b² + R b e` (`psi_pred_le`, :314), and with
`A_u ≥ R²b³`, the three terms of the square satisfy
- `b⁴/A ≤ b/R²` — fine;
- `2Rb³e/A ≤ 2e/R` — fine;
- `R²b²e²/A ≤ e²/b` — this needs `e² ≲ b³ + Rbe`: true for k ≥ 3, false for k = 2 (`b⁴` vs
  `b³(1+R)`), and false for k = 1 (`Ψ(2,0)²/A ≈ R²A_u`).

So the ladder starts only at level 2 (`Ξ_2 ≲ R A_s^{1/2}`), and nothing reaches level 2 from the
a-priori level A_u. This agrees with supervisor §2A. **Does not close.**

(e) **S(2,l)(+,+) used only in a weaker form.** Every use:

| Place | What is used | Needed strength |
|---|---|---|
| (5.92) p.67 / (5.83) p.65, term `max_{k<n}Ξ_k` (source (5.78): `[K∼(L−K)]^{l_K=n}` has a length-2 L−K piece, which is (+,+) e.g. for σ=(+,+,−) cut at (1,2)) | Ξ_2(+,+) **linearly** in Ξ_n | final target Ξ_n ≺ A_s^{1/2} forces Ξ_2 ≲ A_s^{1/2} |
| (5.92), `Ξ_2·Ξ_n/A` (k=2 and k=n of (5.79)) | product | Ξ_2 ≲ A_u/A_s^{1/4} (see below) |
| Ward (5.96)–(5.100) p.68 | reduces to Ξ_{n−1}, and Q is used only for even n ≥ 4, so n−1 ≥ 3 | none |
| (5.119) p.71 | Ψ(2l_m,k−1) with 2l_m ≥ 4 for n ≥ 3 | none |
| Lean `S_of_S` `hsmall` (Step3.lean:517) with m=2 | `X 2 ≺ Ψ(n,k)` from S(2,k), for every k | → A_s^{1/2}(1+o(1)) as k grows |
| Lean `hquad2` (:528) via `xiLK_two_le` (:473) | `X 2 ≺ A_s^{1/2}` from S(2,3) | (math needs only A_u/A_s^{1/4}) |
| Lean `S_all` (:606), `xiLK_le`/`xiL_le_one_of` at n=2 | S(2,k) itself | A_s^{1/2} |

- The product term alone would tolerate `Ξ_2 ≲ A_u/b`, because Ψ(n,k−1)/Ψ(n,k) ≤ b
  (`ineq_quad_two`, :245). That is still sub-critical against the CS bound A_u.
- The linear term (row 1) needs the full A_s^{1/2} in the paper's own scheme.
- **Does not close.**

**Conclusion of 1.2: no threshold-free argument exists with the paper's internal tools. A threshold
(bootstrap) stopping time is necessary for S(2,l) on (+,+)/(−,−).**

### 1.3 The minimal bootstrap, fully specified (grid framework)

**Setting** (as in Step 2 on the grid: `GridPath`, T1516/T1519/T1520/T1524).
- Fix E (|E| ≤ 2−κ) and s, t with the gained (2.72) (`N^c R_t^{30} ≤ A_t`, the form used by T1519).
- Fix a terminal sequence u(N) ∈ [s_N,t_N], a grid u_j = `time s u K N j` (j ≤ K), Δ = (u−s)/K, and
  H_j = `H d s u K N j`.
- σ_pp := (+,+), ξ_pp = (m², m²) (Lean `xiOf (mSigma E) ![true,true]`).
- `A_j := (L−K)_{u_j,σ_pp,·}(H_j) : Z_L² → ℂ`.
- `J_j := A_{u_j}² · max_a |A_j(a)|` (this is Ξ_2(+,+) at time u_j).
- Threshold `θ_j := A_{u_j}^{1/2}`.

**Good set** `G^{pp}(v)` (fixed-time matrix sets, each from a flow-level ≺ statement):
- (G1) `Ξ^{(L−K)}_{v,1}(M) ≤ N^ε` for both charges — P0(b), §2;
- (G2) `Ξ^L_{v,3}(M) ≤ N^ε R²` — (2.73)/(5.106) (Lean `AprioriFlow`);
- (G3) `Ξ^L_{v,6}(M) ≤ N^ε R^5` — same source;
- (G4) (v,τ,D)-decay (5.74) of L and L−K of lengths 2, 3, 6 at scale ℓ_vW^τ with tail W^{-D} —
  Lemma 5.9 (p.64);
- (G5) the entry local law (2.75) (needed only inside the proofs of (G1), (G4)).

**Stopping time** (T1519/T1520 shape):
`τ := min( firstHit (j ↦ J_j − θ_j) 0 K , firstHit (j ↦ 1_{H_j ∉ G^{pp}(u_j)}) (1/2) K )`.
Only **one** threshold process, on Ξ_2(+,+). (−,−) is covered pointwise by the conjugation symmetry.
(+,−)/(−,+) do not enter the n=2 (+,+) equation.

**Expansion at the random target k = τ(ω)** (exact telescoping, `duhamel_telescope` /
`duhamel_telescope_stopped`, GridDuhamel.lean:101). The grid form of (5.20) at n=2 (p.54):
`A_k = U_{0,k}A_0 + Σ_{j<k∧τ} U_{j+1,k}(Δ·D_j + Z_{j+1} + Y_{j+1} + R_j)`, where
- `U_{i,k} = Uker(ξ_pp, u_i, u_k)` is (5.17);
- `D_j = eGterm_{σ_pp}(H_j) + primBil(A_j,A_j)`: this is (5.15) at n=2, whose Σ_{l_K>2} is empty
  (T1523's `discrete_hierarchy_step_n`, stated for every σ, including n=2);
- Z_{j+1} is the linear Gaussian part, Y_{j+1} the second-order part, and R_j the one-step remainder.

On {j < τ}: `J_j < θ_j` and `H_j ∈ G^{pp}(u_j)`. The bounds below are in units `A_{u_k}²`, with
`A_{u_k} ≤ A_{u_j}` for j ≤ k (monotonicity of Wℓη, p.24; Lean `flowScale_antitoneOn`).

(A) **Initial term.** `A_{u_k}²|U_{0,k}A_0(a)| ≤ C_U·J_0`, where C_U bounds the kernel (item B).
`J_0 ≤ N^ε` by (2.68) at s for σ=(+,+) (p.24; point 3). Alternatively use Lemma 7.3 Case 1 (7.16)
at n=2 (Lean `Q716.uker_decay_le_nonAlt`, Q716Pointwise.lean:78, with `hk : σ 0 = σ 1`): it gives
`cKerShort·K²·(A_s/A_{u_k})²·max|A_0| + ((1−s)/(1−u_k))²·δ`, and then `A_{u_k}²(A_s/A_{u_k})²A_s^{-2}J_0
= J_0`. Both routes give the same bound.

(B) **Kernel.**
- For ξ = m² each edge factor `(1−u m²S)(1−t m²S)^{-1} = I + (t−u)m²SΘ_{tm²}` ((5.18), p.53) has
  ℓ¹ row sums `≤ 1 + (t−u)C/κ'`. This uses (2.52) with |1−tm²| ≥ κ' = κ'(κ); Lean
  `sum_norm_edgeKer_sub_one_le_short` (KernelDecay.lean:1112).
- So `Σ_b|U_{i,k}(a,b)| ≤ C_U := (1+C/κ')²`, and `norm_Uker_apply_le` (Kernel.lean:256) gives
  ‖U_{i,k}A‖_max ≤ C_U‖A‖_max.
- No decay or sum-zero is needed. This is why P3's joint-decay problem for (Q⊗Q)(E⊗E) does not
  arise here.

(C) **Drift, quadratic term.** (5.79) at n=2 (p.64), on {j<τ}:
- `|primBil(A_j,A_j)(a)| ≤ 3W·(2ℓ_{u_j}W^τ+1)·(θ_jA_{u_j}^{-2})² + tail ≤ C W^τ θ_j² A_{u_j}^{-3}η_{u_j}^{-1}
  + W^{-D+C}`.
- The b_1-sum is restricted by (G4) for (L−K)_{(+,+)} of length 2; b_2 is restricted by S^{(B)}
  (|b_1−b_2| ≤ 1); and `Wℓ_u = A_u/η_u`.
- With θ_j² = A_{u_j}: `A_{u_j}²|primBil| ≤ C W^τ/η_{u_j}`.

(D) **Drift, E^{(G̃)} term.** (5.80) at n=2 (p.65), definition (2.47) (p.18):
- `E^{(G̃)} = W Σ_{k=1,2}Σ_{a,b}⟨G̃(σ_k)E_a⟩S_{ab}(G^{(b)}_k∘L)`, where the second factor is a 3-loop.
- On {j<τ}, with (G1), (G2) and (G4) for 3-loops:
  `|eGterm(a)| ≤ 2·3W·(ℓ_{u_j}W^τ)·N^εA_{u_j}^{-1}·N^εR²A_{u_j}^{-2} + tail ≤ C W^τN^{2ε}R² A_{u_j}^{-2}
  η_{u_j}^{-1}`.
- Here Ξ_1 must be the sharp one; this is supervisor 1a(i).
- Summing (C)+(D) over j: `A_{u_k}²Σ_{j<τ}Δ|U_{j+1,k}D_j| ≤ C_U·C W^τ(1+N^{2ε}R²)·Σ_{j<K}Δ/η_{u_j}`.
- `Σ_{j<K}Δ/η_{u_j} ≤ (Im m)^{-1}log((1−s)/(1−u)) + Δ/η_u ≤ C log N` (by (2.72), and
  `etaT_inv_le_of_hreg`, GridNetLift.lean:86). This is the plan's "trivial log N lemma" (§3.2).

(E) **Martingale.**
- For fixed k: `M_k := Σ_{j<k∧τ}U_{j+1,k}Z_{j+1}`.
- The conditional variance of the (stopped) j-th increment at label a is the variance of a linear
  form in the Gaussian increment. The weights are w_b = U_{j+1,k}(a,b) on the linear forms
  `gradMat Φ_{u_{j+1},b}` at H_j.
- sqrt(v) is a seminorm (v is a positive semidefinite Hermitian form, Lean `GridQVForm`), so
  Minkowski gives `v(Σ_b w_b X_b) ≤ (Σ_b|w_b|)² max_b v(X_b) ≤ C_U² max_b v(X_b)`.
- `v(X_b)` is the diagonal (E⊗E)_{b,b} of (5.22)–(5.25) (pp.54–55): six-loops
  σ^{(k)} ∈ {±}^6 with `WΣ_{c,c'}S_{cc'}`. On {j<τ}, by (G3) and (G4) for 6-loops, (5.81) at n=2
  (p.65) gives `v(X_b) ≤ C W^τ N^εR^5 A_{u_j}^{-4}η_{u_j}^{-1}`.
- So the increment variances satisfy `c_j ≤ Δ·C_U²·C W^τN^εR^5A_{u_j}^{-4}η_{u_j}^{-1}`, and
  `A_{u_k}^4Σ_j c_j ≤ C W^τN^εR^5 log N`.
- Complex values: Re/Im are treated separately (`azuma_complex`).
- `stopped_duhamel_azuma_tail(_union)` (GridDuhamelTail.lean:394, generic in n and complex ξ) gives,
  with probability ≥ 1 − N^{-D₁} simultaneously for all k ≤ K and all a,
  `A_{u_k}²|M_k(a)| ≤ N^ε(C W^τN^εR^5 log N)^{1/2}`.
- Only the diagonal is used, and that is legitimate here: the Minkowski step needs only the
  row-sum bound (B). The plan's "whole tensor" warning (§3.3(c)) concerns the Q⊗Q sum-zero gain,
  which is absent for (+,+).

(F) **Second-order and remainder terms.**
- Y: `stopped_duhamel_cheb_tail` (:448) with E|Y_{j+1}|² ≤ N^CΔ².
- R_j: `‖R_j‖ ≤ stepErr ≤ C_1Δ² + C_2Δ^{3/2}` with polynomial C_i (T1506 `stepErr_le_unif`, general
  n in T1523). Then `stopped_duhamel_det_bound` (:662) with the amplification-r device.
- Both are ≤ N^{-1} once K = N^{C(D₁)} is chosen **after** D₁ (T1519/T1520 `GridPointwise'`
  lesson).

**Closure.** On the high-probability event (good set at all j ≤ K, tails (E)/(F) for all k ≤ K,
`J_0 ≤ N^ε`), evaluating at k = τ(ω) gives
`J_τ ≤ C N^{2ε}W^τ log N·(1 + R² + R^{5/2}) + N^{-1} =: Out`.

Then `Out < θ_τ = A_{u_τ}^{1/2}`, eventually and uniformly:
- `A_{u_τ} ≥ A_u ≥ R²A_s^{3/4}` (`Scales.le_A`), so `A_{u_τ}^{1/2} ≥ R·A_s^{3/8}`.
- `R^{5/2} = R·R^{3/2} ≤ R·A_s^{3/16}`.
- So it suffices that `C N^{2ε}W^τ log N < A_s^{3/16}`, which holds for ε, τ small because
  `A_s ≥ A_t ≥ N^c`.

**Why τ = K.** `min_firstHit_eq_of_at` (GridBootstrap.lean:367) is generic in (J, J', θ, θ', K). Its
two hypotheses hold on the event:
- (i) `hgood`: `J'_j = 1_{H_j∉G^{pp}} < 1/2` for all j ≤ K (good set at every grid point);
- (ii) `hat`: `J_τ < θ_τ` (the closure).

So τ = K. There is no circularity: the bound at τ uses the deterministic inputs only at j < τ, and
the fresh increment Z_τ is controlled by the conditional variance computed at H_{τ−1}. If τ = 0, the
bound at τ is `J_0 ≤ N^ε < θ_0`, which contradicts `J_0 ≥ θ_0`.

**Output.**
- At k = K = τ, `Ξ_2(+,+)(u_K) = J_K ≤ Out` with u_K = u (`time_last`).
- By `map_H_eq` (GridPath.lean:452), for every terminal sequence u(N) ∈ [s,t]:
  `A_{u(N)}²·max_a|(L−K)_{u(N),(+,+),a}| ≺ 1 + R² + R^{5/2}`, at the fixed time u(N).
- Uniform in the time via the chain accepted by supervisor §3: `unifDomIcc_of_forall_stochDom`
  (Lemma514Moment.lean:128) → `unifDomIcc_mul_scale` (:223) → `stochDom_timeIcc_of_unifDom_const`
  (:259), with the Hölder modulus `hHol_flow`/`hKb_flow`/`exists_highProb_normX`
  (Lemma514Holder.lean:721/864/1049) at loop length 2. No `MomentDuhamel`.
- (−,−) follows by conjugation.
- Finally `1 + R² + R^{5/2} ≤ 3R^{5/2} ≤ 3R^4 ≤ 3A_s^{1/2} ≤ 3Ψ(2,l)` for every l: R² ≤ b, and
  Ψ(2,l) ≥ A_s^{1/2} by (5.108) (p.70; `psi`, Step3.lean:290).
- This is S(2,l) on (+,+)/(−,−) for all l.

**Remaining charges.** (+,−) and (−,+): (2.76) gives `Ξ_2 ≺ (η_s/η_u)^4`, and
`(η_s/η_u)^4 ≤ ((1−s)/(1−t))^4 ≤ A_t^{2/15} ≤ A_s^{1/2}` by (2.72). This step needs (2.72) itself,
not only `Scales`. m=1: `flow_S_one'` (StepGlue.lean:342) — Ψ(1,l) ≥ A_s^{1/2} ≥ A_u^{1/2}.

**Why this is not Step-2 size.** Compared with Step 2 (§5.3, (5.26)–(5.48)):
- there is no tail function J*_{u,D} and no (5.44)-type near/far time sums;
- no (+,−) positivity (`Uker_one_nonneg`, `v_Ab_le`) and no T-profiles;
- no Q/sum-zero;
- the target is a max-norm; the kernel is bounded (B);
- all E-bounds are (5.79)–(5.81) at n=2.

The threshold/stopping/endpoint skeleton, however, is exactly Step 2's grid skeleton (T1519 `gridTau`,
T1520 `min_firstHit_eq_of_at`, T1524 closing).

### 1.4 Lean statement targets and ticket count

Names are new unless cited. All sit on the grid of `GridPath`, with hypotheses in T1519/T1524 style
(bulk κ, gained Cond272 with exponent c, `hs0/hst/ht1`). Fixed parameters come before `∀ᶠ N`; K is
chosen after D₁.

- **PP-1 (Ξ_1 sharp; this is P0(b), shared with goodSet514).**
  - (a) `xiLK_one_sharp_seq`: for `hLL : LocalLawFlow (sample d) E s t` and every `v : ℕ → ℝ` with
    `v N ∈ [s N, t N]`,
    `StochDom (P d) (fun N (w : LoopData (d.L N) 1) ω => (band d).scale E N (v N) *
    (sample d).lkErr E N (v N) ω w.idx) (fun _ _ _ => 1)`.
  - (b) `highProb_grid_xiLK_one`:
    `HighProb (Pg d) {ω | ∀ j ≤ K N, ∀ w, scale(u_j)·lkErrMat(u_j,H_j ω,w) ≤ N^ε}`
    (via `unifDomIcc_of_forall_stochDom` plus a `map_H_eq`/union-bound transfer from a
    pointwise-uniform input; `highProb_grid_of_flow` needs a continuum-simultaneous input).
  - 1 ticket.
- **PP-2 (n=2, non-alternating drift bounds, deterministic, per matrix M).** For
  `I = ⟨![true,true], ofFn a⟩`:
  - (a) `norm_primBil_pp_le`: if A := gloop−Kval at σ_pp satisfies `FastDecay L (ℓ_v·Kd) δ A` and
    `‖A b‖ ≤ θA_v^{-2}`, then `‖primBil(A,A)(I)‖ ≤ C·Kd·θ²A_v^{-3}η_v^{-1} + C·W·L²·δ·θA_v^{-2}`.
  - (b) `norm_eGterm_pp_le`: with `Ξ_1(M) ≤ φ_1`, `max|L_3(M)| ≤ φ_3A_v^{-2}` and 3-loop decay,
    `‖eGterm(M)(I)‖ ≤ C·Kd·φ_1φ_3A_v^{-2}η_v^{-1} + tail`.
  - 1 ticket; it can be the n=2 instance of P4 if P4 is written for general n.
- **PP-3 (n=2 conditional variance).** `condVar_pp_le`: for weights `w : LoopArg L 2 → ℂ`,
  `v(Σ_b w_b gradMat(Φ_{v,b}))(M) ≤ (Σ_b‖w_b‖)²·(C·Kd·Ξ^L_6(M)·A_v^{-4}η_v^{-1} + tail)`, on 6-loop
  decay. This includes the identification of `v(gradMat Φ_b)` with the diagonal (5.22) six-loops. It
  is the n=2 diagonal case of P3's `eeTensor`. 1 ticket.
- **PP-4 (bounded (+,+) kernel).** `sum_norm_Uker_pp_le : Σ_b ‖U_{u,v,σ_pp}(a,b)‖ ≤ C(κ)` from
  `sum_norm_edgeKer_sub_one_le_short` plus `|1−t m²| ≥ κ'(κ)`. 0 tickets (fold into PP-3/PP-6).
- **PP-5 (general-σ grid expansion at n=2, complex Z/Y).** This is T1516 `grid_expansion_all'`
  (GridExpansion.lean:928) with `ξ_pp` complex in place of `fun _ => 1`, plus the complex `stepZC`.
  0 tickets if P5 is written generically in (n, σ); otherwise 1–2.
- **PP-6 (good set, threshold stopping time, good event).**
  - `goodSetPP d E N v ε Kd D`: (G1)–(G4), measurable (`measurable_gloop_matrix`).
  - `highProb_grid_goodSetPP`: from `AprioriFlow`, PP-1, P4's decay sets and
    `highProb_grid_of_flow`.
  - `JPP`, `thetaPP j := scale(u_j)^{1/2}`, and
    `tauPP := min (firstHit (fun j ω => JPP j ω − thetaPP j) 0 K) (firstHit 1_{goodSetPPᶜ} (1/2) K)`.
  - Stopping-time property via `isStoppingTime_min_firstHit_grid` (GridStopFilt.lean:69).
  - `highProb_init_pp : JPP 0 ≤ N^ε` from (2.68) at s.
  - `goodEventPP` in T1519 `goodEvent_grid`/`goodEvent_grid_imp` form.
  - 1–2 tickets.
- **PP-7 (stopped estimate at the random target).** `pp_at_tau`: on `goodEventPP`,
  `JPP (tauPP ω) ω ≤ C N^{2ε}Kd·log N·(1 + R² + R^{5/2}) + N^{-1}`, and eventually this is
  `< thetaPP (tauPP ω)`. Inputs: (A)–(F), PP-2–PP-5, and T1504 tails. 1 ticket, or 0 if the P5
  assembly takes an abstract stopping time with "deterministic bounds on {j<τ}" as a hypothesis.
- **PP-8 (endpoint, flow, time-uniform).**
  - `pp_endpoint`: `min_firstHit_eq_of_at` gives τ = K and `JPP K ≤ Out`.
  - `map_H_eq` then gives a per-sequence StochDom.
  - The time-uniform lift (supervisor §3 chain) gives
    `StochDom P (fun N (p : TimeIcc s t N × ZMod L²) ω => scale(p.1)²·lkErr(p.1,(σ_pp,p.2)))
    (fun N _ _ => 1 + R N ^ 2 + R N ^ (5/2))`.
  - The (−,−) conjugation lemma is included.
  - 1 ticket.
- **PP-9 (glue h12).** `S_le_two_all : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S P (flowXiLK …) As R A m l`.
  - m=1 from `flow_S_one'`.
  - m=2: `lkMax` over the four charges, using (+,−) from `AprioriDecayFlow` with
    `(η_s/η_u)^4 ≤ A_s^{1/2}` (Cond272), (−,+) by cyclicity, (+,+) from PP-8, (−,−) by conjugation.
  - 1 ticket.

**Count: 7–11 tickets** (PP-1, 2, 3, 6, 7, 8, 9 always; PP-5 0–2; PP-6 1–2). If P5 is specified
generically in n and in the stopping time (recommended), PP-5 and most of PP-7 disappear:
**net 6–8**. Dependencies:
- P4's decay sets must cover lengths 2, 3, 6: extend the P4 spec; +0–1.
- T1523 (`discrete_hierarchy_step_n`, still proving) must cover n=2 and all σ. Its ticket says
  "every σ", and `primRhs_split` has `2 ≤ I.length`.

---------------------------------------------------------------------------------------------------

## (T2) P0(b): Ξ^{(L−K)}_{u,1} ≺ 1 for both charges

**What (5.80) needs.**
- Definition (2.47) (p.18): E^{(G̃)} contains `⟨G̃_u(σ_k)E_a⟩` for **both** σ_k = ±, multiplied by an
  (n+1)-loop at the same time u.
- So (5.80) needs `max_{σ∈{±}, a}|(L−K)_{u,σ,a}| ≺ A_u^{-1}`, i.e. `Ξ^{(L−K)}_{u,1} ≺ 1` **at every
  time u of the Duhamel integral**. On the grid this is the good-set item
  `{Ξ^{(L−K)}_{u_j,1}(M) ≤ N^ε}` at every u_j (supervisor 1a(i)).
- The weak S(1,l) (`flow_S_one'`, Ξ_1 ≺ A_u^{1/2}) does not suffice: see 1.3(D) and the failure
  analysis in 1.1 point 5.

**Paper proof.**
1. For n=1, K_{u,+,a} = m (p.19), so `(L−K)_{u,(+),(a)} = Tr(G_uE_a) − m = ⟨(G_u−m)E_a⟩`, since
   Tr E_a = 1 ((2.9) notation, p.26).
   For σ = (−): `⟨(G_u*−m̄)E_a⟩ = conj⟨(G_u−m)E_a⟩` (E_a is real diagonal), with the same modulus.
2. (4.4) holds: `‖G_u−m‖_max ≺ A_u^{-1/2} ≤ W^{-c}` by (2.75) (p.24) and `A_u ≥ A_t ≥ N^c`. The
   latter follows from (2.72) in its application form, p.24: `(Wℓ_tη_t)^{-1} ≤ W^{-30τ'}`.
3. (4.5) (p.48): `max_a|⟨(G_u−m)E_a⟩| ≺ max_{a,b}L_{u,(+,−),(a,b)}`.
4. (5.73) (p.63): `max_{a,b}L_{u,(+,−),(a,b)} ≺ A_u^{-1}`. It uses:
   - (2.59)/(2.58)+(2.52) for K: `|K_{(+,−)}| ≤ C(Wℓ_uη_u)^{-1}`;
   - (2.76) for L−K: `≤ (η_s/η_u)^4A_u^{-2}`;
   - (2.72): `(η_s/η_u)^4 ≤ A_t^{2/15} ≤ A_u`.
5. Hence `A_u·max_{σ,a}|(L−K)_{u,σ,a}| ≺ 1` at each fixed u. Uniformity in u follows from the
   paper's net argument (5.1) (p.51), or on the grid from the union bound over K+1 ≤ N^C points.

This is exactly p.65 "(5.80) … with (2.76), Ξ^L_{u,2} ≺ 1" and p.72 "Ξ_{t,1} ≺ 1". **PASS.**

**T1525's Lean route — CONFIRMED, with three corrections.**
- `detAvgIBP_stochDom_of_localLaw_complete` (DetAvgIBPFlow.lean:274): for a single time family u and
  `hll : LocalLawUnifIcc d E u u Ψ`, `‖Tr((G_{u_N}−m)Eblk b)‖ ≺ Ψ_N²`, uniformly in b. It has no
  hypothesis beyond `hll` and scalar side conditions. T1525 built it and printed axioms
  `[propext, Classical.choice, Quot.sound]`.
- `lkErr_one_eq_norm_trace` (Eq45Flow.lean:89): `lkErr(w.idx) = ‖Tr((G−m)Eblk(w.2 0))‖` for **both**
  charges (the right side does not depend on the charge).
- With `Ψ_N = scale(u_N)^{-1/2}`, `scale·Ψ² = 1`, so `scale(u_N)·lkMax(u_N,1) ≺ 1`.

Match with the paper:
- The paper's (4.5) proof (p.50) uses about Ψ only "max|G_ij−mδ_ij|² ≺ Ψ² := max_a L_{(+,−),a}",
  plus (4.12) (cited there from [40] eq. (4.11)).
- The Lean theorem instantiates the same control directly from (2.75) (`Ψ² = A_u^{-1}`) instead of
  via (5.73). Both give Ψ² ≍ A_u^{-1}, because `L_{(+,−)} ≤ max|G_ij−mδ_ij|² + W^{-1}` and
  `W^{-1} ≤ A_u^{-1}`.
- The side conditions correspond: `hΨlo` (Ψ ≥ W^{-1/2}) mirrors p.50's `cW^{-1} ≤ max L_{(+,−)}`.
- Same estimate, different instantiation of the control parameter; the conclusion Ξ_1 ≺ 1 is
  identical. (4.12) is proved internally in Lean (no fluctuation-averaging hypothesis in the
  signature). This is consistent with CLAUDE.md §3.1.

Corrections:
1. `StepGlue.norm_lkErr_one_le` (StepGlue.lean:125) is **not** part of the sharp route. It bounds the
   1-loop by the entry scale ‖G−m‖_max, i.e. Ξ_1 ≺ A_u^{1/2}, which is the weak S(1,l)
   (`flow_lkErr_one_le'`/`flow_S_one'`). The operative pieces are `detAvgIBP_…_complete` and
   `lkErr_one_eq_norm_trace` only.
2. `hll` must be produced at the **tight singleton** control `Ψ_N = scale(u_N)^{-1/2}`.
   - `localLawUnifIcc_of_localLawFlow` (GoodSetFlow.lean:230) takes `LocalLawFlow` on the **same**
     interval as its conclusion. A trivial restriction lemma from [s,t] to [u_N,u_N] is needed;
     `LocalLawFlow` is tight per time (Flow/Hypotheses.lean:357).
   - The canonical `localLawUnifIcc_of_localLawFlow_scales` must **not** be used: its
     `Ψ = (R²A_s^{3/4})^{-1/2}` gives only `Ξ_1 ≺ A_u/(R²A_s^{3/4}) ≤ A_s^{1/4}`.
   - Side conditions: `hΨlo` from `ℓ_uη_u ≤ 1`; `hΨhi` from `scale(u_N) ≥ N^{2a}` (gained Cond272);
     `hη` from `η_u ≥ N^{-K}`.
3. The output is **per time sequence**.
   - goodSet514 and goodSetPP need it at all grid points simultaneously: use
     `unifDomIcc_of_forall_stochDom`, then a `map_H_eq` + union-bound transfer. The existing
     `highProb_grid_of_flow` (GridJStar.lean:214) assumes a continuum-simultaneous flow event, so a
     pointwise-uniform variant (or a Hölder lift via `stochDom_of_forall_seq_relaxed`,
     Step1Hyp.lean:317, with the 1-loop's Lipschitz modulus) is needed.
   - This is inside PP-1, which stays **1 ticket** (T1525's estimate).

---------------------------------------------------------------------------------------------------

## (T3) Effect on the G1c plan, paper-delta wording, revised estimate

**Plan changes.**
1. Supervisor §1a ("only a good-set stopping time, no threshold stopping time") remains correct for
   Lemma 5.14 with n ≥ 3. For **S(2,l) on (+,+)/(−,−)** a threshold stopping time is required (§1.2).
   New block **G1c-PP** (§1.3–1.4) sits upstream of `S_all`/`flow_sharpLoop`, not of Lemma 5.14.
2. **P5 spec:** state the fixed-endpoint assembly generically in n and σ, with an abstract grid
   stopping time and the hypothesis "deterministic drift, QV and remainder bounds on {j < τ}". Then
   PP-7 is an instance (n=2, σ_pp, τ with threshold) and PP-5 is free.
   - Supervisor §4 notes that P5's 2-loop sub-terms can be (+,+). In the bound-transfer form they
     enter only as the `Lemma514` premises `X 2 ≺ Φ` and `X 2·X n·A⁻¹ ≺ Φ`, i.e. as good-set
     hypotheses of P5/`lemma514_of_seq`, not as statements P5 must prove.
   - So P5's Lean statement does not depend on PP. P5 can proceed in parallel with PP **after** the
     supervisor's review of this report.
3. **P4 spec:** include the n=2 case (the (5.79)/(5.80) bounds of PP-2) and decay sets for lengths
   2, 3, 6. Add the sharp Ξ_1 set (PP-1) to goodSet514.
4. **P3:** the n=2 diagonal QV bound (PP-3) needs only Minkowski plus the diagonal (5.22). The
   joint- vs slot-wise decay choice (supervisor 1b) is irrelevant for PP.
5. **G1d (Step 4):** (5.125) at n=2, σ=(+,+) is again self-quadratic (`Ξ_2 ≺ 1 + Ξ_1 + Ξ_2²/A`).
   It closes only with the Step-3 output of PP-8 (`Ξ_2(+,+) ≺ R^{5/2}`, so `Ξ_2²/A ≺ R^5/A ≪ 1`).
   p.72's "Ξ_{t,2} ≺ A^{1/4} by (2.76),(4.5)" covers only (+,−). Record under the same delta.

**Candidate paper-delta G1c-a** (draft only; not written into `docs/paper-deltas.md`; temporary tag
`T1526a`):

> **T1526a (G1c-a)** — p.70, proof of (2.77): "By (2.76), S(m,l,s,u,t) holds for any l and m ≤ 2";
> p.72, Step 4: "By (2.76) and (4.5) … Ξ_{t,1} ≺ 1, Ξ_{t,2} ≺ (Wℓ_tη_t)^{1/4}". (2.76) and (2.69) are
> stated only for σ = (+,−) (hence (−,+) by cyclicity), while Ξ^{(L−K)}_{u,m} in (5.76) is a maximum
> over all σ ∈ {+,−}^m. Lean:
> - (i) m = 1: S(1,l) (scale Ψ(1,l) ≥ (Wℓ_sη_s)^{1/2}) from (2.75) alone. The sharp
>   Ξ^{(L−K)}_{u,1} ≺ 1 used in (5.80) is (4.5) with the control parameter read off (2.75) instead
>   of (5.73) (`detAvgIBP_stochDom_of_localLaw_complete`, `lkErr_one_eq_norm_trace`).
> - (ii) m = 2, σ ∈ {(+,−),(−,+)}: (2.76) together with (η_s/η_u)^4 ≤ (Wℓ_sη_s)^{1/2} from (2.72).
> - (iii) m = 2, σ ∈ {(+,+),(−,−)}: **not covered by the paper; added argument.** Ξ^{(L−K)}_{u,2}(+,+)
>   ≺ 1 + (ℓ_t/ℓ_s)^{5/2} (≤ (Wℓ_sη_s)^{1/2} ≤ Ψ(2,l)) is proved by an n = 2 bootstrap:
>   - the integrated hierarchy (5.20) at n = 2, σ = (+,+), on a time grid, stopped at the first grid
>     time where (Wℓ_uη_u)² max_a|(L−K)_{u,(+,+),a}| ≥ (Wℓ_uη_u)^{1/2} or where the fixed-time good
>     set fails;
>   - the drift by (5.79), (5.80) at n = 2, with Ξ_1 ≺ 1 and Ξ^{(L)}_3 ≺ (ℓ_t/ℓ_s)² from (2.73);
>   - the martingale by (5.81) at n = 2, with Ξ^{(L)}_6 ≺ (ℓ_t/ℓ_s)^5 and the bounded short-edge
>     kernel U_{u,t,(+,+)} ((2.52), Lemma 7.3 Case 1);
>   - (−,−) by complex conjugation.
>
>   The self-quadratic term Ξ_2(+,+)²/(Wℓ_uη_u) makes a threshold stopping time unavoidable. The
>   paper's "S(m,l) for m ≤ 2" and Step 4's "Ξ_{t,2} ≺ A^{1/4}" are used for (+,+) only through (iii).
>
> Classification: 补证 (added argument); statements unchanged.

**Revised ticket estimate.**
- Plan base 35–45.
- Plus P0 tickets: T1525 (1) and T1526 (1).
- Plus the G1c-PP block: 6–10. This includes PP-1, which replaces the supervisor's "(4.5) producer
  1–3". The supervisor's placeholder for the (+,+) producer was 2–5.
- **Narrow ≈ 43–57. Wide, with G1b's ≈ 0.3 rework rate: ≈ 56–74.**
- This exceeds the 50-ticket automatic HOLD with high probability. The 45-ticket checkpoint remains
  the real decision point.
- G1c tickets so far: T1522, T1523, T1525, T1526 = 4.
- If P5 is made generic as recommended in item 2, PP drops to 6–8 and the narrow total to about
  43–55.

---------------------------------------------------------------------------------------------------

## Key facts used (paper)

- Def. 2.10 (p.17), (2.45)–(2.48) (p.18), (2.52), (2.57)–(2.59) (pp.20–21), (2.68)–(2.76)
  (p.24), (2.82) (p.26).
- Lemma 3.6 (3.12)/(3.13) (p.33).
- Lemma 4.1 (4.1)–(4.5) (p.48) and its proof (4.12) (p.50).
- (5.13)–(5.21) (pp.53–54), Def. 5.4/(5.22)–(5.25) (pp.54–55), (5.43)–(5.47) (p.58), (5.73) (p.63).
- Lemma 5.9 (5.75), Lemma 5.10 (5.77)–(5.81) (pp.64–65), Lemma 5.11 (5.82)–(5.86) (p.65),
  Lemma 5.14 (5.92)–(5.105) (pp.67–69).
- (5.106)–(5.113), (5.118)–(5.120) (pp.69–71).
- Lemma 7.1 (7.1) (p.76), Lemma 7.3 (7.13)–(7.24) (pp.78–80).

## Open issues

1. **Supervisor review required before P5 dispatch** (supervisor §4 failure signal: "(+,+) needs a
   stopping-time argument"). The argument in §1.3 is complete at paper level. Its Lean realization
   depends on P4 (decay sets for lengths 2, 3, 6), T1523 (n=2, all σ, still proving), and either a
   generic P5 or PP-5.
2. `highProb_grid_of_flow` needs a continuum-simultaneous input. PP-1 and goodSetPP need a
   pointwise-uniform grid transfer or a Hölder lift for the 1-loop (small; inside PP-1).
3. The Ξ^{(L−K)}_{s,2} ≺ 1 initial condition for (+,+) is the Theorem 2.21 hypothesis (2.68) at s.
   Its Lean form as a producer input (shared with P5's initial condition (5.110)) should be fixed in
   the PP-6 spec.
4. (2.72) itself (not only `Scales`) is needed in PP-9 for `(η_s/η_u)^4 ≤ A_s^{1/2}` in the (+,−)
   charges.
