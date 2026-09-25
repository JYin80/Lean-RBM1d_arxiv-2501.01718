Prover model: claude-opus-5-5[1m]

# T1499: is `h560` of `eGpm_le_rhs535_of_jS` / `h535_of_jS` satisfiable, and what replaces it?

2026-09-25T20:20Z (preflight written before any Lean).

Notation (Lean). `G := green (X.H N u ω) (zt E u)`, `G⁻ := green … (conj (zt E u)) = Gᴴ`,
`η := etaT E u = (zt E u).im`, `ℓ := B.ell N u`, `W := B.W N`, `L := B.L N`,
`A := W·ℓ·η`, `T(d) := tailT W ℓ η D' d = A⁻² e^{-√(d/ℓ)} + W^{-D'}`, `jS := Step2.jS X E D' N u ω`,
`gm := Step2FarInputs.gmOfJS X E D' N u ω`, so `gm x y = √jS · √T(zdist(x-y))`, and
`L3(a₂,b,a₁) := gloop L W (X.H N u ω) (zt E u) ⟨[false,true,true],[a₂,b,a₁]⟩
 = tr(G⁻E_{a₂} G E_b G E_{a₁})`, `E_a = W⁻¹·1_{I_a}` (`Eblk`), `gloop` = unnormalized trace.
`s := Im m = (mE E).im`, `|m| = 1`.

## (a) Math preflight

### Step 0 (read-only checks)

- `gmOfJS` (Step2FarInputs.lean:2184): `√(jS) * √(tailT W ℓ η D' (zdist (x-y)))`, for **all**
  `x y`, including `x = y`, where `gm a a = √jS·√(A⁻² + W^{-D'}) ≈ √jS·A⁻¹`.
- `jS` (`Step2.jS`, APrimeSmoothPrefixCanonicalCore.lean:96): `1 + max_{pairs a} |(L-K)_{(+,-),a}| /
  T(zdist(a0-a1))`, over **all** pairs, diagonal included. It is ≤ the paper's `J*_{u,D}` of (5.29)
  (the paper divides by `T(ℓ)` with `ℓ ≤ |a-b|`), so every paper bound on `J*` bounds `jS`.
- `tailT` (StretchedExp.lean:281) is (5.27) literally.
- `eGpm_le_rhs535_of_jS` (:2224): fixed `a₁ a₂` (arbitrary; `a₁ = a₂` allowed), hypothesis
  `h560 : ∀ b, ‖L3(a₂,b,a₁)‖ ≤ gm a₂ b * gm a₁ b * gm a₂ a₁`.
- `h535_of_jS` (:2267): `h560 : ∀ u ∈ Ico, ∀ (b : LoopArg L 2) (c : ZMod L), ‖L3(b 1, c, b 0)‖ ≤
  gm (b 1) c * gm (b 0) c * gm (b 1) (b 0)` — all pairs, all `c`.
- Where `h560` is consumed: it is passed through `eGpm_le_rhs535` → `EGDef.eGpm_le_reduced` →
  `Lemma57.eG_le` (:1116). In `eG_le` the near branch (`zdist(a₁-a₂) ≤ ℓ*`) does not use it; the
  far branch passes it to `sum_far_le` (:545), which uses it **only** through
  `case2_pointwise` (:506), i.e. only for `b` with `ℓ*/2 < zdist(a₁-b)` and `ℓ*/2 < zdist(a₂-b)`
  (and `ℓ*/2 ≤ zdist(a₁-a₂)`), and only together with `h42`. Every other instance of `h560` is
  demanded but never used.
- Paper pp. 59–61. (5.60): `L_{u,(-,+,+),(a₁,b,a₂)} ≺ max_{x₁,x₂,y} |G_{x₁y}||G_{yx₂}||G_{x₁x₂}|·1(x₁∈I_{a₁})1(x₂∈I_{a₂})1(y∈I_b)`
  — the maximum of **actual entries** (true for every `b`, trivially). (5.61):
  `|G_{yx₂}||G_{x₁x₂}||G_{x₁y}| ≺ (J*)^{3/2}(T(|a₁-a₂|)T(|a₁-b|)T(|a₂-b|))^{1/2}`, stated **only in
  case (2)** (`min_i |a_i-b| ≥ ℓ*_u/2`, and `|a₁-a₂| ≥ ℓ*_u`), because it uses (4.2) off the
  diagonal block and (5.31), which needs `|a-b| ≥ δℓ*`. In case (1) the paper uses the Schwarz
  bound (5.56)–(5.58), `L ≺ (L_{(-,+),(a₁,a₂)} + L_{(-,+),(a₂,b)})·A^{-1/2}(1+J*A^{-1})`. For
  `|a₁-a₂| ≤ ℓ*` it uses (2.73)/(5.53) and (5.54). (5.62)/(5.63) sum case (2) over `b`.

### Target (T1): verdict — **FAIL** (`h560` as stated is not satisfiable in the regime where the
theorems are meant to be used)

**What `h560` was meant to encode, and the mis-transcription.** `h560` is (5.60)+(5.61) fused
into a single inequality with `Gm := gmOfJS`. Three defects:

- (D1) Quantifier: (5.61) holds only in case (2). `h560` asks for it for **every** `b`, and
  `h535_of_jS` asks for it for **every pair** `(a₁,a₂)`, including the diagonal and near pairs
  where the proof of (5.35) never uses it.
- (D2) The object: (5.60) bounds `L3` by the maximum of actual entries `max|G_{xy}|`. Lean
  replaces that maximum by `gmOfJS`, i.e. by the (4.2)+(5.31) far-field bound `√(J*·T)`, also
  where that bound is false. On the diagonal block, `max_{i,j∈I_a}|G_ij| ≥ |G_ii| ≈ |m| = 1`,
  but `gm a a ≈ √jS·A⁻¹`: this is off by a factor about `A`. (4.2) itself has the extra term
  `W⁻¹·1(|a-b| ≤ 1)`, and (5.31) needs `|a-b| ≥ δℓ*`.
- (D3) Constant: (5.61) is a `≺` statement (a factor `N^ε`, and 9 neighbour blocks in (4.2)).
  `h560` has constant `1`.

The mis-transcription is therefore not an exponent error. It is a wrong domain (D1) combined
with the wrong object (D2).

**Proof that `h560` fails.** The proof uses only instances that both theorems require: `a₁ = a`,
`b = a`, and `a₂` ranging over all of `ZMod L`. In `h535_of_jS` this is `b := ![a, a₂]`, `c := a`.
In `eGpm_le_rhs535_of_jS` it is the pairs `(a, a₂)`, for every `a₂`, at `b = a`. The instance reads
`‖L3(a₂,a,a)‖ ≤ gm(a₂,a)²·gm(a,a) = jS^{3/2} T(zdist(a₂-a)) √T(0)`.

Step 1 (Ward identity, exact, deterministic). `∑_{a₂} E_{a₂} = W⁻¹·1` (`sum_Eblk`) and
`G⁻G = (G - G⁻)/(2iη)` (`green_sub_green_conj'`) give
`2iη·W·∑_{a₂} L3(a₂,a,a) = L_{(+,+),(a,a)} − L_{(−,+),(a,a)}`.

Step 2 (deterministic lower bound). Write `g = G`. Then
`L_{(−,+),(a,a)} − Re L_{(+,+),(a,a)} = W⁻²∑_{p,q∈I_a}(|g_{qp}|² − Re g_{pq}g_{qp})
 = ½W⁻²∑_{p,q∈I_a}|g_{pq} − conj(g_{qp})|² ≥ ½W⁻²∑_{p∈I_a}|2i·Im g_{pp}|² = 2W⁻²∑_{p∈I_a}(Im g_{pp})²
 ≥ 2W⁻¹(Im tr(G E_a))²` (Cauchy–Schwarz on `W` terms).

Step 3 (right-hand side). `∑_{a₂} T(zdist(a₂-a)) ≤ (168ℓA⁻¹ + L√(W^{-D'}))·√T(0)`. This is
`Lemma57.sum_sqrt_tailT_mul_le` at `a₁ = a₂ = a`. Hence
`∑_{a₂} RHS ≤ jS^{3/2}·T(0)·(168ℓA⁻¹ + L√(W^{-D'}))`, with `T(0) = A⁻² + W^{-D'}`.

Combining Steps 1–3 with `‖∑‖ ≤ ∑‖·‖`, `h560` implies, **for every Hermitian matrix**:

  (★) `(Im tr(G E_a))² ≤ η W² · jS^{3/2} · (A⁻² + W^{-D'}) · (168ℓA⁻¹ + L√(W^{-D'}))`.

The leading term of the right side is `168·jS^{3/2}/(Wℓ²η²)`. With `hone` (the (4.5) 1-loop
hypothesis already assumed by both theorems), `Im tr(G E_a) ≥ s − κA⁻¹`. So `h560` forces
`jS^{3/2} ≥ (s − κ/A)²·Wℓ²η²/168·(1 − o(1))`, where `o(1)` covers the `W^{-D'}` terms.

- (T1-det) **Deterministic regime.** If `(s − κ/A)²·Wℓ²η² > 168·jS^{3/2}(1+ε_{D'})`, then
  `h560` and `hone` together are false for every Hermitian `H`. This is compiled in (T3).
  Since `ℓ²η ≍ s` (`ℓ = min((1-u)^{-1/2}, L)`), the condition reads `A·ℓη ≫ jS^{3/2}`, i.e. roughly
  `Wη ≫ jS^{3/2}`.
- (T1-model) **Full regime, for the Gaussian model.** Step 2 is lossy by a factor `ℓη`: it keeps
  only the diagonal `p = q`. The model supplies the full size.
  - (i) By (2.58), `K_{(+,−),(a,a)} − Re K_{(+,+),(a,a)} = W⁻¹L⁻¹∑_p D(tŝ_p)`. Here
    `ŝ_p = (1+2cos(2πp/L))/3` and, with `x = tŝ_p ∈ (−1/3,1)` and `m² = w`, `|w| = 1`,
    `D(x) = 1/(1−x) − Re(w/(1−wx)) = 2s²(1+x)/((1−x)((1−x)²+4xs²)) > 0`.
    For `x ∈ [0,1)` this gives `D ≥ 2s²/(5(1−x))`. The low modes `|p| ≲ L√(1−u)` (or `p = 0` if
    `ℓ = L`) then give `≥ c₀ s²ℓ/W ≥ c₀' s³ A⁻¹`, with `c₀'` universal.
  - (ii) `|L−K|_{(+,−)}(a,a) ≤ (jS−1)T(0)` by the definition of `jS`.
  - (iii) `|L−K|_{(+,+)}(a,a) ≺ A⁻²` (Lemma 2.18 / (2.68) at time `u`, a proven property of the
    model).

  Steps 1 and 3 then give: `h560` ⟹ `c₀' s³ A ≤ jS + N^ε + 337·jS^{3/2}` (up to `W^{-D'}` terms).
  But on the paper's good event `jS ≤ J*_{u,D} ≺ (η_s/η_u)²` by (5.47), and
  `(η_s/η_u)^{30} ≤ A_t ≤ A_u` by (2.72) and the monotonicity of `Wℓη`. So
  `jS^{3/2} ≺ A_u^{1/10} ≪ A_u`, since `A_u ≥ N^c`. Hence **`h560` is false with high
  probability, for every `u ∈ [s,t]` and every block `a`.**

**Verdict per theorem.**
- `h535_of_jS.h560`: **no**. On a high-probability event it fails for every `u`, at some
  `(b, c) = (![a, a₂], a)`, for every `a`. It can hold only where `jS^{3/2} ≳ c s³ A`. That is
  exactly where `J*` is uncontrolled, where σ has already stopped, and where `rhs535` is useless.
- `eGpm_le_rhs535_of_jS.h560`: for each `a`, the family of its instances at the pairs
  `(a₁,a₂) = (a, a₂)`, over all `a₂`, is jointly false w.h.p. So it cannot be supplied for all
  pairs, and `h535_of_jS` cannot be fed from it. For a single **far** pair (`zdist(a₁-a₂) > ℓ*`):
  - the case-(2) instances hold up to `≺` (paper (5.61));
  - the case-(1) instances (`b` within `ℓ*/2` of `a₁` or `a₂`) are neither claimed by the paper
    (which proves only the weaker (5.58)) nor refuted here. I leave them undetermined; they are
    never used.
- Regime statement asked by the ticket: `h560` can hold only if `jS^{3/2} ≳ s³A`
  (model regime), and it provably fails for all Hermitian `H` whenever
  `(s−κ/A)²Wℓ²η² > 168 jS^{3/2}(1+ε_{D'})` (deterministic regime).

**Correction to the ticket's and T1488/T1496's heuristic.** The configuration they cite
(`b = a₁`, far `a₂`, "`K₃ ≈ A⁻²`") is **not** a demonstrated violation:
- for `|a₁−a₂| ≥ ℓ*`, `K_{(−,+,+),(a₂,a₁,a₁)}` contains a long edge `Θ_t(a₂,·)` pinned near `a₁`
  by the short edge `Θ_{tm²}`, so it is `≤ W^{-D}` by (2.52)/(5.30);
- the diagonal part of `L3(a₂,a₁,a₁)` is `m·W⁻¹·L_{(−,+),(a₁,a₂)} ≤ 2W⁻¹jS·T(d) ≤ RHS`
  (`W⁻¹ ≤ A⁻¹`).

The genuine violation is at near and diagonal configurations. It is caught rigorously by the
Ward sum above, not by a pointwise `K₃` estimate.

### Target (T2): replacement — PASS (ticket-ready, two options)

`eGpm_le_rhs535` (frozen, abstract `Gm`) is **correct**: its `Gm` is free except for `h42` (far
pairs only) and nonnegativity. Only the instantiation `Gm := gmOfJS` breaks it. No frozen
signature needs to change.

**Option A (smallest hypothesis change; keeps `J := jS` up to an explicit loss `c`).**
Primed successor in a new file (for example `RBM1D/Hierarchy/Step2FarInputsH560.lean`):
```
theorem eGpm_le_rhs535_of_jS' (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}
    {ℓs D' c : ℝ} (hc : 1 ≤ c)
    -- every hypothesis of `eGpm_le_rhs535_of_jS` except `h560`, verbatim:
    (hL …) (hW …) (hℓu …) (hℓs …) (hηu …) (hA …) (hr …) (hD …) (a₁ a₂) {ρ κ} (hρ …) (hK …)
    (h273 …) (h554 …) (h557C …) (h557R …) (hone …) (hκ …)
    (h560' : ∀ b,
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (a₁ - a₂) : ℝ) →
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (a₂ - b) : ℝ) →
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (a₁ - b) : ℝ) →
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖
        ≤ c ^ 3 * (gmOfJS X E D' N u ω a₂ b * gmOfJS X E D' N u ω a₁ b
                    * gmOfJS X E D' N u ω a₂ a₁)) :
    ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) a₁ a₂‖
      ≤ rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) ℓs (etaT E u) D'
          (c ^ 2 * Step2.jS X E D' N u ω) ρ (zdist (B.L N) (a₁ - a₂))
```
At `c = 1` the conclusion is **verbatim** the current one.

Proof plan (one file, no core change). Apply `eGpm_le_rhs535` with `J := c²·jS` and
`Gm x y := if ℓ*/2 ≤ zdist(x−y) then c·gm x y else Λ`, where
`Λ := 1 + M + M/q₀²`, `M := ∑_b ‖L3(a₂,b,a₁)‖` and `q₀ := √(W^{-D'}) ≤ c·gm` on far pairs.
- `hJ`: `1 ≤ c²jS`.
- `h531`: `re_gloop_pm_le_jS_mul_tailT` together with `jS ≤ c²jS`.
- `h42`: `c√jS√T = √(c²jS)√T`.
- `h560`: if all three distances are `≥ ℓ*/2`, this is `h560'`. Otherwise at least one factor is
  `Λ` and the others are `≥ min(Λ, q₀)`, so the product is `≥ M` in every pattern (checked:
  `Λq₀² ≥ M`; `Λ²q₀ ≥ M` whether `q₀ ≤ 1` or `q₀ > 1`; `Λ³ ≥ M`).

Optional lemma: `rhs535 … (c²J) … ≤ c³ · rhs535 … J …` for `c ≥ 1` (degrees 1 and 3/2 in `J`),
the analogue of `rhs535_div_le`. Primed `h535_of_jS'` is the `∀ u ∈ Ico` wrapper.

Satisfiability of `h560'`. It follows deterministically from
`hjG : APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D' ≤ c² · jS`:
- (5.60) is `norm_gloop_three_le_gmBlk` (APrimeFirstCellEGFar.lean:140, all `b`, no hypothesis);
- `APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail` bounds each far entry by `√(jG·T)`.

`hjG` holds w.h.p. with `c = N^τ` for every `τ > 0`, by the following chain:
- `gsqBlk(x,y) ≤ max_{x'∼x} gmBlk(x',y)²`;
- (4.2) (`entry_bound_gauss`, fixed time, every `d`) gives
  `gmBlk(x',y)² ≺ ∑_{9 neighbours} L_{(+,−)} ≤ 9(jS+1)·T(d−2)`, where the neighbour `K` is
  `≤ W^{-D}` by (5.30);
- `T(d−2) ≤ e²T(d)` (`tailT_sub_le`).

So `jG ≤ 1 + N^ε·18e²·jS ≤ N^{2ε}jS`. This is nondegenerate: `jG, jS ≥ 1`, all dimensions
general, and it is a statement on the same event as (4.2).

**Option B (no replacement hypothesis at all).** `eGpm_le_rhs535_of_jG`: the hypotheses of
`eGpm_le_rhs535_of_jS` minus `hK` and `h560`, with conclusion `rhs535 … (jG) …`. Proof:
`eGpm_le_rhs535` with `J := jG`, `Gm := gmBlk`.
- `h560` is `norm_gloop_three_le_gmBlk`.
- `h42` is `gmBlk_le_sqrt_jG_tail`.
- `h531` holds because `re L_{(+,−),(x,y)} ≤ gmBlk(y,x)² = gmBlk(y,x)gmBlk(x,y) ≤ gsqBlk(x,y) ≤ jG·T`.
  Here `gmBlk` is symmetric because it maximizes over both charges and `G⁻ = Gᴴ`; the neighbour
  `x' = x` is in the sup since `SB x x ≠ 0`; the last step is `gsqBlk_le_jG_mul_tailT`.
- `1 ≤ jG` holds by definition.

This is the paper's (5.60)→(5.61) route verbatim: entries first, then (4.2)/(5.31) only on far
pairs. With `hjG`, `rhs535(jG) ≤ rhs535(c²jS) ≤ c³·rhs535(jS)`.

Recommendation: Option B as the (5.35) statement. `hjG` (w.h.p.) is a separate ticket if a
consumer must see `jS`. Estimates:
- Option B: 1 ticket (~150 lines, deterministic);
- Option A: 1 ticket (~250 lines, the `Λ` bookkeeping);
- `hjG` on a `HighProb` event from `entry_bound_gauss` + `hK` + `tailT_sub_le`: 1–2 tickets;
- rhs535 `c³` monotonicity: ½ ticket (can join A or B).

`eGpm_le_rhs535_of_jS` / `h535_of_jS` should be marked unusable (DECISIONS §10b stays). Their
`h560` should be recorded as a paper-delta (tag `T1499a`, see (d)).

### Target (T3): compiled refutation — PASS (necessary condition + `¬h560` in the deterministic regime; see (b))

There is **no clean deterministic counterexample of the form "explicit `H` with `¬h560`"**:
- for any explicit, non-diffusive `H` (diagonal, `H = 0`, …), `L_{(+,−)}` has no diffusive profile;
- so `|L−K|(a,a) ≍ K(a,a) ≍ A⁻¹` and `jS ≍ A`;
- then `h560`'s right side `jS^{3/2}T(0)^{3/2} ≈ A^{-3/2}` dominates, and `h560` actually holds
  at `(a,a,a)`. For example, for `H = 0`, `|L3(a,a,a)| = W⁻²|z|⁻³ ≤ A^{-3/2}`.

The failure is a random-model phenomenon: it needs `jS ≪ A^{2/3}`. The compiled content is
instead the deterministic necessary condition (★), for arbitrary Hermitian `H`, and its
`gmOfJS` + `hone` corollary. Together they give `¬h560` in the deterministic regime. This is a
negative statement about the hypothesis, compiled; it adds no hypothesis to anything.

Planned file `RBM1D/Hierarchy/H560Check.lean` (namespace `RBM.H560Check`):
1. `sum_gloop3_ward` — the identity of Step 1.
2. `two_inv_W_mul_sq_im_trace_le_re` — Step 2.
3. `sq_im_trace_le_sum_norm_gloop3` — `(Im tr(G E_a))² ≤ η W² ∑_b ‖L3(b,a,a)‖`.
4. `h560_diag_forces` — with abstract `Gm`, from the `h560` instances `(b,a,a)`.
5. `h535_h560_forces` — with `Gm := gmOfJS`, the `hone` instance at `a`, giving (★) with
   `(s − κA⁻¹)²` on the left.
6. `not_h535_h560` — `¬ h560` (the `h535_of_jS` form at one `u`) under `hone` and the strict
   inequality `RHS(★) < (s − κA⁻¹)²`. (This was added during the Lean stage; it is the
   contrapositive of item 5.)

## (b) Declarations, build, axioms

File: `RBM1D/Hierarchy/H560Check.lean` (worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1499`,
branch `t/T1499`, commit `ca712b8`). It imports only `RBM1D.Hierarchy.Step2FarInputs`. Nothing
else was touched. The root import is to be added at merge, per the ticket.

Public declarations, namespace `RBM.H560Check`:
- `wt`, `wt_nonneg`, `Eblk_eq_diagonal_wt`, `trace_mul_Eblk_mul_Eblk`, `trace_mul_Eblk`,
  `normSq_sub_conj`, `normSq_sub_conj_self`, `sum_ind_sq`, `sq_sum_wt_mul_le` (helpers).
- `sum_gloop3_ward` (Step 1):
  `(2 * I * z.im) * ∑ b, gloop L W H z ⟨[false,true,true],[b,a,a]⟩
   = (W:ℂ)⁻¹ * (gloop L W H z ⟨[true,true],[a,a]⟩ - gloop L W H z ⟨[false,true],[a,a]⟩)`.
- `two_inv_W_mul_sq_im_trace_le_re` (Step 2, `H` Hermitian):
  `2 * (W:ℝ)⁻¹ * (trace (green H z * Eblk L W a)).im ^ 2
   ≤ (gloop … ⟨[false,true],[a,a]⟩ - gloop … ⟨[true,true],[a,a]⟩).re`.
- `sq_im_trace_le_sum_norm_gloop3` (`H` Hermitian, `0 < z.im`):
  `(trace (green H z * Eblk L W a)).im ^ 2 ≤ z.im * W^2 * ∑ b, ‖gloop … ⟨[false,true,true],[b,a,a]⟩‖`.
- `h560_diag_forces`: the same bound with the right side `z.im * W^2 * ∑ b, Gm b a * Gm a a * Gm b a`,
  under `h560 : ∀ b, ‖gloop … [b,a,a]‖ ≤ Gm b a * Gm a a * Gm b a`. The function `Gm` is
  arbitrary.
- `sum_gmOfJS_diag_le`: `∑ b, gm b a * gm a a * gm b a ≤ jS * √jS * (A⁻² + W^{-D'}) *
  (168 ℓ A⁻¹ + L √(W^{-D'}))`, from `Lemma57.sum_sqrt_tailT_mul_le` at `a₁ = a₂ = a`.
- `h535_h560_forces` (Sample level). Hypotheses:
  - `0 < etaT E u`, `1 ≤ B.ell N u`;
  - `h560`, verbatim the `h535_of_jS` hypothesis at a fixed `u`;
  - `hone`, the `h535_of_jS` hypothesis at `σ = true`, block `a`;
  - `hκ : κA⁻¹ ≤ (mE E).im`.

  Conclusion: `((mE E).im − κA⁻¹)^2 ≤ etaT E u * W^2 * (jS * √jS * (A⁻² + W^{-D'}) *
  (168 ℓ A⁻¹ + L √(W^{-D'})))`.
- `not_h535_h560`: `¬ (h560 at u)` under `hone`, `hκ` and `hgt : RHS < ((mE E).im − κA⁻¹)^2`.

No new hypothesis enters any existing theorem: these are consequences of `h560`, not inputs.
The only hypotheses beyond `h560` are `hone`/`hκ`, which `h535_of_jS` already assumes, plus
positivity. The regime of `hgt`, `(s−κ/A)²Wℓ²η² > 168 jS^{3/2}(1+W^{-D'}-terms)`, is
nondegenerate. Example: `s ≍ 1`, `κ ≤ 1`, `jS ≤ N^δ`, `ℓ = (1−u)^{-1/2} ≤ L`,
`η = s(1−u) ≥ N^{2δ}/W`. Then `Wℓ²η² = Wηs ≥ N^{2δ}s² ≫ 168 N^{3δ/2}`, at every `N`.

Build:
```
$ lake build RBM1D.Hierarchy.H560Check
✔ [3770/3770] Built RBM1D.Hierarchy.H560Check
Build completed successfully (3770 jobs).
```
No `sorry`/`admit`/`axiom`. There are no warnings in `H560Check.lean`; the warnings printed
come from the already-built `Step2FarInputs.lean`.

Axioms (`lake env lean` on a scratch file importing the module), for each of
`sum_gloop3_ward`, `two_inv_W_mul_sq_im_trace_le_re`, `sq_im_trace_le_sum_norm_gloop3`,
`h560_diag_forces`, `sum_gmOfJS_diag_le`, `h535_h560_forces`, `not_h535_h560`:
`[propext, Classical.choice, Quot.sound]`.

## (c) Key lemmas used

`sum_gloop_head`, `trace_green_sub_trace_green_conj'`, `gloop_two`, `Gsig_conjTranspose`,
`isUnit_sub_smul_one_of_im_ne_zero` (Loop layer); `trace_Eblk`; `Lemma57.sum_sqrt_tailT_mul_le`,
`Lemma57.zdist_sub_comm`, `zdist_zero`, `tailT_nonneg`; `Step2Moment.one_le_jS`;
`etaT_eq_zt_im`, `mSigma_true`; Mathlib `Finset.sum_mul_sq_le_sq_mul_sq`, `Complex.re_le_norm`,
`norm_sum_le`, `Complex.abs_im_le_norm`, `Finset.single_le_sum`.

Paper inputs of the model-level part of (T1): (2.58), (2.52), Lemma 2.18 / (2.68) at time `u`,
(2.72), (5.47). They are used only to show falsity in the full regime; none of them is used in
Lean.

## (d) Open issues

1. Model-level part of (T1). The full-regime refutation (`c₀'s³A ≤ jS + N^ε + 337 jS^{3/2}`) is
   argued on paper only. It uses (2.58) with a Fourier lower bound, and the `(+,+)` 2-loop
   local law (Lemma 2.18). It is not compiled. The compiled part covers the deterministic
   regime `(s−κ/A)²Wℓ²η² > 168 jS^{3/2}(1+o(1))`, roughly `Wη ≫ jS^{3/2}`. It does not cover the
   smallest `η` (`η ≲ jS^{3/2}/W`), where the refutation needs the model. The Fourier
   bound `K_{(+,−),(a,a)} − Re K_{(+,+),(a,a)} ≥ c s³ A⁻¹` could be compiled from `Kgen`/Ward.lean if
   wanted (≈1 ticket). It is not needed for the decision.
2. For a single far pair, the case-(1) instances of `h560` (`b` within `ℓ*/2` of `a₁` or `a₂`)
   are undetermined here. They are unused, and both replacements drop them.
3. The ticket's statement of the obstruction (`b = a₁`, far `a₂`, "`K₃ ≈ A⁻²`") is not a valid
   counterexample (see (a) "Correction"). The same applies to T1488 open issue #2 and
   T1496 §T2. The verdict is nevertheless the same ("false"), established by the Ward argument
   at near/diagonal instances.
4. Paper-delta candidate (not written; the sole writable files are this report and
   `H560Check.lean`), tag `T1499a`:
   - `Step2FarInputs.eGpm_le_rhs535_of_jS`/`h535_of_jS` encode (5.60)+(5.61) with
     `Gm := gmOfJS` for all `b` and all pairs.
   - The paper states (5.61) only in case (2), and (5.60) with actual entries.
   - The Lean hypothesis is false w.h.p. (this report).
   - Replacement: Option B (`J := jG`, `Gm := gmBlk`), or Option A (case-(2) `h560'` with loss `c³`,
     conclusion at `J := c²jS`).
5. Downstream: the (5.35) route through `rhs535` (M3/M4) remains usable via Option A or B.
   `eGpm_le_rhs535_of_jS`/`h535_of_jS` themselves should stay banned (DECISIONS §10b).
   `rhs535_div_le` (T1496) composes with either option.
