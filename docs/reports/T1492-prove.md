Prover model: claude-sonnet-5

# T1492: (4.2) ⇒ (5.57), column and row forms, at (2.73)-reduced strength, on one high-probability event

## 0. Method

Sources read (only these, per the ticket): `CLAUDE.md` §3; `docs/reports/T1488-prove.md` §1
(rows A1–A3, for (2.73)/(2.74)/(4.2)) and §3 (target **M2**, and the common notation/"Step-1
hypotheses" paragraph at the top of §3); the Lean files M2 names as sources
(`RBM.Gauss.entryBoundFlow_floor`, `RBM.Step1.apriori`, `RBM.Gauss.step1Hyp_gauss_of_scale''`,
`RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`), plus the declarations they depend on
that were needed to state the exact Lean shapes (`RBM.Lemma57.blkW`/`sum_blkW`,
`RBM.OffPair`/`goodSet`/`Lre`, `RBM.GoodEvent`, `RBM.Gauss.EntryBoundFlow'`,
`RBM.Step1.Hyp`/`.apriori`, `RBM.Cond272Reg`, `RBM.Band.ell`/`scale`, `RBM.Step3.ellHat_mono`,
`RBM.etaT_mul_ellHat_le`, `RBM.EEBridge.eeFacts`), all `#check`-ed or read at their `theorem`/
`def` line in the worktree before use.

## (a) Math preflight (per target), written before any Lean edit

### Step 0 (read-only checks)

Every source M2 names was `#check`-ed (via reading the file at its cited line) and its
hypotheses confirmed:

* `RBM.Gauss.entryBoundFlow_floor (d : Dims) (hE : |E| < 2) (hs0) (hst) (ht1) {K} (hK : 0 ≤ K) (hη) {c₀} (hc₀ : 0 < c₀) (hδ) {B} (hB : 0 ≤ B) : EntryBoundFlow' d E s t (fun N => 2*N^(-B))` — `EntryBoundFlow'` unfolds (by `def`, checked to unify directly with `StochDom.highProb`) to a `StochDom` over `TimeIcc s t N × OffPair d.L d.W N`. **This already gives the uniform-in-`u` form** (the whole `u`-range sits inside the `∃` of `StochDom`'s `badSet`, per `RBM.StochDom`'s definition in `RBM1D/Defs/StochDom.lean`) — the ticket's Step-0 worry ("if any source only gives fixed-`u` statements") does **not** apply to this source.
* `RBM.Step1.apriori (hκ)(hE)(hB)(hs0)(hst)(ht1)(hc:Cond272)(hc0)(hreg)(h:Step1.Hyp) : ∀ n ≥ 1, StochDom (…‖L_{u,σ,a}‖…) (…(ℓ_u/ℓ_s)^{n-1}(A_u)⁻¹^{n-1}…)` over `TimeIcc s t N × LoopData (B.L N) n` — likewise already uniform in `u`. At `n = 2` this is the `(+,-)` `2`-loop `L_{(+,-)}`, exponent `1`.
* `RBM.Gauss.step1Hyp_gauss_of_scale'' (d)(hκ)(hE)(hB)(hs0)(hst)(ht1)(hcond:Cond272)(hc0)(hreg) : Step1.Hyp (sample d) E s t` for **every** `d : Dims`, hypotheses exactly the "Step-1 hypotheses" list of `docs/reports/T1488-prove.md` §3.
* `RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow (d)(hE)(hs0)(hst)(ht1)(hc)(hreg:Cond272Reg)(hB) : HighProb (P d) (goodSetFlow d E s t (flowDelta d E t))`, for every `d`. **Defect found and avoided**: the *other* candidate with the same base name, `RBM.APrimeGeneralMovingGoodSetFlowActual.highProb_goodSetFlow`, is hard-wired to a private `d := Dims.exampleGrow` and does **not** take `d` as an argument; it is not usable for a general-`d` statement. The `APrimeGoodSetFlowGeneralDims` version (T1369, already used inside `highProb_commonEvent` in `Gauss/APrimeGeneralMovingDriftSourceGeneralDims.lean`) is the correct, general one, and it needs `Cond272Reg (band d) E s t c`, not the bare `Cond272` in the Step-1 list; `Cond272Reg B E s t c := Cond272 B E s t ∧ (∀ᶠN, N^c ≤ B.scale E N (t N))` (`RBM1D/Flow/Iteration.lean:385`), so it is built for free as `⟨hcond, hreg⟩` from the two Step-1 hypotheses already in hand — no new hypothesis is added.
* Two further deterministic facts, checked at their statement: `RBM.Step3.ellHat_mono (hst : s ≤ t)(ht1 : t < 1) : ellHat L s ≤ ellHat L t` (gives `ℓ_s ≤ ℓ_u`, hence `r := ℓ_u/ℓ_s ≥ 1`, for `u ∈ [s_N,t_N]`); `RBM.etaT_mul_ellHat_le (hL : 3 ≤ L)(hE : |E| ≤ 2)(ht0 : 0 ≤ t)(ht1 : t < 1) : etaT E t * ellHat L t ≤ 1` (gives `A_u = Wℓ_uη_u ≤ W`, hence `W⁻¹ ≤ A_u⁻¹`, and `A_u ≤ N` from `RBM.EEBridge.eeFacts` + `Dims.dim`, hence the additive floor of `entryBoundFlow_floor` is `≤ A_u⁻¹` once its exponent `B` is taken `≥ 2`).

### Target statement vs. paper formula

M2 (`docs/reports/T1488-prove.md` §3): for `d : Dims` under the Step-1 hypotheses, `∀ τ > 0`,
`HighProb (P d) {ω | ∀ u : TimeIcc s t N, ∀ x y p, p.1 = y → ∑_r blkW(r,x)·‖G_u(r,p)‖ ≤
N^τ·√(ℓ_u/ℓ_s)·(√A_u)⁻¹}`, together with the row form, on the same event. This is the
Lean shape of (5.57) (`docs/reports/T1488-prove.md` row A3: "the paper's
`W⁻¹max_y Σ_x|G_xy| ≺ (Wℓ_uη_u)^{-1/2}(1+J*(Wℓ_uη_u)^{-1})`") **at the (2.73)-reduced strength**
— i.e. the weaker, `J*`-free exponent `√r·A_u^{-1/2}` that (2.73)'s Step-1 loop bound, not the
full local law, gives directly. Quantifier order: `d, κ, E, s, t, hypotheses, τ` — fixed
parameters before `τ`, and `τ` before the `HighProb`'s own `∀D` (inside `HighProb`'s definition);
matches the paper's order (fix the model, then quantify the loss). No `N = 0`/empty-index-set
vacuity: `TimeIcc s t N` is a real interval `[s_N,t_N]` (nonempty since `s_N ≤ t_N`), `ZMod (d.L N)`
and `Fin (d.W N)` are nonempty since `d.L N ≥ 3`, `d.W N ≥ 1`.

### Dependencies

All four named sources are already-accepted, committed declarations (root import closure);
`Cond272Reg`, `Band.ell`/`scale`, `Step3.ellHat_mono`, `etaT_mul_ellHat_le`, `EEBridge.eeFacts`
like-wise. No forward reference to anything not yet on `main`.

### Hypotheses: satisfiability, no widening

(T1)/(T2)'s hypothesis list is **exactly** `step1Hyp_gauss_of_scale''`'s list (verbatim: `0<κ`,
`|E|≤2-κ`, `BoundsCore (sample d) E s`, `∀N,0≤sN`, `∀N,sN≤tN`, `∀N,tN<1`, `Cond272 (band d) E s t`,
`0<c`, `∀ᶠN,N^c≤(band d).scale E N (tN)`) plus `τ>0` — no hypothesis is added, none dropped, none
weakened into a stronger form. Simultaneous satisfiability: this is the identical list discharged
in every general-`Dims` ticket that used it, witnessed non-vacuously (not by an astronomically
large parameter) by `RBM.APrimeGeneralMovingDriftSourceGeneralDims.eventually_commonEvent_nonempty`
(`docs/reports/T1488-prove.md` §3, common-notation paragraph), which the auditor is asked to cite.

### Boundary cases

`u = s_N` (start of the window): `r = ℓ_u/ℓ_s = 1 ≥ 1`, everything above still holds (`≤`, not
`<`). `x = y` (diagonal block): handled uniformly, no case split needed in the final statement
(the diagonal *point* `v = p`, resp. `v = r`, is excluded from `OffPair` and is bounded instead by
`GoodEvent.norm_diag_le`; whether that point's *block* equals the other's block is irrelevant to
the argument). `A_u` large or small: the proof only uses `A_u ≤ N` and `A_u ≤ W_N` (both
deterministic, no lower bound on `A_u` needed beyond `A_u > 0`, which `Band.scale_pos'` gives from
`u < 1`).

### Verdict

**PASS** for both (T1) and (T2), at the (2.73)-reduced strength exactly as M2 states it (not the
full local-law (5.57), and not a weaker one — the loss is a single `N^τ`, matching M2's own
statement of the target). No workaround was needed: the one Step-0 concern (a fixed-`u`-only
source) does not arise, since both `entryBoundFlow_floor` and `Step1.apriori` are already stated
uniformly over `u ∈ TimeIcc s t N`.

## (b) Declarations added, build, axioms

File: `RBM1D/Gauss/Step2Eq557.lean` (sole writable file), namespace `RBM.Gauss.Step2`.

* `RBM.Gauss.Step2.highProb_eq557_colRow` — **(T2)**: the column and row forms of (5.57) on the
  same event, exactly as M2 states them.
* `RBM.Gauss.Step2.highProb_eq557_col` — **(T1)**: the column form alone, obtained from (T2) by
  `HighProb.mono` (drop the row conjunct).
* Two private helper lemmas used only inside this file: `sqrt_add_le_aux` (subadditivity of
  `Real.sqrt` on nonnegatives) and `blockSum_le` (the Cauchy–Schwarz / diagonal-split
  combinatorial core: given a diagonal bound `1+δ` at a point `i0` and an off-diagonal control
  `Cx` at every other point, the `blkW`-weighted block average of a nonnegative kernel is at most
  `√(Cx) + √(Wb⁻¹)(1+δ)`; this is the single-`G` analogue of
  `RBM.Lemma57.norm_gloop_three_le_schwarz`, which does the same Cauchy–Schwarz step for the
  `3`-loop).

Build:
```
lake build RBM1D.Gauss.Step2Eq557
```
Result: **success** (3879 jobs; "Build completed successfully"). No `sorry`, `admit`, or `axiom`
in the file (checked by `grep`). Two harmless lints remain (a "flexible tactic" note on one
`simp … at hmem` used twice downstream, and one line over 100 characters); neither is an error
and neither affects correctness.

Axioms (via `lake env lean` on a scratch file `import RBM1D.Gauss.Step2Eq557` +
`#print axioms …`):
```
'RBM.Gauss.Step2.highProb_eq557_col' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2.highProb_eq557_colRow' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three standard axioms, as required.

Commit: on branch `t/T1492` in the worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1492`, file
`RBM1D/Gauss/Step2Eq557.lean` only.

## (c) Key lemmas used

`RBM.Gauss.step1Hyp_gauss_of_scale''`, `RBM.Gauss.entryBoundFlow_floor` (+ its regime inputs
`RBM.Gauss.rpow_neg_one_le_etaT_of_scale_ge`, `RBM.Gauss.flowDelta_le_rpow_neg`),
`RBM.Step1.apriori` at `n = 2`, `RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`,
`RBM.Cond272Reg`, `RBM.StochDom.highProb`, `RBM.HighProb.inter`/`.mono`,
`RBM.Lemma57.blkW`/`blkW_nonneg`/`sum_blkW`, `RBM.Lre`/`Lre_nonneg`, `RBM.GoodEvent.norm_diag_le`,
`RBM.card_sbSupport`, `RBM.Step3.ellHat_mono`, `RBM.etaT_mul_ellHat_le`, `RBM.one_le_ellHat_of_nonneg`,
`RBM.EEBridge.eeFacts`, `RBM.Sample.Lval`/`RBM.Gauss.sample_Lval`, `Finset.sum_mul_sq_le_sq_mul_sq`
(Cauchy–Schwarz), `RBM.eventually_le_rpow`, `Complex.re_le_norm`.

## (d) Open issues

1. **Loss constant, not optimized.** The proof's internal exponent split (`τ0 := τ/4` for both
   the entry-bound and the apriori event, an additive floor `B := 2`) is chosen only to make the
   arithmetic close comfortably; it is not claimed to be sharp. This does not affect the
   statement, which is `∀ τ > 0` (any positive loss suffices).
2. **`RBM.APrimeGeneralMovingGoodSetFlowActual.highProb_goodSetFlow` is not usable for a general
   `d`.** This module's own name collides with the general one; a reader who greps only the
   short name and picks the first hit will get a theorem hard-wired to `Dims.exampleGrow`. This
   was already implicit in `docs/reports/T1488-prove.md` row A2 (which cites the general-`Dims`
   version by its full module path), but the collision itself is worth a `paper-deltas.md`
   remark; tag `T1492a` (not added to `docs/paper-deltas.md` here, since the sole writable file
   for this ticket is `RBM1D/Gauss/Step2Eq557.lean` and this report).
3. Per M2's own text, the (2.73)-reduced strength proved here is what feeds **M4** ((5.35) on one
   event) and σ's check list; whether it (rather than the weaker APrime route's
   `κ₂ = (Wℓ_tη_t)^{-1/6}+W^{-1}`) is actually the one A5 needs is left to A5's assembly, exactly
   as `docs/reports/T1488-prove.md` §3 leaves it.
