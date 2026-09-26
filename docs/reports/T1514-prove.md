Prover model: claude-opus-5-5[1m]
(Repairer after audit RETURN, 2026-09-26. Original prover: claude-sonnet-5. See the "Repair" section at the end.)

# T1514 — math preflight (written before any Lean)

Ticket: R3a, the single-label quadratic variation on the good set, with the one-step time
shift. Sole writable file: `RBM1D/Gauss/GridQVStep.lean`.

Notation as in the ticket: `Φ_{u,a} := fun M' => MomentDuhamel.lkFun (band d) E N u M' Step2.sigPM a`
(a fixed 2-loop, `a : LoopArg (d.L N) 2`, `Step2.sigPM : Fin 2 → Bool = (+,-)`), `T_w(a) :=
tailT W ℓ_w η_w D (zdist (a 0 − a 1))`.

## Step 0 (read-only checks)

- `lkFun` (`MomentDuhamel.lean:144`): `gloop L W M (zt E u) idx − Kval E N u idx`; `Kval` does
  not depend on `M`, so `coordD1(lkFun) = coordD1(gloop)` (confirmed: this identification is
  already a merged lemma, `RBM.EarlyQVRate.coordD1_lkFun_eq`, `Gauss/EarlyQVRate.lean:106`, and
  it further identifies `coordD1(gloop)` at a Hermitian `M` with `coordD1(loopObs)`, via
  `coordD1_hermFun`).
- `coordD1_loopObs_eq` (`Gauss/LoopLeibniz.lean:284`): explicit Leibniz formula, `coordD1
  (loopObs z I) M q = −∑_{k<I.a.length} tr(Bmat_q · loopCut(M,z,I,k))`.
- `loopCut` (`Gauss/DischargeBDG.lean:307`): `G(σ_k) E_{a_k} · P₁(z) · P₂(z) · G(σ_k)`, a
  5-factor matrix product with `P₁,P₂` themselves finite products of resolvents/blocks
  (`prodList`, `Gauss/DischargeBDG.lean:293`), **at the single spectral parameter `z`** (no
  other `z`-dependence anywhere in `loopCut`/`prodList`/`Eblk`). This is exactly the structure
  the ticket's route describes ("coordD1 of the 2-loop is a sum of products of two resolvents
  at `z_u` with one `E_a`-block insertion").
- `quadVar`, `usedCoord`, `gvar`, `coordD1` (`Gauss/MomentGronwall.lean:349`,
  `Gauss/Generator.lean:407,592`): `quadVar d N F M = ∑_{q∈usedCoord d N} gvar(crd q)·‖coordD1 F
  M q‖²`, a **finite weighted sum over a fixed (F-independent) index set** — so `√quadVar` is
  literally a weighted-ℓ² norm and the two-term Minkowski inequality
  `RBM.Gauss.sqrt_wsum_add_le` (`Gauss/APrimeDuhamel.lean:668`, already merged and generic in
  the weight/finset) applies with no new machinery.
- `diagShape'`, `diagNearRate`, `diagFarRate` (`Gauss/APrimeNearRem.lean:714`,
  `Gauss/APrimeQVEndpoint.lean:807,810`): `diagNearRate` does not depend on `J`; `diagFarRate` is
  an explicit sum of nonnegative-coefficient terms in `(2J)²,(2J)³`, hence monotone increasing
  in `J` for `J ≥ 0` (coefficients nonneg via `Lemma57.cFar2_nonneg`, needs `1 ≤ W`, `0 < ℓu`).
  `nearEpsilon` (`Gauss/APrimeNearRem.lean:271`, `EEDef` namespace) has a single `J²` factor with
  a manifestly nonnegative remaining coefficient, hence also monotone in `J≥0`.
- `sDet`, `tailT` and its lower bound (`Analysis/StretchedExp.lean:281,296`, `Gauss/
  EarlyQVRateEv.lean:580`): `tailT ≥ W^{-D}` unconditionally (`rpow_neg_le_tailT`); `tailT_mono_time`
  (`Gauss/GridDriftSum.lean:66`, already merged, T1510) gives `T_{u}(ℓ) ≤ T_{v}(ℓ)` for `u ≤ v <
  1` at the *same* `d`, using `ellHat` monotone increasing and `(1-t)m` monotone decreasing —
  exactly the ticket's `T_{u_j} ≤ T_{u_{j+1}}`.
- `loop_step_time_err` (`Gauss/GridLoopStep.lean:582`) and `norm_green_sub_le_of_herm`
  (`Gauss/GridDriftLip.lean:71`) are the paper's suggested route for the *value*-level time
  Lipschitz bound of a single loop observable; for (T1) here we need the **derivative**
  (`coordD1`) version, one level down. Rather than re-deriving it from the value-level FTC
  identity (which would need a nontrivial "Lipschitz ⟹ bounded directional derivative"
  meta-step, not available off the shelf), the proof goes directly through the **explicit**
  Leibniz formula `coordD1_loopObs_eq` and telescopes the two resolvent-difference identities
  `green M z − green M z' = (z−z')·green M z·green M z'` (`green_sub_green`,
  `RBM.Loop.GLoop`) at the **same** `M` (only `z` moves), combined with `‖z_u − z_{u'}‖ = |u−u'|`
  (`RBM.norm_zt_sub`, `Gauss/FlowHolder.lean:121`) and `‖green‖ ≤ η⁻¹` (`RBM.norm_green_le`,
  `Loop/Split.lean:513`). This is a strictly more elementary (matrix-algebra-only) route than
  the paper's Duhamel-style FTC, but it proves the *same* deterministic fact and uses only
  already-merged resolvent identities plus one small self-contained induction (a `prodList`
  telescoping lemma, mirroring the already-merged `norm_gloopProd_sub_le` in
  `Gauss/LoopLipschitz.lean:318`, adapted from the two-list `(σ,a)` shape to the single zipped
  `List (Bool × ZMod L)` shape that `prodList` uses). No paper formula is being reproved
  differently from how the paper states it: (T1) is a purely auxiliary deterministic lemma the
  ticket itself introduces to bridge the one-step time shift, not a numbered paper equation.

## Preflight per target

### (T1) `sqrt_quadVar_time_shift`

Statement vs. route: for `|E|<2`, `0 ≤ u ≤ u' < 1`, Hermitian `M`, every 2-loop `a`,
`√(quadVar Φ_{u',a} M) ≤ √(quadVar Φ_{u,a} M) + Csh·(u'−u)`, `Csh` explicit, polynomial in
`Fintype.card (d.Idx N)` and `(etaT E u')⁻¹`.

- Hypothesis order: fixed `d,N,E` before `u,u'`; no `∀ᶠ N` needed since the bound is
  **deterministic** at every `N` (no probability, matching the ticket's "Reuse status:
  deterministic, a fixed `M`; allowed").
- Quantifier order matches the paper's convention (all parameters before the per-`(u,M,a)`
  statement); no hidden existential.
- Boundary case `u = u'`: both sides equal `√(quadVar Φ_{u,a}M)` (RHS's extra term is `0`); the
  proof's bound also degenerates correctly to `0 ≤ 0` in the time-difference factor, no division
  by a possibly-zero quantity anywhere in the route (the only reciprocal used is `(etaT E
  u')⁻¹`, which is strictly positive since `u'<1,|E|<2`).
- Satisfiability of hypotheses: witnessed by e.g. `E=0, u=0, u'=1/2, M=0` (Hermitian), any `a`, any
  `d` with `d.L N ≥ 3` (always true, `Dims.three_le_L`); nondegenerate, `u<u'` strictly, `Csh>0`.
- Dependencies used: `RBM.EarlyQVRate.coordD1_lkFun_eq`, `RBM.Gauss.coordD1_loopObs_eq`
  (both already merged, T-independent deterministic identities), `RBM.green_sub_green`,
  `RBM.norm_green_le`, `RBM.norm_zt_sub`, `RBM.Gauss.sqrt_wsum_add_le` — all already-accepted,
  already-merged results; no forward reference.
- Verdict: **PASS**.

### (T2) `diagShape'_mono_J`

Statement vs. route: `diagShape'` monotone in `J` (`J≥0`, `J≤J'`) at fixed `ℓu,ℓs,ηu,D,Smax,ε`;
plus `nearEpsilon` monotone in `J`, and the "drop-the-indicator" bound
`diagShape' ≤ (diagNearRate+2ε+diagFarRate)·T²`. [repair] Both of these are now public:
`nearEpsilon_mono_J` and `diagShape'_le_dropIndicator`.

- Every summand of `diagFarRate` with `J`-dependence has an explicitly nonnegative coefficient
  (`Lemma57.cFar2_nonneg`, `1 ≤ W`, needs `0 < ℓu` — both available at every window point since
  `ℓ_t ≥ 1` always, `RBM.one_le_ellHat`); `diagNearRate` is `J`-free. Boundary `J=0`: reduces to
  the smallest value, no degeneracy (`diagFarRate` at `J=0` is finite and the inequality is an
  equality only for `J=J'=0`, non-vacuous test: `J=0<J'=1` gives a strict, checkable inequality).
- Hypotheses (`0<ℓu,0<ηu,1≤W,0≤J≤J',0≤Smax`) are simultaneously satisfiable, e.g. `ℓu=ηu=W=1,
  J=0,J'=1,Smax=0`.
- Dependencies: `Lemma57.cFar2_nonneg` (already merged); no forward reference.
- Verdict: **PASS**.

### (T3) `quadVar_step_le`

Statement vs. route: exactly the ticket's displayed conclusion, `Q'` written out in full (no
new definition introduced for it — the constituent pieces `diagNearRate`, `nearEpsilon`,
`diagFarRate`, and `Csh` from (T1) are the only symbols used, matched literally against the
ticket's formula so a later assembly ticket can close by `rfl`/`ring_nf` against T1508
amend-1's rate).

- Hypothesis order: `M` Hermitian, grid times `u_j ≤ u_j+Δ<1`, `J' ≤ J`, `hqv` (the per-`a`
  hypothesis at `u_j` with cap `J'`) — matches the paper's left-endpoint convention noted in
  the ticket ("that is the left-endpoint form of T1508 amend-1").
- Route composition, checked term-by-term above (T1 gives the time shift and `(x+y)²≤2x²+2y²`;
  T2's two monotonicity facts move `J'↦J` in both the direct slot and inside `nearEpsilon`; the
  drop-indicator bound turns `diagShape'` into the flat `(...)·T²` shape; `tailT_mono_time`
  moves `T_{u_j}↦T_{u_j+Δ}` (coefficient nonnegative, so squaring/monotone-multiplying is valid);
  `rpow_neg_le_tailT` absorbs the constant `2·Csh²·Δ²` term into `2·Csh²·Δ²·W^{2D}·T_{u_j+Δ}²`
  via `1 ≤ W^{2D}·T_{u_j+Δ}(a)²`) is a chain of already-merged, order-preserving steps on
  manifestly nonnegative quantities; no hidden strengthening of any hypothesis.
- Boundary `Δ = 0`: [repair] the ticket's hypothesis "`u_j ≤ u_{j+1} = u_j+Δ < 1`" means `0 ≤ Δ`, and
  the grid allows `Δ = 0` (when `s N = t N`). At `Δ = 0` the conclusion reduces to the `hqv` bound
  after the `J' ↦ J` monotonicity and dropping the indicator, which is true. The Lean statement now takes
  `hΔ : 0 ≤ Δ`. (The original text said "`Δ>0` is the ticket's own hypothesis"; that was wrong, and the
  audit returned the work for this reason.)
- Satisfiability: same witness family as (T1)/(T2) above, plus `hqv` itself is satisfiable
  because its right-hand side is `diagShape'` at a manifestly nonnegative value while `quadVar`
  can be made `0` by choosing `M` so that `Φ_{u_j,a}` is (locally) constant in the tested
  direction — not needed for the *proof*, only recorded here since the ticket demands a witness
  for the assembled hypotheses; a full simultaneous witness (`d,N,E,u_j,Δ,D,J,J',τ,M,a`
  satisfying every hypothesis at once, including `hqv`) is exhibited in the report's "witness"
  remark in §(Lean, below) via the deterministic bound `quadVar_nonneg` and `diagShape'`'s own
  nonnegativity (`diagNearRate,diagFarRate,tailT ≥ 0`), so `hqv` holds trivially whenever `N^τ ·
  diagShape'(...) ≥ 0`, i.e. always — hence the hypothesis set is non-vacuously satisfiable for
  *every* choice of the other parameters, in particular a family that is not "astronomically
  large" (e.g. `D=60,J=J'=0,τ=1`).
- Dependencies: (T1), (T2) above (both proved in this same file), `tailT_mono_time`
  (`Gauss/GridDriftSum.lean:66`, T1510, already merged), `rpow_neg_le_tailT`
  (`Analysis/StretchedExp.lean:296`, already merged). No forward reference; T1497 is used only
  for the *shape* of `hqv` (as the ticket specifies), not invoked as a proof dependency here.
- Verdict: **PASS**.

## Conclusion

All three targets PASS the preflight. Proceeding to Lean.

---

# Lean (post-preflight)

File: `RBM1D/Gauss/GridQVStep.lean` (the ticket's sole writable file), all in namespace
`RBM.Gauss.Grid`.

## Declarations added

Public (the three targets, plus one supporting public constant/lemma):

* `qvTimeShiftConst (d : Dims) (N : ℕ) (E u' : ℝ) : ℝ` — the explicit `Csh` of (T1):
  `16 * √2 * (Fintype.card (d.Idx N) : ℝ)^2 * (1 + (etaT E u')⁻¹)^6`.
* `qvTimeShiftConst_nonneg`.
* `sqrt_quadVar_time_shift` — **(T1)**.
* `diagShape'_mono_J` — **(T2)**.
* `quadVar_step_le` — **(T3)**, with `Q'` written out in full in the conclusion (no new
  definition for it), matching the ticket's displayed formula term-by-term
  (`diagNearRate(ℓ_{u_j}, ℓ_s, η_{u_j}) + 2·nearEpsilon(…, J) + diagFarRate(ℓ_{u_j}, η_{u_j}, D,
  J, sDet(u_j, ℓ_s))`, plus `2·Csh²·Δ²·W^{2D}`, all multiplied by `2·N^τ` resp. left alone, then
  the whole sum times `T_{u_{j+1}}(a)²`).

Private helpers (all in the same file, needed only internally):

* `band_toDims_eq`, `norm_single_le`, `norm_Bmat_le_two`, `gvar_le_one`,
  `sum_gvar_usedCoord_le` — the coordinate-weight/`Bmat`-norm bounds (mirrored from the
  `private` copies in `Gauss/APrimeQVGlobalPolyCore.lean`, reproved here since that file's
  copies are not importable).
* `norm_Eblk_le_one`, `norm_prodList_le_pow`, `norm_prodList_sub_le` — a self-contained
  telescoping bound for `prodList` (mirroring the already-merged `norm_gloopProd_le_pow` /
  `norm_gloopProd_sub_le` of `Gauss/LoopLipschitz.lean`, adapted from the two-list `(σ, a)`
  shape to `prodList`'s single zipped list).
* `gsig_bounds`, `norm_loopCut_time_sub_le` — the uniform resolvent envelope/increment at two
  times `u ≤ u'` and the resulting `loopCut` time-Lipschitz bound (`≤ 4·K⁶·(u'-u)`,
  `K := 1 + η_{u'}⁻¹`), via the resolvent identity `G(z) - G(z') = (z - z')·G(z)·G(z')`
  (`RBM.green_sub_eq`, `Gauss/FlowHolder.lean`) and `‖z_u - z_{u'}‖ = |u - u'|`
  (`RBM.norm_zt_sub`).
* `norm_coordD1_loopObs_time_sub_le` — sums the `loopCut` bound over the two edges `k < 2` of
  the fixed `2`-loop and multiplies by the `‖Bmat‖ ≤ 2` and `card(idx)` factors from
  `coordD1_loopObs_eq`'s explicit Leibniz formula.
* `diagFarRate_mono_J`, `diagShape'_mono_eps`, `nearEpsilon_mono_J`, `diagShape'_le_sum` — the
  remaining monotonicity/drop-indicator facts (T2), used only by (T3)'s proof.

## Build commands and results

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1514 && lake build RBM1D.Gauss.GridQVStep
```
`Build completed successfully (3844 jobs)`, 0 errors. One residual style-linter warning
(`hSmax` in `diagFarRate_mono_J` is unused — kept for the mathematically meaningful
hypothesis name, matching the paper's `J, Smax ≥ 0` convention even though `Real.sqrt`'s totalized
non-negativity makes it unnecessary for this particular proof step).

## Axioms

```
#print axioms RBM.Gauss.Grid.sqrt_quadVar_time_shift
#print axioms RBM.Gauss.Grid.diagShape'_mono_J
#print axioms RBM.Gauss.Grid.quadVar_step_le
```
All three: `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `axiom`.

## Key lemmas used (already merged, not reproved)

`RBM.EarlyQVRate.coordD1_lkFun_eq`, `RBM.Gauss.coordD1_loopObs_eq`, `RBM.green_sub_eq`,
`RBM.norm_green_le`, `RBM.norm_Gsig_le`, `RBM.norm_Gsig_sub_le_norm_green_sub`,
`RBM.norm_green_sub_le` (`Gauss/FlowHolder.lean`), `RBM.norm_zt_sub`, `RBM.Gauss.etaT_le_of_le`,
`RBM.Gauss.etaT_pos_of_lt_one'`, `RBM.Gauss.Grid.tailT_mono_time` (T1510),
`RBM.rpow_neg_le_tailT`, `RBM.Cutoff.one_le_rpow_mul_tailT_sq`, `RBM.Gauss.sqrt_wsum_add_le`,
`RBM.Lemma57.cNear2_nonneg`, `RBM.Lemma57.cFar2_nonneg`, `RBM.EarlyQVRateEv.sDet_nonneg`,
`RBM.Gauss.Dims.nonempty_Idx`, `RBM.sum_Sblk_row`, `RBM.Sblk_nonneg`.

## Open issues / notes for the auditor

1. **Route deviates from the ticket's literal suggestion for (T1) at one point.** The ticket's
   route sketch cites `loop_step_time_err` (`Gauss/GridLoopStep.lean:582`) and
   `norm_green_sub_le_of_herm` (`Gauss/GridDriftLip.lean:71`) — both are *value*-level (the loop
   observable itself, via the paper's Duhamel/FTC identity), whereas (T1) needs a
   *derivative*-level (`coordD1`) time modulus. A value-level Lipschitz bound alone does not
   bound the derivative's time-difference (a bounded function can have an unbounded pointwise
   derivative). The proof instead goes through the already-merged **explicit** Leibniz formula
   `coordD1_loopObs_eq` and telescopes the resolvent identity directly at the `loopCut` level —
   the same "`G(z') - G(z) = (z' - z)G(z')G(z)`, `‖G‖ ≤ η⁻¹`" identity the ticket names, just
   applied to the derivative's explicit formula rather than re-derived through the value-level
   FTC. This is recorded as the one place the Lean route differs from the ticket's route
   description; the *statement* proved is exactly (T1) as specified.
2. **`Csh`'s exact polynomial form** is `16·√2·(L·W)²·(1+η_{u'}⁻¹)⁶` up to the crude bound
   `Fintype.card(d.Idx N) ≤ L·W` — looser than the ticket's illustrative
   `≤ C·L·W·η_{u'}⁻³`, but the ticket only requires "explicit and at most polynomial in `N`",
   which this satisfies (both `Fintype.card(d.Idx N)` and `η_{u'}⁻¹` are themselves at most
   polynomial in `N` under the paper's standing bandwidth/window hypotheses, though that fact
   is not needed or used inside this file).
3. **Witness for (T3)'s hypotheses (not compiled, argued mathematically).** Fix any `d : Dims`
   (e.g. `Dims.exampleGrow`), `N`, `E = 0`, `u_j = 0`, `Δ = 1/4` (so `u_j + Δ = 1/4 < 1`),
   `D = 64 ≥ 0`, `ℓ_s = 1 > 0`, `J' = J = 1 ≥ 0` (so `J' ≤ J`), `M = 0` (Hermitian). With
   `J = 1 > 0`, `diagFarRate(...) > 0` strictly for every `a` (its `(2J)^2, (2J)^3` terms have
   strictly positive coefficients built from `Lemma57.cFar2 > 0`, `D ≥ 0`), hence
   `diagShape'(..., a) > 0` for every `a` (finitely many `a`, since `LoopArg (d.L N) 2` is a
   finite type). `quadVar(Φ_{0,a})(0)` is a fixed finite non-negative real for each of the
   finitely many `a` (a finite sum of norms of directional derivatives of a smooth function at a
   point). Since `N^τ → ∞` as `τ → ∞` (for `N ≥ 2`) while `diagShape'(..., a) > 0` is fixed, `τ`
   can be chosen (uniformly over the finitely many `a`) large enough that `hqv` holds for every
   `a`; this `τ` is not "astronomically large" relative to the other data — it only has to
   exceed the (fixed, finite) ratio `log(quadVar)/log(N)` for each of finitely many `a`. All
   other hypotheses (`huj0, hΔ, hu'1, hℓs, hJ'0, hJ'J, hM`) are immediate from the concrete
   choices above. A fully compiled numeric `example` was not built (it would require restating
   an explicit numeric bound on `quadVar(Φ_{0,a})(0)`, e.g. via the already-merged
   `EarlyQVRate.quadVar_lkFun_le_norm_eeFun`, purely to pin down how large `τ` must be) — flagged
   here for the auditor rather than left silent.
4. `diagFarRate_mono_J`'s `hSmax : 0 ≤ Smax` hypothesis is unused in the proof (kept for
   parity with the paper's `Smax ≥ 0` convention); the `sq`/`cube` monotonicity argument does not
   need it because `Real.sqrt` is total and non-negative regardless of sign.

---

# Repair after audit RETURN (claude-opus-5-5[1m], 2026-09-26)

The audit report is `docs/reports/T1514-audit.md`. This repair covers its required fixes 1 and 2, plus the optional fix 3.

1. **(T3) `quadVar_step_le`.** The hypothesis `(hΔ : 0 < Δ)` is now `(hΔ : 0 ≤ Δ)`. This is the ticket's
   `u_j ≤ u_{j+1} = u_j + Δ`, and it matches the `0 ≤ step` carried by T1508/T1512. The proof is unchanged
   because it never used strictness. Nothing else in the signature changed, and `Q'` is still written out
   literally.
2. **(T2) helpers made public.** These were the ticket's "and so is the nearEpsilon term" and "Also: … dropping
   the indicator" statements.
   - `RBM.Gauss.Grid.nearEpsilon_mono_J`: was `private`. Its statement is unchanged:
     `0 ≤ W → 0 ≤ L → 0 ≤ J → J ≤ J' → nearEpsilon W L ℓu ηu D J ≤ nearEpsilon W L ℓu ηu D J'`.
   - `RBM.Gauss.Grid.diagShape'_le_dropIndicator`: was `private diagShape'_le_sum`. Its statement is unchanged:
     `1 ≤ W_N → 0 < ℓu → 0 < ℓs → 0 < ηu → 0 ≤ ε → diagShape' … J Smax ε b ≤ (diagNearRate … + 2ε + diagFarRate … J Smax) · tailT(…, zdist(b0−b1))²`.
3. **Optional cleanup.** The unused `hSmax` in the private `diagFarRate_mono_J` is renamed `_hSmax`, and one
   docstring line over 100 characters is wrapped. The module now builds with no warnings from `GridQVStep.lean`.

(T1) `sqrt_quadVar_time_shift`, `qvTimeShiftConst` and `diagShape'_mono_J` did not change.

**Build.** I ran `cd /Users/junyin/Lean_proof/RBM1D-wt/T1514 && lake build RBM1D.Gauss.GridQVStep`. Result:
`Build completed successfully (3844 jobs)`, with no warnings or errors in `GridQVStep.lean`.

**Axioms.** These are the in-file `#print axioms` results.

| Declaration | Axioms |
|---|---|
| `RBM.Gauss.Grid.sqrt_quadVar_time_shift` | `[propext, Classical.choice, Quot.sound]` |
| `RBM.Gauss.Grid.diagShape'_mono_J` | `[propext, Classical.choice, Quot.sound]` |
| `RBM.Gauss.Grid.nearEpsilon_mono_J` | `[propext, Classical.choice, Quot.sound]` |
| `RBM.Gauss.Grid.diagShape'_le_dropIndicator` | `[propext, Classical.choice, Quot.sound]` |
| `RBM.Gauss.Grid.quadVar_step_le` | `[propext, Classical.choice, Quot.sound]` |

**Other checks.** The file contains no `sorry`, `admit` or `axiom`.

**Commit.** `97a181d` on `t/T1514`. Only `RBM1D/Gauss/GridQVStep.lean` changed.

**Open issues.** None new. The (T3) witness from audit item (D) still applies, because weakening `0 < Δ` to
`0 ≤ Δ` only enlarges the set of admissible parameters.
