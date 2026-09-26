Prover model: claude-opus-5-5[1m]

(Repair after audit RETURN `docs/reports/T1516-audit.md`. The original T0-T4 and their preflight
below were written by the original prover, claude-sonnet-5, and are kept unchanged; the repairer's
additions are the section "Repair preflight" and the "Repair: Lean" section at the end.)

# T1516 — the grid Duhamel expansion of `A_k`

Ticket: `docs/tickets/T1516.md`. Sole writable file: `RBM1D/Gauss/GridExpansion.lean`.

## Math preflight (written before any Lean)

Notation as in the ticket: fixed `N`, grid `u_j := time s t K N j`, `Δ := step s t K N`;
`A_j ω := fun a => Lval B E N u_j (H_j ω) a − Kv B E N u_j a`; `U_{j,k} := Uker (B.L N)
(fun _ => 1) u_j u_k`; `D_j ω := (eGterm + primBil(A_j,A_j))(H_j ω)`; `R_j` the T1506 (T4)
remainder.

### Step 0 checks (read only)

* T1485 `duhamel_telescope` (generic `V : AddCommGroup`, family `U : ℕ→ℕ→V→+V` with
  `hself`/`hcomp` for **all** `i≤j≤k : ℕ`, not merely up to a cutoff), `UkerHom`,
  `Uker_grid_semigroup` (takes an arbitrary sequence `u : ℕ → ℝ` with `∀ k i, ‖(u k:ℂ)*ξ i‖<1`
  for **every** `k:ℕ`). Consequence for T3/T4: since our concrete grid times `time s t K N j`
  exceed `1` for `j > K N` (the affine formula is unbounded), the semigroup hypothesis cannot be
  discharged for the raw sequence at all `k:ℕ`. Fix (recorded as part of the route, not a
  weakening of any statement): use the *clamped* sequence `uClamp j := time s t K N (min j (K N))`,
  which stays in `[s N, t N] ⊆ [0,1)` for every `j : ℕ` and agrees with `time s t K N j` exactly
  on `j ≤ K N` (`min j (K N) = j` there). `duhamel_telescope` is invoked with this family, and its
  conclusion at any fixed `k ≤ K N` is read back through the agreement, so no loss occurs and (T3)
  is unconditionally about `time`, not `uClamp`.
* T1505 `stepXi`/`stepZ`/`stepY`/`stepDecomp`/`integrable_Phi_H`: `stepXi = stepZ + stepY`
  holds **pointwise for every `ω`** (not merely a.e.), since `stepY := stepXi − stepZ` by
  definition; this removes one layer of a.e. bookkeeping from the route. `stepDecomp`'s
  hypotheses (`hΦ`, `hReal`, `hC₂`, `hIntReal`) are all satisfiable, discharged below.
* T1506 `discrete_hierarchy_step`: a.e. `ω`, `∀ a`, `‖E[A_{k+1}(a)|F_k](ω) − U_{k,k+1}A_k(ω)(a)
  − Δ·D_k(ω)(a)‖ ≤ stepErr`, with `ξ = xiOf (mSigma E) ![true,false]`, rewritten to `fun _ => 1`
  via `Step2.sigPM_xi`. This is *exactly* what (T2) restates with `R_k` named by subtraction.
* T1509 `Uker_one_nonneg`: every kernel entry of `Uker L (fun _=>1) u v` (`0≤u≤v<1`) is a
  nonnegative real; this is what makes (T1)'s `ukerMat` well-defined (`.re` loses nothing).
* `MomentDuhamel.lkFun`, `Step2.sigPM`, `sigPM_xi`, `Gsig`: `lkFun B E N u M Step2.sigPM a`
  unfolds (by the definitions of `lkFun`, `Lval`, `Kv`, `LoopData.idx`, and `Step2.sigPM :=
  ![true,false]`) to *exactly* `Lval B E N u M a − Kv B E N u a`; this is a definitional identity,
  not an estimate. **(T0) verdict: PASS**, provable by unfolding plus `List.ofFn` on `Fin 2`.

### `hReal` — actually discharged, not assumed (ticket's explicit demand)

`Φ_{u,a} M := loopObs (B.toDims) N (zt E u) ⟨[true,false],List.ofFn a⟩ M − Kv B E N u a` (the
`loopObs`-based, globally-`C²` version of `Lval − Kv` that `TestFun` needs; it agrees with
`Lval M a − Kv u a` on the Hermitian submanifold by `loopObs_of_isHermitian`, which is enough
since the grid flow `H_j ω` is always Hermitian, `H_isHermitian`). Reality on Hermitian `M`:

* **`(+,-)` `2`-loop part.** `RBM.gloop_two_plus_minus_nonneg` (`Loop/GLoop.lean`, already
  merged, no hypothesis on `z`): for Hermitian `H`, `gloop L W H z ⟨[true,false],[a,b]⟩ = (r:ℂ)`
  for an explicit `r = W⁻²·Σ_{β,α}‖G_{(b,β),(a,α)}‖² ≥ 0`. This *is* the "(+,-) 2-loop trace
  `⟨G(z)E_{a0}G(z̄)E_{a1}⟩ ≥ 0`" argument the ticket names (proved there via `Gsig_conjTranspose`,
  i.e. `G(z̄) = G(z)ᴴ` for Hermitian `H`, folded into a sum of `Complex.normSq`). Hence
  `.im = 0`.
* **`Kv` part.** `Kv B E N u a = B.Kval E N u ⟨[true,false],List.ofFn a⟩ = (B.Kval, Kgen_two,
  kTwo unfolded) = (W:ℂ)⁻¹ · μ · Theta (B.L N) ((u:ℂ)·μ) (a 0)(a 1)`, `μ := mSigma E true *
  mSigma E false = mE E * conj(mE E) = (Complex.normSq (mE E) : ℂ)` (via `Complex.mul_conj`;
  `mSigma E true = mE E`, `mSigma E false = conj (mE E)` by definition), so `μ` and `(u:ℂ)·μ` are
  real. `RBM.ChargeReduce.conj_Theta_apply` (already merged) gives `conj (Theta L ξ a b) =
  Theta L (conj ξ) a b` for `‖ξ‖<1`; since `conj((u:ℂ)·μ) = (u:ℂ)·μ`, `Theta (B.L N) ((u:ℂ)·μ)
  (a 0)(a 1)` is fixed by conjugation, hence real. The needed norm bound `‖(u:ℂ)·μ‖<1` is
  `RBM.norm_mul_mSigma_lt_one hE.le hu0 hu1 true false` (`0≤u<1`). Hence `(Kv B E N u a).im=0`.

Both pieces are *actually proved* below (not assumed), using only already-merged public lemmas
(`gloop_two_plus_minus_nonneg`, `ChargeReduce.conj_Theta_apply`, `norm_mul_mSigma_lt_one`,
`Complex.mul_conj`), matching the ticket's Step 0 requirement. **Verdict: hReal PASS** (it is a
genuine theorem here, with an explicit nondegenerate witness: any `|E|<2`, `0≤u<1`).

### `hC₂`

`bddC2C_loopObs` (`Gauss/LoopC2.lean`, merged) gives, at `B := 2·(1+η⁻¹)³` (any `0<η≤|Im z|`),
an **explicit constant** `C₂ = card(B.Idx N)·(2²·B²)` for the `2`-loop (`I.a.length = 2`
uniformly, since the loop shape `[true,false]` is fixed), the *same* for every label `a`, so
`hC₂ : ∀ a M, ‖D²Φ_{u,a} M‖ ≤ C₂` holds with one constant. Subtracting the `M`-independent
constant `Kv B E N u a` does not change any derivative (`fderiv (Φ - c) = fderiv Φ`, proved once
as a two-line helper `testFun_sub_const`/`fderiv2_sub_const`). **Verdict: PASS.**

### `hIntReal`

Re-proved here (T1505's own scratch discharge is not carried over as a dependency, since it was
deleted per that audit): `stepZ = h0 −(shift) ... `, precisely: from `g_eq_pointwise`,
`g = h0 + Zc + R` **pointwise**, where `g,h0,R` (complex-valued) are integrable by
`integrable_h0`/`integrable_Rlabel_sum` (both already merged, T1505), so `Zc = g − h0 − R` is
integrable; `stepZ = Zc.re` (`Complex.ofReal_re`), and `Integrable.re` (Mathlib) plus
`RCLike.ofReal_re` transfers integrability from `Zc` to the real function `stepZ`.
**Verdict: PASS**, using only the finitely many already-merged lemmas named above; no new
estimate.

### (T1) `ukerMat`, `Uker_eq_sum_ukerMat`

`ukerMat L u v b a := (Uker L (fun _=>1) u v (Pi.single a 1) b).re`. Since `Uker L (fun_=>1) u v
(Pi.single a 1) b` collapses (by `Uker_apply` and `Finset.sum_eq_single`) to the single kernel
entry `∏ i, edgeKer L 1 u v (b i)(a i)`, which `Uker_one_nonneg hL hu0 huv hv1 b a` (T1509,
argument order `(b,a)` matching `Uker_apply`'s `(outer, inner)` roles) shows is `(r:ℂ)`, `r≥0` —
so `.re` recovers it exactly, no information lost, and `Uker L (fun_=>1) u v A b = Σ_a (ukerMat L
u v b a:ℂ)·A a` is then a direct rewrite of `Uker_apply` termwise. Nonnegativity of `ukerMat` is
the same `r`. **Verdict: PASS** for `0 ≤ u ≤ v < 1` (the hypotheses under which `Uker_one_nonneg`
applies); this is exactly the ticket's stated range.

### (T2) `condExp_A_succ`

`R_j ω a := E[A_{j+1}(a)|F_j](ω) − U_{j,j+1}(A_j ω)(a) − Δ·D_j(ω)(a)` (definition by
subtraction, so the displayed equation is immediate); the norm bound `‖R_j ω a‖ ≤ stepErr B E N
u_j u_{j+1} Δ` is *exactly* T1506's `discrete_hierarchy_step`'s conclusion after rewriting
`xiOf (mSigma E) ![true,false]` to `fun _=>1` via `Step2.sigPM_xi hEb.le` (`![true,false]` is
`Step2.sigPM` by definition) and unfolding `⟨[true,false],List.ofFn a⟩` on both sides. Hypotheses
carried verbatim from `discrete_hierarchy_step`: `|E|<2`, `s N<t N`, `j<K N`, `0≤u_j`, `u_{j+1}<1`.
**Verdict: PASS** — this is a restatement, no new estimate, matching the ticket's own
description ("restates T1506... with R named").

### (T3) `grid_expansion`, (T4) `grid_expansion_all`

Route exactly as the ticket's §Route, checked term by term above (semigroup via the clamp,
`stepXi = stepZ+stepY` pointwise, `Uker_eq_sum_ukerMat` + `condExp_finsetSum`/`condExp_smul`
(Mathlib, unconditional a.e. identity, no new hypothesis) for the first bracket, `condExp_A_succ`
for the second bracket, `Uker_add`/`Uker_smul`/`Uker_comp` (all already merged, T1485/Kernel.lean)
for the deterministic linear-map algebra). The two brackets' images under `U_{j+1,k}` combine
into *exactly* the ticket's four summands (`stepZ`, `stepY`, `Δ·U(D_j)`, `U(R_j)`), each a.e., and
the finitely many a.e. sets (over `j < k`, all `b`, for (T3); additionally over `k ≤ K N` for
(T4)) intersect via `ae_all_iff` (index types `ℕ`/`LoopArg (B.L N) 2` both countable), exactly the
pattern `discrete_hierarchy_step` itself uses at its own end (`ae_all_iff.mpr hlabel`). No
hypothesis is added beyond `|E|<2, 0≤s N, s N<t N, t N<1, K N≥1` (needed for the grid times to
stay inside `[0,1)`, for `duhamel_telescope`'s clamp trick, and for `discrete_hierarchy_step`'s own
hypotheses at each step `j<K N`). **Verdict: PASS** for both targets, modulo the mechanical Lean
work below; if any single gluing step below fails to close without weakening, this report is
updated to BLOCKED with the precise obstacle before merge is attempted (see "Open issues" in the
final report for the actual outcome).

### Boundary / satisfiability check

Witness carried by the ticket's own hypothesis list: `E = 0` (`|E|<2`), `s N := 0`, `t N := 1/2`
(`0≤s N`, `s N<t N`, `t N<1`), `K N := 4` (`K N ≥ 1`), any `k ≤ K N` (e.g. `k=2`); every grid time
`time s t K N j` for `j ≤ K N` then lies in `[0, 1/2] ⊂ [0,1)`, a nondegenerate window with `k≠0`,
`K N > k` allowed (no vacuous `N=0`, empty index set, or astronomically large parameter). No
`∀ᶠ N` degeneracy — the statement is for a single fixed `N`.

## Repair preflight (written before any repair Lean)

Audit defect addressed (the only RETURN reason): in T3/T4 the kernel is folded into the label
weight (`U := ukerMat u_{j+1} u_k` inside `stepZ`/`stepY`), whereas T1504 (T1'/T1''/T2) needs
`(Σ_{j<k} Uker ξ (u(j+1)) (u k) (Z (j+1) ω)) a` with a label vector `Z : ℕ → Ω → LoopArg L 2 → ℂ`
independent of the target `k` (checked against `GridDuhamelTail.lean`
`stopped_duhamel_azuma_tail` / `stopped_duhamel_cheb_tail` on `main`). All additions are
additive; T0-T4 are untouched. Notation: `δ b a := if b = a then (1:ℝ) else 0`.

### (R1) `stepZ_ukerMat_eq_Uker` (pointwise)

`stepZ U b ω = √Δ · lin N (Ab U b ω) X`, `Ab U b ω = Σ_a (U b a : ℂ) • gradMat (Φ a) (H_j ω)`,
`lin N A X = (trace (A X)).re`. `trace` is additive and `ℂ`-homogeneous, and `re((r:ℂ) z) = r re z`
for real `r`, so `lin N (Ab U b ω) X = Σ_a U b a · lin N (gradMat (Φ a) (H_j ω)) X` for every real
kernel `U`. With `U = δ` the sum collapses: `stepZ δ a ω = √Δ · lin N (gradMat (Φ a) (H_j ω)) X`.
Hence, for every real `U`, every `ω`, `b`: `stepZ U b ω = Σ_a U b a · stepZ δ a ω` (no
hypotheses at all). With `U = ukerMat L v w` and T1 `Uker_eq_sum_ukerMat` (needs `3 ≤ L`, which
holds for `L = d.L N` by `Dims.three_le_L`, and `0 ≤ v ≤ w < 1`):
`Uker L 1 v w (fun a => (stepZ δ a ω : ℂ)) b = Σ_a (ukerMat b a : ℂ) · stepZ δ a ω`, which is the
cast of the previous sum. **Verdict: PASS.** Hypotheses `0 ≤ v ≤ w < 1` are exactly those of
`Uker_eq_sum_ukerMat`; satisfiable (e.g. `v = w = 0`, or grid times `u_{j+1} ≤ u_k` in `[0,1/2]`).

### (R2) `stepY_ukerMat_eq_Uker_ae` (a.e.)

`stepXi U b ω = Σ_a (U b a) Φ_a(H_{j+1} ω) − E[Σ_a (U b a) Φ_a(H_{j+1}) | F_j](ω)`. Pointwise
`Σ_c (δ a c) Φ_c(H_{j+1} ω) = Φ_a(H_{j+1} ω)` (as functions of `ω`), so
`stepXi δ a ω = Φ_a(H_{j+1} ω) − E[Φ_a(H_{j+1}) | F_j](ω)`. Conditional expectation is linear over
a finite sum of integrable functions and real (here `ℂ`-cast) scalars (`condExp_finsetSum`,
`condExp_smul`); integrability of `ω ↦ Φ_a(H_{j+1} ω)` is T1505 `integrable_Phi_H` from
`TestFun (Φ a)`. Hence a.e. (one null set for all `b`, since labels are finite, `ae_all_iff`):
`stepXi U b ω = Σ_a U b a · stepXi δ a ω`. Subtracting (R1)'s pointwise identity for `stepZ` gives
the same for `stepY = stepXi − stepZ`, and then `Uker_eq_sum_ukerMat` as in (R1). The single
extra hypothesis `hΦ : ∀ a, TestFun d N (Φ a)` is necessary in general (without integrability the
conditional expectation is `0` and linearity fails) and is discharged in the use by T1516's own
`Φgrid_testFun` (`|E| < 2`, `u < 1`), so it is not a hidden assumption of the primed T3/T4.
**Verdict: PASS.**

### (R3) `grid_expansion'` (T3′), `grid_expansion_all'` (T4′)

Label vectors, independent of the target `k`: `Zvec i ω a := (stepZ (i−1) (Φgrid u_i) δ a ω : ℂ)`,
`Yvec i ω a := stepY (i−1) (Φgrid u_i) δ a ω`, so that `Zvec (j+1) ω a = stepZ j (Φgrid u_{j+1}) δ a ω`
(`j+1−1 = j`). For `j < k ≤ K N`, `0 ≤ u_{j+1} ≤ u_k ≤ t N < 1`, so (R1) and (R2) apply to the
`j`-th Z- and Y-summands of T3 (`Φ := Φgrid u_{j+1}`, `v := u_{j+1}`, `w := u_k`), a.e. over the
finite set `{j < k} × labels` (and, for T4′, over `k ≤ K N`; `ae_all_iff` on countable index
types). Then `Σ_j Uker(u_{j+1},u_k)(Zvec (j+1) ω) b = (Σ_j Uker(u_{j+1},u_k)(Zvec (j+1) ω)) b` by
`Finset.sum_apply`. I also write the drift and R sums in the applied-vector form of their
consumers: `(Σ_j (Δ:ℝ) • Uker(u_{j+1},u_k)(D_j ω)) b` (T1510 `weighted_duhamel_sum_stopped`) and
`(Σ_j Uker(u_{j+1},u_k)(R_j ω)) b` (T1504 (T3) `stopped_duhamel_det_bound`). These are equal to the
T3 forms by `Finset.sum_apply`, `Pi.smul_apply`, `Complex.real_smul`. Hypotheses are the same as
T3/T4 (`|E|<2`, `0 ≤ s N`, `s N < t N`, `t N < 1`, `1 ≤ K N`, `k ≤ K N`). Boundary case `k = 0`:
all sums are empty, as in T3. Witness: the one already recorded below (`E = 0`, `s N = 0`,
`t N = 1/2`, `K N = 2`). No `∀ᶠ N`. **Verdict: PASS** for both.

## Lean

All five targets went through **after** the PASS preflight above; no target was weakened, no
hypothesis was added beyond what the preflight lists, and no cited lemma (T1485, T1505, T1506,
T1509) was reproved or altered. The route matched the preflight exactly; the only genuine
obstacles hit were mechanical Lean ones (Dims-vs-Band index/label spelling, and `Matrix
(B.Idx N)` picking up the plain product topology while `Matrix (B.toDims.Idx N)` picks up the
`Matrix.Norms.L2Operator` scoped norm `TestFun`/`loopObs` need), both fixed without touching any
statement's mathematical content — see "Open issues" below.

### Declarations added (`RBM1D/Gauss/GridExpansion.lean`, `namespace RBM.Gauss.Grid`)

* `lkFun_eq_Lval_sub_Kv` (T0).
* `ukerMat`, `Uker_eq_sum_ukerMat`, `ukerMat_nonneg` (T1).
* `Φgrid`, `Φgrid_of_isHermitian`, `testFun_sub_const`, `Φgrid_im_eq_zero` (hReal, actually
  discharged), `Φgrid_testFun`, `Φgrid_bdd2` (hC₂, explicit uniform constant) — the Step‑0
  discharge machinery.
* `Agrid`, `Dgrid`, `Rgrid`, `condExp_A_succ` (T2).
* `grid_duhamel_telescope` (private: the clamped T1485 telescope, read back at `time`),
  `stepZ_integrable` (private: `hIntReal` re-derived), `grid_step_summand_ae` (private: the
  per-`j` `Z+Y+ΔD+R` split), `time_mono` (private).
* `grid_expansion` (T3), `grid_expansion_all` (T4).

### Build commands and results

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1516 && lake build RBM1D.Gauss.GridExpansion
```
`Build completed successfully (3817 jobs)` (only 3 pre-existing-style `longLine` warnings, no
errors). `grep -n "sorry\|admit\|axiom" RBM1D/Gauss/GridExpansion.lean` — no matches.

### Axioms

`#print axioms` for `lkFun_eq_Lval_sub_Kv`, `ukerMat`, `Uker_eq_sum_ukerMat`, `ukerMat_nonneg`,
`Φgrid_im_eq_zero`, `condExp_A_succ`, `grid_expansion`, `grid_expansion_all` all give exactly
`[propext, Classical.choice, Quot.sound]`.

### Key lemmas used (all already merged)

T1485 `duhamel_telescope`, `UkerHom`, `Uker_grid_semigroup`; T1505 `stepZ`, `stepY`, `stepXi`,
`stepDecomp`, `g_eq_pointwise`, `integrable_h0`, `integrable_Rlabel_sum`, `integrable_Phi_H`;
T1506 `discrete_hierarchy_step`, `Lval`, `Kv`; T1509 `Uker_one_nonneg`; `MomentDuhamel.lkFun`;
`Step2.sigPM`, `Step2.sigPM_xi`; `gloop_two_plus_minus_nonneg` (`Loop/GLoop.lean`);
`ChargeReduce.conj_Theta_apply`; `norm_mul_mSigma_lt_one`, `Complex.mul_conj`;
`bddC2C_loopObs`, `testFun_loopObs_of_im_le`, `loopObs_of_isHermitian`; Mathlib
`condExp_finsetSum`, `condExp_smul`, `Integrable.re`, `RCLike.ofReal_re`, `ae_all_iff`.

### Open issues (mechanical, non-mathematical; recorded for the auditor)

* **Two spellings of the same matrix type.** `Matrix (B.Idx N) (B.Idx N) ℂ` (T1506's own
  convention) and `Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ` (what `loopObs`/`TestFun`/
  `bddC2C_loopObs` are stated for) are the same type by `Band.toDims_Idx` (`rfl`), but the file
  opens `Matrix.Norms.L2Operator`, and the L2-operator `NormedAddCommGroup`/`NormedSpace`
  instance is only found through the `B.toDims.Idx N` spelling (`B.Idx N` alone picks up the
  plain product topology, which is not even a normed space instance usable by `fderiv`). `Φgrid`
  is therefore stated with `M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ` throughout, and the
  bridge to `Lval`/`Kv` (`B.Idx N`-typed) is the one-line `Φgrid_of_isHermitian`. This is a
  spelling choice, not a mathematical restriction: `Φgrid`'s domain is exactly the matrices the
  grid flow `H B.toDims s t K N j ω` already lives in.
* **`rw`/`congr` vs. `exact`/`show` on this same diamond.** Several intermediate identities
  (`Uker_apply`'s indicator collapse, the `Φgrid`↔`Lval` bridge, `stepXi`'s unfolding, the
  `Finset.sum`/`Pi.sub_apply` bookkeeping) needed `show`+`exact`/`rw`-at-a-freshly-typed-hypothesis
  instead of `congr`/direct `rw` on the goal, because `congr` triggered a `whnf` timeout and plain
  `rw` could not match across the `B.L N` / `B.toDims.L N` (or `B.Idx N` / `B.toDims.Idx N`)
  spelling difference even though both sides are definitionally equal. No lemma's *statement* was
  touched by this; it is purely proof-script plumbing, and every such spot is a `private` lemma or
  a `have` internal to a proof (`stepZ_integrable`, `grid_step_summand_ae`,
  `grid_duhamel_telescope`, `Φgrid_bdd2`), not part of the four/five public statements the ticket
  names.
* No other open issues. The ticket's acceptance criteria (exact names T0–T4; the four sums in
  (T3) exactly matching the input shapes T1504/T1510 will need; `hReal` actually discharged; the
  a.e. quantifier in (T4) covering all `k ≤ K N` and all labels at once) are all met as stated.

## Repair: Lean (repairer, claude-opus-5-5[1m])

Branch `t/T1516`, commit `edb89af` (on top of the audited `7cc0dda`). Only
`RBM1D/Gauss/GridExpansion.lean` was changed, and the change is purely additive: T0-T4 and all
their helpers are byte-for-byte unchanged.

### Declarations added (`namespace RBM.Gauss.Grid`)

* `gridDelta L b a := if b = a then (1:ℝ) else 0`: the identity label kernel `δ`.
* `stepZ_eq_sum_gridDelta` (pointwise, no hypotheses, for any real `U`):
  `stepZ d s t K N j Φ U b ω = Σ_a U b a * stepZ d s t K N j Φ (gridDelta (d.L N)) a ω`.
* **(R1) `stepZ_ukerMat_eq_Uker`**: for every `ω` and `0 ≤ v ≤ w < 1`,
  `(stepZ d s t K N j Φ (ukerMat (d.L N) v w) b ω : ℂ) = Uker (d.L N) (fun _ => 1) v w (fun a => (stepZ d s t K N j Φ (gridDelta (d.L N)) a ω : ℂ)) b`.
* `stepXi_eq_sum_gridDelta_ae` (`hΦ : ∀ a, TestFun d N (Φ a)`, any real `U`): a.e., for all `b`,
  `stepXi U b ω = Σ_a (U b a : ℂ) * stepXi δ a ω`.
* `stepY_eq_sum_gridDelta_ae`: the same statement for `stepY`.
* **(R2) `stepY_ukerMat_eq_Uker_ae`** (`hΦ`, `0 ≤ v ≤ w < 1`): a.e., for all `b`,
  `stepY d s t K N j Φ (ukerMat (d.L N) v w) b ω = Uker (d.L N) (fun _ => 1) v w (fun a => stepY d s t K N j Φ (gridDelta (d.L N)) a ω) b`.
* `Zvec B E s t K N i ω a := (stepZ B.toDims s t K N (i-1) (Φgrid B E N (time s t K N i)) (gridDelta (B.L N)) a ω : ℂ)` and
  `Yvec` (the same with `stepY`), with `Zvec_succ` and `Yvec_succ` (`rfl`):
  `Zvec (j+1) ω a = stepZ j (Φgrid u_{j+1}) δ a ω`. These vectors do not depend on the target `k`.
* private `grid_ZY_bridge_ae`: the per-step Z/Y bridge at the grid, for `j < k ≤ K N`.
* **(T3′) `grid_expansion'`** (same hypotheses as T3). For fixed `k ≤ K N`, a.e. ω, ∀ b:
  `Agrid k ω b = Uker(u_0,u_k)(Agrid 0 ω) b + (Σ_{j<k} Uker(u_{j+1},u_k)(Zvec (j+1) ω)) b + (Σ_{j<k} Uker(u_{j+1},u_k)(Yvec (j+1) ω)) b + (Σ_{j<k} step • Uker(u_{j+1},u_k)(Dgrid j ω)) b + (Σ_{j<k} Uker(u_{j+1},u_k)(Rgrid j ω)) b`.
  In every sum, `Uker = Uker (B.L N) (fun _ => (1:ℂ))`, the times are `(time s t K N (j+1) : ℂ)` and `(time s t K N k : ℂ)`, and the smul is `ℝ • (LoopArg → ℂ)`.
* **(T4′) `grid_expansion_all'`**: `∀ᵐ ω, ∀ k, k ≤ K N → ∀ b, …` with the T3′ body. One null set
  covers all `k ≤ K N` and all labels (`ae_all_iff` over `k : ℕ`, trivial for `k > K N`).

Shape check against the consumers on `main`:
* Z sum = T1504 `stopped_duhamel_azuma_tail` shape `(Σ_{j∈range k} Uker L ξ (u(j+1)) (u k) (Z (j+1) ω)) a`, with `ξ = fun _ => 1`, `u = time s t K N`, `Z = Zvec B E s t K N`.
* Y sum = the same shape for `stopped_duhamel_cheb_tail`, with `Y = Yvec …`.
* R sum = `stopped_duhamel_det_bound`, with `R = Rgrid …`.
* Drift sum = T1510 `weighted_duhamel_sum_stopped` shape `(Σ_j Δ • Uker L 1 (u(j+1)) (u k') (A j)) a`, with `A = fun j => Dgrid … j ω`.

In each case the target index `k` is instantiated by the consumer (`τ ω` or `min k (τ ω)`, both `≤ K N`, so T4′ covers them).

### Build and axioms

```
cd /Users/junyin/Lean_proof/RBM1D-wt/T1516 && lake build RBM1D.Gauss.GridExpansion
```
Result: `Build completed successfully (3817 jobs)`, with only linter warnings (longLine etc.).
`grep sorry|admit|^axiom` finds no matches.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of: `gridDelta`,
`stepZ_eq_sum_gridDelta`, `stepZ_ukerMat_eq_Uker`, `stepXi_eq_sum_gridDelta_ae`,
`stepY_eq_sum_gridDelta_ae`, `stepY_ukerMat_eq_Uker_ae`, `Zvec`, `Yvec`, `Zvec_succ`, `Yvec_succ`,
`grid_expansion'`, `grid_expansion_all'`, and the unchanged `grid_expansion` and `grid_expansion_all`.

`git grep` on `main` finds none of the new public names, so there are no clashes.

### Key lemmas used (repair)

* T1505: `Ab`, `stepZ`, `stepXi`, `stepY`, `lin`, `integrable_Phi_H`. The `lin`/`Ab` linearity is re-proved as private `lin_Ab_eq_sum'`, because T1505's `lin_Ab_eq_sum` is private.
* T1516: `Uker_eq_sum_ukerMat`, `Φgrid_testFun`, `grid_expansion`.
* `Dims.three_le_L`.
* Mathlib: `condExp_finsetSum`, `condExp_smul`, `ae_all_iff`, `Finset.sum_eq_single`, `Finset.sum_apply`, `Complex.real_smul`.

### Open issues

* The one extra hypothesis of (R2) is `hΦ : ∀ a, TestFun d N (Φ a)`. It is needed for the integrability behind conditional-expectation linearity. In T3′/T4′ it is discharged internally by `Φgrid_testFun`, so T3′/T4′ carry exactly T3's hypotheses.
* Adaptedness of `Zvec (j+1)` / `Yvec (j+1)` to `filt (j+1)` is required downstream by T1504 (`hZ`/`hY`). It is not part of this ticket and was not proved here.
* I appended the paper-deltas entry `T1516a` (Φgrid convention + vector form) to `docs/paper-deltas.md`. The dispatcher assigns the number.
