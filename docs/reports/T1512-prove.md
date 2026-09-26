Prover model: claude-opus-5-5[1m] (repairer, after audit RETURN; original prover: claude-sonnet-5)

# T1512 — prove report

## (a) Math preflight (before any Lean)

Targets, per the ticket (`docs/tickets/T1512.md`) and `docs/supervisor/2026-09-25-2045.md` §3 (i).

**Step 0 checks (read-only), recorded first.**

* `v`, `lin`, `coordFinset`, `linVar` (`Gauss/GridMarkov.lean`): `v N A` is `linVar (gvar d)
  (fun c => lin N A (Xmat (single c))) (coordFinset N)`, and `coordFinset N` is the image of
  **all** raw coordinates `d.Idx N × d.Idx N × Bool` (at size `N`) under `crd d N` — i.e. every
  `(i,j,b)` pair, not just the canonical representative `usedCoord d N` picks per unordered pair.
  `GridMarkov.lean` has a private `v_eq_sum` unfolding this (inaccessible outside that file, so
  T1512 reproves the same one-line fact locally wherever it is needed).
* `gvar` (`Gauss/Model.lean:204`) is defined on **all** of `Coord d` (both `(i,j,b)` and
  `(j,i,b)` for `i ≠ j` get the same value `Sblk(i,j)/2`), consistent with `coordFinset`'s wider
  index set.
* `quadVar`, `usedCoord`, `crd`, `coordD1`, `Bmat` (`Gauss/MomentGronwall.lean:349`,
  `Gauss/Generator.lean`): `quadVar` sums only over `usedCoord d N` (the canonical
  `(min,max)`-ordered representative, `mem_usedCoord`). `Xentry`/`Xmat` (`Gauss/Model.lean:244`)
  always read off the coordinate of the canonical representative in `idxKey` order; consequently
  `Xmat d N (Pi.single c 1) = 0` for every raw coordinate `c` outside the image of `usedCoord d N`
  under `crd d N` (proved here from the existing `Xmat_eq_sum`, `Gauss/Generator.lean:417`, which
  gives `Xmat d N ω = Σ_{p∈usedCoord} ω(crd p) • Bmat p` for *every* `ω`, hence in particular for
  `ω = Pi.single c 1`).
  **Consequence for (T2):** the extra terms of `v`'s sum outside `usedCoord` are identically `0`
  on *both* sides regardless of the direction `A`, so (T2) is provable as an **equality**, not
  merely `≤` — the ticket's alternative ("prove `≤` with the extra terms `0`") is not needed; a
  genuine `=` is available and stronger, and is what is proved below.
* `qv_conv_le`, `Uker_one_nonneg` (`Gauss/GridQVConv.lean`, T1509, merged): read exactly as
  stated; the hypothesis shape is `EE : LoopArg L 2 → LoopArg L 2 → ℂ`, `‖EE a a'‖ ≤ √(R a)√(R a')`,
  `R a ≤ Q·tailT(dist a)²`, conclusion a bound on `‖Σ_a Σ_a' (∏edgeKer b a)·conj(∏edgeKer b a')·EE
  a a'‖`. No `U⁻¹`, no M7b, matches the ticket's "reuse status" note.
* The `quadVar` bound `RBM.highProb_quadVar_diagShape_of_jS` gives (`Gauss/Step2QVEvent.lean`),
  after its `diagShape' ≤ Q·tailT²` step, is a pointwise bound `quadVar d N Φ_a M ≤ Q·tailT(...,
  dist a)²` at a sample matrix `M` (in the downstream use, `M = H_j ω` on the stopped event). This
  is **exactly** the shape (T3)'s `hqv` hypothesis below consumes — **no mismatch** found; the
  ticket's Step-0 concern does not materialize, so Lean writing proceeds under the ticket's own
  contingency ("only after PASS").

**(T1) `RBM.Gauss.Grid.vB`, `v_sum_eq`, Cauchy–Schwarz.** Verdict: **PASS**.
`vB N A A' := Σ_{c∈coordFinset N} gvar(c)·lin(A,c)·lin(A',c)` is literally the covariance form of
the two centred Gaussians `lin N A ∘ Xmat`, `lin N A' ∘ Xmat` (both linear combinations of the
same independent coordinates `Xmat d N (Pi.single c 1)` of variance `gvar c`), so `vB A A = v A`
by unfolding `v`/`linVar` and reordering one multiplication (`ring` per term) — a one-line proof,
matching the auditor's stated check. The general identity `v(Σ_i r_i•A_i) = Σ_i Σ_i' r_i r_i' vB(A_i,A_i')`
is the bilinear expansion of the variance of a linear combination of jointly-Gaussian linear
forms, valid for any real weights `r : ι → ℝ` over a `Fintype ι` (no hypothesis beyond
`Fintype ι`, hence trivially satisfiable, e.g. `ι = PUnit`, `r = 1`, giving back `vB A A = v A`).
Cauchy–Schwarz `|vB A A'| ≤ √(v A)·√(v A')` is the finite Cauchy–Schwarz inequality
(`Finset.sum_mul_sq_le_sq_mul_sq`) applied to `f c = √(gvar c)·lin(A,c)`, `g c = √(gvar c)·lin(A',c)`;
no hidden hypothesis, no vacuity (holds for every `N`, `A`, `A'`, including `A = A'`, the
diagonal case degenerating to `v A ≤ v A` — sharp, no loss).

**(T2) `RBM.Gauss.Grid.v_gradMat_eq_quadVar`.** Verdict: **PASS** (as an equality).
Hypotheses: `Φ` in T1505's `TestFun d N Φ` class, `hReal : ∀ A, A.IsHermitian → (Φ A).im = 0`
(T1505's real-on-Hermitian-submanifold hypothesis, already shown satisfiable there for
`(L−K)_{u,(+,-),a}`-type combinations), `M` Hermitian. Route as in the ticket: reindex
`coordFinset N` as the image of `crd d N` over the full raw index set (`Finset.sum_map` on
`coordFinset`'s definition as `Finset.univ.map (Function.Embedding.sigmaMk N)`); the terms
outside `usedCoord d N` vanish (Step-0 fact above); on `usedCoord d N`,
`Xmat d N (Pi.single (crd p) 1) = Bmat d N p.1 p.2.1 p.2.2` (again `Xmat_eq_sum`, picking out
the single term `p`); `lin N (gradMat Φ M) (Bmat p) = (coordD1 d N Φ M p).re` is T1505's
`lin_eq_fderiv` applied at the Hermitian direction `Bmat p` (`Bmat_isHermitian`, needs `p ∈
usedCoord d N`, which holds), since `coordD1 Φ M p` is definitionally `fderiv ℝ Φ M (Bmat p)`;
`coordD1 Φ M p` is real (`im = 0`) by T1505's `fderiv_im_eq_zero_of_herm` using `hReal` and `hM`,
so `‖coordD1 Φ M p‖² = (coordD1 Φ M p).re²` exactly. No quantifier-order issue (`Φ`, `M` are
fixed, matching the paper's per-label, per-time-sample use); no vacuity (`hReal`/`TestFun` are
exactly T1505's hypotheses, already shown jointly satisfiable there).

**(T3) `RBM.Gauss.Grid.v_Ab_le` — REVISED preflight (repair of audit RETURN, 2026-09-26T01:23Z).**
Verdict: **PASS**.

Audit defect addressed (`docs/reports/T1512-audit.md`, (T3) RETURN): the branch stated (T3) only
at the special point `M = H_j ω` in `Ab`-form and lacked the `Δ`-multiplied corollary. Revised
statements:

1. `v_Ab_le` (the ticket's name, now the general target): for an **arbitrary** matrix
   `M` with `hM : M.IsHermitian`, and `hqv : ∀ a, quadVar d N (Φ a) M ≤ Q·tailT(u)(dist a)²`
   at that `M`,
   `v N (Σ_a ((∏_i edgeKer (L N) 1 u v (b i) (a i)).re : ℂ) • gradMat (Φ a) M)
      ≤ (√Q · ((1-u)/(1-v))² · xiK (L N) W m · tailT(v)(dist b))²`.
   Statement vs ticket: `K(b,a) = ∏_i edgeKer(b i)(a i)` is the kernel of
   `Uker (L N) (fun _ => 1) u v` (T1509 orientation, same as T1505's `Ab` with `U b a`); the ticket
   writes `(K(b,a) : ℂ)`, which equals `((K(b,a)).re : ℂ)` since `K` is real (`Uker_one_nonneg`,
   T1509 (T1)) — the `.re` form is the one that type-checks against T1505's real-kernel `Ab`
   (`U : LoopArg → LoopArg → ℝ`), so the conclusion is literally the ticket's quantity. Hypotheses:
   exactly `qv_conv_le`'s (`hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv`), T1505's `hΦ`/`hReal`, `hM`,
   `hqv` — no new hypothesis. Right-hand side is syntactically `qv_conv_le`'s: no extra loss.
   Quantifier order: all parameters fixed; deterministic in `M`. The previous proof used
   `H_isHermitian` only to obtain `hM`, so it transports verbatim with `M` generalized.
2. `v_Ab_le_H`: the `Ab`-form at `M = H d s t K N j ω` — `Ab … U b ω` with
   `U b' a' := (∏ edgeKer (b' i) (a' i)).re` is definitionally
   `Σ_a (U b a : ℂ) • gradMat (Φ a) (H_j ω)` (T1505 `Ab` definition), and `H_isHermitian` gives
   `hM`. A corollary of 1, not a replacement.
3. `step_mul_v_Ab_le`: in exactly the shape of T1505 `stepDecomp_Z_subG`'s
   `hbound : ∀ ω ∈ E, step s t K N * v N (Ab d s t K N j Φ U b ω) ≤ c`, with
   `c := step s t K N * (√Q·((1-u)/(1-v))²·xiK·tailT(v)(dist b))²`, from
   `hqvE : ∀ ω ∈ E, ∀ a, quadVar d N (Φ a) (H_j ω) ≤ Q·tailT(u)(dist a)²`.
   Boundary case: `step s t K N = (t N - s N)/K N` can be negative (if `t N < s N`), in which case
   multiplying reverses the inequality; so this corollary carries the explicit hypothesis
   `hstep : 0 ≤ step s t K N` (as the audit prescribes). This is not a weakening of the ticket:
   the ticket's `Δ` is a nonnegative time step, and `hbound` also needs `0 ≤ c`, which likewise
   requires `0 ≤ step`; a companion `step_mul_bound_nonneg` supplies that `hc`. Satisfiability of
   `hstep`: any `s N ≤ t N` (e.g. `s = 0`, `t = 1`, any `K`) — `0 ≤ (t N - s N)/K N` holds also
   for `K N = 0` (division by zero is `0`), and nondegenerately for `K N > 0`.
   Satisfiability of `hqvE` with `Q > 0` and non-constant `Φ`: the audit's compiled witness
   (`hqv_sat`, `Φ0 = |tr (herm M - i)⁻¹|²`) gives, for each fixed `ω`, such a `Q`; on an event `E`
   one needs a uniform `Q`, which is exactly what T1497 supplies on the stopped event; for a
   compiled nondegenerate check at the general-`M` level I reuse the audit's witness construction
   (any finite family of sample points / `E` a singleton gives a uniform finite `Q`).

Dependencies: T1505 (merged: `Ab`, `gradMat`, `TestFun`, `lin_eq_fderiv`,
`fderiv_im_eq_zero_of_herm`, `stepDecomp_Z_subG` shape), T1509 (merged: `qv_conv_le`,
`Uker_one_nonneg`), `GridPath` (`step`, `H`, `H_isHermitian`). No cycle.

<details><summary>Original (T3) preflight of the first prover (superseded; kept for the record)</summary>

**(T3) `RBM.Gauss.Grid.v_Ab_le`.** Verdict: **PASS**.
Packaged as the `Ab`-form corollary the ticket asks for directly (T1505 (T4)'s `hbound` consumes
`Δ · v N (Ab ω) ≤ Δ · (bound)²`, so stating `v_Ab_le` already in `Ab`-form saves a wrapping step;
downstream tickets multiply by `Δ = step s t K N ≥ 0` themselves). Hypotheses: exactly T1509
`qv_conv_le`'s hypotheses (`hL, hm0, hm1, hu0, huv, hv0, hv1, hW, hQ, hAuv`, all jointly
satisfiable as already established for T1509 — e.g. `m = 1`, `u = 0`, `v ∈ (0,1)`, `W = e`,
`Q > 0` is a nondegenerate witness with `Φ` non-constant, since `TestFun`/`hReal` place no
constraint tying `Q` to a specific value: any `Q > 0` bounding the specific `Φ_a`'s in use
works), plus the pointwise `hqv : quadVar d N (Φ a) (H d s t K N j ω) ≤ Q·tailT(...)²` for every
label `a`, at the *specific* sample point `H_j ω` — matching what T1497 supplies on the stopped
event (Step-0 above). Route: `v_sum_eq` (T1) turns `v N (Ab ...)` into the `vB`-quadratic form in
the real kernel entries `r(a) := (∏ᵢ edgeKer L 1 u v (b i) (a i)).re`; `Uker_one_nonneg`
(T1509 (T1)) shows each kernel entry equals `(r(a):ℂ)` on the nose (real, and in fact ≥ 0,
though nonnegativity is not needed here); `qv_conv_le` is then fed `EE a a' := (vB N (gradMat Φ_a
M)(gradMat Φ_a' M):ℂ)`, `R a := quadVar d N (Φ a) M`, whose Cauchy–Schwarz hypothesis is exactly
(T1)'s `abs_vB_le` combined with (T2)'s `v_gradMat_eq_quadVar`; the two real double sums are
identified by casting to `ℂ` and matching term-by-term (`conj` of a real kernel entry is itself),
then reading off the norm of a nonnegative real. **No loss factor beyond `qv_conv_le`'s own**
(`√Q · ((1-u)/(1-v))² · xiK · tailT(v)(dist b)`, squared) is introduced by this packaging step —
matches the auditor's stated check. Witness for joint satisfiability with `Q > 0` and non-constant
`Φ`: any instantiation already used to discharge T1509's own witness (e.g. `Φ_a` a bounded
non-constant `C²` function of the matrix entries, `Q` any upper bound on its `quadVar` at the
finitely many sample points in play) transports unchanged, since (T3) adds no new hypothesis on
`Φ` beyond T1505's `TestFun`/`hReal` (already witnessed) and T1509's own (already witnessed).


</details>

**Overall verdict: PASS for (T1), (T2), (T3).** No claim needed weakening; no hypothesis added
beyond what T1505/T1509 already carry (the only new hypothesis, `0 ≤ step s t K N`, sits on the
`Δ`-corollary, where it is necessary and nondegenerately satisfiable; see revised (T3)).

## (b) Declarations, files, build, axioms

File (sole writable): `RBM1D/Gauss/GridQVForm.lean`, branch `t/T1512`. Repair commit `487798e`
(on top of the original prover's `e74c9da`).

Declarations (namespace `RBM.Gauss.Grid`):
* `vB` (def), `vB_self`, `vB_nonneg_diag` — unchanged (T1, audit PASS)
* `v_sum_eq`, `abs_vB_le` — unchanged (T1, audit PASS)
* `v_gradMat_eq_quadVar` — unchanged (T2, audit PASS; proved as an equality)
* `v_Ab_le` (**T3, revised**) — general Hermitian `M`:
  ```
  theorem v_Ab_le {Φ} (hΦ) (hReal) (hL) {m} (hm0) (hm1) {u vt} (hu0) (huv) (hv0) (hv1)
      {W D Q} (hW) (hQ) (hAuv) (b : LoopArg (d.L N) 2) {M} (hM : M.IsHermitian)
      (hqv : ∀ a, quadVar d N (Φ a) M ≤ Q * (tailT W (ellHat (d.L N) u) ((1-u)*m) D (zdist (d.L N) (a 0 - a 1)))^2) :
      v N (∑ a, ((∏ i : Fin 2, edgeKer (d.L N) 1 u vt (b i) (a i)).re : ℂ) • gradMat (Φ a) M)
        ≤ (√Q * ((1-u)/(1-vt))^2 * Step2.xiK (d.L N) W m * tailT W (ellHat (d.L N) vt) ((1-vt)*m) D (zdist (d.L N) (b 0 - b 1)))^2
  ```
* `v_Ab_le_H` (**T3, corollary**) — the former `Ab`-form statement at `M = H d s t K N j ω`
  (same hypotheses and conclusion as the pre-repair `v_Ab_le`), one line from `v_Ab_le` +
  `H_isHermitian` (the `Ab`/sum identification is definitional).
* `step_mul_v_Ab_le` (**T3, `Δ`-corollary**) — under `hstep : 0 ≤ step s t K N` and
  `hqvE : ∀ ω ∈ E, ∀ a, quadVar d N (Φ a) (H d s t K N j ω) ≤ Q·tailT(u)(dist a)²`, concludes
  `∀ ω ∈ E, step s t K N * v N (Ab d s t K N j Φ U b ω) ≤ step s t K N * (…)²`
  (`U b' a' := (∏ edgeKer (b' i) (a' i)).re`) — literally the `hbound` binder of T1505's
  `stepDecomp_Z_subG` with `c := step s t K N * (…)²`.
* `step_mul_bound_nonneg` — the companion `hc : 0 ≤ step s t K N * B²` from `hstep`.

Naming: the ticket's name `v_Ab_le` now carries the ticket's general-`M` target, so no rename
needs dispatcher acceptance; the extra names `v_Ab_le_H`, `step_mul_v_Ab_le`,
`step_mul_bound_nonneg` are the ticket's requested corollaries. No `paper-deltas` entry needed.

Build (repairer's worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1512`):
```
lake build RBM1D.Gauss.GridQVForm
```
Result: `Build completed successfully (3767 jobs).` Only warnings: three pre-existing cosmetic
`if_neg`/`if_pos` deprecation notices in (T2)'s proof (now at lines 257, 276, 279).

Compiled feed check (scratch file, not a source file; `lake env lean`, 0 errors): with
arbitrary `d s t K N j Φ E` and `hE : MeasurableSet[filt d j] E`,
`stepDecomp_Z_subG d s t K N j hΦ _ b E hE _ (step_mul_bound_nonneg hstep _)
 (step_mul_v_Ab_le hΦ hReal hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv hstep b E hqvE)` type-checks,
i.e. the corollary feeds T1505 (T4) directly. Also compiled: `0 < step (fun _ => 0) (fun _ => 1)
(fun _ => 1) 5` (nondegenerate witness for `hstep`). The joint satisfiability of the remaining
hypotheses with `Q > 0` and non-constant `Φ` is the auditor's compiled witness
(`Φ0 = |tr (herm M - i)⁻¹|²`, `m = 1`, `u = 0`, `vt = 1/2`, `W = e`, `D = 1`), which applies
unchanged since `v_Ab_le_H` has exactly the pre-repair `v_Ab_le` signature and is derived from the
general theorem.

Axioms (`#print axioms`):
```
'RBM.Gauss.Grid.v_Ab_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.v_Ab_le_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.step_mul_v_Ab_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.step_mul_bound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.vB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.vB_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.v_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.abs_vB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Grid.v_gradMat_eq_quadVar' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/declared `axiom` (grep clean).

## (c) Key lemmas used

* T1505 (`Gauss/GridStepDecomp.lean`, merged): `gradMat`, `Ab`, `TestFun`, `lin_eq_fderiv`,
  `fderiv_im_eq_zero_of_herm`; `stepDecomp_Z_subG` (shape of `hbound`/`hc`, feed check only).
* T1509 (`Gauss/GridQVConv.lean`, merged): `qv_conv_le`, `Uker_one_nonneg`.
* `Gauss/GridMarkov.lean`: `v`, `lin`, `coordFinset`, `v_nonneg`.
* `Gauss/Generator.lean`: `Xmat_eq_sum`, `crd`, `crd_injective`, `usedCoord`, `Bmat`,
  `Bmat_isHermitian`, `coordD1`.
* `Gauss/MomentGronwall.lean`: `quadVar`, `quadVar_nonneg`.
* `Gauss/GridPath.lean`: `step`, `H`, `H_isHermitian`.
* Mathlib: `Finset.sum_mul_sq_le_sq_mul_sq`, `Finset.sum_map`, `Finset.sum_comm`,
  `mul_le_mul_of_nonneg_left`, `Complex.norm_of_nonneg`/`norm_real`.

## (d) Open issues

* None for this ticket's targets. Downstream: T1504 (T1′) uses `step_mul_v_Ab_le` with
  `c_j^{(k,b)} := Δ·(√Q·((1-u)/(1-v))²·xiK·tailT_v(dist b))²` on the stopped event (it must supply
  `0 ≤ step`, i.e. `s N ≤ t N`, and a `Q` uniform on the event, from T1497/T1501/T1502); T1508
  sums `c_j` over `j`.
* Cosmetic: the three `if_neg`/`if_pos` deprecation warnings in (T2)'s proof are left as-is
  ((T2) PASSed and was to be kept exactly).
