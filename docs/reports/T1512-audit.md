Auditor model: claude-opus-5-5[1m]

# T1512 — audit (independent, final; re-audit after repair)

Date (UTC): 2026-09-26T01:29Z. Branch `t/T1512` at `487798e`
(repair commit on top of `e74c9da`), checked out detached in a **fresh** worktree
`/Users/junyin/Lean_proof/RBM1D-wt/T1512-audit2` (not the repairer's `RBM1D-wt/T1512`, not the
first audit's `RBM1D-wt/T1512-audit`). Build cache cloned from main with `cp -c -R`; all
`GridQVForm*` artifacts deleted before building, so the module was compiled from scratch.

Diff vs branch base `6415b0f` (= merge-base with `main`): exactly one file,
`RBM1D/Gauss/GridQVForm.lean` (new, +437). (`git diff main t/T1512` also shows
`GridQVSum.lean` deleted only because `main` has since merged T1508; the branch does not touch
it.) Root `RBM1D.lean` untouched; no frozen signature changed. No name clash with current `main`
(`git grep` of all ten new declaration names in `main:RBM1D` — none found).

## Overall verdict: PASS

(T1) PASS, (T2) PASS, (T3) PASS.

## Gate 1 — math preflight

`docs/reports/T1512-prove.md` §(a) has the Step-0 checks and a per-target preflight PASS,
followed by a revised (T3) preflight (timestamped 2026-09-26T01:23Z, the repair) placed before
§(b) Lean; the original (T3) preflight is kept under `<details>`. Present.

## (T1) `vB`, `vB_self`, `v_sum_eq`, `abs_vB_le` — PASS (no regression)

`git diff e74c9da 487798e` has two hunks only: the module docstring header (lines 23–33) and
the (T3) section (from the `/-! ### (T3)` heading on). Every line of (T1) and (T2) is
byte-for-byte identical to the version PASSed in the first audit. `vB` is literally the
covariance of the Gaussian linear forms (same index set `coordFinset N`, same weights `gvar`
as `v`); `vB_self` re-proved as a one-liner in scratch (first audit). Axioms standard.

## (T2) `v_gradMat_eq_quadVar` — PASS (equality; reported honestly; no regression)

Unchanged (see above). Equality holds because the extra raw coordinates in `coordFinset` have
`Xmat d N (Pi.single c 1) = 0`; the report says so.

## (T3) `v_Ab_le`, `v_Ab_le_H`, `step_mul_v_Ab_le`, `step_mul_bound_nonneg` — PASS

**`v_Ab_le` is genuinely general.** `#check @v_Ab_le` (auditor): binders are `d N Φ hΦ hReal hL
m hm0 hm1 u vt hu0 huv hv0 hv1 W D Q hW hQ hAuv b {M} (hM : M.IsHermitian) (hqv : ∀ a,
quadVar d N (Φ a) M ≤ Q * tailT W (ellHat u) ((1-u) m) D (zdist (a 0 - a 1))^2)`; conclusion
`v N (∑ a, ((∏ i, edgeKer (d.L N) 1 u vt (b i) (a i)).re : ℂ) • gradMat (Φ a) M) ≤ (√Q ·
((1-u)/(1-vt))² · xiK (d.L N) W m · tailT W (ellHat vt) ((1-vt) m) D (zdist (b 0 - b 1)))²`.
No `s t K j ω`, no `H`, no `Ab` anywhere in the signature; `M` is an arbitrary matrix subject
only to `hM`. The proof body is the old one with the two lines `set M := H … ω` /
`have hM := H_isHermitian …` removed and `hAb_eq` replaced by the definitional `hsum_eq : … =
∑ a, (r a : ℂ) • A a := rfl`. Compiled general-`M` instance (not a grid sample): see Witness,
`v_Ab_le_general_witness` at `M = x • 1`, `x : ℝ` arbitrary.
Statement vs ticket: the ticket writes `(K(b,a) : ℂ)`; Lean uses `((K(b,a)).re : ℂ)`. These are
equal since the kernel is real (`Uker_one_nonneg`, T1509 (T1), used inside the proof), and the
`.re` form is what matches T1505's real-kernel `Ab` (`U : … → ℝ`). Acceptable, no paper-delta.

**No extra loss.** The right-hand side is syntactically `qv_conv_le`'s (same `√Q`,
`((1-u)/(1-v))²`, `xiK`, `tailT_v(dist b)`, squared); hypotheses are exactly `qv_conv_le`'s plus
T1505's `hΦ`/`hReal`, `hM`, `hqv`. Nothing new beyond the first audit's check.

**`v_Ab_le_H` is a one-line corollary.** Its body is the single term
`v_Ab_le hΦ hReal hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv b (H_isHermitian d s t K N j ω) hqv`
(term-mode, no tactic re-proof). The conclusion's `Ab d s t K N j Φ U b ω` with
`U b' a' := (∏ i, edgeKer … (b' i) (a' i)).re` is definitionally `∑ a, (U b a : ℂ) • gradMat
(Φ a) (H d s t K N j ω)` (T1505 `Ab`, `GridStepDecomp.lean:433–437`), which matches T1505's `Ab`
exactly; it type-checks by defeq.

**`step_mul_v_Ab_le` matches `stepDecomp_Z_subG`'s `hbound` exactly.** T1505 signature
(`RBM1D/Gauss/GridStepDecomp.lean:982–986`, identical on branch base and current `main`):
`(E : Set (Ωg d)) (hE : MeasurableSet[filt d j] E) (c : ℝ) (hc : 0 ≤ c)
(hbound : ∀ ω ∈ E, step s t K N * v N (Ab d s t K N j Φ U b ω) ≤ c)`. The corollary concludes
`∀ ω ∈ E, step s t K N * v N (Ab d s t K N j Φ U b ω) ≤ step s t K N * (…)²` with the same `U`
as `v_Ab_le_H`. Independently re-checked by the auditor (scratch `example`, below): with
arbitrary `d s t K N j Φ b E`, `hE`, all hypotheses, the term
`stepDecomp_Z_subG d s t K N j hΦ _ b E hE _ (step_mul_bound_nonneg hstep _)
 (step_mul_v_Ab_le hΦ hReal hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv hstep b E hqvE)`
elaborates against the fully written-out expected type `HasCondSubgaussianMGF (filt d j)
((filt d).le j) (fun ω => E.indicator (stepZ … U b) ω) ⟨step·(…)², _⟩ (Pg d)`. 0 errors.

**`hstep : 0 ≤ step s t K N` is reasonable.** `step s t K N = (t N - s N)/K N`
(`GridPath.lean:48`) has no built-in sign, so multiplying the inequality by it requires
nonnegativity; the same fact is needed for `hbound`'s companion `hc : 0 ≤ c`. It encodes the
paper's `Δ > 0` (grid on `[s, t]`, `s ≤ t`), does not restrict `M`, `Φ`, labels, windows or
parameters, and sits only on the Δ-corollary (the general `v_Ab_le` has no such hypothesis).
Nondegenerate witness compiled: `0 < step (fun _ => 0) (fun _ => 1) (fun _ => 5) N` (= 1/5).
`step_mul_bound_nonneg` is the trivial `mul_nonneg hstep (sq_nonneg B)`.

**Vacuity / boundary cases.** `hqv` satisfiable with `Q > 0` and non-constant `Φ` (compiled,
both at a grid sample and at a general Hermitian `M`); `u = 0 < vt = 1/2` (non-collapsed
window), `W = e`, `D = 1`, `m = 1`, `N` arbitrary, `L ≥ 3` from `Dims`; `Q` is the explicit
finite ratio `Σ_a quadVar / (W^{-D})² + 1`, not astronomically forced. On `E` downstream a
uniform `Q` is T1497/T1501/T1502's job (T1504), as the ticket states. No structure-field
smuggling, no cycle (imports only `GridStepDecomp` (T1505) and `GridQVConv` (T1509), both merged).

**Naming.** The ticket's (T3) names `RBM.Gauss.Grid.v_Ab_le` as the general-`M` bound and asks
to "also state the corollary in the `Ab` form"; the branch now has exactly that (`v_Ab_le`
general, `v_Ab_le_H` / `step_mul_v_Ab_le` corollaries). The repairer's reading is correct; no
dispatcher sign-off or paper-delta needed.

## Witness and feed check (compiled by the auditor; scratch only, not a source file)

`/Users/junyin/Lean_proof/RBM1D-wt/T1512-audit2/scratch/Witness2.lean`, `lake env lean` in the
audit worktree: 0 errors, no `sorry`.
* `Φ0 d N := |tr (herm M - i)⁻¹|²`: `TestFun`, real on Hermitian, non-constant (`Φ0_nonconst`).
* `v_Ab_le_witness`: `v_Ab_le_H` fully discharged at `H_j ω` with `Q > 0`.
* `v_Ab_le_general_witness`: general `v_Ab_le` fully discharged at `M = (x:ℂ) • 1`, with
  `hM` proved and `Q > 0`.
* feed-check `example` into `stepDecomp_Z_subG` (above); `hstep` witness `example`.
* `#print axioms` for both witnesses, `Φ0_nonconst`, and every branch declaration (`vB`,
  `vB_self`, `v_sum_eq`, `abs_vB_le`, `v_gradMat_eq_quadVar`, `v_Ab_le`, `v_Ab_le_H`,
  `step_mul_v_Ab_le`, `step_mul_bound_nonneg`): `[propext, Classical.choice, Quot.sound]`.

## Builds and axioms

* `lake build RBM1D.Gauss.GridQVForm` (fresh worktree, module compiled from scratch):
  `Build completed successfully (3767 jobs)`. Warnings in the file: only three `if_neg`/`if_pos`
  deprecation notices at lines 257, 276, 279 (cosmetic, in unchanged (T2) proof).
* `lake build RBM1D` (branch root, without the new import, which is added at merge):
  `Build completed successfully (9659 jobs)`, no errors.
* `grep sorry|admit|axiom` in `GridQVForm.lean`: none.

## Minor notes (not blocking)

* `hv0 : 0 ≤ vt` is redundant (from `hu0`, `huv`); mirrors `qv_conv_le`.
* Downstream (T1504) must supply `0 ≤ step` (i.e. `s N ≤ t N`) and a `Q` uniform on the stopped
  event; recorded in the prove report's open issues.
