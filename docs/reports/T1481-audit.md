# T1481 (amend-1) — audit report

Auditor worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1481-audit` (detached at `t/T1481` = `5f656ab`,
since `t/T1481` is checked out in the prover worktree). Branch base `ab96505`; diff vs base = one new
file `RBM1D/Gauss/GridPath.lean` (492 lines). No other file touched; `RBM1D.lean`, `Gauss/Model.lean`
unchanged; `GridPath.lean` does not exist on `main`, so no conflict.

## Overall verdict: PASS (all targets T1–T6)

## 1. Math preflight
`docs/reports/T1481-prove.md` §(a) contains Step 0 (a)(b)(c) and a per-target preflight PASS for
T1–T6, stated before the Lean section (§(b)). OK.

## 2. Statement vs ticket / design (`pilot-P4P5-paper.md` §2)
- T1: `Ωg d := ℕ → Ω d`, `Pg d := Measure.infinitePi (fun _ : ℕ => P d)` (the actual `Gauss.P d`),
  instance `isProbabilityMeasure_Pg`. Matches.
- T2: `step = (t N - s N)/K N`, `time = s N + k*step`; `time_zero`, `time_last (hK : K N ≠ 0)`. Matches.
- T3: `H d s t K N k ω = (√(s N):ℂ) • Xmat d N (ω 0) + (√step:ℂ) • ∑ i ∈ Icc 1 k, Xmat d N (ω i)`,
  verbatim; `H_isHermitian`, `measurable_H` entrywise. Matches. Increment `H_{k+1}-H_k = √Δ·X_{k+1}`,
  covariance `Δ·S`, as in design §2.
- T4: `map_H_eq : 0 ≤ s N → s N ≤ t N → K N ≠ 0 → (Pg d).map (H d s t K N k) = (P d).map (Hflow d N (time s t K N k))`
  for every `k : ℕ` (no `k ≤ K N`), stated for the concrete `Gauss.P d` / `Gauss.Hflow` on the matrix
  space (Borel via `Mathlib.Analysis.Matrix.MeasurableSpace`), not an abstract measure. Matches.
  Cosmetic: `d` is implicit in `map_H_eq` (section `variable {d}`) while explicit in the other
  declarations; the ticket fixes no binder style. Not a defect.
- T5: `filt d := Filtration.piLE`; checked by `rfl` that `filt d k = comap (Preorder.restrictLe k) pi`,
  i.e. the coordinate filtration on `ω 0..ω k`, not `⊤`. `H_adapted` is `StronglyMeasurable[filt d k]`
  of each entry (checked with explicit `@StronglyMeasurable _ _ _ (filt d k)`), for all `N k i j`.
  This is the natural reading of the ticket's phrasing; accepted.
- T6: `indep_incr k : Indep (comap (· (k+1))) (filt d k) (Pg d)`, `map_incr k : (Pg d).map (· (k+1)) = P d`.
  Verbatim. `filt d k = σ(ω_0..ω_k)` contains design's `F_k = σ(H_{u_0..u_k})`, so this is at least
  as strong as needed.

## 3. Vacuity / hidden hypotheses / cycles
- No structure fields, no extra hypotheses beyond the ticket's. `hK` in `map_H_eq` is unused by the
  proof (linter hint) but required by the ticket signature; harmless (only weakens nothing).
- Witness compiled (throwaway file, not in the repo): `s ≡ 0, t ≡ 1/2, K ≡ 1`, arbitrary `d, N, k`:
  `map_H_eq (d := d) _ _ _ N k le_rfl (by norm_num) one_ne_zero` type-checks; `time … 5 1 = 1/2`
  via `time_last`. Nondegenerate: positive variance increment, window `[0,1/2]` not collapsed, no
  `N = 0` or empty-index dependence (`s,t,K` are free functions of `N`).
- T1/T3/T5/T6 are hypothesis-free.
- No circularity: file imports only `RBM1D.Gauss.Model` plus Mathlib.

## 4. Dependencies
`RBM.Gauss.{P, Xmat, Xentry, Hflow, gvar, Dims, Coord, Ω, Xmat_isHermitian, measurable_Xentry,
Hflow_apply, Xmat_apply}` — all in committed `Gauss/Model.lean`. Remaining inputs are Mathlib
(`infinitePi_map_curry(_symm)`, `infinitePi_map_piCongrLeft`, `infinitePi_map_pi`,
`iIndepFun_infinitePi`, `gaussianReal_add_gaussianReal_of_indepFun`, `gaussianReal_map_const_mul`,
`indep_biSup_compl`). No use of the reserved [51, Thm 2.2] input.

## 5. Build / axioms
- `lake build RBM1D.Gauss.GridPath`: Build completed successfully (3701 jobs), no errors.
- `lake build RBM1D` (branch root; no root import required by the ticket): Build completed
  successfully (9324 jobs).
- `#print axioms` for `map_H_eq, indep_incr, map_incr, H_adapted, measurable_H, H_isHermitian,
  time_last, time_zero, isProbabilityMeasure_Pg`: each `[propext, Classical.choice, Quot.sound]`.
- `grep` for `sorry|admit|axiom` in `GridPath.lean`: none. No frozen signature touched.

## Paper deltas
The grid model itself replaces the Brownian flow (2.34) by design (dispatcher's pilot route); this
ticket introduces no further Lean/paper difference beyond that design. No new delta entry needed from
this file.

## Per-target verdicts
T1 PASS · T2 PASS · T3 PASS · T4 PASS · T5 PASS · T6 PASS
