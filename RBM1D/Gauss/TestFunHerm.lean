/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.LoopIto
import RBM1D.Hierarchy.EGDef

/-!
# Test functions quantified over the Hermitian matrices only (T187)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  `RBM.Gauss.TestFun` (T71) and `RBM.Gauss.TestFunT` (T132b) ask for `C²` and
for bounds on `Φ`, `∂Φ`, `∂²Φ` at **every** matrix.  T180 found that the moment-route test
function `Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}` is not in that class and cannot be:
`(M - z_u)⁻¹` is unbounded off the Hermitian set, and at a singular non-Hermitian `M` the
function is not even continuous (Lean's `Ring.inverse` is `0` there).  On the Hermitian set
both conditions hold, and the whole argument lives there: the flow `H_u = √u X` is Hermitian
(`RBM.Gauss.Hflow_isHermitian`) and so are the coordinate directions `Bmat` on used
coordinates (`RBM.Gauss.Bmat_isHermitian`).

This file adds the primed classes and carries the generator identity through them.  It is the
same repair T145 made to `RBM.MomentDuhamel.Hyp.drift`, and the fifth instance of the pattern
(T145, T132b, T154, T164/T172, T180).

## Main definitions

* `RBM.Gauss.TestFun'`, `RBM.Gauss.TestFunT'` — `RBM.Gauss.TestFun` and
  `RBM.Gauss.TestFunT` with `∀ M` weakened to `∀ M, M.IsHermitian →` in every field,
  `ContDiff` weakened to `ContDiffAt` at Hermitian points.
* `RBM.Gauss.hermFun`, `RBM.Gauss.hermFunT` — `Φ ∘ hermCLM` and `(u, M) ↦ Ψ u (hermCLM M)`,
  the Hermitian *regularisation* of a test function.

## Main results

* `RBM.Gauss.fderiv_comp_clm_apply`, `RBM.Gauss.fderiv2_comp_clm_apply` — the calculus that
  makes the relaxation work: for a continuous linear `P`, the first and second derivatives of
  `f ∘ P` at `M` are those of `f` at `P M`, read on the directions `P B`.  With `P = hermCLM`,
  `M` Hermitian and `B` Hermitian this says the regularisation changes **nothing**: the
  sentence in `RBM1D/Gauss/Generator.lean`'s "The Hermitian projection" section, which was
  prose there, is `RBM.Gauss.coordD1_hermFun` / `RBM.Gauss.coordD2_hermFun` here.
* `RBM.Gauss.TestFun'.herm`, `RBM.Gauss.TestFunT'.herm` — **the bridge**: a primed test
  function has an unprimed regularisation, with the same constants.  This is what lets the
  primed generator identity be *deduced* from the unprimed one instead of reproving the
  dominated-convergence argument on the flow.
* `RBM.Gauss.hasDerivAt_integral_Phi'`, `RBM.Gauss.hasDerivAt_integral_Phi_pairs'`,
  `RBM.Gauss.hasDerivAt_integral_Psi'`, `RBM.Gauss.hasDerivAt_integral_Psi_pairs'` — the
  generator identities of T71 and T132b, for the primed classes, **with the conclusion
  unchanged** (it is about `Φ` and `Ψ` themselves, not about their regularisations).
* `RBM.Gauss.hasDerivAt_integral_Phi_pairs_of_herm`,
  `RBM.Gauss.hasDerivAt_integral_Psi_pairs_of_herm` (and their coordinate forms) — the same
  identities under the two hypotheses the proof actually uses: regularity at Hermitian
  matrices, and bounds *for the regularisation*.  These are strictly weaker than the primed
  classes — a bound on `∂(Φ ∘ hermCLM)` does not bound `∂Φ` in the anti-Hermitian directions —
  and they are the form the moment route can discharge today; see the `Satisfiability`
  section.
* `RBM.Gauss.genMomentPt_le'` — T72's pointwise bound on `𝓛(|F|^{2p})` with its global
  `ContDiff ℝ 2` weakened to `ContDiffAt` at Hermitian points, asserted at Hermitian `M`.
  (This is the second seam T180 flagged.)
* `RBM.Gauss.TestFun.toTestFun'`, `RBM.Gauss.TestFunT.toTestFunT'` — the old classes are
  contained in the new ones, so every existing supply still applies.  **The old classes are
  not changed.**

## What is *not* claimed

Nothing here says that the raw `Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}`, with
`RBM.MomentDuhamel.lkFun`'s unregularised `gloop`, is in `TestFunT'`; that needs bounds on the
derivatives of `gloop` *at* Hermitian points, i.e. a pointwise version of the `BddC2C` chain of
`RBM1D/Gauss/LoopC2.lean`.  What is shown instead is that the regularised
`RBM.Gauss.loopObs`/`RBM.Gauss.ukerObs` of T74/T133 — which agree with the raw ones at every
Hermitian matrix, in particular along the whole flow — are in the primed class, so the
relaxation is inhabited by the functions the moment route evaluates.  See
`RBM.Gauss.hasDerivAt_integral_momentFun_ukerRaw`, which is the generator identity for the
**raw** observable of `RBM.MomentDuhamel.Hyp.momentDuhamel` at a fixed spectral parameter, and
the rest of the `Satisfiability` section.

## Overlap with `RBM1D/Hierarchy/EGDef.lean`

T58 proved `RBM.EGDef.fderiv2_comp_clm` — the diagonal case `B = B'` of
`RBM.Gauss.fderiv2_comp_clm_apply` at a *fixed point* `T M = M` — and, from it,
`RBM.EGDef.coordD2_gloop_eq` and `wirtSecond_gloop_eq`, which are
`RBM.Gauss.coordD2_hermFun` / `wirtSecond_hermFun` for the loop observable.  The versions here
are the general ones (`P M` arbitrary, two directions, and the operator-norm bound
`RBM.Gauss.norm_fderiv2_comp_clm_le`, which the class transfer needs and the diagonal case
cannot give); nothing in `Hierarchy/` is changed or duplicated downwards.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator NNReal

/-! ### Derivatives through a continuous linear map -/

section Proj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `RBM.Gauss.hasFDerivAt_fderiv_apply` with the `RBM.Gauss.TestFun` hypothesis weakened to
what the proof uses: differentiability of `fderiv ℝ f` at the one point `M`. -/
theorem hasFDerivAt_fderiv_apply' {f : E → ℂ} {M : E}
    (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The first derivative through a continuous linear map.**  `∂(f ∘ P)(M)[B] = ∂f(PM)[PB]`. -/
theorem fderiv_comp_clm_apply (P : E →L[ℝ] E) {f : E → ℂ} {M : E}
    (hf : DifferentiableAt ℝ f (P M)) (B : E) :
    fderiv ℝ (fun M' => f (P M')) M B = fderiv ℝ f (P M) (P B) := by
  have h : HasFDerivAt (fun M' => f (P M')) ((fderiv ℝ f (P M)).comp P) M :=
    (hf.hasFDerivAt).comp M P.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- **The second derivative through a continuous linear map.**
`∂²(f ∘ P)(M)[B, B'] = ∂²f(PM)[PB, PB']`.  Together with `hermCLM_of_isHermitian` and
`Bmat_isHermitian` this is the exact content of the claim in `RBM1D/Gauss/Generator.lean` that
pre-composing with the Hermitian projection "changes neither the value nor any directional
derivative along a Hermitian direction at a Hermitian point". -/
theorem fderiv2_comp_clm_apply (P : E →L[ℝ] E) {f : E → ℂ} {M : E}
    (hf : ContDiffAt ℝ 2 f (P M)) (B B' : E) :
    fderiv ℝ (fderiv ℝ fun M' => f (P M')) M B B'
      = fderiv ℝ (fderiv ℝ f) (P M) (P B) (P B') := by
  have hev : ∀ᶠ M' in nhds M, DifferentiableAt ℝ f (P M') := by
    have h1 : ∀ᶠ y in nhds (P M), ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    exact (P.continuous.tendsto M).eventually
      (h1.mono fun y hy => hy.differentiableAt (by norm_num))
  have heq : (fun M' => fderiv ℝ (fun M'' => f (P M'')) M' B')
      =ᶠ[nhds M] fun M' => fderiv ℝ f (P M') (P B') :=
    hev.mono fun M' h => fderiv_comp_clm_apply P h B'
  have hcP : ContDiffAt ℝ 2 (fun M' => f (P M')) M := hf.comp M P.contDiff.contDiffAt
  have hd1 : DifferentiableAt ℝ (fderiv ℝ fun M' => f (P M')) M :=
    (hcP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f) (P M) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hL : HasFDerivAt (fun M' => fderiv ℝ (fun M'' => f (P M'')) M' B')
      ((fderiv ℝ (fderiv ℝ fun M'' => f (P M'')) M).flip B') M :=
    hasFDerivAt_fderiv_apply' hd1 B'
  have hR : HasFDerivAt (fun M' => fderiv ℝ f (P M') (P B'))
      (((fderiv ℝ (fderiv ℝ f) (P M)).flip (P B')).comp P) M :=
    (hasFDerivAt_fderiv_apply' hd2 (P B')).comp M P.hasFDerivAt
  have huniq := (hL.congr_of_eventuallyEq heq.symm).unique hR
  have happ := congrArg (fun T : E →L[ℝ] ℂ => T B) huniq
  simpa using happ

/-- The operator norm of the second derivative of `f ∘ P`, from that of `f` at `P M`. -/
theorem norm_fderiv2_comp_clm_le (P : E →L[ℝ] E) {f : E → ℂ} {M : E}
    (hf : ContDiffAt ℝ 2 f (P M)) {C : ℝ} (hC : ‖fderiv ℝ (fderiv ℝ f) (P M)‖ ≤ C)
    (hP : ‖P‖ ≤ 1) : ‖fderiv ℝ (fderiv ℝ fun M' => f (P M')) M‖ ≤ C := by
  have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (fderiv ℝ (fderiv ℝ f) (P M))).trans hC
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun B => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun B' => ?_
  rw [fderiv2_comp_clm_apply P hf B B']
  have h1 : ‖fderiv ℝ (fderiv ℝ f) (P M) (P B) (P B')‖
      ≤ ‖fderiv ℝ (fderiv ℝ f) (P M)‖ * ‖P B‖ * ‖P B'‖ :=
    (fderiv ℝ (fderiv ℝ f) (P M)).le_opNorm₂ _ _
  have hPB : ‖P B‖ ≤ ‖B‖ := le_trans (P.le_opNorm B)
    (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg B))
  have hPB' : ‖P B'‖ ≤ ‖B'‖ := le_trans (P.le_opNorm B')
    (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg B'))
  refine h1.trans ?_
  have := mul_le_mul (mul_le_mul hC hPB (norm_nonneg _) hC0) hPB' (norm_nonneg _)
    (by positivity)
  simpa [mul_assoc] using this

/-- The operator norm of the first derivative of `f ∘ P`, from that of `f` at `P M`. -/
theorem norm_fderiv_comp_clm_le (P : E →L[ℝ] E) {f : E → ℂ} {M : E}
    (hf : DifferentiableAt ℝ f (P M)) {C : ℝ} (hC : ‖fderiv ℝ f (P M)‖ ≤ C) (hP : ‖P‖ ≤ 1) :
    ‖fderiv ℝ (fun M' => f (P M'))  M‖ ≤ C := by
  have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (fderiv ℝ f (P M))).trans hC
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun B => ?_
  rw [fderiv_comp_clm_apply P hf B]
  have hPB : ‖P B‖ ≤ ‖B‖ := le_trans (P.le_opNorm B)
    (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg B))
  exact le_trans ((fderiv ℝ f (P M)).le_opNorm _)
    (mul_le_mul hC hPB (norm_nonneg _) hC0)

end Proj

/-! ### The Hermitian regularisation -/

section Herm

variable {d : Dims} {N : ℕ}

/-- The operator norm of the Hermitian projection is at most one. -/
theorem norm_hermCLM_opNorm_le (n : Type*) [Fintype n] [DecidableEq n] :
    ‖hermCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => by
    simpa using norm_hermCLM_le A

/-- **The Hermitian regularisation of a test function**: `Φ ∘ hermCLM`.  It agrees with `Φ` at
every Hermitian matrix, and it is defined — and as regular as `Φ` is on the Hermitian set —
everywhere. -/
noncomputable def hermFun (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :
    Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  fun M => Φ (hermCLM (d.Idx N) M)

/-- The regularisation of a time-dependent test function, in the time-frozen slot. -/
noncomputable def hermFunT (d : Dims) (N : ℕ) (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  fun u M => Ψ u (hermCLM (d.Idx N) M)

@[simp] theorem hermFun_of_isHermitian {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) : hermFun d N Φ M = Φ M := by
  rw [hermFun, hermCLM_of_isHermitian hM]

@[simp] theorem hermFunT_of_isHermitian {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (u : ℝ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) : hermFunT d N Ψ u M = Ψ u M := by
  rw [hermFunT, hermCLM_of_isHermitian hM]

theorem hermFunT_slice (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) :
    hermFunT d N Ψ u = hermFun d N (Ψ u) := rfl

/-- The time derivative of the regularisation is that of `Ψ` at the projected matrix. -/
theorem timeD1_hermFunT_apply (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    timeD1 (hermFunT d N Ψ) u M = timeD1 Ψ u (hermCLM (d.Idx N) M) := rfl

/-- The regularisation has the same time derivative at Hermitian matrices. -/
theorem timeD1_hermFunT (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    timeD1 (hermFunT d N Ψ) u M = timeD1 Ψ u M := by
  rw [timeD1, timeD1]
  congr 1
  funext s
  exact hermFunT_of_isHermitian s hM

/-- **The regularisation has the same first derivative** at a Hermitian matrix, along a
Hermitian direction. -/
theorem fderiv_hermFun_apply {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M)
    {B : Matrix (d.Idx N) (d.Idx N) ℂ} (hB : B.IsHermitian) :
    fderiv ℝ (hermFun d N Φ) M B = fderiv ℝ Φ M B := by
  have hPM : hermCLM (d.Idx N) M = M := hermCLM_of_isHermitian hM
  change fderiv ℝ (fun M' => Φ (hermCLM (d.Idx N) M')) M B = fderiv ℝ Φ M B
  rw [fderiv_comp_clm_apply (hermCLM (d.Idx N)) (by rw [hPM]; exact hΦ), hPM,
    hermCLM_of_isHermitian hB]

/-- **The regularisation has the same second derivative** at a Hermitian matrix, along
Hermitian directions.  This is the prose claim of `RBM1D/Gauss/Generator.lean`'s "The Hermitian
projection" section, proved. -/
theorem fderiv2_hermFun_apply {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (hΦ : ContDiffAt ℝ 2 Φ M)
    {B B' : Matrix (d.Idx N) (d.Idx N) ℂ} (hB : B.IsHermitian) (hB' : B'.IsHermitian) :
    fderiv ℝ (fderiv ℝ (hermFun d N Φ)) M B B' = fderiv ℝ (fderiv ℝ Φ) M B B' := by
  have hPM : hermCLM (d.Idx N) M = M := hermCLM_of_isHermitian hM
  change fderiv ℝ (fderiv ℝ fun M' => Φ (hermCLM (d.Idx N) M')) M B B'
      = fderiv ℝ (fderiv ℝ Φ) M B B'
  rw [fderiv2_comp_clm_apply (hermCLM (d.Idx N)) (by rw [hPM]; exact hΦ), hPM,
    hermCLM_of_isHermitian hB, hermCLM_of_isHermitian hB']

/-- The regularisation has the same first directional derivative at a Hermitian matrix along a
used coordinate direction. -/
theorem coordD1_hermFun {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hΦ : DifferentiableAt ℝ Φ M) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    coordD1 d N (hermFun d N Φ) M p = coordD1 d N Φ M p :=
  fderiv_hermFun_apply hM hΦ (Bmat_isHermitian hp)

/-- The regularisation has the same second directional derivative at a Hermitian matrix along a
used coordinate direction. -/
theorem coordD2_hermFun {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hΦ : ContDiffAt ℝ 2 Φ M) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    coordD2 d N (hermFun d N Φ) M p = coordD2 d N Φ M p :=
  fderiv2_hermFun_apply hM hΦ (Bmat_isHermitian hp) (Bmat_isHermitian hp)

/-- The same at any direction the Wirtinger second derivative reads
(`RBM.Gauss.isHermitian_Bmat_of`), used or not. -/
theorem coordD2_hermFun_of {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (hΦ : ContDiffAt ℝ 2 Φ M)
    {i j : d.Idx N} {b : Bool} (hb : i ≠ j ∨ b = true) :
    coordD2 d N (hermFun d N Φ) M (i, j, b) = coordD2 d N Φ M (i, j, b) :=
  fderiv2_hermFun_apply hM hΦ (isHermitian_Bmat_of i j b hb) (isHermitian_Bmat_of i j b hb)

/-- **The regularisation has the same Wirtinger second derivative** at a Hermitian matrix. -/
theorem wirtSecond_hermFun {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (hΦ : ContDiffAt ℝ 2 Φ M)
    (i j : d.Idx N) :
    wirtSecond d N (hermFun d N Φ) M i j = wirtSecond d N Φ M i j := by
  unfold wirtSecond
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    exact coordD2_hermFun_of hM hΦ (Or.inr rfl)
  · rw [ite_eq_right hij, ite_eq_right hij, coordD2_hermFun_of hM hΦ (Or.inl hij),
      coordD2_hermFun_of hM hΦ (Or.inl hij)]

end Herm

/-! ### The primed classes -/

section Classes

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **`RBM.Gauss.TestFun` quantified over the Hermitian matrices only.**

`∀ M` is weakened to `∀ M, M.IsHermitian →` in every field, and the global `ContDiff ℝ 2` to
`ContDiffAt ℝ 2` at each Hermitian matrix — which is still a statement about a full
neighbourhood in the ambient matrix space, and is what the resolvent supplies there
(`M - z` is invertible at Hermitian `M` when `Im z ≠ 0`, and invertibility is open).

The class is weaker than `RBM.Gauss.TestFun` (`RBM.Gauss.TestFun.toTestFun'`), and everything
T71 proves from `TestFun` is re-proved from it below by regularisation
(`RBM.Gauss.TestFun'.herm`). -/
structure TestFun' (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) : Prop where
  /-- `Φ` is twice continuously differentiable near every Hermitian matrix. -/
  contDiffAt : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M
  /-- `Φ` is bounded on the Hermitian matrices. -/
  bdd₀ : ∃ C : ℝ, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ‖Φ M‖ ≤ C
  /-- The first derivative of `Φ` is bounded at the Hermitian matrices. -/
  bdd₁ : ∃ C : ℝ, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C
  /-- The second derivative of `Φ` is bounded at the Hermitian matrices. -/
  bdd₂ : ∃ C : ℝ, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
    ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C

/-- **The old class is contained in the new one.**  So every existing supply of
`RBM.Gauss.TestFun` — `RBM.Gauss.testFun_loopObs`, `RBM.Gauss.testFun_momentFun_ukerObs`, … —
is a supply of `RBM.Gauss.TestFun'`, and no existing statement has to change. -/
theorem TestFun.toTestFun' (h : TestFun d N Φ) : TestFun' d N Φ where
  contDiffAt := fun _ _ => h.contDiff.contDiffAt
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, fun M _ => hC M⟩
  bdd₁ := let ⟨C, hC⟩ := h.bdd₁; ⟨C, fun M _ => hC M⟩
  bdd₂ := let ⟨C, hC⟩ := h.bdd₂; ⟨C, fun M _ => hC M⟩

/-- **The bridge**: the Hermitian regularisation of a primed test function is an honest
`RBM.Gauss.TestFun`, with the *same* constants.  This is what makes the primed generator
identity a corollary of the unprimed one rather than a second dominated-convergence argument:
`hermFun` changes no value and no derivative at the points and in the directions that the
identity ever reads (`hermFun_of_isHermitian`, `coordD1_hermFun`, `coordD2_hermFun`). -/
theorem TestFun'.herm (h : TestFun' d N Φ) : TestFun d N (hermFun d N Φ) where
  contDiff := by
    rw [contDiff_iff_contDiffAt]
    intro M
    exact (h.contDiffAt _ (isHermitian_hermCLM M)).comp M (hermCLM (d.Idx N)).contDiff.contDiffAt
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, fun M => hC _ (isHermitian_hermCLM M)⟩
  bdd₁ := by
    obtain ⟨C, hC⟩ := h.bdd₁
    exact ⟨C, fun M => norm_fderiv_comp_clm_le _
      ((h.contDiffAt _ (isHermitian_hermCLM M)).differentiableAt (by norm_num))
      (hC _ (isHermitian_hermCLM M)) (norm_hermCLM_opNorm_le _)⟩
  bdd₂ := by
    obtain ⟨C, hC⟩ := h.bdd₂
    exact ⟨C, fun M => norm_fderiv2_comp_clm_le _ (h.contDiffAt _ (isHermitian_hermCLM M))
      (hC _ (isHermitian_hermCLM M)) (norm_hermCLM_opNorm_le _)⟩

variable {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **`RBM.Gauss.TestFunT` quantified over the Hermitian matrices only.**  The window `T` is
unchanged — it is the *time* restriction, forced by `Im z_u → 0` as `u → 1`, and has nothing
to do with the matrix restriction added here. -/
structure TestFunT' (d : Dims) (N : ℕ) (T : Set ℝ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) : Prop where
  /-- Joint `C²` in `(time, matrix)` over the window, at Hermitian matrices. -/
  contDiffAt : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)
  /-- `Ψ` is bounded on the Hermitian matrices, uniformly over the window. -/
  bdd₀ : ∃ C : ℝ, ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ‖Ψ u M‖ ≤ C
  /-- `∂_M Ψ` is bounded at the Hermitian matrices, uniformly over the window. -/
  bdd₁ : ∃ C : ℝ, ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
    ‖fderiv ℝ (Ψ u) M‖ ≤ C
  /-- `∂²_M Ψ` is bounded at the Hermitian matrices, uniformly over the window. -/
  bdd₂ : ∃ C : ℝ, ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
    ‖fderiv ℝ (fderiv ℝ (Ψ u)) M‖ ≤ C
  /-- `∂_1 Ψ` is bounded at the Hermitian matrices, uniformly over the window. -/
  bddT : ∃ C : ℝ, ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
    ‖timeD1 Ψ u M‖ ≤ C

/-- The old time-dependent class is contained in the new one. -/
theorem TestFunT.toTestFunT' (h : TestFunT d N T Ψ) : TestFunT' d N T Ψ where
  contDiffAt := fun u hu M _ => h.contDiffAt u hu M
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, fun u hu M _ => hC u hu M⟩
  bdd₁ := let ⟨C, hC⟩ := h.bdd₁; ⟨C, fun u hu M _ => hC u hu M⟩
  bdd₂ := let ⟨C, hC⟩ := h.bdd₂; ⟨C, fun u hu M _ => hC u hu M⟩
  bddT := let ⟨C, hC⟩ := h.bddT; ⟨C, fun u hu M _ => hC u hu M⟩

/-- Each slice of a `RBM.Gauss.TestFunT'` is `C²` at each Hermitian matrix — the primed form
of the step `RBM.Gauss.TestFunT.slice` takes. -/
theorem TestFunT'.contDiffAt_slice (h : TestFunT' d N T Ψ) {u : ℝ} (hu : u ∈ T)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) : ContDiffAt ℝ 2 (Ψ u) M :=
  (h.contDiffAt u hu M hM).comp M ((contDiff_const.prodMk contDiff_id).contDiffAt (x := M))

/-- Each slice of a `RBM.Gauss.TestFunT'` is a `RBM.Gauss.TestFun'`. -/
theorem TestFunT'.slice (h : TestFunT' d N T Ψ) {u : ℝ} (hu : u ∈ T) : TestFun' d N (Ψ u) where
  contDiffAt := fun _ hM => h.contDiffAt_slice hu hM
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, hC u hu⟩
  bdd₁ := let ⟨C, hC⟩ := h.bdd₁; ⟨C, hC u hu⟩
  bdd₂ := let ⟨C, hC⟩ := h.bdd₂; ⟨C, hC u hu⟩

/-- **The bridge, time-dependent version.** -/
theorem TestFunT'.herm (h : TestFunT' d N T Ψ) : TestFunT d N T (hermFunT d N Ψ) where
  contDiffAt := by
    intro u hu M
    have hmap : ContDiff ℝ 2 fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (q.1, hermCLM (d.Idx N) q.2) :=
      contDiff_fst.prodMk ((hermCLM (d.Idx N)).contDiff.comp contDiff_snd)
    exact (h.contDiffAt u hu _ (isHermitian_hermCLM M)).comp (u, M) hmap.contDiffAt
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, fun u hu M => hC u hu _ (isHermitian_hermCLM M)⟩
  bdd₁ := by
    obtain ⟨C, hC⟩ := h.bdd₁
    refine ⟨C, fun u hu M => ?_⟩
    have hsl : hermFunT d N Ψ u = fun M' => Ψ u (hermCLM (d.Idx N) M') := rfl
    rw [hsl]
    exact norm_fderiv_comp_clm_le _
      ((h.contDiffAt_slice hu (isHermitian_hermCLM M)).differentiableAt (by norm_num))
      (hC u hu _ (isHermitian_hermCLM M)) (norm_hermCLM_opNorm_le _)
  bdd₂ := by
    obtain ⟨C, hC⟩ := h.bdd₂
    refine ⟨C, fun u hu M => ?_⟩
    have hsl : hermFunT d N Ψ u = fun M' => Ψ u (hermCLM (d.Idx N) M') := rfl
    rw [hsl]
    exact norm_fderiv2_comp_clm_le _ (h.contDiffAt_slice hu (isHermitian_hermCLM M))
      (hC u hu _ (isHermitian_hermCLM M)) (norm_hermCLM_opNorm_le _)
  bddT := by
    obtain ⟨C, hC⟩ := h.bddT
    refine ⟨C, fun u hu M => ?_⟩
    rw [timeD1_hermFunT_apply]
    exact hC u hu _ (isHermitian_hermCLM M)

end Classes

/-! ### The generator identity, for the primed classes -/

section Identity

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- The regularisation changes no integral along the flow: `H_s` is Hermitian. -/
theorem integral_hermFun_Hflow (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (s : ℝ) :
    ∫ ω, hermFun d N Φ (Hflow d N s ω) ∂(P d) = ∫ ω, Φ (Hflow d N s ω) ∂(P d) :=
  integral_congr_ae (Eventually.of_forall fun ω =>
    hermFun_of_isHermitian (Hflow_isHermitian d N s ω))

theorem funext_integral_hermFun_Hflow (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :
    (fun s : ℝ => ∫ ω, hermFun d N Φ (Hflow d N s ω) ∂(P d))
      = fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d) :=
  funext fun s => integral_hermFun_Hflow Φ s

/-- **T71's generator identity under the two hypotheses that are actually used**: `Φ` is `C²`
at each Hermitian matrix (which is where the conclusion's derivatives are read), and its
*regularisation* is a `RBM.Gauss.TestFun` (which is what the domination needs).

The conclusion is unchanged: it is about `Φ` itself, not about its regularisation.  The proof
is *not* a second dominated-convergence argument: it is the unprimed identity for
`hermFun d N Φ`, transported by the fact that neither the values along the flow nor the second
derivatives along the used coordinate directions can tell the two apart.

This is the form the moment route can use, because the raw loop has `hreg`
(`RBM.EGDef.contDiffAt_gloop_matrix`) and its regularisation is T133's `ukerObs`, for which
`hbd` is `RBM.Gauss.testFun_momentFun_ukerObs`.  `RBM.Gauss.hasDerivAt_integral_Phi'` is the
`RBM.Gauss.TestFun'` packaging of it. -/
theorem hasDerivAt_integral_Phi_of_herm (hst : MatrixStein d)
    (hreg : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M)
    (hbd : TestFun d N (hermFun d N Φ)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d)) u := by
  have key := hasDerivAt_integral_Phi hst hbd hu
  have hsum : ∀ p ∈ usedCoord d N,
      (gvar d (crd d N p) : ℝ) • ∫ ω, coordD2 d N (hermFun d N Φ) (Hflow d N u ω) p ∂(P d)
        = (gvar d (crd d N p) : ℝ) • ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d) := by
    intro p hp
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => coordD2_hermFun
      (Hflow_isHermitian d N u ω) (hreg _ (Hflow_isHermitian d N u ω)) hp)
  rw [funext_integral_hermFun_Hflow Φ, Finset.sum_congr rfl hsum] at key
  exact key

/-- **T71's generator identity for `RBM.Gauss.TestFun'`**, coordinate form. -/
theorem hasDerivAt_integral_Phi' (hst : MatrixStein d) (h : TestFun' d N Φ) {u : ℝ}
    (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d)) u :=
  hasDerivAt_integral_Phi_of_herm hst h.contDiffAt h.herm hu

/-- **T71's generator identity in the paper's `∑_{ij} S_ij` form**, under the same two
hypotheses as `RBM.Gauss.hasDerivAt_integral_Phi_of_herm`. -/
theorem hasDerivAt_integral_Phi_pairs_of_herm (hst : MatrixStein d)
    (hreg : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M)
    (hbd : TestFun d N (hermFun d N Φ)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d)) u := by
  have key := hasDerivAt_integral_Phi_pairs hst hbd hu
  have hsum : ∀ i : d.Idx N, ∀ _ : i ∈ Finset.univ,
      (∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (hermFun d N Φ) (Hflow d N u ω) i j ∂(P d))
        = ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
            ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d) := by
    intro i _
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => wirtSecond_hermFun
      (Hflow_isHermitian d N u ω) (hreg _ (Hflow_isHermitian d N u ω)) i j)
  rw [funext_integral_hermFun_Hflow Φ, Finset.sum_congr rfl hsum] at key
  exact key

/-- **T71's generator identity for `RBM.Gauss.TestFun'`**, in the paper's `∑_{ij} S_ij` form. -/
theorem hasDerivAt_integral_Phi_pairs' (hst : MatrixStein d) (h : TestFun' d N Φ) {u : ℝ}
    (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d)) u :=
  hasDerivAt_integral_Phi_pairs_of_herm hst h.contDiffAt h.herm hu

variable {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

theorem funext_integral_hermFunT_Hflow (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :
    (fun s : ℝ => ∫ ω, hermFunT d N Ψ s (Hflow d N s ω) ∂(P d))
      = fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d) :=
  funext fun s => integral_congr_ae (Eventually.of_forall fun ω =>
    hermFunT_of_isHermitian s (Hflow_isHermitian d N s ω))

/-- **T132b's generator identity with explicit time dependence, under the two hypotheses that
are actually used.**  This is the theorem T180 needed and could not have: `TestFunT` is
over-quantified for `Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}`. -/
theorem hasDerivAt_integral_Psi_of_herm (hst : MatrixStein d)
    (hreg : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ContDiffAt ℝ 2 (Ψ u) M)
    (hbd : TestFunT d N T (hermFunT d N Ψ)) {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
          ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)) u := by
  have huT : u ∈ T := mem_of_mem_nhds hT
  have key := hasDerivAt_integral_Psi hst hbd hu hT
  have htime : ∫ ω, timeD1 (hermFunT d N Ψ) u (Hflow d N u ω) ∂(P d)
      = ∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d) :=
    integral_congr_ae (Eventually.of_forall fun ω =>
      timeD1_hermFunT Ψ u (Hflow_isHermitian d N u ω))
  have hsum : ∀ p ∈ usedCoord d N,
      (gvar d (crd d N p) : ℝ) •
          ∫ ω, coordD2 d N (hermFunT d N Ψ u) (Hflow d N u ω) p ∂(P d)
        = (gvar d (crd d N p) : ℝ) • ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d) := by
    intro p hp
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => coordD2_hermFun
      (Hflow_isHermitian d N u ω)
      (hreg u huT _ (Hflow_isHermitian d N u ω)) hp)
  rw [funext_integral_hermFunT_Hflow Ψ, htime, Finset.sum_congr rfl hsum] at key
  exact key

/-- **T132b's generator identity with explicit time dependence, for `RBM.Gauss.TestFunT'`**,
coordinate form. -/
theorem hasDerivAt_integral_Psi' (hst : MatrixStein d) (h : TestFunT' d N T Ψ)
    {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
          ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)) u :=
  hasDerivAt_integral_Psi_of_herm hst (fun _ hu' _ hM => h.contDiffAt_slice hu' hM) h.herm hu hT

/-- **T132b's generator identity with explicit time dependence**, in the paper's
`∑_{ij} S_ij` form — the shape the moment route consumes — under the two hypotheses that are
actually used. -/
theorem hasDerivAt_integral_Psi_pairs_of_herm (hst : MatrixStein d)
    (hreg : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ContDiffAt ℝ 2 (Ψ u) M)
    (hbd : TestFunT d N T (hermFunT d N Ψ)) {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d)) u := by
  have huT : u ∈ T := mem_of_mem_nhds hT
  have key := hasDerivAt_integral_Psi_pairs hst hbd hu hT
  have htime : ∫ ω, timeD1 (hermFunT d N Ψ) u (Hflow d N u ω) ∂(P d)
      = ∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d) :=
    integral_congr_ae (Eventually.of_forall fun ω =>
      timeD1_hermFunT Ψ u (Hflow_isHermitian d N u ω))
  have hsum : ∀ i : d.Idx N, ∀ _ : i ∈ Finset.univ,
      (∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (hermFunT d N Ψ u) (Hflow d N u ω) i j ∂(P d))
        = ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
            ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d) := by
    intro i _
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => wirtSecond_hermFun
      (Hflow_isHermitian d N u ω)
      (hreg u huT _ (Hflow_isHermitian d N u ω)) i j)
  rw [funext_integral_hermFunT_Hflow Ψ, htime, Finset.sum_congr rfl hsum] at key
  exact key

/-- **T132b's generator identity with explicit time dependence, for `RBM.Gauss.TestFunT'`**, in
the paper's `∑_{ij} S_ij` form. -/
theorem hasDerivAt_integral_Psi_pairs' (hst : MatrixStein d) (h : TestFunT' d N T Ψ)
    {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d)) u :=
  hasDerivAt_integral_Psi_pairs_of_herm hst (fun _ hu' _ hM => h.contDiffAt_slice hu' hM)
    h.herm hu hT

end Identity

/-! ### T72's pointwise moment bound, at Hermitian matrices -/

section MomentPt

/-- `ContDiffAt` version of `RBM.Gauss.contDiff_momentFun`. -/
theorem contDiffAt_momentFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {F : E → ℂ} {M : E} (hF : ContDiffAt ℝ n F M) (p : ℕ) :
    ContDiffAt ℝ n (momentFun F p) M := by
  have hconj : ContDiffAt ℝ n (fun M' => (starRingEnd ℂ) (F M')) M :=
    ContDiffAt.comp M ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt) hF
  exact (hF.mul hconj).pow p

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- The regularisation of a function that is `C²` at every Hermitian matrix is `C²`
everywhere. -/
theorem contDiff_hermFun
    (hF : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian → ContDiffAt ℝ 2 F M) :
    ContDiff ℝ 2 (hermFun d N F) := by
  rw [contDiff_iff_contDiffAt]
  intro M
  exact (hF _ (isHermitian_hermCLM M)).comp M (hermCLM (d.Idx N)).contDiff.contDiffAt

/-- `momentFun` commutes with the regularisation, by definition. -/
theorem momentFun_hermFun (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (p : ℕ) :
    momentFun (hermFun d N F) p = hermFun d N (momentFun F p) := rfl

theorem genD_hermFun {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hF : ContDiffAt ℝ 2 F M) : genD d N (hermFun d N F) M = genD d N F M := by
  rw [genD, genD]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  congr 1
  exact coordD2_hermFun hM hF hq

theorem quadVar_hermFun {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hF : DifferentiableAt ℝ F M) : quadVar d N (hermFun d N F) M = quadVar d N F M := by
  rw [quadVar, quadVar]
  refine Finset.sum_congr rfl fun q hq => ?_
  congr 2
  exact congrArg norm (coordD1_hermFun hM hF hq)

theorem genMomentPt_hermFun {p : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hF : ContDiffAt ℝ 2 F M) : genMomentPt d N (hermFun d N F) p M = genMomentPt d N F p M := by
  rw [genMomentPt, genMomentPt]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  congr 1
  exact congrArg Complex.re (coordD2_hermFun hM (contDiffAt_momentFun hF p) hq)

/-- **T72's Grönwall-ready pointwise bound, with the global `ContDiff ℝ 2` weakened.**

`RBM.Gauss.genMomentPt_le` asks for `F` to be `C²` on the whole matrix space; the moment
route's `F` is not.  Here `F` need only be `C²` at each Hermitian matrix, and the conclusion is
asserted at a Hermitian matrix — which is where the flow lives.  This is the second seam T180
recorded, and it closes the same way the first one does. -/
theorem genMomentPt_le'
    (hF : ∀ M' : Matrix (d.Idx N) (d.Idx N) ℂ, M'.IsHermitian → ContDiffAt ℝ 2 F M')
    {p : ℕ} (hp : 1 ≤ p) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    genMomentPt d N F p M
      ≤ 2 * p * ‖F M‖ ^ (2 * p - 1) * ‖genD d N F M‖
        + p * (2 * p - 1) * ‖F M‖ ^ (2 * p - 2) * quadVar d N F M := by
  have key := genMomentPt_le (contDiff_hermFun hF) hp M
  rwa [genMomentPt_hermFun hM (hF M hM), hermFun_of_isHermitian hM,
    genD_hermFun hM (hF M hM),
    quadVar_hermFun hM ((hF M hM).differentiableAt (by norm_num))] at key

end MomentPt

/-! ### Satisfiability: the moment route's own observable -/

section Satisfiability

variable {d : Dims} {N : ℕ}

/-- **The moment route's observable with the *raw* resolvent.**

`(U_{s,t,σ} ∘ (L - K))_a` as a function of the matrix, built from `RBM.gloop` — not from
`RBM.Gauss.loopObs` — so that this is literally `RBM.MomentDuhamel.lkFun` conjugated by the
propagator, i.e. the function whose `2p`-th moment `RBM.MomentDuhamel.Hyp.momentDuhamel` is
about (`RBM.MomentDuhamel.lkFun_H`).  It is **not** in `RBM.Gauss.TestFun`: `(M - z)⁻¹` is
unbounded off the Hermitian set and `Ring.inverse` is `0` at a singular non-Hermitian `M`. -/
noncomputable def ukerRaw (d : Dims) (N : ℕ) (z : ℂ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (s t : ℂ) (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Uker (d.L N) ξ s t (fun b => gloop (d.L N) (d.W N) M z ⟨σ, List.ofFn b⟩ - K b) a

/-- **The regularisation of the raw observable is T133's `RBM.Gauss.ukerObs`** — by `rfl`,
because `loopObs` *is* `gloop ∘ hermCLM`.  This is the whole reason the bounds of the primed
class are available for it. -/
theorem hermFun_ukerRaw (z : ℂ) (σ : List Bool) {m : ℕ} (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) :
    hermFun d N (ukerRaw d N z σ ξ s t K a) = ukerObs d N z σ ξ s t K a := by
  funext M
  simp only [hermFun, ukerRaw, ukerObs, loopObs]

/-- The same for `|·|^{2p}`. -/
theorem hermFun_momentFun_ukerRaw (z : ℂ) (σ : List Bool) {m : ℕ} (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ) :
    hermFun d N (momentFun (ukerRaw d N z σ ξ s t K a) p)
      = momentFun (ukerObs d N z σ ξ s t K a) p := by
  funext M
  have hpt : ukerRaw d N z σ ξ s t K a (hermCLM (d.Idx N) M) = ukerObs d N z σ ξ s t K a M :=
    congrFun (hermFun_ukerRaw z σ ξ s t K a) M
  simp only [hermFun, momentFun, hpt]

/-- **The raw observable is `C²` at every Hermitian matrix**, for every spectral parameter off
the real axis: `M - z` is invertible there and invertibility is an open condition
(`RBM.EGDef.contDiffAt_gloop_matrix`).  This is the `hreg` half of
`RBM.Gauss.hasDerivAt_integral_Phi_pairs_of_herm`. -/
theorem contDiffAt_ukerRaw {z : ℂ} (hz : z.im ≠ 0) (σ : List Bool) {m : ℕ} (ξ : Fin m → ℂ)
    (s t : ℂ) (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (ukerRaw d N z σ ξ s t K a) M := by
  have hfun : ukerRaw d N z σ ξ s t K a = fun M' => ∑ b : LoopArg (d.L N) m,
      (∏ i, edgeKer (d.L N) (ξ i) s t (a i) (b i))
        * (gloop (d.L N) (d.W N) M' z ⟨σ, List.ofFn b⟩ - K b) := rfl
  rw [hfun]
  refine ContDiffAt.sum fun b _ => ?_
  exact contDiffAt_const.mul
    ((EGDef.contDiffAt_gloop_matrix (L := d.L N) (W := d.W N) hM hz _).sub contDiffAt_const)

/-- `|(U ∘ (L - K))_a|^{2p}` with the raw resolvent is `C²` at every Hermitian matrix. -/
theorem contDiffAt_momentFun_ukerRaw {z : ℂ} (hz : z.im ≠ 0) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (s t : ℂ) (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (momentFun (ukerRaw d N z σ ξ s t K a) p) M :=
  contDiffAt_momentFun (contDiffAt_ukerRaw hz σ ξ s t K a hM) p

/-- **The satisfiability check: the generator identity holds for the moment route's own
observable, with the raw resolvent.**

Both hypotheses of `RBM.Gauss.hasDerivAt_integral_Phi_pairs_of_herm` are supplied from the
repository: `hreg` by `RBM.Gauss.contDiffAt_momentFun_ukerRaw`, and `hbd` — the bounds — by
T133's `RBM.Gauss.testFun_momentFun_ukerObs` through `RBM.Gauss.hermFun_momentFun_ukerRaw`.
So the relaxation of T187 is not a weakening into a vacuum: the class of hypotheses it asks
for is met by the function `RBM.MomentDuhamel.Hyp.momentDuhamel` is about, at every spectral
parameter with `Im z ≠ 0` — in particular at every `z_u` on the window `[s_N, t_N]`,
`t_N < 1`.

What is *not* claimed: that this raw observable is in `RBM.Gauss.TestFun'` itself.  Its
derivative bounds at Hermitian matrices are true — they are powers of `‖G‖ ≤ |Im z|⁻¹` — but
proving them in Lean needs a pointwise version of the `BddC2C` chain of
`RBM1D/Gauss/LoopC2.lean`, which is stated for globally bounded functions.  The `_of_herm`
form above is exactly what avoids needing them. -/
theorem hasDerivAt_integral_momentFun_ukerRaw (hst : MatrixStein d) {z : ℂ} {η : ℝ}
    (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|) {m : ℕ} {σ : List Bool}
    (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ) (K : LoopArg (d.L N) m → ℂ)
    (a : LoopArg (d.L N) m) (p : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun r : ℝ => ∫ ω, momentFun (ukerRaw d N z σ ξ s t K a) p (Hflow d N r ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        ∫ ω, wirtSecond d N (momentFun (ukerRaw d N z σ ξ s t K a) p)
          (Hflow d N u ω) i j ∂(P d)) u :=
  by
  refine hasDerivAt_integral_Phi_pairs_of_herm hst
    (fun _ hM => contDiffAt_momentFun_ukerRaw hz σ ξ s t K a p hM) ?_ hu
  rw [hermFun_momentFun_ukerRaw]
  exact testFun_momentFun_ukerObs hz hη hzη hσ ξ s t K a p

/-- The primed class is inhabited by the regularised moment-route observable, with the
constants of T133. -/
theorem testFun'_momentFun_ukerObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) {m : ℕ} {σ : List Bool} (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ) :
    TestFun' d N (momentFun (ukerObs d N z σ ξ s t K a) p) :=
  (testFun_momentFun_ukerObs hz hη hzη hσ ξ s t K a p).toTestFun'

end Satisfiability

end RBM.Gauss



