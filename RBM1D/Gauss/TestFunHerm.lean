/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.LoopIto
import RBM1D.Hierarchy.EGDef

/-!
# Test functions quantified over the Hermitian matrices only

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  `RBM.Gauss.TestFun` asks for `C²` and for bounds on `Φ`, `∂Φ`, `∂²Φ` at
**every** matrix.  The moment-route test function
`Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}` is not in that class and cannot be:
`(M - z_u)⁻¹` is unbounded off the Hermitian set, and at a singular non-Hermitian `M` the
function is not even continuous (Lean's `Ring.inverse` is `0` there).  On the Hermitian set
both conditions hold, and the whole argument lives there: the flow `H_u = √u X` is Hermitian
(`RBM.Gauss.Hflow_isHermitian`) and so are the coordinate directions `Bmat` on used
coordinates (`RBM.Gauss.Bmat_isHermitian`).

This file adds the primed class and the Hermitian regularisation.

## Main definitions

* `RBM.Gauss.TestFun'` — `RBM.Gauss.TestFun` with `∀ M` weakened to `∀ M, M.IsHermitian →` in
  every field, `ContDiff` weakened to `ContDiffAt` at Hermitian points.
* `RBM.Gauss.hermFun` — `Φ ∘ hermCLM`, the Hermitian *regularisation* of a test function.

## Main results

* `RBM.Gauss.fderiv_comp_clm_apply`, `RBM.Gauss.fderiv2_comp_clm_apply` — the calculus that
  makes the relaxation work: for a continuous linear `P`, the first and second derivatives of
  `f ∘ P` at `M` are those of `f` at `P M`, read on the directions `P B`.  With `P = hermCLM`,
  `M` Hermitian and `B` Hermitian this says the regularisation changes **nothing**: the
  sentence in `RBM1D/Gauss/Generator.lean`'s "The Hermitian projection" section, which was
  prose there, is `RBM.Gauss.coordD1_hermFun` / `RBM.Gauss.coordD2_hermFun_of` here.
* `RBM.Gauss.TestFun'.herm` — **the bridge**: a primed test function has an unprimed
  regularisation, with the same constants.  This is what lets a generator identity for the
  primed class be *deduced* from the unprimed one instead of reproving the dominated-convergence
  argument on the flow.

## What is *not* claimed

Nothing here says that the raw `Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}`, with
`RBM.MomentDuhamel.lkFun`'s unregularised `gloop`, is in `TestFun'`; that needs bounds on the
derivatives of `gloop` *at* Hermitian points, i.e. a pointwise version of the `BddC2C` chain of
`RBM1D/Gauss/LoopC2.lean`.  The regularised `RBM.Gauss.loopObs` agrees with the raw loop at
every Hermitian matrix, in particular along the whole flow.

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

@[simp] theorem hermFun_of_isHermitian {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) : hermFun d N Φ M = Φ M := by
  rw [hermFun, hermCLM_of_isHermitian hM]

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

The class is weaker than `RBM.Gauss.TestFun`, and the regularisation `RBM.Gauss.TestFun'.herm`
turns it back into a `RBM.Gauss.TestFun`. -/
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

/-- **The bridge**: the Hermitian regularisation of a primed test function is an honest
`RBM.Gauss.TestFun`, with the *same* constants.  This is what makes the primed generator
identity a corollary of the unprimed one rather than a second dominated-convergence argument:
`hermFun` changes no value and no derivative at the points and in the directions that the
identity ever reads (`hermFun_of_isHermitian`, `coordD1_hermFun`, `coordD2_hermFun_of`). -/
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

end Classes

/-! ### The generator identity, for the primed classes -/

section Identity

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

variable {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

end Identity

/-! ### the pointwise moment bound, at Hermitian matrices -/

section MomentPt

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

end MomentPt

/-! ### Satisfiability: the moment route's own observable -/

section Satisfiability

variable {d : Dims} {N : ℕ}

end Satisfiability

end RBM.Gauss



