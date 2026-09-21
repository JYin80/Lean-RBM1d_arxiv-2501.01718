/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentGronwall
import RBM1D.Gauss.Hierarchy
import RBM1D.Hierarchy.Kernel

/-!
# `C²` bounds for the loop observables (T133)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, (2.41) and (5.17), on the analytic side only.

`RBM1D/Gauss/MomentGronwall.lean` (T72) discharged `RBM.Gauss.TestFun` for the *degree one*
observables `φ(G)`; the loop `L_{σ,a}(H) = ⟨∏_i G(σ_i) E_{a_i}⟩` is a **product** of `n`
resolvents, and `docs/STATUS.md` records the two missing pieces as
"Fréchet (not line-wise) `C²` for the matrix inverse plus a Leibniz rule for the
`List.foldr` product".  This file supplies the second one and packages the first.

## The quantitative class

`RBM.Gauss.BddC2C F C₀ C₁ C₂` is `RBM.Gauss.BddC2` with the three existentials made
explicit: `F` is `C²` and `‖F‖ ≤ C₀`, `‖DF‖ ≤ C₁`, `‖D²F‖ ≤ C₂` **everywhere**.  It takes
values in an arbitrary real normed space, so the same class covers the matrix-valued
partial products and the scalar loop.

The Leibniz step is `RBM.Gauss.bddC2C_clm_apply`: for `F` valued in `V →L[ℝ] V'` and `G`
valued in `V`,

  `D²(F·G)[B,A] = (DF[B])(DG[A]) + F(D²G[B,A]) + (D²F[B,A])(G) + (DF[A])(DG[B])`,

whence `C₂(F·G) = C₀(F)C₂(G) + 2C₁(F)C₁(G) + C₂(F)C₀(G)`.  Matrix multiplication is the
special case `F = mul ℝ (Matrix n n ℂ) ∘ F'` (`RBM.Gauss.bddC2C_matrix_mul`), and that is
what makes the `List.foldr` of `RBM.gloopProd` an induction.

## Main results

* `RBM.Gauss.bddC2C_clm_apply` — **`BddC2C` is closed under products** (the Leibniz gap
  of T72/T76), with explicit constants.
* `RBM.Gauss.bddC2C_resH` — the Fréchet `C²` bounds `η⁻¹`, `η⁻²`, `2η⁻³` for the resolvent
  (pre-composed with `RBM.Gauss.hermCLM`, T71's device for global definedness).
* `RBM.Gauss.bddC2C_gloopProdFun` — the matrix product `∏_i G(σ_i) E_{a_i}` is `C²` with
  constants `Bⁿ`, `n Bⁿ`, `n² Bⁿ`, `B = 2(1 + η⁻¹)³`.
* `RBM.Gauss.bddC2C_loopObs`, `RBM.Gauss.bddC2_loopObs` — the loop `L_{σ,a}` itself.
* `RBM.Gauss.testFun_loopObs_of_im_le` — **the `TestFun` of `RBM1D/Gauss/Hierarchy.lean`
  (T76) for a loop observable, unconditionally**; `RBM.Gauss.testFun_momentFun_loopObs`
  is the `|L|^{2p}` version that the moment route consumes.
* `RBM.Gauss.bddC2_ukerObs`, `RBM.Gauss.testFun_momentFun_ukerObs` — the same for
  `(U_{s,t,σ} ∘ (L − K))_a` of (5.17), which is a finite linear combination of loops with
  `H`-independent coefficients.

### Uniformity in `z`, and the joint derivative (T141)

* `RBM.Gauss.bddC2C_loopObs_ball` and friends — the bounds above hold **uniformly in `z` over
  a ball** with a common lower bound on `|Im z|`.  This is free: the constants never mention
  `z`.
* `RBM.Gauss.BddC1On` — the first-order, set-localised version of `RBM.Gauss.BddC2C`, closed
  under products, which is the class the parametric-integral lemmas consume.
* `RBM.Gauss.norm_fderiv_Gsig_flow_le` — the joint derivative of a resolvent factor in
  `(flow time, spectral time)` is bounded **deterministically** (no `‖X(ω)‖`), because
  `∂_v H_v = (2v)⁻¹ H_v` and `G H G = G + ζ G²`.
* `RBM.Gauss.bddC1On_gloop_flow` — the same for the whole loop, uniformly over a set of pairs.
* `RBM.Gauss.differentiableAt_integral_gloop_flow` — **the `hjoint` hypothesis of
  `RBM1D/Gauss/LoopIto.lean` (T134), discharged.**

## Deviations

* The trace is bounded through `RBM.Gauss.traceCLM`, whose operator norm is at most
  `Fintype.card n = W L`.  The value bound of (5.2) (`RBM.norm_gloop_le_of_le_abs_im`) is
  sharper — it rotates the last `E_{a_n}` to the end and pays nothing for the trace — but
  the derivative terms are not of that shape, so the constants here carry one factor of the
  dimension.  They are deterministic and polynomial, which is all the dominated-convergence
  consumers need.
* The constants are not optimal: `B = 2(1 + η⁻¹)³` dominates all of `1`, `η⁻¹`, `η⁻²`,
  `2η⁻³` at once so that the induction over the `foldr` closes in the clean form
  `(Bⁿ, n Bⁿ, n² Bⁿ)`.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ### The quantitative `C²` class and its closure properties -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- **`RBM.Gauss.BddC2` with the constants exposed**, and for maps into an arbitrary real
normed space: `F` is `C²` with `‖F‖ ≤ C₀`, `‖DF‖ ≤ C₁`, `‖D²F‖ ≤ C₂` on all of `E`. -/
structure BddC2C (F : E → V) (C₀ C₁ C₂ : ℝ) : Prop where
  /-- `F` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 F
  /-- `‖F M‖ ≤ C₀` for every `M`. -/
  bdd₀ : ∀ M, ‖F M‖ ≤ C₀
  /-- `‖DF M‖ ≤ C₁` for every `M`. -/
  bdd₁ : ∀ M, ‖fderiv ℝ F M‖ ≤ C₁
  /-- `‖D²F M‖ ≤ C₂` for every `M`. -/
  bdd₂ : ∀ M, ‖fderiv ℝ (fderiv ℝ F) M‖ ≤ C₂

namespace BddC2C

variable {F : E → V} {C₀ C₁ C₂ D₀ D₁ D₂ : ℝ}

theorem nonneg₀ (h : BddC2C F C₀ C₁ C₂) : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (h.bdd₀ 0)

theorem nonneg₁ (h : BddC2C F C₀ C₁ C₂) : 0 ≤ C₁ :=
  (norm_nonneg (fderiv ℝ F 0)).trans (h.bdd₁ 0)

theorem nonneg₂ (h : BddC2C F C₀ C₁ C₂) : 0 ≤ C₂ :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)).trans (h.bdd₂ 0)

/-- The constants may be enlarged. -/
theorem mono (h : BddC2C F C₀ C₁ C₂) (h₀ : C₀ ≤ D₀) (h₁ : C₁ ≤ D₁) (h₂ : C₂ ≤ D₂) :
    BddC2C F D₀ D₁ D₂ :=
  ⟨h.contDiff, fun M => (h.bdd₀ M).trans h₀, fun M => (h.bdd₁ M).trans h₁,
    fun M => (h.bdd₂ M).trans h₂⟩

theorem differentiable (h : BddC2C F C₀ C₁ C₂) : Differentiable ℝ F :=
  h.contDiff.differentiable (by norm_num)

theorem differentiable_fderiv (h : BddC2C F C₀ C₁ C₂) : Differentiable ℝ (fderiv ℝ F) :=
  (h.contDiff.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

/-- The scalar-valued case is exactly `RBM.Gauss.BddC2`. -/
theorem bddC2 {F : E → ℂ} (h : BddC2C F C₀ C₁ C₂) : BddC2 F :=
  ⟨h.contDiff, ⟨C₀, h.bdd₀⟩, ⟨C₁, h.bdd₁⟩, ⟨C₂, h.bdd₂⟩⟩

end BddC2C

/-- A uniform bound on `DK` gives one on each directional derivative. -/
theorem norm_fderiv_apply_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : E → W} {c : ℝ} (hc : ∀ M, ‖fderiv ℝ K M‖ ≤ c) (M X : E) :
    ‖fderiv ℝ K M X‖ ≤ c * ‖X‖ :=
  ((fderiv ℝ K M).le_opNorm X).trans (mul_le_mul_of_nonneg_right (hc M) (norm_nonneg _))

/-- A uniform bound on `D²K` gives one on each mixed directional derivative. -/
theorem norm_fderiv2_apply_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : E → W} {c : ℝ} (hc : ∀ M, ‖fderiv ℝ (fderiv ℝ K) M‖ ≤ c) (M B X : E) :
    ‖fderiv ℝ (fderiv ℝ K) M B X‖ ≤ c * ‖B‖ * ‖X‖ :=
  ((fderiv ℝ (fderiv ℝ K) M B).le_opNorm X).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_apply_le hc M B) (norm_nonneg _))

/-- A constant map. -/
theorem bddC2C_const (v : V) : BddC2C (fun _ : E => v) ‖v‖ 0 0 := by
  refine ⟨contDiff_const, fun _ => le_rfl, fun M => ?_, fun M => ?_⟩
  · rw [show fderiv ℝ (fun _ : E => v) M = 0 from by simp]
    exact le_of_eq ContinuousLinearMap.opNorm_zero
  · rw [show fderiv ℝ (fderiv ℝ fun _ : E => v) M = 0 from by simp]
    exact le_of_eq ContinuousLinearMap.opNorm_zero

/-- Post-composition with a continuous linear map. -/
theorem bddC2C_clm_comp (φ : V →L[ℝ] V') {F : E → V} {C₀ C₁ C₂ : ℝ}
    (h : BddC2C F C₀ C₁ C₂) :
    BddC2C (fun M => φ (F M)) (‖φ‖ * C₀) (‖φ‖ * C₁) (‖φ‖ * C₂) := by
  have hc1 := h.nonneg₁
  have hc2 := h.nonneg₂
  have hcd : ContDiff ℝ 2 (fun M => φ (F M)) := φ.contDiff.comp h.contDiff
  have hfd : ∀ M, fderiv ℝ (fun M => φ (F M)) M = φ.comp (fderiv ℝ F M) := fun M =>
    (φ.hasFDerivAt.comp M (h.differentiable M).hasFDerivAt).fderiv
  refine ⟨hcd, fun M => ?_, fun M => ?_, fun M => ?_⟩
  · exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.bdd₀ M) (norm_nonneg _))
  · rw [hfd M]
    exact (φ.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (h.bdd₁ M) (norm_nonneg _))
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun B => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    have key : fderiv ℝ (fderiv ℝ fun M => φ (F M)) M B A
        = φ (fderiv ℝ (fderiv ℝ F) M B A) := by
      have hlhs : HasDerivAt (fun t : ℝ => fderiv ℝ (fun M => φ (F M)) (M + t • B) A)
          (fderiv ℝ (fderiv ℝ fun M => φ (F M)) M B A) 0 := hasDerivAt_dir2' hcd M A B
      have hinner : HasDerivAt (fun t : ℝ => fderiv ℝ F (M + t • B) A)
          (fderiv ℝ (fderiv ℝ F) M B A) 0 := hasDerivAt_dir2' h.contDiff M A B
      have hfun : (fun t : ℝ => fderiv ℝ (fun M => φ (F M)) (M + t • B) A)
          = fun t : ℝ => φ (fderiv ℝ F (M + t • B) A) := by
        funext t
        rw [hfd (M + t • B)]
        rfl
      rw [hfun] at hlhs
      exact hlhs.unique (by simpa [Function.comp_def] using
        (φ.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hinner)
    rw [key]
    have h1 : ‖fderiv ℝ (fderiv ℝ F) M B A‖ ≤ C₂ * ‖B‖ * ‖A‖ :=
      norm_fderiv2_apply_le h.bdd₂ M B A
    calc ‖φ (fderiv ℝ (fderiv ℝ F) M B A)‖ ≤ ‖φ‖ * ‖fderiv ℝ (fderiv ℝ F) M B A‖ :=
          φ.le_opNorm _
      _ ≤ ‖φ‖ * (C₂ * ‖B‖ * ‖A‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖φ‖ * C₂ * ‖B‖ * ‖A‖ := by ring

/-- The first Leibniz rule for the pairing `(F, G) ↦ F · G` of a `V →L[ℝ] V'`-valued map
with a `V`-valued one. -/
theorem fderiv_clm_apply_apply {F : E → (V →L[ℝ] V')} {G : E → V}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (M A : E) :
    fderiv ℝ (fun M => F M (G M)) M A = F M (fderiv ℝ G M A) + (fderiv ℝ F M A) (G M) := by
  rw [fderiv_clm_apply (hF M) (hG M)]
  rfl

/-- **The second Leibniz rule** — the step `docs/STATUS.md` records as missing (the
`List.foldr` product rule of T76). -/
theorem fderiv2_clm_apply_apply {F : E → (V →L[ℝ] V')} {G : E → V}
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (M A B : E) :
    fderiv ℝ (fderiv ℝ fun M => F M (G M)) M B A
      = ((fderiv ℝ F M B) (fderiv ℝ G M A) + F M (fderiv ℝ (fderiv ℝ G) M B A))
        + ((fderiv ℝ (fderiv ℝ F) M B A) (G M) + (fderiv ℝ F M A) (fderiv ℝ G M B)) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hzero : M + (0 : ℝ) • B = M := by simp
  have hlhs : HasDerivAt (fun t : ℝ => fderiv ℝ (fun M => F M (G M)) (M + t • B) A)
      (fderiv ℝ (fderiv ℝ fun M => F M (G M)) M B A) 0 :=
    hasDerivAt_dir2' (hF.clm_apply hG) M A B
  have hfun : (fun t : ℝ => fderiv ℝ (fun M => F M (G M)) (M + t • B) A)
      = fun t : ℝ => F (M + t • B) (fderiv ℝ G (M + t • B) A)
          + (fderiv ℝ F (M + t • B) A) (G (M + t • B)) :=
    funext fun t => fderiv_clm_apply_apply hFd hGd (M + t • B) A
  rw [hfun] at hlhs
  -- the four terms
  have h1 : HasDerivAt (fun t : ℝ => F (M + t • B)) (fderiv ℝ F M B) 0 := by
    have h := hasDerivAt_dir (hF.of_le (by norm_num)) M B 0
    rwa [hzero] at h
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ G (M + t • B) A)
      (fderiv ℝ (fderiv ℝ G) M B A) 0 := hasDerivAt_dir2' hG M A B
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ F (M + t • B) A)
      (fderiv ℝ (fderiv ℝ F) M B A) 0 := hasDerivAt_dir2' hF M A B
  have h4 : HasDerivAt (fun t : ℝ => G (M + t • B)) (fderiv ℝ G M B) 0 := by
    have h := hasDerivAt_dir (hG.of_le (by norm_num)) M B 0
    rwa [hzero] at h
  have hA := h1.clm_apply h2
  have hB := h3.clm_apply h4
  simp only [hzero] at hA hB
  exact hlhs.unique (hA.add hB)

/-- **`BddC2C` is closed under products.**  This is the Leibniz closure that
`docs/STATUS.md` lists as the missing half of `TestFun` for loops. -/
theorem bddC2C_clm_apply {F : E → (V →L[ℝ] V')} {G : E → V} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (hG : BddC2C G b₀ b₁ b₂) :
    BddC2C (fun M => F M (G M)) (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) := by
  have ha0 := hF.nonneg₀
  have ha1 := hF.nonneg₁
  have ha2 := hF.nonneg₂
  have hb0 := hG.nonneg₀
  have hb1 := hG.nonneg₁
  have hb2 := hG.nonneg₂
  refine ⟨hF.contDiff.clm_apply hG.contDiff, fun M => ?_, fun M => ?_, fun M => ?_⟩
  · exact ((F M).le_opNorm _).trans (mul_le_mul (hF.bdd₀ M) (hG.bdd₀ M) (norm_nonneg _) ha0)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    rw [fderiv_clm_apply_apply hF.differentiable hG.differentiable M A]
    have e1 : ‖F M (fderiv ℝ G M A)‖ ≤ a₀ * (b₁ * ‖A‖) :=
      ((F M).le_opNorm _).trans (mul_le_mul (hF.bdd₀ M)
        (norm_fderiv_apply_le hG.bdd₁ M A) (norm_nonneg _) ha0)
    have e2 : ‖(fderiv ℝ F M A) (G M)‖ ≤ (a₁ * ‖A‖) * b₀ :=
      ((fderiv ℝ F M A).le_opNorm _).trans
        (mul_le_mul (norm_fderiv_apply_le hF.bdd₁ M A) (hG.bdd₀ M)
          (norm_nonneg _) (by positivity))
    calc ‖F M (fderiv ℝ G M A) + (fderiv ℝ F M A) (G M)‖
        ≤ ‖F M (fderiv ℝ G M A)‖ + ‖(fderiv ℝ F M A) (G M)‖ := norm_add_le _ _
      _ ≤ a₀ * (b₁ * ‖A‖) + (a₁ * ‖A‖) * b₀ := add_le_add e1 e2
      _ = (a₀ * b₁ + a₁ * b₀) * ‖A‖ := by ring
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun B => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    rw [fderiv2_clm_apply_apply hF.contDiff hG.contDiff M A B]
    have dF1 : ∀ X : E, ‖fderiv ℝ F M X‖ ≤ a₁ * ‖X‖ := norm_fderiv_apply_le hF.bdd₁ M
    have dG1 : ∀ X : E, ‖fderiv ℝ G M X‖ ≤ b₁ * ‖X‖ := norm_fderiv_apply_le hG.bdd₁ M
    have dF2 : ‖fderiv ℝ (fderiv ℝ F) M B A‖ ≤ a₂ * ‖B‖ * ‖A‖ :=
      norm_fderiv2_apply_le hF.bdd₂ M B A
    have dG2 : ‖fderiv ℝ (fderiv ℝ G) M B A‖ ≤ b₂ * ‖B‖ * ‖A‖ :=
      norm_fderiv2_apply_le hG.bdd₂ M B A
    have e1 : ‖(fderiv ℝ F M B) (fderiv ℝ G M A)‖ ≤ (a₁ * ‖B‖) * (b₁ * ‖A‖) :=
      ((fderiv ℝ F M B).le_opNorm _).trans
        (mul_le_mul (dF1 B) (dG1 A) (norm_nonneg _) (by positivity))
    have e2 : ‖F M (fderiv ℝ (fderiv ℝ G) M B A)‖ ≤ a₀ * (b₂ * ‖B‖ * ‖A‖) :=
      ((F M).le_opNorm _).trans (mul_le_mul (hF.bdd₀ M) dG2 (norm_nonneg _) ha0)
    have e3 : ‖(fderiv ℝ (fderiv ℝ F) M B A) (G M)‖ ≤ (a₂ * ‖B‖ * ‖A‖) * b₀ :=
      ((fderiv ℝ (fderiv ℝ F) M B A).le_opNorm _).trans
        (mul_le_mul dF2 (hG.bdd₀ M) (norm_nonneg _) (by positivity))
    have e4 : ‖(fderiv ℝ F M A) (fderiv ℝ G M B)‖ ≤ (a₁ * ‖A‖) * (b₁ * ‖B‖) :=
      ((fderiv ℝ F M A).le_opNorm _).trans
        (mul_le_mul (dF1 A) (dG1 B) (norm_nonneg _) (by positivity))
    have hstep : ‖((fderiv ℝ F M B) (fderiv ℝ G M A) + F M (fderiv ℝ (fderiv ℝ G) M B A))
            + ((fderiv ℝ (fderiv ℝ F) M B A) (G M) + (fderiv ℝ F M A) (fderiv ℝ G M B))‖
        ≤ ((a₁ * ‖B‖) * (b₁ * ‖A‖) + a₀ * (b₂ * ‖B‖ * ‖A‖))
            + ((a₂ * ‖B‖ * ‖A‖) * b₀ + (a₁ * ‖A‖) * (b₁ * ‖B‖)) :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add e1 e2))
        ((norm_add_le _ _).trans (add_le_add e3 e4)))
    refine hstep.trans (le_of_eq ?_)
    ring

/-- Sums. -/
theorem bddC2C_add {F G : E → V} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (hG : BddC2C G b₀ b₁ b₂) :
    BddC2C (fun M => F M + G M) (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) := by
  have hfd : (fderiv ℝ fun M => F M + G M) = fun M => fderiv ℝ F M + fderiv ℝ G M :=
    funext fun M => fderiv_add (hF.differentiable M) (hG.differentiable M)
  refine ⟨hF.contDiff.add hG.contDiff, fun M => ?_, fun M => ?_, fun M => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hF.bdd₀ M) (hG.bdd₀ M))
  · rw [hfd]
    exact (norm_add_le _ _).trans (add_le_add (hF.bdd₁ M) (hG.bdd₁ M))
  · have h2 : fderiv ℝ (fun M' => fderiv ℝ F M' + fderiv ℝ G M') M
        = fderiv ℝ (fderiv ℝ F) M + fderiv ℝ (fderiv ℝ G) M :=
      fderiv_add (hF.differentiable_fderiv M) (hG.differentiable_fderiv M)
    rw [hfd, h2]
    exact (norm_add_le (fderiv ℝ (fderiv ℝ F) M) (fderiv ℝ (fderiv ℝ G) M)).trans
      (add_le_add (hF.bdd₂ M) (hG.bdd₂ M))

/-- Finite sums, with the constants summed. -/
theorem bddC2C_sum {ι : Type*} (s : Finset ι) {f : ι → E → V} {c₀ c₁ c₂ : ι → ℝ}
    (h : ∀ i ∈ s, BddC2C (f i) (c₀ i) (c₁ i) (c₂ i)) :
    BddC2C (fun M => ∑ i ∈ s, f i M) (∑ i ∈ s, c₀ i) (∑ i ∈ s, c₁ i) (∑ i ∈ s, c₂ i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (bddC2C_const (E := E) (0 : V)).mono (by simp) le_rfl le_rfl
  | insert i s hi ih =>
    have hmem : ∀ j ∈ s, BddC2C (f j) (c₀ j) (c₁ j) (c₂ j) := fun j hj =>
      h j (Finset.mem_insert_of_mem hj)
    have hsum := bddC2C_add (h i (Finset.mem_insert_self i s)) (ih hmem)
    simpa [Finset.sum_insert hi] using hsum

/-- The existential form `RBM.Gauss.BddC2` with the constants named. -/
theorem BddC2.toBddC2C {F : E → ℂ} (h : BddC2 F) : ∃ C₀ C₁ C₂, BddC2C F C₀ C₁ C₂ := by
  obtain ⟨hcd, ⟨C₀, h0⟩, ⟨C₁, h1⟩, ⟨C₂, h2⟩⟩ := h
  exact ⟨C₀, C₁, C₂, ⟨hcd, h0, h1, h2⟩⟩

theorem bddC2_add {F G : E → ℂ} (hF : BddC2 F) (hG : BddC2 G) :
    BddC2 (fun M => F M + G M) := by
  obtain ⟨a₀, a₁, a₂, hA⟩ := hF.toBddC2C
  obtain ⟨b₀, b₁, b₂, hB⟩ := hG.toBddC2C
  exact (bddC2C_add hA hB).bddC2

theorem bddC2_finset_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℂ}
    (h : ∀ i ∈ s, BddC2 (f i)) : BddC2 (fun M => ∑ i ∈ s, f i M) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (bddC2C_const (E := E) (0 : ℂ)).bddC2
  | insert i s hi ih =>
    have hsum := bddC2_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using hsum

end General

/-! ### Matrix products and the resolvent -/

section Matrices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Matrix multiplication**: the special case of `RBM.Gauss.bddC2C_clm_apply` that the
`List.foldr` of `RBM.gloopProd` needs. -/
theorem bddC2C_matrix_mul {F G : E → Matrix n n ℂ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (hG : BddC2C G b₀ b₁ b₂) :
    BddC2C (fun M => F M * G M) (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) := by
  have hmul : ‖ContinuousLinearMap.mul ℝ (Matrix n n ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_mul_le ℝ (Matrix n n ℂ)
  have hF' : BddC2C (fun M => ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (F M)) a₀ a₁ a₂ :=
    (bddC2C_clm_comp (ContinuousLinearMap.mul ℝ (Matrix n n ℂ)) hF).mono
      (mul_le_of_le_one_left hF.nonneg₀ hmul) (mul_le_of_le_one_left hF.nonneg₁ hmul)
      (mul_le_of_le_one_left hF.nonneg₂ hmul)
  exact bddC2C_clm_apply hF' hG

/-- The trace as a continuous `ℝ`-linear functional. -/
noncomputable def traceCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous (Matrix.traceLinearMap n ℝ ℂ) (Fintype.card n) fun M => by
    show ‖Matrix.trace M‖ ≤ (Fintype.card n : ℝ) * ‖M‖
    rw [Matrix.trace]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : n, ‖Matrix.diag M i‖ ≤ ∑ _i : n, ‖M‖ :=
          Finset.sum_le_sum fun i _ => norm_apply_le_l2_opNorm M i i
      _ = (Fintype.card n : ℝ) * ‖M‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

@[simp] theorem traceCLM_apply (M : Matrix n n ℂ) : traceCLM n M = Matrix.trace M := rfl

theorem norm_traceCLM_le : ‖traceCLM n‖ ≤ (Fintype.card n : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **Fréchet `C²` for the resolvent** (as opposed to the line-wise `iteratedDeriv` bounds of
`RBM1D/Gauss/Generator.lean`): `‖G‖ ≤ η⁻¹`, `‖DG‖ ≤ η⁻²`, `‖D²G‖ ≤ 2η⁻³`, everywhere on the
matrix space, thanks to the Hermitian projection built into `RBM.Gauss.resH`. -/
theorem bddC2C_resH {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|) :
    BddC2C (resH (n := n) z) η⁻¹ (η⁻¹ * η⁻¹) (2 * (η⁻¹ * η⁻¹ * η⁻¹)) :=
  ⟨contDiff_resH hz, norm_resH_le hη hzη, norm_fderiv_resH_le hz hη hzη,
    norm_fderiv2_resH_le hz hη hzη⟩

/-- `G(σ)` at the Hermitian projection is `RBM.Gauss.resH` at `z` or at `z̄`. -/
theorem Gsig_hermCLM_eq (z : ℂ) (σ : Bool) (M : Matrix n n ℂ) :
    Gsig (hermCLM n M) z σ = resH (if σ then z else (starRingEnd ℂ) z) M := by
  rw [Gsig, resH_eq_green]

theorem abs_im_ite_conj (z : ℂ) (σ : Bool) :
    |(if σ then z else (starRingEnd ℂ) z).im| = |z.im| := by
  cases σ <;> simp

theorem im_ite_conj_ne_zero {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
  cases σ <;> simpa using hz

/-- Each `G(σ_i)` factor of the loop is `C²` with the constants `η⁻¹`, `η⁻²`, `2η⁻³`. -/
theorem bddC2C_Gsig_hermCLM {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (σ : Bool) :
    BddC2C (fun M : Matrix n n ℂ => Gsig (hermCLM n M) z σ)
      η⁻¹ (η⁻¹ * η⁻¹) (2 * (η⁻¹ * η⁻¹ * η⁻¹)) := by
  have hfun : (fun M : Matrix n n ℂ => Gsig (hermCLM n M) z σ)
      = resH (if σ then z else (starRingEnd ℂ) z) := funext fun M => Gsig_hermCLM_eq z σ M
  rw [hfun]
  exact bddC2C_resH (im_ite_conj_ne_zero hz σ) hη (by rw [abs_im_ite_conj]; exact hzη)

end Matrices

/-! ### The loop product `∏_i G(σ_i) E_{a_i}` -/

section LoopProd

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **`RBM.gloopProd` read as a function of the matrix**, pre-composed with the Hermitian
projection `RBM.Gauss.hermCLM` so that it is defined on the whole matrix space.  The list is
the zipped index data `σ.zip a` of (2.41). -/
noncomputable def gloopProdFun (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ)
    (l : List (Bool × ZMod L)) (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) :
    Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  l.foldr (fun p X => Gsig (hermCLM _ M) z p.1 * Eblk L W p.2 * X) 1

@[simp] theorem gloopProdFun_nil (z : ℂ) :
    gloopProdFun L W z [] = fun _ => (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) := rfl

theorem gloopProdFun_cons (z : ℂ) (p : Bool × ZMod L) (l : List (Bool × ZMod L)) :
    gloopProdFun L W z (p :: l)
      = fun M => (Gsig (hermCLM _ M) z p.1 * Eblk L W p.2) * gloopProdFun L W z l M := rfl

theorem gloopProdFun_zip (z : ℂ) (I : LoopIdx (ZMod L))
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) :
    gloopProdFun L W z (I.σ.zip I.a) M = gloopProd L W (hermCLM _ M) z I := rfl

theorem norm_Eblk_le_one' (b : ZMod L) : ‖Eblk L W b‖ ≤ 1 := by
  refine (norm_Eblk_le (W := W) b).trans ?_
  have hW : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  rw [inv_le_one_iff₀]
  right
  exact hW

/-- One factor `G(σ) E_b` of the loop product. -/
theorem bddC2C_Gsig_mul_Eblk {z : ℂ} {η B : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) (hBa : η⁻¹ ≤ B) (hBb : η⁻¹ * η⁻¹ ≤ B)
    (hBc : 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ B) (σ : Bool) (b : ZMod L) :
    BddC2C (fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ =>
      Gsig (hermCLM _ M) z σ * Eblk L W b) B B B := by
  have hE : BddC2C (fun _ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ => Eblk L W b) 1 0 0 :=
    (bddC2C_const (E := Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (Eblk L W b)).mono
      (norm_Eblk_le_one' b) le_rfl le_rfl
  have hprod := bddC2C_matrix_mul
    (bddC2C_Gsig_hermCLM (n := ZMod L × Fin W) hz hη hzη σ) hE
  refine hprod.mono ?_ ?_ ?_
  · simpa using hBa
  · simpa using hBb
  · simpa using hBc

/-- **The Leibniz induction over the `List.foldr`.**  With every factor `G(σ_i)E_{a_i}`
bounded by `B` in all three derivatives, the product of `n` of them obeys
`(Bⁿ, n Bⁿ, n² Bⁿ)`. -/
theorem bddC2C_gloopProdFun {z : ℂ} {η B : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) (hBa : η⁻¹ ≤ B) (hBb : η⁻¹ * η⁻¹ ≤ B)
    (hBc : 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ B) (l : List (Bool × ZMod L)) :
    BddC2C (gloopProdFun L W z l) (B ^ l.length)
      ((l.length : ℝ) * B ^ l.length) ((l.length : ℝ) ^ 2 * B ^ l.length) := by
  induction l with
  | nil =>
    rw [gloopProdFun_nil]
    refine (bddC2C_const (E := Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
      (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)).mono ?_ ?_ ?_ <;> simp
  | cons p l ih =>
    rw [gloopProdFun_cons]
    have hfac := bddC2C_Gsig_mul_Eblk (W := W) hz hη hzη hBa hBb hBc p.1 p.2
    refine (bddC2C_matrix_mul hfac ih).mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_) <;>
      · simp only [List.length_cons, pow_succ]
        push_cast
        ring

end LoopProd

/-! ### The loop observable `L_{σ,a}` and its `TestFun` -/

section LoopObs

variable {d : Dims} {N : ℕ}

/-- The three inequalities that make `B = 2(1 + η⁻¹)³` dominate all the per-factor
constants at once. -/
theorem le_two_mul_one_add_inv_cube {η : ℝ} (hη : 0 < η) :
    η⁻¹ ≤ 2 * (1 + η⁻¹) ^ 3 ∧ η⁻¹ * η⁻¹ ≤ 2 * (1 + η⁻¹) ^ 3
      ∧ 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ 2 * (1 + η⁻¹) ^ 3 := by
  have hx : 0 < η⁻¹ := by positivity
  have h2 : (0 : ℝ) < η⁻¹ * η⁻¹ := mul_pos hx hx
  have h3 : (0 : ℝ) < η⁻¹ * η⁻¹ * η⁻¹ := mul_pos h2 hx
  have hexp : 2 * (1 + η⁻¹) ^ 3
      = 2 + 6 * η⁻¹ + 6 * (η⁻¹ * η⁻¹) + 2 * (η⁻¹ * η⁻¹ * η⁻¹) := by ring
  refine ⟨?_, ?_, ?_⟩ <;> rw [hexp] <;> linarith

/-- **The loop `L_{σ,a}` is `C²` in `H`, with deterministic bounds.**  With
`B = 2(1 + η⁻¹)³` and `n` the loop length the constants are `card · Bⁿ`, `card · n Bⁿ`,
`card · n² Bⁿ`, where `card = W L` is the matrix dimension. -/
theorem bddC2C_loopObs {z : ℂ} {η B : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (hBa : η⁻¹ ≤ B) (hBb : η⁻¹ * η⁻¹ ≤ B) (hBc : 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ B)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    BddC2C (loopObs d N z I)
      ((Fintype.card (d.Idx N) : ℝ) * B ^ I.a.length)
      ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length))
      ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2 * B ^ I.a.length)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (by positivity) hBa
  have hBn : (0 : ℝ) ≤ B ^ I.a.length := pow_nonneg hB0 _
  have hlen : (I.σ.zip I.a).length = I.a.length := by
    rw [List.length_zip, hwf, min_self]
  have hfun : loopObs d N z I
      = fun M => traceCLM (d.Idx N) (gloopProdFun (d.L N) (d.W N) z (I.σ.zip I.a) M) := rfl
  have hprod := bddC2C_gloopProdFun (L := d.L N) (W := d.W N) hz hη hzη hBa hBb hBc
    (I.σ.zip I.a)
  rw [hlen] at hprod
  rw [hfun]
  exact (bddC2C_clm_comp (traceCLM (d.Idx N)) hprod).mono
    (mul_le_mul_of_nonneg_right norm_traceCLM_le hBn)
    (mul_le_mul_of_nonneg_right norm_traceCLM_le (by positivity))
    (mul_le_mul_of_nonneg_right norm_traceCLM_le (by positivity))

/-- **`BddC2` for the loop observable** — the closure of `RBM.Gauss.BddC2` under products
that `docs/STATUS.md` records as missing (T72 had only degree-one `φ(G)`). -/
theorem bddC2_loopObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) : BddC2 (loopObs d N z I) := by
  obtain ⟨h1, h2, h3⟩ := le_two_mul_one_add_inv_cube hη
  exact (bddC2C_loopObs (B := 2 * (1 + η⁻¹) ^ 3) hz hη hzη h1 h2 h3 hwf).bddC2

/-- **The `TestFun` gap of T76, closed.**  `RBM.Gauss.testFun_loopObs` had the `bdd₀` field
already; the three remaining ones are exactly what `RBM.Gauss.bddC2_loopObs` supplies. -/
theorem testFun_loopObs_of_im_le {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    TestFun d N (loopObs d N z I) :=
  let h := bddC2_loopObs hz hη hzη hwf
  testFun_loopObs hη hzη hwf hn h.contDiff h.bdd₁ h.bdd₂

/-- `Φ = |L_{σ,a}|^{2p}` is a test function: this is what the moment route of
`RBM1D/Gauss/MomentGronwall.lean` consumes. -/
theorem testFun_momentFun_loopObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (p : ℕ) :
    TestFun d N (momentFun (loopObs d N z I) p) :=
  TestFun.of_bddC2 (bddC2_loopObs hz hη hzη hwf) p

end LoopObs

/-! ### `(U_{s,t,σ} ∘ (L − K))_a` -/

section UkerObs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bddC2_const_mul {F : E → ℂ} (c : ℂ) (h : BddC2 F) : BddC2 (fun M => c * F M) := by
  obtain ⟨a₀, a₁, a₂, hA⟩ := h.toBddC2C
  exact (bddC2C_clm_comp (ContinuousLinearMap.mul ℝ ℂ c) hA).bddC2

theorem bddC2_const (c : ℂ) : BddC2 (fun _ : E => c) := (bddC2C_const c).bddC2

variable {d : Dims} {N : ℕ}

/-- **(5.17) applied to `L − K`**, read as a function of the matrix `H`: the propagator
`U_{s,t,σ}` has `H`-independent coefficients, so this is a finite `ℂ`-linear combination of
loop observables plus a constant. -/
noncomputable def ukerObs (d : Dims) (N : ℕ) (z : ℂ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (s t : ℂ) (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Uker (d.L N) ξ s t (fun b => loopObs d N z ⟨σ, List.ofFn b⟩ M - K b) a

/-- **`(U ∘ (L − K))_a` is `C²` in `H` with deterministic bounds.** -/
theorem bddC2_ukerObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    {m : ℕ} {σ : List Bool} (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) :
    BddC2 (ukerObs d N z σ ξ s t K a) := by
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hfun : ukerObs d N z σ ξ s t K a
      = fun M => ∑ b : LoopArg (d.L N) m,
          ((∏ i, edgeKer (d.L N) (ξ i) s t (a i) (b i)) * loopObs d N z ⟨σ, List.ofFn b⟩ M
            + -((∏ i, edgeKer (d.L N) (ξ i) s t (a i) (b i)) * K b)) := by
    funext M
    rw [ukerObs, Uker]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hfun]
  exact bddC2_finset_sum Finset.univ fun b _ =>
    bddC2_add (bddC2_const_mul _ (bddC2_loopObs hz hη hzη (hwf b))) (bddC2_const _)

/-- The `TestFun` of `RBM1D/Gauss/Generator.lean` for `(U ∘ (L − K))_a`. -/
theorem testFun_ukerObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    {m : ℕ} {σ : List Bool} (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) :
    TestFun d N (ukerObs d N z σ ξ s t K a) :=
  let h := bddC2_ukerObs hz hη hzη hσ ξ s t K a
  ⟨h.contDiff, h.bdd₀, h.bdd₁, h.bdd₂⟩

/-- `Φ = |(U ∘ (L − K))_a|^{2p}` is a test function. -/
theorem testFun_momentFun_ukerObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) {m : ℕ} {σ : List Bool} (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ) :
    TestFun d N (momentFun (ukerObs d N z σ ξ s t K a) p) :=
  TestFun.of_bddC2 (bddC2_ukerObs hz hη hzη hσ ξ s t K a) p

end UkerObs

/-! ### Uniformity in the spectral parameter over a ball (T141)

`RBM1D/Gauss/LoopIto.lean` (T134) needs the bounds of the previous sections *uniformly in
`z` over a ball*, in order to differentiate `∫ L(H_v, z_w)` under the integral sign jointly in
`(v, w)`.  Nothing has to be reproved: every constant in `RBM.Gauss.bddC2C_loopObs` is built
from `η`, the loop length and the dimension — **the spectral parameter enters only through the
hypothesis `η ≤ |z.im|`**.  So a ball of `z`'s carrying a common lower bound on `|Im z|`
carries the same constants, and the lemmas below are one-liners.
-/

section BallUniform

/-- On a ball of radius `r ≤ |z₀.im| / 2` the imaginary part stays at least `|z₀.im| / 2`.
This is the usual way to produce the hypothesis `hball` below. -/
theorem half_abs_im_le_abs_im_of_mem_ball {z₀ z : ℂ} {r : ℝ} (hr : r ≤ |z₀.im| / 2)
    (hz : z ∈ Metric.ball z₀ r) : |z₀.im| / 2 ≤ |z.im| := by
  have hd : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
    simpa using Complex.abs_im_le_norm (z - z₀)
  have hlt : ‖z - z₀‖ < r := by
    rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
  have h1 : |z₀.im| - |z.im| ≤ |z.im - z₀.im| := by
    have := abs_sub_abs_le_abs_sub z₀.im z.im
    rwa [abs_sub_comm z₀.im z.im] at this
  linarith [hd.trans hlt.le]

variable {d : Dims} {N : ℕ}

/-- **The `C²` bounds of `RBM.Gauss.bddC2C_loopObs`, uniformly in `z` over a ball.**  The
constants do not depend on `z` at all: only on `η`, the loop length and the dimension. -/
theorem bddC2C_loopObs_ball {z₀ : ℂ} {r η B : ℝ} (hη : 0 < η)
    (hball : ∀ z ∈ Metric.ball z₀ r, η ≤ |z.im|) (hBa : η⁻¹ ≤ B) (hBb : η⁻¹ * η⁻¹ ≤ B)
    (hBc : 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ B) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    ∀ z ∈ Metric.ball z₀ r,
      BddC2C (loopObs d N z I)
        ((Fintype.card (d.Idx N) : ℝ) * B ^ I.a.length)
        ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length))
        ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2 * B ^ I.a.length)) := fun z hz =>
  bddC2C_loopObs (abs_pos.mp (hη.trans_le (hball z hz))) hη (hball z hz) hBa hBb hBc hwf

/-- `RBM.Gauss.bddC2_loopObs`, uniformly in `z` over a ball. -/
theorem bddC2_loopObs_ball {z₀ : ℂ} {r η : ℝ} (hη : 0 < η)
    (hball : ∀ z ∈ Metric.ball z₀ r, η ≤ |z.im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    ∀ z ∈ Metric.ball z₀ r, BddC2 (loopObs d N z I) := fun z hz =>
  bddC2_loopObs (abs_pos.mp (hη.trans_le (hball z hz))) hη (hball z hz) hwf

/-- `RBM.Gauss.testFun_loopObs_of_im_le`, uniformly in `z` over a ball. -/
theorem testFun_loopObs_ball {z₀ : ℂ} {r η : ℝ} (hη : 0 < η)
    (hball : ∀ z ∈ Metric.ball z₀ r, η ≤ |z.im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ∀ z ∈ Metric.ball z₀ r, TestFun d N (loopObs d N z I) := fun z hz =>
  testFun_loopObs_of_im_le (abs_pos.mp (hη.trans_le (hball z hz))) hη (hball z hz) hwf hn

/-- `RBM.Gauss.testFun_momentFun_loopObs`, uniformly in `z` over a ball. -/
theorem testFun_momentFun_loopObs_ball {z₀ : ℂ} {r η : ℝ} (hη : 0 < η)
    (hball : ∀ z ∈ Metric.ball z₀ r, η ≤ |z.im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (p : ℕ) :
    ∀ z ∈ Metric.ball z₀ r, TestFun d N (momentFun (loopObs d N z I) p) := fun z hz =>
  testFun_momentFun_loopObs (abs_pos.mp (hη.trans_le (hball z hz))) hη (hball z hz) hwf p

/-- `RBM.Gauss.bddC2_ukerObs`, uniformly in `z` over a ball. -/
theorem bddC2_ukerObs_ball {z₀ : ℂ} {r η : ℝ} (hη : 0 < η)
    (hball : ∀ z ∈ Metric.ball z₀ r, η ≤ |z.im|)
    {m : ℕ} {σ : List Bool} (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) :
    ∀ z ∈ Metric.ball z₀ r, BddC2 (ukerObs d N z σ ξ s t K a) := fun z hz =>
  bddC2_ukerObs (abs_pos.mp (hη.trans_le (hball z hz))) hη (hball z hz) hσ ξ s t K a

/-- `RBM.Gauss.testFun_momentFun_ukerObs`, uniformly in `z` over a ball. -/
theorem testFun_momentFun_ukerObs_ball {z₀ : ℂ} {r η : ℝ} (hη : 0 < η)
    (hball : ∀ z ∈ Metric.ball z₀ r, η ≤ |z.im|)
    {m : ℕ} {σ : List Bool} (hσ : σ.length = m) (ξ : Fin m → ℂ) (s t : ℂ)
    (K : LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ) :
    ∀ z ∈ Metric.ball z₀ r, TestFun d N (momentFun (ukerObs d N z σ ξ s t K a) p) := fun z hz =>
  testFun_momentFun_ukerObs (abs_pos.mp (hη.trans_le (hball z hz))) hη (hball z hz) hσ ξ s t K a p

end BallUniform


/-! ### The joint derivative in `(flow time, spectral time)` (T141)

`RBM1D/Gauss/LoopIto.lean` (T134) closes the moving-`z` hierarchy modulo one named input,
`hjoint`: joint Fréchet differentiability of

  `(v, w) ↦ ∫ L_{σ,a}(H_v, z_w) dP`

at `(u, u)`.  Pointwise in `ω` that is `RBM.Gauss.contDiffAt_gloop_flow` of T134; what is
missing is a **dominating bound on the joint derivative, uniform in the pair over a ball**,
which is what this section supplies, ending in
`RBM.Gauss.differentiableAt_integral_gloop_flow`.

## Why the bound is deterministic

`H_v = √v • X` with `X` Gaussian, so the naive bound on `∂_v G` carries `‖X(ω)‖` and the
dominating function would need all moments of `‖X‖`.  It is not needed: `∂_v H_v = (2v)⁻¹ H_v`
and `G H G = G + ζ G²` (`RBM.Gauss.green_mul_self_mul_green`), so

  `‖∂_v G‖ ≤ (2v)⁻¹ (η⁻¹ + ‖z‖ η⁻²)`,   `‖∂_w G‖ ≤ ‖m^{(E)}‖ η⁻²`,

with **no** `ω` in sight (`RBM.Gauss.norm_fderiv_Gsig_flow_le`).  The dominating function is
therefore a constant, and `MeasureTheory.integrable_const` discharges its integrability.

## The carrier

`RBM.Gauss.BddC1On F s C₀ C₁` is the `C¹`-with-bounds class **on a set** — the first-order,
set-localised analogue of `RBM.Gauss.BddC2C` — closed under products
(`RBM.Gauss.bddC1On_clm_apply`, `RBM.Gauss.bddC1On_matrix_mul`), so the `List.foldr` of the
loop is again an induction with constants `(Bⁿ, n Bⁿ)`.

Measurability of `ω ↦ D(v,w) ↦ L` is obtained without any formula for the derivative: a
`ℝ × ℝ`-functional is determined by its two coordinate values (`RBM.Gauss.clm_prod_eq_smulRight`)
and each of those is a pointwise limit of difference quotients of functions that are
*continuous* in `ω` (`RBM.Gauss.measurable_deriv_of_hasDerivAt_zero`).
-/

section JointResolvent

variable {d : Dims} {N : ℕ}

/-- `z_w` read through the charge `σ` is affine in `w`: `ζ_σ(w) = (E + m(σ)) - w m(σ)`. -/
theorem zt_charge_eq (E w : ℝ) (σ : Bool) :
    (if σ then zt E w else (starRingEnd ℂ) (zt E w))
      = ((E : ℂ) + mSigma E σ) + (w : ℝ) • (-(mSigma E σ)) := by
  cases σ <;> simp [zt, mSigma, Complex.real_smul, Complex.conj_ofReal] <;> ring

/-- `(v, w) ↦ H_v = √v • X(ω)`, as a map on the pair. -/
theorem hasFDerivAt_Hflow_pair (ω : Ω d) {v w : ℝ} (hv : v ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ => Hflow d N p.1 ω)
      (((1 / (2 * Real.sqrt v)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight (Xmat d N ω))
      (v, w) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => Real.sqrt p.1)
      ((1 / (2 * Real.sqrt v)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) (v, w) :=
    (Real.hasDerivAt_sqrt hv).comp_hasFDerivAt (v, w) hasFDerivAt_fst
  have h2 := h1.smul_const (Xmat d N ω)
  have hfun : (fun p : ℝ × ℝ => Real.sqrt p.1 • Xmat d N ω)
      = fun p : ℝ × ℝ => Hflow d N p.1 ω := by
    funext p; rw [Hflow_eq_realSmul]
  rwa [hfun] at h2

/-- `(v, w) ↦ ζ_σ(w)`, as a map on the pair; its derivative is `-m(σ)` in the second slot. -/
theorem hasFDerivAt_zChg_pair (E : ℝ) (σ : Bool) (v w : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => (if σ then zt E p.2 else (starRingEnd ℂ) (zt E p.2)))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(mSigma E σ))) (v, w) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => (p.2 : ℝ) • (-(mSigma E σ)))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(mSigma E σ))) (v, w) :=
    hasFDerivAt_snd.smul_const _
  have h2 := h1.const_add ((E : ℂ) + mSigma E σ)
  have hfun : (fun p : ℝ × ℝ => ((E : ℂ) + mSigma E σ) + (p.2 : ℝ) • (-(mSigma E σ)))
      = fun p : ℝ × ℝ => (if σ then zt E p.2 else (starRingEnd ℂ) (zt E p.2)) := by
    funext p; rw [zt_charge_eq]
  rwa [hfun] at h2

/-- The joint Fréchet derivative of one resolvent factor along the flow. -/
theorem hasFDerivAt_Gsig_flow (ω : Ω d) {E v w : ℝ} (hv : 0 < v)
    (hz : (zt E w).im ≠ 0) (σ : Bool) :
    HasFDerivAt (fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt E p.2) σ)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (d.Idx N) (d.Idx N) ℂ)
            (Gsig (Hflow d N v ω) (zt E w) σ) (Gsig (Hflow d N v ω) (zt E w) σ))).comp
        ((((1 / (2 * Real.sqrt v)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight (Xmat d N ω))
          - ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(mSigma E σ))).smulRight
              (1 : Matrix (d.Idx N) (d.Idx N) ℂ)))
      (v, w) := by
  set ζ : ℝ → ℂ := fun s => if σ then zt E s else (starRingEnd ℂ) (zt E s) with hζdef
  have hA : HasFDerivAt
      (fun p : ℝ × ℝ => Hflow d N p.1 ω - ζ p.2 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
      ((((1 / (2 * Real.sqrt v)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight (Xmat d N ω))
        - ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(mSigma E σ))).smulRight
            (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) (v, w) :=
    (hasFDerivAt_Hflow_pair ω hv.ne').sub
      ((hasFDerivAt_zChg_pair E σ v w).smul_const (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
  obtain ⟨u, hu⟩ : ∃ u : (Matrix (d.Idx N) (d.Idx N) ℂ)ˣ,
      (u : Matrix (d.Idx N) (d.Idx N) ℂ)
        = Hflow d N v ω - ζ w • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) :=
    ⟨(isUnit_sub_smul_one_of_im_ne_zero (Hflow_isHermitian d N v ω)
      (im_ite_conj_ne_zero hz σ)).unit, IsUnit.unit_spec _⟩
  have hinv : ((u⁻¹ : (Matrix (d.Idx N) (d.Idx N) ℂ)ˣ) : Matrix (d.Idx N) (d.Idx N) ℂ)
      = Gsig (Hflow d N v ω) (zt E w) σ := by
    rw [Gsig, green, Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix (d.Idx N) (d.Idx N) ℂ) ↑u⁻¹) ↑u⁻¹))
      ((fun p : ℝ × ℝ => Hflow d N p.1 ω - ζ p.2 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) (v, w)) := by
    show HasFDerivAt _ _ (Hflow d N v ω - ζ w • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have key := hF.comp (v, w) hA
  rw [hinv] at key
  have hcomp : (Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
      ∘ (fun p : ℝ × ℝ => Hflow d N p.1 ω - ζ p.2 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
      = fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt E p.2) σ := by
    funext p
    show Ring.inverse _ = green (Hflow d N p.1 ω) (ζ p.2)
    rw [green, Matrix.nonsing_inv_eq_ringInverse]
  rw [hcomp] at key
  exact key



/-- **`G H G = G + ζ G²`.**  This is what makes the flow derivative deterministic: the
direction `∂_v H_v = (2v)⁻¹ H_v` is the matrix itself, and the resolvent absorbs it. -/
theorem green_mul_self_mul_green {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) {ζ : ℂ} (hU : IsUnit (M - ζ • (1 : Matrix m m ℂ))) :
    green M ζ * M * green M ζ = green M ζ + ζ • (green M ζ * green M ζ) := by
  have hdet : IsUnit (M - ζ • (1 : Matrix m m ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have h1 : green M ζ * (M - ζ • (1 : Matrix m m ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have h2 : green M ζ * (M - ζ • (1 : Matrix m m ℂ)) * green M ζ
      = green M ζ * M * green M ζ - ζ • (green M ζ * green M ζ) := by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc]
  rw [h1, one_mul] at h2
  exact sub_eq_iff_eq_add.mp h2.symm

/-- The two charges of `m^{(E)}` have the same modulus. -/
theorem norm_mSigma_eq (E : ℝ) (σ : Bool) : ‖mSigma E σ‖ = ‖mE E‖ := by
  cases σ <;> simp [mSigma]

/-- Conjugation does not change the modulus, so neither does the charge. -/
theorem norm_ite_conj (z : ℂ) (σ : Bool) :
    ‖(if σ then z else (starRingEnd ℂ) z)‖ = ‖z‖ := by cases σ <;> simp

/-- **The joint derivative of a resolvent factor is bounded deterministically.**  The flow
direction is `∂_v H_v = (2v)⁻¹ H_v`, and `G H G = G + ζ G²`, so the Gaussian matrix `X` does
**not** appear in the bound. -/
theorem norm_fderiv_Gsig_flow_le (ω : Ω d) {E v w η : ℝ} (hv : 0 < v) (hη : 0 < η)
    (hzη : η ≤ |(zt E w).im|) (σ : Bool) :
    ‖fderiv ℝ (fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt E p.2) σ) (v, w)‖
      ≤ (2 * v)⁻¹ * (η⁻¹ + ‖zt E w‖ * (η⁻¹ * η⁻¹)) + ‖mE E‖ * (η⁻¹ * η⁻¹) := by
  have hz : (zt E w).im ≠ 0 := abs_pos.mp (hη.trans_le hzη)
  have hsq : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hηi : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
  set ζ : ℂ := if σ then zt E w else (starRingEnd ℂ) (zt E w) with hζ
  set G : Matrix (d.Idx N) (d.Idx N) ℂ := Gsig (Hflow d N v ω) (zt E w) σ with hGdef
  have hGgreen : G = green (Hflow d N v ω) ζ := rfl
  have hζim : η ≤ |ζ.im| := by rw [hζ, abs_im_ite_conj]; exact hzη
  have hGn : ‖G‖ ≤ η⁻¹ := by
    rw [hGgreen]; exact norm_green_le (Hflow_isHermitian d N v ω) hη hζim
  have hG2 : ‖G * G‖ ≤ η⁻¹ * η⁻¹ :=
    (norm_mul_le _ _).trans (mul_le_mul hGn hGn (norm_nonneg _) hηi.le)
  have hU : IsUnit (Hflow d N v ω - ζ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (Hflow_isHermitian d N v ω) (im_ite_conj_ne_zero hz σ)
  have hX : Xmat d N ω = (Real.sqrt v)⁻¹ • Hflow d N v ω := by
    rw [Hflow_eq_realSmul, inv_smul_smul₀ hsq.ne']
  have hGXG : G * Xmat d N ω * G = (Real.sqrt v)⁻¹ • (G + ζ • (G * G)) := by
    rw [hX, mul_smul_comm, smul_mul_assoc, hGgreen, green_mul_self_mul_green _ hU]
  set A : ℝ := η⁻¹ + ‖zt E w‖ * (η⁻¹ * η⁻¹) with hA
  have hA0 : 0 ≤ A := by
    have := norm_nonneg (zt E w)
    have h2 : (0:ℝ) ≤ η⁻¹ * η⁻¹ := mul_nonneg hηi.le hηi.le
    exact add_nonneg hηi.le (mul_nonneg this h2)
  have hGXGn : ‖G * Xmat d N ω * G‖ ≤ (Real.sqrt v)⁻¹ * A := by
    rw [hGXG, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hsq.le)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hsq.le)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hζ, norm_ite_conj]
    exact add_le_add hGn (mul_le_mul_of_nonneg_left hG2 (norm_nonneg _))
  have hmnn : (0:ℝ) ≤ ‖mE E‖ := norm_nonneg _
  have hcnn : 0 ≤ (2 * v)⁻¹ * A + ‖mE E‖ * (η⁻¹ * η⁻¹) :=
    add_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith)) hA0)
      (mul_nonneg hmnn (mul_nonneg hηi.le hηi.le))
  refine ContinuousLinearMap.opNorm_le_bound _ hcnn fun q => ?_
  have hval : (fderiv ℝ (fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt E p.2) σ) (v, w)) q
      = -(((1 / (2 * Real.sqrt v)) * q.1) • (G * Xmat d N ω * G))
        + (q.2 • (-(mSigma E σ))) • (G * G) := by
    rw [(hasFDerivAt_Gsig_flow (N := N) ω hv hz σ).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.neg_apply,
      _root_.sub_apply, ContinuousLinearMap.smulRight_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul]
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, mul_one, smul_mul_assoc]
    abel
  rw [hval]
  have e1 : ‖-(((1 / (2 * Real.sqrt v)) * q.1) • (G * Xmat d N ω * G))‖
      ≤ (1 / (2 * Real.sqrt v)) * |q.1| * ((Real.sqrt v)⁻¹ * A) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.sqrt v))]
    exact mul_le_mul_of_nonneg_left hGXGn (by positivity)
  have e2 : ‖(q.2 • (-(mSigma E σ))) • (G * G)‖ ≤ (|q.2| * ‖mE E‖) * (η⁻¹ * η⁻¹) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, norm_neg, norm_mSigma_eq]
    exact mul_le_mul_of_nonneg_left hG2 (by positivity)
  have hsv : (1 / (2 * Real.sqrt v)) * (Real.sqrt v)⁻¹ = (2 * v)⁻¹ := by
    have hvv : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
    rw [one_div, ← mul_inv, mul_assoc, hvv]
  have hq1 : |q.1| ≤ ‖q‖ := norm_fst_le q
  have hq2 : |q.2| ≤ ‖q‖ := norm_snd_le q
  have hstep : (1 / (2 * Real.sqrt v)) * |q.1| * ((Real.sqrt v)⁻¹ * A)
      + (|q.2| * ‖mE E‖) * (η⁻¹ * η⁻¹)
      ≤ ((2 * v)⁻¹ * A + ‖mE E‖ * (η⁻¹ * η⁻¹)) * ‖q‖ := by
    have hre : (1 / (2 * Real.sqrt v)) * |q.1| * ((Real.sqrt v)⁻¹ * A)
        = ((2 * v)⁻¹ * A) * |q.1| := by
      rw [← hsv]; ring
    rw [hre]
    have h1 : ((2 * v)⁻¹ * A) * |q.1| ≤ ((2 * v)⁻¹ * A) * ‖q‖ :=
      mul_le_mul_of_nonneg_left hq1 (mul_nonneg (inv_nonneg.mpr (by linarith)) hA0)
    have h2 : (|q.2| * ‖mE E‖) * (η⁻¹ * η⁻¹) ≤ (‖mE E‖ * (η⁻¹ * η⁻¹)) * ‖q‖ := by
      have := mul_le_mul_of_nonneg_right hq2 (mul_nonneg hmnn (mul_nonneg hηi.le hηi.le))
      calc (|q.2| * ‖mE E‖) * (η⁻¹ * η⁻¹) = |q.2| * (‖mE E‖ * (η⁻¹ * η⁻¹)) := by ring
        _ ≤ ‖q‖ * (‖mE E‖ * (η⁻¹ * η⁻¹)) := this
        _ = (‖mE E‖ * (η⁻¹ * η⁻¹)) * ‖q‖ := by ring
    linarith
  exact ((norm_add_le _ _).trans (add_le_add e1 e2)).trans hstep


end JointResolvent

section C1On

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- **`RBM.Gauss.BddC2C` at first order and localised to a set**: `F` is differentiable on
`s` with `‖F‖ ≤ C₀` and `‖DF‖ ≤ C₁` there.  This is the exact shape
`hasFDerivAt_integral_of_dominated_of_fderiv_le` consumes. -/
structure BddC1On (F : E → V) (s : Set E) (C₀ C₁ : ℝ) : Prop where
  /-- `F` is differentiable at every point of `s`. -/
  diff : ∀ x ∈ s, DifferentiableAt ℝ F x
  /-- `‖F x‖ ≤ C₀` on `s`. -/
  bdd₀ : ∀ x ∈ s, ‖F x‖ ≤ C₀
  /-- `‖DF x‖ ≤ C₁` on `s`. -/
  bdd₁ : ∀ x ∈ s, ‖fderiv ℝ F x‖ ≤ C₁

namespace BddC1On

variable {F : E → V} {s : Set E} {C₀ C₁ D₀ D₁ : ℝ}

theorem mono (h : BddC1On F s C₀ C₁) (h₀ : C₀ ≤ D₀) (h₁ : C₁ ≤ D₁) : BddC1On F s D₀ D₁ :=
  ⟨h.diff, fun x hx => (h.bdd₀ x hx).trans h₀, fun x hx => (h.bdd₁ x hx).trans h₁⟩

theorem norm_fderiv_apply_le (h : BddC1On F s C₀ C₁) {x : E} (hx : x ∈ s) (A : E) :
    ‖fderiv ℝ F x A‖ ≤ C₁ * ‖A‖ :=
  ((fderiv ℝ F x).le_opNorm A).trans
    (mul_le_mul_of_nonneg_right (h.bdd₁ x hx) (norm_nonneg A))

end BddC1On

/-- A constant map. -/
theorem bddC1On_const (v : V) (s : Set E) : BddC1On (fun _ : E => v) s ‖v‖ 0 :=
  ⟨fun _ _ => differentiableAt_const v, fun _ _ => le_rfl, fun x _ => by
    rw [show fderiv ℝ (fun _ : E => v) x = 0 from by simp]
    exact le_of_eq ContinuousLinearMap.opNorm_zero⟩

/-- Post-composition with a continuous linear map. -/
theorem bddC1On_clm_comp (φ : V →L[ℝ] V') {F : E → V} {s : Set E} {C₀ C₁ : ℝ}
    (h : BddC1On F s C₀ C₁) :
    BddC1On (fun x => φ (F x)) s (‖φ‖ * C₀) (‖φ‖ * C₁) := by
  refine ⟨fun x hx => φ.differentiableAt.comp x (h.diff x hx), fun x hx => ?_, fun x hx => ?_⟩
  · exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.bdd₀ x hx) (norm_nonneg _))
  · have hfd : fderiv ℝ (fun y => φ (F y)) x = φ.comp (fderiv ℝ F x) :=
      (φ.hasFDerivAt.comp x (h.diff x hx).hasFDerivAt).fderiv
    rw [hfd]
    exact (φ.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (h.bdd₁ x hx) (norm_nonneg _))

/-- The Leibniz rule for the CLM pairing, at a single point. -/
theorem fderiv_clm_apply_apply_of_differentiableAt {F : E → (V →L[ℝ] V')} {G : E → V} {x : E}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (A : E) :
    fderiv ℝ (fun y => F y (G y)) x A = F x (fderiv ℝ G x A) + (fderiv ℝ F x A) (G x) := by
  rw [fderiv_clm_apply hF hG]
  rfl

/-- **`BddC1On` is closed under products**, with the first-order Leibniz constants. -/
theorem bddC1On_clm_apply {F : E → (V →L[ℝ] V')} {G : E → V} {s : Set E} {a₀ a₁ b₀ b₁ : ℝ}
    (hF : BddC1On F s a₀ a₁) (hG : BddC1On G s b₀ b₁) :
    BddC1On (fun x => F x (G x)) s (a₀ * b₀) (a₀ * b₁ + a₁ * b₀) := by
  refine ⟨fun x hx => (hF.diff x hx).clm_apply (hG.diff x hx), fun x hx => ?_, fun x hx => ?_⟩
  · have ha0 : 0 ≤ a₀ := (norm_nonneg (F x)).trans (hF.bdd₀ x hx)
    exact ((F x).le_opNorm _).trans
      (mul_le_mul (hF.bdd₀ x hx) (hG.bdd₀ x hx) (norm_nonneg _) ha0)
  · have ha0 : 0 ≤ a₀ := (norm_nonneg (F x)).trans (hF.bdd₀ x hx)
    have ha1 : 0 ≤ a₁ := (norm_nonneg (fderiv ℝ F x)).trans (hF.bdd₁ x hx)
    have hb0 : 0 ≤ b₀ := (norm_nonneg (G x)).trans (hG.bdd₀ x hx)
    have hb1 : 0 ≤ b₁ := (norm_nonneg (fderiv ℝ G x)).trans (hG.bdd₁ x hx)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    rw [fderiv_clm_apply_apply_of_differentiableAt (hF.diff x hx) (hG.diff x hx) A]
    have e1 : ‖F x (fderiv ℝ G x A)‖ ≤ a₀ * (b₁ * ‖A‖) :=
      ((F x).le_opNorm _).trans
        (mul_le_mul (hF.bdd₀ x hx) (hG.norm_fderiv_apply_le hx A) (norm_nonneg _) ha0)
    have e2 : ‖(fderiv ℝ F x A) (G x)‖ ≤ (a₁ * ‖A‖) * b₀ :=
      ((fderiv ℝ F x A).le_opNorm _).trans
        (mul_le_mul (hF.norm_fderiv_apply_le hx A) (hG.bdd₀ x hx) (norm_nonneg _)
          (by positivity))
    calc ‖F x (fderiv ℝ G x A) + (fderiv ℝ F x A) (G x)‖
        ≤ ‖F x (fderiv ℝ G x A)‖ + ‖(fderiv ℝ F x A) (G x)‖ := norm_add_le _ _
      _ ≤ a₀ * (b₁ * ‖A‖) + (a₁ * ‖A‖) * b₀ := add_le_add e1 e2
      _ = (a₀ * b₁ + a₁ * b₀) * ‖A‖ := by ring

end C1On

section MatMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix multiplication: the instance of `RBM.Gauss.bddC1On_clm_apply` the `List.foldr`
of the loop needs. -/
theorem bddC1On_matrix_mul {F G : E → Matrix n n ℂ} {s : Set E} {a₀ a₁ b₀ b₁ : ℝ}
    (hF : BddC1On F s a₀ a₁) (hG : BddC1On G s b₀ b₁) :
    BddC1On (fun x => F x * G x) s (a₀ * b₀) (a₀ * b₁ + a₁ * b₀) := by
  have hmul : ‖ContinuousLinearMap.mul ℝ (Matrix n n ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_mul_le ℝ (Matrix n n ℂ)
  have hF' : BddC1On (fun x => ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (F x)) s a₀ a₁ := by
    rcases Set.eq_empty_or_nonempty s with hs | ⟨x₀, hx₀⟩
    · subst hs; exact ⟨by simp, by simp, by simp⟩
    · have ha0 : 0 ≤ a₀ := (norm_nonneg (F x₀)).trans (hF.bdd₀ x₀ hx₀)
      have ha1 : 0 ≤ a₁ := (norm_nonneg (fderiv ℝ F x₀)).trans (hF.bdd₁ x₀ hx₀)
      exact (bddC1On_clm_comp (ContinuousLinearMap.mul ℝ (Matrix n n ℂ)) hF).mono
        (mul_le_of_le_one_left ha0 hmul) (mul_le_of_le_one_left ha1 hmul)
  exact bddC1On_clm_apply hF' hG

end MatMul

section GloopFlow

variable {d : Dims} {N : ℕ}

/-- One resolvent factor, uniformly on a set of pairs. -/
theorem bddC1On_Gsig_flow (ω : Ω d) {Ev η B : ℝ} {s : Set (ℝ × ℝ)}
    (hη : 0 < η) (hpos : ∀ p ∈ s, 0 < p.1) (hzs : ∀ p ∈ s, η ≤ |(zt Ev p.2).im|)
    (hBa : η⁻¹ ≤ B)
    (hBb : ∀ p ∈ s,
      (2 * p.1)⁻¹ * (η⁻¹ + ‖zt Ev p.2‖ * (η⁻¹ * η⁻¹)) + ‖mE Ev‖ * (η⁻¹ * η⁻¹) ≤ B)
    (σ : Bool) :
    BddC1On (fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt Ev p.2) σ) s B B := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨v, w⟩ := p
    exact (hasFDerivAt_Gsig_flow ω (hpos _ hp)
      (abs_pos.mp (hη.trans_le (hzs _ hp))) σ).differentiableAt
  · refine le_trans ?_ hBa
    rw [Gsig]
    exact norm_green_le (Hflow_isHermitian d N p.1 ω) hη
      (by rw [abs_im_ite_conj]; exact hzs p hp)
  · obtain ⟨v, w⟩ := p
    exact (norm_fderiv_Gsig_flow_le ω (hpos _ hp) hη (hzs _ hp) σ).trans (hBb _ hp)

/-- The loop product along the flow, as a function of `(v, w)`. -/
noncomputable def gloopProdFlow (d : Dims) (N : ℕ) (ω : Ω d) (Ev : ℝ)
    (l : List (Bool × ZMod (d.L N))) (p : ℝ × ℝ) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  l.foldr (fun c X => Gsig (Hflow d N p.1 ω) (zt Ev p.2) c.1 * Eblk (d.L N) (d.W N) c.2 * X) 1

/-- The zipped index data of (2.41) recovers `RBM.gloopProd`. -/
theorem gloopProdFlow_zip (ω : Ω d) (Ev : ℝ) (I : LoopIdx (ZMod (d.L N))) (p : ℝ × ℝ) :
    gloopProdFlow d N ω Ev (I.σ.zip I.a) p
      = gloopProd (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I := rfl

/-- The loop is the trace of the product, through the bounded functional `traceCLM`. -/
theorem gloop_eq_traceCLM_gloopProdFlow (ω : Ω d) (Ev : ℝ) (I : LoopIdx (ZMod (d.L N)))
    (p : ℝ × ℝ) :
    gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I
      = traceCLM (d.Idx N) (gloopProdFlow d N ω Ev (I.σ.zip I.a) p) := rfl

/-- **The Leibniz induction over the `List.foldr`**, first order: `n` factors bounded by `B`
in value and derivative give `(Bⁿ, n Bⁿ)`. -/
theorem bddC1On_gloopProdFlow (ω : Ω d) {Ev η B : ℝ} {s : Set (ℝ × ℝ)}
    (hη : 0 < η) (hpos : ∀ p ∈ s, 0 < p.1) (hzs : ∀ p ∈ s, η ≤ |(zt Ev p.2).im|)
    (hBa : η⁻¹ ≤ B)
    (hBb : ∀ p ∈ s,
      (2 * p.1)⁻¹ * (η⁻¹ + ‖zt Ev p.2‖ * (η⁻¹ * η⁻¹)) + ‖mE Ev‖ * (η⁻¹ * η⁻¹) ≤ B)
    (l : List (Bool × ZMod (d.L N))) :
    BddC1On (gloopProdFlow d N ω Ev l) s (B ^ l.length) ((l.length : ℝ) * B ^ l.length) := by
  induction l with
  | nil =>
      have h := bddC1On_const (E := ℝ × ℝ)
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ) s
      refine h.mono ?_ ?_ <;> simp
  | cons c l ih =>
      have hE : BddC1On (fun _ : ℝ × ℝ => Eblk (d.L N) (d.W N) c.2) s 1 0 :=
        (bddC1On_const (E := ℝ × ℝ) (Eblk (d.L N) (d.W N) c.2) s).mono
          (norm_Eblk_le_one' c.2) le_rfl
      have hfac : BddC1On
          (fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt Ev p.2) c.1
            * Eblk (d.L N) (d.W N) c.2) s B B := by
        refine (bddC1On_matrix_mul
          (bddC1On_Gsig_flow (N := N) ω hη hpos hzs hBa hBb c.1) hE).mono ?_ ?_ <;> simp
      have hstep := bddC1On_matrix_mul hfac ih
      refine hstep.mono (le_of_eq ?_) (le_of_eq ?_) <;>
        · simp only [List.length_cons, pow_succ]
          push_cast
          ring

/-- **The loop `L_{σ,a}(H_v, z_w)` is `C¹` in the pair with a deterministic bound**, uniform
over any set of pairs on which the flow time is positive and `|Im z_w| ≥ η`.  This is T133's
`bdd₁` strengthened to be uniform in the spectral parameter, which is what T134 asked for. -/
theorem bddC1On_gloop_flow (ω : Ω d) {Ev η B : ℝ} {s : Set (ℝ × ℝ)}
    (hη : 0 < η) (hpos : ∀ p ∈ s, 0 < p.1) (hzs : ∀ p ∈ s, η ≤ |(zt Ev p.2).im|)
    (hBa : η⁻¹ ≤ B)
    (hBb : ∀ p ∈ s,
      (2 * p.1)⁻¹ * (η⁻¹ + ‖zt Ev p.2‖ * (η⁻¹ * η⁻¹)) + ‖mE Ev‖ * (η⁻¹ * η⁻¹) ≤ B)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    BddC1On (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I) s
      ((Fintype.card (d.Idx N) : ℝ) * B ^ I.a.length)
      ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (by positivity) hBa
  have hBn : (0 : ℝ) ≤ B ^ I.a.length := pow_nonneg hB0 _
  have hlen : (I.σ.zip I.a).length = I.a.length := by
    rw [List.length_zip, hwf, min_self]
  have hprod := bddC1On_gloopProdFlow (N := N) ω hη hpos hzs hBa hBb (I.σ.zip I.a)
  rw [hlen] at hprod
  have hfun : (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
      = fun p : ℝ × ℝ => traceCLM (d.Idx N) (gloopProdFlow d N ω Ev (I.σ.zip I.a) p) := rfl
  rw [hfun]
  exact (bddC1On_clm_comp (traceCLM (d.Idx N)) hprod).mono
    (mul_le_mul_of_nonneg_right norm_traceCLM_le hBn)
    (mul_le_mul_of_nonneg_right norm_traceCLM_le (by positivity))

end GloopFlow
/-- A continuous linear functional on `ℝ × ℝ` is determined by its two coordinate values. -/
theorem clm_prod_eq_smulRight {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : (ℝ × ℝ) →L[ℝ] V) :
    T = (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (T (1, 0))
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (T (0, 1)) := by
  refine ContinuousLinearMap.ext fun q => ?_
  have hq : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_ <;> simp
  have hT : T q = q.1 • T (1, 0) + q.2 • T (0, 1) := by
    conv_lhs => rw [hq]
    rw [map_add, map_smul, map_smul]
  rw [hT]
  simp

/-- Measurability of a parametrised derivative, from difference quotients. -/
theorem measurable_deriv_of_hasDerivAt_zero {α : Type*} [MeasurableSpace α]
    {f : α → ℝ → ℂ} {L : α → ℂ} {δ : ℕ → ℝ}
    (hδ0 : ∀ n, δ n ≠ 0) (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hm : ∀ n, Measurable fun a => f a (δ n)) (hm0 : Measurable fun a => f a 0)
    (hd : ∀ a, HasDerivAt (f a) (L a) 0) : Measurable L := by
  have hmeas : ∀ n, Measurable fun a => (δ n)⁻¹ • (f a (δ n) - f a 0) := by
    intro n
    exact ((hm n).sub hm0).const_smul ((δ n)⁻¹ : ℝ)
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr fun a => ?_)
  have hslope : Filter.Tendsto (slope (f a) 0) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (L a)) :=
    hasDerivAt_iff_tendsto_slope.mp (hd a)
  have hδ' : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within δ hδ
      (Filter.Eventually.of_forall hδ0)
  refine (hslope.comp hδ').congr fun n => ?_
  show slope (f a) 0 (δ n) = (δ n)⁻¹ • (f a (δ n) - f a 0)
  simp [slope]

section JointIntegral

open MeasureTheory

variable {d : Dims} {N : ℕ}

/-- A crude modulus bound for `z_w`, enough to make the constant above uniform on a ball. -/
theorem norm_zt_le (Ev w : ℝ) : ‖zt Ev w‖ ≤ |Ev| + (1 + |w|) * ‖mE Ev‖ := by
  have hzt : zt Ev w = (Ev : ℂ) + ((1 - w : ℝ) : ℂ) * mE Ev := by
    rw [zt]; push_cast; ring
  rw [hzt]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |1 - w| ≤ 1 + |w| := (abs_sub _ _).trans (by simp)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

/-- **`hjoint` of `RBM1D/Gauss/LoopIto.lean` (T134), discharged.**

`(v, w) ↦ E[L_{σ,a}(H_v, z_w)]` is differentiable at `(u, u)`, hence
`RBM.Gauss.hasDerivAt_integral_gloop_hierarchy_movingZ` and
`RBM.Gauss.hasDerivAt_sample_ELval_hierarchy` take `(this).hasFDerivAt` for their `hjoint`
and acquire no new hypothesis.  Differentiation under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) with the deterministic constant of
`RBM.Gauss.bddC1On_gloop_flow` as the dominating function; the hypotheses `hu`, `hη`, `hε`,
`hball` are exactly the ones those two theorems already carry. -/
theorem differentiableAt_integral_gloop_flow (d : Dims) (N : ℕ) {Ev u η ε : ℝ}
    (hu : 0 < u) (hη : 0 < η) (hε : 0 < ε)
    (hball : ∀ t ∈ Metric.ball u ε, η ≤ |(zt Ev t).im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ =>
      ∫ ω, gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I ∂(P d)) (u, u) := by
  classical
  have hηi : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
  set r : ℝ := min ε (u / 2) with hrdef
  have hr0 : 0 < r := lt_min hε (by linarith)
  have hre : r ≤ ε := min_le_left _ _
  have hru : r ≤ u / 2 := min_le_right _ _
  set s : Set (ℝ × ℝ) := Metric.ball ((u, u) : ℝ × ℝ) r with hsdef
  have hmem1 : ∀ p ∈ s, |p.1 - u| < r := by
    intro p hp
    have h := Metric.mem_ball.mp hp
    rw [Prod.dist_eq, max_lt_iff] at h
    simpa [Real.dist_eq] using h.1
  have hmem2 : ∀ p ∈ s, |p.2 - u| < r := by
    intro p hp
    have h := Metric.mem_ball.mp hp
    rw [Prod.dist_eq, max_lt_iff] at h
    simpa [Real.dist_eq] using h.2
  have hpos : ∀ p ∈ s, 0 < p.1 := by
    intro p hp
    have h := (abs_lt.mp (hmem1 p hp)).1
    linarith
  have hhalf : ∀ p ∈ s, u ≤ 2 * p.1 := by
    intro p hp
    have h := (abs_lt.mp (hmem1 p hp)).1
    linarith
  have hzs : ∀ p ∈ s, η ≤ |(zt Ev p.2).im| := by
    intro p hp
    refine hball p.2 ?_
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_lt_of_le (hmem2 p hp) hre
  -- the uniform constant
  set Z : ℝ := |Ev| + (1 + (u + r)) * ‖mE Ev‖ with hZdef
  have hZle : ∀ p ∈ s, ‖zt Ev p.2‖ ≤ Z := by
    intro p hp
    refine (norm_zt_le Ev p.2).trans ?_
    have h := (abs_lt.mp (hmem2 p hp))
    have habs : |p.2| ≤ u + r := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  set B : ℝ := max η⁻¹ (u⁻¹ * (η⁻¹ + Z * (η⁻¹ * η⁻¹)) + ‖mE Ev‖ * (η⁻¹ * η⁻¹)) with hBdef
  have hBa : η⁻¹ ≤ B := le_max_left _ _
  have hBb : ∀ p ∈ s,
      (2 * p.1)⁻¹ * (η⁻¹ + ‖zt Ev p.2‖ * (η⁻¹ * η⁻¹)) + ‖mE Ev‖ * (η⁻¹ * η⁻¹) ≤ B := by
    intro p hp
    refine le_trans (add_le_add ?_ le_rfl) (le_max_right _ _)
    have h2 : (2 * p.1)⁻¹ ≤ u⁻¹ := by
      exact inv_anti₀ hu (hhalf p hp)
    have h3 : η⁻¹ + ‖zt Ev p.2‖ * (η⁻¹ * η⁻¹) ≤ η⁻¹ + Z * (η⁻¹ * η⁻¹) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (hZle p hp)
        (mul_nonneg hηi.le hηi.le))
    have h4 : (0 : ℝ) ≤ η⁻¹ + ‖zt Ev p.2‖ * (η⁻¹ * η⁻¹) :=
      add_nonneg hηi.le (mul_nonneg (norm_nonneg _) (mul_nonneg hηi.le hηi.le))
    exact mul_le_mul h2 h3 h4 (inv_nonneg.mpr hu.le)
  have hC1 : ∀ ω : Ω d,
      BddC1On (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I) s
        ((Fintype.card (d.Idx N) : ℝ) * B ^ I.a.length)
        ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length)) := fun ω =>
    bddC1On_gloop_flow (N := N) ω hη hpos hzs hBa hBb hwf
  have hcenter : ((u, u) : ℝ × ℝ) ∈ s := Metric.mem_ball_self hr0
  have hzu : (zt Ev u).im ≠ 0 := abs_pos.mp (hη.trans_le (hzs _ hcenter))
  -- the difference-quotient sequence
  set δ : ℕ → ℝ := fun n => (r / 2) * (1 / ((n : ℝ) + 1)) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => mul_pos (by linarith) (by positivity)
  have hδ0 : ∀ n, δ n ≠ 0 := fun n => (hδpos n).ne'
  have hδlt : ∀ n, δ n < r := by
    intro n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      simp
    calc δ n ≤ (r / 2) * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ < r := by linarith
  have hδt : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / 2)
    rw [mul_zero] at h
    exact h
  -- measurability of the two directional derivatives
  have hA : Measurable fun ω : Ω d =>
      fderiv ℝ (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
        (u, u) (1, 0) := by
    refine measurable_deriv_of_hasDerivAt_zero
      (f := fun (ω : Ω d) (t : ℝ) =>
        gloop (d.L N) (d.W N) (Hflow d N (u + t) ω) (zt Ev u) I)
      (δ := δ) hδ0 hδt (fun n => (continuous_gloop_Hflow d N (u + δ n) hzu I).measurable)
      (continuous_gloop_Hflow d N (u + 0) hzu I).measurable (fun ω => ?_)
    have hd : HasDerivAt (fun t : ℝ => ((u, u) : ℝ × ℝ) + t • ((1 : ℝ), (0 : ℝ)))
        ((1 : ℝ), (0 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((1 : ℝ), (0 : ℝ))).const_add
        ((u, u) : ℝ × ℝ)
    have hfd : HasFDerivAt
        (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
        (fderiv ℝ (fun p : ℝ × ℝ =>
          gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I) (u, u))
        (((u, u) : ℝ × ℝ) + (0 : ℝ) • ((1 : ℝ), (0 : ℝ))) := by
      simpa using ((hC1 ω).diff _ hcenter).hasFDerivAt
    have hco := hfd.comp_hasDerivAt (0 : ℝ) hd
    rw [Function.comp_def] at hco
    exact hco.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp)
  have hB : Measurable fun ω : Ω d =>
      fderiv ℝ (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
        (u, u) (0, 1) := by
    have hzn : ∀ n, (zt Ev (u + δ n)).im ≠ 0 := by
      intro n
      refine abs_pos.mp (hη.trans_le (hball (u + δ n) ?_))
      rw [Metric.mem_ball, Real.dist_eq]
      have : |u + δ n - u| = δ n := by
        rw [show u + δ n - u = δ n by ring, abs_of_pos (hδpos n)]
      rw [this]
      exact lt_of_lt_of_le (hδlt n) hre
    refine measurable_deriv_of_hasDerivAt_zero
      (f := fun (ω : Ω d) (t : ℝ) =>
        gloop (d.L N) (d.W N) (Hflow d N u ω) (zt Ev (u + t)) I)
      (δ := δ) hδ0 hδt (fun n => (continuous_gloop_Hflow d N u (hzn n) I).measurable)
      (by simpa using (continuous_gloop_Hflow d N u hzu I).measurable) (fun ω => ?_)
    have hd : HasDerivAt (fun t : ℝ => ((u, u) : ℝ × ℝ) + t • ((0 : ℝ), (1 : ℝ)))
        ((0 : ℝ), (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ), (1 : ℝ))).const_add
        ((u, u) : ℝ × ℝ)
    have hfd : HasFDerivAt
        (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
        (fderiv ℝ (fun p : ℝ × ℝ =>
          gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I) (u, u))
        (((u, u) : ℝ × ℝ) + (0 : ℝ) • ((0 : ℝ), (1 : ℝ))) := by
      simpa using ((hC1 ω).diff _ hcenter).hasFDerivAt
    have hco := hfd.comp_hasDerivAt (0 : ℝ) hd
    rw [Function.comp_def] at hco
    exact hco.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp)
  have hF'meas : AEStronglyMeasurable (fun ω : Ω d =>
      fderiv ℝ (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
        (u, u)) (P d) := by
    have hEq : (fun ω : Ω d =>
        fderiv ℝ (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
          (u, u))
        = (fun ω : Ω d => (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ
              (ContinuousLinearMap.fst ℝ ℝ ℝ))
            (fderiv ℝ (fun p : ℝ × ℝ =>
              gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I) (u, u) (1, 0)))
          + (fun ω : Ω d => (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ
              (ContinuousLinearMap.snd ℝ ℝ ℝ))
            (fderiv ℝ (fun p : ℝ × ℝ =>
              gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I) (u, u) (0, 1))) := by
      funext ω
      exact clm_prod_eq_smulRight _
    rw [hEq]
    exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous).comp_aestronglyMeasurable
          hA.aestronglyMeasurable).add
      (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous).comp_aestronglyMeasurable
          hB.aestronglyMeasurable)
  refine ⟨_, hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (p : ℝ × ℝ) (ω : Ω d) =>
      gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt Ev p.2) I)
    (F' := fun (p : ℝ × ℝ) (ω : Ω d) =>
      fderiv ℝ (fun q : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N q.1 ω) (zt Ev q.2) I) p)
    (bound := fun _ : Ω d =>
      (Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length))
    (Metric.ball_mem_nhds _ hr0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds ((u, u) : ℝ × ℝ) hr0) fun p hp =>
      Continuous.aestronglyMeasurable
        (continuous_gloop_Hflow d N p.1 (abs_pos.mp (hη.trans_le (hzs p hp))) I))
    (integrable_gloop_Hflow d N u hη (hzs _ hcenter) I hwf hn)
    hF'meas
    (Filter.Eventually.of_forall fun ω p hp => (hC1 ω).bdd₁ p hp)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω p hp => ((hC1 ω).diff p hp).hasFDerivAt)⟩

end JointIntegral

end RBM.Gauss
