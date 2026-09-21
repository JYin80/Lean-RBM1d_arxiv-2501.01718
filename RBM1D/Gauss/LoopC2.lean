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

end RBM.Gauss
