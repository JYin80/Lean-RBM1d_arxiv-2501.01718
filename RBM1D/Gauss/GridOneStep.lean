/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.SteinMatrix

/-!
# T1486 — one-step Gaussian expansion (discrete replacement of Itô's drift)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*; discrete-grid preparation for the true-path pilot A5,
`docs/claude-team/pilot-P4P5-paper.md` §3 ("the drift of one grid step is `Δ ×` the generator,
plus a small error").  This file does
**not** use a fourth-order Taylor expansion: the whole content is the generator identity
`RBM.Gauss.hasDerivAt_integral_Phi` (`RBM1D/Gauss/Generator.lean:803`), integrated in time by the
fundamental theorem of calculus, plus a Lipschitz hypothesis on the generator's pointwise value
to control the linearization error.

## Main results

* `RBM.Gauss.TestFun.shift` — `TestFun` is invariant under shifting the test function's matrix
  argument by any fixed matrix `M`: `Φ (M + ·)` is again a `TestFun`, with the same three
  constants.  Proved via the chain rule for `A ↦ M + A` (`HasFDerivAt.comp` with the identity
  derivative of a translation), applied twice (`fderiv` and `fderiv ∘ fderiv`).
* `RBM.Gauss.coordD2_shift` — the same shift, read off at the level of `coordD2`: moving `Φ`'s
  argument by `M` moves `coordD2` the same way.  This is the bridge from
  `hasDerivAt_integral_Phi` (stated for the shifted test function) back to a statement about
  `Φ` and `M` directly.
* `RBM.Gauss.Grid.gen`, `RBM.Gauss.Grid.genPt` — the time-integrand of the one-step expansion
  (an expectation) and its pointwise (deterministic, `ω`-free) counterpart.
* `RBM.Gauss.Grid.oneStep_integral_eq` (**T2**) — for `v ≥ 0` (including `v = 0`), the exact
  identity `E[Φ(M + √v X)] - Φ(M) = ∫₀^v gen(w) dw`.  The route is exactly the one the ticket
  prescribes: `TestFun.shift` turns this into the generator identity applied to the shifted test
  function on `(0, v)`, continuity of the left side at `w = 0` is proved directly by dominated
  convergence (`Real.sqrt` is continuous at `0`, so no extra hypothesis is needed there), and the
  fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`) closes
  the window including the left endpoint.
* `RBM.Gauss.Grid.oneStep_error_le` (**T3**) — assuming the deterministic generator value
  `genPt` is `Λ`-Lipschitz (ℓ²-operator norm, `Matrix.Norms.L2Operator`, the same norm
  `RBM1D/Gauss/LoopLipschitz.lean` uses) on Hermitian matrices, the one-step expansion has error
  `O(Δ^{3/2})`: `‖E[Φ(M + √Δ X)] - Φ(M) - Δ · genPt(M)‖ ≤ (2/3) Λ Δ^{3/2} E‖X‖`.  The route:
  `gen(w) = E[genPt(M + √w X)]` (finite-sum/integral Fubini), so `gen(w) - genPt(M) =
  E[genPt(M + √w X) - genPt(M)]`, bounded in norm by `Λ √w E‖X‖` pointwise (both arguments are
  Hermitian: `M` by hypothesis, `M + √w X` because `√w X = H_w` is `Hflow_isHermitian`); then
  integrate the `T2` identity against this bound over `[0, Δ]` and evaluate
  `∫₀^Δ √w dw = (2/3) Δ^{3/2}` (`integral_rpow`, `Real.sqrt_eq_rpow`).
* `RBM.Gauss.integrable_norm_Xmat` — `‖X‖` is integrable: `X` is dominated by the finite sum
  `∑_α |ω_α| ‖B_α‖` of integrable coordinates (`RBM.Gauss.integrable_coord`), so `X` itself is
  Bochner integrable, hence so is its norm.

## Step 0 checks (read-only, recorded here per the ticket)

(a) `hasDerivAt_integral_Phi` is stated for `Φ (Hflow d N s ω)` with `Hflow d N s ω = (√s :
ℂ) • Xmat d N ω` (`Gauss/Model.lean:363` — this is *definitional*, not merely propositionally
equal), and requires `0 < u` (the `(2√u)⁻¹` chain-rule factor blows up at `u = 0`).  Consequently
`oneStep_integral_eq` only invokes it on the open interval `(0, v)`; the closed left endpoint is
supplied separately by `MeasureTheory.continuous_of_dominated` (§ above), which needs no
positivity: `Real.sqrt` is continuous at `0` too.

(b) `RBM1D/Gauss/LoopLipschitz.lean` opens `Matrix.Norms.L2Operator` (line 113,
`open scoped Matrix.Norms.L2Operator`) for the whole file; so does `RBM1D/Gauss/Generator.lean`
(line 127), which is where `TestFun`'s three global bounds (`bdd₀`, `bdd₁`, `bdd₂`) are stated.
This file opens the same scope, so every norm appearing in `TestFun`, in `genPt`'s Lipschitz
hypothesis and in `Xmat`'s norm below is the *same* `ℓ² → ℓ²` operator norm.

(c) `TestFun.shift` does not already exist; grepping the repository for `TestFun.*shift`,
`Φ (M + A)` before writing this file turned up no reusable declaration (only the *unshifted*
generator identity and its `u`-Duhamel closures in `RBM1D/Gauss/APrimeDuhamel.lean`, which are
not enough by themselves: `norm_integral_sub_le_of_genTerm_le` there requires the *left* window
endpoint to be strictly positive, `0 < a`, so it cannot supply the `v = 0` endpoint this ticket
needs).

## Deviations from the paper (for `docs/paper-deltas.md`)

None beyond the ones already recorded for `Hflow = √u • X` (T69) and for `TestFun`'s *global*
bounds (`Generator.lean`); this file only assembles those with the fundamental theorem of
calculus.
-/

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator NNReal

/-! ### T1: `TestFun` is invariant under shifting the argument by a fixed matrix -/

section Shift

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- The chain rule for a translation of the argument: `f (M + ·)` has the same derivative as
`f` itself, read off at the shifted point.  `A ↦ M + A` has derivative the identity everywhere,
so composing with it just re-centres the base point. -/
private theorem hasFDerivAt_shift {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : Differentiable ℝ f) (M A : E) :
    HasFDerivAt (fun A' => f (M + A')) (fderiv ℝ f (M + A)) A := by
  have h1 : HasFDerivAt f (fderiv ℝ f (M + A)) (M + A) := (hf (M + A)).hasFDerivAt
  have h2 : HasFDerivAt (fun A' : E => M + A') (ContinuousLinearMap.id ℝ E) A :=
    (hasFDerivAt_id A).const_add M
  have h3 := h1.comp A h2
  rwa [ContinuousLinearMap.comp_id] at h3

/-- **T1.** `TestFun` is invariant under shifting `Φ`'s argument by any fixed matrix `M`: the
three global bounds (value, first derivative, second derivative) carry over unchanged, because
`fderiv ℝ (Φ (M + ·)) A = fderiv ℝ Φ (M + A)` and likewise one order higher. -/
theorem TestFun.shift (h : TestFun d N Φ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    TestFun d N (fun A => Φ (M + A)) where
  contDiff := h.contDiff.comp (contDiff_const.add contDiff_id)
  bdd₀ := h.bdd₀.imp fun C hC A => hC (M + A)
  bdd₁ := by
    obtain ⟨C₁, hC₁⟩ := h.bdd₁
    exact ⟨C₁, fun A => by
      rw [(hasFDerivAt_shift h.differentiable M A).fderiv]
      exact hC₁ _⟩
  bdd₂ := by
    obtain ⟨C₂, hC₂⟩ := h.bdd₂
    refine ⟨C₂, fun A => ?_⟩
    have hfd : fderiv ℝ (fun A' => Φ (M + A')) = fun A' => fderiv ℝ Φ (M + A') :=
      funext fun A' => (hasFDerivAt_shift h.differentiable M A').fderiv
    rw [hfd, (hasFDerivAt_shift h.differentiable_fderiv M A).fderiv]
    exact hC₂ _

/-- The shift read off at the level of `coordD2`: moving `Φ`'s argument by `M` moves the second
directional derivative the same way. This is the bridge from the generator identity applied to
the shifted test function `Φ (M + ·)` back to a statement about `Φ` and `M` directly. -/
theorem coordD2_shift (h : TestFun d N Φ) (M A : Matrix (d.Idx N) (d.Idx N) ℂ)
    (p : d.Idx N × d.Idx N × Bool) :
    coordD2 d N (fun A' => Φ (M + A')) A p = coordD2 d N Φ (M + A) p := by
  have hfd : fderiv ℝ (fun A' => Φ (M + A')) = fun A' => fderiv ℝ Φ (M + A') :=
    funext fun A' => (hasFDerivAt_shift h.differentiable M A').fderiv
  unfold coordD2
  rw [hfd, (hasFDerivAt_shift h.differentiable_fderiv M A).fderiv]

end Shift

/-! ### `‖X‖` is integrable -/

/-- **`integrable_norm_Xmat`.** `X` is dominated by the finite sum `∑_α |ω_α| ‖B_α‖` of
integrable coordinates, so `X` itself is Bochner integrable, hence so is its norm. -/
theorem integrable_norm_Xmat (d : Dims) (N : ℕ) :
    Integrable (fun ω : Ω d => ‖Xmat d N ω‖) (P d) := by
  have hbound : ∀ ω : Ω d, ‖Xmat d N ω‖
      ≤ ∑ p ∈ usedCoord d N, |ω (crd d N p)| * ‖Bmat d N p.1 p.2.1 p.2.2‖ := by
    intro ω
    rw [Xmat_eq_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  have hg : Integrable (fun ω : Ω d =>
      ∑ p ∈ usedCoord d N, |ω (crd d N p)| * ‖Bmat d N p.1 p.2.1 p.2.2‖) (P d) :=
    integrable_finsetSum _ fun p _ => ((integrable_coord d (crd d N p)).abs).mul_const _
  have hXInt : Integrable (fun ω : Ω d => Xmat d N ω) (P d) :=
    hg.mono' (continuous_Xmat d N).aestronglyMeasurable (Eventually.of_forall hbound)
  exact hXInt.norm

/-! ### T2, T3: the one-step Gaussian expansion -/

namespace Grid

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- Continuity of `A ↦ coordD2 d N Φ A p`, from the global boundedness/continuity of `Φ`'s
second derivative that `TestFun` supplies. -/
theorem continuous_coordD2_arg (h : TestFun d N Φ) (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun A : Matrix (d.Idx N) (d.Idx N) ℂ => coordD2 d N Φ A p :=
  (h.continuous_fderiv2.clm_apply continuous_const).clm_apply continuous_const

/-- A parametric integral along the flow `Hflow` is continuous in the time parameter, jointly by
dominated convergence: `Real.sqrt` is continuous everywhere (including at `0`), and `G` is
continuous and globally bounded. -/
theorem continuous_integral_comp_Hflow {G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hGc : Continuous G) {C : ℝ} (hGb : ∀ A, ‖G A‖ ≤ C) :
    Continuous fun s : ℝ => ∫ ω, G (Hflow d N s ω) ∂(P d) := by
  have := isProbabilityMeasure_P d
  refine continuous_of_dominated
    (fun s => (hGc.comp (continuous_Hflow d N s)).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun ω => hGb _)
    (integrable_const C)
    (Eventually.of_forall fun ω => ?_)
  have hcs : Continuous fun s : ℝ => Hflow d N s ω := by
    have hfun : (fun s : ℝ => Hflow d N s ω) = fun s => (Real.sqrt s : ℂ) • Xmat d N ω := rfl
    rw [hfun]
    exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const
  exact hGc.comp hcs

/-- **The time-integrand of the one-step expansion, as an expectation.**
`gen d N Φ M w := ½ ∑_{p ∈ usedCoord} S_p E[coordD2 Φ (M + √w X) p]`. -/
noncomputable def gen (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (w : ℝ) : ℂ :=
  (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
    ∫ ω, coordD2 d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) p ∂(P d)

/-- **The pointwise (deterministic, `ω`-free) generator value.**
`genPt d N Φ A := ½ ∑_{p ∈ usedCoord} S_p · coordD2 Φ A p`. -/
noncomputable def genPt (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (A : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • coordD2 d N Φ A p

theorem continuous_gen (h : TestFun d N Φ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Continuous (gen d N Φ M) := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  have hterm : ∀ p ∈ usedCoord d N, Continuous fun w : ℝ =>
      ∫ ω, coordD2 d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) p ∂(P d) := by
    intro p _
    have hGc : Continuous fun A : Matrix (d.Idx N) (d.Idx N) ℂ => coordD2 d N Φ (M + A) p :=
      (continuous_coordD2_arg h p).comp (continuous_const.add continuous_id)
    exact continuous_integral_comp_Hflow hGc fun A => norm_coordD2_le hC₂ _ p
  exact Continuous.const_smul
    (continuous_finsetSum (usedCoord d N) fun p hp =>
      (hterm p hp).const_smul (gvar d (crd d N p) : ℝ)) (1 / 2 : ℝ)

theorem continuous_genPt (h : TestFun d N Φ) : Continuous (genPt d N Φ) := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  exact Continuous.const_smul
    (continuous_finsetSum (usedCoord d N) fun p _ =>
      (continuous_coordD2_arg h p).const_smul (gvar d (crd d N p) : ℝ)) (1 / 2 : ℝ)

/-- `genPt` is globally bounded, uniformly in the (possibly non-Hermitian) matrix argument, by
the same constant `TestFun.bdd₂` supplies for `coordD2`. -/
theorem norm_genPt_le {C₂ : ℝ} (hC₂ : ∀ A, ‖fderiv ℝ (fderiv ℝ Φ) A‖ ≤ C₂)
    (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖genPt d N Φ A‖
      ≤ (1 / 2 : ℝ) * ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) *
          (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ ^ 2) := by
  have hterm : ∀ p ∈ usedCoord d N,
      ‖(gvar d (crd d N p) : ℝ) • coordD2 d N Φ A p‖
        ≤ (gvar d (crd d N p) : ℝ) * (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ ^ 2) := by
    intro p _
    have hgv : |((gvar d (crd d N p) : ℝ))| = ((gvar d (crd d N p) : ℝ)) :=
      abs_of_nonneg (gvar d (crd d N p)).2
    rw [norm_smul, Real.norm_eq_abs, hgv]
    refine mul_le_mul_of_nonneg_left ?_ (gvar d (crd d N p)).2
    calc ‖coordD2 d N Φ A p‖
        ≤ C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖ :=
          norm_coordD2_le hC₂ A p
      _ = C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ ^ 2 := by ring
  unfold genPt
  rw [norm_smul, Real.norm_eq_abs, show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
    (by norm_num)

theorem integrable_genPt_shift (h : TestFun d N Φ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (w : ℝ) :
    Integrable (fun ω : Ω d => genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω)) (P d) := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  have hsqrtConst : Continuous fun _ : Ω d => (Real.sqrt w : ℂ) := continuous_const
  have hcont : Continuous fun ω : Ω d => genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) :=
    (continuous_genPt h).comp (continuous_const.add (hsqrtConst.smul (continuous_Xmat d N)))
  exact integrable_of_continuous_of_bound hcont fun ω => norm_genPt_le hC₂ _

/-- The integral of a constant complex number against the probability measure `P d` is itself. -/
theorem integral_const_P (d : Dims) (c : ℂ) : ∫ _ω : Ω d, c ∂(P d) = c := by
  have := isProbabilityMeasure_P d
  rw [MeasureTheory.integral_const]
  have huniv : (P d).real Set.univ = 1 := by simp
  rw [huniv, one_smul]

/-- **`gen` is the expectation of `genPt` along the shifted flow.** Swapping the (finite)
coordinate sum with the integral, using the boundedness/continuity `TestFun.bdd₂` supplies for
integrability. -/
theorem gen_eq_integral_genPt (h : TestFun d N Φ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (w : ℝ) :
    gen d N Φ M w = ∫ ω, genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) ∂(P d) := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  have hsqrtConst : Continuous fun _ : Ω d => (Real.sqrt w : ℂ) := continuous_const
  have hshiftCont : ∀ p : d.Idx N × d.Idx N × Bool,
      Continuous fun ω : Ω d => coordD2 d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) p := by
    intro p
    have hA : Continuous fun A : Matrix (d.Idx N) (d.Idx N) ℂ => coordD2 d N Φ (M + A) p :=
      (continuous_coordD2_arg h p).comp (continuous_const.add continuous_id)
    exact hA.comp (hsqrtConst.smul (continuous_Xmat d N))
  have hint : ∀ p ∈ usedCoord d N,
      Integrable (fun ω : Ω d => coordD2 d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) p) (P d) :=
    fun p _ => integrable_of_continuous_of_bound (hshiftCont p) fun ω => norm_coordD2_le hC₂ _ p
  have hswap := integral_finsetSum (usedCoord d N)
    (f := fun p (a : Ω d) => (gvar d (crd d N p) : ℝ) •
      coordD2 d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N a) p)
    (fun p hp => (hint p hp).smul (gvar d (crd d N p) : ℝ))
  unfold genPt gen
  rw [integral_smul, hswap]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
  rw [integral_smul]

/-- **T2.** `RBM.Gauss.Grid.oneStep_integral_eq`: the exact one-step Gaussian expansion, for
every `v ≥ 0` (`v = 0` included). Route: `TestFun.shift` turns the generator identity
`hasDerivAt_integral_Phi` into a derivative of `s ↦ E[Φ(M + √s X)]` on `(0, v)`; continuity of
that same function at every `s` (including `s = 0`) is dominated convergence
(`continuous_integral_comp_Hflow`); the fundamental theorem of calculus closes the window. -/
theorem oneStep_integral_eq (h : TestFun d N Φ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ ω, Φ (M + (Real.sqrt v : ℂ) • Xmat d N ω) ∂(P d)) - Φ M
      = ∫ w in (0 : ℝ)..v, gen d N Φ M w := by
  have hΨtf : TestFun d N (fun A => Φ (M + A)) := h.shift M
  have hFcont : Continuous fun s : ℝ => ∫ ω, Φ (M + Hflow d N s ω) ∂(P d) := by
    obtain ⟨C₀, hC₀⟩ := hΨtf.bdd₀
    exact continuous_integral_comp_Hflow hΨtf.contDiff.continuous hC₀
  have hFderiv : ∀ x ∈ Set.Ioo (0 : ℝ) v,
      HasDerivAt (fun s : ℝ => ∫ ω, Φ (M + Hflow d N s ω) ∂(P d)) (gen d N Φ M x) x := by
    intro x hx
    have hd := hasDerivAt_integral_Phi (matrixStein d) hΨtf hx.1
    have heq : ((1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N (fun A => Φ (M + A)) (Hflow d N x ω) p ∂(P d)) = gen d N Φ M x := by
      unfold gen
      refine congrArg _ (Finset.sum_congr rfl fun p _ => congrArg _ ?_)
      exact integral_congr_ae
        (Eventually.of_forall fun ω => coordD2_shift h M (Hflow d N x ω) p)
    rwa [heq] at hd
  have hgenInt : IntervalIntegrable (gen d N Φ M) MeasureTheory.volume 0 v :=
    (continuous_gen h M).intervalIntegrable 0 v
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv
    hFcont.continuousOn hFderiv hgenInt
  have h0 : (∫ ω, Φ (M + Hflow d N 0 ω) ∂(P d)) = Φ M := by
    simp only [Hflow_zero, add_zero]
    exact integral_const_P d (Φ M)
  rw [h0] at hmain
  exact hmain.symm

/-- **T3.** `RBM.Gauss.Grid.oneStep_error_le`: the one-step expansion linearizes with error
`O(Δ^{3/2})`, given a Lipschitz bound on the deterministic generator value `genPt` on Hermitian
matrices, in the `ℓ²`-operator norm. Route: `T2` writes the left side as
`∫₀^Δ (gen(w) - genPt(M)) dw`; `gen(w) - genPt(M) = E[genPt(M + √w X) - genPt(M)]`
(`gen_eq_integral_genPt`), whose norm is `≤ Λ √w E‖X‖` pointwise, since both `M + √w X = M +
Hflow_w` and `M` are Hermitian; integrating this bound over `[0, Δ]` and evaluating
`∫₀^Δ √w dw = (2/3) Δ^{3/2}` gives the stated constant. -/
theorem oneStep_error_le (h : TestFun d N Φ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {Λ : ℝ}
    (hLip : ∀ A A' : Matrix (d.Idx N) (d.Idx N) ℂ, A.IsHermitian → A'.IsHermitian →
      ‖genPt d N Φ A - genPt d N Φ A'‖ ≤ Λ * ‖A - A'‖)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ‖(∫ ω, Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω) ∂(P d)) - Φ M - (Δ : ℂ) • genPt d N Φ M‖
      ≤ (2 / 3) * Λ * Δ ^ (3 / 2 : ℝ) * ∫ ω, ‖Xmat d N ω‖ ∂(P d) := by
  classical
  set K : ℝ := ∫ ω, ‖Xmat d N ω‖ ∂(P d) with hK
  -- The pointwise (in `w ≥ 0`) bound on `‖gen w - genPt M‖`.
  have hbound : ∀ w : ℝ, 0 ≤ w → ‖gen d N Φ M w - genPt d N Φ M‖ ≤ Λ * Real.sqrt w * K := by
    intro w _
    have hge : gen d N Φ M w = ∫ ω, genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) ∂(P d) :=
      gen_eq_integral_genPt h M w
    have hgpM : (∫ _ω : Ω d, genPt d N Φ M ∂(P d)) = genPt d N Φ M := integral_const_P d _
    have hintA := integrable_genPt_shift h M w
    have hintB : Integrable (fun _ω : Ω d => genPt d N Φ M) (P d) := integrable_const _
    have hstep1 : gen d N Φ M w - genPt d N Φ M
        = ∫ ω, (genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) - genPt d N Φ M) ∂(P d) := by
      rw [integral_sub hintA hintB, hgpM, hge]
    have hptwise : ∀ ω : Ω d,
        ‖genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) - genPt d N Φ M‖
          ≤ Λ * Real.sqrt w * ‖Xmat d N ω‖ := by
      intro ω
      have hHerm : (M + (Real.sqrt w : ℂ) • Xmat d N ω).IsHermitian :=
        hM.add (Hflow_isHermitian d N w ω)
      have h1 := hLip (M + (Real.sqrt w : ℂ) • Xmat d N ω) M hHerm hM
      have h2 : (M + (Real.sqrt w : ℂ) • Xmat d N ω) - M = (Real.sqrt w : ℂ) • Xmat d N ω := by
        abel
      have h3 : ‖(Real.sqrt w : ℂ) • Xmat d N ω‖ = Real.sqrt w * ‖Xmat d N ω‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg w)]
      rw [h2, h3, ← mul_assoc] at h1
      exact h1
    have hboundIntegrable : Integrable
        (fun ω : Ω d => Λ * Real.sqrt w * ‖Xmat d N ω‖) (P d) :=
      (integrable_norm_Xmat d N).const_mul (Λ * Real.sqrt w)
    calc ‖gen d N Φ M w - genPt d N Φ M‖
        = ‖∫ ω, (genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) - genPt d N Φ M) ∂(P d)‖ := by
          rw [hstep1]
      _ ≤ ∫ ω, ‖genPt d N Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) - genPt d N Φ M‖ ∂(P d) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, Λ * Real.sqrt w * ‖Xmat d N ω‖ ∂(P d) :=
          integral_mono ((hintA.sub hintB).norm) hboundIntegrable hptwise
      _ = Λ * Real.sqrt w * K := by
          rw [MeasureTheory.integral_const_mul, ← hK]
  -- `T2`, rewritten with `genPt M` subtracted as a constant interval integral.
  have hstep := oneStep_integral_eq h M hΔ
  have hgenPtInt : IntervalIntegrable (fun _ : ℝ => genPt d N Φ M) MeasureTheory.volume 0 Δ :=
    intervalIntegrable_const
  have hgenInt : IntervalIntegrable (gen d N Φ M) MeasureTheory.volume 0 Δ :=
    (continuous_gen h M).intervalIntegrable 0 Δ
  have hconstInt : (∫ _w in (0 : ℝ)..Δ, genPt d N Φ M) = (Δ : ℂ) • genPt d N Φ M := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, smul_eq_mul]
  have hdiff : (∫ ω, Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω) ∂(P d)) - Φ M
      - (Δ : ℂ) • genPt d N Φ M
      = ∫ w in (0 : ℝ)..Δ, (gen d N Φ M w - genPt d N Φ M) := by
    rw [intervalIntegral.integral_sub hgenInt hgenPtInt, hconstInt, ← hstep]
  rw [hdiff]
  have hnormDiffCont : Continuous fun w : ℝ => ‖gen d N Φ M w - genPt d N Φ M‖ :=
    ((continuous_gen h M).sub continuous_const).norm
  have hboundCont : Continuous fun w : ℝ => Λ * Real.sqrt w * K :=
    (continuous_const.mul Real.continuous_sqrt).mul continuous_const
  calc ‖∫ w in (0 : ℝ)..Δ, (gen d N Φ M w - genPt d N Φ M)‖
      ≤ ∫ w in (0 : ℝ)..Δ, ‖gen d N Φ M w - genPt d N Φ M‖ :=
        intervalIntegral.norm_integral_le_integral_norm hΔ
    _ ≤ ∫ w in (0 : ℝ)..Δ, Λ * Real.sqrt w * K := by
        refine intervalIntegral.integral_mono_on hΔ
          (hnormDiffCont.intervalIntegrable 0 Δ) (hboundCont.intervalIntegrable 0 Δ) ?_
        intro w hw
        exact hbound w hw.1
    _ = Λ * K * ∫ w in (0 : ℝ)..Δ, Real.sqrt w := by
        have hre : (fun w : ℝ => Λ * Real.sqrt w * K) = fun w : ℝ => (Λ * K) * Real.sqrt w := by
          funext w; ring
        rw [hre, intervalIntegral.integral_const_mul]
    _ = Λ * K * ((2 / 3 : ℝ) * Δ ^ (3 / 2 : ℝ)) := by
        have hsqrtInt : (∫ w in (0 : ℝ)..Δ, Real.sqrt w) = (2 / 3 : ℝ) * Δ ^ (3 / 2 : ℝ) := by
          have hrw : (fun w : ℝ => Real.sqrt w) = fun w : ℝ => w ^ (1 / 2 : ℝ) :=
            funext fun w => Real.sqrt_eq_rpow w
          rw [hrw, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2)),
            show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
            Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), sub_zero]
          ring
        rw [hsqrtInt]
    _ = (2 / 3) * Λ * Δ ^ (3 / 2 : ℝ) * K := by ring

end Grid

end RBM.Gauss
