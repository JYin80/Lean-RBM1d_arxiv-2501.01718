/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator
import RBM1D.Loop.Split
import RBM1D.Loop.Primitive

/-!
# (2.34) and Lemma 2.11 in moment form (T76)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §2.4–2.6, pp. 15–19: the stochastic flow (2.34) and the loop hierarchy of
Lemma 2.11, (2.45)–(2.47).

This file is the **loop end of the moment route** (project note `claude/moment-route-plan.md`).
The flow is `H_u = √u • X` (`RBM1D/Gauss/Model.lean`, T69) and the generator identity

  `∂_u E[Φ(H_u)] = ½ ∑_{ij} S_ij E[∂_ij ∂_ji Φ(H_u)]`

is `RBM.Gauss.hasDerivAt_integral_Phi_pairs` (`RBM1D/Gauss/Generator.lean`, T71).  Here that
identity is specialized to the `G`-loops of (2.41), which turns Lemma 2.11 into a statement
about `∂_u E[L_{u,σ,a}]`.

## The largest paper-delta of the project

**The SDE (2.45) is never proved, and is not used.**  The paper's Lemma 2.11 is an identity
between stochastic differentials: `dL = E^{(M)} + E^{(G̃)} dt + W ∑_{k<l} (…) dt`, whose first
summand (2.46) is a martingale differential.  In the moment route there is no filtration, no
Brownian motion and no martingale, so no such identity can be stated.  What replaces it is its
expectation, in which the martingale term simply does not occur:

  `∂_u E[L_{u,σ,a}] = E[E^{(G̃)}_{u,σ,a}] + E[W ∑_{k<l} ∑_{a,b} (G^{(a),L}_{k,l}∘L)S_ab(G^{(b),R}_{k,l}∘L)]`.

The right-hand side is `RBM.primRhs` applied to the loop function `L_{u,·}` plus the `Ẽ`-term.
This is `RBM.Gauss.hasDerivAt_integral_gloop_hierarchy`.  Everything the paper does with (2.45)
downstream (§5.2 onwards) is done after taking expectations or second moments, so no consumer
needs the pathwise form; what a consumer *does* need — the second-moment bound that the paper
gets from BDG applied to (2.46) — comes from the same generator identity applied to `|F|^{2p}`
and is the subject of T72 (`Gauss/MomentGronwall.lean`), not of this file.

## What is proved, and the split of Lemma 2.11

Lemma 2.11 factors into two halves:

1. **Itô's formula** — replaced, in expectation, by T71's generator identity.  This half is a
   *theorem* here: `RBM.Gauss.hasDerivAt_integral_gloop`.
2. **The deterministic algebra**: the identity that computes the second-order term
   `½ ∑_{ij} S_ij ∂_ij ∂_ji L_{σ,a}` of a loop as `E^{(G̃)} + W ∑_{k<l} (…)`, i.e. the
   cut-and-glue combinatorics of Definition 2.10.  Nothing probabilistic is left in it.  It is
   **not proved here**; it is the single field `second` of the hypothesis structure
   `RBM.Gauss.LoopIto`, whose `EG` field carries the `Ẽ` term the way `RBM.Hierarchy`'s `F`
   carries the drift of (5.15).  `RBM.Gauss.eGterm` writes out the intended `EG`, (2.47).

## The spectral parameter is frozen

`RBM.Sample.G` is `(H_t - z_t)⁻¹` with `z_t = E + (1-t) m^{(E)}` **moving** with `t`
(Definition 2.7), so `u ↦ L_{u,σ,a}` depends on `u` through two arguments.  T71's identity
differentiates the matrix argument only.  The theorems below therefore differentiate

  `v ↦ E[⟨∏ G(H_v, z_u)(σ_i) E_{a_i}⟩]`   at `v = u`,

the spectral parameter frozen at its value `z_u` at the base point; at the base point itself
the function is `RBM.Sample.ELval E N u I` (`RBM.Gauss.sample_ELval`).  This is a genuine
deviation and it is why the `Ẽ` term appearing in `LoopIto.second` is the paper's (2.47) *with
`G` in place of `G̃ = G - m`*: in the paper the `-m(σ_k)` subtraction is produced precisely by
the motion of `z_t` (Itô's `∂_t G = G (∂_t z_t) G = -m G G`, which is what turns `S[G]` into
`S[G] - m` in the SDE for `G_t` on p. 15).  Adding the missing `z`-drift needs a two-variable
chain rule (`d/du f(u,u)` from the two partials, with the `z`-partial continuous at the base
point), which Mathlib does not provide in a directly usable form and which is **not done here**.
Since the `Ẽ` term of `LoopIto` is abstract, the frozen statement is nonetheless exactly the
paper's shape; only the intended meaning of `EG` changes.

## Main definitions

* `RBM.Gauss.loopObs` — the `n`-loop (2.41) read as a function of the matrix, precomposed with
  the Hermitian projection `RBM.Gauss.hermCLM` so that it is defined, and bounded, on the whole
  matrix space (`TestFun` demands global bounds; `(M - z)⁻¹` only has them on the Hermitian
  matrices, and `hermCLM` is the identity on the values `H_u` of the flow).
* `RBM.Gauss.eGterm` — (2.47), the `Ẽ` term, in the cut-and-glue vocabulary of
  `RBM.LoopIdx.cutGlue`.  Not used by any theorem; recorded as the intended `LoopIto.EG`.
* `RBM.Gauss.LoopIto` — **the one hypothesis of this file besides `MatrixStein` and
  `TestFun`**: the deterministic second-order identity of Lemma 2.11 (see above).

## Main results

**(2.34) in expectation form.**  The three fields of `RBM.Sample` are already theorems (T69);
what the expectation-level consumers need on top of them is that `E L_{u,σ,a}` is a genuine
Bochner integral and has the deterministic envelope `‖G‖ ≤ η⁻¹` gives it:

* `RBM.Gauss.continuous_gloop_Hflow` : `ω ↦ L_{u,σ,a}(ω)` is continuous (through
  `RBM.Gauss.continuous_green_comp`, continuity of the resolvent at a Hermitian matrix).
* `RBM.Gauss.integrable_sample_Lval` : `L_{u,σ,a}` is integrable — this **closes the
  integrability gap** recorded in the deviations of `RBM1D/Flow/Hypotheses.lean` ("(2.71)/(2.80)
  use the Bochner integral `∫ ω, L ∂P` for `E L`; integrability is not demanded").
* `RBM.Gauss.norm_sample_Lval_le`, `RBM.Gauss.norm_sample_ELval_le` : the deterministic (not
  high-probability) envelope `|L_{u,σ,a}| ≤ η^{-n} W^{-n+1}` of (5.2), on the whole space and
  after integration.
* `RBM.Gauss.sample_G`, `sample_Lval`, `sample_ELval` : the bridge from the `RBM.Sample`
  vocabulary to `Hflow`/`green`/`gloop`.

**Lemma 2.11 in moment form.**

* `RBM.Gauss.hasDerivAt_integral_gloop` : T71's generator identity at a loop observable,
  `∂_v E[L(H_v, z)]|_{v=u} = ½ ∑_i ∑_j S_ij E[∂_ij ∂_ji L(H_u, z)]`.  No hypothesis beyond
  `MatrixStein` (T70) and `TestFun` for the observable.
* `RBM.Gauss.integral_sum_wirtSecond` : the finite index sum of the generator identity may be
  moved inside the expectation (`RBM.Gauss.integrable_wirtSecond`).
* `RBM.Gauss.hasDerivAt_integral_gloop_hierarchy` and its `RBM.Sample`-vocabulary form
  `RBM.Gauss.hasDerivAt_integral_Lval_hierarchy` : **the moment form of Lemma 2.11**,
  `∂_v E[L(H_v, z_u)]|_{v=u} = E[Ẽ] + E[primRhs L_u]`.
* `RBM.Gauss.testFun_loopObs` : the `bdd₀` field of `TestFun` for a loop observable is free
  (it is (5.2) again); what is left of `TestFun` for loops is `ContDiff ℝ 2` and global bounds
  on the first two Fréchet derivatives, which this file does not prove.

## Hypotheses (nothing here is an `axiom`)

* `RBM.Gauss.MatrixStein d` (T71's interface, owed by T70).
* `RBM.Gauss.TestFun d N (loopObs d N z I)` for the loop observable — see
  `RBM.Gauss.testFun_loopObs` for what remains of it.
* `RBM.Gauss.LoopIto d N z` — the deterministic half of Lemma 2.11.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator

/-! ### The loop observable as a globally defined test function -/

section LoopObs

variable (d : Dims) (N : ℕ)

/-- The `n`-loop `L_{σ,a} = ⟨∏_i G(σ_i) E_{a_i}⟩` read as a function of the matrix, precomposed
with the Hermitian projection `RBM.Gauss.hermCLM`. -/
noncomputable def loopObs (z : ℂ) (I : LoopIdx (ZMod (d.L N)))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  gloop (d.L N) (d.W N) (hermCLM (d.Idx N) M) z I

variable {d N}

@[simp] theorem loopObs_of_isHermitian {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    loopObs d N z I M = gloop (d.L N) (d.W N) M z I := by
  rw [loopObs, hermCLM_of_isHermitian hM]

@[simp] theorem loopObs_Hflow (z : ℂ) (I : LoopIdx (ZMod (d.L N))) (u : ℝ) (ω : Ω d) :
    loopObs d N z I (Hflow d N u ω) = gloop (d.L N) (d.W N) (Hflow d N u ω) z I :=
  loopObs_of_isHermitian (Hflow_isHermitian d N u ω)

/-- The loop observable is globally bounded. -/
theorem norm_loopObs_le {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖loopObs d N z I M‖ ≤ η⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1) :=
  norm_gloop_le_of_le_abs_im (isHermitian_hermCLM _) hη hz I hwf hn

/-- `TestFun` for the loop observable, with its `bdd₀` field discharged. -/
theorem testFun_loopObs {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (hC : ContDiff ℝ 2 (loopObs d N z I))
    (h1 : ∃ C : ℝ, ∀ M, ‖fderiv ℝ (loopObs d N z I) M‖ ≤ C)
    (h2 : ∃ C : ℝ, ∀ M, ‖fderiv ℝ (fderiv ℝ (loopObs d N z I)) M‖ ≤ C) :
    TestFun d N (loopObs d N z I) where
  contDiff := hC
  bdd₀ := ⟨_, norm_loopObs_le hη hz I hwf hn⟩
  bdd₁ := h1
  bdd₂ := h2

end LoopObs

/-! ### (2.34) in expectation form: continuity, integrability, the deterministic envelope -/

section Integrability

variable {d : Dims} {N : ℕ}

/-- The resolvent depends continuously on a continuously varying Hermitian matrix. -/
theorem continuous_green_comp {V : Type*} [TopologicalSpace V]
    {f : V → Matrix (d.Idx N) (d.Idx N) ℂ} (hf : Continuous f)
    (hherm : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun v => green (f v) z := by
  rw [continuous_iff_continuousAt]
  intro v
  have hU : IsUnit (f v - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (hherm v) hz
  have hspec : ((hU.unit : (Matrix (d.Idx N) (d.Idx N) ℂ)ˣ) : Matrix (d.Idx N) (d.Idx N) ℂ)
      = f v - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
      (f v - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun w => f w - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) v :=
    hf.continuousAt.sub continuousAt_const
  have := ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
    (f := fun w => f w - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) h1 h2
  simpa [green, Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

/-- `ω ↦ G_u(σ)` is continuous. -/
theorem continuous_Gsig_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω : Ω d => Gsig (Hflow d N u ω) z σ := by
  cases σ with
  | false =>
      refine continuous_green_comp (continuous_Hflow d N u) (Hflow_isHermitian d N u) ?_
      simpa using hz
  | true => exact continuous_green_comp (continuous_Hflow d N u) (Hflow_isHermitian d N u) hz

/-- The loop product of `H_u` is continuous in `ω`. -/
theorem continuous_foldr_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × ZMod (d.L N))) :
    Continuous fun ω : Ω d =>
      l.foldr (fun p M => Gsig (Hflow d N u ω) z p.1 * Eblk (d.L N) (d.W N) p.2 * M)
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((continuous_Gsig_Hflow d N u hz p.1).mul continuous_const).mul ih

theorem continuous_gloopProd_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω : Ω d => gloopProd (d.L N) (d.W N) (Hflow d N u ω) z I :=
  continuous_foldr_Hflow d N u hz (I.σ.zip I.a)

theorem continuous_matrixTrace : Continuous (Matrix.trace : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :=
  LinearMap.continuous_of_finiteDimensional (Matrix.traceLinearMap (d.Idx N) ℂ ℂ)

/-- **The loop is a continuous function of `ω`.** -/
theorem continuous_gloop_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω : Ω d => gloop (d.L N) (d.W N) (Hflow d N u ω) z I :=
  continuous_matrixTrace.comp (continuous_gloopProd_Hflow d N u hz I)

/-- **The `G`-loop along the flow is integrable**, so `E L_{u,σ,a}` of `RBM.Sample.ELval` is a
genuine Bochner integral. -/
theorem integrable_gloop_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    Integrable (fun ω : Ω d => gloop (d.L N) (d.W N) (Hflow d N u ω) z I) (P d) := by
  have hz0 : z.im ≠ 0 := abs_pos.mp (hη.trans_le hz)
  exact integrable_of_continuous_of_bound (continuous_gloop_Hflow d N u hz0 I)
    (fun ω => norm_gloop_le_of_le_abs_im (Hflow_isHermitian d N u ω) hη hz I hwf hn)

end Integrability

/-! ### The interface of `RBM1D/Flow/Hypotheses.lean` -/

section SampleBridge

variable (d : Dims) (N : ℕ) (E : ℝ) (u : ℝ)

@[simp] theorem sample_G (ω : Ω d) :
    (sample d).G E N u ω = green (Hflow d N u ω) (zt E u) := rfl

@[simp] theorem sample_Lval (ω : Ω d) (I : LoopIdx (ZMod (d.L N))) :
    (sample d).Lval E N u ω I = gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) I := rfl

@[simp] theorem sample_ELval (I : LoopIdx (ZMod (d.L N))) :
    (sample d).ELval E N u I
      = ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) I ∂(P d) := rfl

variable {d N E u}

/-- **The `≺`-free envelope of `L_u`** on the whole space. -/
theorem norm_sample_Lval_le {η : ℝ} (hη : 0 < η) (hz : η ≤ |(zt E u).im|) (ω : Ω d)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ‖(sample d).Lval E N u ω I‖ ≤ η⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1) :=
  norm_gloop_le_of_le_abs_im (Hflow_isHermitian d N u ω) hη hz I hwf hn

/-- **`E L_{u,σ,a}` is a genuine Bochner integral** — the integrability gap left open by
`RBM1D/Flow/Hypotheses.lean` is closed for the moment-route sample. -/
theorem integrable_sample_Lval {η : ℝ} (hη : 0 < η) (hz : η ≤ |(zt E u).im|)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    Integrable (fun ω : Ω d => (sample d).Lval E N u ω I) (P d) :=
  integrable_gloop_Hflow d N u hη hz I hwf hn

/-- The same envelope for the expectation `E L_{u,σ,a}`. -/
theorem norm_sample_ELval_le {η : ℝ} (hη : 0 < η) (hz : η ≤ |(zt E u).im|)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ‖(sample d).ELval E N u I‖ ≤ η⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1) := by
  have h := norm_integral_le_of_norm_le_const (μ := P d)
    (f := fun ω : Ω d => (sample d).Lval E N u ω I)
    (C := η⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1))
    (Filter.Eventually.of_forall fun ω => norm_sample_Lval_le hη hz ω I hwf hn)
  simpa using h

end SampleBridge

/-! ### The generator identity applied to the loop observables -/

section Moment

variable {d : Dims} {N : ℕ}

/-- `∂_ij ∂_ji Φ` along the flow is integrable. -/
theorem integrable_wirtSecond {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : TestFun d N Φ)
    (u : ℝ) (i j : d.Idx N) :
    Integrable (fun ω : Ω d => wirtSecond d N Φ (Hflow d N u ω) i j) (P d) := by
  by_cases hij : i = j
  · subst hij
    have hfun : (fun ω : Ω d => wirtSecond d N Φ (Hflow d N u ω) i i)
        = fun ω : Ω d => coordD2 d N Φ (Hflow d N u ω) (i, i, true) := by
      funext ω; simp [wirtSecond]
    rw [hfun]
    exact integrable_coordD2 h u (i, i, true)
  · simp only [wirtSecond, ite_eq_right hij]
    exact (Integrable.smul ((1 : ℝ) / 4) ((integrable_coordD2 h u (i, j, true)).add
      (integrable_coordD2 h u (i, j, false))) :
      Integrable (fun ω : Ω d => ((1 : ℝ) / 4) •
        (coordD2 d N Φ (Hflow d N u ω) (i, j, true)
          + coordD2 d N Φ (Hflow d N u ω) (i, j, false))) (P d))

/-- **The loop hierarchy in moment form, raw shape.** -/
theorem hasDerivAt_integral_gloop (hst : MatrixStein d) {z : ℂ}
    {I : LoopIdx (ZMod (d.L N))} (h : TestFun d N (loopObs d N z I)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => ∫ ω, gloop (d.L N) (d.W N) (Hflow d N v ω) z I ∂(P d))
      ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        ∫ ω, wirtSecond d N (loopObs d N z I) (Hflow d N u ω) i j ∂(P d)) u := by
  have key := hasDerivAt_integral_Phi_pairs hst h hu
  simpa only [loopObs_Hflow] using key

/-- Moving the finite index sum of the generator identity inside the expectation. -/
theorem integral_sum_wirtSecond {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : TestFun d N Φ)
    (u : ℝ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d)
      = ∫ ω, (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d) := by
  have hint : ∀ i j : d.Idx N, Integrable
      (fun ω : Ω d => Sblk (d.L N) (d.W N) i j • wirtSecond d N Φ (Hflow d N u ω) i j) (P d) :=
    fun i j => (Integrable.smul (Sblk (d.L N) (d.W N) i j) (integrable_wirtSecond h u i j) :
      Integrable (fun ω : Ω d =>
        Sblk (d.L N) (d.W N) i j • wirtSecond d N Φ (Hflow d N u ω) i j) (P d))
  have hinner : ∀ i : d.Idx N,
      ∫ ω, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d)
        = ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
            ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d) := by
    intro i
    rw [integral_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => integral_smul _ _
  rw [integral_smul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => (hinner i).symm)

/-- **The `Ẽ` term (2.47)** of Lemma 2.11, written out in the loop vocabulary of
`RBM1D/Loop/Index.lean`:

`E^{(G̃)}_{σ,a} = W ∑_{1 ≤ k ≤ n} ∑_{a,b} ⟨G̃(σ_k) E_a⟩ · S^(B)_{ab} · L_{G^{(b)}_k (σ,a)}`,
`G̃(σ) = G(σ) - m(σ)`,

with `G^{(b)}_k` the single cut-and-glue operator `RBM.LoopIdx.cutGlue` of Definition 2.10 (1).
This definition is **not used** by any theorem below: the hypothesis `RBM.Gauss.LoopIto` keeps
its `Ẽ` term abstract, exactly as `RBM.Hierarchy`'s drift `F` does.  It is recorded here to pin
down the intended instantiation for whoever discharges `LoopIto`. -/
noncomputable def eGterm (L W : ℕ) [NeZero L] [NeZero W] (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
        - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      * Eblk L W a) * SB L a b * gloop L W M z (I.cutGlue k b)

/-- **Lemma 2.11 in moment form: the deterministic second-order identity.** -/
structure LoopIto (d : Dims) (N : ℕ) (z : ℂ) where
  /-- The `Ẽ` term (2.47). -/
  EG : Matrix (d.Idx N) (d.Idx N) ℂ → LoopIdx (ZMod (d.L N)) → ℂ
  /-- The generator's second-order term splits as in (2.45). -/
  second : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
    ∀ I : LoopIdx (ZMod (d.L N)), I.WF → 1 ≤ I.a.length →
      (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          wirtSecond d N (loopObs d N z I) M i j
        = EG M I + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) I

/-- **The loop hierarchy in moment form, the paper's shape.** -/
theorem hasDerivAt_integral_gloop_hierarchy (hst : MatrixStein d) {z : ℂ}
    (hito : LoopIto d N z) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (h : TestFun d N (loopObs d N z I)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => ∫ ω, gloop (d.L N) (d.W N) (Hflow d N v ω) z I ∂(P d))
      (∫ ω, (hito.EG (Hflow d N u ω) I
        + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) (Hflow d N u ω) z) I) ∂(P d)) u := by
  have key := hasDerivAt_integral_gloop hst h hu
  rw [integral_sum_wirtSecond h u] at key
  refine key.congr_deriv ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact hito.second _ (Hflow_isHermitian d N u ω) I hwf hn

/-- **The loop hierarchy in moment form, in the vocabulary of `RBM1D/Flow/Hypotheses.lean`.**

Same statement as `RBM.Gauss.hasDerivAt_integral_gloop_hierarchy` with the spectral parameter
frozen at `z_u = z_t^{(E)}|_{t = u}` and the quadratic term written with `RBM.Sample.Lval` of
the moment-route sample.  **At the base point `v = u` the differentiated function is exactly
`RBM.Sample.ELval E N u I`** (`RBM.Gauss.sample_ELval`); away from it the spectral parameter
stays at `z_u` while the matrix flows — see the module docstring for what this frozen reading
does and does not give. -/
theorem hasDerivAt_integral_Lval_hierarchy (hst : MatrixStein d) {E : ℝ} {u : ℝ}
    (hito : LoopIto d N (zt E u)) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF)
    (hn : 1 ≤ I.a.length) (h : TestFun d N (loopObs d N (zt E u) I)) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => ∫ ω, gloop (d.L N) (d.W N) (Hflow d N v ω) (zt E u) I ∂(P d))
      (∫ ω, (hito.EG (Hflow d N u ω) I
        + primRhs (d.L N) (d.W N) ((sample d).Lval E N u ω) I) ∂(P d)) u :=
  hasDerivAt_integral_gloop_hierarchy hst hito hwf hn h hu

end Moment

end RBM.Gauss
