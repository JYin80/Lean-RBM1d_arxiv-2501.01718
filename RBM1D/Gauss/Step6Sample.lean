/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6DriftEG
import RBM1D.Gauss.Step6Hyp
import RBM1D.Gauss.SteinMatrix
import RBM1D.Gauss.LoopIto
import RBM1D.Flow.Initial
import RBM1D.Flow.Iteration

/-!
# The sample side of Step 6, and the time quantifier of its envelope hypotheses

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8 ((5.126)–(5.136)) and §2.7 ((2.71), (2.80)).

The second pass of Theorem 2.21 — propagating (2.71) itself, which is what feeds (2.62) and
hence the expectation bounds (2.8), (2.9) of Theorem 2.4 and Theorem 2.5 — goes through Step 6.
This file supplies two sample-side inputs of Step 6 for the Gaussian model `RBM.Gauss.sample`.

## Why Step 6's envelope is read on the window

A deterministic polynomial envelope of the drift integrands that quantifies the *time* `v` over
**all of `ℝ`**, rather than over the window `[s_N, t_N]`, does not exist.  At the energy `E = 0`
and the sample point `ω = 0` (where `H_v = 0` for every `v`, since `H_v = √v · X`), as `v ↑ 1`
the spectral parameter `z_v = (1-v) i` tends to `0`, so the resolvent of `H_v = 0` is
`(1-v)⁻¹ i` and the integrand of (5.131) is the *real* number `2 (w⁻¹ - 1) w⁻³ / W` with
`w = 1 - v`, which is unbounded.  There is no cancellation to rescue it: the whole `a`, `b` sum
collapses through `∑_a S^{(B)}_{a a₀} = 1` (`RBM.SumZeroDyn.sum_SB_col`) and both `k = 1, 2`
terms are equal.  Since Theorems 2.4/2.5 quantify over all `|E| ≤ 2 - κ`, the (2.71) induction
reads the envelope, the measurability in `ω` and the integrability of the `1`-loop only at
window times; see `RBM1D/Gauss/Step6EnvWindow.lean`.

## Main results (§3)

* `RBM.Gauss.hEL_gauss` — `∂_v E L_{v,σ,a}` is the integrated generator.  This
  is `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` fed with
  `RBM.Gauss.differentiableAt_integral_gloop_flow` and `RBM.Gauss.matrixStein`;
  the ball radius is `ε = (1-v)/2` and the floor is `η = ε · Im m^{(E)}`.  No new hypothesis.
* `RBM.Gauss.hintL2_gauss` — the integrability of the `2`-loop, from
  `RBM.Gauss.integrable_sample_Lval`.

Both are quantified over `0 < v < 1`, so the window question above does not arise for them.
-/

open MeasureTheory Filter Matrix

namespace RBM.Gauss

open RBM Finset

/-! ### §1  The sample point `ω = 0` and the loops there

`H_v(0) = √v · X(0) = 0` for every `v`, so the resolvent is the scalar `(-z_v)⁻¹` and every
loop can be evaluated in closed form with the tools of `RBM1D/Flow/Initial.lean`. -/

section ZeroPoint

variable (d : Dims) (N : ℕ)

end ZeroPoint

section ZeroLoops

variable {L W : ℕ} [NeZero L] [NeZero W]

end ZeroLoops

/-! ### §2  The envelope on all of `ℝ`

The loop `I = ((+,+), (a₀,a₀))` is the one of the computation in the module docstring;
`RBM.LoopIdx.cutGlue` at `k = 1, 2` turns it into the two `3`-loops that the second slot of
`RBM.Decay.eG` reads. -/

section EGShape

end EGShape

/-! ### §3  The Step 6 slots that *are* producible for the Gaussian model

These two are quantified over `0 < v < 1`, so they are not touched by §2. -/

section Analytic

/-- **`∂_v E L_{v,σ,a}` is the integrated generator, for the Gaussian model.**

`RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` needs a ball around `v` on which
`|Im z| ≥ η`; on `|q - v| < (1-v)/2` one has `1 - q > (1-v)/2`, so `η := ((1-v)/2)·Im m^{(E)}`
works.  `hjoint` is `RBM.Gauss.differentiableAt_integral_gloop_flow` and the Stein
hypothesis is the proved `RBM.Gauss.matrixStein`. -/
theorem hEL_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      HasDerivAt (fun q : ℝ => (sample d).ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm ((band d).L N) ((band d).W N) (mSigma E)
              ((sample d).H N v ω) (zt E v) (LoopData.idx (σ, b))
            + primRhs ((band d).L N) ((band d).W N) ((sample d).Lval E N v ω)
              (LoopData.idx (σ, b))) ∂(band d).P) v := by
  intro N v hv0 hv1 σ b
  have hm : 0 < (mE E).im := mE_im_pos hE
  set ε : ℝ := (1 - v) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set η : ℝ := ε * (mE E).im with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hball : ∀ q ∈ Metric.ball v ε, η ≤ |(zt E q).im| := by
    intro q hq
    rw [Metric.mem_ball, Real.dist_eq] at hq
    have hq1 : q < 1 := by
      have := (abs_lt.mp hq).2; rw [hεdef] at this; linarith
    rw [← etaT_eq_zt_im, abs_of_pos (etaT_pos hE hq1), etaT, hηdef]
    have : ε ≤ 1 - q := by
      have := (abs_lt.mp hq).2; rw [hεdef] at this ⊢; linarith
    exact mul_le_mul_of_nonneg_right this hm.le
  have hwf : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hn : 1 ≤ (LoopData.idx (σ, b)).a.length := by
    show 1 ≤ (List.ofFn b).length
    rw [List.length_ofFn]
    norm_num
  exact hasDerivAt_sample_ELval_hierarchy_gauss (matrixStein d) hv0 hη hε hball hwf hn
    (differentiableAt_integral_gloop_flow d N hv0 hη hε hball hwf hn).hasFDerivAt

/-- **The `2`-loop is integrable**, from `RBM.Gauss.integrable_sample_Lval`. -/
theorem hintL2_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      Integrable (fun ω => (sample d).Lval E N v ω (LoopData.idx (σ, b))) (band d).P := by
  intro N v _ hv1 σ b
  have hn : 1 ≤ (LoopData.idx (σ, b)).a.length := by
    show 1 ≤ (List.ofFn b).length
    rw [List.length_ofFn]
    norm_num
  exact integrable_sample_Lval (etaT_pos_of_lt_one hE hv1) (abs_im_zt E hE hv1).ge
    (LoopData.idx (σ, b)) (LoopData.idx_wf _) hn

end Analytic

end RBM.Gauss

/-! ### §4  The (2.71) half of the induction step -/

namespace RBM

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end Assembly

end RBM

namespace RBM.Gauss

open RBM

section Witness

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

end Witness

end RBM.Gauss

