/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridQVForm
import RBM1D.Gauss.GridExpansion

/-!
# The complex-valued `Z`/`Y` decomposition and the `E⊗E` tensor

A one-step `Z`/`Y` decomposition of a **complex-valued** loop observable family,
transported by a **complex** kernel `U` (needed for a general charge sequence `σ` — non-alternating
`σ` gives complex edges `ξ = m(σ_i)m(σ_{i+1})`), and the Hermitian `E⊗E` tensor `eeHerm` (the
polarization of `vC`, the conditional variance of the whole complex increment).

## Why no `hReal`

`stepDecomp` needs `Φ` real on the Hermitian submanifold and `U` real (`hReal`): this is needed
only to keep the exactly-linear part `Z` **real**
(so that the remainder `Y` stays `O(Δ‖X‖²)` and does not pick up the uncancelled imaginary part
of the first-order Taylor term). Since `RBM.Gauss.Grid.fderiv_eq_trace_gradMat` /
`RBM.Gauss.Grid.lin_eq_fderiv` are already **unconditional** (no
`hReal` anywhere), this file instead lets `Z` be the *whole* complex first-order term: its real
part is `lin N (AbC ω) X` and its imaginary part is `lin N ((-I)•AbC ω) X` (a short algebraic fact,
`lin N ((-I)•A) X = (trace(A·X)).im`), so no information is ever pushed into `Y`, and no reality
hypothesis on `Φ` or `U` is ever needed.

## Main declarations

* `RBM.Gauss.Grid.AbC`, `RBM.Gauss.Grid.stepZC`, `RBM.Gauss.Grid.stepXiC`, `RBM.Gauss.Grid.stepYC`
  — the complex analogues of `Ab`/`stepZ`/`stepXi`/`stepY`, for a general loop length `n`,
  a complex label family `Φ`, and a complex kernel `U`. `RBM.Gauss.Grid.stepDecompC` packages the
  decomposition exactly as `stepDecomp` does. `RBM.Gauss.Grid.condExp_stepZC_eq_zero` and
  `RBM.Gauss.Grid.stepDecompC_ZC_subG` supply the two facts `azuma_complex`
  (`Gauss/GridAzuma.lean`) needs of `Z`'s real and imaginary parts.
* `RBM.Gauss.Grid.ukerMatC`, `RBM.Gauss.Grid.stepZC_ukerMatC_eq_Uker`,
  `RBM.Gauss.Grid.stepYC_ukerMatC_eq_Uker_ae` — the complex-kernel analogues of
  `ukerMat`/`stepZ_ukerMat_eq_Uker`/`stepY_ukerMat_eq_Uker_ae`, *without* the `3 ≤ L`/
  `0 ≤ u ≤ v < 1` side conditions of `ukerMat` (those are only needed to identify a real
  kernel's *real part* with itself; a genuinely complex kernel needs no such identification).
* `RBM.Gauss.Grid.integrable_stepZC_re_of_testFun`, `RBM.Gauss.Grid.integrable_stepZC_im_of_testFun`
  — the integrability hypotheses of `stepDecompC` are dischargeable.
* `RBM.Gauss.Grid.vC`, `RBM.Gauss.Grid.vC_eq_sum_abs_sq`, `RBM.Gauss.Grid.eeHerm`,
  `RBM.Gauss.Grid.vC_sum_eq_eeHerm`, `RBM.Gauss.Grid.v_le_vC`, `RBM.Gauss.Grid.v_neg_I_le_vC`,
  `RBM.Gauss.Grid.vC_sum_le` — the Hermitian E⊗E tensor for complex weights.
* `RBM.Gauss.Grid.ΦgridG`, `RBM.Gauss.Grid.ΦgridG_testFun`, `RBM.Gauss.Grid.ΦgridG_bdd2`,
  `RBM.Gauss.Grid.testFun_sum`, `RBM.Gauss.Grid.testFun_linComb` — the general-`n`/`σ` analogue of
  `Φgrid`, and `TestFun` closure under finite ℂ-linear label combinations.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal MeasureTheory Matrix.Norms.L2Operator ComplexConjugate

/-! ## T1 : the complex `Z`/`Y` decomposition -/

section StepDecompC

variable {d : Dims} {N : ℕ}

/-- **`AbC`**: the `filt d j`-measurable direction attached to a label-indexed **complex** test
function family `Φ`, a **complex** kernel `U`, and a target label `b`:
`AbC ω := Σ_a U(b,a) • gradMat (Φ a) (H_j ω)`. Unlike `Ab`, `U` is genuinely complex-valued
(no real cast). -/
noncomputable def AbC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  ∑ a : LoopArg (d.L N) n, U b a • gradMat (Φ a) (H d s t K N j ω)

/-- **`stepZC_re`**: the real part of the complex linear term, `√Δ · lin N (AbC ω) X`. -/
noncomputable def stepZC_re (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) : ℝ :=
  Real.sqrt (step s t K N) * lin N (AbC d s t K N j n Φ U b ω) (Xmat d N (ω (j + 1)))

/-- **`stepZC_im`**: the imaginary part of the complex linear term,
`√Δ · lin N ((-I)•AbC ω) X`; this equals `√Δ · (trace(AbC ω · X)).im`
(`lin_neg_I_smul_eq_im` below). -/
noncomputable def stepZC_im (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) : ℝ :=
  Real.sqrt (step s t K N) *
    lin N ((-Complex.I) • AbC d s t K N j n Φ U b ω) (Xmat d N (ω (j + 1)))

/-- **`stepZC`**: the exactly-linear part of one grid step,
`Z^C = stepZC_re + I•stepZC_im`. By construction, `Z^C`'s real and imaginary parts are each
of the exact shape
`hasCondSubgaussianMGF_linear` (`GridMarkov.lean`) consumes. -/
noncomputable def stepZC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) : ℂ :=
  (stepZC_re d s t K N j n Φ U b ω : ℂ) + Complex.I * (stepZC_im d s t K N j n Φ U b ω : ℂ)

/-- **`stepXiC`**: the observable minus its own conditional mean, complex `U`. -/
noncomputable def stepXiC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) : ℂ :=
  (∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω))
    - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω')
        | filt d j] ω

/-- **`stepYC`**: the remainder, `Y^C = ξ^C − Z^C`. -/
noncomputable def stepYC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) : ℂ :=
  stepXiC d s t K N j n Φ U b ω - stepZC d s t K N j n Φ U b ω

/-- **The key algebraic fact behind (T1)**: `lin` at the direction `(-I)•A` reads the *imaginary*
part of `trace(A·X)`. Combined with `lin N A X = (trace(A·X)).re` (`lin`'s own definition), this is
where `stepZC` recombines into the whole complex first-order term, without any reality
hypothesis. -/
theorem lin_neg_I_smul_eq_im (A X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold lin
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- `AbC` is `filt d j`-measurable. -/
theorem measurable_AbC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ)
    (b : LoopArg (d.L N) n) :
    Measurable[filt d j] (fun ω : Ωg d => AbC d s t K N j n Φ U b ω) := by
  have hHmeas : Measurable[filt d j] (fun ω : Ωg d => H d s t K N j ω) :=
    H_measurable_filt d s t K N j
  have hgradCont : ∀ a, Continuous (gradMat (Φ a)) := by
    intro a
    apply continuous_pi; intro i; apply continuous_pi; intro k
    unfold gradMat wirtFirst
    simp only [Matrix.of_apply]
    split_ifs
    · exact (hΦ a).continuous_fderiv.clm_apply continuous_const
    · exact (((hΦ a).continuous_fderiv.clm_apply continuous_const).sub
        ((continuous_const).mul ((hΦ a).continuous_fderiv.clm_apply continuous_const))).const_smul
        (2⁻¹ : ℂ)
  exact Finset.measurable_sum _ fun a _ =>
    (((hgradCont a).measurable.comp hHmeas)).const_smul (U b a)

/-- **The complex algebraic bridge behind (T1)**: `AbC`-weighted sum of directional derivatives is
`stepZC`, unconditionally (no reality hypothesis `hReal` of `stepDecomp`, no reality of `U`). -/
theorem sum_fderivC_eq_stepZC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) :
    (Real.sqrt (step s t K N) : ℂ) *
      (∑ a : LoopArg (d.L N) n, U b a *
        fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))))
      = stepZC d s t K N j n Φ U b ω := by
  have hXherm := Xmat_isHermitian d N (ω (j + 1))
  have hcomb : (∑ a : LoopArg (d.L N) n, U b a *
      fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))))
      = Matrix.trace (AbC d s t K N j n Φ U b ω * Xmat d N (ω (j + 1))) := by
    unfold AbC
    rw [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, fderiv_eq_trace_gradMat _ hXherm]
  rw [hcomb]
  set w := Matrix.trace (AbC d s t K N j n Φ U b ω * Xmat d N (ω (j + 1))) with hw
  have hre : lin N (AbC d s t K N j n Φ U b ω) (Xmat d N (ω (j + 1))) = w.re := rfl
  have him : lin N ((-Complex.I) • AbC d s t K N j n Φ U b ω) (Xmat d N (ω (j + 1))) = w.im :=
    lin_neg_I_smul_eq_im _ _
  unfold stepZC stepZC_re stepZC_im
  rw [hre, him]
  have hreim := Complex.re_add_im w
  push_cast
  linear_combination (Real.sqrt (step s t K N) : ℂ) * hreim.symm

/-- **The pointwise identity behind (T1)**: `Σ_a U(b,a)·Φ_a(H_{j+1})` splits into the
`F_j`-measurable "self" term, `stepZC`, and the `U`-weighted Taylor remainder. -/
theorem g_eq_pointwiseC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) :
    (∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω))
      = (∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N j ω))
        + stepZC d s t K N j n Φ U b ω
        + ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω := by
  have hZ := sum_fderivC_eq_stepZC d s t K N j n U b ω (Φ := Φ)
  have hexpand : ∀ a : LoopArg (d.L N) n,
      U b a * Φ a (H d s t K N (j + 1) ω)
        = U b a * Φ a (H d s t K N j ω)
          + (Real.sqrt (step s t K N) : ℂ) *
              (U b a * fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))))
          + U b a * Rlabel d s t K N j (Φ a) ω := by
    intro a
    have hR : Rlabel d s t K N j (Φ a) ω
        = Φ a (H d s t K N (j + 1) ω) - Φ a (H d s t K N j ω)
          - (Real.sqrt (step s t K N) : ℂ) *
            fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))) := by
      unfold Rlabel; rw [Complex.real_smul]
    rw [hR]; ring
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hZ]

/-- `h0C := Σ_a U(b,a)·Φ_a(H_jω)` is `filt d j`-measurable. -/
theorem measurable_h0C (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Measurable[filt d j]
      (fun ω : Ωg d => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N j ω)) := by
  have hHm : Measurable[filt d j] (fun ω : Ωg d => H d s t K N j ω) :=
    H_measurable_filt d s t K N j
  exact Finset.measurable_sum _ fun a _ =>
    Measurable.const_mul (((hΦ a).contDiff.continuous.measurable.comp hHm)) (U b a)

/-- `Σ_a U(b,a)·Φ_a(H_jω)`, with a complex kernel `U`, is integrable. -/
theorem integrable_h0C (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Integrable
      (fun ω : Ωg d => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N j ω)) (Pg d) :=
  integrable_finsetSum _ fun a _ =>
    (integrable_Phi_H d s t K N j (hΦ a)).const_mul (U b a)

/-- **The pathwise bound on the `U`-weighted sum of Taylor remainders**, complex `U`. -/
theorem norm_RlabelC_sum_le (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) :
    ‖∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω‖
      ≤ (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
        * ‖Xmat d N (ω (j + 1))‖ ^ 2 := by
  calc ‖∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω‖
      ≤ ∑ a : LoopArg (d.L N) n, ‖U b a * Rlabel d s t K N j (Φ a) ω‖ := norm_sum_le _ _
    _ = ∑ a : LoopArg (d.L N) n, ‖U b a‖ * ‖Rlabel d s t K N j (Φ a) ω‖ := by
        refine Finset.sum_congr rfl fun a _ => norm_mul _ _
    _ ≤ ∑ a : LoopArg (d.L N) n,
          ‖U b a‖ * ((C₂ / 2) * step s t K N * ‖Xmat d N (ω (j + 1))‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (norm_Rlabel_le d s t K N j (hΦ a) (hC₂ a) hΔ ω)
          (norm_nonneg _)
    _ = (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
          * ‖Xmat d N (ω (j + 1))‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- **The `U`-weighted sum of Taylor remainders is integrable**, complex `U`. -/
theorem integrable_RlabelC_sum (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Integrable (fun ω : Ωg d => ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω)
      (Pg d) := by
  have hcont : Continuous (fun ω : Ωg d =>
      ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω) :=
    continuous_finsetSum _ fun a _ =>
      continuous_const.mul (continuous_Rlabel d s t K N j (hΦ a))
  have hgint : Integrable (fun ω : Ωg d =>
      (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
        * ‖Xmat d N (ω (j + 1))‖ ^ 2) (Pg d) :=
    (integrable_normSq_incr d N j).const_mul _
  exact hgint.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => norm_RlabelC_sum_le d s t K N j n hΦ hC₂ hΔ U b ω)

/-- `stepZC`, as a complex-valued function, is integrable given integrability of its real and
imaginary parts. -/
theorem integrable_stepZC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (hIntRe : Integrable (stepZC_re d s t K N j n Φ U b) (Pg d))
    (hIntIm : Integrable (stepZC_im d s t K N j n Φ U b) (Pg d)) :
    Integrable (stepZC d s t K N j n Φ U b) (Pg d) := by
  have h1 : Integrable (fun ω => (stepZC_re d s t K N j n Φ U b ω : ℂ)) (Pg d) := hIntRe.ofReal
  have h2 : Integrable (fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ)) (Pg d) := hIntIm.ofReal
  have h3 : Integrable (fun ω => Complex.I * (stepZC_im d s t K N j n Φ U b ω : ℂ)) (Pg d) :=
    h2.const_mul Complex.I
  have heq : stepZC d s t K N j n Φ U b
      = (fun ω => (stepZC_re d s t K N j n Φ U b ω : ℂ))
        + (fun ω => Complex.I * (stepZC_im d s t K N j n Φ U b ω : ℂ)) := by
    funext ω; rfl
  rw [heq]; exact h1.add h3

/-- **`Z^C` has conditional mean zero.** Follows from `condExp_linear_eq_zero` applied to
the real direction `AbC` and to `(-I)•AbC`, then recombined via `condExp_add`/`condExp_smul`. -/
theorem condExp_stepZC_eq_zero (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (hIntRe : Integrable (stepZC_re d s t K N j n Φ U b) (Pg d))
    (hIntIm : Integrable (stepZC_im d s t K N j n Φ U b) (Pg d)) :
    (Pg d)[stepZC d s t K N j n Φ U b | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) := by
  have hAmeas := measurable_AbC d s t K N j n hΦ U b
  have hAmeas' : Measurable[filt d j]
      (fun ω => (-Complex.I) • AbC d s t K N j n Φ U b ω) := hAmeas.const_smul (-Complex.I)
  have hrealRe : (Pg d)[stepZC_re d s t K N j n Φ U b | filt d j] =ᵐ[Pg d] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K N j hAmeas Set.univ MeasurableSet.univ
      (show Integrable (fun ω => Real.sqrt (step s t K N)
        * lin N (AbC d s t K N j n Φ U b ω) (Xmat d N (ω (j + 1)))) (Pg d) from hIntRe)
    rwa [Set.indicator_univ] at h
  have hrealIm : (Pg d)[stepZC_im d s t K N j n Φ U b | filt d j] =ᵐ[Pg d] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K N j hAmeas' Set.univ MeasurableSet.univ
      (show Integrable (fun ω => Real.sqrt (step s t K N)
        * lin N ((-Complex.I) • AbC d s t K N j n Φ U b ω) (Xmat d N (ω (j + 1)))) (Pg d)
        from hIntIm)
    rwa [Set.indicator_univ] at h
  have hliftRe := ContinuousLinearMap.comp_condExp_comm (μ := Pg d) (m := filt d j)
    hIntRe Complex.ofRealCLM
  have hliftRe' : (fun ω => ((Pg d)[stepZC_re d s t K N j n Φ U b | filt d j] ω : ℂ))
      =ᵐ[Pg d] (Pg d)[fun ω => (stepZC_re d s t K N j n Φ U b ω : ℂ) | filt d j] := by
    simpa [Function.comp_def] using hliftRe
  have hliftIm := ContinuousLinearMap.comp_condExp_comm (μ := Pg d) (m := filt d j)
    hIntIm Complex.ofRealCLM
  have hliftIm' : (fun ω => ((Pg d)[stepZC_im d s t K N j n Φ U b | filt d j] ω : ℂ))
      =ᵐ[Pg d] (Pg d)[fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ) | filt d j] := by
    simpa [Function.comp_def] using hliftIm
  have hReC : (Pg d)[fun ω => (stepZC_re d s t K N j n Φ U b ω : ℂ) | filt d j]
      =ᵐ[Pg d] fun _ => (0 : ℂ) := by
    refine hliftRe'.symm.trans ?_
    filter_upwards [hrealRe] with ω hω
    simp [hω]
  have hImC : (Pg d)[fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ) | filt d j]
      =ᵐ[Pg d] fun _ => (0 : ℂ) := by
    refine hliftIm'.symm.trans ?_
    filter_upwards [hrealIm] with ω hω
    simp [hω]
  have heq : stepZC d s t K N j n Φ U b
      = (fun ω => (stepZC_re d s t K N j n Φ U b ω : ℂ))
        + Complex.I • (fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ)) := by
    funext ω; rfl
  rw [heq]
  have hIntImC : Integrable (fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ)) (Pg d) := hIntIm.ofReal
  have hIntReC : Integrable (fun ω => (stepZC_re d s t K N j n Φ U b ω : ℂ)) (Pg d) := hIntRe.ofReal
  have hIntSmul :
      Integrable (Complex.I • (fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ))) (Pg d) :=
    hIntImC.smul Complex.I
  have hAddCond := condExp_add hIntReC hIntSmul (filt d j)
  have hSmulCond := condExp_smul (μ := Pg d) Complex.I
    (fun ω => (stepZC_im d s t K N j n Φ U b ω : ℂ)) (filt d j)
  refine hAddCond.trans ?_
  filter_upwards [hReC, hSmulCond, hImC] with ω h1 h2 h3
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp [h3]

/-- **`ξ^C` a.e. equals `Z^C` plus the `U`-weighted Taylor remainder minus its own conditional
mean.** -/
theorem stepXiC_eq_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (hIntRe : Integrable (stepZC_re d s t K N j n Φ U b) (Pg d))
    (hIntIm : Integrable (stepZC_im d s t K N j n Φ U b) (Pg d)) :
    stepXiC d s t K N j n Φ U b
      =ᵐ[Pg d] fun ω => stepZC d s t K N j n Φ U b ω
        + ((∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω)
          - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) n,
              U b a * Rlabel d s t K N j (Φ a) ω' | filt d j] ω) := by
  set h0 : Ωg d → ℂ := fun ω => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N j ω) with hh0def
  set R : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω with hRdef
  set Zc : Ωg d → ℂ := stepZC d s t K N j n Φ U b with hZcdef
  set g : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω) with hgdef
  have hgeq : g = h0 + Zc + R := funext fun ω => g_eq_pointwiseC d s t K N j n U b ω (Φ := Φ)
  have hh0meas := measurable_h0C d s t K N j n hΦ U b
  have hh0int := integrable_h0C d s t K N j n hΦ U b
  have hZcint := integrable_stepZC d s t K N j n U b hIntRe hIntIm
  have hRint := integrable_RlabelC_sum d s t K N j n hΦ hC₂ hΔ U b
  have hcondg : (Pg d)[g | filt d j]
      =ᵐ[Pg d] (Pg d)[h0 | filt d j] + (Pg d)[Zc | filt d j] + (Pg d)[R | filt d j] := by
    rw [hgeq]
    exact (condExp_add (hh0int.add hZcint) hRint (filt d j)).trans
      ((condExp_add hh0int hZcint (filt d j)).add (EventuallyEq.refl _ _))
  have hh0cond : (Pg d)[h0 | filt d j] =ᵐ[Pg d] h0 := by
    rw [condExp_of_stronglyMeasurable ((filt d).le j) hh0meas.stronglyMeasurable hh0int]
  have hZccond : (Pg d)[Zc | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) :=
    condExp_stepZC_eq_zero d s t K N j n hΦ U b hIntRe hIntIm
  have hstepXi : stepXiC d s t K N j n Φ U b = fun ω => g ω - (Pg d)[g | filt d j] ω := rfl
  rw [hstepXi]
  filter_upwards [hcondg, hh0cond, hZccond] with ω hω1 hω2 hω3
  have hω1' : (Pg d)[g | filt d j] ω = h0 ω + (Pg d)[R | filt d j] ω := by
    rw [hω1]; simp only [Pi.add_apply, hω2, hω3, add_zero]
  rw [hω1']
  have hgω : g ω = h0 ω + Zc ω + R ω := by rw [hgeq]; rfl
  rw [hgω]
  ring

/-- **`Y^C` a.e. equals the `U`-weighted Taylor remainder minus its own conditional mean.** -/
theorem stepYC_eq_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (hIntRe : Integrable (stepZC_re d s t K N j n Φ U b) (Pg d))
    (hIntIm : Integrable (stepZC_im d s t K N j n Φ U b) (Pg d)) :
    stepYC d s t K N j n Φ U b
      =ᵐ[Pg d] fun ω => (∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω)
        - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) n,
            U b a * Rlabel d s t K N j (Φ a) ω' | filt d j] ω := by
  have hXi := stepXiC_eq_ae d s t K N j n hΦ hC₂ hΔ U b hIntRe hIntIm
  filter_upwards [hXi] with ω hω
  show stepXiC d s t K N j n Φ U b ω - stepZC d s t K N j n Φ U b ω = _
  rw [hω]; ring

set_option maxHeartbeats 4000000 in
-- this lemma chains several `set`-bound local `condExp` targets through `calc`; the default
-- heartbeat budget is not enough for the kernel to re-check the resulting elaborated term.
/-- **The pathwise `L²`-bound on `Y^C`, a.e.** -/
theorem stepYC_norm_le_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (hIntRe : Integrable (stepZC_re d s t K N j n Φ U b) (Pg d))
    (hIntIm : Integrable (stepZC_im d s t K N j n Φ U b) (Pg d)) :
    ∀ᵐ ω ∂(Pg d), ‖stepYC d s t K N j n Φ U b ω‖
      ≤ (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
          * ‖Xmat d N (ω (j + 1))‖ ^ 2
        + (Pg d)[fun ω' => (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
            * ‖Xmat d N (ω' (j + 1))‖ ^ 2 | filt d j] ω := by
  have hY := stepYC_eq_ae d s t K N j n hΦ hC₂ hΔ U b hIntRe hIntIm
  set R : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω with hRdef
  set g : Ωg d → ℝ := fun ω => (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
      * ‖Xmat d N (ω (j + 1))‖ ^ 2 with hgdef
  have hRnorm : ∀ ω, ‖R ω‖ ≤ g ω := fun ω => norm_RlabelC_sum_le d s t K N j n hΦ hC₂ hΔ U b ω
  have hgint : Integrable g (Pg d) := (integrable_normSq_incr d N j).const_mul _
  have hRint : Integrable R (Pg d) := integrable_RlabelC_sum d s t K N j n hΦ hC₂ hΔ U b
  have hcondRmono : (Pg d)[fun ω => ‖R ω‖ | filt d j] ≤ᵐ[Pg d] (Pg d)[g | filt d j] :=
    condExp_mono hRint.norm hgint (Filter.Eventually.of_forall hRnorm)
  have hnormcond : (fun x => ‖(Pg d)[R | filt d j] x‖) ≤ᵐ[Pg d] (Pg d)[fun x => ‖R x‖ | filt d j] :=
    _root_.norm_condExp_le R
  filter_upwards [hY, hcondRmono, hnormcond] with ω hω h2 h3
  rw [hω]
  calc ‖R ω - (Pg d)[R | filt d j] ω‖
      ≤ ‖R ω‖ + ‖(Pg d)[R | filt d j] ω‖ := norm_sub_le _ _
    _ ≤ g ω + (Pg d)[g | filt d j] ω := add_le_add (hRnorm ω) (le_trans h3 h2)

set_option maxHeartbeats 4000000 in
-- this lemma chains several `set`-bound local `condExp` targets; the default heartbeat budget
-- is not enough for the kernel to re-check the resulting elaborated term.
/-- **`RBM.Gauss.Grid.stepDecompC`.** The pathwise complex `Z`/`Y` decomposition of one grid
step: `ξ^C b ω = Z^C b ω + Y^C b ω` (pointwise, by construction), `AbC` is `filt d j`-measurable,
`Y^C`'s pathwise `L²` bound holds a.e., and `Y^C` has conditional mean zero. No reality
hypothesis of the kind `hReal` of `stepDecomp` appears anywhere. -/
theorem stepDecompC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (hIntRe : Integrable (stepZC_re d s t K N j n Φ U b) (Pg d))
    (hIntIm : Integrable (stepZC_im d s t K N j n Φ U b) (Pg d)) :
    (∀ ω, stepXiC d s t K N j n Φ U b ω
        = stepZC d s t K N j n Φ U b ω + stepYC d s t K N j n Φ U b ω)
      ∧ Measurable[filt d j] (fun ω => AbC d s t K N j n Φ U b ω)
      ∧ (∀ᵐ ω ∂(Pg d), ‖stepYC d s t K N j n Φ U b ω‖
          ≤ (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
              * ‖Xmat d N (ω (j + 1))‖ ^ 2
            + (Pg d)[fun ω' => (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
                * ‖Xmat d N (ω' (j + 1))‖ ^ 2 | filt d j] ω)
      ∧ (Pg d)[stepYC d s t K N j n Φ U b | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) :=
  ⟨fun ω => by unfold stepYC; ring, measurable_AbC d s t K N j n hΦ U b,
    stepYC_norm_le_ae d s t K N j n hΦ hC₂ hΔ U b hIntRe hIntIm,
    by
      have hY := stepYC_eq_ae d s t K N j n hΦ hC₂ hΔ U b hIntRe hIntIm
      have hRint := integrable_RlabelC_sum d s t K N j n hΦ hC₂ hΔ U b
      have hcond : (Pg d)[fun ω => ∑ a : LoopArg (d.L N) n,
          U b a * Rlabel d s t K N j (Φ a) ω
            - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) n,
                U b a * Rlabel d s t K N j (Φ a) ω' | filt d j] ω | filt d j]
          =ᵐ[Pg d] fun _ => (0 : ℂ) := by
        set R : Ωg d → ℂ :=
          fun ω => ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω with hRdef
        have hsub := condExp_sub hRint (integrable_condExp (f := R) (m := filt d j)) (filt d j)
        have hidem : (Pg d)[(Pg d)[R | filt d j] | filt d j] =ᵐ[Pg d] (Pg d)[R | filt d j] :=
          condExp_condExp_of_le (le_refl (filt d j)) ((filt d).le j)
        have hfe : (fun ω => ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω
            - (Pg d)[R | filt d j] ω) = R - (Pg d)[R | filt d j] := by
          funext ω
          show R ω - (Pg d)[R | filt d j] ω = (R - (Pg d)[R | filt d j]) ω
          rw [Pi.sub_apply]
        rw [hfe]
        filter_upwards [hsub, hidem] with ω hω1 hω2
        rw [hω1]
        simp only [Pi.sub_apply]
        rw [hω2]
        ring
      exact (condExp_congr_ae hY).trans hcond⟩

/-- **`RBM.Gauss.Grid.stepDecompC_ZC_subG`.** `stepZC_re`/`stepZC_im` (the real and imaginary parts
of `Z^C`) each satisfy the hypotheses of `hasCondSubgaussianMGF_linear`, with the *same*
deterministic parameter `c` — exactly the pair `azuma_complex` (`GridAzuma.lean`) needs of a single
`Z (i+1)` increment. -/
theorem stepDecompC_ZC_subG (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (E : Set (Ωg d)) (hE : MeasurableSet[filt d j] E) (c : ℝ) (hc : 0 ≤ c)
    (hboundRe : ∀ ω ∈ E, step s t K N * v N (AbC d s t K N j n Φ U b ω) ≤ c)
    (hboundIm : ∀ ω ∈ E, step s t K N * v N ((-Complex.I) • AbC d s t K N j n Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZC_re d s t K N j n Φ U b ω) ω) ⟨c, hc⟩ (Pg d)
    ∧ HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZC_im d s t K N j n Φ U b ω) ω) ⟨c, hc⟩ (Pg d) := by
  refine ⟨?_, ?_⟩
  · have h := hasCondSubgaussianMGF_linear s t K N j (measurable_AbC d s t K N j n hΦ U b) E hE c hc
      hboundRe
    simpa only [stepZC_re] using h
  · have hAmeas' : Measurable[filt d j] (fun ω => (-Complex.I) • AbC d s t K N j n Φ U b ω) :=
      (measurable_AbC d s t K N j n hΦ U b).const_smul (-Complex.I)
    have h := hasCondSubgaussianMGF_linear s t K N j hAmeas' E hE c hc hboundIm
    simpa only [stepZC_im] using h

/-- **`Z^C` is integrable, unconditionally** (for a `TestFun` family with uniform `C₂`, `0 ≤ Δ`, any
complex `U`): `stepZC = g − h0 − R` (`g_eq_pointwiseC`) with all three terms integrable. This makes
the `hIntRe`/`hIntIm` hypotheses of `stepDecompC` dischargeable. -/
theorem integrable_stepZC_of_testFun (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Integrable (stepZC d s t K N j n Φ U b) (Pg d) := by
  have hg : Integrable (fun ω : Ωg d => ∑ a : LoopArg (d.L N) n,
      U b a * Φ a (H d s t K N (j + 1) ω)) (Pg d) :=
    integrable_finsetSum _ fun a _ =>
      (integrable_Phi_H d s t K N (j + 1) (hΦ a)).const_mul (U b a)
  have h0 := integrable_h0C d s t K N j n hΦ U b
  have hR := integrable_RlabelC_sum d s t K N j n hΦ hC₂ hΔ U b
  have heq : stepZC d s t K N j n Φ U b
      = fun ω => (∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω))
        - (∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N j ω))
        - ∑ a : LoopArg (d.L N) n, U b a * Rlabel d s t K N j (Φ a) ω := by
    funext ω
    rw [g_eq_pointwiseC d s t K N j n U b ω (Φ := Φ)]
    ring
  rw [heq]
  exact (hg.sub h0).sub hR

/-- `stepZC_re` is integrable, unconditionally (discharges `hIntRe` of `stepDecompC`). -/
theorem integrable_stepZC_re_of_testFun (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Integrable (stepZC_re d s t K N j n Φ U b) (Pg d) := by
  have h := Complex.reCLM.integrable_comp
    (integrable_stepZC_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [stepZC]

/-- `stepZC_im` is integrable, unconditionally (discharges `hIntIm` of `stepDecompC`). -/
theorem integrable_stepZC_im_of_testFun (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Integrable (stepZC_im d s t K N j n Φ U b) (Pg d) := by
  have h := Complex.imCLM.integrable_comp
    (integrable_stepZC_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [stepZC]

end StepDecompC

/-! ## T2 : linearity through a complex kernel -/

section KernelC

variable {d : Dims} {N : ℕ}

/-- **`gridDeltaC`**: the complex identity kernel on labels. -/
def gridDeltaC (L n : ℕ) (b a : LoopArg L n) : ℂ := if b = a then 1 else 0

/-- **`ukerMatC`**: the complex matrix entry of a general-charge kernel `Uker L ξ u v`, read off
directly (no `.re`, no positivity side condition — unlike `ukerMat`, this loses nothing
for **any** `ξ, u, v`, since `Uker_apply` is unconditional). -/
noncomputable def ukerMatC {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (u v : ℝ)
    (b a : LoopArg L n) : ℂ :=
  ∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (b i) (a i)

/-- **(T2a)**: `Uker L ξ u v A b = Σ_a (ukerMatC ξ u v b a) * A a`, unconditionally. -/
theorem Uker_eq_sum_ukerMatC {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (u v : ℝ)
    (A : LoopArg L n → ℂ) (b : LoopArg L n) :
    Uker L ξ (u : ℂ) (v : ℂ) A b = ∑ a : LoopArg L n, ukerMatC ξ u v b a * A a :=
  Uker_apply L ξ (u : ℂ) (v : ℂ) A b

private theorem stepZC_gridDeltaC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (a : LoopArg (d.L N) n)
    (ω : Ωg d) :
    stepZC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω
      = (Real.sqrt (step s t K N) : ℂ) *
        fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))) := by
  rw [← sum_fderivC_eq_stepZC d s t K N j n (gridDeltaC (d.L N) n) a ω (Φ := Φ)]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp [gridDeltaC]
  · intro c _ hc; simp [gridDeltaC, Ne.symm hc]
  · simp

/-- **`stepZC` is linear in the complex kernel `U`** (pointwise, every `ω`). -/
theorem stepZC_eq_sum_gridDeltaC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) (ω : Ωg d) :
    stepZC d s t K N j n Φ U b ω
      = ∑ a : LoopArg (d.L N) n, U b a * stepZC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω := by
  rw [← sum_fderivC_eq_stepZC d s t K N j n U b ω (Φ := Φ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [stepZC_gridDeltaC]
  ring

/-- **`stepZC_ukerMatC_eq_Uker`**: for every `ω` and **any** `v, w : ℝ`, the kernel folded
into the label weight equals the kernel `Uker L ξ v w` applied to the `k`-independent label vector
`a ↦ stepZC δ a ω`. Unlike `stepZ_ukerMat_eq_Uker`, no `3 ≤ L` or `0 ≤ v ≤ w < 1` hypothesis
is needed. -/
theorem stepZC_ukerMatC_eq_Uker (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (ξ : Fin n → ℂ) (v w : ℝ)
    (b : LoopArg (d.L N) n) (ω : Ωg d) :
    stepZC d s t K N j n Φ (ukerMatC ξ v w) b ω
      = Uker (d.L N) ξ (v : ℂ) (w : ℂ)
          (fun a => stepZC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω) b := by
  rw [Uker_eq_sum_ukerMatC, stepZC_eq_sum_gridDeltaC]

/-- **`stepXiC` is linear in the complex kernel `U`**, a.e., simultaneously for all labels `b`. -/
theorem stepXiC_eq_sum_gridDeltaC_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) :
    ∀ᵐ ω ∂(Pg d), ∀ b : LoopArg (d.L N) n,
      stepXiC d s t K N j n Φ U b ω
        = ∑ a : LoopArg (d.L N) n, U b a * stepXiC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω := by
  have hfun : ∀ a : LoopArg (d.L N) n,
      (fun ω' => ∑ c : LoopArg (d.L N) n,
          gridDeltaC (d.L N) n a c * Φ c (H d s t K N (j + 1) ω'))
        = fun ω' => Φ a (H d s t K N (j + 1) ω') := by
    intro a; funext ω'
    rw [Finset.sum_eq_single a]
    · simp [gridDeltaC]
    · intro c _ hc; simp [gridDeltaC, Ne.symm hc]
    · simp
  have hδ : ∀ a (ω : Ωg d), stepXiC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω
      = Φ a (H d s t K N (j + 1) ω)
        - (Pg d)[fun ω' => Φ a (H d s t K N (j + 1) ω') | filt d j] ω := by
    intro a ω
    have h1 := congrFun (hfun a) ω
    unfold stepXiC
    rw [h1, hfun a]
  refine ae_all_iff.mpr fun b => ?_
  have hint_a : ∀ a ∈ (Finset.univ : Finset (LoopArg (d.L N) n)),
      Integrable (fun ω => U b a * Φ a (H d s t K N (j + 1) ω)) (Pg d) :=
    fun a _ => (integrable_Phi_H d s t K N (j + 1) (hΦ a)).const_mul (U b a)
  have hcondsum := condExp_finsetSum hint_a (filt d j)
  have hsmul_ae : ∀ᵐ ω ∂(Pg d), ∀ a : LoopArg (d.L N) n,
      (Pg d)[fun ω' => U b a * Φ a (H d s t K N (j + 1) ω') | filt d j] ω
        = U b a * (Pg d)[fun ω' => Φ a (H d s t K N (j + 1) ω') | filt d j] ω :=
    ae_all_iff.mpr fun a => condExp_smul (U b a) (fun ω' => Φ a (H d s t K N (j + 1) ω'))
      (filt d j)
  have hsum_fn : (∑ a : LoopArg (d.L N) n,
        fun ω' => U b a * Φ a (H d s t K N (j + 1) ω'))
      = (fun ω' => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω')) := by
    funext ω'; simp only [Finset.sum_apply]
  rw [hsum_fn] at hcondsum
  filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
  simp_rw [hδ]
  unfold stepXiC
  rw [hω1]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => hω2 a]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepYC` is linear in the complex kernel `U`**, a.e., simultaneously for all labels `b`. -/
theorem stepYC_eq_sum_gridDeltaC_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) :
    ∀ᵐ ω ∂(Pg d), ∀ b : LoopArg (d.L N) n,
      stepYC d s t K N j n Φ U b ω
        = ∑ a : LoopArg (d.L N) n, U b a * stepYC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω := by
  filter_upwards [stepXiC_eq_sum_gridDeltaC_ae d s t K N j n hΦ U] with ω hω b
  unfold stepYC
  rw [hω b, stepZC_eq_sum_gridDeltaC d s t K N j n U b ω (Φ := Φ)]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepYC_ukerMatC_eq_Uker_ae`**: for **any** `v, w : ℝ`, a.e. `ω`, for every label `b`,
the kernel folded into the label weight equals `Uker L ξ v w` applied to the `k`-independent label
vector `a ↦ stepYC δ a ω`. -/
theorem stepYC_ukerMatC_eq_Uker_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (ξ : Fin n → ℂ) (v w : ℝ) :
    ∀ᵐ ω ∂(Pg d), ∀ b : LoopArg (d.L N) n,
      stepYC d s t K N j n Φ (ukerMatC ξ v w) b ω
        = Uker (d.L N) ξ (v : ℂ) (w : ℂ)
            (fun a => stepYC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω) b := by
  filter_upwards [stepYC_eq_sum_gridDeltaC_ae d s t K N j n hΦ (ukerMatC ξ v w)] with ω hω b
  rw [hω b, Uker_eq_sum_ukerMatC]

end KernelC

/-! ## The `E⊗E` tensor

**Real `v`.** The literal formula
`v(Σ_b c_b·gradMat(Φ_b)(M)) = Σ_{b,b'} c_b·conj(c_{b'})·T_{b,b'}(M)` with a *single* tensor `T` and
**arbitrary complex** `c_b` is **false** for the real-part variance `v`: `v` is only ℝ-bilinear in
its direction and `v N A ≠ v N (Complex.I • A)` in general.  For `v`, what holds is the
real-coefficient identity and a Cauchy–Schwarz bound.

**Complex `vC`.** The conditional variance of the whole
complex increment `Z^C`, `vC N A := v N A + v N ((-I)•A) = Σ_c gvar(c)·|tr(A X_c)|²`, **is** a
Hermitian form: `vC_sum_eq_eeHerm` expresses `vC(Σ_b c_b A_b)` through the single Hermitian tensor
`eeHerm` (conjugation on the second slot), with the paired/Minkowski bound `vC_sum_le`.
`v_le_vC`/`v_neg_I_le_vC` turn one `vC`
bound into the common `c` for `azuma_complex` (`stepDecompC_ZC_subG_vC`). -/

section EETensor

variable {d : Dims} {N : ℕ}

/-- **`vC`** (T3′): the conditional variance of the whole complex increment `Z^C`,
`vC N A := v N A + v N ((-I)•A)` (real part plus imaginary part). -/
noncomputable def vC (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  v N A + v N ((-Complex.I) • A)

/-- `vC` is nonnegative. -/
theorem vC_nonneg (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : 0 ≤ vC N A :=
  add_nonneg (v_nonneg N A) (v_nonneg N _)

/-- The real-part variance is dominated by `vC`. -/
theorem v_le_vC (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : v N A ≤ vC N A :=
  le_add_of_nonneg_right (v_nonneg N _)

/-- The imaginary-part variance is dominated by `vC`. -/
theorem v_neg_I_le_vC (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    v N ((-Complex.I) • A) ≤ vC N A :=
  le_add_of_nonneg_left (v_nonneg N A)

/-- **`vC_eq_sum_abs_sq`** (T3′): `vC N A = Σ_c gvar(c)·|tr(A·X_c)|²`, `X_c := Xmat(single c 1)`.
Via `lin_neg_I_smul_eq_im`. -/
theorem vC_eq_sum_abs_sq (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    vC N A = ∑ c ∈ coordFinset N,
      (gvar d c : ℝ) * ‖Matrix.trace (A * Xmat d N (Pi.single c 1))‖ ^ 2 := by
  unfold vC v linVar
  push_cast [NNReal.coe_mk]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lin_neg_I_smul_eq_im]
  show (Matrix.trace (A * Xmat d N (Pi.single c 1))).re ^ 2 * (gvar d c : ℝ)
      + (Matrix.trace (A * Xmat d N (Pi.single c 1))).im ^ 2 * (gvar d c : ℝ) = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **`vH`**: the Hermitian (sesquilinear) form on directions,
`vH N A A' := Σ_c gvar(c)·tr(A·X_c)·conj(tr(A'·X_c))`; ℂ-linear in `A`, conjugate-linear in `A'`. -/
noncomputable def vH (N : ℕ) (A A' : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ∑ c ∈ coordFinset N, ((gvar d c : ℝ) : ℂ) * Matrix.trace (A * Xmat d N (Pi.single c 1))
    * conj (Matrix.trace (A' * Xmat d N (Pi.single c 1)))

/-- `vC` is the diagonal of `vH`. -/
theorem vC_eq_vH (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : (vC N A : ℂ) = vH N A A := by
  rw [vC_eq_sum_abs_sq]
  unfold vH
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

private theorem trace_sum_smul_mul {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (A : ι → Matrix (d.Idx N) (d.Idx N) ℂ) (X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Matrix.trace ((∑ b ∈ s, w b • A b) * X) = ∑ b ∈ s, w b * Matrix.trace (A b * X) := by
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- **Sesquilinearity of `vH`**: linear in the first slot, conjugate-linear in the second. -/
theorem vH_sum {ι : Type*} [Fintype ι] (N : ℕ) (w w' : ι → ℂ)
    (A A' : ι → Matrix (d.Idx N) (d.Idx N) ℂ) :
    vH N (∑ b : ι, w b • A b) (∑ b' : ι, w' b' • A' b')
      = ∑ b : ι, ∑ b' : ι, w b * conj (w' b') * vH N (A b) (A' b') := by
  unfold vH
  simp only [trace_sum_smul_mul, map_sum, map_mul]
  have hc : ∀ c : Coord d, ((gvar d c : ℝ) : ℂ)
      * (∑ b : ι, w b * Matrix.trace (A b * Xmat d N (Pi.single c 1)))
      * (∑ b' : ι, conj (w' b') * conj (Matrix.trace (A' b' * Xmat d N (Pi.single c 1))))
      = ∑ b : ι, ∑ b' : ι, w b * conj (w' b') * (((gvar d c : ℝ) : ℂ)
          * Matrix.trace (A b * Xmat d N (Pi.single c 1))
          * conj (Matrix.trace (A' b' * Xmat d N (Pi.single c 1)))) := by
    intro c
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun c _ => hc c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.mul_sum]

/-- **Cauchy–Schwarz for `vH`**: `‖vH A A'‖² ≤ vC A · vC A'`. -/
theorem norm_vH_sq_le (N : ℕ) (A A' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖vH N A A'‖ ^ 2 ≤ vC N A * vC N A' := by
  set f : Coord d → ℝ := fun c =>
    Real.sqrt (gvar d c : ℝ) * ‖Matrix.trace (A * Xmat d N (Pi.single c 1))‖ with hf
  set g : Coord d → ℝ := fun c =>
    Real.sqrt (gvar d c : ℝ) * ‖Matrix.trace (A' * Xmat d N (Pi.single c 1))‖ with hg
  have hsq : ∀ c : Coord d, Real.sqrt (gvar d c : ℝ) * Real.sqrt (gvar d c : ℝ) = (gvar d c : ℝ) :=
    fun c => Real.mul_self_sqrt (gvar d c).2
  have h1 : ‖vH N A A'‖ ≤ ∑ c ∈ coordFinset N, f c * g c := by
    unfold vH
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => le_of_eq ?_)
    have hn : ‖((gvar d c : ℝ) : ℂ)‖ = (gvar d c : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    rw [norm_mul, norm_mul, hn, Complex.norm_conj, hf, hg]
    simp only
    have e := hsq c
    set s := Real.sqrt (gvar d c : ℝ)
    rw [← e]
    ring
  have hf2 : ∑ c ∈ coordFinset N, f c ^ 2 = vC N A := by
    rw [vC_eq_sum_abs_sq]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hf]; simp only
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hg2 : ∑ c ∈ coordFinset N, g c ^ 2 = vC N A' := by
    rw [vC_eq_sum_abs_sq]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hg]; simp only
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg _)]
  calc ‖vH N A A'‖ ^ 2 ≤ (∑ c ∈ coordFinset N, f c * g c) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ c ∈ coordFinset N, f c ^ 2) * ∑ c ∈ coordFinset N, g c ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = vC N A * vC N A' := by rw [hf2, hg2]

/-- **`eeHerm`**: the Hermitian E⊗E tensor
`eeHerm b b' := Σ_c gvar(c)·tr(A_b X_c)·conj(tr(A_{b'} X_c))`, `A_b := gradMat (Φ b) M`.
The conjugation sits on the **second** slot `b'`.  Its relation to the paper's `(E⊗E)` of
(5.22)/(5.23)/(5.25) is `RBM1D/Gauss/EETensorBound.lean`. -/
noncomputable def eeHerm {ι : Type*} (Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (b b' : ι)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  vH N (gradMat (Φ b) M) (gradMat (Φ b') M)

/-- **`vC_sum_eq_eeHerm`** (T3′): for complex weights `c_b`,
`vC(Σ_b c_b • gradMat(Φ_b)(M)) = Σ_{b,b'} c_b · conj(c_{b'}) · eeHerm b b'`. -/
theorem vC_sum_eq_eeHerm {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (c : ι → ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (vC N (∑ b : ι, c b • gradMat (Φ b) M) : ℂ)
      = ∑ b : ι, ∑ b' : ι, c b * conj (c b') * eeHerm Φ b b' M := by
  rw [vC_eq_vH, vH_sum]
  rfl

/-- The diagonal of `eeHerm` is the real number `vC(gradMat Φ_b M)`. -/
theorem eeHerm_self {ι : Type*} (Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (b : ι)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : eeHerm Φ b b M = (vC N (gradMat (Φ b) M) : ℂ) :=
  (vC_eq_vH N _).symm

/-- **Minkowski form, uniform-bound version**: if `vC(A_b) ≤ C` for all `b`, then
`vC(Σ_b w_b • A_b) ≤ (Σ_b ‖w_b‖)² · C`. -/
theorem vC_sum_le_of_le {ι : Type*} [Fintype ι] (A : ι → Matrix (d.Idx N) (d.Idx N) ℂ)
    (w : ι → ℂ) {C : ℝ} (hC : ∀ b, vC N (A b) ≤ C) :
    vC N (∑ b : ι, w b • A b) ≤ (∑ b : ι, ‖w b‖) ^ 2 * C := by
  have hT : ∀ b b', ‖vH N (A b) (A b')‖ ≤ C := by
    intro b b'
    have hCnn : 0 ≤ C := (vC_nonneg N _).trans (hC b)
    have h := norm_vH_sq_le N (A b) (A b')
    have h2 : vC N (A b) * vC N (A b') ≤ C ^ 2 := by
      rw [sq]; exact mul_le_mul (hC b) (hC b') (vC_nonneg N _) hCnn
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hCnn two_ne_zero).1 (h.trans h2)
  have heq : (vC N (∑ b : ι, w b • A b) : ℂ)
      = ∑ b : ι, ∑ b' : ι, w b * conj (w b') * vH N (A b) (A b') := by
    rw [vC_eq_vH, vH_sum]
  have hnn := vC_nonneg N (∑ b : ι, w b • A b)
  calc vC N (∑ b : ι, w b • A b) = ‖(vC N (∑ b : ι, w b • A b) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    _ = ‖∑ b : ι, ∑ b' : ι, w b * conj (w b') * vH N (A b) (A b')‖ := by rw [heq]
    _ ≤ ∑ b : ι, ∑ b' : ι, ‖w b‖ * ‖w b'‖ * C := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hT b b') (by positivity)
    _ = (∑ b : ι, ‖w b‖) ^ 2 * C := by
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]

/-- **`vC_sum_le`** (paired form):
`vC(Σ_b w_b • A_b) ≤ (Σ_b ‖w_b‖)² · max_b vC(A_b)` (`max` as `⨆` over a finite type). -/
theorem vC_sum_le {ι : Type*} [Fintype ι] (A : ι → Matrix (d.Idx N) (d.Idx N) ℂ) (w : ι → ℂ) :
    vC N (∑ b : ι, w b • A b) ≤ (∑ b : ι, ‖w b‖) ^ 2 * ⨆ b, vC N (A b) :=
  vC_sum_le_of_le A w fun b => le_ciSup (f := fun b => vC N (A b)) (Set.finite_range _).bddAbove b

/-- **One `vC` bound gives the common `c` of `azuma_complex`**: a single bound on
`Δ·vC(AbC)` yields both sub-Gaussian conclusions of `stepDecompC_ZC_subG` with the same `c`. -/
theorem stepDecompC_ZC_subG_vC (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    (E : Set (Ωg d)) (hE : MeasurableSet[filt d j] E) (c : ℝ) (hc : 0 ≤ c)
    (hΔ : 0 ≤ step s t K N)
    (hbound : ∀ ω ∈ E, step s t K N * vC N (AbC d s t K N j n Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZC_re d s t K N j n Φ U b ω) ω) ⟨c, hc⟩ (Pg d)
    ∧ HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZC_im d s t K N j n Φ U b ω) ω) ⟨c, hc⟩ (Pg d) :=
  stepDecompC_ZC_subG d s t K N j n hΦ U b E hE c hc
    (fun ω hω => (mul_le_mul_of_nonneg_left (v_le_vC N _) hΔ).trans (hbound ω hω))
    (fun ω hω => (mul_le_mul_of_nonneg_left (v_neg_I_le_vC N _) hΔ).trans (hbound ω hω))

end EETensor

/-! ## Instances (hypothesis-level `TestFun` regularity) -/

section LinearCombination

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **`ΦgridG`**: the general-`n`/`σ`-charge analogue of `Φgrid`, built the same way (the
globally `C²` `loopObs`, agreeing with `Lval − Kv` on the Hermitian submanifold), using
`LoopData.idx (σ,a)` in place of the hard-coded alternating shape `⟨[true,false], List.ofFn a⟩`. -/
noncomputable def ΦgridG (B : Band Ω') (E : ℝ) (N : ℕ) (u : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (a : LoopArg (B.L N) n) (M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ) : ℂ :=
  loopObs B.toDims N (zt E u) (LoopData.idx (σ, a)) M
    - B.Kval E N u (LoopData.idx (σ, a))

/-- `ΦgridG` is a `TestFun`, for `|E| < 2`, `u < 1`, and any nonempty loop length `1 ≤ n`. No
reality hypothesis is needed (unlike `Φgrid_im_eq_zero`, which is specific to the alternating
`σ = (+,-)` charge and is **not** reproved here, matching (T1): no reality hypothesis of the kind
`hReal` of `stepDecomp`). -/
theorem ΦgridG_testFun (B : Band Ω') {E : ℝ} (hEb : |E| < 2) (N : ℕ) {u : ℝ} (hu1 : u < 1)
    {n : ℕ} (hn : 1 ≤ n) (σ : Fin n → Bool) (a : LoopArg (B.L N) n) :
    TestFun B.toDims N (ΦgridG B E N u σ a) := by
  have hzu : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  have hwf : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).WF := LoopData.idx_wf (σ, a)
  have hlen : 1 ≤ (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).a.length := by
    have hlen' : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).a.length = n :=
      List.length_ofFn
    rw [hlen']; exact hn
  have hTF : TestFun B.toDims N (loopObs B.toDims N (zt E u) (LoopData.idx (σ, a))) :=
    testFun_loopObs_of_im_le hzu (abs_pos.mpr hzu) le_rfl hwf hlen
  exact testFun_sub_const hTF (B.Kval E N u (LoopData.idx (σ, a)))

/-- **`hC₂`, an explicit uniform constant** for `ΦgridG`, general `n`. -/
theorem ΦgridG_bdd2 (B : Band Ω') {E : ℝ} (hEb : |E| < 2) (N : ℕ) {u η : ℝ} (hu1 : u < 1)
    (hη : 0 < η) (hzη : η ≤ |(zt E u).im|) {n : ℕ} (σ : Fin n → Bool) (a : LoopArg (B.L N) n)
    (M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ) :
    ‖fderiv ℝ (fderiv ℝ (ΦgridG B E N u σ a)) M‖
      ≤ (Fintype.card (B.toDims.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) := by
  have hzu : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  obtain ⟨h1, h2, h3⟩ := le_two_mul_one_add_inv_cube hη
  have hwf : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).WF := LoopData.idx_wf (σ, a)
  have hbdd := bddC2C_loopObs (d := B.toDims) (N := N) (B := 2 * (1 + η⁻¹) ^ 3) hzu hη hzη h1 h2 h3
    hwf
  have hfd : fderiv ℝ (ΦgridG B E N u σ a)
      = fderiv ℝ (loopObs B.toDims N (zt E u) (LoopData.idx (σ, a))) := by
    funext M'
    show fderiv ℝ (fun M => loopObs B.toDims N (zt E u) (LoopData.idx (σ, a)) M
        - B.Kval E N u (LoopData.idx (σ, a))) M' = _
    exact ((hbdd.differentiable M').hasFDerivAt.sub_const
      (B.Kval E N u (LoopData.idx (σ, a)))).fderiv
  have hlen : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).a.length = n :=
    LoopData.idx_length (σ, a)
  show ‖fderiv ℝ (fderiv ℝ (ΦgridG B E N u σ a)) M‖
      ≤ (Fintype.card (B.toDims.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n)
  rw [hfd]
  simpa [hlen] using hbdd.bdd₂ M

/-- Post-composition by a fixed complex scalar `q` preserves the `TestFun` class (the building
block of `testFun_linComb`, which handles a genuine label-space `Q`). -/
theorem testFun_const_smul {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (h : TestFun d N Φ) (q : ℂ) : TestFun d N (fun M => q • Φ M) := by
  refine ⟨h.contDiff.const_smul q, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bdd₀
    exact ⟨‖q‖ * C, fun M => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC M) (norm_nonneg _)⟩
  · obtain ⟨C, hC⟩ := h.bdd₁
    refine ⟨‖q‖ * C, fun M => ?_⟩
    have hfd : fderiv ℝ (fun M => q • Φ M) M = q • fderiv ℝ Φ M :=
      ((h.differentiable M).hasFDerivAt.const_smul q).fderiv
    rw [hfd, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC M) (norm_nonneg _)
  · obtain ⟨C, hC⟩ := h.bdd₂
    refine ⟨‖q‖ * C, fun M => ?_⟩
    have hfd1 : fderiv ℝ (fun M => q • Φ M) = fun M => q • fderiv ℝ Φ M := by
      funext M'
      exact ((h.differentiable M').hasFDerivAt.const_smul q).fderiv
    rw [hfd1]
    have hfd2 : fderiv ℝ (fun M => q • fderiv ℝ Φ M) M = q • fderiv ℝ (fderiv ℝ Φ) M := by
      have hh : HasFDerivAt (fun M' => fderiv ℝ Φ M') (fderiv ℝ (fderiv ℝ Φ) M) M :=
        (h.differentiable_fderiv M).hasFDerivAt
      exact (hh.const_smul q).fderiv
    rw [hfd2, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC M) (norm_nonneg _)

/-- Second derivative of a finite sum of `TestFun`s. -/
theorem fderiv2_sum_eq {d : Dims} {N : ℕ} {ι : Type*} (s : Finset ι)
    {Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : ∀ i ∈ s, TestFun d N (Φ i))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    fderiv ℝ (fderiv ℝ (fun M => ∑ i ∈ s, Φ i M)) M = ∑ i ∈ s, fderiv ℝ (fderiv ℝ (Φ i)) M := by
  have hfd1 : fderiv ℝ (fun M => ∑ i ∈ s, Φ i M) = fun M => ∑ i ∈ s, fderiv ℝ (Φ i) M :=
    funext fun M => fderiv_fun_sum fun i hi => ((h i hi).differentiable M)
  rw [hfd1]
  exact fderiv_fun_sum fun i hi => ((h i hi).differentiable_fderiv M)

/-- Second derivative of a constant multiple of a `TestFun`. -/
theorem fderiv2_const_smul_eq {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (h : TestFun d N Φ) (q : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    fderiv ℝ (fderiv ℝ (fun M => q • Φ M)) M = q • fderiv ℝ (fderiv ℝ Φ) M := by
  have hfd1 : fderiv ℝ (fun M => q • Φ M) = fun M => q • fderiv ℝ Φ M := by
    funext M'
    exact ((h.differentiable M').hasFDerivAt.const_smul q).fderiv
  rw [hfd1]
  have hh : HasFDerivAt (fun M' => fderiv ℝ Φ M') (fderiv ℝ (fderiv ℝ Φ) M) M :=
    (h.differentiable_fderiv M).hasFDerivAt
  exact (hh.const_smul q).fderiv

/-- **`testFun_sum`** (T4′): `TestFun` is closed under finite sums. -/
theorem testFun_sum {d : Dims} {N : ℕ} {ι : Type*} (s : Finset ι)
    {Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : ∀ i ∈ s, TestFun d N (Φ i)) :
    TestFun d N (fun M => ∑ i ∈ s, Φ i M) := by
  have hfd1 : fderiv ℝ (fun M => ∑ i ∈ s, Φ i M) = fun M => ∑ i ∈ s, fderiv ℝ (Φ i) M :=
    funext fun M => fderiv_fun_sum fun i hi => ((h i hi).differentiable M)
  refine ⟨ContDiff.sum fun i hi => (h i hi).contDiff, ?_, ?_, ?_⟩
  · choose! C hC using fun i (hi : i ∈ s) => (h i hi).bdd₀
    refine ⟨∑ i ∈ s, C i, fun M => ?_⟩
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun i hi => hC i hi M
  · choose! C hC using fun i (hi : i ∈ s) => (h i hi).bdd₁
    refine ⟨∑ i ∈ s, C i, fun M => ?_⟩
    rw [hfd1]
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun i hi => hC i hi M
  · choose! C hC using fun i (hi : i ∈ s) => (h i hi).bdd₂
    refine ⟨∑ i ∈ s, C i, fun M => ?_⟩
    rw [fderiv2_sum_eq s h M]
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun i hi => hC i hi M

/-- **`testFun_linComb`** (T4′): `TestFun` is closed under finite ℂ-linear label combinations. -/
theorem testFun_linComb {d : Dims} {N : ℕ} {ι : Type*} [Fintype ι] (q : ι → ℂ)
    {Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : ∀ i, TestFun d N (Φ i)) :
    TestFun d N (fun M => ∑ i : ι, q i * Φ i M) :=
  testFun_sum Finset.univ (Φ := fun i M => q i • Φ i M) fun i _ => testFun_const_smul (h i) (q i)

/-- `hC₂` for a finite ℂ-linear combination: `‖D²(Σ q_i Φ_i)‖ ≤ (Σ ‖q_i‖) · C`. -/
theorem norm_fderiv2_linComb_le {d : Dims} {N : ℕ} {ι : Type*} [Fintype ι] (q : ι → ℂ)
    {Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : ∀ i, TestFun d N (Φ i)) {C : ℝ}
    (hC : ∀ i M, ‖fderiv ℝ (fderiv ℝ (Φ i)) M‖ ≤ C) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖fderiv ℝ (fderiv ℝ (fun M => ∑ i : ι, q i * Φ i M)) M‖ ≤ (∑ i : ι, ‖q i‖) * C := by
  show ‖fderiv ℝ (fderiv ℝ (fun M => ∑ i ∈ Finset.univ, (fun i M => q i • Φ i M) i M)) M‖ ≤ _
  rw [fderiv2_sum_eq Finset.univ (fun i _ => testFun_const_smul (h i) (q i)) M, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [fderiv2_const_smul_eq (h i) (q i) M, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC i M) (norm_nonneg _)

end LinearCombination

end RBM.Gauss.Grid

end
