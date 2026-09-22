/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeModel

/-!
# Route (A′): the model-layer Duhamel expansion (T275)
-/

namespace RBM

namespace APrimeDuhamelModel

open MeasureTheory Filter Set Real
open Gauss MomentDuhamel
open scoped Matrix.Norms.L2Operator NNReal

variable {d : Gauss.Dims} {N : ℕ} {T : Set ℝ}
  {Ψ Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
  {w : Gauss.Ω d → ℝ} {wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ}

/-- `Y_u(ω) = ‖Ψ₁(u, H_u ω)‖`. -/
noncomputable def flowY (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) (ω : Gauss.Ω d) : ℝ :=
  ‖Ψ₁ u (Gauss.Hflow d N u ω)‖

theorem flowY_nonneg (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) (ω : Gauss.Ω d) :
    0 ≤ flowY d N Ψ₁ u ω := norm_nonneg _

theorem abs_flowY (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) (ω : Gauss.Ω d) :
    |flowY d N Ψ₁ u ω| = flowY d N Ψ₁ u ω := abs_of_nonneg (norm_nonneg _)

/-- The drift part of (★). -/
noncomputable def driftPart (d : Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (w : Gauss.Ω d → ℝ) (u : ℝ) : ℝ :=
  (∫ ω, w ω • Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω) ∂(Gauss.P d)).re

/-- The second-order part of (★). -/
noncomputable def qvPart (d : Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (w : Gauss.Ω d → ℝ) (u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
    (∫ ω, w ω • Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re

/-- The cross part of (★). -/
noncomputable def crossPart (d : Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ)
    (u : ℝ) : ℝ :=
  (1 / (2 * √u)) * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
    (∫ ω, wD q ω • Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re

/-- `φ'` of (G) at the model family. -/
noncomputable def momFlowDeriv (d : Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (w : Gauss.Ω d → ℝ)
    (wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ) (u : ℝ) : ℝ :=
  driftPart d N Ψ w u + qvPart d N Ψ w u + crossPart d N Ψ wD u

/-- The realness bridge: `Ψ` is the `2p`-th power of the modulus of `Ψ₁`. -/
def IsModulusPow (Ψ Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (p : ℕ) : Prop :=
  ∀ u M, Ψ u M = ((‖Ψ₁ u M‖ ^ (2 * p) : ℝ) : ℂ)

theorem smul_Psi_eq {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) (u : ℝ) (ω : Gauss.Ω d) :
    w ω • Ψ u (Gauss.Hflow d N u ω)
      = ((w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) : ℝ) : ℂ) := by
  rw [hre u (Gauss.Hflow d N u ω), Complex.real_smul, ← Complex.ofReal_mul, abs_flowY, flowY]

theorem re_smul_Psi {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) (u : ℝ) (ω : Gauss.Ω d) :
    (w ω • Ψ u (Gauss.Hflow d N u ω)).re = w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) := by
  rw [smul_Psi_eq hre, Complex.ofReal_re]

theorem abs_flowY_pow_eq_norm {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) (u : ℝ) (ω : Gauss.Ω d) :
    |flowY d N Ψ₁ u ω| ^ (2 * p) = ‖Ψ u (Gauss.Hflow d N u ω)‖ := by
  rw [hre u (Gauss.Hflow d N u ω), Complex.norm_real, Real.norm_eq_abs, abs_flowY, flowY]
  exact (abs_of_nonneg (by positivity)).symm

theorem integral_weighted_eq_ofReal {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) (u : ℝ) :
    (∫ ω, w ω • Ψ u (Gauss.Hflow d N u ω) ∂(Gauss.P d))
      = (((∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d) : ℝ)) : ℂ) := by
  rw [funext fun ω : Gauss.Ω d => smul_Psi_eq (w := w) hre u ω, integral_complex_ofReal]

/-- `u ↦ H_u ω = √u · X(ω)` is continuous. -/
theorem continuous_Hflow_time (d : Gauss.Dims) (N : ℕ) (ω : Gauss.Ω d) :
    Continuous fun u : ℝ => Gauss.Hflow d N u ω := by
  unfold Gauss.Hflow
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const

/-! ### 2. `hderiv`: the (★) identity, read on the real moment -/

/-- **⭐⭐ `hderiv` of (G), as a theorem.**  The weighted generator identity (★) of T264,
composed with `Complex.reCLM`, differentiates the *real* weighted moment
`φ u = E[w·|Y_u|^{2p}]` and pins `φ'` to `RBM.APrimeDuhamelModel.momFlowDeriv` — the sum of the
drift, the second-order and the cross part of (★).  No slot is left to the caller. -/
theorem hasDerivAt_momFlow (h : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun r : ℝ => ∫ ω, w ω * |flowY d N Ψ₁ r ω| ^ (2 * p) ∂(Gauss.P d))
      (momFlowDeriv d N Ψ w wD u) u := by
  have hD := Gauss.hasDerivAt_integral_weighted (Gauss.matrixStein d) h hw hu hT
  rw [funext fun r : ℝ => integral_weighted_eq_ofReal (w := w) hre r] at hD
  have hre' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hD
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re, Complex.add_re,
    Complex.smul_re, Complex.re_sum, smul_eq_mul] at hre'
  refine hre'.congr_deriv ?_
  simp only [momFlowDeriv, driftPart, qvPart, crossPart]
  ring

/-! ### 3. `hcont`: the weighted moment is continuous on the closed window

The left endpoint may be `0`: nothing below uses `0 < u`. -/

/-- **⭐ `hcont` of (G), as a theorem.**  Dominated convergence with the window envelope
`RBM.Gauss.TestFunT₁.bdd₀` and the weight bound `RBM.Gauss.WeightC1.bdd`; the pointwise
continuity in time is the joint differentiability field `diffJoint`, composed with
`u ↦ H_u ω`. -/
theorem continuousOn_momFlow (h : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) {s v : ℝ} (hsub : Set.Icc s v ⊆ T) :
    ContinuousOn (fun r : ℝ => ∫ ω, w ω * |flowY d N Ψ₁ r ω| ^ (2 * p) ∂(Gauss.P d))
      (Set.Icc s v) := by
  classical
  obtain ⟨Cw, hCw⟩ := hw.bdd
  obtain ⟨C₀, hC₀⟩ := h.bdd₀
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans (abs_nonneg _) (hCw 0)
  have hFc : ∀ x ∈ Set.Icc s v,
      Continuous fun ω : Gauss.Ω d => w ω * |flowY d N Ψ₁ x ω| ^ (2 * p) := by
    intro x hx
    have hc : Continuous fun ω : Gauss.Ω d => (w ω • Ψ x (Gauss.Hflow d N x ω)).re :=
      Complex.continuous_re.comp (hw.cont.smul
        ((h.slice (hsub hx)).contDiff.continuous.comp (Gauss.continuous_Hflow d N x)))
    exact hc.congr fun ω => re_smul_Psi hre x ω
  refine MeasureTheory.continuousOn_of_dominated
    (bound := fun _ : Gauss.Ω d => Cw * C₀)
    (fun x hx => (hFc x hx).aestronglyMeasurable) (fun x hx => ?_)
    (MeasureTheory.integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun ω => ?_
    have habs : |w ω * |flowY d N Ψ₁ x ω| ^ (2 * p)|
        = |w ω| * ‖Ψ x (Gauss.Hflow d N x ω)‖ := by
      rw [abs_flowY_pow_eq_norm hre x ω, abs_mul, abs_norm]
    rw [Real.norm_eq_abs, habs]
    exact mul_le_mul (hCw ω) (hC₀ x (hsub hx) _) (norm_nonneg _) hCw0
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hjoint : ∀ x ∈ Set.Icc s v,
        ContinuousAt (fun r : ℝ => Ψ r (Gauss.Hflow d N r ω)) x := by
      intro x hx
      have hd : ContinuousAt (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2)
          (x, Gauss.Hflow d N x ω) :=
        (h.diffJoint x (hsub hx) (Gauss.Hflow d N x ω)).continuousAt
      have hmap : ContinuousAt
          (fun r : ℝ => ((r, Gauss.Hflow d N r ω) :
            ℝ × Matrix (d.Idx N) (d.Idx N) ℂ)) x :=
        (continuous_id.prodMk (continuous_Hflow_time d N ω)).continuousAt
      exact ContinuousAt.comp (x := x)
        (g := fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) hd hmap
    intro x hx
    have hc : ContinuousWithinAt
        (fun r : ℝ => (w ω • Ψ r (Gauss.Hflow d N r ω)).re) (Set.Icc s v) x :=
      (Complex.continuous_re.continuousAt.comp
        ((hjoint x hx).const_smul (w ω))).continuousWithinAt
    exact hc.congr (fun r _ => (re_smul_Psi hre r ω).symm) (re_smul_Psi hre x ω).symm

/-! ### 4. `hφ'int`: `φ'` is interval integrable, `s = 0` included

The only unbounded factor is the `(2√u)⁻¹` of the cross term of (★), and `u^{-1/2}` is
integrable at `0`.  Measurability is free: on the open window `φ'` **is** `deriv φ`, and
`Mathlib`'s `measurable_deriv` applies. -/

/-- `∑_α S_α ‖B_α‖`, the deterministic first-order coordinate weight. -/
noncomputable def coordWt1 (d : Gauss.Dims) (N : ℕ) : ℝ :=
  ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
    ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖

/-- `∑_α S_α ‖B_α‖²`, the deterministic second-order coordinate weight. -/
noncomputable def coordWt2 (d : Gauss.Dims) (N : ℕ) : ℝ :=
  ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
    (‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)

theorem coordWt1_nonneg (d : Gauss.Dims) (N : ℕ) : 0 ≤ coordWt1 d N :=
  Finset.sum_nonneg fun q _ => mul_nonneg (Gauss.gvar d (Gauss.crd d N q)).2 (norm_nonneg _)

theorem coordWt2_nonneg (d : Gauss.Dims) (N : ℕ) : 0 ≤ coordWt2 d N :=
  Finset.sum_nonneg fun q _ =>
    mul_nonneg (Gauss.gvar d (Gauss.crd d N q)).2 (by positivity)

theorem abs_driftPart_le {Cw CT : ℝ}
    (hCw : ∀ ω, |w ω| ≤ Cw) (hCT : ∀ M, ‖Gauss.timeD1 Ψ u M‖ ≤ CT) :
    |driftPart d N Ψ w u| ≤ Cw * CT := by
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans (abs_nonneg _) (hCw 0)
  refine le_trans (Complex.abs_re_le_norm _) ?_
  have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := Gauss.P d)
    (C := Cw * CT) (f := fun ω : Gauss.Ω d => w ω • Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω))
    (Filter.Eventually.of_forall fun ω => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hCw ω) (hCT _) (norm_nonneg _) hCw0)
  simpa using this

theorem abs_qvPart_le {Cw C₂ : ℝ}
    (hCw : ∀ ω, |w ω| ≤ Cw) (hC₂ : ∀ M, ‖fderiv ℝ (fderiv ℝ (Ψ u)) M‖ ≤ C₂) :
    |qvPart d N Ψ w u| ≤ (1 / 2 : ℝ) * (Cw * C₂) * coordWt2 d N := by
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans (abs_nonneg _) (hCw 0)
  have hterm : ∀ q ∈ Gauss.usedCoord d N,
      |(Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (∫ ω, w ω • Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re|
        ≤ (Cw * C₂) * ((Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) := by
    intro q _
    have hb : |(∫ ω, w ω • Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q
          ∂(Gauss.P d)).re|
        ≤ Cw * (C₂ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖
            * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := Gauss.P d)
        (C := Cw * (C₂ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖
          * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖))
        (f := fun ω : Gauss.Ω d =>
          w ω • Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q)
        (Filter.Eventually.of_forall fun ω => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hCw ω) (Gauss.norm_coordD2_le hC₂ _ q) (norm_nonneg _) hCw0)
      simpa using this
    rw [abs_mul, NNReal.abs_eq]
    calc (Gauss.gvar d (Gauss.crd d N q) : ℝ) * |(∫ ω, w ω •
            Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re|
        ≤ (Gauss.gvar d (Gauss.crd d N q) : ℝ) * (Cw * (C₂ *
            ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) :=
          mul_le_mul_of_nonneg_left hb (Gauss.gvar d (Gauss.crd d N q)).2
      _ = _ := by ring
  rw [qvPart, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [coordWt2, Finset.mul_sum]
  exact Finset.sum_le_sum hterm

theorem abs_crossPart_le {CwD C₁ : ℝ} (hCwD0 : 0 ≤ CwD)
    (hCwD : ∀ q ∈ Gauss.usedCoord d N, ∀ ω, |wD q ω| ≤ CwD)
    (hC₁ : ∀ M, ‖fderiv ℝ (Ψ u) M‖ ≤ C₁) (hu : 0 < u) :
    |crossPart d N Ψ wD u| ≤ (1 / (2 * √u)) * ((CwD * C₁) * coordWt1 d N) := by
  have hsu : 0 < √u := Real.sqrt_pos.2 hu
  have hterm : ∀ q ∈ Gauss.usedCoord d N,
      |(Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (∫ ω, wD q ω • Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re|
        ≤ (CwD * C₁) * ((Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) := by
    intro q hq
    have hb : |(∫ ω, wD q ω • Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q
          ∂(Gauss.P d)).re| ≤ CwD * (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := Gauss.P d)
        (C := CwD * (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖))
        (f := fun ω : Gauss.Ω d =>
          wD q ω • Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q)
        (Filter.Eventually.of_forall fun ω => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hCwD q hq ω) (Gauss.norm_coordD1_le hC₁ _ q)
            (norm_nonneg _) hCwD0)
      simpa using this
    rw [abs_mul, NNReal.abs_eq]
    calc (Gauss.gvar d (Gauss.crd d N q) : ℝ) * |(∫ ω, wD q ω •
            Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re|
        ≤ (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (CwD * (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) :=
          mul_le_mul_of_nonneg_left hb (Gauss.gvar d (Gauss.crd d N q)).2
      _ = _ := by ring
  rw [crossPart, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * √u))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [coordWt1, Finset.mul_sum]
  exact Finset.sum_le_sum hterm

/-- **⭐ `hφ'int` of (G), as a theorem.**  `φ'` is measurable because on the open window it
*is* `deriv φ` (`Mathlib`'s `measurable_deriv`), and it is dominated by
`K₁ + K₂·u^{-1/2}`, whose singularity at the left endpoint `0` is integrable.  The left
endpoint may therefore be `0` — the first cell of D17. -/
theorem intervalIntegrable_momFlowDeriv (h : Gauss.TestFunT₁ d N T Ψ)
    (hw : Gauss.WeightC1 d N w wD) {p : ℕ} (hre : IsModulusPow Ψ Ψ₁ p) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hsub : Set.Icc s v ⊆ T) :
    IntervalIntegrable (momFlowDeriv d N Ψ w wD) volume s v := by
  classical
  obtain ⟨Cw, hCw⟩ := hw.bdd
  obtain ⟨CwD', hCwD'⟩ := hw.bddD
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  obtain ⟨CT, hCT⟩ := h.bddT
  set CwD : ℝ := max 0 CwD' with hCwDdef
  have hCwD0 : (0 : ℝ) ≤ CwD := le_max_left _ _
  have hCwD : ∀ q ∈ Gauss.usedCoord d N, ∀ ω, |wD q ω| ≤ CwD := fun q hq ω =>
    le_trans (hCwD' q hq ω) (le_max_right _ _)
  set K₁ : ℝ := Cw * CT + (1 / 2 : ℝ) * (Cw * C₂) * coordWt2 d N with hK₁
  set K₂ : ℝ := (1 / 2 : ℝ) * ((CwD * C₁) * coordWt1 d N) with hK₂
  set φ : ℝ → ℝ := fun r : ℝ => ∫ ω, w ω * |flowY d N Ψ₁ r ω| ^ (2 * p) ∂(Gauss.P d) with hφ
  -- the pointwise envelope
  have hbd : ∀ u ∈ Set.uIoc s v, ‖momFlowDeriv d N Ψ w wD u‖
      ≤ K₁ + K₂ * u ^ (-(1 : ℝ) / 2) := by
    intro u hu
    rw [Set.uIoc_of_le hsv] at hu
    have hu0 : 0 < u := lt_of_le_of_lt hs0 hu.1
    have huT : u ∈ T := hsub ⟨le_of_lt hu.1, hu.2⟩
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    have hrw : u ^ (-(1 : ℝ) / 2) = (√u)⁻¹ := by
      rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hu0.le]
    have h1 := abs_driftPart_le (w := w) (Ψ := Ψ) (u := u) hCw (fun M => hCT u huT M)
    have h2 := abs_qvPart_le (w := w) (Ψ := Ψ) (u := u) hCw (fun M => hC₂ u huT M)
    have h3 := abs_crossPart_le (wD := wD) (Ψ := Ψ) (u := u) hCwD0 hCwD
      (fun M => hC₁ u huT M) hu0
    have hcr : (1 / (2 * √u)) * ((CwD * C₁) * coordWt1 d N) = K₂ * u ^ (-(1 : ℝ) / 2) := by
      rw [hrw, hK₂]
      field_simp
    rw [Real.norm_eq_abs, momFlowDeriv]
    calc |driftPart d N Ψ w u + qvPart d N Ψ w u + crossPart d N Ψ wD u|
        ≤ |driftPart d N Ψ w u + qvPart d N Ψ w u| + |crossPart d N Ψ wD u| := abs_add_le _ _
      _ ≤ (|driftPart d N Ψ w u| + |qvPart d N Ψ w u|) + |crossPart d N Ψ wD u| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (Cw * CT + (1 / 2 : ℝ) * (Cw * C₂) * coordWt2 d N)
            + (1 / (2 * √u)) * ((CwD * C₁) * coordWt1 d N) :=
          add_le_add (add_le_add h1 h2) h3
      _ = K₁ + K₂ * u ^ (-(1 : ℝ) / 2) := by rw [hcr, hK₁]
  -- `φ'` is `deriv φ` on the open window, hence measurable there
  have hderiv : ∀ u ∈ Set.Ioo s v, HasDerivAt φ (momFlowDeriv d N Ψ w wD u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hs0 hu.1
    exact hasDerivAt_momFlow h hw hre hu0
      (Filter.mem_of_superset (Icc_mem_nhds hu.1 hu.2) hsub)
  have hmeas : MeasureTheory.AEStronglyMeasurable (momFlowDeriv d N Ψ w wD)
      (volume.restrict (Set.uIoc s v)) := by
    refine ((measurable_deriv φ).aestronglyMeasurable).congr ?_
    rw [Set.uIoc_of_le hsv,
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Ioc (a := s) (b := v))).symm]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
    exact (hderiv u hu).deriv
  refine IntervalIntegrable.mono_fun' (g := fun u : ℝ => K₁ + K₂ * u ^ (-(1 : ℝ) / 2))
    ?_ hmeas ?_
  · exact intervalIntegrable_const.add
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K₂)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with u hu
    exact hbd u hu

/-! ### 5. Weighted Hölder

The two Hölder steps of T191 (`RBM.MomentDuhamel.integral_pow_sub_one_mul_le` and
`integral_pow_sub_two_mul_le`) are stated for a bare measure.  The weighted versions needed by
(G) follow from them **without** a new Hölder argument: substituting `W^{1/(2p)}·Y` for `Y`
turns every weighted integrand into an unweighted one, because
`(W^{1/(2p)})^{2p} = W`.  This is the same device as the `χ^{2p}` weight itself. -/

section Holder

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}

/-- `W^{1/(2p)}·Y`: the substitution that removes the weight. -/
noncomputable def wscale (W : Ω → ℝ) (p : ℕ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => W ω ^ ((1 : ℝ) / (2 * (p : ℝ))) * Y ω

omit [MeasurableSpace Ω] in
theorem abs_wscale {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (p : ℕ) (Y : Ω → ℝ) (ω : Ω) :
    |wscale W p Y ω| = W ω ^ ((1 : ℝ) / (2 * (p : ℝ))) * |Y ω| := by
  rw [wscale, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) _)]

omit [MeasurableSpace Ω] in
/-- `(W^{1/(2p)})^{2p} = W`. -/
theorem rpow_inv_pow {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p) (ω : Ω) :
    (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p) = W ω := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [← Real.rpow_natCast (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) (2 * p),
    ← Real.rpow_mul (hW0 ω)]
  push_cast
  rw [show (1 : ℝ) / (2 * (p : ℝ)) * (2 * (p : ℝ)) = 1 by field_simp]
  exact Real.rpow_one _

omit [MeasurableSpace Ω] in
theorem abs_wscale_pow {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p)
    (Y : Ω → ℝ) (ω : Ω) :
    |wscale W p Y ω| ^ (2 * p) = W ω * |Y ω| ^ (2 * p) := by
  rw [abs_wscale hW0, mul_pow, rpow_inv_pow hW0 hp]

omit [MeasurableSpace Ω] in
theorem abs_wscale_pow_sub_one_mul {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p)
    (Y Z : Ω → ℝ) (ω : Ω) :
    |wscale W p Y ω| ^ (2 * p - 1) * |wscale W p Z ω|
      = W ω * |Y ω| ^ (2 * p - 1) * |Z ω| := by
  have hsucc : 2 * p - 1 + 1 = 2 * p := by omega
  rw [abs_wscale hW0, abs_wscale hW0, mul_pow]
  calc (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 1) * |Y ω| ^ (2 * p - 1)
        * (W ω ^ ((1 : ℝ) / (2 * (p : ℝ))) * |Z ω|)
      = (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 1 + 1)
        * |Y ω| ^ (2 * p - 1) * |Z ω| := by rw [pow_succ]; ring
    _ = W ω * |Y ω| ^ (2 * p - 1) * |Z ω| := by rw [hsucc, rpow_inv_pow hW0 hp]

/-- **⭐ Weighted Hölder, first order.** -/
theorem integral_weight_pow_sub_one_mul_le {p : ℕ} (hp : 1 ≤ p) {W Y Z : Ω → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hYm : MeasureTheory.AEStronglyMeasurable (wscale W p Y) P)
    (hZm : MeasureTheory.AEStronglyMeasurable (wscale W p Z) P)
    (hY : MeasureTheory.Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hZ : MeasureTheory.Integrable (fun ω => W ω * |Z ω| ^ (2 * p)) P) :
    (∫ ω, W ω * |Y ω| ^ (2 * p - 1) * |Z ω| ∂P)
      ≤ (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
          * MomentDuhamel.momNormW P W p Z := by
  have hYi : MeasureTheory.Integrable (fun ω => |wscale W p Y ω| ^ (2 * p)) P :=
    hY.congr (Filter.Eventually.of_forall fun ω => (abs_wscale_pow hW0 hp Y ω).symm)
  have hZi : MeasureTheory.Integrable (fun ω => |wscale W p Z ω| ^ (2 * p)) P :=
    hZ.congr (Filter.Eventually.of_forall fun ω => (abs_wscale_pow hW0 hp Z ω).symm)
  have hkey := MomentDuhamel.integral_pow_sub_one_mul_le (P := P) hp hYm hZm hYi hZi
  rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => abs_wscale_pow_sub_one_mul hW0 hp Y Z ω),
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => abs_wscale_pow hW0 hp Y ω)] at hkey
  refine hkey.trans (le_of_eq ?_)
  congr 1
  rw [MomentDuhamel.momNorm, MomentDuhamel.momNormW,
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => abs_wscale_pow hW0 hp Z ω)]
  push_cast
  ring_nf

/-- `W^{1/p}·Q`: the substitution for the rate slot, whose dimension is that of `Y²`. -/
noncomputable def wscaleQ (W : Ω → ℝ) (p : ℕ) (Q : Ω → ℝ) : Ω → ℝ :=
  fun ω => W ω ^ ((1 : ℝ) / (p : ℝ)) * Q ω

omit [MeasurableSpace Ω] in
theorem wscaleQ_nonneg {W Q : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (hQ0 : ∀ ω, 0 ≤ Q ω) (p : ℕ)
    (ω : Ω) : 0 ≤ wscaleQ W p Q ω :=
  mul_nonneg (Real.rpow_nonneg (hW0 ω) _) (hQ0 ω)

omit [MeasurableSpace Ω] in
/-- `W^{1/p} = (W^{1/(2p)})²`. -/
theorem rpow_inv_p_eq_sq {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p) (ω : Ω) :
    W ω ^ ((1 : ℝ) / (p : ℝ)) = (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [← Real.rpow_natCast (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) 2, ← Real.rpow_mul (hW0 ω)]
  congr 1
  push_cast
  field_simp

omit [MeasurableSpace Ω] in
theorem abs_wscaleQ_pow {W Q : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p) (ω : Ω) :
    |wscaleQ W p Q ω| ^ p = W ω * |Q ω| ^ p := by
  have hsq : ((W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ 2) ^ p
      = (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p) := by
    rw [← pow_mul]
  rw [wscaleQ, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) _), mul_pow,
    rpow_inv_p_eq_sq hW0 hp, hsq, rpow_inv_pow hW0 hp]

omit [MeasurableSpace Ω] in
theorem abs_wscale_pow_sub_two_mul {W Q : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p)
    (Y : Ω → ℝ) (ω : Ω) :
    |wscale W p Y ω| ^ (2 * p - 2) * wscaleQ W p Q ω
      = W ω * |Y ω| ^ (2 * p - 2) * Q ω := by
  have hsucc : 2 * p - 2 + 2 = 2 * p := by omega
  rw [abs_wscale hW0, mul_pow, wscaleQ, rpow_inv_p_eq_sq hW0 hp]
  calc (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 2) * |Y ω| ^ (2 * p - 2)
        * ((W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ 2 * Q ω)
      = (W ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 2 + 2)
          * |Y ω| ^ (2 * p - 2) * Q ω := by rw [pow_add]; ring
    _ = W ω * |Y ω| ^ (2 * p - 2) * Q ω := by rw [hsucc, rpow_inv_pow hW0 hp]

/-- **⭐ Weighted Hölder, second order.** -/
theorem integral_weight_pow_sub_two_mul_le {p : ℕ} (hp : 1 ≤ p) {W Y Q : Ω → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hQ0 : ∀ ω, 0 ≤ Q ω)
    (hYm : MeasureTheory.AEStronglyMeasurable (wscale W p Y) P)
    (hQm : MeasureTheory.AEStronglyMeasurable (wscaleQ W p Q) P)
    (hY : MeasureTheory.Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hQ : MeasureTheory.Integrable (fun ω => W ω * |Q ω| ^ p) P) :
    (∫ ω, W ω * |Y ω| ^ (2 * p - 2) * Q ω ∂P)
      ≤ (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ))
          * APrimeModel.rateNormW P W p Q := by
  have hYi : MeasureTheory.Integrable (fun ω => |wscale W p Y ω| ^ (2 * p)) P :=
    hY.congr (Filter.Eventually.of_forall fun ω => (abs_wscale_pow hW0 hp Y ω).symm)
  have hQi : MeasureTheory.Integrable (fun ω => |wscaleQ W p Q ω| ^ p) P :=
    hQ.congr (Filter.Eventually.of_forall fun ω => (abs_wscaleQ_pow hW0 hp ω).symm)
  have hkey := MomentDuhamel.integral_pow_sub_two_mul_le (P := P) hp hYm hQm
    (wscaleQ_nonneg hW0 hQ0 p) hYi hQi
  rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => abs_wscale_pow_sub_two_mul hW0 hp (Q := Q) Y ω),
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => abs_wscale_pow hW0 hp Y ω)] at hkey
  refine hkey.trans (le_of_eq ?_)
  congr 1
  rw [MomentDuhamel.momNorm, APrimeModel.rateNormW,
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => abs_wscaleQ_pow hW0 hp (Q := Q) ω)]

end Holder

/-! ### 6. `hbound`: the differential inequality of (G) -/

/-- The generator's second-order coefficient at one matrix, for a general observable. -/
noncomputable def genPt (d : Gauss.Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  (2⁻¹ : ℝ) * ∑ q ∈ Gauss.usedCoord d N,
    (Gauss.gvar d (Gauss.crd d N q) : ℝ) * (Gauss.coordD2 d N Φ M q).re

/-- `RBM.Gauss.genMomentPt` is this, at `Φ = |F|^{2p}`. -/
theorem genPt_momentFun (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (p : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genPt d N (Gauss.momentFun F p) M = Gauss.genMomentPt d N F p M := rfl

/-- **The drift and the second-order part of (★) are one weighted integral.** -/
theorem driftPart_add_qvPart (h : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {u : ℝ} (hu : u ∈ T) :
    driftPart d N Ψ w u + qvPart d N Ψ w u
      = ∫ ω, w ω * ((Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω)).re
          + genPt d N (Ψ u) (Gauss.Hflow d N u ω)) ∂(Gauss.P d) := by
  classical
  obtain ⟨Cw, hCw⟩ := hw.bdd
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  obtain ⟨CT, hCT⟩ := h.bddT
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans (abs_nonneg _) (hCw 0)
  have hintT : MeasureTheory.Integrable
      (fun ω : Gauss.Ω d => w ω • Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω)) (Gauss.P d) := by
    refine Gauss.integrable_of_continuous_of_bound
      (hw.cont.smul ((h.contT u hu).comp (Gauss.continuous_Hflow d N u))) (C := Cw * CT)
      fun ω => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hCw ω) (hCT u hu _) (norm_nonneg _) hCw0
  have hintQ : ∀ q ∈ Gauss.usedCoord d N, MeasureTheory.Integrable
      (fun ω : Gauss.Ω d => w ω • Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q)
      (Gauss.P d) := by
    intro q _
    refine Gauss.integrable_of_continuous_of_bound
      (hw.cont.smul (Gauss.continuous_coordD2 (h.slice hu) u q))
      (C := Cw * (C₂ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖
        * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) fun ω => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hCw ω) (Gauss.norm_coordD2_le (hC₂ u hu) _ q) (norm_nonneg _) hCw0
  have hdrift : driftPart d N Ψ w u
      = ∫ ω, w ω * (Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω)).re ∂(Gauss.P d) := by
    have h0 := integral_re (𝕜 := ℂ) hintT
    rw [driftPart]
    simpa [Complex.smul_re] using h0.symm
  have hqv : qvPart d N Ψ w u
      = ∫ ω, w ω * genPt d N (Ψ u) (Gauss.Hflow d N u ω) ∂(Gauss.P d) := by
    have hterm : ∀ q ∈ Gauss.usedCoord d N,
        (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (∫ ω, w ω • Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re
          = ∫ ω, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
              (w ω * (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re) ∂(Gauss.P d) := by
      intro q hq
      have h1 := integral_re (𝕜 := ℂ) (hintQ q hq)
      rw [MeasureTheory.integral_const_mul]
      congr 1
      simpa [Complex.smul_re] using h1.symm
    have hsum : MeasureTheory.Integrable (fun ω : Gauss.Ω d =>
        ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (w ω * (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re)) (Gauss.P d) := by
      refine integrable_finsetSum _ fun q hq => ?_
      refine MeasureTheory.Integrable.const_mul ?_ _
      exact ((hintQ q hq).re).congr (Filter.Eventually.of_forall fun ω => by simp)
    rw [qvPart, Finset.sum_congr rfl hterm,
      ← integral_finsetSum _ (fun q hq => by
        refine MeasureTheory.Integrable.const_mul ?_ _
        exact ((hintQ q hq).re).congr (Filter.Eventually.of_forall fun ω => by simp)),
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [genPt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hdrift, hqv, ← MeasureTheory.integral_add]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  · exact (hintT.re).congr (Filter.Eventually.of_forall fun ω => by simp)
  · have hbase : MeasureTheory.Integrable (fun ω : Gauss.Ω d =>
        (2⁻¹ : ℝ) * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (w ω * (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re)) (Gauss.P d) := by
      refine MeasureTheory.Integrable.const_mul ?_ _
      refine integrable_finsetSum _ fun q hq => ?_
      refine MeasureTheory.Integrable.const_mul ?_ _
      exact ((hintQ q hq).re).congr (Filter.Eventually.of_forall fun ω => by simp)
    refine hbase.congr (Filter.Eventually.of_forall fun ω => ?_)
    have hs : ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (w ω * (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re)
        = w ω * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    change (2⁻¹ : ℝ) * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (w ω * (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re)
      = w ω * genPt d N (Ψ u) (Gauss.Hflow d N u ω)
    rw [hs, genPt]
    ring

/-- The generator integrand of (★) is integrable. -/
theorem integrable_genIntegrand (h : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {u : ℝ} (hu : u ∈ T) :
    MeasureTheory.Integrable (fun ω : Gauss.Ω d => w ω *
      ((Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω)).re
        + genPt d N (Ψ u) (Gauss.Hflow d N u ω))) (Gauss.P d) := by
  classical
  obtain ⟨Cw, hCw⟩ := hw.bdd
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  obtain ⟨CT, hCT⟩ := h.bddT
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans (abs_nonneg _) (hCw 0)
  have hgc : Continuous fun ω : Gauss.Ω d => genPt d N (Ψ u) (Gauss.Hflow d N u ω) := by
    have hs : Continuous fun ω : Gauss.Ω d => ∑ q ∈ Gauss.usedCoord d N,
        (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re :=
      continuous_finsetSum _ fun q _ =>
        (Complex.continuous_re.comp (Gauss.continuous_coordD2 (h.slice hu) u q)).const_mul _
    exact hs.const_mul (2⁻¹ : ℝ)
  have hgb : ∀ ω : Gauss.Ω d,
      |genPt d N (Ψ u) (Gauss.Hflow d N u ω)| ≤ 2⁻¹ * (C₂ * coordWt2 d N) := by
    intro ω
    rw [genPt, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2⁻¹ : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [coordWt2, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [abs_mul, NNReal.abs_eq]
    have : |(Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re|
        ≤ C₂ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ :=
      le_trans (Complex.abs_re_le_norm _) (Gauss.norm_coordD2_le (hC₂ u hu) _ q)
    calc (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          |(Gauss.coordD2 d N (Ψ u) (Gauss.Hflow d N u ω) q).re|
        ≤ (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (C₂ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) :=
          mul_le_mul_of_nonneg_left this (Gauss.gvar d (Gauss.crd d N q)).2
      _ = _ := by ring
  refine Gauss.integrable_of_continuous_of_bound
    (hw.cont.mul ((Complex.continuous_re.comp
      ((h.contT u hu).comp (Gauss.continuous_Hflow d N u))).add hgc))
    (C := Cw * (CT + 2⁻¹ * (C₂ * coordWt2 d N))) fun ω => ?_
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul (hCw ω) (le_trans (abs_add_le _ _) (add_le_add ?_ (hgb ω)))
    (abs_nonneg _) hCw0
  exact le_trans (Complex.abs_re_le_norm _) (hCT u hu _)

/-- **⭐⭐ `hbound` of (G), as a theorem.**

The three terms of (★) are read off in the (G) shape: the drift and the second-order part
against the **weighted** Hölder inequalities of §5, and the cross term against the bound
`hcross` — which is the (S5) input, discharged in §7.  `A u = ‖G‖_{W,2p}` is the weighted
drift norm, `g u = ‖Q‖^{rate}_{W,p}` the weighted quadratic-variation rate, and `Bc` the
cross-term budget. -/
theorem momFlowDeriv_le {p : ℕ} (hp : 1 ≤ p) (h : Gauss.TestFunT₁ d N T Ψ)
    (hw : Gauss.WeightC1 d N w wD) {u : ℝ} (hu : u ∈ T)
    {G Q : Gauss.Ω d → ℝ} {Bc : ℝ}
    (hW0 : ∀ ω, 0 ≤ w ω) (hQ0 : ∀ ω, 0 ≤ Q ω)
    (hYm : MeasureTheory.AEStronglyMeasurable
      (wscale w p (flowY d N Ψ₁ u)) (Gauss.P d))
    (hGm : MeasureTheory.AEStronglyMeasurable (wscale w p G) (Gauss.P d))
    (hQm : MeasureTheory.AEStronglyMeasurable (wscaleQ w p Q) (Gauss.P d))
    (hYi : MeasureTheory.Integrable
      (fun ω => w ω * |flowY d N Ψ₁ u ω| ^ (2 * p)) (Gauss.P d))
    (hGi : MeasureTheory.Integrable (fun ω => w ω * |G ω| ^ (2 * p)) (Gauss.P d))
    (hQi : MeasureTheory.Integrable (fun ω => w ω * |Q ω| ^ p) (Gauss.P d))
    (hm1 : MeasureTheory.Integrable
      (fun ω => w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|) (Gauss.P d))
    (hm2 : MeasureTheory.Integrable
      (fun ω => w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω) (Gauss.P d))
    (hle : ∀ ω, w ω * ((Gauss.timeD1 Ψ u (Gauss.Hflow d N u ω)).re
        + genPt d N (Ψ u) (Gauss.Hflow d N u ω))
      ≤ w ω * (2 * (p : ℝ) * (|flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|)
        + (p : ℝ) * (2 * (p : ℝ) - 1) * (|flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω)))
    (hcross : crossPart d N Ψ wD u
      ≤ 2 * (p : ℝ) * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * Bc) :
    momFlowDeriv d N Ψ w wD u
      ≤ 2 * (p : ℝ) * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (MomentDuhamel.momNormW (Gauss.P d) w p G + Bc)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
                ^ (((p : ℝ) - 1) / (p : ℝ))
            * APrimeModel.rateNormW (Gauss.P d) w p Q := by
  classical
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hc0 : (0 : ℝ) ≤ (p : ℝ) * (2 * (p : ℝ) - 1) := by nlinarith
  set φa : ℝ := (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
      ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) with hφa
  have hm1' : MeasureTheory.Integrable
      (fun ω => w ω * (|flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|)) (Gauss.P d) :=
    hm1.congr (Filter.Eventually.of_forall fun ω => by ring)
  have hm2' : MeasureTheory.Integrable
      (fun ω => w ω * (|flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω)) (Gauss.P d) :=
    hm2.congr (Filter.Eventually.of_forall fun ω => by ring)
  have hRi : MeasureTheory.Integrable (fun ω => w ω *
      (2 * (p : ℝ) * (|flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
          * (|flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω))) (Gauss.P d) := by
    refine ((hm1'.const_mul (2 * (p : ℝ))).add
      (hm2'.const_mul ((p : ℝ) * (2 * (p : ℝ) - 1)))).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have hmono := MeasureTheory.integral_mono (integrable_genIntegrand h hw hu) hRi hle
  have hsplit : (∫ ω, w ω *
      (2 * (p : ℝ) * (|flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
          * (|flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω)) ∂(Gauss.P d))
      = 2 * (p : ℝ) * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω| ∂(Gauss.P d))
        + (p : ℝ) * (2 * (p : ℝ) - 1)
          * ∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω ∂(Gauss.P d) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      show w ω * (2 * (p : ℝ) * (|flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|)
          + (p : ℝ) * (2 * (p : ℝ) - 1) * (|flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω))
        = 2 * (p : ℝ) * (w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|)
          + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω) from by ring),
      MeasureTheory.integral_add (hm1.const_mul _) (hm2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hH1 := integral_weight_pow_sub_one_mul_le (P := Gauss.P d) hp hW0 hYm hGm hYi hGi
  have hH2 := integral_weight_pow_sub_two_mul_le (P := Gauss.P d) hp hW0 hQ0 hYm hQm hYi hQi
  have hkey : driftPart d N Ψ w u + qvPart d N Ψ w u
      ≤ 2 * (p : ℝ) * φa * MomentDuhamel.momNormW (Gauss.P d) w p G
        + (p : ℝ) * (2 * (p : ℝ) - 1)
          * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
              ^ (((p : ℝ) - 1) / (p : ℝ))
          * APrimeModel.rateNormW (Gauss.P d) w p Q := by
    rw [driftPart_add_qvPart h hw hu]
    refine hmono.trans ?_
    rw [hsplit]
    have e1 : 2 * (p : ℝ) * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 1) * |G ω|
        ∂(Gauss.P d)) ≤ 2 * (p : ℝ) * (φa * MomentDuhamel.momNormW (Gauss.P d) w p G) :=
      mul_le_mul_of_nonneg_left hH1 (by linarith)
    have e2 : (p : ℝ) * (2 * (p : ℝ) - 1)
        * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p - 2) * Q ω ∂(Gauss.P d))
        ≤ (p : ℝ) * (2 * (p : ℝ) - 1)
          * ((∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
                ^ (((p : ℝ) - 1) / (p : ℝ))
            * APrimeModel.rateNormW (Gauss.P d) w p Q) :=
      mul_le_mul_of_nonneg_left hH2 hc0
    nlinarith [e1, e2]
  rw [momFlowDeriv]
  have hexp : 2 * (p : ℝ) * φa * (MomentDuhamel.momNormW (Gauss.P d) w p G + Bc)
      = 2 * (p : ℝ) * φa * MomentDuhamel.momNormW (Gauss.P d) w p G
        + 2 * (p : ℝ) * φa * Bc := by ring
  rw [hexp]
  have hcross' : crossPart d N Ψ wD u ≤ 2 * (p : ℝ) * φa * Bc := hcross
  linarith [hkey, hcross']

/-! ### 7. `hBbd`: the cross term against the (S6) integrand

The chain is exactly the one T271 left open: the (S5) **pointwise** bound of T265
(`RBM.Gauss.sum_gvar_crossTerm_le`, both gradients at the *same* matrix variable), integrated
against the weight, then the two rescaling obligations of T271
(`RBM.APrimeModel.sqrt_div_le_sqrt_inv`, `RBM.APrimeModel.inv_two_sqrt_le_sqrt_inv`), and
finally the (5.42) envelope of the **evolved** rate **on the good event** (§7.1's
`RBM.APrimeDuhamelModel.EvolvedQVBound`).

⚠ T277 showed that T269's `RBM.APrimeModel.qvRate` is the *un-evolved* `quadVar (lkFun)`, so
it is **not** what enters here; see §7.1. -/

/-- **Step A: the cross term is below a weighted `ℓ¹` integral of the two gradients.** -/
theorem crossPart_le_integral (h : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {u : ℝ} (hu : u ∈ T) (hu0 : 0 < u) :
    crossPart d N Ψ wD u
      ≤ (1 / (2 * √u)) * ∫ ω, ∑ q ∈ Gauss.usedCoord d N,
          (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖) ∂(Gauss.P d) := by
  classical
  obtain ⟨CwD, hCwD⟩ := hw.bddD
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  have hint : ∀ q ∈ Gauss.usedCoord d N, MeasureTheory.Integrable
      (fun ω : Gauss.Ω d => (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)) (Gauss.P d) := by
    intro q hq
    have hCwD0 : (0 : ℝ) ≤ CwD := le_trans (abs_nonneg _) (hCwD q hq 0)
    refine MeasureTheory.Integrable.const_mul ?_ _
    refine Gauss.integrable_of_continuous_of_bound
      ((hw.contD q hq).abs.mul (Gauss.continuous_coordD1 (h.slice hu) u q).norm)
      (C := CwD * (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_norm]
    exact mul_le_mul (hCwD q hq ω) (Gauss.norm_coordD1_le (hC₁ u hu) _ q)
      (norm_nonneg _) hCwD0
  have hq : ∀ q ∈ Gauss.usedCoord d N,
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (∫ ω, wD q ω • Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q ∂(Gauss.P d)).re
        ≤ ∫ ω, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖) ∂(Gauss.P d) := by
    intro q _
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Gauss.gvar d (Gauss.crd d N q)).2
    refine le_trans (Complex.re_le_norm _)
      (le_trans (MeasureTheory.norm_integral_le_integral_norm _) (le_of_eq ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [norm_smul, Real.norm_eq_abs]
  rw [crossPart]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [MeasureTheory.integral_finsetSum _ hint]
  exact Finset.sum_le_sum hq

/-- **Step B: `∫ |W^{1/(2p)}Y|^{2p-1} ≤ φ^{(2p-1)/(2p)}`** — the Hölder step with the trivial
second factor, on a probability measure. -/
theorem integral_wscale_pow_sub_one_le {p : ℕ} (hp : 1 ≤ p) {Y : Gauss.Ω d → ℝ}
    (hW0 : ∀ ω, 0 ≤ w ω)
    (hYm : MeasureTheory.AEStronglyMeasurable (wscale w p Y) (Gauss.P d))
    (hYi : MeasureTheory.Integrable (fun ω => w ω * |Y ω| ^ (2 * p)) (Gauss.P d)) :
    (∫ ω, |wscale w p Y ω| ^ (2 * p - 1) ∂(Gauss.P d))
      ≤ (∫ ω, w ω * |Y ω| ^ (2 * p) ∂(Gauss.P d))
          ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) := by
  have hYi' : MeasureTheory.Integrable
      (fun ω : Gauss.Ω d => |wscale w p Y ω| ^ (2 * p)) (Gauss.P d) :=
    hYi.congr (Filter.Eventually.of_forall fun ω => (abs_wscale_pow hW0 hp Y ω).symm)
  have hone : MeasureTheory.Integrable
      (fun _ : Gauss.Ω d => |(1 : ℝ)| ^ (2 * p)) (Gauss.P d) :=
    MeasureTheory.integrable_const _
  have hkey := MomentDuhamel.integral_pow_sub_one_mul_le (P := Gauss.P d) hp hYm
    (MeasureTheory.aestronglyMeasurable_const (b := (1 : ℝ))) hYi' hone
  have hmom : MomentDuhamel.momNorm (Gauss.P d) (2 * p) (fun _ : Gauss.Ω d => (1 : ℝ)) = 1 := by
    rw [MomentDuhamel.momNorm]
    simp
  rw [hmom, mul_one,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      abs_wscale_pow hW0 hp Y ω)] at hkey
  refine le_trans (le_of_eq ?_) hkey
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp

theorem integrable_crossSum (h : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {u : ℝ} (hu : u ∈ T) :
    MeasureTheory.Integrable (fun ω : Gauss.Ω d => ∑ q ∈ Gauss.usedCoord d N,
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)) (Gauss.P d) := by
  classical
  obtain ⟨CwD, hCwD⟩ := hw.bddD
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  refine integrable_finsetSum _ fun q hq => ?_
  have hCwD0 : (0 : ℝ) ≤ CwD := le_trans (abs_nonneg _) (hCwD q hq 0)
  refine MeasureTheory.Integrable.const_mul ?_ _
  refine Gauss.integrable_of_continuous_of_bound
    ((hw.contD q hq).abs.mul (Gauss.continuous_coordD1 (h.slice hu) u q).norm)
    (C := CwD * (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) fun ω => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_norm]
  exact mul_le_mul (hCwD q hq ω) (Gauss.norm_coordD1_le (hC₁ u hu) _ q) (norm_nonneg _) hCwD0

/-- Off the good event the soft-cutoff weight vanishes, hence so does the Hölder factor. -/
theorem wscale_pow_eq_zero {p : ℕ} (hp : 1 ≤ p) {Y : Gauss.Ω d → ℝ} {ω : Gauss.Ω d}
    (hw0 : w ω = 0) : |wscale w p Y ω| ^ (2 * p - 1) = 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hz : wscale w p Y ω = 0 := by
    rw [wscale, hw0, Real.zero_rpow (by positivity), zero_mul]
  rw [hz, abs_zero, zero_pow (by omega : 2 * p - 1 ≠ 0)]

/-- **⭐⭐ Step C: the cross term of (★) against the (S5) pointwise bound.**

`Cs` is the (S5) constant (T265: `(2p)²·(15/8)/Θ·card^{1/(2r)}·K`, with `K` the *rescaled*
gradient rate of the weight), `Rte` the random same-time rate `√QV(Ψ_u)` and `Rbd` its
deterministic envelope **on the good event**.

⚠ Every hypothesis that could fail off the good event is restricted to it: `hwD` and `hS5`
hold only on `Good`, and off `Good` all that is asked is `hwDoff`, that the weight's
coordinate derivative vanishes — which is a **theorem** for the soft cutoff `χ(J̃/Θ)^{2p}`
outside the transition band (`RBM.Gauss.quadVar_softW_pow_eq_zero_of_outside_band`,
`RBM.Gauss.fderiv_softW_pow_eq_zero_of_sum_eq_zero`), not a fiat.  There is **no `∀ ω` size
assumption** anywhere. -/
theorem crossPart_le_of_S5 {p : ℕ} (hp : 1 ≤ p) (h : Gauss.TestFunT₁ d N T Ψ)
    (hw : Gauss.WeightC1 d N w wD) {u : ℝ} (hu : u ∈ T) (hu0 : 0 < u)
    {Wm : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {Rte : Gauss.Ω d → ℝ} {Cs Rbd : ℝ}
    (hW0 : ∀ ω, 0 ≤ w ω) (hCs0 : 0 ≤ Cs) (hRbd0 : 0 ≤ Rbd)
    {Good : Set (Gauss.Ω d)}
    (hwDoff : ∀ q ∈ Gauss.usedCoord d N, ∀ ω ∉ Good, wD q ω = 0)
    (hwD : ∀ q ∈ Gauss.usedCoord d N, ∀ ω ∈ Good,
      |wD q ω| ≤ √u * ‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖)
    (hS5 : ∀ ω ∈ Good, ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖
            * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)
        ≤ Cs * (|wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p - 1) * Rte ω))
    (hGood : ∀ ω ∈ Good, Rte ω ≤ Rbd)
    (hYm : MeasureTheory.AEStronglyMeasurable
      (wscale w p (flowY d N Ψ₁ u)) (Gauss.P d))
    (hYi : MeasureTheory.Integrable
      (fun ω => w ω * |flowY d N Ψ₁ u ω| ^ (2 * p)) (Gauss.P d))
    (hAi : MeasureTheory.Integrable
      (fun ω => |wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p - 1)) (Gauss.P d)) :
    crossPart d N Ψ wD u
      ≤ (1 / 2 : ℝ) * (Cs * Rbd)
        * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) := by
  classical
  have hsu : 0 < √u := Real.sqrt_pos.2 hu0
  set A : Gauss.Ω d → ℝ :=
    fun ω => |wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p - 1) with hA
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => pow_nonneg (abs_nonneg _) _
  -- pointwise: the `ℓ¹` sum is below `√u·Cs·Rbd·A`
  have hpt : ∀ ω, ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)
      ≤ √u * (Cs * Rbd) * A ω := by
    intro ω
    by_cases hg : ω ∈ Good
    case neg =>
      have hzero : ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖) = 0 := by
        refine Finset.sum_eq_zero fun q hq => ?_
        rw [hwDoff q hq ω hg, abs_zero, zero_mul, mul_zero]
      rw [hzero]
      have : 0 ≤ √u * (Cs * Rbd) * A ω := by
        have := hA0 ω
        have hs : (0 : ℝ) ≤ √u := Real.sqrt_nonneg u
        positivity
      exact this
    have h1 : ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)
        ≤ √u * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖
            * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      have hstep : |wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖
          ≤ (√u * ‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖)
            * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖ :=
        mul_le_mul_of_nonneg_right (hwD q hq ω hg) (norm_nonneg _)
      calc (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)
          ≤ (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
              ((√u * ‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖)
                * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖) :=
            mul_le_mul_of_nonneg_left hstep (Gauss.gvar d (Gauss.crd d N q)).2
        _ = √u * ((Gauss.gvar d (Gauss.crd d N q) : ℝ) *
              (‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖
                * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)) := by ring
    have h3 : A ω * Rte ω ≤ Rbd * A ω := by
      calc A ω * Rte ω ≤ A ω * Rbd :=
            mul_le_mul_of_nonneg_left (hGood ω hg) (hA0 ω)
        _ = Rbd * A ω := by ring
    calc ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (|wD q ω| * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖)
        ≤ √u * ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (‖Gauss.coordD1 d N Wm (Gauss.Hflow d N u ω) q‖
              * ‖Gauss.coordD1 d N (Ψ u) (Gauss.Hflow d N u ω) q‖) := h1
      _ ≤ √u * (Cs * (A ω * Rte ω)) :=
          mul_le_mul_of_nonneg_left (hS5 ω hg) hsu.le
      _ ≤ √u * (Cs * (Rbd * A ω)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hCs0) hsu.le
      _ = √u * (Cs * Rbd) * A ω := by ring
  -- integrate
  have hmono := MeasureTheory.integral_mono (integrable_crossSum h hw hu)
    (hAi.const_mul (√u * (Cs * Rbd))) hpt
  have hfin : (∫ ω, √u * (Cs * Rbd) * A ω ∂(Gauss.P d))
      ≤ √u * (Cs * Rbd) * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
          ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_wscale_pow_sub_one_le hp hW0 hYm hYi)
      (by positivity)
  refine le_trans (crossPart_le_integral h hw hu hu0) ?_
  have hchain := le_trans hmono hfin
  have hrw : (1 / (2 * √u)) * (√u * (Cs * Rbd)
        * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))))
      = (1 / 2 : ℝ) * (Cs * Rbd)
        * (∫ ω, w ω * |flowY d N Ψ₁ u ω| ^ (2 * p) ∂(Gauss.P d))
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) := by
    field_simp
  rw [← hrw]
  exact mul_le_mul_of_nonneg_left hchain (by positivity)

/-- The shape `RBM.APrimeDuhamelModel.momFlowDeriv_le` consumes: `crossPart ≤ 2p·φ^{…}·B`. -/
theorem crossPart_le_budget {p : ℕ} (hp : 1 ≤ p) {Cs Rbd φa : ℝ}
    (hstep : crossPart d N Ψ wD u ≤ (1 / 2 : ℝ) * (Cs * Rbd) * φa) :
    crossPart d N Ψ wD u ≤ 2 * (p : ℝ) * φa * ((Cs * Rbd) / (4 * (p : ℝ))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

/-! #### The `hBbd` arithmetic -/

/-- **⭐⭐ `hBbd`, via T271's first rescaling obligation.**  The Duhamel rescaling factor
`√(u_j/u)` is the one that carries the `u^{-1/2}` of the (S6) integrand
(`RBM.APrimeModel.sqrt_div_le_sqrt_inv`), and the surviving constant is absorbed into `κ̂`
by the explicit, checkable inequality `hfit : c² ≤ κ̂`. -/
theorem crossBudget_le_crossInt {u uj κh c : ℝ} {Qh : ℝ → ℝ} (hu : 0 < u) (huj : uj ≤ 1)
    (hc0 : 0 ≤ c) (hfit : c ^ 2 ≤ κh) :
    c * (√(uj / u) * √(Qh u)) ≤ APrimeModel.crossInt κh Qh u := by
  have hκ0 : (0 : ℝ) ≤ κh := le_trans (sq_nonneg c) hfit
  have hcs : c ≤ √κh := by
    nth_rewrite 1 [show c = √(c ^ 2) from (Real.sqrt_sq hc0).symm]
    exact Real.sqrt_le_sqrt hfit
  have h1 : √(uj / u) ≤ √u⁻¹ := APrimeModel.sqrt_div_le_sqrt_inv hu huj
  rw [APrimeModel.crossInt, Real.sqrt_mul hκ0]
  calc c * (√(uj / u) * √(Qh u))
      ≤ √κh * (√u⁻¹ * √(Qh u)) :=
        mul_le_mul hcs (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _))
          (by positivity) (Real.sqrt_nonneg _)
    _ = √u⁻¹ * (√κh * √(Qh u)) := by ring

/-- **⭐ `hBbd`, via T271's second rescaling obligation** — the reading in which the prefactor
`(2√u)⁻¹` of the fixed-`ω` generator identity supplies the `u^{-1/2}`
(`RBM.APrimeModel.inv_two_sqrt_le_sqrt_inv`). -/
theorem crossBudget_le_crossInt' {u κh c : ℝ} {Qh : ℝ → ℝ} (hu : 0 < u)
    (hc0 : 0 ≤ c) (hfit : c ^ 2 ≤ κh) :
    (2 * √u)⁻¹ * (c * √(Qh u)) ≤ APrimeModel.crossInt κh Qh u := by
  have hκ0 : (0 : ℝ) ≤ κh := le_trans (sq_nonneg c) hfit
  have hcs : c ≤ √κh := by
    nth_rewrite 1 [show c = √(c ^ 2) from (Real.sqrt_sq hc0).symm]
    exact Real.sqrt_le_sqrt hfit
  have h1 : (2 * √u)⁻¹ ≤ √u⁻¹ := APrimeModel.inv_two_sqrt_le_sqrt_inv hu
  rw [APrimeModel.crossInt, Real.sqrt_mul hκ0]
  calc (2 * √u)⁻¹ * (c * √(Qh u))
      ≤ √u⁻¹ * (√κh * √(Qh u)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right hcs (Real.sqrt_nonneg _))
          (by positivity) (Real.sqrt_nonneg _)
    _ = √u⁻¹ * (√κh * √(Qh u)) := rfl

/-! #### 7.1 The **evolved** quadratic-variation rate

⚠ T277 found that `RBM.APrimeModel.qvRate` is the **un-evolved** `quadVar (lkFun)`, while the
rate slot `g` of (G) — and the random rate of the (S5) cross term — is the quadratic variation
of the *evolved* functional `Ψ_u = (U_{u,t}∘(L−K)_u)_a / (T_{t,D}·R⁴)`.  The two are different
objects, so **nothing below reads `RBM.APrimeModel.qvRate`**; the evolved rate is defined here
and its (5.42) envelope enters as the **named, event-restricted** hypothesis
`RBM.APrimeDuhamelModel.EvolvedQVBound`, to be discharged by T277. -/

/-- **The evolved same-time rate** `QV(Ψ_u)` along the flow. -/
noncomputable def qvRateEvolved (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) (ω : Gauss.Ω d) : ℝ :=
  Gauss.quadVar d N (Ψ₁ u) (Gauss.Hflow d N u ω)

theorem qvRateEvolved_nonneg (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) (ω : Gauss.Ω d) :
    0 ≤ qvRateEvolved d N Ψ₁ u ω := Gauss.quadVar_nonneg _ _

/-- **T72's fulcrum**: the evolved rate is the paper's `∑_α |E^{(M)}(α)|²` of (5.42), by
`RBM.Gauss.secondOrder_eq_quadVar`.  This is the identification the (G) rate slot needs. -/
theorem qvRateEvolved_eq_quadVarPairs (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ) (ω : Gauss.Ω d) :
    qvRateEvolved d N Ψ₁ u ω
      = Gauss.quadVarPairs d N (Ψ₁ u) (Gauss.Hflow d N u ω) :=
  Gauss.secondOrder_eq_quadVar _ _

/-- The evolved rate, restricted to the good event: `0` where nothing is known. -/
noncomputable def qvRateEvolvedOn (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (Good : Set (Gauss.Ω d)) (u : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  Set.indicator Good (qvRateEvolved d N Ψ₁ u) ω

theorem qvRateEvolvedOn_nonneg (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (Good : Set (Gauss.Ω d)) (u : ℝ)
    (ω : Gauss.Ω d) : 0 ≤ qvRateEvolvedOn d N Ψ₁ Good u ω := by
  by_cases hg : ω ∈ Good
  · rw [qvRateEvolvedOn, Set.indicator_of_mem hg]
    exact qvRateEvolved_nonneg _ _ _ _ _
  · rw [qvRateEvolvedOn, Set.indicator_of_notMem hg]

/-- **The (5.42) envelope for the evolved rate, on an event.**

This is the one statement of this file that is still a *hypothesis* rather than a theorem: it
is T277's deliverable (`docs/CODEX-TICKETS.md` §5 — Minkowski `sqrt_wsum_sum_le`, then the
diagonal bound `quadVar_lkFun_le_ee_sym`, then the `U`-propagation).  It is written **with the
event restriction**, never `∀ ω`: on `Good` the a priori level is available and off it nothing
is claimed. -/
def EvolvedQVBound (d : Gauss.Dims) (N : ℕ)
    (Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (Good : Set (Gauss.Ω d)) (u Qev : ℝ) : Prop :=
  ∀ ω ∈ Good, qvRateEvolved d N Ψ₁ u ω ≤ Qev

/-- **The `Rbd` slot of `RBM.APrimeDuhamelModel.crossPart_le_of_S5`**, from the evolved
envelope.  Off `Good` the rate is `0`, so the bound holds there too. -/
theorem sqrt_qvRateEvolvedOn_le {d : Gauss.Dims} {N : ℕ}
    {Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {Good : Set (Gauss.Ω d)} {u Qev : ℝ}
    (hQev : 0 ≤ Qev) (hEv : EvolvedQVBound d N Ψ₁ Good u Qev) (ω : Gauss.Ω d) :
    √(qvRateEvolvedOn d N Ψ₁ Good u ω) ≤ √Qev := by
  refine Real.sqrt_le_sqrt ?_
  by_cases hg : ω ∈ Good
  · rw [qvRateEvolvedOn, Set.indicator_of_mem hg]
    exact hEv ω hg
  · rw [qvRateEvolvedOn, Set.indicator_of_notMem hg]
    exact hQev

/-- **⭐ The `g` slot of (G), below the (5.42) envelope.**  `RBM.APrimeModel.rateNormW_le_of_le_on`
at the **evolved** rate: the weighted `L^p` norm of `QV(Ψ_u)·1_{Good}` is below the
deterministic `Qev`. -/
theorem rateNormW_qvRateEvolvedOn_le {d : Gauss.Dims} {N : ℕ}
    {Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {Good : Set (Gauss.Ω d)} {u Qev : ℝ}
    {w : Gauss.Ω d → ℝ} (hW0 : ∀ ω, 0 ≤ w ω) (hW1 : ∀ ω, w ω ≤ 1) {p : ℕ} (hp : 1 ≤ p)
    (hQev : 0 ≤ Qev) (hEv : EvolvedQVBound d N Ψ₁ Good u Qev) :
    APrimeModel.rateNormW (Gauss.P d) w p (qvRateEvolvedOn d N Ψ₁ Good u) ≤ Qev := by
  refine APrimeModel.rateNormW_le_of_le_on hW0 hW1 hp hQev (G := Good)
    (fun ω hω => ?_) (fun ω hω => ?_)
  · rw [qvRateEvolvedOn, Set.indicator_of_mem hω,
      abs_of_nonneg (qvRateEvolved_nonneg _ _ _ _ _)]
    exact hEv ω hω
  · rw [qvRateEvolvedOn, Set.indicator_of_notMem hω]

/-- `EvolvedQVBound` is monotone in the event. -/
theorem EvolvedQVBound.mono {d : Gauss.Dims} {N : ℕ}
    {Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {u Qev : ℝ}
    (h : EvolvedQVBound d N Ψ₁ Set.univ u Qev) (Good : Set (Gauss.Ω d)) :
    EvolvedQVBound d N Ψ₁ Good u Qev := fun ω _ => h ω (Set.mem_univ ω)

/-- **A compiled satisfiability certificate for `EvolvedQVBound`.**

Every `RBM.Gauss.TestFunT₁` slice has a gradient bound `C₁` (field `bdd₁`), and that already
gives the crude envelope `QV(Ψ_u) ≤ C₁²·∑_α S_α‖B_α‖²`.  So the hypothesis is **not**
unsatisfiable, and `Qev` is strictly positive as soon as one Gaussian coordinate has
`S_α > 0` and `B_α ≠ 0` — the sharp `(5.42)` envelope T277 supplies replaces this one. -/
theorem evolvedQVBound_univ_of_bdd₁ {d : Gauss.Dims} {N : ℕ}
    {Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {u C₁ : ℝ}
    (hC₁ : ∀ M, ‖fderiv ℝ (Ψ₁ u) M‖ ≤ C₁) :
    EvolvedQVBound d N Ψ₁ Set.univ u (C₁ ^ 2 * coordWt2 d N) := by
  intro ω _
  rw [qvRateEvolved, Gauss.quadVar, coordWt2, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hb := Gauss.norm_coordD1_le hC₁ (Gauss.Hflow d N u ω) q
  have hsq : ‖Gauss.coordD1 d N (Ψ₁ u) (Gauss.Hflow d N u ω) q‖ ^ 2
      ≤ (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        ‖Gauss.coordD1 d N (Ψ₁ u) (Gauss.Hflow d N u ω) q‖ ^ 2
      ≤ (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Gauss.gvar d (Gauss.crd d N q)).2
    _ = C₁ ^ 2 * ((Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) := by ring

/-- **⭐⭐⭐ `hBbd` in the shape the slot needs.**

`Bc = Cs·Rbd/(4p)` is the cross-term budget produced by
`RBM.APrimeDuhamelModel.crossPart_le_budget`; with `Cs = Cs₀·√(u_j/u)` the (S5) constant
carrying the Duhamel rescaling and `Rbd = √(Q̂_u)` the (5.42) envelope of the **evolved** rate,
this says exactly `Bcr u ≤ crossInt κ̂ Q̂ u`.  The only arithmetic left is `hfit`, an
inequality between two explicit deterministic numbers. -/
theorem crossBudget_le_crossInt_model {p : ℕ} (hp : 1 ≤ p) {u uj κh Cs₀ : ℝ} {Qh : ℝ → ℝ}
    (hu : 0 < u) (huj : uj ≤ 1) (hCs₀ : 0 ≤ Cs₀)
    (hfit : (Cs₀ / (4 * (p : ℝ))) ^ 2 ≤ κh) :
    (Cs₀ * √(uj / u)) * √(Qh u) / (4 * (p : ℝ)) ≤ APrimeModel.crossInt κh Qh u := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hc0 : (0 : ℝ) ≤ Cs₀ / (4 * (p : ℝ)) := by positivity
  have hrw : (Cs₀ * √(uj / u)) * √(Qh u) / (4 * (p : ℝ))
      = (Cs₀ / (4 * (p : ℝ))) * (√(uj / u) * √(Qh u)) := by
    field_simp
  rw [hrw]
  exact crossBudget_le_crossInt hu huj hc0 hfit

/-! ### 8. Satisfiability

T264 delivered `RBM.Gauss.WeightC1` with **no** inhabitant.  The class is therefore checked
here, and not with a constant weight: `w(ω) = (1 + cos ω_e)/2` takes values in `[0,1]`, is
**not constant** (`cosW_ne`), and has a **nonvanishing** coordinate derivative
(`cosWD_ne_zero`).  So none of §2–§7 is vacuous for lack of a weight. -/

section Witness

open Classical in
/-- A non-constant `[0,1]`-valued weight of one Gaussian coordinate. -/
noncomputable def cosW (d : Gauss.Dims) (e : Gauss.Coord d) : Gauss.Ω d → ℝ :=
  fun ω => (1 + Real.cos (ω e)) / 2

open Classical in
/-- Its coordinate derivative. -/
noncomputable def cosWD (d : Gauss.Dims) (N : ℕ) (e : Gauss.Coord d) :
    (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ :=
  fun q ω => if Gauss.crd d N q = e then -(Real.sin (ω e)) / 2 else 0

theorem cosW_nonneg (d : Gauss.Dims) (e : Gauss.Coord d) (ω : Gauss.Ω d) :
    0 ≤ cosW d e ω := by
  have := Real.neg_one_le_cos (ω e)
  simp only [cosW]; linarith

theorem cosW_le_one (d : Gauss.Dims) (e : Gauss.Coord d) (ω : Gauss.Ω d) :
    cosW d e ω ≤ 1 := by
  have := Real.cos_le_one (ω e)
  simp only [cosW]; linarith

/-- **The weight is not constant.** -/
theorem cosW_ne (d : Gauss.Dims) (e : Gauss.Coord d) :
    cosW d e (fun _ => 0) ≠ cosW d e (fun _ => Real.pi) := by
  simp [cosW, Real.cos_pi]

/-- **The coordinate derivative does not vanish identically.** -/
theorem cosWD_ne_zero (d : Gauss.Dims) (N : ℕ) (q : d.Idx N × d.Idx N × Bool) :
    cosWD d N (Gauss.crd d N q) q (fun _ => Real.pi / 2) ≠ 0 := by
  simp [cosWD, Real.sin_pi_div_two]

/-- **⭐ A compiled, non-degenerate `RBM.Gauss.WeightC1`.** -/
theorem weightC1_cosW (d : Gauss.Dims) (N : ℕ) (e : Gauss.Coord d) :
    Gauss.WeightC1 d N (cosW d e) (cosWD d N e) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_const.add (Real.continuous_cos.comp (continuous_apply e))).div_const 2
  · intro q _
    by_cases hq : Gauss.crd d N q = e
    · have hfun : cosWD d N e q = fun ω : Gauss.Ω d => -(Real.sin (ω e)) / 2 := by
        funext ω; simp [cosWD, hq]
      rw [hfun]
      exact ((Real.continuous_sin.comp (continuous_apply e)).neg).div_const 2
    · have hfun : cosWD d N e q = fun _ : Gauss.Ω d => (0 : ℝ) := by
        funext ω; simp [cosWD, hq]
      rw [hfun]
      exact continuous_const
  · exact ⟨{e}, fun ω ω' hagree => by
      simp only [cosW, hagree e (Finset.mem_singleton_self e)]⟩
  · intro q _
    refine ⟨{e}, fun ω ω' hagree => ?_⟩
    simp only [cosWD]
    split_ifs with hq
    · rw [hagree e (Finset.mem_singleton_self e)]
    · rfl
  · intro q _ ω
    simp only [cosWD]
    split_ifs with hq
    · subst hq
      have hfun : (fun t : ℝ => cosW d (Gauss.crd d N q)
          (Function.update ω (Gauss.crd d N q) t))
          = fun t : ℝ => (1 + Real.cos t) / 2 := by
        funext t
        simp only [cosW, Function.update_self]
      rw [hfun]
      have hd := ((Real.hasDerivAt_cos (ω (Gauss.crd d N q))).const_add 1).div_const 2
      simpa using hd
    · have hfun : (fun t : ℝ => cosW d e (Function.update ω (Gauss.crd d N q) t))
          = fun _ : ℝ => cosW d e ω := by
        funext t
        simp only [cosW, Function.update_of_ne (Ne.symm hq)]
      rw [hfun]
      exact hasDerivAt_const _ _
  · exact ⟨1, fun ω => by
      rw [abs_of_nonneg (cosW_nonneg d e ω)]; exact cosW_le_one d e ω⟩
  · refine ⟨1 / 2, fun q _ ω => ?_⟩
    simp only [cosWD]
    split_ifs with hq
    · rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      have := Real.abs_sin_le_one (ω e)
      linarith
    · norm_num

/-- **Every moment family is a `RBM.APrimeDuhamelModel.IsModulusPow` pair**, by
`RBM.Gauss.momentFun_eq`.  In particular `RBM.Gauss.coefMomentObsT`, which is
`fun u M => momentFun (coefObsT … u) p M` by definition, is one with `Ψ₁ = coefObsT …` — so
the model family of route (A′) feeds §2–§7 with no adapter. -/
theorem isModulusPow_momentFun {d : Gauss.Dims} {N : ℕ}
    (F : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (p : ℕ) :
    IsModulusPow (fun u M => Gauss.momentFun (F u) p M) F p :=
  fun _ M => Gauss.momentFun_eq _ p M

/-- **A non-degenerate witness for `hBbd`.**  Every quantity is strictly positive: `c = 1`,
`κ̂ = 1`, `Q̂ ≡ 1`, `u_j = 1`, `u = 1/2` — no `Q ≡ 0`, no `κ̂ = 0`, and `u_j` is **not** sent to
`0`.  The conclusion is a genuine inequality between two positive numbers. -/
theorem sat_crossBudget_le_crossInt :
    (1 : ℝ) * (√(1 / (1 / 2 : ℝ)) * √((fun _ : ℝ => (1 : ℝ)) (1 / 2 : ℝ)))
      ≤ APrimeModel.crossInt 1 (fun _ => 1) (1 / 2 : ℝ) :=
  crossBudget_le_crossInt (u := 1 / 2) (uj := 1) (κh := 1) (c := 1)
    (Qh := fun _ => 1) (by norm_num) le_rfl zero_le_one (by norm_num)

end Witness

end APrimeDuhamelModel

end RBM
