/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeAssembly

#check @RBM.MomentDuhamel.weightedMinkowski_of_deriv_le
#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.APrimeDuhamelModel.continuousOn_momFlow
#check @RBM.APrimeInit.coordinate_integral_of_small_slots

/-!
# T285: time integrability in the Gaussian coordinate moment route

The moment norm is continuous on the closed flow window.  Consequently its
product with an integrable drift rate is integrable on every prefix.  The
remaining rates still require their own time integrability producers.
-/

namespace RBM.APrimeTimeIntegrability

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The third time-integrability premise of weighted Minkowski follows from
the first and continuity of the weighted moment. -/
theorem intervalIntegrable_momNormW_mul_of_AB
    {s v : ℝ} {p : ℕ} (hp : 1 ≤ p)
    {W : Ω → ℝ} {Y : ℝ → Ω → ℝ} {A B : ℝ → ℝ}
    (hcont : ContinuousOn
      (fun r => ∫ ω, W ω * |Y r ω| ^ (2 * p) ∂P) (Icc s v))
    (hAB : IntervalIntegrable (fun r => A r + B r) volume s v)
    {u : ℝ} (hu : u ∈ Icc s v) :
    IntervalIntegrable
      (fun r => MomentDuhamel.momNormW P W p (Y r) * (A r + B r)) volume s u := by
  have hp0 : (0 : ℝ) ≤ (1 : ℝ) / (2 * (p : ℝ)) := by positivity
  have hnorm : ContinuousOn (fun r => MomentDuhamel.momNormW P W p (Y r))
      (Icc s v) := by
    exact (Real.continuous_rpow_const hp0).comp_continuousOn hcont
  have hsub : Set.uIcc s u ⊆ Set.uIcc s v :=
    Set.uIcc_subset_uIcc_left (Set.Icc_subset_uIcc hu)
  have hAB' := hAB.mono_set hsub
  have hnorm' : ContinuousOn (fun r => MomentDuhamel.momNormW P W p (Y r))
      (Set.uIcc s u) := hnorm.mono (by
    rw [Set.uIcc_of_le hu.1]
    intro r hr
    exact ⟨hr.1, le_trans hr.2 hu.2⟩)
  exact hAB'.continuousOn_mul hnorm'

/-- For the Gaussian coordinate flow, the required continuity comes from
`TestFunT₁` and `WeightC1`; no separate product-integrability input is needed. -/
theorem intervalIntegrable_momNormW_mul_flowY
    {d : Gauss.Dims} {N : ℕ} {T : Set ℝ}
    {Ψ Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {w : Gauss.Ω d → ℝ}
    {wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ}
    {s v : ℝ} (hsv : s ≤ v) (hsub : Icc s v ⊆ T)
    {p : ℕ} (hp : 1 ≤ p)
    (h : Gauss.TestFunT₁ d N T Ψ)
    (hw : Gauss.WeightC1 d N w wD)
    (hre : APrimeDuhamelModel.IsModulusPow Ψ Ψ₁ p)
    {A B : ℝ → ℝ}
    (hAB : IntervalIntegrable (fun r => A r + B r) volume s v)
    {u : ℝ} (hu : u ∈ Icc s v) :
    IntervalIntegrable
      (fun r => MomentDuhamel.momNormW (Gauss.P d) w p
        (APrimeDuhamelModel.flowY d N Ψ₁ r) * (A r + B r)) volume s u :=
  intervalIntegrable_momNormW_mul_of_AB hp
    (APrimeDuhamelModel.continuousOn_momFlow h hw hre hsub) hAB hu

/-- The continuity-times-integrability interface has a Gaussian witness
with the nonconstant `cosW` weight, a nonzero observable, positive drift
rate, and a nontrivial window. -/
theorem positive_prefix_witness (d : Gauss.Dims) (e : Gauss.Coord d) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun r => MomentDuhamel.momNormW (Gauss.P d)
          (APrimeDuhamelModel.cosW d e) 1 (fun _ => (1 : ℝ)) * ((1 : ℝ) + 0))
        volume 0 u := by
  intro u hu
  have hcont : ContinuousOn
      (fun r : ℝ => ∫ ω : Gauss.Ω d,
        APrimeDuhamelModel.cosW d e ω * |(1 : ℝ)| ^ (2 * 1) ∂(Gauss.P d))
      (Icc (0 : ℝ) 1) := continuousOn_const
  have hAB : IntervalIntegrable (fun r : ℝ => (1 : ℝ) + 0) volume 0 1 := by
    simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
  exact intervalIntegrable_momNormW_mul_of_AB (P := Gauss.P d) (p := 1)
    (W := APrimeDuhamelModel.cosW d e) (Y := fun _ _ => 1)
    (A := fun _ => 1) (B := fun _ => 0)
    (by norm_num) hcont hAB hu

/-! The pointwise sample-space hypotheses in `momFlowDeriv_le` do not
constrain time dependence of its auxiliary drift variable. -/

/-- A constant Gaussian random variable has exactly its absolute value as
weighted moment norm under the unit weight. -/
theorem momNormW_const_gauss (d : Gauss.Dims) (c : ℝ) :
    MomentDuhamel.momNormW (Gauss.P d) (fun _ => (1 : ℝ)) 1
      (fun _ => c) = |c| := by
  simpa [MomentDuhamel.momNormW, Real.sqrt_eq_rpow] using (Real.sqrt_sq_eq_abs c)

theorem rateNormW_const_gauss (d : Gauss.Dims) (c : ℝ) :
    APrimeModel.rateNormW (Gauss.P d) (fun _ => (1 : ℝ)) 1
      (fun _ => c) = |c| := by
  simp [APrimeModel.rateNormW]

/-- Even for the actual Gaussian probability space and a nonzero observable,
pointwise finite moments of a time-dependent drift do not force an integrable
drift norm on the first cell.  This is the precise missing time-regularity
interface, rather than a numerical-budget claim. -/
theorem no_time_integrability_from_pointwise_gaussian_moments (d : Gauss.Dims) :
    ¬ (∀ G : ℝ → Gauss.Ω d → ℝ,
      (∀ u, Integrable (fun ω => |G u ω| ^ (2 : ℕ)) (Gauss.P d)) →
      IntervalIntegrable
        (fun u => MomentDuhamel.momNormW (Gauss.P d) (fun _ => (1 : ℝ)) 1 (G u))
        volume 0 1) := by
  intro h
  let G : ℝ → Gauss.Ω d → ℝ := fun u _ => u⁻¹
  have hpt : ∀ u, Integrable (fun ω => |G u ω| ^ (2 : ℕ)) (Gauss.P d) := by
    intro u
    simpa [G] using (integrable_const (μ := Gauss.P d) (|u⁻¹| ^ (2 : ℕ)))
  have hi := h G hpt
  have hfun : (fun u => MomentDuhamel.momNormW (Gauss.P d)
      (fun _ => (1 : ℝ)) 1 (G u)) = fun u : ℝ => |u⁻¹| := by
    funext u
    exact momNormW_const_gauss d _
  rw [hfun] at hi
  have hInv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume 0 1 :=
    hi.congr_uIoo (by
      intro u hu
      rw [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] at hu
      exact abs_of_nonneg (inv_nonneg.mpr (le_of_lt hu.1)))
  have hnot : ¬ IntervalIntegrable (fun u : ℝ => u⁻¹) volume 0 1 := by
    simp [intervalIntegrable_inv_iff]
  exact hnot hInv

/-- The quadratic-variation norm has the same missing time-regularity
interface, even though every fixed-time Gaussian moment is finite. -/
theorem no_time_integrability_from_pointwise_gaussian_qv (d : Gauss.Dims) :
    ¬ (∀ Q : ℝ → Gauss.Ω d → ℝ,
      (∀ u, Integrable (fun ω => |Q u ω|) (Gauss.P d)) →
      IntervalIntegrable
        (fun u => APrimeModel.rateNormW (Gauss.P d) (fun _ => (1 : ℝ)) 1 (Q u))
        volume 0 1) := by
  intro h
  let Q : ℝ → Gauss.Ω d → ℝ := fun u _ => u⁻¹
  have hpt : ∀ u, Integrable (fun ω => |Q u ω|) (Gauss.P d) := by
    intro u
    simpa [Q] using (integrable_const (μ := Gauss.P d) |u⁻¹|)
  have hi := h Q hpt
  have hfun : (fun u => APrimeModel.rateNormW (Gauss.P d)
      (fun _ => (1 : ℝ)) 1 (Q u)) = fun u : ℝ => |u⁻¹| := by
    funext u
    exact rateNormW_const_gauss d _
  rw [hfun] at hi
  have hInv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume 0 1 :=
    hi.congr_uIoo (by
      intro u hu
      rw [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] at hu
      exact abs_of_nonneg (inv_nonneg.mpr (le_of_lt hu.1)))
  have hnot : ¬ IntervalIntegrable (fun u : ℝ => u⁻¹) volume 0 1 := by
    simp [intervalIntegrable_inv_iff]
  exact hnot hInv

#print axioms RBM.APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_of_AB
#print axioms RBM.APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
#print axioms RBM.APrimeTimeIntegrability.positive_prefix_witness
#print axioms RBM.APrimeTimeIntegrability.no_time_integrability_from_pointwise_gaussian_moments
#print axioms RBM.APrimeTimeIntegrability.no_time_integrability_from_pointwise_gaussian_qv

end RBM.APrimeTimeIntegrability
