/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVRateCore
import RBM1D.Gauss.APrimeNormalizedGenerator
import RBM1D.Gauss.APrimeWeight

/-! # T294: time integrability of the actual evolved Gaussian QV rate -/

#check @RBM.APrimeDriftTimeFamily.qvAt
#check @RBM.APrimeDriftTimeFamily.coordAt
#check @RBM.Gauss.differentiableAt_ukerObsT_pair
#check @RBM.Gauss.bddC2C_ukerObsT
#check @RBM.Gauss.continuous_ukerRow
#check @measurable_fderiv_with_param
#check @MeasureTheory.StronglyMeasurable.integral_prod_right'
#check @RBM.APrimeWeight.measurable_prefixSoftW
#check @RBM.APrimeSlotFields.measurable_jSnorm

namespace RBM.APrimeQVRateTime

open MeasureTheory Set Step2Bootstrap
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

/-- The time rate is Borel measurable on the closed-window subtype; this
uses joint parameterized matrix-derivative measurability. -/
theorem measurable_rateNormW_qvAt_window (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (w : Gauss.Ω d → ℝ) (hw : Measurable w) :
    Measurable (fun r : Icc s v => APrimeModel.rateNormW (Gauss.P d) w p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v r.1)) := by
  have hq := measurable_qvAt_on_window d E D N σ a hE hs0 hsv hv1
  have hintg : Measurable (fun q : (Icc s v) × Gauss.Ω d =>
      w q.2 * |APrimeDriftTimeFamily.qvAt d E D N σ a s v q.1.1 q.2| ^ p) :=
    (hw.comp measurable_snd).mul ((continuous_abs.measurable.comp hq).pow_const p)
  have hint : StronglyMeasurable (fun r : Icc s v =>
      ∫ ω, w ω * |APrimeDriftTimeFamily.qvAt d E D N σ a s v r.1 ω| ^ p
        ∂(Gauss.P d)) := by
    exact hintg.stronglyMeasurable.integral_prod_right'
  exact (Real.continuous_rpow_const
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ))).measurable.comp hint.measurable

/-- The actual, uncut evolved-QV rate is time integrable for every fixed
measurable sample weight between zero and one. -/
theorem intervalIntegrable_rateNormW_qvAt (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hp : 1 ≤ p) (w : Gauss.Ω d → ℝ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1) :
    IntervalIntegrable (fun r => APrimeModel.rateNormW (Gauss.P d) w p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v r)) volume s v := by
  obtain ⟨C, hC0, hQ⟩ := exists_bdd_qvAt d E D N σ a hE hs0 hsv hv1
  let f : ℝ → ℝ := fun r => APrimeModel.rateNormW (Gauss.P d) w p
    (APrimeDriftTimeFamily.qvAt d E D N σ a s v r)
  have hmeas : Measurable (fun r : Icc s v => f r.1) :=
    measurable_rateNormW_qvAt_window d E D N p σ a hE hs0 hsv hv1 w hw
  have hbd : ∀ r : Icc s v, ‖f r.1‖ ≤ C := by
    intro ⟨r, hr⟩
    have hnonneg := APrimeModel.rateNormW_nonneg (P := Gauss.P d) hw0 p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v r)
    have hle : f r ≤ C := by
      apply APrimeModel.rateNormW_le_of_le_on (P := Gauss.P d) hw0 hw1 hp hC0
        (G := Set.univ)
      · intro ω _
        rw [abs_of_nonneg (hQ r hr ω).1]
        exact (hQ r hr ω).2
      · intro ω hω
        exact False.elim (hω (Set.mem_univ ω))
    simpa [f, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  let μ : Measure (Icc s v) := volume.comap ((↑) : Icc s v → ℝ)
  haveI hcompact : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  haveI : IsFiniteMeasure μ := inferInstance
  have hint : Integrable (fun r : Icc s v => f r.1) μ :=
    Integrable.of_bound hmeas.stronglyMeasurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbd)
  have hintOn : IntegrableOn f (Icc s v) volume :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).2 hint
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).2 hintOn

/-- Specialization to the actual prefix soft weight driven by measurable
`jSnorm`; the QV itself remains uncut. -/
theorem intervalIntegrable_rateNormW_prefixSoftW (d : Gauss.Dims) (E D : ℝ)
    (N p r k : ℕ) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2)
    (sGrid mesh : ℕ → ℝ) (θ : ℝ) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hp : 1 ≤ p) :
    IntervalIntegrable (fun u => APrimeModel.rateNormW (Gauss.P d)
      (APrimeWeight.prefixSoftW r
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D sGrid N u ω)
        sGrid mesh N k θ) p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v u)) volume s v := by
  let J : ℕ → ℝ → Gauss.Ω d → ℝ :=
    fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D sGrid N u ω
  let w : Gauss.Ω d → ℝ := APrimeWeight.prefixSoftW r J sGrid mesh N k θ
  have hw : Measurable w :=
    APrimeWeight.measurable_prefixSoftW r J sGrid mesh N k θ
      (fun u => APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D sGrid N u)
  have hw0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact softW_nonneg _ _ _ _
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    exact softW_le_one _ _ _ _
  exact intervalIntegrable_rateNormW_qvAt d E D N p σ a hE hs0 hsv hv1 hp
    w hw hw0 hw1

/-- The empty-prefix first cell has a genuinely positive time length and
unit soft weight. -/
theorem first_cell_empty_prefix_witness (d : Gauss.Dims) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) :
    (∀ ω : Gauss.Ω d,
      APrimeWeight.prefixSoftW 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 0 sGrid N u ω)
        sGrid mesh N 0 1 ω = 1) ∧
    IntervalIntegrable (fun u => APrimeModel.rateNormW (Gauss.P d)
      (APrimeWeight.prefixSoftW 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 0 sGrid N u ω)
        sGrid mesh N 0 1) 1
      (APrimeDriftTimeFamily.qvAt d 0 0 N σ a 0 (1 / 2) u))
      volume 0 (1 / 2) ∧
    (0 : ℝ) < 1 / 2 := by
  constructor
  · intro ω
    simp [APrimeWeight.prefixSoftW, softW, softMax, Cutoff.cutChi_eq_one]
  constructor
  · exact intervalIntegrable_rateNormW_prefixSoftW d 0 0 N 1 1 0 σ a
      sGrid mesh 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · norm_num

#print axioms RBM.APrimeQVRateTime.measurable_qvAt_on_window
#print axioms RBM.APrimeQVRateTime.exists_bdd_qvAt
#print axioms RBM.APrimeQVRateTime.intervalIntegrable_rateNormW_qvAt
#print axioms RBM.APrimeQVRateTime.intervalIntegrable_rateNormW_prefixSoftW
#print axioms RBM.APrimeQVRateTime.first_cell_empty_prefix_witness

end RBM.APrimeQVRateTime
