/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVRateTime

/-!
# T316: the finite-size first-cell drift envelope of the actual Gaussian model

The envelope is the attained maximum of the weighted norm of the actual
`Uker ∘ driftF` rate, divided by the fixed endpoint normalization. This
constructs the constant `Qb` required by the first-cell deterministic
integral lemma, without asserting a bound uniform in the matrix size.
-/

namespace RBM.APrimeDriftEnvelope

open MeasureTheory Set Step2Bootstrap

/-- The actual prefix cutoff, driven by the model's `jSnorm`. -/
noncomputable def prefixWeight (d : Gauss.Dims) (E D : ℝ)
    (r : ℕ) (sGrid mesh : ℕ → ℝ) (N k : ℕ) (θ : ℝ) : Gauss.Ω d → ℝ :=
  APrimeWeight.prefixSoftW r
    (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D sGrid N u ω)
    sGrid mesh N k θ

theorem measurable_prefixWeight (d : Gauss.Dims) (E D : ℝ)
    (r : ℕ) (sGrid mesh : ℕ → ℝ) (N k : ℕ) (θ : ℝ) :
    Measurable (prefixWeight d E D r sGrid mesh N k θ) := by
  exact APrimeWeight.measurable_prefixSoftW r
    (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D sGrid N u ω)
    sGrid mesh N k θ
    (fun u => APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D sGrid N u)

theorem prefixWeight_nonneg (d : Gauss.Dims) (E D : ℝ)
    (r : ℕ) (sGrid mesh : ℕ → ℝ) (N k : ℕ) (θ : ℝ) (ω : Gauss.Ω d) :
    0 ≤ prefixWeight d E D r sGrid mesh N k θ ω := by
  exact softW_nonneg _ _ _ _

theorem prefixWeight_le_one (d : Gauss.Dims) (E D : ℝ)
    (r : ℕ) (sGrid mesh : ℕ → ℝ) (N k : ℕ) (θ : ℝ) (ω : Gauss.Ω d) :
    prefixWeight d E D r sGrid mesh N k θ ω ≤ 1 := by
  exact softW_le_one _ _ _ _

/-- The actual, weighted drift rate at the running time `u`. -/
noncomputable def driftRate (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ v u : ℝ) : ℝ :=
  MomentDuhamel.momNormW (Gauss.P d)
    (prefixWeight d E D r sGrid mesh N k θ) p
    (APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a 0 v u)

theorem driftRate_nonneg (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ v u : ℝ) :
    0 ≤ driftRate d E D N p r k a sGrid mesh θ v u := by
  exact MomentDuhamel.momNormW_nonneg (Gauss.P d)
    (fun ω => prefixWeight_nonneg d E D r sGrid mesh N k θ ω) p _

theorem continuousOn_driftRate (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ContinuousOn (driftRate d E D N p r k a sGrid mesh θ v) (Icc 0 v) := by
  exact APrimeDriftTimeFamily.continuousOn_momNormW_driftAt
    d E D N Step2.sigPM a hE le_rfl hv0 hv1
    (prefixWeight d E D r sGrid mesh N k θ)
    (measurable_prefixWeight d E D r sGrid mesh N k θ)
    (prefixWeight_nonneg d E D r sGrid mesh N k θ)
    (prefixWeight_le_one d E D r sGrid mesh N k θ) p

/-- At fixed finite size, the actual weighted rate attains a maximum on
the nonempty closed first cell. -/
theorem exists_max_driftRate (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ∃ u ∈ Icc (0 : ℝ) v,
      ∀ t ∈ Icc (0 : ℝ) v,
        driftRate d E D N p r k a sGrid mesh θ v t ≤
          driftRate d E D N p r k a sGrid mesh θ v u := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := v)).exists_isMaxOn
    ⟨0, ⟨le_rfl, hv0⟩⟩
    (continuousOn_driftRate d E D N p r k a sGrid mesh θ hE hv0 hv1)
  exact ⟨u, hu, fun t ht => hmax ht⟩

/-- A maximizer of the actual rate. This is a finite-size object. -/
noncomputable def maxTime (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) : ℝ :=
  Classical.choose (exists_max_driftRate d E D N p r k a sGrid mesh θ hE hv0 hv1)

/-- The model-pinned constant envelope for the actual first-cell drift. -/
noncomputable def QbActual (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) : ℝ :=
  driftRate d E D N p r k a sGrid mesh θ v
    (maxTime d E D N p r k a sGrid mesh θ hE hv0 hv1)

theorem maxTime_mem (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    maxTime d E D N p r k a sGrid mesh θ hE hv0 hv1 ∈ Icc (0 : ℝ) v :=
  (Classical.choose_spec
    (exists_max_driftRate d E D N p r k a sGrid mesh θ hE hv0 hv1)).1

theorem driftRate_le_QbActual (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) v) :
    driftRate d E D N p r k a sGrid mesh θ v u ≤
      QbActual d E D N p r k a sGrid mesh θ hE hv0 hv1 := by
  exact (Classical.choose_spec
    (exists_max_driftRate d E D N p r k a sGrid mesh θ hE hv0 hv1)).2 u hu

theorem QbActual_nonneg (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    0 ≤ QbActual d E D N p r k a sGrid mesh θ hE hv0 hv1 :=
  driftRate_nonneg d E D N p r k a sGrid mesh θ v _

theorem exists_attains_QbActual (d : Gauss.Dims) (E D : ℝ) (N p r k : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) (θ : ℝ) {v : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ∃ u ∈ Icc (0 : ℝ) v,
      driftRate d E D N p r k a sGrid mesh θ v u =
        QbActual d E D N p r k a sGrid mesh θ hE hv0 hv1 :=
  ⟨maxTime d E D N p r k a sGrid mesh θ hE hv0 hv1,
    maxTime_mem d E D N p r k a sGrid mesh θ hE hv0 hv1, rfl⟩

/-- A strict first cell with empty prefix, unit weight, and an attained
maximum of the model's actual drift rate. -/
theorem first_cell_witness (d : Gauss.Dims) (N : ℕ)
    (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) :
    (0 : ℝ) < 1 / 2 ∧
    (∀ ω : Gauss.Ω d,
      prefixWeight d 0 0 1 sGrid mesh N 0 1 ω = 1) ∧
    0 ≤ QbActual d 0 0 N 1 1 0 a sGrid mesh 1
      (by norm_num : |(0 : ℝ)| < 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) ∧
    ∃ u ∈ Icc (0 : ℝ) (1 / 2),
      driftRate d 0 0 N 1 1 0 a sGrid mesh 1 (1 / 2) u =
        QbActual d 0 0 N 1 1 0 a sGrid mesh 1
          (by norm_num : |(0 : ℝ)| < 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hv0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hv1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨by norm_num, ?_, QbActual_nonneg d 0 0 N 1 1 0 a sGrid mesh 1 hE hv0 hv1, ?_⟩
  · intro ω
    simp [prefixWeight, APrimeWeight.prefixSoftW, softW, softMax,
      Cutoff.cutChi_eq_one]
  · exact exists_attains_QbActual d 0 0 N 1 1 0 a sGrid mesh 1 hE hv0 hv1

#print axioms RBM.APrimeDriftEnvelope.exists_max_driftRate
#print axioms RBM.APrimeDriftEnvelope.driftRate_le_QbActual
#print axioms RBM.APrimeDriftEnvelope.QbActual_nonneg
#print axioms RBM.APrimeDriftEnvelope.exists_attains_QbActual
#print axioms RBM.APrimeDriftEnvelope.first_cell_witness

end RBM.APrimeDriftEnvelope
