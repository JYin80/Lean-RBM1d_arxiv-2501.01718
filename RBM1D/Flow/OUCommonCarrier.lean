/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUMarginalGaussian

/-!
# One carrier for all fixed-time OU marginals

The common probability space is the product of the actual band field and a sequence of
independent normalized GUE fields, one for each size parameter.  Its projection at any size has
the product law used by `OUMarginalGaussian`.  This transports the existing fixed-time laws; it
does not construct a Brownian OU process or assert an (7.26) terminal law.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Gauss

/-- The common sample space carrying one band field and a GUE field at every size. -/
abbrev ouCommonOmega (d : Dims) : Type := Ω d × (ℕ → Ω d)

/-- A single probability measure carrying the band field and all size-indexed GUE fields. -/
noncomputable def ouCommonMeasure (d : Dims) : Measure (ouCommonOmega d) :=
  (P d).prod (Measure.infinitePi fun N => gueMeasure d N)

instance ouCommonMeasure_isProbabilityMeasure (d : Dims) :
    IsProbabilityMeasure (ouCommonMeasure d) := by
  unfold ouCommonMeasure
  infer_instance

/-- Projection to the band field and the GUE field at one requested size. -/
def ouCommonProjection (d : Dims) (N : ℕ) : ouCommonOmega d → Ω d × Ω d :=
  fun ω => (ω.1, ω.2 N)

theorem ouCommonProjection_measurable (d : Dims) (N : ℕ) :
    Measurable (ouCommonProjection d N) := by
  change Measurable (fun ω : Ω d × (ℕ → Ω d) => (ω.1, ω.2 N))
  fun_prop

/-- Every size projection pushes the common measure to the accepted T1401 product measure.
This includes `N = 0`. -/
theorem ouCommonProjection_map (d : Dims) (N : ℕ) :
    (ouCommonMeasure d).map (ouCommonProjection d N) = ouProductMeasure d N := by
  change Measure.map (Prod.map id (fun g : ℕ → Ω d => g N))
      ((P d).prod (Measure.infinitePi fun n => gueMeasure d n)) = ouProductMeasure d N
  rw [← Measure.map_prod_map (P d) (Measure.infinitePi fun n => gueMeasure d n)
    measurable_id (measurable_pi_apply N)]
  simp [ouProductMeasure, Measure.infinitePi_map_eval]

/-- The projection is measure-preserving onto the corresponding accepted finite-size space. -/
theorem ouCommonProjection_measurePreserving (d : Dims) (N : ℕ) :
    MeasurePreserving (ouCommonProjection d N) (ouCommonMeasure d) (ouProductMeasure d N) :=
  ⟨ouCommonProjection_measurable d N, ouCommonProjection_map d N⟩

/-- The existing band geometry carried by the common probability space.  All parameters of
`d`, including its bandwidth exponent, remain fixed before the eventual-size fields. -/
noncomputable def ouCommonBand (d : Dims) : RBM.Band (ouCommonOmega d) where
  P := ouCommonMeasure d
  isProbabilityMeasure := ouCommonMeasure_isProbabilityMeasure d
  W := d.W
  L := d.L
  W_pos := d.W_pos
  three_le_L := d.three_le_L
  dim := d.dim
  c := d.c
  c_pos := d.c_pos
  bandwidth := d.bandwidth

/-- On the common carrier, every finite collection of primitive coordinates of the size-`N`
fixed-time interpolation has the accepted joint Gaussian law. -/
theorem ouCommon_fixedTimeMarginal_jointGaussian (d : Dims) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (I : Finset (Coord d)) :
    HasGaussianLaw
      (fun ω : ouCommonOmega d =>
        ouCoordinateVector d N t I (ouCommonProjection d N ω))
      (ouCommonMeasure d) := by
  have hLaw := fixedTimeMarginal_jointGaussian d N t ht I
  have hcoord : Measurable (fun z : Ω d × Ω d => ouCoordinateVector d N t I z) := by
    apply measurable_pi_iff.mpr
    intro c
    simp only [ouCoordinateVector]
    dsimp [ouCoordinate]
    fun_prop
  have hproj := ouCommonProjection_measurable d N
  refine ⟨(hcoord.comp hproj).aemeasurable, ?_⟩
  change IsGaussian
    (Measure.map ((fun z : Ω d × Ω d => ouCoordinateVector d N t I z) ∘
      ouCommonProjection d N) (ouCommonMeasure d))
  rw [← Measure.map_map hcoord hproj, ouCommonProjection_map]
  exact hLaw.2

/-- The accepted (7.25) entry-covariance formula transported to the common carrier, for each
deterministic nonnegative time and every size parameter. -/
theorem ouCommon_ouMatrix_entry_covariance (d : Dims) (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (i j : d.Idx N) :
    ∫ ω, ‖ouMatrix d N t (ouCommonProjection d N ω) i j‖ ^ 2 ∂(ouCommonMeasure d) =
      (1 - ouZeta t) * Sblk (d.L N) (d.W N) i j +
        ouZeta t / (ouMatrixSize d N : ℝ) := by
  let f : Ω d × Ω d → ℝ := fun ω => ‖ouMatrix d N t ω i j‖ ^ 2
  have hsample : Measurable (ouInterpolatedSample d N t) := by
    apply measurable_pi_iff.mpr
    intro c
    simp only [ouInterpolatedSample]
    fun_prop
  have hentry : Measurable (fun z : Ω d × Ω d =>
      Xentry d N (ouInterpolatedSample d N t z) i j) :=
    (measurable_Xentry d N i j).comp hsample
  have hf : Measurable f := by
    dsimp [f]
    convert hentry.norm.pow_const 2 using 1
    funext z
    rw [ouMatrix_entry_eq_interpolatedSample]
  have hfm : AEStronglyMeasurable f
      ((ouCommonMeasure d).map (ouCommonProjection d N)) := by
    rw [ouCommonProjection_map]
    exact hf.aestronglyMeasurable
  calc
    ∫ ω, ‖ouMatrix d N t (ouCommonProjection d N ω) i j‖ ^ 2 ∂(ouCommonMeasure d) =
        ∫ z, f z ∂((ouCommonMeasure d).map (ouCommonProjection d N)) := by
          change ∫ ω, f (ouCommonProjection d N ω) ∂(ouCommonMeasure d) = _
          exact (integral_map (ouCommonProjection_measurable d N).aemeasurable hfm).symm
    _ = (1 - ouZeta t) * Sblk (d.L N) (d.W N) i j +
          ouZeta t / (ouMatrixSize d N : ℝ) := by
      rw [ouCommonProjection_map]
      exact ouMatrix_entry_covariance d N t ht i j

/-- A same-sample nonzero band/GUE witness on the common carrier for `exampleGrow`.  The second
coordinate is constant away from the selected size, so its size-`N` projection is exactly the
accepted T1401 witness sample. -/
theorem exampleGrow_ouCommon_nonzero_witness (N : ℕ) :
    ∃ (i : Dims.exampleGrow.Idx N) (ω : ouCommonOmega Dims.exampleGrow),
      ouBandMatrix Dims.exampleGrow N (ouCommonProjection Dims.exampleGrow N ω) i i ≠ 0 ∧
        ouGueMatrix Dims.exampleGrow N (ouCommonProjection Dims.exampleGrow N ω) i i ≠ 0 := by
  obtain ⟨i, ω, hx, hg⟩ := exampleGrow_ouBandGue_nonzero_witness N
  refine ⟨i, (ω.1, fun _ => ω.2), ?_, ?_⟩
  · simpa [ouCommonProjection] using hx
  · simpa [ouCommonProjection] using hg

end RBM.Gauss
