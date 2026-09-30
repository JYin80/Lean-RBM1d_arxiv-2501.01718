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

/-- Every size projection pushes the common measure to the product measure
`ouProductMeasure d N`.
This includes `N = 0`. -/
theorem ouCommonProjection_map (d : Dims) (N : ℕ) :
    (ouCommonMeasure d).map (ouCommonProjection d N) = ouProductMeasure d N := by
  change Measure.map (Prod.map id (fun g : ℕ → Ω d => g N))
      ((P d).prod (Measure.infinitePi fun n => gueMeasure d n)) = ouProductMeasure d N
  rw [← Measure.map_prod_map (P d) (Measure.infinitePi fun n => gueMeasure d n)
    measurable_id (measurable_pi_apply N)]
  simp [ouProductMeasure, Measure.infinitePi_map_eval]

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

end RBM.Gauss
