/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Finite Gaussian support and local measurable-core retention

This file isolates two low-level measure-theoretic facts used by the Gaussian layer.

First, a finite family of coordinates has full support only after coordinates of zero variance
are removed.  `effectiveCoords d J` performs exactly that removal.  On the original sample space,
the corresponding support event is the effective open cylinder intersected with `zeroFix d J`,
which fixes every discarded coordinate at zero.  This hybrid cylinder is measurable and has the
same positive mass as its effective part.

Second, `local_core_retention` records the local consequence of replacing an arbitrary carrier
`R` by a subset `C` having the same complement measure.  It requires measurability only of the
local set `U`, not of `R`, and deliberately makes no global null-difference claim about `R \ C`.

These facts are internal consequences of the formal Gaussian model and Mathlib.  Formula (5.42)
of the paper is an evolved quadratic-variation estimate and supplies no support theorem.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open Set

/-- The coordinates in `J` whose Gaussian variance is nonzero. -/
noncomputable def effectiveCoords (d : Dims) (J : Finset (Coord d)) : Finset (Coord d) :=
  J.filter fun c => gvar d c ≠ 0

/-- A finite product of nondegenerate real Gaussian measures is positive on every nonempty open
set. -/
theorem gaussian_pi_open_pos (d : Dims) (I : Finset (Coord d))
    (hvar : ∀ c : I, gvar d c.1 ≠ 0) :
    Measure.IsOpenPosMeasure (Measure.pi fun c : I => gaussianReal 0 (gvar d c.1)) := by
  letI (c : I) : Measure.IsOpenPosMeasure (gaussianReal 0 (gvar d c.1)) :=
    (gaussianReal_absolutelyContinuous' 0 (hvar c)).isOpenPosMeasure
  infer_instance

/-- Every nonempty open cylinder on a finite subtype of nonzero-variance coordinates has positive
`P d`-mass.  The quantifier in `U` is exactly over the subtype `c : I`. -/
theorem effective_open_cylinder_pos (d : Dims) (I : Finset (Coord d))
    (hvar : ∀ c : I, gvar d c.1 ≠ 0) {U : Set (∀ c : I, Real)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    0 < P d (I.restrict ⁻¹' U) := by
  rw [← Measure.map_apply (Finset.measurable_restrict I) hU.measurableSet, P_map_restrict]
  letI := gaussian_pi_open_pos d I hvar
  exact hU.measure_pos _ hne

/-- The finite event fixing every zero-variance coordinate in `J` at its Dirac value `0`. -/
def zeroFix (d : Dims) (J : Finset (Coord d)) : Set (Ω d) :=
  {omega | ∀ c ∈ J, gvar d c = 0 → omega c = 0}

/-- A zero-variance Gaussian coordinate is almost surely its Dirac value `0`. -/
theorem zero_variance_coord_ae_zero (d : Dims) (c : Coord d) (hvar : gvar d c = 0) :
    ∀ᵐ omega ∂(P d), omega c = 0 := by
  refine ae_of_ae_map (μ := P d) (f := fun omega : Ω d => omega c)
    (p := fun x : ℝ => x = 0) (measurable_pi_apply c).aemeasurable ?_
  rw [P_map_eval, hvar, gaussianReal_zero_var]
  simp

/-- All zero-variance coordinates in a finite set are simultaneously almost surely zero. -/
theorem zero_variance_coords_ae_zero (d : Dims) (J : Finset (Coord d)) :
    ∀ᵐ omega ∂(P d), omega ∈ zeroFix d J := by
  change ∀ᵐ omega ∂(P d), ∀ c ∈ J, gvar d c = 0 → omega c = 0
  rw [Filter.eventually_all_finset]
  intro c hc
  by_cases hvar : gvar d c = 0
  · filter_upwards [zero_variance_coord_ae_zero d c hvar] with omega homega
    exact fun _ => homega
  · exact Filter.Eventually.of_forall fun _ hzero => (hvar hzero).elim

/-- The finite zero-coordinate fixing event is measurable. -/
theorem zeroFix_measurable (d : Dims) (J : Finset (Coord d)) : MeasurableSet (zeroFix d J) := by
  rw [show zeroFix d J = ⋂ c ∈ J, if gvar d c = 0 then {omega | omega c = 0} else Set.univ by
    ext omega
    simp only [zeroFix, Set.mem_iInter]
    constructor
    · intro h c hc
      split_ifs with hvar
      · exact h c hc hvar
      · trivial
    · intro h c hc hvar
      simpa [hvar] using h c hc]
  refine J.measurableSet_biInter fun c _ => ?_
  split_ifs
  · exact measurableSet_eq_fun (measurable_pi_apply c) measurable_const
  · exact MeasurableSet.univ

/-- The full-sample-space support cylinder: open on the effective coordinates and fixed at zero on
the zero-variance coordinates. -/
def supportCylinder (d : Dims) (J : Finset (Coord d))
    (U : Set (∀ c : effectiveCoords d J, Real)) : Set (Ω d) :=
  (effectiveCoords d J).restrict ⁻¹' U ∩ zeroFix d J

/-- A hybrid support cylinder over a measurable effective-coordinate set is measurable. -/
theorem support_cylinder_measurable (d : Dims) (J : Finset (Coord d))
    {U : Set (∀ c : effectiveCoords d J, Real)} (hU : MeasurableSet U) :
    MeasurableSet (supportCylinder d J U) := by
  exact (hU.preimage (Finset.measurable_restrict _)).inter (zeroFix_measurable d J)

/-- A hybrid support cylinder over a nonempty open effective-coordinate set has positive mass. -/
theorem support_cylinder_pos (d : Dims) (J : Finset (Coord d))
    {U : Set (∀ c : effectiveCoords d J, Real)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    0 < P d (supportCylinder d J U) := by
  rw [supportCylinder, inter_comm,
    Measure.measure_inter_eq_of_ae (zero_variance_coords_ae_zero d J)]
  exact effective_open_cylinder_pos d (effectiveCoords d J)
    (fun c => (Finset.mem_filter.1 c.property).2) hU hne

/-- Local retention under a finite measure.  If `C ⊆ R` and the complements have equal mass,
then every measurable `U ⊆ R` retains all of its mass after intersection with `C`.

No measurability of `R` or `C` is assumed. -/
theorem local_core_retention {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P] {R C U : Set Omega}
    (hCsub : C ⊆ R) (hcompl : P Cᶜ = P Rᶜ)
    (hU : MeasurableSet U) (hUR : U ⊆ R) :
    P (U ∩ C) = P U := by
  have hRcompl : Rᶜ ⊆ Cᶜ := compl_subset_compl.mpr hCsub
  have hRU : Rᶜ ∩ U = ∅ := by
    ext omega
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact fun homega => homega.1 (hUR homega.2)
  have hEq : P (Rᶜ ∩ U) = P (Cᶜ ∩ U) :=
    Measure.measure_inter_eq_of_measure_eq hU hcompl.symm hRcompl (measure_ne_top P _)
  have hnull : P (U ∩ Cᶜ) = 0 := by
    rw [inter_comm, ← hEq, hRU, measure_empty]
  simpa [Set.sdiff_eq] using (measure_sdiff_null' hnull)

/-- Direct `toMeasurable` check of local retention.  This proof uses
`Measure.measure_toMeasurable_inter` directly and, like `local_core_retention`, does not assume
that `R` is measurable. -/
theorem direct_toMeasurable_retention {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P] {R U : Set Omega}
    (hU : MeasurableSet U) (hUR : U ⊆ R) :
    P (U ∩ (toMeasurable P Rᶜ)ᶜ) = P U := by
  have hRU : Rᶜ ∩ U = ∅ := by
    ext omega
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact fun homega => homega.1 (hUR homega.2)
  have hEq : P (toMeasurable P Rᶜ ∩ U) = P (Rᶜ ∩ U) :=
    Measure.measure_toMeasurable_inter hU (measure_ne_top P _)
  have hnull : P (U ∩ toMeasurable P Rᶜ) = 0 := by
    rw [inter_comm, hEq, hRU, measure_empty]
  simpa [Set.sdiff_eq] using (measure_sdiff_null' hnull)

end RBM.Gauss

#print axioms RBM.Gauss.effectiveCoords
#print axioms RBM.Gauss.gaussian_pi_open_pos
#print axioms RBM.Gauss.effective_open_cylinder_pos
#print axioms RBM.Gauss.zeroFix
#print axioms RBM.Gauss.zero_variance_coord_ae_zero
#print axioms RBM.Gauss.zero_variance_coords_ae_zero
#print axioms RBM.Gauss.zeroFix_measurable
#print axioms RBM.Gauss.supportCylinder
#print axioms RBM.Gauss.support_cylinder_measurable
#print axioms RBM.Gauss.support_cylinder_pos
#print axioms RBM.Gauss.local_core_retention
#print axioms RBM.Gauss.direct_toMeasurable_retention
