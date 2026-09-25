/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleDensityMeasure

/-!
# Exact support of the semicircle density measure

The density is positive on every open interval contained in `(-2, 2)`. The
closedness of measure support then adds the two endpoints.
-/

namespace RBM

open MeasureTheory Set

/-- Every point in the open semicircle interval belongs to the measure support. -/
theorem semicircleMeasure_Ioo_subset_support :
    Ioo (-2 : ℝ) 2 ⊆ semicircleMeasure.support := by
  intro x hx
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hUopen
  obtain ⟨a, b, hxab, hIooU⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hUopen.mem_nhds hxU)
  let c := max a (-2 : ℝ)
  let d := min b (2 : ℝ)
  have hcx : c < x := (max_lt_iff).2 ⟨hxab.1, hx.1⟩
  have hxd : x < d := (lt_min_iff).2 ⟨hxab.2, hx.2⟩
  have hcd : c < d := hcx.trans hxd
  have hcb : -2 ≤ c := le_max_right _ _
  have hdb : d ≤ 2 := min_le_right _ _
  have hsub : Ioo c d ⊆ U := by
    intro y hy
    exact hIooU ⟨(lt_of_le_of_lt (le_max_left _ _) hy.1),
      (lt_of_lt_of_le hy.2 (min_le_left _ _))⟩
  exact lt_of_lt_of_le
    (semicircleMeasure_Ioo_pos hcb hcd hdb)
    (measure_mono hsub)

/-- The exact topological support of the semicircle density measure is `[-2, 2]`. -/
theorem semicircleMeasure_support_eq :
    semicircleMeasure.support = Icc (-2 : ℝ) 2 := by
  apply Set.Subset.antisymm semicircleMeasure_support_subset
  have hclosed : IsClosed semicircleMeasure.support := Measure.isClosed_support
  have hclosure : closure (Ioo (-2 : ℝ) 2) ⊆ semicircleMeasure.support :=
    closure_minimal semicircleMeasure_Ioo_subset_support hclosed
  simpa [closure_Ioo (by norm_num : (-2 : ℝ) ≠ 2)] using hclosure

theorem semicircleMeasure_zero_mem_support :
    (0 : ℝ) ∈ semicircleMeasure.support := by
  rw [semicircleMeasure_support_eq]
  norm_num

theorem semicircleMeasure_leftEndpoint_mem_support :
    (-2 : ℝ) ∈ semicircleMeasure.support := by
  rw [semicircleMeasure_support_eq]
  norm_num

theorem semicircleMeasure_rightEndpoint_mem_support :
    (2 : ℝ) ∈ semicircleMeasure.support := by
  rw [semicircleMeasure_support_eq]
  norm_num

#print axioms semicircleMeasure_Ioo_subset_support
#print axioms semicircleMeasure_support_eq
#print axioms semicircleMeasure_zero_mem_support
#print axioms semicircleMeasure_leftEndpoint_mem_support
#print axioms semicircleMeasure_rightEndpoint_mem_support

end RBM
