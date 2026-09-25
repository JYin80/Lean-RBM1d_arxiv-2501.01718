/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleCDFStrict
import RBM1D.Defs.SemicircleCDFContinuous
import RBM1D.Defs.SemicircleCDFEndpoints
import Mathlib.Topology.Order.IntermediateValue

/-!
# The inverse of the semicircle CDF on its support

Continuity and endpoint values give every level in `[0,1]`; strict increase
on `[-2,2]` makes its preimage there unique. The resulting inverse is the
choice-based semicircle quantile.
-/

namespace RBM

open Set

noncomputable section

private abbrev semicircleCDF : ℝ → ℝ := ProbabilityTheory.cdf semicircleMeasure

/-- Every level in `[0,1]` has exactly one preimage in the semicircle support. -/
theorem existsUnique_semicircleCDF_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃! x : Icc (-2 : ℝ) 2, semicircleCDF x = t := by
  have hcont : ContinuousOn semicircleCDF (Icc (-2 : ℝ) 2) :=
    semicircleMeasure_cdf_continuous.continuousOn
  have himage : t ∈ semicircleCDF '' Icc (-2 : ℝ) 2 := by
    apply intermediate_value_Icc (by norm_num : (-2 : ℝ) ≤ 2) hcont
    simpa [semicircleCDF, semicircleMeasure_cdf_neg_two,
      semicircleMeasure_cdf_two] using (show t ∈ Icc (0 : ℝ) 1 from ⟨ht0, ht1⟩)
  obtain ⟨x, hx, hxt⟩ := himage
  let x' : Icc (-2 : ℝ) 2 := ⟨x, hx⟩
  have huniq : ∀ y : Icc (-2 : ℝ) 2, semicircleCDF y = t → y = x' := by
    intro y hyt
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := semicircleMeasure_cdf_strictMonoOn y.property x'.property hlt
      change ProbabilityTheory.cdf semicircleMeasure y.val <
        ProbabilityTheory.cdf semicircleMeasure x at h
      change ProbabilityTheory.cdf semicircleMeasure y.val = t at hyt
      change ProbabilityTheory.cdf semicircleMeasure x = t at hxt
      rw [hyt, hxt] at h
      exact (lt_irrefl t) h
    · have h := semicircleMeasure_cdf_strictMonoOn x'.property y.property hgt
      change ProbabilityTheory.cdf semicircleMeasure x <
        ProbabilityTheory.cdf semicircleMeasure y.val at h
      change ProbabilityTheory.cdf semicircleMeasure y.val = t at hyt
      change ProbabilityTheory.cdf semicircleMeasure x = t at hxt
      rw [hxt, hyt] at h
      exact (lt_irrefl t) h
  refine ⟨x', ?_, ?_⟩
  · exact hxt
  · intro y hy
    exact huniq y hy

/-- The unique support point whose semicircle CDF value is the given level. -/
def semicircleQuantile (t : Icc (0 : ℝ) 1) : Icc (-2 : ℝ) 2 :=
  Classical.choose (existsUnique_semicircleCDF_eq t t.property.1 t.property.2)

/-- The CDF evaluated at the chosen semicircle quantile is its level. -/
theorem semicircleCDF_semicircleQuantile (t : Icc (0 : ℝ) 1) :
    semicircleCDF (semicircleQuantile t) = t :=
  (Classical.choose_spec (existsUnique_semicircleCDF_eq t t.property.1 t.property.2)).1

/-- The quantile lies in the closed support interval, by its subtype value. -/
theorem semicircleQuantile_mem (t : Icc (0 : ℝ) 1) :
    -2 ≤ (semicircleQuantile t).val ∧ (semicircleQuantile t).val ≤ 2 :=
  (semicircleQuantile t).property

/-- The semicircle quantile is strictly increasing with its level. -/
theorem strictMono_semicircleQuantile : StrictMono semicircleQuantile := by
  intro s t hst
  change (semicircleQuantile s).val < (semicircleQuantile t).val
  by_contra hnot
  have hrev : (semicircleQuantile t).val ≤ (semicircleQuantile s).val := le_of_not_gt hnot
  have hqs : ProbabilityTheory.cdf semicircleMeasure (semicircleQuantile s).val = s := by
    simpa [semicircleCDF] using semicircleCDF_semicircleQuantile s
  have hqt : ProbabilityTheory.cdf semicircleMeasure (semicircleQuantile t).val = t := by
    simpa [semicircleCDF] using semicircleCDF_semicircleQuantile t
  have hlevels :
      ProbabilityTheory.cdf semicircleMeasure (semicircleQuantile s).val <
        ProbabilityTheory.cdf semicircleMeasure (semicircleQuantile t).val := by
    rw [hqs, hqt]
    exact hst
  by_cases heq : (semicircleQuantile t).val = (semicircleQuantile s).val
  · rw [heq] at hlevels
    exact (lt_irrefl _) hlevels
  · have hlt : (semicircleQuantile t).val < (semicircleQuantile s).val := lt_of_le_of_ne hrev heq
    have h := semicircleMeasure_cdf_strictMonoOn
      (semicircleQuantile t).property (semicircleQuantile s).property hlt
    rw [hqt, hqs] at h
    exact (lt_asymm hst h)

/-- The zero quantile is the left endpoint. -/
theorem semicircleQuantile_zero :
    semicircleQuantile ⟨0, by norm_num, by norm_num⟩ = (-2 : ℝ) := by
  have h := semicircleCDF_semicircleQuantile (⟨0, by norm_num, by norm_num⟩ : Icc (0 : ℝ) 1)
  change ProbabilityTheory.cdf semicircleMeasure
    (semicircleQuantile ⟨0, by norm_num, by norm_num⟩).val = 0 at h
  by_contra hne
  have hlt : (-2 : ℝ) < (semicircleQuantile ⟨0, by norm_num, by norm_num⟩).val :=
    lt_of_le_of_ne (semicircleQuantile ⟨0, by norm_num, by norm_num⟩).property.1
      (Ne.symm hne)
  have hstrict := semicircleMeasure_cdf_strictMonoOn
    (show (-2 : ℝ) ∈ Icc (-2 : ℝ) 2 by norm_num)
    (semicircleQuantile ⟨0, by norm_num, by norm_num⟩).property hlt
  rw [semicircleMeasure_cdf_neg_two, h] at hstrict
  exact (lt_irrefl 0) hstrict

/-- The one quantile is the right endpoint. -/
theorem semicircleQuantile_one :
    semicircleQuantile ⟨1, by norm_num, by norm_num⟩ = (2 : ℝ) := by
  have h := semicircleCDF_semicircleQuantile (⟨1, by norm_num, by norm_num⟩ : Icc (0 : ℝ) 1)
  change ProbabilityTheory.cdf semicircleMeasure
    (semicircleQuantile ⟨1, by norm_num, by norm_num⟩).val = 1 at h
  by_contra hne
  have hlt : (semicircleQuantile ⟨1, by norm_num, by norm_num⟩).val < 2 :=
    lt_of_le_of_ne (semicircleQuantile ⟨1, by norm_num, by norm_num⟩).property.2 hne
  have hstrict := semicircleMeasure_cdf_strictMonoOn
    (semicircleQuantile ⟨1, by norm_num, by norm_num⟩).property
    (show (2 : ℝ) ∈ Icc (-2 : ℝ) 2 by norm_num) hlt
  rw [h, semicircleMeasure_cdf_two] at hstrict
  exact (lt_irrefl 1) hstrict

/-- Any strictly interior level has a quantile strictly inside the support. -/
theorem semicircleQuantile_interior {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    -2 < (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).val ∧
      (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).val < 2 := by
  constructor
  · by_contra h
    have heq : (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).val = -2 :=
      le_antisymm (le_of_not_gt h) (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).property.1
    have hval := semicircleCDF_semicircleQuantile (⟨t, ⟨ht0.le, ht1.le⟩⟩ : Icc (0 : ℝ) 1)
    change ProbabilityTheory.cdf semicircleMeasure
      (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).val = t at hval
    rw [heq, semicircleMeasure_cdf_neg_two] at hval
    linarith
  · by_contra h
    have heq : (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).val = 2 :=
      le_antisymm (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).property.2 (le_of_not_gt h)
    have hval := semicircleCDF_semicircleQuantile (⟨t, ⟨ht0.le, ht1.le⟩⟩ : Icc (0 : ℝ) 1)
    change ProbabilityTheory.cdf semicircleMeasure
      (semicircleQuantile ⟨t, ⟨ht0.le, ht1.le⟩⟩).val = t at hval
    rw [heq, semicircleMeasure_cdf_two] at hval
    linarith

/-- The median level gives a concrete nondegenerate interior quantile. -/
theorem semicircleQuantile_half_interior :
    -2 < (semicircleQuantile ⟨(1 / 2 : ℝ), by norm_num⟩).val ∧
      (semicircleQuantile ⟨(1 / 2 : ℝ), by norm_num⟩).val < 2 := by
  exact semicircleQuantile_interior (by norm_num) (by norm_num)

#print axioms existsUnique_semicircleCDF_eq
#print axioms semicircleQuantile
#print axioms semicircleCDF_semicircleQuantile
#print axioms semicircleQuantile_mem
#print axioms strictMono_semicircleQuantile
#print axioms semicircleQuantile_zero
#print axioms semicircleQuantile_one
#print axioms semicircleQuantile_interior
#print axioms semicircleQuantile_half_interior

end

end RBM
