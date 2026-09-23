/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.DenselyOrdered

/-!
# A nonnegative function with a closed hard cutoff

The active branch includes the boundary of the closed set. Its possible jump is upward,
which preserves upper semicontinuity. This file contains only a topological statement;
the continuity and sign of any particular quotient must be proved separately.
-/

namespace RBM.Gauss

open scoped Topology

open scoped Classical in
/-- Zero-extending a continuous nonnegative real function off a closed set preserves
upper semicontinuity. Equality at the cutoff belongs to the active branch. -/
theorem upperSemicontinuous_closedCutoff {α : Type*} [TopologicalSpace α]
    {C : Set α} (hC : IsClosed C) {f : α → ℝ}
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    UpperSemicontinuous (fun x => if x ∈ C then f x else 0) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro r
  by_cases hr : r ≤ 0
  · have hempty : (fun x => if x ∈ C then f x else 0) ⁻¹' Set.Iio r = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
      split_ifs with hx
      · exact not_lt_of_ge (le_trans hr (hn x))
      · exact not_lt_of_ge hr
    rw [hempty]
    exact isOpen_empty
  · have hr' : 0 < r := lt_of_not_ge hr
    have heq : (fun x => if x ∈ C then f x else 0) ⁻¹' Set.Iio r =
        f ⁻¹' Set.Iio r ∪ Cᶜ := by
      ext x
      by_cases hx : x ∈ C <;> simp [hx, hr']
    rw [heq]
    exact (hf.isOpen_preimage _ isOpen_Iio).union hC.isOpen_compl

open scoped Classical in
/-- The closed half-line cutoff of the constant-one function is upper semicontinuous
but has a genuine upward jump at its boundary. -/
theorem closedCutoff_Ici_zero_witness :
    IsClosed (Set.Ici (0 : ℝ)) ∧
      Continuous (fun _ : ℝ => (1 : ℝ)) ∧
      (∀ _x : ℝ, 0 ≤ (1 : ℝ)) ∧
      UpperSemicontinuous
        (fun x : ℝ => if x ∈ Set.Ici (0 : ℝ) then (1 : ℝ) else 0) ∧
      ¬ ContinuousAt
        (fun x : ℝ => if x ∈ Set.Ici (0 : ℝ) then (1 : ℝ) else 0) 0 := by
  refine ⟨isClosed_Ici, continuous_const, (fun _ => by norm_num),
    upperSemicontinuous_closedCutoff (f := fun _ : ℝ => (1 : ℝ))
      isClosed_Ici continuous_const (fun _ => by norm_num), ?_⟩
  intro hcont
  have hpre : (fun x : ℝ => if x ∈ Set.Ici (0 : ℝ) then (1 : ℝ) else 0) ⁻¹'
      Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (0 : ℝ) := by
    apply hcont.preimage_mem_nhds
    simpa using (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have heq : (fun x : ℝ => if x ∈ Set.Ici (0 : ℝ) then (1 : ℝ) else 0) ⁻¹'
      Set.Ioi (1 / 2 : ℝ) = Set.Ici (0 : ℝ) := by
    ext x
    by_cases hx : 0 ≤ x
    · simp [Set.mem_Ici, hx]
      norm_num
    · simp [Set.mem_Ici, hx]
  rw [heq] at hpre
  have hmem : (0 : ℝ) ∈ interior (Set.Ici (0 : ℝ)) :=
    mem_interior_iff_mem_nhds.mpr hpre
  rw [interior_Ici] at hmem
  exact (lt_irrefl (0 : ℝ)) hmem

#print axioms upperSemicontinuous_closedCutoff
#print axioms closedCutoff_Ici_zero_witness

end RBM.Gauss
