/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Upper semicontinuity of a nonempty finite supremum

This purely topological lemma retains the exact `Finset.sup'` used by a finite
maximum. It does not establish upper semicontinuity of any particular quotient.
-/

namespace RBM.Gauss

/-- The exact finite maximum of a nonempty family of upper semicontinuous
real-valued functions is upper semicontinuous. -/
theorem upperSemicontinuous_finset_sup' {ι α : Type*} [TopologicalSpace α]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, UpperSemicontinuous (f i)) :
    UpperSemicontinuous (fun x => s.sup' hs (fun i => f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa only [Finset.sup'_singleton] using hf i (Finset.mem_singleton_self i)
  | cons i t hit ht ih =>
      have hi : UpperSemicontinuous (f i) := hf i (Finset.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ j ∈ t, UpperSemicontinuous (f j) := by
        intro j hj
        exact hf j (Finset.mem_cons.mpr (Or.inr hj))
      have hmax := hi.sup (ih hrest)
      simpa only [Finset.sup'_cons ht] using hmax

/-- An explicit nonconstant two-function family: the finite maximum of `u`
and `-u` is `|u|`. In particular, the hypotheses are satisfiable nontrivially. -/
theorem upperSemicontinuous_twoFunction_witness :
    UpperSemicontinuous
      (fun u : ℝ => (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
        (fun b => if b then u else -u)) ∧
    (∀ u : ℝ, (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
        (fun b => if b then u else -u) = |u|) ∧
    (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
        (fun b => if b then (0 : ℝ) else -0) ≠
      (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
        (fun b => if b then (1 : ℝ) else -1) := by
  have hf : ∀ b ∈ (Finset.univ : Finset Bool),
      UpperSemicontinuous (fun u : ℝ => if b then u else -u) := by
    intro b _
    cases b
    · change UpperSemicontinuous (fun u : ℝ => -u)
      exact (continuous_id.neg : Continuous (fun u : ℝ => -u)).upperSemicontinuous
    · change UpperSemicontinuous (fun u : ℝ => u)
      exact (continuous_id : Continuous (fun u : ℝ => u)).upperSemicontinuous
  refine ⟨upperSemicontinuous_finset_sup' _ _ _ hf, ?_, ?_⟩
  · intro u
    simp [Finset.sup'_insert, Finset.sup'_singleton, abs_eq_max_neg]
  · norm_num [Finset.sup'_insert, Finset.sup'_singleton]

#print axioms upperSemicontinuous_finset_sup'
#print axioms upperSemicontinuous_twoFunction_witness

end RBM.Gauss
