/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Clopen

/-!
# Continuous induction (the bootstrap argument)

A self-improving bound propagates along an interval: if `φ` is continuous on `[a, b]`, starts
below `B`, and *every* point where `φ ≤ C` already satisfies `φ ≤ B` (with `B < C`), then
`φ ≤ B` on all of `[a, b]`.

This is the analytic core of the usual "continuity/bootstrap argument" of the paper's §5.3
(Step 2), where it replaces the stopping time (5.43): once the quantity being bootstrapped is a
*deterministic continuous* function of the time (a moment `φ(u) = E[(J*_{u,D})^q]` rather than a
path), no optional stopping is needed — the set where the improved bound holds is open and
closed in `[a, b]`, hence everything.

Nothing here is specific to the model, and nothing outside Mathlib is used.

## Main statements

* `le_of_bootstrap` : `[a, b]` version, self-improvement `φ u ≤ C → φ u ≤ B` with `B < C`
* `le_of_bootstrap_two_mul` : the common shape, `C = 2 * B` with `0 < B`
-/

namespace RBM

open Set

/-- **Continuous induction.**  If `φ` is continuous on `[a, b]`, `φ a ≤ B`, `B < C`, and at every
point of `[a, b]` the bound `φ u ≤ C` improves itself to `φ u ≤ B`, then `φ ≤ B` on `[a, b]`.

The set `{u | φ u ≤ B}` equals `{u | φ u < C}` by self-improvement, so it is at once closed and
open in `[a, b]`; it contains `a`, and `[a, b]` is connected. -/
theorem le_of_bootstrap {a b B C : ℝ} {φ : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (hBC : B < C) (h0 : φ a ≤ B)
    (hstep : ∀ u ∈ Icc a b, φ u ≤ C → φ u ≤ B) :
    ∀ u ∈ Icc a b, φ u ≤ B := by
  have hpre : PreconnectedSpace (Icc a b) :=
    isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  set ψ : Icc a b → ℝ := fun u => φ u with hψ
  have hψc : Continuous ψ := continuousOn_iff_continuous_domRestrict.1 hc
  set S : Set (Icc a b) := {u | ψ u ≤ B} with hS
  -- self-improvement identifies the closed sublevel set with an open one
  have hSeq : S = {u : Icc a b | ψ u < C} := by
    ext u
    refine ⟨fun hu => lt_of_le_of_lt hu hBC, fun hu => hstep u.1 u.2 hu.le⟩
  have hclosed : IsClosed S := isClosed_le hψc continuous_const
  have hopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_lt hψc continuous_const
  have hne : S.Nonempty := ⟨⟨a, left_mem_Icc.2 hab⟩, h0⟩
  have := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  intro u hu
  have : (⟨u, hu⟩ : Icc a b) ∈ S := this ▸ mem_univ _
  exact this

/-- The common shape of the bootstrap: the improved bound is half of the a priori one. -/
theorem le_of_bootstrap_two_mul {a b B : ℝ} {φ : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (hB : 0 < B) (h0 : φ a ≤ B)
    (hstep : ∀ u ∈ Icc a b, φ u ≤ 2 * B → φ u ≤ B) :
    ∀ u ∈ Icc a b, φ u ≤ B :=
  le_of_bootstrap hab hc (by linarith) h0 hstep

end RBM
