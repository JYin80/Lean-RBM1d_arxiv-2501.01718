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
* `le_of_bootstrap_prefix` : the self-improvement may use the bound on all of `[a, u]`
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

/-- **Continuous induction, prefix form.**  The self-improvement may use the a priori bound on
the whole initial segment `[a, u]`, not just at `u`: this is the shape of the paper's Step 2,
where "assume `J*_{v,D} ≤ (η_s/η_t)⁴` for all `v ≤ u`" improves the bound at `u`.

Let `s` be the supremum of the times up to which `φ ≤ B` holds.  Continuity gives `φ s ≤ B`,
so the bound holds on `[a, s]`; if `s < b`, continuity gives `φ < C` slightly beyond `s`, and
the self-improvement then upgrades it to `φ ≤ B` there, contradicting the supremum. -/
theorem le_of_bootstrap_prefix {a b B C : ℝ} {φ : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (hBC : B < C) (h0 : φ a ≤ B)
    (hstep : ∀ u ∈ Icc a b, (∀ v ∈ Icc a u, φ v ≤ C) → φ u ≤ B) :
    ∀ u ∈ Icc a b, φ u ≤ B := by
  set S : Set ℝ := {u | u ∈ Icc a b ∧ ∀ v ∈ Icc a u, φ v ≤ B} with hSdef
  have haS : a ∈ S := ⟨left_mem_Icc.2 hab, fun v hv => by
    rw [le_antisymm hv.2 hv.1]; exact h0⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hbdd : BddAbove S := ⟨b, fun u hu => hu.1.2⟩
  set s : ℝ := sSup S with hsdef
  have hsa : a ≤ s := le_csSup hbdd haS
  have hsb : s ≤ b := csSup_le hSne fun u hu => hu.1.2
  have hsIcc : s ∈ Icc a b := ⟨hsa, hsb⟩
  -- `φ ≤ B` strictly below the supremum
  have hlt : ∀ v ∈ Ico a s, φ v ≤ B := by
    intro v hv
    obtain ⟨u, huS, hvu⟩ := exists_lt_of_lt_csSup hSne hv.2
    exact huS.2 v ⟨hv.1, hvu.le⟩
  -- and at the supremum, by continuity
  have hφs : φ s ≤ B := by
    rcases eq_or_lt_of_le hsa with h | h
    · rw [← h]; exact h0
    · by_contra hcon
      push Not at hcon
      obtain ⟨δ, hδ0, hδ⟩ :=
        Metric.continuousWithinAt_iff.1 (hc s hsIcc) (φ s - B) (by linarith)
      have hy2 : max a (s - δ / 2) < s := by
        rcases le_or_gt (s - δ / 2) a with h' | h'
        · rwa [max_eq_left h']
        · rw [max_eq_right h'.le]; linarith
      have hy1 : a ≤ max a (s - δ / 2) := le_max_left _ _
      have hdist : dist (max a (s - δ / 2)) s < δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        have : s - δ / 2 ≤ max a (s - δ / 2) := le_max_right _ _
        linarith
      have hclose := hδ ⟨hy1, le_trans hy2.le hsb⟩ hdist
      have hyB : φ (max a (s - δ / 2)) ≤ B := hlt _ ⟨hy1, hy2⟩
      rw [Real.dist_eq] at hclose
      have := abs_lt.1 hclose
      linarith [this.1]
  have hsS : s ∈ S := ⟨hsIcc, fun v hv => by
    rcases eq_or_lt_of_le hv.2 with h | h
    · rw [h]; exact hφs
    · exact hlt v ⟨hv.1, h⟩⟩
  -- the supremum is the right endpoint
  have hsEq : s = b := by
    by_contra hne
    have hsb2 : s < b := lt_of_le_of_ne hsb hne
    obtain ⟨δ, hδ0, hδ⟩ :=
      Metric.continuousWithinAt_iff.1 (hc s hsIcc) (C - φ s) (by linarith)
    have hsu : s < min b (s + δ / 2) := lt_min hsb2 (by linarith)
    have huIcc : min b (s + δ / 2) ∈ Icc a b := ⟨le_trans hsa hsu.le, min_le_left _ _⟩
    have hCon : ∀ v ∈ Icc a (min b (s + δ / 2)), φ v ≤ C := by
      intro v hv
      rcases le_or_gt v s with h | h
      · exact le_trans (hsS.2 v ⟨hv.1, h⟩) hBC.le
      · have hvb : v ≤ b := le_trans hv.2 huIcc.2
        have hdist : dist v s < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          have := le_trans hv.2 (min_le_right b (s + δ / 2))
          linarith
        have hclose := hδ ⟨hv.1, hvb⟩ hdist
        rw [Real.dist_eq] at hclose
        have := abs_lt.1 hclose
        linarith [this.2]
    have huS : min b (s + δ / 2) ∈ S :=
      ⟨huIcc, fun v hv => hstep v ⟨hv.1, le_trans hv.2 huIcc.2⟩
        fun w hw => hCon w ⟨hw.1, le_trans hw.2 hv.2⟩⟩
    exact absurd (le_csSup hbdd huS) (not_le.2 hsu)
  intro u hu
  exact (hsEq ▸ hsS).2 u hu

/-- The common shape of the bootstrap: the improved bound is half of the a priori one. -/
theorem le_of_bootstrap_two_mul {a b B : ℝ} {φ : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (hB : 0 < B) (h0 : φ a ≤ B)
    (hstep : ∀ u ∈ Icc a b, φ u ≤ 2 * B → φ u ≤ B) :
    ∀ u ∈ Icc a b, φ u ≤ B :=
  le_of_bootstrap hab hc (by linarith) h0 hstep

end RBM
