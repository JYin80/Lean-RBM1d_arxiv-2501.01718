/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OneLoopSharpGrid
import RBM1D.Gauss.GridNetLift
import RBM1D.Gauss.Step2Plain

/-!
# The sharp one-loop bound, time-uniform: the sup of a Hölder family

Formalization support for Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 4.1 (4.5) lifted from one
fixed grid time to the whole window `u ∈ [s_N, t_N]`, uniformly.

## Lifting a per-loop Hölder modulus to the sup

A Hölder modulus of `scale_u^m·‖(L−K)_{u,σ,a}‖` in the time holds **for each fixed loop**
`q = (σ,a)`, while the one-loop bound is stated at the **sup** `Sample.lkMax`.
`abs_ciSup_sub_ciSup_le` below is the two-line deterministic fact that lets a per-loop modulus
become a modulus for the sup, using only finiteness of the loop index set (for `BddAbove`) — no
new probabilistic content; `mul_ciSup_pos` moves a positive constant through the sup.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter

/-! ### A generic real-analysis fact: the sup of a Hölder family is Hölder -/

/-- **The sup of a bounded family inherits any common bound on pairwise differences.**
`|sup f − sup g| ≤ C` as soon as `|f i − g i| ≤ C` for every `i`, given the two sups exist
(`BddAbove` on the ranges — automatic here since the loop index is finite). -/
theorem abs_ciSup_sub_ciSup_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) {C : ℝ}
    (hC : ∀ i, |f i - g i| ≤ C) : |(⨆ i, f i) - ⨆ i, g i| ≤ C := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have h : (⨆ i, f i) ≤ C + ⨆ j, g j := by
      refine ciSup_le fun i => ?_
      have h1 : f i - g i ≤ C := (abs_sub_le_iff.mp (hC i)).1
      have h2 : g i ≤ ⨆ j, g j := le_ciSup hg i
      linarith
    linarith
  · have h : (⨆ i, g i) ≤ C + ⨆ j, f j := by
      refine ciSup_le fun i => ?_
      have h1 : g i - f i ≤ C := (abs_sub_le_iff.mp (hC i)).2
      have h2 : f i ≤ ⨆ j, f j := le_ciSup hf i
      linarith
    linarith

/-- **A positive constant passes through a (bounded) `ciSup`.** -/
theorem mul_ciSup_pos {ι : Type*} [Nonempty ι] {f : ι → ℝ} {k : ℝ} (hk : 0 < k)
    (hf : BddAbove (Set.range f)) : k * ⨆ i, f i = ⨆ i, k * f i := by
  have h := (OrderIso.mulLeft₀ k hk).map_ciSup hf
  simpa using h

variable (d : Dims)

/-! ### (T1) The time-uniform sharp one-loop bound -/

end RBM.Gauss

end



