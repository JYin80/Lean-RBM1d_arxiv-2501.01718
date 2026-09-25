/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.GridStop

/-!
# Grid stopping times specialised to the coordinate filtration

Specialises the generic (filtration-agnostic) stopping-time facts of `RBM1D/Gauss/GridStop.lean`
(T1483) to the coordinate filtration `RBM.Gauss.Grid.filt` on the grid sample space
`RBM.Gauss.Grid.Ωg d` (T1481, `GridPath.lean`), for processes built from the grid path `H`:
`docs/claude-team/pilot-P4P5-paper.md` §4 (τ, σ are stopping times of the grid path).

This is T1489, pilot P1/P3 API plumbing of the True-Path track.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory

variable (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)

/-! ### Step 0 : the matrix-level measurability lemma

`H_adapted` (`GridPath.lean`) only gives entrywise `StronglyMeasurable[filt d k]` of the grid
path `H`. `Matrix (d.Idx N) (d.Idx N) ℂ` unfolds to the doubly-nested Pi type
`d.Idx N → d.Idx N → ℂ`, and Mathlib's `measurable_pi_iff` is stated for an arbitrary source
`MeasurableSpace`, so it transports unchanged to the relative measurable space `filt d k` exactly
as `measurable_Xmat`/`measurable_H` already do for the ambient measurable space in
`GridPath.lean`. This assembles the entrywise statement into the matrix-level one. -/
theorem H_measurable_filt (k : ℕ) :
    Measurable[filt d k] (fun ω : Ωg d => H d s t K N k ω) :=
  (@Matrix.measurable_iff (d.Idx N) (d.Idx N) ℂ _ (Ωg d) (filt d k)
      (fun ω => H d s t K N k ω)).mpr
    (fun i j => stronglyMeasurable_iff_measurable.mp (H_adapted d s t K N k i j))

/-- A "loop-observable" process built from a family `F` of measurable functions of the grid
matrix `H` is adapted to the coordinate filtration. -/
theorem adapted_of_measurable_H {F : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) :
    Adapted (filt d) (fun j (ω : Ωg d) => F j (H d s t K N j ω)) :=
  fun j => (hF j).comp (H_measurable_filt d s t K N j)

/-- (T1) The first grid index at which a grid-observable process reaches a threshold is a
stopping time for the coordinate filtration. -/
theorem isStoppingTime_firstHit_grid {F : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (θ : ℝ) (K' : ℕ) :
    IsStoppingTime (filt d)
      (fun ω => (firstHit (fun j (ω : Ωg d) => F j (H d s t K N j ω)) θ K' ω : ℕ)) :=
  isStoppingTime_firstHit (ℱ := filt d) (fun j (ω : Ωg d) => F j (H d s t K N j ω)) θ K'
    (adapted_of_measurable_H d s t K N hF)

/-- (T2) The event that a grid-observable process has not yet stopped by time `j` is
`filt d j`-measurable. -/
theorem lt_firstHit_grid_measurableSet {F : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (θ : ℝ) (K' : ℕ) (j : ℕ) :
    MeasurableSet[filt d j]
      {ω | j < firstHit (fun j (ω : Ωg d) => F j (H d s t K N j ω)) θ K' ω} :=
  lt_firstHit_measurableSet (ℱ := filt d) (fun j (ω : Ωg d) => F j (H d s t K N j ω)) θ K'
    (adapted_of_measurable_H d s t K N hF) j

/-- (T3, part 1) The minimum of two grid-observable stopping times (over the same grid horizon
`K'`) is again a stopping time for the coordinate filtration. -/
theorem isStoppingTime_min_firstHit_grid
    {F F' : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (hF' : ∀ j, Measurable (F' j)) (θ θ' : ℝ) (K' : ℕ) :
    IsStoppingTime (filt d)
      (fun ω => (min (firstHit (fun j (ω : Ωg d) => F j (H d s t K N j ω)) θ K' ω)
        (firstHit (fun j (ω : Ωg d) => F' j (H d s t K N j ω)) θ' K' ω) : ℕ)) :=
  isStoppingTime_min_firstHit (ℱ := filt d) (fun j (ω : Ωg d) => F j (H d s t K N j ω))
    (fun j (ω : Ωg d) => F' j (H d s t K N j ω)) θ θ' K'
    (adapted_of_measurable_H d s t K N hF) (adapted_of_measurable_H d s t K N hF')

/-- (T3, part 2) The event that neither of two grid-observable stopping times has fired by `j`
is `filt d j`-measurable. -/
theorem lt_min_firstHit_grid_measurableSet
    {F F' : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (hF' : ∀ j, Measurable (F' j)) (θ θ' : ℝ) (K' : ℕ) (j : ℕ) :
    MeasurableSet[filt d j]
      {ω | j < min (firstHit (fun j (ω : Ωg d) => F j (H d s t K N j ω)) θ K' ω)
        (firstHit (fun j (ω : Ωg d) => F' j (H d s t K N j ω)) θ' K' ω)} :=
  lt_min_firstHit_measurableSet (ℱ := filt d) (fun j (ω : Ωg d) => F j (H d s t K N j ω))
    (fun j (ω : Ωg d) => F' j (H d s t K N j ω)) θ θ' K'
    (adapted_of_measurable_H d s t K N hF) (adapted_of_measurable_H d s t K N hF') j

end RBM.Gauss.Grid

end
