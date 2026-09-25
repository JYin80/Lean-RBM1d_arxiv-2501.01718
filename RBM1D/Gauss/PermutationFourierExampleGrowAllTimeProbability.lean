/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowGridProbability
import RBM1D.Gauss.PermutationFourierClosedTimeInterpolation
import RBM1D.Gauss.PermutationFourierSemicircleZeroMode
import RBM1D.Gauss.PermutationFourierExampleGrowFlowMargin
import RBM1D.Gauss.PermutationFourierExampleGrowZeroFlowMargin
import RBM1D.Defs.SemicircleQuantileCells

/-! # Growing-model all-time Fourier permutation probability

The same permutation satisfies the strict centered Fourier bound at every
closed half-time and every canonical mode with probability at least
`1 - 8 N^(-14)` eventually, under the finite uniform-permutation law. This is
not a Gaussian event estimate or either paper local law (2.3)--(2.4).
-/

open Filter MeasureTheory

namespace RBM.Gauss

/-- One permutation has the strict centered Fourier error below the literal
closed-flow threshold simultaneously at every time and canonical mode. -/
def permutationFourierExampleGrowAllTimeCenteredSet (N : ℕ) :
    Set (PermΩ (Dims.exampleGrow.W N)) :=
  {π | ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (1 / 2) →
      ∀ q : Fin (Dims.exampleGrow.W N),
        ‖permutationFourierSum (Dims.exampleGrow.W N)
          (fun j => semicircleFlowKernel u
            (semicircleLambda (Dims.exampleGrow.W N)
              (Dims.exampleGrow.W_pos N) j.val j.isLt))
          (permutationFourierCharacter (Dims.exampleGrow.W N) q) π -
          (if q = (⟨0, by have h := Dims.exampleGrow.W_pos N; omega⟩ :
            Fin (Dims.exampleGrow.W N)) then Complex.I else 0)‖ <
          flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N}

/-- The actual strict grid event implies the all-time centered event. The
nonzero modes use T930 and the strict T937 margin; the zero mode uses T933 and
the strict T948 margin. The same permutation is retained throughout. -/
private theorem permutationFourierExampleGrow_gridSet_subset_allTime
    (N : ℕ) (hW : 2 ≤ Dims.exampleGrow.W N)
    (hh : 0 < permutationFourierExampleGrowMesh N)
    (hnonzero : 76 * Real.sqrt
      (Real.log N / (Dims.exampleGrow.W N : ℝ)) <
        flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N)
    (hzero : 8 * Real.sqrt 2 / (Dims.exampleGrow.W N : ℝ) <
        flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N) :
    permutationFourierGridGoodSet (Dims.exampleGrow.W N)
      (permutationFourierExampleGrowGridCount N) hW
      (fun t j => semicircleFlowKernel
        (permutationFourierClosedTimeGrid (permutationFourierExampleGrowMesh N) t)
        (semicircleLambda (Dims.exampleGrow.W N) (by omega) j.val j.isLt))
      (permutationFourierExampleGrowThreshold N) ⊆
        permutationFourierExampleGrowAllTimeCenteredSet N := by
  intro π hπ u hu q
  let W := Dims.exampleGrow.W N
  let hW1 : 1 ≤ W := Nat.le_trans (by decide) hW
  let h := permutationFourierExampleGrowMesh N
  let T := permutationFourierExampleGrowGridCount N
  let r := permutationFourierExampleGrowThreshold N
  let lam : Fin W → ℝ := fun j => semicircleLambda W hW1 j.val j.isLt
  have hlam : ∀ j : Fin W, |lam j| ≤ 2 := by
    intro j
    have hj := (semicircleMidpointQuantile W hW1 j.val j.isLt).property
    change -2 ≤ lam j ∧ lam j ≤ 2 at hj
    exact abs_le.mpr hj
  have hχ : ∀ j : Fin W, ‖permutationFourierCharacter W q j‖ ≤ 1 := by
    intro j
    rw [permutationFourierCharacter_norm_eq_one]
  by_cases hq : q = (⟨0, by omega⟩ : Fin W)
  · subst q
    rw [permutationFourierCharacter_zero_eq_one W hW1]
    have hbound := permutationFourierSemicircleZeroMode_bound W hW1 u hu.1 hu.2 π
    simpa [W] using lt_of_le_of_lt hbound hzero
  · have hgrid : ∀ t : Fin (permutationFourierClosedTimeGridCount h),
        ‖permutationFourierSum W
          (fun k => semicircleFlowKernel
            (permutationFourierClosedTimeGrid h t) (lam k))
          (permutationFourierCharacter W q) π‖ < r := by
      intro t
      have ht : t.val < T := by
        dsimp [T, h]
        exact t.isLt
      have ht' : (⟨t.val, ht⟩ : Fin T) = t := by ext; rfl
      change ∀ t : Fin T, ∀ q : Fin W, q ≠ (⟨0, by omega⟩ : Fin W) →
        ‖permutationFourierSum W
          (fun j => semicircleFlowKernel
            (permutationFourierClosedTimeGrid h t)
            (semicircleLambda W (by omega) j.val j.isLt))
          (permutationFourierCharacter W q) π‖ < r at hπ
      simpa [T, h, r, W, lam, ht'] using hπ (⟨t.val, ht⟩ : Fin T) q hq
    have hinterp := permutationFourierClosedTimeInterpolation W h hW1 hh lam
      (permutationFourierCharacter W q) hlam hχ π r hgrid u hu.1 hu.2
    have hsum : r + 12 * Real.sqrt h =
        76 * Real.sqrt (Real.log N / (W : ℝ)) := by
      dsimp [r, h, W, permutationFourierExampleGrowThreshold,
        permutationFourierExampleGrowMesh]
      ring
    have hstrict :
        ‖permutationFourierSum W
          (fun j => semicircleFlowKernel u (lam j))
          (permutationFourierCharacter W q) π‖ <
          flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
      exact lt_trans hinterp (by rw [hsum]; exact hnonzero)
    simpa only [ite_eq_right hq, sub_zero] using hstrict

/-- Any subset of the finite permutation space, including this uncountably
quantified all-time event, is measurable for the discrete uniform law. -/
theorem permutationFourierExampleGrowAllTimeCenteredSet_measurable (N : ℕ) :
    MeasurableSet (permutationFourierExampleGrowAllTimeCenteredSet N) := by
  exact MeasurableSpace.measurableSet_top

/-- For the actual midpoint-quantile table on `Dims.exampleGrow`, one
permutation obeys the strict centered Fourier threshold at all times and all
canonical modes with probability at least `1 - 8 N^(-14)` eventually. The
probability space is only the finite uniform-permutation space. -/
theorem permutationFourierExampleGrow_eventually_allTime_good_probability :
    ∀ᶠ N : ℕ in atTop,
      1 - 8 * (N : ℝ) ^ (-14 : ℝ) ≤
        (uniformPerm (Dims.exampleGrow.W N)).real
          (permutationFourierExampleGrowAllTimeCenteredSet N) := by
  filter_upwards
    [permutationFourierExampleGrow_eventually_grid_good_probability,
      permutationFourierExampleGrow_eventually_bounds,
      PermutationFourierExampleGrowFlowMargin.eventual_margin,
      PermutationFourierExampleGrowZeroFlowMargin.eventual_zero_mode_lt_flowDelta]
    with N hprob hgrid hnonzero hzero
  rcases hprob with ⟨hW, hT, hr, hprob⟩
  have hsubset := permutationFourierExampleGrow_gridSet_subset_allTime
    N hW hgrid.1 hnonzero hzero
  exact le_trans hprob (measureReal_mono hsubset)

#print axioms permutationFourierExampleGrowAllTimeCenteredSet_measurable
#print axioms permutationFourierExampleGrow_eventually_allTime_good_probability

end RBM.Gauss
