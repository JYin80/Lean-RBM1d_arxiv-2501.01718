/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVCurrentRows

/-!
# T448: favorable-event weighted current QV rows

This file multiplies T438's literal moving current-row estimate by the
actual smooth first-cell weight.  The zero-weight branch is treated
algebraically; the positive branch stays on T434's `sharpCommonEvent` and
uses T438 without changing its endpoint or rows.
-/

namespace RBM.APrimeFirstCellQVWeightedGood

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- On the favorable event, the actual smooth weight times the actual uncut
QV is bounded by the same weight times T438's current rate. -/
def weightedCurrentRowsGood (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      let w := APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
        w * APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
          w * APrimeFirstCellQVCurrentRows.currentRate
            δ (δ / 16) ν N v r

/-- The favorable weighted estimate follows by splitting the actual weight
at zero.  No assertion about the value of `qvAt` is made in the zero branch. -/
theorem weightedCurrentRowsGood_of_currentRows {τ' δ ν : ℝ}
    (hcurrent : APrimeFirstCellQVCurrentRows.currentRowsBound τ' δ ν) :
    weightedCurrentRowsGood τ' δ ν := by
  filter_upwards [hcurrent] with N hcurrent
  intro ω hω N0 p k m hN0 hp hm hk1 hk
  let w := APrimeSupportRunning.weight δ (firstCellT τ')
    N0 p N k m ω
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  change ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
    w * APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      w * APrimeFirstCellQVCurrentRows.currentRate
        δ (δ / 16) ν N v r
  have hw0 : 0 ≤ w := by
    dsimp [w, APrimeSupportRunning.weight]
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh
      N0 p N k m ω
  by_cases hwzero : w = 0
  · intro r hr a
    norm_num [hwzero]
  · have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hwzero)
    have hrows := hcurrent ω hω N0 p k m hN0 hp hm hk1 hk
      (by simpa only [w] using hwpos)
    obtain ⟨_hvpos, _hvle, _hvhalf, _hJall, hprof⟩ := hrows
    intro r hr a
    exact mul_le_mul_of_nonneg_left ((hprof r hr).2.2 a) hw0

/-- The positive `k = 2` resident from T438, now carrying the weighted
estimate with its actual weight equal to one for every moment label. -/
def positiveWeightedCurrentRowsPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    APrimeFullQV.SourceEvent (sample d) 0 N v ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N v) ∧
    (∀ q ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N q ω ≤ 2) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) v,
      1 ≤ APrimeSupportRunning.jG N r ω ∧
      APrimeSupportRunning.jG N r ω ≤ 2 ∧
        ∀ p : ℕ, ∀ a : LoopArg (d.L N) 2,
          APrimeSupportRunning.weight δ (firstCellT τ')
              2 p N 2 N ω *
            APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
          APrimeSupportRunning.weight δ (firstCellT τ')
              2 p N 2 N ω *
            APrimeFirstCellQVCurrentRows.currentRate
              δ (δ / 16) ν N v r) ∧
    (∀ p : ℕ, ∀ a : LoopArg (d.L N) 2,
      APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v 0 ω ≤
        APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeFirstCellQVCurrentRows.currentRate
            δ (δ / 16) ν N v 0) ∧
    ∀ p : ℕ, ∀ a : LoopArg (d.L N) 2,
      APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v v ω ≤
        APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeFirstCellQVCurrentRows.currentRate
            δ (δ / 16) ν N v v

theorem positiveWeightedCurrentRowsPlateau_of_current
    {τ' δ ν : ℝ}
    (hpositive :
      APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau τ' δ ν) :
    positiveWeightedCurrentRowsPlateau τ' δ ν := by
  filter_upwards [hpositive] with N hpositive
  dsimp only [APrimeFirstCellQVCurrentRows.positiveCurrentRowsPlateau]
    at hpositive
  obtain ⟨ω, hω, hvpos, hvle, hvhalf, hw, hsource, hJall, hprof,
    hzero, hend⟩ := hpositive
  refine ⟨ω, hω, hvpos, hvle, hvhalf, hw, hsource, hJall, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨hJ1, hJ2, hqv⟩ := hprof r hr
    refine ⟨hJ1, hJ2, ?_⟩
    intro p a
    rw [hw p]
    simpa using hqv a
  · intro p a
    rw [hw p]
    simpa using hzero a
  · intro p a
    rw [hw p]
    simpa using hend a

/-- Closed same-event favorable weighted producer with the positive T438
resident.  It makes no statement about the event complement. -/
theorem exists_weightedCurrentRowsGood_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        weightedCurrentRowsGood τ' δ ν ∧
        positiveWeightedCurrentRowsPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQVCurrentRows.exists_currentRowsBound_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hcurrent, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, weightedCurrentRowsGood_of_currentRows hcurrent,
    positiveWeightedCurrentRowsPlateau_of_current hpositive⟩

end RBM.APrimeFirstCellQVWeightedGood

#print axioms RBM.APrimeFirstCellQVWeightedGood.weightedCurrentRowsGood_of_currentRows
#print axioms RBM.APrimeFirstCellQVWeightedGood.positiveWeightedCurrentRowsPlateau_of_current
#print axioms RBM.APrimeFirstCellQVWeightedGood.exists_weightedCurrentRowsGood_with_plateau
