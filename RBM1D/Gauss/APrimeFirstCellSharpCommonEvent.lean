/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGAllOutputRunning
import RBM1D.Gauss.APrimeFirstCellJGActual

/-!
# T434: sharp common-event positive first-cell package

The actual first-cell all-time block event is intersected with T418's
literal common event.  A single resident of that intersection carries the
active `k = 2` weight, the source event at its positive endpoint, and the
sharp block `jG ≤ 2` bound at every real time in the first half interval.
-/

namespace RBM.APrimeFirstCellSharpCommonEvent

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The literal intersection of T428's sharp block event and T418's common event. -/
def sharpCommonEvent (τ' δ ν : ℝ) (N : ℕ) : Set (Ω d) :=
  APrimeFirstCellJGAllTime.good N ∩
    APrimeFirstCellEGAllOutputRunning.good τ' δ ν N

theorem measurableSet_sharpCommonEvent {τ' : ℝ} (hτ' : 0 < τ')
    (δ ν : ℝ) (N : ℕ) : MeasurableSet (sharpCommonEvent τ' δ ν N) :=
  (APrimeFirstCellJGAllTime.measurableSet_good N).inter
    (APrimeFirstCellMovingSupport.measurableSet_commonEvent hτ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) (δ / 16) N)

theorem highProb_sharpCommonEvent {τ' δ ν : ℝ}
    (hcommon : HighProb (P d)
      (APrimeFirstCellEGAllOutputRunning.good τ' δ ν)) :
    HighProb (P d) (sharpCommonEvent τ' δ ν) :=
  APrimeFirstCellJGActual.highProb_good.inter hcommon

/-- A nondegenerate resident of the literal sharp/common intersection.
The endpoint bounds are deterministic, while every sample-dependent field
is carried by the same `ω`.  The last two fields make the two endpoint
instances of the all-real-time sharp cap explicit. -/
def positiveSharpPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ sharpCommonEvent τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧
    u2 ≤ firstCellT τ' N ∧
    firstCellT τ' N ≤ 1 / 2 ∧
    APrimeFullQV.SourceEvent (sample d) 0 N u2 ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N u2) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N r ω ≤ 2) ∧
    APrimeSupportRunning.jG N 0 ω ≤ 2 ∧
    APrimeSupportRunning.jG N u2 ω ≤ 2

theorem positiveSharpPlateau_of_common {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ)
    (hp : HighProb (P d) (sharpCommonEvent τ' δ ν))
    (hplat : APrimeFirstCellEGAllOutputRunning.positiveAllOutputPlateau
      τ' δ ν) :
    positiveSharpPlateau τ' δ ν := by
  filter_upwards [hp.nonempty (by simp), hplat,
    APrimeFirstCellCommon.eventually_active_weight_two_one hτ' hδ,
    APrimeFirstCellCTDecay.eventually_all_time_jG_le_two_on_good,
    eventually_ge_atTop 2] with N hne hplat hweight hsharp hN
  obtain ⟨ω, hω⟩ := hne
  dsimp only [APrimeFirstCellEGAllOutputRunning.positiveAllOutputPlateau] at hplat
  obtain ⟨_ωold, _hωold, hk, _hwold, _hw100old,
    hu2pos, hu2le, _hallold⟩ := hplat
  have hcommon : ω ∈ APrimeFirstCellMovingSupport.commonEvent τ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) (δ / 16) N := hω.2
  have hdyn := APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hcommon
  have hraw := APrimeSupportRunning.good_subset τ' (δ / 16) N hdyn
  have hnorm : ‖Xmat d N ω‖ ≤ (N : ℝ) := hraw.1.1.1
  have hwδ : ∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1 := by
    intro p
    have h := hweight ω hnorm p
    rw [APrimeSupportRunning.firstS_eq] at h
    exact h
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hTle : firstCellT τ' N ≤ 1 / 2 :=
    (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hs0 : firstCellS τ' N = 0 := Gauss.firstCellS_eq_zero τ' N
  let ut : TimeIcc (firstCellS τ') (firstCellT τ') N := by
    refine ⟨u2, ?_⟩
    rw [hs0]
    exact ⟨hu2pos.le, hu2le⟩
  have hsource := APrimeFirstCellSourceAllTime.sourceEvent_of_common
    (show 0 < N by omega) ut
      (APrimeFirstCellMovingSupport.commonEvent_to_source hcommon)
  have hJall : ∀ r ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N r ω ≤ 2 := hsharp ω hω.1
  have hJ0 : APrimeSupportRunning.jG N 0 ω ≤ 2 :=
    hJall 0 ⟨le_rfl, by norm_num⟩
  have hJu2 : APrimeSupportRunning.jG N u2 ω ≤ 2 :=
    hJall u2 ⟨hu2pos.le, hu2le.trans hTle⟩
  refine ⟨ω, hω, hk, hwδ, hu2pos, hu2le, hTle, ?_, hJall, hJ0, hJu2⟩
  simpa only [ut] using hsource

/-- One first-cell parameter, chosen before the cutoff and source losses,
supplies the measurable high-probability intersection and its same-resident
positive `k = 2` sharp package. -/
theorem exists_sharpCommonEvent_with_positive_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet (sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d) (sharpCommonEvent τ' δ ν) ∧
        positiveSharpPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hcommon⟩ :=
    APrimeFirstCellEGAllOutputRunning.exists_good_with_all_output
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨_hmeas, hp, _hall, hplat⟩ := hcommon δ hδ hδ100 ν hν
  have hpSharp := highProb_sharpCommonEvent hp
  exact ⟨measurableSet_sharpCommonEvent hτ' δ ν, hpSharp,
    positiveSharpPlateau_of_common hτ' hδ hpSharp hplat⟩

#print axioms measurableSet_sharpCommonEvent
#print axioms highProb_sharpCommonEvent
#print axioms positiveSharpPlateau_of_common
#print axioms exists_sharpCommonEvent_with_positive_plateau

end RBM.APrimeFirstCellSharpCommonEvent
