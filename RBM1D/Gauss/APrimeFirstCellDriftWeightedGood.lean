/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDriftAbsorbed
import RBM1D.Gauss.APrimeFirstCellSharpCommonEvent

/-!
# T456: favorable-event weighted drift at the moving first-cell endpoint

T442 is instantiated at loss `2 * alpha`, so its literal event loss is
`(2 * alpha) / 2 = alpha`.  This makes its EG event exactly the second
component of T434's `sharpCommonEvent tauPrime delta alpha`.  The actual
smooth weight is split at zero before the favorable drift estimate is used.
-/

namespace RBM.APrimeFirstCellDriftWeightedGood

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The reparameterized T442 event is literally the EG component of the
T434 event at loss `alpha`. -/
theorem egEvent_two_mul (τ' δ α : ℝ) (N : ℕ) :
    APrimeFirstCellEGAllOutputRunning.good τ' δ ((2 * α) / 2) N =
      APrimeFirstCellEGAllOutputRunning.good τ' δ α N := by
  rw [show (2 * α) / 2 = α by ring]

/-- The T442 coefficient after reparameterization retains its full near/far
shape and has the outer loss `N^(2 * alpha)`. -/
theorem endpointCoefficient_two_mul (δ α : ℝ) (N : ℕ) (v r : ℝ) :
    APrimeFirstCellDriftCoefficient.endpointCoefficient δ (2 * α) N v r =
      APrimeFirstCellDriftCoefficient.coefficientConstant *
        (N : ℝ) ^ (2 * α) * (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) *
            (APrimeFirstCellLoopCap.xRate r ^ (-(1 : ℝ) / 2) +
              (N : ℝ) ^ (4 * δ) *
                (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
                  APrimeFirstCellLoopCap.xRate r ^ 6) := by
  rfl

/-- On T434's one sharp event, the actual smooth weight times the normalized
drift is bounded by the same weight times the full T442 coefficient at loss
`2 * alpha`. -/
def weightedDriftGood (τ' δ α : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      let w := APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
        w * APrimeDriftTimeFamily.driftAt
            d 0 60 N Step2.sigPM a 0 v r ω ≤
          w * APrimeFirstCellDriftCoefficient.endpointCoefficient
            δ (2 * α) N v r

/-- The favorable weighted estimate follows by splitting the actual weight
at zero.  T442 is used only in the positive branch. -/
theorem weightedDriftGood_of_absorbed {τ' δ α : ℝ}
    (habs : APrimeFirstCellDriftAbsorbed.absorbedDriftBound
      τ' δ (2 * α)) :
    weightedDriftGood τ' δ α := by
  filter_upwards [habs] with N habs
  intro ω hω N0 p k m hN0 hp hm hk1 hk
  let w := APrimeSupportRunning.weight δ (firstCellT τ')
    N0 p N k m ω
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  change ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
    w * APrimeDriftTimeFamily.driftAt
        d 0 60 N Step2.sigPM a 0 v r ω ≤
      w * APrimeFirstCellDriftCoefficient.endpointCoefficient
        δ (2 * α) N v r
  have hw0 : 0 ≤ w := by
    dsimp [w, APrimeSupportRunning.weight]
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh
      N0 p N k m ω
  by_cases hwzero : w = 0
  · intro r hr a
    norm_num [hwzero]
  · have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hwzero)
    have hωeg : ω ∈ APrimeFirstCellEGAllOutputRunning.good
        τ' δ ((2 * α) / 2) N := by
      rw [egEvent_two_mul]
      exact hω.2
    have hbound := habs ω hωeg N0 p k m hN0 hp hm hk1 hk
      (by simpa only [w] using hwpos)
    intro r hr a
    exact mul_le_mul_of_nonneg_left (hbound r hr a) hw0

/-- The empty prefix has weight one and zero moving window.  Its weighted
drift estimate is handled separately from the active-prefix theorem. -/
theorem weightedDrift_zero_prefix (τ' δ α : ℝ)
    (N0 p N m : ℕ) (hm : 1 ≤ m) (ω : Ω d)
    (a : LoopArg (d.L N) 2) :
    let w := APrimeSupportRunning.weight δ (firstCellT τ')
      N0 p N 0 m ω
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    w = 1 ∧ v = 0 ∧
      w * APrimeDriftTimeFamily.driftAt
          d 0 60 N Step2.sigPM a 0 v 0 ω ≤
        w * APrimeFirstCellDriftCoefficient.endpointCoefficient
          δ (2 * α) N v 0 := by
  dsimp only
  have hw : APrimeSupportRunning.weight δ (firstCellT τ')
      N0 p N 0 m ω = 1 := by
    exact APrimeSmoothWeightActual.weight_zero_prefix d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh
      N0 p N m hm ω
  have hv : cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 = 0 := by
    simp only [cutNetPt_zero]
  refine ⟨hw, hv, ?_⟩
  rw [hw, hv, one_mul, one_mul]
  simpa only [d, cutNetPt_zero] using
    (APrimeFirstCellDriftAbsorbed.driftAt_cutNet_zero_le_endpointCoefficient
      δ (2 * α) N ω a)

/-- The positive `k = 2` resident of T434 carries the reparameterized
weighted drift estimate on the same sample, including both endpoints. -/
def positiveWeightedDriftPlateau (τ' δ α : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT τ' N ∧ firstCellT τ' N ≤ 1 / 2 ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) v, ∀ p : ℕ,
      ∀ a : LoopArg (d.L N) 2,
        APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
            APrimeDriftTimeFamily.driftAt
              d 0 60 N Step2.sigPM a 0 v r ω ≤
          APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
            APrimeFirstCellDriftCoefficient.endpointCoefficient
              δ (2 * α) N v r) ∧
    (∀ p : ℕ, ∀ a : LoopArg (d.L N) 2,
      APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeDriftTimeFamily.driftAt
            d 0 60 N Step2.sigPM a 0 v 0 ω ≤
        APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeFirstCellDriftCoefficient.endpointCoefficient
            δ (2 * α) N v 0) ∧
    ∀ p : ℕ, ∀ a : LoopArg (d.L N) 2,
      APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeDriftTimeFamily.driftAt
            d 0 60 N Step2.sigPM a 0 v v ω ≤
        APrimeSupportRunning.weight δ (firstCellT τ') 2 p N 2 N ω *
          APrimeFirstCellDriftCoefficient.endpointCoefficient
            δ (2 * α) N v v

theorem positiveWeightedDriftPlateau_of_sharp {τ' δ α : ℝ}
    (habs : APrimeFirstCellDriftAbsorbed.absorbedDriftBound
      τ' δ (2 * α))
    (hpositive :
      APrimeFirstCellSharpCommonEvent.positiveSharpPlateau τ' δ α) :
    positiveWeightedDriftPlateau τ' δ α := by
  filter_upwards [habs, hpositive, eventually_ge_atTop 2]
      with N habs hpositive hN
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau]
    at hpositive
  obtain ⟨ω, hω, hk, hw, hvpos, hvle, hvhalf, _hsource,
    _hJall, _hJ0, _hJv⟩ := hpositive
  have hωeg : ω ∈ APrimeFirstCellEGAllOutputRunning.good
      τ' δ ((2 * α) / 2) N := by
    rw [egEvent_two_mul]
    exact hω.2
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hprof : ∀ r ∈ Set.Icc (0 : ℝ) v,
      ∀ a : LoopArg (d.L N) 2,
        APrimeDriftTimeFamily.driftAt
            d 0 60 N Step2.sigPM a 0 v r ω ≤
          APrimeFirstCellDriftCoefficient.endpointCoefficient
            δ (2 * α) N v r := by
    exact habs ω hωeg 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hk (by rw [hw 1]; norm_num)
  refine ⟨ω, hω, hk, hvpos, hvle, hvhalf, hw, ?_, ?_, ?_⟩
  · intro r hr p a
    rw [hw p]
    simpa using hprof r hr a
  · intro p a
    rw [hw p]
    simpa using hprof 0 ⟨le_rfl, hvpos.le⟩ a
  · intro p a
    rw [hw p]
    simpa using hprof v ⟨hvpos.le, le_rfl⟩ a

/-- Closed same-event favorable weighted drift producer.  It makes no
weighted moment or event-complement claim. -/
theorem exists_weightedDriftGood_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ α : ℝ, 0 < α →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α) ∧
        weightedDriftGood τ' δ α ∧
        positiveWeightedDriftPlateau τ' δ α := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 α hα
  obtain ⟨hmeas, hp, hpositive⟩ := hall δ hδ hδ100 α hα
  have habs :=
    APrimeFirstCellDriftAbsorbed.eventually_absorbed_drift_on_active_support
      hτ' hδ hδ100 (by positivity : 0 < 2 * α)
  exact ⟨hmeas, hp, weightedDriftGood_of_absorbed habs,
    positiveWeightedDriftPlateau_of_sharp habs hpositive⟩

end RBM.APrimeFirstCellDriftWeightedGood

#print axioms RBM.APrimeFirstCellDriftWeightedGood.egEvent_two_mul
#print axioms RBM.APrimeFirstCellDriftWeightedGood.endpointCoefficient_two_mul
#print axioms RBM.APrimeFirstCellDriftWeightedGood.weightedDriftGood_of_absorbed
#print axioms RBM.APrimeFirstCellDriftWeightedGood.weightedDrift_zero_prefix
#print axioms RBM.APrimeFirstCellDriftWeightedGood.positiveWeightedDriftPlateau_of_sharp
#print axioms RBM.APrimeFirstCellDriftWeightedGood.exists_weightedDriftGood_with_plateau
