/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeNormalizedGenerator
import RBM1D.Gauss.APrimeFirstCellTimeIntegrability
import RBM1D.Gauss.APrimeFirstCellSharpCommonEvent

/-!
# T446: the actual weighted first-cell generator comparison

The normalized Gaussian generator comparison is multiplied by the actual
nonnegative smooth prefix weight.  This is precisely the pointwise `hle`
premise of `APrimeDuhamelModel.momFlowDeriv_le`.
-/

namespace RBM.APrimeFirstCellGeneratorHle

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The literal moving endpoint `u_k` of the first-cell prefix. -/
noncomputable def endpoint (N k : ℕ) : ℝ :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

/-- The actual smooth prefix weight, with its smoothing order left explicit. -/
noncomputable def actualWeight (τ' δ : ℝ) (N₀ p N k m : ℕ) : Ω d → ℝ :=
  APrimeSmoothWeightActual.weight d 0 60 δ (fun _ => 0) (firstCellT τ')
    APrimeSmoothTransition.transitionMesh N₀ p N k m

/-- The canonical actual smooth prefix weight. -/
noncomputable def canonicalWeight (τ' δ : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  actualWeight τ' δ 2 p N k
    (APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)

/-- The exact pointwise `hle` inequality at one sample. -/
def generatorHleAtSample (τ' δ : ℝ) (N₀ p N k m : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) (ω : Ω d) : Prop :=
  actualWeight τ' δ N₀ p N k m ω *
      ((Gauss.timeD1
          (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0
            (endpoint N k)) r (Gauss.Hflow d N r ω)).re +
        APrimeDuhamelModel.genPt d N
          (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0
            (endpoint N k) r) (Gauss.Hflow d N r ω))
    ≤ actualWeight τ' δ N₀ p N k m ω *
      (2 * (p : ℝ) *
          (|APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
                (endpoint N k)) r ω| ^ (2 * p - 1) *
            |APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0
              (endpoint N k) r ω|) +
        (p : ℝ) * (2 * (p : ℝ) - 1) *
          (|APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
                (endpoint N k)) r ω| ^ (2 * p - 2) *
            APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
              (endpoint N k) r ω))

/-- The full-sample-space version of the exact `hle` premise. -/
def generatorHle (τ' δ : ℝ) (N₀ p N k m : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : Prop :=
  ∀ ω : Ω d, generatorHleAtSample τ' δ N₀ p N k m a r ω

/-- Multiplying the normalized generator bridge by any actual smooth prefix
weight proves `hle`; no event restriction is present. -/
theorem actualWeight_generatorHle {τ' δ : ℝ} (hτ' : 0 < τ')
    {N₀ p N k m : ℕ} (hp : 1 ≤ p)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (endpoint N k)) :
    generatorHle τ' δ N₀ p N k m a r := by
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : endpoint N k ∈ Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  intro ω
  unfold generatorHleAtSample
  apply mul_le_mul_of_nonneg_left
  · exact APrimeNormalizedGenerator.normalizedGeneratorBridge
      d 0 60 N p Step2.sigPM a
      (by norm_num) (by norm_num) hr.1 hr.2 hv1 hp ω
  · exact APrimeSmoothWeightActual.weight_nonneg d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh
      N₀ p N k m ω

/-- The same theorem for the canonical actual weight. -/
theorem canonicalWeight_generatorHle {τ' δ : ℝ} (hτ' : 0 < τ')
    {p N k : ℕ} (hp : 1 ≤ p)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (endpoint N k)) :
    generatorHle τ' δ 2 p N k
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N) a r :=
  actualWeight_generatorHle hτ' hp hk a hr

/-- The moment order is chosen before the eventual cutoff.  In fact the
pointwise generator statement holds at every finite cutoff. -/
theorem eventually_canonicalWeight_generatorHle {τ' δ : ℝ}
    (hτ' : 0 < τ') :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k, k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) (endpoint N k),
          generatorHle τ' δ 2 p N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (firstCellT τ') APrimeSmoothTransition.transitionMesh N) a r := by
  intro p hp
  exact Filter.Eventually.of_forall fun N k hk a r hr =>
    canonicalWeight_generatorHle hτ' hp hk a hr

/-- Both closed-interval endpoints are included. -/
theorem eventually_canonicalWeight_generatorHle_endpoints {τ' δ : ℝ}
    (hτ' : 0 < τ') :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k, k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        ∀ a : LoopArg (d.L N) 2,
          generatorHle τ' δ 2 p N k
              (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
                (firstCellT τ') APrimeSmoothTransition.transitionMesh N) a 0 ∧
            generatorHle τ' δ 2 p N k
              (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
                (firstCellT τ') APrimeSmoothTransition.transitionMesh N) a
              (endpoint N k) := by
  intro p hp
  filter_upwards [eventually_canonicalWeight_generatorHle hτ' p hp] with N hN
  intro k hk a
  have hv : 0 ≤ endpoint N k := by
    have ht := APrimeSupportRunning.firstT_bounds hτ' N
    exact (MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)).1
  exact ⟨hN k hk a 0 ⟨le_rfl, hv⟩,
    hN k hk a (endpoint N k) ⟨hv, le_rfl⟩⟩

/-- The separate `k = 0` branch is the zero window and is valid for every
cutoff, without an eventuality. -/
theorem canonicalWeight_generatorHle_k_zero (τ' δ : ℝ) {p N : ℕ}
    (hp : 1 ≤ p) (a : LoopArg (d.L N) 2) :
    generatorHle τ' δ 2 p N 0
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N) a 0 := by
  intro ω
  unfold generatorHleAtSample
  apply mul_le_mul_of_nonneg_left
  · simpa only [endpoint, cutNetPt_zero] using
      (APrimeNormalizedGenerator.normalizedGeneratorBridge
        d 0 60 N p Step2.sigPM a
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hp ω)
  · exact APrimeSmoothWeightActual.weight_nonneg d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N 0
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω

/-- The drift used above is literally `eGpm + quadGlue`. -/
theorem driftF_eq_eGpm_add_quadGlue (N : ℕ) (r : ℝ) (ω : Ω d)
    (a : LoopArg ((Gauss.band d).L N) 2) :
    Step2FarInputs.farDrift (Gauss.sample d) 0 N r ω a =
      EGDef.eGpm ((Gauss.band d).L N) ((Gauss.band d).W N) (mSigma 0)
          ((Gauss.sample d).H N r ω) (zt 0 r) (a 0) (a 1) +
        primBil ((Gauss.band d).L N) ((Gauss.band d).W N)
          (gloop ((Gauss.band d).L N) ((Gauss.band d).W N)
              ((Gauss.sample d).H N r ω) (zt 0 r) -
            (Gauss.band d).Kval 0 N r)
          (gloop ((Gauss.band d).L N) ((Gauss.band d).W N)
              ((Gauss.sample d).H N r ω) (zt 0 r) -
            (Gauss.band d).Kval 0 N r)
          ⟨[true, false], [a 0, a 1]⟩ :=
  Step2FarInputs.farDrift_eq_eGpm_add_quadGlue
    (Gauss.sample d) (E := 0) N r ω a

/-- The covariance in `hle` is the uncut quadratic variation of the same
normalized evolved coordinate. -/
theorem qvAt_eq_uncut_evolved (N : ℕ) (a : LoopArg (d.L N) 2)
    (v r : ℝ) (ω : Ω d) :
    APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω =
      APrimeDuhamelModel.qvRateEvolved d N
        (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v) r ω :=
  rfl

/-- T434's same-event resident has a positive `k = 2` endpoint, actual
weight one (with smoothing order `m = N`), and the pointwise generator
comparison.  Event membership is only part of the nondegenerate witness. -/
def positiveActualWeightResident (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, actualWeight τ' δ 2 p N 2 N ω = 1) ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    ∀ p : ℕ, 1 ≤ p → ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (0 : ℝ) (endpoint N 2),
        generatorHleAtSample τ' δ 2 p N 2 N a r ω

theorem positiveActualWeightResident_of_sharp {τ' δ ν : ℝ}
    (hτ' : 0 < τ')
    (hpositive : APrimeFirstCellSharpCommonEvent.positiveSharpPlateau
      τ' δ ν) :
    positiveActualWeightResident τ' δ ν := by
  filter_upwards [hpositive] with N hN
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hN
  obtain ⟨ω, hω, hk, hw, hu2, hu2T, _hT, _hsource,
    _hJall, _hJ0, _hJ2⟩ := hN
  refine ⟨ω, hω, hk, ?_, hu2, hu2T, ?_⟩
  · intro p
    simpa only [actualWeight, APrimeSupportRunning.weight,
      Gauss.firstCellS_eq_zero] using hw p
  · intro p hp a r hr
    exact actualWeight_generatorHle hτ' hp hk a hr ω

/-- Closed producer retaining T434's parameter order and same-event resident. -/
theorem exists_sharpCommonEvent_with_generatorHle :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        positiveActualWeightResident τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, positiveActualWeightResident_of_sharp hτ' hpositive⟩

#print axioms actualWeight_generatorHle
#print axioms eventually_canonicalWeight_generatorHle
#print axioms canonicalWeight_generatorHle_k_zero
#print axioms driftF_eq_eGpm_add_quadGlue
#print axioms qvAt_eq_uncut_evolved
#print axioms positiveActualWeightResident_of_sharp
#print axioms exists_sharpCommonEvent_with_generatorHle

end

end RBM.APrimeFirstCellGeneratorHle
