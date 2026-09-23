/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaTargetWeight
import RBM1D.Gauss.APrimeFirstCellDeltaSameWeightLyapunov
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget

/-!
# T547: variable-delta canonical first-cell initial-moment budget

The delta-parametric moving initial-data estimate is applied on the literal
first cell with constant weight one.  Pointwise domination of the actual
delta-dependent canonical weight by one then gives the same estimate with
coefficient one, uniformly over every active endpoint and output coordinate.

Only the initial term is treated here.  No drift, cross, quadratic-variation,
Minkowski-sum, or finite-family assertion is made.
-/

namespace RBM.APrimeFirstCellDeltaInitialMomentBudget

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal endpoint of the `k`th first-cell prefix. -/
noncomputable def endpoint (N k : Nat) : Real :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

/-- The evolved initial coordinate at a moving first-cell endpoint. -/
noncomputable def initial (N k : Nat) (a : LoopArg (d.L N) 2) : Ω d -> Real :=
  APrimeAssembly.initialEvolvedNormAt (sample d) 0 60 (fun _ => 0) N
    (endpoint N k) a

/-- The actual canonical smooth weight, with `delta` kept explicit. -/
noncomputable def canonicalWeight (tauPrime delta : Real)
    (p N k : Nat) : Ω d -> Real :=
  APrimeFirstCellDeltaSameWeightLyapunov.canonicalHighWeight
    tauPrime delta p N k

/-- The unsimplified numerical slot delivered by the general initial-data
theorem. -/
noncomputable def initialBudget (delta : Real) (N k : Nat) : Real :=
  APrimeOneStep.initTerm ((N : Real) ^ (delta / 8))
    (etaT 0 0 / etaT 0 (endpoint N k))
    (APrimeInit.slotXi' ((N : Real) ^ (delta / 8))) /
    (etaT 0 0 / etaT 0 (endpoint N k)) ^ 4

/-- The desired variable-delta initial estimate at one active endpoint and
one output coordinate. -/
def initialBoundAt (tauPrime delta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (canonicalWeight tauPrime delta p N k) p
      (initial N k a) <=
    (N : Real) ^ (5 * delta / 32) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))

/-- Exact simplification of the raw slot at every active endpoint. -/
theorem initialBudget_eq {tauPrime delta : Real} (hTau : 0 < tauPrime)
    {N k : Nat} (hN : 1 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    initialBudget delta N k =
      (N : Real) ^ (5 * delta / 32) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real)) := by
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  exact APrimeAssembly.initial_slot_scale_eq hN
    (Step2Moment.ratR_pos (s := fun _ => 0) (N := N)
      (by norm_num : |(0 : Real)| < 2) (by norm_num) hv1)

/-- One eventual threshold works simultaneously for every active first-cell
index and every output coordinate. -/
theorem eventually_initialBoundAt {tauPrime delta : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      ∀ a : LoopArg (d.L N) 2,
        initialBoundAt tauPrime delta p N k a := by
  have ht0 : ∀ N, (0 : Real) <= firstCellT tauPrime N :=
    fun N => (APrimeSupportRunning.firstT_bounds hTau N).1
  have ht1 : ∀ N, firstCellT tauPrime N < 1 :=
    fun N => (APrimeSupportRunning.firstT_bounds hTau N).2.trans_lt (by norm_num)
  have hone := APrimeGeneralMovingInitialHinit.eventually_initial_hinit
    (E := 0) (D := 60) (c := 1 / 2) (δ := delta)
    (s := fun _ => 0) (t := firstCellT tauPrime)
    (by norm_num) (by norm_num) (fun _ => le_rfl) ht0 ht1
    (by norm_num)
    (APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg hTau)
    APrimeFirstCellInitialMomentBudget.firstCell_boundsCore hDelta p hp
    (fun _ _ _ => 1) (fun _ _ => aestronglyMeasurable_const)
    (fun _ _ _ => zero_le_one) (fun _ _ _ => le_rfl)
  filter_upwards [hone, eventually_ge_atTop 1] with N hraw hN k hk a
  have hv := MomentDuhamelCut.netFinset_subset_Icc (ht0 N)
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  let v : TimeIcc (fun _ => 0) (firstCellT tauPrime) N :=
    ⟨endpoint N k, hv⟩
  have hint := APrimeAssembly.integrable_initialEvolvedNormAt_pow_gauss d
    (E := 0) (by norm_num) (fun _ => le_rfl) ht0 ht1 p N v 60 a
  have hmono := APrimeFirstCellInitialMomentBudget.momNormW_le_one_weight (P d)
    (canonicalWeight tauPrime delta p N k) (initial N k a) p
    (fun omega => APrimeSmoothWeightActual.weight_nonneg d 0 60 delta
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh 2 p N k
      (APrimeFirstCellMinkowskiExact.canonicalM tauPrime N) omega)
    (fun omega => APrimeSmoothWeightActual.weight_le_one d 0 60 delta
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh 2 p N k
      (APrimeFirstCellMinkowskiExact.canonicalM tauPrime N) omega)
    hint
  have hb : momNormW (P d) (canonicalWeight tauPrime delta p N k) p
      (initial N k a) <= initialBudget delta N k := by
    exact hmono.trans (hraw (v, a))
  rw [initialBudget_eq hTau hN hk] at hb
  exact hb

/-- At the empty prefix, the endpoint is zero, the eta-ratio factor and the
actual canonical weight are exactly one, and the initial estimate loses no
additional factor. -/
theorem eventually_initial_k_zero {tauPrime delta : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
      endpoint N 0 = 0 ∧
      (etaT 0 0 / etaT 0 (endpoint N 0)) ^ (-(2 : Real)) = 1 ∧
      (∀ omega : Ω d,
        canonicalWeight tauPrime delta p N 0 omega = 1) ∧
      momNormW (P d) (canonicalWeight tauPrime delta p N 0) p
        (initial N 0 a) <= (N : Real) ^ (5 * delta / 32) := by
  filter_upwards [eventually_initialBoundAt hTau hDelta p hp] with N hbound a
  have hb := hbound 0 (Nat.zero_le _) a
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [endpoint, cutNetPt_zero]
  · simp [endpoint, cutNetPt_zero, etaT, mE_zero]
  · intro omega
    simpa only [canonicalWeight] using
      (APrimeFirstCellDeltaSameWeightLyapunov.canonicalHighWeight_k_zero
        tauPrime delta p N omega)
  · change momNormW (P d) (canonicalWeight tauPrime delta p N 0) p
      (initial N 0 a) <=
        (N : Real) ^ (5 * delta / 32) *
          (etaT 0 0 / etaT 0 (endpoint N 0)) ^ (-(2 : Real)) at hb
    simpa [endpoint, cutNetPt_zero, etaT, mE_zero] using hb

/-- A positive `k = 2` sample of the literal sharp event carries both the
canonical weight-one plateau and the initial estimate for every output. -/
def positiveTwoInitialResident (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧
    endpoint N 2 <= firstCellT tauPrime N ∧
    canonicalWeight tauPrime delta p N 2 omega = 1 ∧
    ∀ a : LoopArg (d.L N) 2,
      initialBoundAt tauPrime delta p N 2 a

/-- T467's canonical plateau and the uniform initial estimate are combined
on the identical event and sample. -/
theorem positiveTwoInitialResident_of_canonical
    {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (p : Nat) (hp : 1 <= p)
    (hresident :
      APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau
        tauPrime delta alpha) :
    positiveTwoInitialResident tauPrime delta alpha p := by
  filter_upwards [hresident,
    eventually_initialBoundAt hTau hDelta p hp] with N hr hb
  dsimp only [APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau]
    at hr
  obtain ⟨omega, homega, hk, hweight, hu2pos, hu2le, _hTle,
      _hsource, _hJall, _hJ0, _hJu2⟩ := hr
  refine ⟨omega, homega, hk, ?_, ?_, ?_, fun a => hb 2 hk a⟩
  · simpa only [endpoint, APrimeFirstCellCanonicalPlateau.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hu2pos
  · simpa only [endpoint, APrimeFirstCellCanonicalPlateau.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hu2le
  · simpa only [canonicalWeight,
      APrimeFirstCellDeltaSameWeightLyapunov.canonicalHighWeight,
      APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellCanonicalPlateau.canonicalWeight] using hweight p

/-- One first-cell parameter is chosen before every admissible `delta`.
For `alpha = delta/16`, the literal sharp event is measurable and high
probability, all active endpoints satisfy the variable-delta initial budget,
and a positive `k = 2` resident on that same event has canonical weight one. -/
theorem exists_deltaInitialMomentBudget_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      Cond272Reg B 0 (fun _ => 0) (firstCellT tauPrime) (1 / 2) ∧
      BoundsCore (sample d) 0 (fun _ => 0) ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        (∀ᶠ N : Nat in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N).Nonempty) ∧
        (∀ᶠ N : Nat in atTop, ∀ k,
          k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
            APrimeSmoothTransition.transitionMesh N ->
          ∀ a : LoopArg (d.L N) 2,
            initialBoundAt tauPrime delta p N k a) ∧
        (∀ᶠ N : Nat in atTop,
          ∀ a : LoopArg (d.L N) 2,
            endpoint N 0 = 0 ∧
            (etaT 0 0 / etaT 0 (endpoint N 0)) ^ (-(2 : Real)) = 1 ∧
            (∀ omega : Ω d,
              canonicalWeight tauPrime delta p N 0 omega = 1) ∧
            momNormW (P d) (canonicalWeight tauPrime delta p N 0) p
              (initial N 0 a) <= (N : Real) ^ (5 * delta / 32)) ∧
        positiveTwoInitialResident tauPrime delta (delta / 16) p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellCanonicalPlateau.exists_sharpCommonEvent_with_canonical_plateau
  refine ⟨tauPrime, hTau,
    APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg hTau,
    APrimeFirstCellInitialMomentBudget.firstCell_boundsCore, ?_⟩
  intro delta hDelta hDelta100 p hp
  have hAlpha : 0 < delta / 16 := by positivity
  obtain ⟨hmeas, hprob, hcanonical⟩ :=
    hall delta hDelta hDelta100 (delta / 16) hAlpha
  have hne := HighProb.nonempty (by simp) hprob
  exact ⟨hmeas, hprob, hne,
    eventually_initialBoundAt hTau hDelta p hp,
    eventually_initial_k_zero hTau hDelta p hp,
    positiveTwoInitialResident_of_canonical hTau hDelta p hp hcanonical⟩

#print axioms initialBudget_eq
#print axioms eventually_initialBoundAt
#print axioms eventually_initial_k_zero
#print axioms positiveTwoInitialResident_of_canonical
#print axioms exists_deltaInitialMomentBudget_with_resident

end

end RBM.APrimeFirstCellDeltaInitialMomentBudget
