/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellMomFlowDerivExact
import RBM1D.Gauss.APrimeFirstCellQVNormBudget
import RBM1D.Gauss.APrimeAssembly

/-!
# T494: exact first-cell canonical-weight Minkowski assembly

The actual pointwise derivative inequality is integrated with the canonical
smooth prefix weight.  The conclusion retains the literal drift, full-cross,
and uncut quadratic-variation integrals.
-/

namespace RBM.APrimeFirstCellMinkowskiExact

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real := APrimeFirstCellMomFlowDerivExact.delta

noncomputable def canonicalM (tauPrime : Real) (N : Nat) : Nat :=
  APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh N

noncomputable def endpoint (N k : Nat) : Real :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

noncomputable def weight (tauPrime : Real) (p N k : Nat) : Ω d -> Real :=
  APrimeSmoothWeightActual.weight d 0 60 delta (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    2 p N k (canonicalM tauPrime N)

noncomputable def Y (N k : Nat) (a : LoopArg (d.L N) 2)
    (r : Real) : Ω d -> Real :=
  APrimeDuhamelModel.flowY d N
    (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 (endpoint N k)) r

noncomputable def A (tauPrime : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  momNormW (P d) (weight tauPrime p N k) p
    (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r)

noncomputable def B (tauPrime alpha : Real) (p N k : Nat) (r : Real) : Real :=
  APrimeFirstCellFullCrossBudget.literalBfull tauPrime alpha p N
    (endpoint N k) r

noncomputable def g (tauPrime : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  APrimeModel.rateNormW (P d) (weight tauPrime p N k) p
    (APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r)

noncomputable def initial (N k : Nat) (a : LoopArg (d.L N) 2) : Ω d -> Real :=
  APrimeAssembly.initialEvolvedNormAt (sample d) 0 60 (fun _ => 0) N
    (endpoint N k) a

/-- The exact integrated conclusion at one actual moving first-cell output. -/
def minkowskiBoundAt (tauPrime alpha : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight tauPrime p N k) p (Y N k a (endpoint N k)) <=
    momNormW (P d) (weight tauPrime p N k) p (initial N k a) +
      2 * (∫ r in (0 : Real)..endpoint N k,
        (A tauPrime p N k a r + B tauPrime alpha p N k r)) +
      Real.sqrt ((2 * (p : Real) - 1) *
        ∫ r in (0 : Real)..endpoint N k, g tauPrime p N k a r)

/-- The normalized flow at the left endpoint is the literal evolved initial
coordinate used by the first-cell initial-data estimate. -/
theorem Y_zero_eq_initial {N k : Nat} (a : LoopArg (d.L N) 2)
    (hv0 : 0 <= endpoint N k) (hv1 : endpoint N k < 1) :
    Y N k a 0 = initial N k a := by
  funext omega
  have hflow := APrimeDriftTimeFamily.flowY_coordAt d 0 60 N Step2.sigPM a
    (s := 0) (v := endpoint N k) (by norm_num) hv0 hv1 0 omega
  change APrimeDuhamelModel.flowY d N
      (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
        (endpoint N k)) 0 omega = _
  rw [hflow]
  rfl

/-- Fixed-size exact Minkowski assembly from T480's pointwise derivative
bound. -/
theorem minkowskiBoundAt_of_deriv
    {tauPrime alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha)
    (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hbound : ∀ r ∈ Ioc (0 : Real) (endpoint N k),
      APrimeFirstCellMomFlowDerivExact.momFlowDerivBoundAt
        tauPrime alpha p N k a r) :
    minkowskiBoundAt tauPrime alpha p N k a := by
  let v := endpoint N k
  let m := canonicalM tauPrime N
  let w := weight tauPrime p N k
  let Psi := APrimeDriftTimeFamily.momentAt
    d 0 60 N p Step2.sigPM a 0 v
  let Psi1 := APrimeDriftTimeFamily.coordAt
    d 0 60 N Step2.sigPM a 0 v
  let wD := APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    2 p N k m
  let phi' := APrimeDuhamelModel.momFlowDeriv d N Psi w wD
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have htest : Gauss.TestFunT₁ d N (Icc (0 : Real) v) Psi := by
    exact APrimeNormalizedTestFun.normalizedTestFunBridge
      d 0 60 N p Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hwC1 : Gauss.WeightC1 d N w wD := by
    dsimp only [w, weight, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight, wD, m, canonicalM]
    exact APrimeSmoothWeightActual.weightC1 d (E := 0) (D := 60)
      (δ := delta) (s := fun _ => 0) (t := firstCellT tauPrime)
      (mesh := APrimeSmoothTransition.transitionMesh) (N₀ := 2)
      (p := p) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)
      (by norm_num) (by norm_num) hN hm hu
  have hw0 : ∀ omega, 0 <= w omega := by
    intro omega
    dsimp only [w, weight, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight]
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hw1 : ∀ omega, w omega <= 1 := by
    intro omega
    dsimp only [w, weight, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight]
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hre := APrimeDriftTimeFamily.momentAt_isModulusPow
    d 0 60 N p Step2.sigPM a 0 v
  have hcont := APrimeDuhamelModel.continuousOn_momFlow
    htest hwC1 hre (Set.Subset.rfl : Icc (0 : Real) v ⊆ Icc 0 v)
  have hderiv : ∀ u ∈ Ioo (0 : Real) v,
      HasDerivAt (fun r : Real => ∫ omega,
        w omega * |APrimeDuhamelModel.flowY d N Psi1 r omega| ^ (2 * p) ∂(P d))
        (phi' u) u := by
    intro u huI
    exact APrimeDuhamelModel.hasDerivAt_momFlow htest hwC1 hre huI.1
      (Icc_mem_nhds huI.1 huI.2)
  have hphiInt : IntervalIntegrable phi' volume 0 v := by
    exact APrimeDuhamelModel.intervalIntegrable_momFlowDeriv
      htest hwC1 hre (by norm_num) hv.1 Set.Subset.rfl
  have hA0 : ∀ u ∈ Icc (0 : Real) v,
      0 <= A tauPrime p N k a u := by
    intro u huI
    exact momNormW_nonneg (P := P d) hw0 p _
  have hB0 : ∀ u ∈ Icc (0 : Real) v,
      0 <= B tauPrime alpha p N k u := by
    intro u huI
    unfold B APrimeFirstCellFullCrossBudget.literalBfull
    unfold APrimeFirstCellFullCrossIntegrability.Bfull
    have hrate : 0 <= APrimeFirstCellQVCurrentRows.currentRate
        delta (delta / 16) alpha N v u := by
      exact APrimeFirstCellFullCrossIntegrability.currentRate_nonneg
        (by omega) hv.1 (hv.2.trans ht.2) huI
    have hpref : 0 <= APrimeFirstCellFullCrossBudget.prefixRate alpha N v :=
      APrimeFirstCellFullCrossBudget.prefixRate_nonneg hv.1
    have henv : 0 <= APrimeFirstCellCrossBadPayment.jointEnvelope N := by
      unfold APrimeFirstCellCrossBadPayment.jointEnvelope
      positivity
    have hrho : 0 <= APrimeFirstCellCrossBadPayment.rho
        tauPrime delta alpha N := ENNReal.toReal_nonneg
    positivity
  have hg0 : ∀ u ∈ Icc (0 : Real) v,
      0 <= g tauPrime p N k a u := by
    intro u huI
    exact APrimeModel.rateNormW_nonneg hw0 p _
  have hAint : IntervalIntegrable (A tauPrime p N k a) volume 0 v := by
    unfold A
    exact APrimeDriftTimeFamily.intervalIntegrable_momNormW_driftAt
      d 0 60 N Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
      w hwC1.cont.measurable hw0 hw1 p
  have hBint : IntervalIntegrable (B tauPrime alpha p N k) volume 0 v := by
    unfold B APrimeFirstCellFullCrossBudget.literalBfull
    exact (APrimeFirstCellFullCrossIntegrability.intervalIntegrable_Bfull
      APrimeFirstCellFarRowAbsorb.delta_pos.le
      hAlpha (by omega) hp hv.1 (hv.2.trans ht.2)
      (APrimeFirstCellFullCrossBudget.prefixRate_nonneg hv.1)
      (by unfold APrimeFirstCellCrossBadPayment.jointEnvelope; positivity)
      ENNReal.toReal_nonneg).1
  have hABint : IntervalIntegrable
      (fun r => A tauPrime p N k a r + B tauPrime alpha p N k r)
      volume 0 v := hAint.add hBint
  have hgint : IntervalIntegrable (g tauPrime p N k a) volume 0 v := by
    unfold g
    exact APrimeQVRateTime.intervalIntegrable_rateNormW_qvAt
      d 0 60 N p Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1 hp
      w hwC1.cont.measurable hw0 hw1
  have hprefix : ∀ u ∈ Icc (0 : Real) v,
      IntervalIntegrable (fun r => momNormW (P d) w p
        (APrimeDuhamelModel.flowY d N Psi1 r) *
          (A tauPrime p N k a r + B tauPrime alpha p N k r)) volume 0 u := by
    intro u huI
    exact APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
      hv.1 Set.Subset.rfl hp htest hwC1 hre hABint huI
  have hMink := weightedMinkowski_of_deriv_le hv.1 hp hw0 hcont hderiv
    hphiInt hA0 hB0 hg0 hABint hgint hprefix (by
      intro u huI
      have hb := hbound u ⟨huI.1, huI.2.le⟩
      simpa [APrimeFirstCellMomFlowDerivExact.momFlowDerivBoundAt,
        APrimeFirstCellSampleRegularity.endpoint,
        APrimeFirstCellGeneratorHle.endpoint,
        APrimeFirstCellSampleRegularity.weight,
        APrimeFirstCellGeneratorHle.canonicalWeight,
        APrimeFirstCellGeneratorHle.actualWeight,
        APrimeFirstCellSampleRegularity.Y,
        APrimeFirstCellSampleRegularity.G,
        APrimeFirstCellSampleRegularity.Q,
        APrimeFirstCellMomFlowDerivExact.canonicalM,
        endpoint, canonicalM, weight, Y, A, B, g, v, m, w, Psi, Psi1, wD, phi', d,
        delta, APrimeFirstCellMomFlowDerivExact.delta,
        APrimeFirstCellHcrossExact.delta] using hb)
  have hY0 : Y N k a 0 = initial N k a := Y_zero_eq_initial a hv.1 hv1
  have hMinkY : momNormW (P d) w p (Y N k a v) <=
      momNormW (P d) w p (Y N k a 0) +
        2 * (∫ r in (0 : Real)..v,
          (A tauPrime p N k a r + B tauPrime alpha p N k r)) +
        Real.sqrt ((2 * (p : Real) - 1) *
          ∫ r in (0 : Real)..v, g tauPrime p N k a r) := by
    simpa [Y, A, B, g, Psi1, d] using hMink
  rw [hY0] at hMinkY
  simpa [minkowskiBoundAt, v, w] using hMinkY

/-- The fixed moment order precedes the eventual matrix size; the exact
integrated estimate is uniform in every active moving endpoint and output. -/
def actualMinkowskiBound (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      minkowskiBoundAt tauPrime alpha p N k a

theorem actualMinkowskiBound_of_deriv
    {tauPrime alpha : Real} {p : Nat}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha) (hp : 1 <= p)
    (hderiv : APrimeFirstCellMomFlowDerivExact.actualMomFlowDerivBound
      tauPrime alpha p) :
    actualMinkowskiBound tauPrime alpha p := by
  filter_upwards [hderiv, eventually_ge_atTop 1] with N hderivN hN
  intro k hk1 hk a
  exact minkowskiBoundAt_of_deriv hTau hAlpha hp (by omega) hk a
    (hderivN k hk1 hk a)

theorem eventually_minkowskiBoundAt
    {tauPrime alpha : Real} (hTau : 0 < tauPrime)
    (hAlpha : 0 < alpha) (p : Nat) (hp : 1 <= p) :
    actualMinkowskiBound tauPrime alpha p :=
  actualMinkowskiBound_of_deriv hTau hAlpha hp
    (APrimeFirstCellMomFlowDerivExact.eventually_momFlowDerivBoundAt
      hTau hAlpha p hp)

/-- The zero mesh index is the exact zero-time branch of the integrated
estimate. -/
theorem minkowskiBoundAt_k_zero (tauPrime alpha : Real) (p N : Nat)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧ minkowskiBoundAt tauPrime alpha p N 0 a := by
  have hv : endpoint N 0 = 0 := by simp [endpoint, cutNetPt_zero]
  have hv0 : 0 <= endpoint N 0 := by rw [hv]
  have hv1 : endpoint N 0 < 1 := by rw [hv]; norm_num
  have hY0 : Y N 0 a 0 = initial N 0 a :=
    Y_zero_eq_initial a hv0 hv1
  constructor
  · exact hv
  · unfold minkowskiBoundAt
    rw [hv, hY0]
    simp

def kZeroMinkowskiBound (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧ minkowskiBoundAt tauPrime alpha p N 0 a

theorem eventually_kZeroMinkowskiBound
    (tauPrime alpha : Real) (p : Nat) :
    kZeroMinkowskiBound tauPrime alpha p := by
  exact Filter.Eventually.of_forall fun N a =>
    minkowskiBoundAt_k_zero tauPrime alpha p N a

/-- A concrete positive `k = 2` resident on T480's literal sharp common
event, with the exact integrated inequality for every output. -/
def positiveTwoMinkowskiResident
    (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    let u0 := endpoint N 0
    let u1 := endpoint N 1
    let v := endpoint N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v <= firstCellT tauPrime N ∧
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    ∀ a : LoopArg (d.L N) 2,
      minkowskiBoundAt tauPrime alpha p N 2 a

theorem positiveTwoMinkowskiResident_of_inputs
    {tauPrime alpha : Real} {p : Nat}
    (hresident :
      APrimeFirstCellMomFlowDerivExact.positiveTwoMomFlowDerivResident
        tauPrime alpha p)
    (hmink : actualMinkowskiBound tauPrime alpha p) :
    positiveTwoMinkowskiResident tauPrime alpha p := by
  filter_upwards [hresident, hmink] with N hresidentN hminkN
  obtain ⟨omega, homega, hu0, hu1, hu12, hv, hk, _hregular,
    _hcross0, _hcrossPositive, _hderiv⟩ := hresidentN
  refine ⟨omega, homega, hu0, hu1, hu12, hv, hk, ?_⟩
  intro a
  exact hminkN 2 (by norm_num) hk a

/-- Closed T494 producer.  It retains the one literal sharp common event
from T480 and adds only deterministic Minkowski integration. -/
theorem exists_minkowski_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ alpha : Real, 0 < alpha -> ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualMinkowskiBound tauPrime alpha p ∧
        kZeroMinkowskiBound tauPrime alpha p ∧
        positiveTwoMinkowskiResident tauPrime alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellMomFlowDerivExact.exists_momFlowDeriv_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro alpha hAlpha p hp
  obtain ⟨hmeas, hprob, hderiv, _hzero, _hkzero, hresident⟩ :=
    hall alpha hAlpha p hp
  have hmink := actualMinkowskiBound_of_deriv hTau hAlpha hp hderiv
  exact ⟨hmeas, hprob, hmink,
    eventually_kZeroMinkowskiBound tauPrime alpha p,
    positiveTwoMinkowskiResident_of_inputs hresident hmink⟩

end

end RBM.APrimeFirstCellMinkowskiExact

namespace RBM.APrimeFirstCellMinkowskiExact

#print axioms Y_zero_eq_initial
#print axioms minkowskiBoundAt_of_deriv
#print axioms actualMinkowskiBound_of_deriv
#print axioms eventually_minkowskiBoundAt
#print axioms minkowskiBoundAt_k_zero
#print axioms positiveTwoMinkowskiResident_of_inputs
#print axioms exists_minkowski_with_resident

end RBM.APrimeFirstCellMinkowskiExact
