/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellHcrossExact

/-!
# T480: actual first-cell pointwise Duhamel derivative assembly

The public `APrimeDuhamelModel.momFlowDeriv_le` theorem is instantiated with
the actual normalized moment, canonical smooth weight, moving endpoint,
actual drift, uncut quadratic variation, and T476's exact cross budget.
-/

#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.APrimeNormalizedTestFun.normalizedTestFunBridge
#check @RBM.APrimeSmoothWeightActual.weightC1
#check @RBM.Gauss.quadVar_nonneg
#check @RBM.APrimeFirstCellGeneratorHle.canonicalWeight_generatorHle
#check @RBM.APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity
#check @RBM.APrimeFirstCellHcrossExact.eventually_exactHcrossAt

namespace RBM.APrimeFirstCellMomFlowDerivExact

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real := APrimeFirstCellHcrossExact.delta

noncomputable def canonicalM (tauPrime : Real) (N : Nat) : Nat :=
  APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh N

/-- The literal conclusion of `momFlowDeriv_le` at one actual moving
first-cell coordinate. -/
def momFlowDerivBoundAt (tauPrime alpha : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Prop :=
  let v := APrimeFirstCellSampleRegularity.endpoint N k
  let w := APrimeFirstCellSampleRegularity.weight tauPrime delta p N k
  let Y := APrimeFirstCellSampleRegularity.Y N k a r
  let G := APrimeFirstCellSampleRegularity.G N k a r
  let Q := APrimeFirstCellSampleRegularity.Q N k a r
  APrimeDuhamelModel.momFlowDeriv d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0 v)
      w
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k (canonicalM tauPrime N)) r <=
    2 * (p : Real) *
        (∫ omega, w omega * |Y omega| ^ (2 * p) ∂(P d)) ^
          ((2 * (p : Real) - 1) / (2 * (p : Real))) *
        (momNormW (P d) w p G +
          APrimeFirstCellFullCrossBudget.literalBfull
            tauPrime alpha p N v r) +
      (p : Real) * (2 * (p : Real) - 1) *
        (∫ omega, w omega * |Y omega| ^ (2 * p) ∂(P d)) ^
          (((p : Real) - 1) / (p : Real)) *
        APrimeModel.rateNormW (P d) w p Q

/-- Fixed-size assembly of every premise of `momFlowDeriv_le`. -/
theorem momFlowDerivBoundAt_of_hcross
    {tauPrime alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : Real}
    (hr : r ∈ Icc (0 : Real)
      (APrimeFirstCellSampleRegularity.endpoint N k))
    (hcross : APrimeFirstCellHcrossExact.exactHcrossAt
      tauPrime alpha p N k a r) :
    momFlowDerivBoundAt tauPrime alpha p N k a r := by
  let v := APrimeFirstCellSampleRegularity.endpoint N k
  let m := canonicalM tauPrime N
  let w := APrimeFirstCellSampleRegularity.weight tauPrime delta p N k
  let Y := APrimeFirstCellSampleRegularity.Y N k a r
  let G := APrimeFirstCellSampleRegularity.G N k a r
  let Q := APrimeFirstCellSampleRegularity.Q N k a r
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have htest : Gauss.TestFunT₁ d N (Icc (0 : Real) v)
      (APrimeDriftTimeFamily.momentAt
        d 0 60 N p Step2.sigPM a 0 v) := by
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
  have hwC1 : Gauss.WeightC1 d N w
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k m) := by
    dsimp only [w, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight, m, canonicalM]
    exact APrimeSmoothWeightActual.weightC1 d (E := 0) (D := 60)
      (δ := delta) (s := fun _ => 0) (t := firstCellT tauPrime)
      (mesh := APrimeSmoothTransition.transitionMesh) (N₀ := 2)
      (p := p) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)
      (by norm_num) (by norm_num) hN hm hu
  have hw0 : ∀ omega, 0 <= w omega := by
    intro omega
    dsimp only [w, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight]
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hQ0 : ∀ omega, 0 <= Q omega := by
    intro omega
    dsimp only [Q, APrimeFirstCellSampleRegularity.Q,
      APrimeDriftTimeFamily.qvAt]
    exact Gauss.quadVar_nonneg _ _
  have hreg := APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity
    (δ := delta) hTau hp hN hk a hr
  have hle := APrimeFirstCellGeneratorHle.canonicalWeight_generatorHle
    (δ := delta) hTau hp hk a hr
  have hcross' : APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt
        d 0 60 N p Step2.sigPM a 0 v)
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k m) r <=
    2 * (p : Real) *
      (∫ omega, w omega * |Y omega| ^ (2 * p) ∂(P d)) ^
        ((2 * (p : Real) - 1) / (2 * (p : Real))) *
      APrimeFirstCellFullCrossBudget.literalBfull
        tauPrime alpha p N v r := by
    simpa [d, delta, canonicalM, v, m, w, Y,
      APrimeFirstCellHcrossExact.exactHcrossAt,
      APrimeFirstCellHcrossExact.endpoint,
      APrimeFirstCellHcrossExact.canonicalM,
      APrimeFirstCellHcrossExact.delta,
      APrimeFirstCellSampleRegularity.Y,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hcross
  have hle' : ∀ omega, w omega *
      ((Gauss.timeD1
          (APrimeDriftTimeFamily.momentAt
            d 0 60 N p Step2.sigPM a 0 v) r
            (Gauss.Hflow d N r omega)).re +
        APrimeDuhamelModel.genPt d N
          (APrimeDriftTimeFamily.momentAt
            d 0 60 N p Step2.sigPM a 0 v r)
          (Gauss.Hflow d N r omega)) <=
      w omega *
        (2 * (p : Real) * (|Y omega| ^ (2 * p - 1) * |G omega|) +
          (p : Real) * (2 * (p : Real) - 1) *
            (|Y omega| ^ (2 * p - 2) * Q omega)) := by
    simpa [d, delta, canonicalM,
      APrimeFirstCellGeneratorHle.generatorHle,
      APrimeFirstCellGeneratorHle.generatorHleAtSample,
      APrimeFirstCellGeneratorHle.actualWeight,
      APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellSampleRegularity.Y,
      APrimeFirstCellSampleRegularity.G,
      APrimeFirstCellSampleRegularity.Q,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint,
      v, w, Y, G, Q] using hle
  dsimp only [momFlowDerivBoundAt, v, w, Y, G, Q]
  exact APrimeDuhamelModel.momFlowDeriv_le
    (Ψ₁ := APrimeDriftTimeFamily.coordAt
      d 0 60 N Step2.sigPM a 0 v)
    (G := G) (Q := Q)
    (Bc := APrimeFirstCellFullCrossBudget.literalBfull
      tauPrime alpha p N v r)
    hp htest hwC1 hr hw0 hQ0
    hreg.hYm hreg.hGm hreg.hQm hreg.hYi hreg.hGi hreg.hQi
    hreg.hm1 hreg.hm2 hle' hcross'

/-- The fixed moment order precedes the eventual matrix size.  The bound is
uniform in every active moving endpoint, output, and positive time. -/
def actualMomFlowDerivBound
    (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Ioc (0 : Real) (APrimeFirstCellSampleRegularity.endpoint N k),
        momFlowDerivBoundAt tauPrime alpha p N k a r

/-- T476's exact cross premise supplies the final remaining hypothesis of
the public pointwise Duhamel derivative theorem. -/
theorem actualMomFlowDerivBound_of_hcross
    {tauPrime alpha : Real} {p : Nat}
    (hTau : 0 < tauPrime) (hp : 1 <= p)
    (hcross : APrimeFirstCellHcrossExact.actualHcrossExact
      tauPrime alpha p) :
    actualMomFlowDerivBound tauPrime alpha p := by
  filter_upwards [hcross, eventually_ge_atTop 1] with N hcrossN hN
  intro k hk1 hk a r hr
  exact momFlowDerivBoundAt_of_hcross hTau hp hN hk a
    ⟨hr.1.le, hr.2⟩ (hcrossN k hk1 hk a r hr)

/-- Closed positive-time producer from T476. -/
theorem eventually_momFlowDerivBoundAt
    {tauPrime alpha : Real} (hTau : 0 < tauPrime)
    (hAlpha : 0 < alpha) (p : Nat) (hp : 1 <= p) :
    actualMomFlowDerivBound tauPrime alpha p :=
  actualMomFlowDerivBound_of_hcross hTau hp
    (APrimeFirstCellHcrossExact.eventually_exactHcrossAt
      hTau hAlpha p hp)

/-- The totalized left endpoint `r = 0` satisfies the same literal
derivative inequality at every active cell, including `k = 0`. -/
def zeroRMomFlowDerivBound
    (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k,
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      momFlowDerivBoundAt tauPrime alpha p N k a 0

theorem eventually_zeroRMomFlowDerivBound
    {tauPrime alpha : Real} (hTau : 0 < tauPrime)
    (p : Nat) (hp : 1 <= p) :
    zeroRMomFlowDerivBound tauPrime alpha p := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro k hk a
  have hr : (0 : Real) ∈ Icc 0
      (APrimeFirstCellSampleRegularity.endpoint N k) := by
    refine ⟨le_rfl, ?_⟩
    exact (MomentDuhamelCut.netFinset_subset_Icc
      (APrimeSupportRunning.firstT_bounds hTau N).1
      (APrimeSupportRunning.mesh_pos N) _
      (cutNetPt_mem_netFinset hk)).1
  exact momFlowDerivBoundAt_of_hcross hTau hp hN hk a hr
    (APrimeFirstCellHcrossExact.exactHcrossAt_zero_r0
      tauPrime alpha p N k a)

/-- Explicit empty-cell boundary package. -/
def kZeroMomFlowDerivBound
    (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
      momFlowDerivBoundAt tauPrime alpha p N 0 a 0

theorem eventually_kZeroMomFlowDerivBound
    {tauPrime alpha : Real} (hTau : 0 < tauPrime)
    (p : Nat) (hp : 1 <= p) :
    kZeroMomFlowDerivBound tauPrime alpha p := by
  filter_upwards [eventually_zeroRMomFlowDerivBound
    (alpha := alpha) hTau p hp] with N hzero
  intro a
  refine ⟨?_, hzero 0 (Nat.zero_le _) a⟩
  simp only [APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero]

/-- A nonempty `k = 2` resident on T476's very same sharp event.  It retains
the cross regularity and exact `hcross` fields and appends the assembled
derivative inequality on the closed time interval. -/
def positiveTwoMomFlowDerivResident
    (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    let u0 := APrimeFirstCellHcrossExact.endpoint N 0
    let u1 := APrimeFirstCellHcrossExact.endpoint N 1
    let v := APrimeFirstCellHcrossExact.endpoint N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v <= firstCellT tauPrime N ∧
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : Real) v,
      APrimeFirstCellJointCrossRegularity.JointCrossSampleRegularity p
        (APrimeFirstCellJointCrossRegularity.Ycut
          tauPrime delta N 2 a r)
        (APrimeFirstCellJointCrossRegularity.jointRate
          tauPrime delta N 2 a r)) ∧
    (∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellHcrossExact.exactHcrossAt
        tauPrime alpha p N 2 a 0) ∧
    (∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Ioc (0 : Real) v,
        APrimeFirstCellHcrossExact.exactHcrossAt
          tauPrime alpha p N 2 a r) ∧
    ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (0 : Real) v,
        momFlowDerivBoundAt tauPrime alpha p N 2 a r

theorem positiveTwoMomFlowDerivResident_of_inputs
    {tauPrime alpha : Real} {p : Nat}
    (hresident : APrimeFirstCellHcrossExact.positiveTwoExactHcrossResident
      tauPrime alpha p)
    (hpositive : actualMomFlowDerivBound tauPrime alpha p)
    (hzero : zeroRMomFlowDerivBound tauPrime alpha p) :
    positiveTwoMomFlowDerivResident tauPrime alpha p := by
  filter_upwards [hresident, hpositive, hzero] with N hresidentN hpositiveN hzeroN
  obtain ⟨omega, homega, hu0, hu1, hu12, hv, hk, hregular,
    hcross0, hcrossPositive⟩ := hresidentN
  refine ⟨omega, homega, hu0, hu1, hu12, hv, hk, hregular,
    hcross0, hcrossPositive, ?_⟩
  intro a r hr
  by_cases hr0 : r = 0
  · subst r
    exact hzeroN 2 hk a
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    exact hpositiveN 2 (by norm_num) hk a r ⟨hrpos, hr.2⟩

/-- Closed T480 package.  The probability statement and the positive
resident use exactly T476's sharp event; the pointwise derivative bound adds
no event or model assumptions. -/
theorem exists_momFlowDeriv_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ alpha : Real, 0 < alpha -> ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualMomFlowDerivBound tauPrime alpha p ∧
        zeroRMomFlowDerivBound tauPrime alpha p ∧
        kZeroMomFlowDerivBound tauPrime alpha p ∧
        positiveTwoMomFlowDerivResident tauPrime alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellHcrossExact.exists_exactHcross_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro alpha hAlpha p hp
  obtain ⟨hmeas, hprob, hcross, _hkzeroCross, hresident⟩ :=
    hall alpha hAlpha p hp
  have hpositive := actualMomFlowDerivBound_of_hcross hTau hp hcross
  have hzero := eventually_zeroRMomFlowDerivBound
    (alpha := alpha) hTau p hp
  have hkzero := eventually_kZeroMomFlowDerivBound
    (alpha := alpha) hTau p hp
  exact ⟨hmeas, hprob, hpositive, hzero, hkzero,
    positiveTwoMomFlowDerivResident_of_inputs
      hresident hpositive hzero⟩

end

end RBM.APrimeFirstCellMomFlowDerivExact

namespace RBM.APrimeFirstCellMomFlowDerivExact

#print axioms momFlowDerivBoundAt_of_hcross
#print axioms actualMomFlowDerivBound_of_hcross
#print axioms eventually_momFlowDerivBoundAt
#print axioms eventually_zeroRMomFlowDerivBound
#print axioms eventually_kZeroMomFlowDerivBound
#print axioms positiveTwoMomFlowDerivResident_of_inputs
#print axioms exists_momFlowDeriv_with_resident

end RBM.APrimeFirstCellMomFlowDerivExact
