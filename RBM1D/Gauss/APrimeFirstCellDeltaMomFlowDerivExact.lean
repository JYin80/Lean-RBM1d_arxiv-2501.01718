/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFullCrossBudget
import RBM1D.Gauss.APrimeFirstCellJointCrossRegularity

/-!
# T549: actual first-cell pointwise Duhamel derivative assembly

The public `APrimeDuhamelModel.momFlowDeriv_le` theorem is instantiated with
the actual normalized moment, canonical smooth weight, moving endpoint,
actual drift, uncut quadratic variation, and T544's literal full cross budget.
-/

#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.APrimeNormalizedTestFun.normalizedTestFunBridge
#check @RBM.APrimeSmoothWeightActual.weightC1
#check @RBM.Gauss.quadVar_nonneg
#check @RBM.APrimeFirstCellGeneratorHle.canonicalWeight_generatorHle
#check @RBM.APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity

namespace RBM.APrimeFirstCellDeltaMomFlowDerivExact

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def canonicalM (tauPrime : Real) (N : Nat) : Nat :=
  APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh N

/-- The exact cross premise consumed by `momFlowDeriv_le`.  The rate is
T544's unscaled `literalBfull`; the derivative lemma supplies the outer
factor `2p`. -/
def exactHcrossAt (tauPrime delta alpha : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Prop :=
  let v := APrimeFirstCellSampleRegularity.endpoint N k
  APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0 v)
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k (canonicalM tauPrime N)) r ≤
    2 * (p : Real) *
      (∫ omega,
        APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
          |APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v)
            r omega| ^ (2 * p) ∂(P d)) ^
        ((2 * (p : Real) - 1) / (2 * (p : Real))) *
      APrimeFirstCellDeltaFullCrossBudget.literalBfull
        tauPrime delta alpha p N v r

/-- Fixed `delta`, `alpha`, and moment order precede the eventual matrix
size, uniformly over active endpoints, outputs, and positive times. -/
def actualHcrossExact (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N →
    ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Ioc (0 : Real) (APrimeFirstCellSampleRegularity.endpoint N k),
        exactHcrossAt tauPrime delta alpha p N k a r

/-- T462's cutoff moment is the identical canonical weighted moment used by
the derivative consumer. -/
theorem ycut_moment_eq_weighted_actual_moment
    {tauPrime delta : Real} {p N k : Nat}
    (hN : 2 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) (r : Real) :
    (∫ omega,
      |APrimeSmoothWeightActual.cutoff d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k (canonicalM tauPrime N) omega *
        ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
          (APrimeFirstCellSampleRegularity.endpoint N k) r
          (Gauss.Hflow d N r omega)‖| ^ (2 * p) ∂(P d)) =
      ∫ omega,
        APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
          |APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
              (APrimeFirstCellSampleRegularity.endpoint N k)) r omega| ^
                (2 * p) ∂(P d) := by
  apply integral_congr_ae
  filter_upwards [] with omega
  have hactive : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧ 2 ≤ N := ⟨hk, hN⟩
  let c := APrimeSmoothWeightActual.cutoff d 0 60 delta (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k (canonicalM tauPrime N) omega
  let y := ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
    (APrimeFirstCellSampleRegularity.endpoint N k) r
      (Gauss.Hflow d N r omega)‖
  have hc0 : 0 ≤ c := Cutoff.cutChi_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  simp only [APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellGeneratorHle.canonicalWeight,
    APrimeFirstCellGeneratorHle.actualWeight,
    APrimeSmoothWeightActual.weight, if_pos hactive,
    APrimeDuhamelModel.flowY]
  change |c * y| ^ (2 * p) = c ^ (2 * p) * |y| ^ (2 * p)
  rw [abs_of_nonneg (mul_nonneg hc0 hy0), abs_of_nonneg hy0, mul_pow]

/-- The T361 coefficient is exactly the derivative lemma's outer `2p`
times T544's unscaled literal consumer rate. -/
theorem t361_rhs_eq_two_p_literalBfull
    (tauPrime delta alpha : Real) (p N : Nat)
    (v r momentFactor : Real) :
    (1 / (2 * Real.sqrt r)) *
        (((2 * p : Nat) : Real) ^ 2 * (15 / 8 : Real)) *
        momentFactor *
        (APrimeFirstCellDeltaFullCrossBudget.prefixRate delta alpha N v *
            Real.sqrt (APrimeFirstCellQVCurrentRows.currentRate
              delta (delta / 16) alpha N v r) +
          APrimeFirstCellCrossBadPayment.jointEnvelope N *
            APrimeFirstCellCrossBadPayment.rho tauPrime delta alpha N ^
              ((1 : Real) / (2 * (p : Real)))) =
      2 * (p : Real) * momentFactor *
        APrimeFirstCellDeltaFullCrossBudget.literalBfull
          tauPrime delta alpha p N v r := by
  unfold APrimeFirstCellDeltaFullCrossBudget.literalBfull
    APrimeFirstCellFullCrossIntegrability.Bfull
    APrimeFirstCellDeltaFullCrossBudget.prefixRate
  push_cast
  ring

/-- Variable-delta specialization of the actual T361 cross estimate to the
verbatim cross premise consumed by `momFlowDeriv_le`. -/
theorem eventually_exactHcrossAt {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (hDelta100 : delta ≤ 1 / 100) (hAlpha : 0 < alpha)
    (p : Nat) (hp : 1 ≤ p) :
    actualHcrossExact tauPrime delta alpha p := by
  filter_upwards [
    APrimeFirstCellDeltaPrefixAbsorbed.eventually_prefixGradient_le
      hTau hDelta hDelta100 hAlpha,
    APrimeFirstCellQVCurrentRows.eventually_currentRowsBound
      hTau hDelta.le hAlpha,
    APrimeFirstCellJointGlobalPoly.eventually_t361_hAll hTau hDelta.le,
    APrimeFirstCellJointCrossRegularity.eventually_actual_jointCrossSampleRegularity
      hTau hDelta.le p hp,
    eventually_ge_atTop 2] with N hprefix hcurrent hAll hreg hN2
  intro k hk1 hk a r hr
  let v := APrimeFirstCellSampleRegularity.endpoint N k
  let m := canonicalM tauPrime N
  have hN : 0 < N := by omega
  have hm : 1 ≤ m := APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hvcell : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 := hvcell.2.trans ht.2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hri : r ∈ Icc (0 : Real) v := ⟨hr.1.le, hr.2⟩
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hb : 0 ≤ APrimeFirstCellDeltaFullCrossBudget.prefixRate
      delta alpha N v :=
    APrimeFirstCellDeltaFullCrossBudget.prefixRate_nonneg hvcell.1
  have hq : 0 ≤ APrimeFirstCellQVCurrentRows.currentRate
      delta (delta / 16) alpha N v r :=
    APrimeFirstCellFullCrossIntegrability.currentRate_nonneg
      hN hvcell.1 hvhalf hri
  have hBgood : ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N ∩
        APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k m,
      APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m omega ≤
          APrimeFirstCellDeltaFullCrossBudget.prefixRate
            delta alpha N v := by
    intro omega homega
    exact hprefix omega homega.1 k hk1 hk homega.2
  have hQgood : ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N ∩
        APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k m,
      APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r omega ≤
        APrimeFirstCellQVCurrentRows.currentRate
          delta (delta / 16) alpha N v r := by
    intro omega homega
    have hw : 0 < APrimeSupportRunning.weight delta (firstCellT tauPrime)
        2 1 N k m omega :=
      APrimeFirstCellPrefixGoodRows.actualWeight_pos_of_transition
        hN2 hk homega.2
    have hrows := hcurrent omega homega.1 2 1 k m hN2
      (by norm_num) hm hk1 hk hw
    simpa only [v, APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint,
      APrimeFirstCellDeltaFarRowAbsorb.tau] using
      ((hrows.2.2.2.2 r hri).2.2 a)
  have hP : ((P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N)ᶜ).toReal ≤
      APrimeFirstCellCrossBadPayment.rho tauPrime delta alpha N := by
    rfl
  have hregular := hreg k hk a r hri
  have hraw := APrimeCrossJointSplit.crossPart_active_le_jointEvent
    d 0 60 delta (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh 2 N k m p Step2.sigPM a v r
    (by norm_num) (by norm_num) (by norm_num) hv1 hri hr.1 hN hm hu hk hN2 hp
    (APrimeFirstCellSharpCommonEvent.measurableSet_sharpCommonEvent
      hTau delta alpha N)
    hb hq (by positivity) ENNReal.toReal_nonneg
    hBgood hQgood (hAll k hk a r hri) hP
    hregular.hYm hregular.hZm hregular.hYi hregular.hZi hregular.hProdInt
  have hmoment := ycut_moment_eq_weighted_actual_moment
    (tauPrime := tauPrime) (delta := delta) (p := p) hN2 hk a r
  unfold exactHcrossAt
  dsimp only [v]
  calc
    _ ≤ _ := hraw
    _ = _ := by
      rw [hmoment]
      exact t361_rhs_eq_two_p_literalBfull
        tauPrime delta alpha p N v r _

/-- At `r=0`, both the cross term and T544's literal consumer vanish. -/
theorem exactHcrossAt_zero_r0 (tauPrime delta alpha : Real)
    (p N k : Nat) (a : LoopArg (d.L N) 2) :
    exactHcrossAt tauPrime delta alpha p N k a 0 := by
  simp only [exactHcrossAt]
  rw [APrimeCrossJointSplit.crossPart_zero_r0]
  simp [APrimeFirstCellDeltaFullCrossBudget.literalBfull,
    APrimeFirstCellFullCrossIntegrability.Bfull]

/-- The literal conclusion of `momFlowDeriv_le` at one actual moving
first-cell coordinate. -/
def momFlowDerivBoundAt (tauPrime delta alpha : Real) (p N k : Nat)
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
          APrimeFirstCellDeltaFullCrossBudget.literalBfull
            tauPrime delta alpha p N v r) +
      (p : Real) * (2 * (p : Real) - 1) *
        (∫ omega, w omega * |Y omega| ^ (2 * p) ∂(P d)) ^
          (((p : Real) - 1) / (p : Real)) *
        APrimeModel.rateNormW (P d) w p Q

/-- Fixed-size assembly of every premise of `momFlowDeriv_le`. -/
theorem momFlowDerivBoundAt_of_hcross
    {tauPrime delta alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : Real}
    (hr : r ∈ Icc (0 : Real)
      (APrimeFirstCellSampleRegularity.endpoint N k))
    (hcross : exactHcrossAt
      tauPrime delta alpha p N k a r) :
    momFlowDerivBoundAt tauPrime delta alpha p N k a r := by
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
      APrimeFirstCellDeltaFullCrossBudget.literalBfull
        tauPrime delta alpha p N v r := by
    simpa [d, canonicalM, v, m, w, Y,
      exactHcrossAt,
      APrimeFirstCellSampleRegularity.endpoint,
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
    simpa [d, canonicalM,
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
    (Bc := APrimeFirstCellDeltaFullCrossBudget.literalBfull
      tauPrime delta alpha p N v r)
    hp htest hwC1 hr hw0 hQ0
    hreg.hYm hreg.hGm hreg.hQm hreg.hYi hreg.hGi hreg.hQi
    hreg.hm1 hreg.hm2 hle' hcross'

/-- The fixed moment order precedes the eventual matrix size.  The bound is
uniform in every active moving endpoint, output, and positive time. -/
def actualMomFlowDerivBound
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Ioc (0 : Real) (APrimeFirstCellSampleRegularity.endpoint N k),
        momFlowDerivBoundAt tauPrime delta alpha p N k a r

/-- The exact variable-delta cross premise supplies the final remaining hypothesis of
the public pointwise Duhamel derivative theorem. -/
theorem actualMomFlowDerivBound_of_hcross
    {tauPrime delta alpha : Real} {p : Nat}
    (hTau : 0 < tauPrime) (hp : 1 <= p)
    (hcross : actualHcrossExact
      tauPrime delta alpha p) :
    actualMomFlowDerivBound tauPrime delta alpha p := by
  filter_upwards [hcross, eventually_ge_atTop 1] with N hcrossN hN
  intro k hk1 hk a r hr
  exact momFlowDerivBoundAt_of_hcross hTau hp hN hk a
    ⟨hr.1.le, hr.2⟩ (hcrossN k hk1 hk a r hr)

/-- Closed positive-time producer from the variable-delta cross estimate. -/
theorem eventually_momFlowDerivBoundAt
    {tauPrime delta alpha : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) (hDelta100 : delta ≤ 1 / 100)
    (hAlpha : 0 < alpha) (p : Nat) (hp : 1 <= p) :
    actualMomFlowDerivBound tauPrime delta alpha p :=
  actualMomFlowDerivBound_of_hcross hTau hp
    (eventually_exactHcrossAt
      hTau hDelta hDelta100 hAlpha p hp)

/-- The totalized left endpoint `r = 0` satisfies the same literal
derivative inequality at every active cell, including `k = 0`. -/
def zeroRMomFlowDerivBound
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k,
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      momFlowDerivBoundAt tauPrime delta alpha p N k a 0

theorem eventually_zeroRMomFlowDerivBound
    {tauPrime delta alpha : Real} (hTau : 0 < tauPrime)
    (p : Nat) (hp : 1 <= p) :
    zeroRMomFlowDerivBound tauPrime delta alpha p := by
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
    (exactHcrossAt_zero_r0
      tauPrime delta alpha p N k a)

/-- Explicit empty-cell boundary package. -/
def kZeroMomFlowDerivBound
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
      momFlowDerivBoundAt tauPrime delta alpha p N 0 a 0

theorem eventually_kZeroMomFlowDerivBound
    {tauPrime delta alpha : Real} (hTau : 0 < tauPrime)
    (p : Nat) (hp : 1 <= p) :
    kZeroMomFlowDerivBound tauPrime delta alpha p := by
  filter_upwards [eventually_zeroRMomFlowDerivBound
    (alpha := alpha) hTau p hp] with N hzero
  intro a
  refine ⟨?_, hzero 0 (Nat.zero_le _) a⟩
  simp only [APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero]

/-- A nonempty `k = 2` resident on the same literal sharp event, carrying
the exact cross premise and assembled derivative inequality. -/
def positiveTwoMomFlowDerivResident
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    let v := APrimeFirstCellSampleRegularity.endpoint N 2
    0 < v ∧ v ≤ firstCellT tauPrime N ∧
    2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ a : LoopArg (d.L N) 2,
      exactHcrossAt tauPrime delta alpha p N 2 a 0) ∧
    (∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Ioc (0 : Real) v,
        exactHcrossAt tauPrime delta alpha p N 2 a r) ∧
    ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (0 : Real) v,
        momFlowDerivBoundAt tauPrime delta alpha p N 2 a r

theorem positiveTwoMomFlowDerivResident_of_inputs
    {tauPrime delta alpha : Real} {p : Nat}
    (hresident : APrimeFirstCellCrossBadPayment.positiveTwoBadPayment
      tauPrime delta alpha p)
    (hcross : actualHcrossExact tauPrime delta alpha p)
    (hpositive : actualMomFlowDerivBound tauPrime delta alpha p)
    (hzero : zeroRMomFlowDerivBound tauPrime delta alpha p) :
    positiveTwoMomFlowDerivResident tauPrime delta alpha p := by
  filter_upwards [hresident, hcross, hpositive, hzero]
      with N hresidentN hcrossN hpositiveN hzeroN
  obtain ⟨omega, homega, hk, _hw, hvpos, hvle, _hpay, _hjoint⟩ := hresidentN
  refine ⟨omega, homega, hvpos, hvle, hk, ?_, ?_, ?_⟩
  · intro a
    exact exactHcrossAt_zero_r0 tauPrime delta alpha p N 2 a
  · exact hcrossN 2 (by norm_num) hk
  intro a r hr
  by_cases hr0 : r = 0
  · subst r
    exact hzeroN 2 hk a
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    exact hpositiveN 2 (by norm_num) hk a r ⟨hrpos, hr.2⟩

/-- Closed variable-delta package.  One mesh exponent precedes every
admissible `delta`, loss exponent, and fixed moment order. -/
theorem exists_momFlowDeriv_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta → delta ≤ 1 / 100 →
      ∀ alpha : Real, 0 < alpha → ∀ p : Nat, 1 <= p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualMomFlowDerivBound tauPrime delta alpha p ∧
        zeroRMomFlowDerivBound tauPrime delta alpha p ∧
        kZeroMomFlowDerivBound tauPrime delta alpha p ∧
        positiveTwoMomFlowDerivResident tauPrime delta alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellCrossBadPayment.exists_badPaymentBound_with_positive_two
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 alpha hAlpha p hp
  obtain ⟨hmeas, hprob, _hpay, hresident⟩ :=
    hall delta hDelta hDelta100 alpha hAlpha p hp
  have hcross := eventually_exactHcrossAt
    hTau hDelta hDelta100 hAlpha p hp
  have hpositive := actualMomFlowDerivBound_of_hcross hTau hp hcross
  have hzero := eventually_zeroRMomFlowDerivBound
    (delta := delta) (alpha := alpha) hTau p hp
  have hkzero := eventually_kZeroMomFlowDerivBound
    (delta := delta) (alpha := alpha) hTau p hp
  exact ⟨hmeas, hprob, hpositive, hzero, hkzero,
    positiveTwoMomFlowDerivResident_of_inputs
      hresident hcross hpositive hzero⟩

end

end RBM.APrimeFirstCellDeltaMomFlowDerivExact

namespace RBM.APrimeFirstCellDeltaMomFlowDerivExact

#print axioms ycut_moment_eq_weighted_actual_moment
#print axioms t361_rhs_eq_two_p_literalBfull
#print axioms eventually_exactHcrossAt
#print axioms exactHcrossAt_zero_r0
#print axioms momFlowDerivBoundAt_of_hcross
#print axioms actualMomFlowDerivBound_of_hcross
#print axioms eventually_momFlowDerivBoundAt
#print axioms eventually_zeroRMomFlowDerivBound
#print axioms eventually_kZeroMomFlowDerivBound
#print axioms positiveTwoMomFlowDerivResident_of_inputs
#print axioms exists_momFlowDeriv_with_resident

end RBM.APrimeFirstCellDeltaMomFlowDerivExact
