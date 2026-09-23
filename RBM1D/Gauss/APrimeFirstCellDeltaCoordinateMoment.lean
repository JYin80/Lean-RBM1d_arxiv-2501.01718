/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaMomFlowDerivExact
import RBM1D.Gauss.APrimeFirstCellDeltaMinkowskiConsumer
import RBM1D.Gauss.APrimeFirstCellDeltaCommonBudgetPackage
import RBM1D.Gauss.APrimeFirstCellDeltaCommonNumericalBudget
import RBM1D.Gauss.APrimeFirstCellDeltaCommonWeightPlateau

/-!
# T562: actual canonical high-order coordinate moment

The exact variable-delta derivative and Minkowski consumer are combined with
the one-parameter budget package and its numerical absorption.  The output is
the actual canonical coordinate estimate only.
-/

namespace RBM.APrimeFirstCellDeltaCoordinateMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (N k : Nat) : Real :=
  APrimeFirstCellDeltaMinkowskiConsumer.endpoint N k

/-- The desired canonical order-`highOrder delta p` coordinate estimate at
one actual first-cell endpoint and output. -/
def coordinateBoundAt (tauPrime delta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) : Prop :=
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  let v := endpoint N k
  momNormW (P d)
      (APrimeFirstCellDeltaTargetWeight.canonicalWeight
        tauPrime delta P0 N k) P0
      (APrimeFirstCellDeltaMinkowskiConsumer.Y N k a v) <=
    (N : Real) ^ (delta / 5) *
      APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real))

/-- T549's literal pointwise derivative conclusion is T556's open premise,
with the same explicit `delta`, canonical weight, sample, and uncut QV. -/
theorem pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
    {tauPrime delta alpha : Real} {p N k : Nat}
    {a : LoopArg (d.L N) 2} {r : Real}
    (h : APrimeFirstCellDeltaMomFlowDerivExact.momFlowDerivBoundAt
      tauPrime delta alpha p N k a r) :
    APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt
      tauPrime delta alpha p N k a r := by
  simpa [APrimeFirstCellDeltaMomFlowDerivExact.momFlowDerivBoundAt,
    APrimeFirstCellDeltaMinkowskiConsumer.pointwiseDerivativePremiseAt,
    APrimeFirstCellDeltaMomFlowDerivExact.canonicalM,
    APrimeFirstCellDeltaMinkowskiConsumer.canonicalM,
    APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
    APrimeFirstCellDeltaMinkowskiConsumer.weight,
    APrimeFirstCellDeltaMinkowskiConsumer.Y,
    APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint,
    APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellGeneratorHle.canonicalWeight,
    APrimeFirstCellGeneratorHle.actualWeight,
    APrimeFirstCellSampleRegularity.Y,
    APrimeFirstCellSampleRegularity.G,
    APrimeFirstCellSampleRegularity.Q, d] using h

/-- Fixed-size exact T549-to-T556 Minkowski assembly. -/
theorem minkowskiBoundAt_of_momFlowDerivBoundAt
    {tauPrime delta alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hderiv : forall r, r ∈ Ioc (0 : Real)
      (APrimeFirstCellDeltaMinkowskiConsumer.endpoint N k) ->
      APrimeFirstCellDeltaMomFlowDerivExact.momFlowDerivBoundAt
        tauPrime delta alpha p N k a r) :
    APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt
      tauPrime delta alpha p N k a := by
  exact APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt_of_deriv
    hTau hDelta hAlpha hp hN hk a
    (fun r hr => pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
      (hderiv r hr))

/-- Exact fixed-size mapping of T556's Minkowski right-hand side into
T554's `totalBudget`.  The cross input is the literal `Bfull` integral and
is multiplied by exactly the consumer's outer factor `2`. -/
theorem coordinateBoundAt_of_minkowski_and_budgets
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p N k : Nat} (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hmink : APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt
      tauPrime delta (delta / 16)
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N k a)
    (hinitial : APrimeFirstCellDeltaInitialMomentBudget.initialBoundAt
      tauPrime delta (APrimeFirstCellDeltaTargetWeight.highOrder delta p)
        N k a)
    (hdrift : 2 * (∫ r in (0 : Real)..
        APrimeFirstCellDeltaDriftIntegralBudget.endpoint N k,
      APrimeFirstCellDeltaDriftIntegralBudget.A tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N k a r) <=
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
        (delta / 16) N
          (APrimeFirstCellDeltaDriftIntegralBudget.endpoint N k) +
        (N : Real) ^ (-delta))
    (hcross : (∫ r in (0 : Real)..endpoint N k,
      APrimeFirstCellDeltaFullCrossBudget.literalBfull tauPrime delta
        (delta / 16)
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N
        (endpoint N k) r) <=
      APrimeFirstCellDeltaFullCrossBudget.budgetConstant
          (APrimeFirstCellDeltaTargetWeight.highOrder delta p) *
        APrimeFirstCellDeltaFullCrossBudget.crossScale delta (delta / 16)
          N (endpoint N k))
    (hqv : Real.sqrt ((2 *
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p : Real) - 1) *
      (∫ r in (0 : Real)..APrimeFirstCellDeltaQVNormBudget.endpoint N k,
        APrimeFirstCellDeltaQVNormBudget.g tauPrime delta
          (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N k a r)) <=
      Real.sqrt (2 *
          (APrimeFirstCellDeltaTargetWeight.highOrder delta p : Real) - 1) *
        (384 * Real.sqrt 3 * (N : Real) ^ ((delta / 16) / 2) *
            APrimeFirstCellLoopCap.xRate
              (APrimeFirstCellDeltaQVNormBudget.endpoint N k) ^
                (-(2 : Real)) +
          Real.sqrt (APrimeFirstCellDeltaQVNormBudget.endpoint N k) *
            (N : Real) ^ (-delta / 2)))
    (hnum : APrimeFirstCellDeltaCommonNumericalBudget.numericalBudgetAt
      delta p N k) :
    coordinateBoundAt tauPrime delta p N k a := by
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  let v := endpoint N k
  let R := APrimeFirstCellLoopCap.xRate v
  have hP : 1 <= P0 :=
    (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  have hAlpha : 0 < delta / 16 := by positivity
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hvhalf : v <= 1 / 2 := hv.2.trans ht.2
  have hAint : IntervalIntegrable
      (APrimeFirstCellDeltaMinkowskiConsumer.A
        tauPrime delta P0 N k a) volume 0 v := by
    change IntervalIntegrable
      (APrimeFirstCellDeltaDriftIntegralBudget.A
        tauPrime delta P0 N k a) volume 0
      (APrimeFirstCellDeltaDriftIntegralBudget.endpoint N k)
    exact APrimeFirstCellDeltaDriftIntegralBudget.intervalIntegrable_A
      (delta := delta) (p := P0) hTau hN hk a
  have hBint : IntervalIntegrable
      (APrimeFirstCellDeltaMinkowskiConsumer.B
        tauPrime delta (delta / 16) P0 N k) volume 0 v := by
    unfold APrimeFirstCellDeltaMinkowskiConsumer.B
    exact (APrimeFirstCellFullCrossIntegrability.intervalIntegrable_Bfull
      hDelta.le hAlpha (by omega) hP hv.1 hvhalf
      (APrimeFirstCellDeltaFullCrossBudget.prefixRate_nonneg hv.1)
      (by unfold APrimeFirstCellCrossBadPayment.jointEnvelope; positivity)
      ENNReal.toReal_nonneg).1
  have hsplit :
      (∫ r in (0 : Real)..v,
        (APrimeFirstCellDeltaMinkowskiConsumer.A
            tauPrime delta P0 N k a r +
          APrimeFirstCellDeltaMinkowskiConsumer.B
            tauPrime delta (delta / 16) P0 N k r)) =
      (∫ r in (0 : Real)..v,
        APrimeFirstCellDeltaMinkowskiConsumer.A
          tauPrime delta P0 N k a r) +
      (∫ r in (0 : Real)..v,
        APrimeFirstCellDeltaMinkowskiConsumer.B
          tauPrime delta (delta / 16) P0 N k r) := by
    exact intervalIntegral.integral_add hAint hBint
  have hi : momNormW (P d)
      (APrimeFirstCellDeltaMinkowskiConsumer.weight
        tauPrime delta P0 N k) P0
      (APrimeFirstCellDeltaMinkowskiConsumer.initial N k a) <=
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.initialBudget
        delta N R := by
    have hi0 := hinitial
    change momNormW (P d)
        (APrimeFirstCellDeltaMinkowskiConsumer.weight
          tauPrime delta P0 N k) P0
        (APrimeFirstCellDeltaMinkowskiConsumer.initial N k a) <=
      (N : Real) ^ (5 * delta / 32) * R ^ (-(2 : Real)) at hi0
    simpa [APrimeFirstCellDeltaCoordinateBudgetArithmetic.initialBudget]
      using hi0
  have hd : 2 * (∫ r in (0 : Real)..v,
      APrimeFirstCellDeltaMinkowskiConsumer.A
        tauPrime delta P0 N k a r) <=
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.driftBudget
        delta N R := by
    have hd0 := hdrift
    change 2 * (∫ r in (0 : Real)..v,
        APrimeFirstCellDeltaMinkowskiConsumer.A
          tauPrime delta P0 N k a r) <=
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
          (delta / 16) N v + (N : Real) ^ (-delta) at hd0
    simpa [APrimeFirstCellDeltaCoordinateBudgetArithmetic.driftBudget,
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.absorbedRateAt,
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.alpha,
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.beta,
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate]
      using hd0
  have hc : 2 * (∫ r in (0 : Real)..v,
      APrimeFirstCellDeltaMinkowskiConsumer.B
        tauPrime delta (delta / 16) P0 N k r) <=
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.literalCrossIntegralBudget
        delta P0 N R := by
    unfold APrimeFirstCellDeltaMinkowskiConsumer.B
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.literalCrossIntegralBudget
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.alpha
    have hc2 : 2 * (∫ r in (0 : Real)..v,
        APrimeFirstCellDeltaFullCrossBudget.literalBfull tauPrime delta
          (delta / 16) P0 N v r) <=
        2 * (APrimeFirstCellDeltaFullCrossBudget.budgetConstant P0 *
          APrimeFirstCellDeltaFullCrossBudget.crossScale
            delta (delta / 16) N v) :=
      mul_le_mul_of_nonneg_left hcross (by norm_num)
    calc
      2 * (∫ r in (0 : Real)..v,
          APrimeFirstCellDeltaFullCrossBudget.literalBfull tauPrime delta
            (delta / 16) P0 N v r) <=
          2 * (APrimeFirstCellDeltaFullCrossBudget.budgetConstant P0 *
            APrimeFirstCellDeltaFullCrossBudget.crossScale
              delta (delta / 16) N v) := hc2
      _ = 2 * APrimeFirstCellDeltaFullCrossBudget.budgetConstant P0 *
          (N : Real) ^ (delta / 16 - 2 * delta) *
          R ^ (-(2 : Real)) := by
        unfold APrimeFirstCellDeltaFullCrossBudget.crossScale
        ring
  have hq : Real.sqrt ((2 * (P0 : Real) - 1) *
      (∫ r in (0 : Real)..v,
        APrimeFirstCellDeltaMinkowskiConsumer.g
          tauPrime delta P0 N k a r)) <=
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.qvSqrtBudget
        delta P0 N R v := by
    have hq0 := hqv
    change Real.sqrt ((2 * (P0 : Real) - 1) *
        (∫ r in (0 : Real)..v,
          APrimeFirstCellDeltaMinkowskiConsumer.g
            tauPrime delta P0 N k a r)) <=
      Real.sqrt (2 * (P0 : Real) - 1) *
        (384 * Real.sqrt 3 * (N : Real) ^ ((delta / 16) / 2) *
            R ^ (-(2 : Real)) +
          Real.sqrt v * (N : Real) ^ (-delta / 2)) at hq0
    simpa [
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.qvSqrtBudget,
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.alpha,
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.beta] using hq0
  have hrhs : momNormW (P d)
      (APrimeFirstCellDeltaMinkowskiConsumer.weight
        tauPrime delta P0 N k) P0
      (APrimeFirstCellDeltaMinkowskiConsumer.Y N k a v) <=
      APrimeFirstCellDeltaCoordinateBudgetArithmetic.totalBudget
        delta P0 N R v := by
    unfold APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt at hmink
    change momNormW (P d)
        (APrimeFirstCellDeltaMinkowskiConsumer.weight
          tauPrime delta P0 N k) P0
        (APrimeFirstCellDeltaMinkowskiConsumer.Y N k a v) <= _ at hmink
    calc
      _ <= momNormW (P d)
            (APrimeFirstCellDeltaMinkowskiConsumer.weight
              tauPrime delta P0 N k) P0
            (APrimeFirstCellDeltaMinkowskiConsumer.initial N k a) +
          2 * (∫ r in (0 : Real)..v,
            (APrimeFirstCellDeltaMinkowskiConsumer.A
                tauPrime delta P0 N k a r +
              APrimeFirstCellDeltaMinkowskiConsumer.B
                tauPrime delta (delta / 16) P0 N k r)) +
          Real.sqrt ((2 * (P0 : Real) - 1) *
            ∫ r in (0 : Real)..v,
              APrimeFirstCellDeltaMinkowskiConsumer.g
                tauPrime delta P0 N k a r) := hmink
      _ = momNormW (P d)
            (APrimeFirstCellDeltaMinkowskiConsumer.weight
              tauPrime delta P0 N k) P0
            (APrimeFirstCellDeltaMinkowskiConsumer.initial N k a) +
          2 * (∫ r in (0 : Real)..v,
            APrimeFirstCellDeltaMinkowskiConsumer.A
              tauPrime delta P0 N k a r) +
          2 * (∫ r in (0 : Real)..v,
            APrimeFirstCellDeltaMinkowskiConsumer.B
              tauPrime delta (delta / 16) P0 N k r) +
          Real.sqrt ((2 * (P0 : Real) - 1) *
            ∫ r in (0 : Real)..v,
              APrimeFirstCellDeltaMinkowskiConsumer.g
                tauPrime delta P0 N k a r) := by rw [hsplit]; ring
      _ <= APrimeFirstCellDeltaCoordinateBudgetArithmetic.initialBudget
            delta N R +
          APrimeFirstCellDeltaCoordinateBudgetArithmetic.driftBudget
            delta N R +
          APrimeFirstCellDeltaCoordinateBudgetArithmetic.literalCrossIntegralBudget
            delta P0 N R +
          APrimeFirstCellDeltaCoordinateBudgetArithmetic.qvSqrtBudget
            delta P0 N R v := by linarith
      _ = APrimeFirstCellDeltaCoordinateBudgetArithmetic.totalBudget
            delta P0 N R v := rfl
  have hnum' : APrimeFirstCellDeltaCoordinateBudgetArithmetic.totalBudget
      delta P0 N R v <=
      (N : Real) ^ (delta / 5) * R ^ (-(2 : Real)) := by
    simpa [APrimeFirstCellDeltaCommonNumericalBudget.numericalBudgetAt,
      APrimeFirstCellDeltaCommonNumericalBudget.endpoint,
      APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
      R, v, endpoint, P0] using hnum
  have hfinal := hrhs.trans hnum'
  simpa [coordinateBoundAt,
    APrimeFirstCellDeltaTargetWeight.canonicalWeight,
    APrimeFirstCellCanonicalPlateau.canonicalWeight,
    APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellGeneratorHle.canonicalWeight,
    APrimeFirstCellGeneratorHle.actualWeight,
    APrimeFirstCellDeltaMinkowskiConsumer.weight,
    APrimeFirstCellDeltaMinkowskiConsumer.canonicalM,
    P0, v, R, endpoint, d] using hfinal

/-- Canonical coordinate bounds for every positive active first-cell index. -/
def actualCoordinateMoments (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    forall a : LoopArg (d.L N) 2,
      coordinateBoundAt tauPrime delta p N k a

/-- The exact empty-prefix coordinate package. -/
def kZeroCoordinateMoments (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ forall a : LoopArg (d.L N) 2,
      coordinateBoundAt tauPrime delta p N 0 a

/-- A same-event positive `k=2` package carrying only geometry, the two
weight-one plateaux, and the proved coordinate bound. -/
def positiveTwoCoordinateMomentPackage
    (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      let v := endpoint N 2
      0 < v ∧
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      v <= 1 / 2 ∧
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 2 omega = 1 ∧
      APrimeFirstCellDeltaTargetWeight.canonicalWeight
        tauPrime delta P0 N 2 omega = 1 ∧
      forall a : LoopArg (d.L N) 2,
        coordinateBoundAt tauPrime delta p N 2 a

/-- The T555 active budgets and T558 numerical absorption close every
positive active coordinate after T549 and T556 supply exact Minkowski. -/
theorem actualCoordinateMoments_of_common
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) (hDelta100 : delta <= 1 / 100)
    {p : Nat} (hp : 1 <= p)
    (hactive : APrimeFirstCellDeltaCommonBudgetPackage.activeBudgets
      tauPrime delta p)
    (hnum : APrimeFirstCellDeltaCommonNumericalBudget.actualNumericalBudgets
      tauPrime delta p) :
    actualCoordinateMoments tauPrime delta p := by
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  have hP : 1 <= P0 :=
    (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  have hAlpha : 0 < delta / 16 := by positivity
  dsimp only [APrimeFirstCellDeltaCommonBudgetPackage.activeBudgets] at hactive
  obtain ⟨hcross, _hqvNorm, _hqvIntegral, _hqvSqrt,
    hqvExplicit, hdrift, hinitial⟩ := hactive
  have hderiv :=
    APrimeFirstCellDeltaMomFlowDerivExact.eventually_momFlowDerivBoundAt
      hTau hDelta hDelta100 hAlpha P0 hP
  filter_upwards [hderiv, hcross, hqvExplicit, hdrift, hinitial, hnum,
    eventually_ge_atTop 1]
      with N hderivN hcrossN hqvN hdriftN hinitialN hnumN hN
  intro k hk1 hk a
  have hmink : APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt
      tauPrime delta (delta / 16) P0 N k a := by
    apply minkowskiBoundAt_of_momFlowDerivBoundAt
      hTau hDelta hAlpha hP hN hk a
    intro r hr
    exact hderivN k hk1 hk a r (by
      simpa [APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
        APrimeFirstCellSampleRegularity.endpoint,
        APrimeFirstCellGeneratorHle.endpoint] using hr)
  exact coordinateBoundAt_of_minkowski_and_budgets
    hTau hDelta hp hN hk a hmink
    (hinitialN k hk a) (hdriftN k hk1 hk a).2
    (hcrossN k hk).1 (hqvN k hk1 hk a) (hnumN k hk)

/-- Exact empty-prefix coordinate estimate from T555's zero components and
T558's zero numerical absorption. -/
theorem kZeroCoordinateMoments_of_common
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 <= p)
    (hactive : APrimeFirstCellDeltaCommonBudgetPackage.activeBudgets
      tauPrime delta p)
    (hzero : APrimeFirstCellDeltaCommonBudgetPackage.exactZeroBudgets
      tauPrime delta p)
    (hnum : APrimeFirstCellDeltaCommonNumericalBudget.kZeroNumericalBudget
      delta p) :
    kZeroCoordinateMoments tauPrime delta p := by
  let P0 := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  have hP : 1 <= P0 :=
    (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  dsimp only [APrimeFirstCellDeltaCommonBudgetPackage.activeBudgets] at hactive
  obtain ⟨_hcrossActive, _hqvNorm, _hqvIntegral, _hqvSqrt,
    _hqvExplicit, _hdriftActive, hinitialActive⟩ := hactive
  dsimp only [APrimeFirstCellDeltaCommonBudgetPackage.exactZeroBudgets] at hzero
  obtain ⟨hcrossZero, hqvZero, hdriftZero, _hinitialZero⟩ := hzero
  filter_upwards [hinitialActive, hdriftZero, hnum,
    eventually_ge_atTop 1]
      with N hinitialN hdriftN hnumN hN
  refine ⟨by simp [endpoint, APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
    cutNetPt_zero], ?_⟩
  intro a
  have hmink :=
    (APrimeFirstCellDeltaMinkowskiConsumer.minkowskiBoundAt_k_zero
      tauPrime delta (delta / 16) P0 N a).2
  have hdrift : 2 * (∫ r in (0 : Real)..
        APrimeFirstCellDeltaDriftIntegralBudget.endpoint N 0,
      APrimeFirstCellDeltaDriftIntegralBudget.A tauPrime delta
        P0 N 0 a r) <=
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
        (delta / 16) N
          (APrimeFirstCellDeltaDriftIntegralBudget.endpoint N 0) +
        (N : Real) ^ (-delta) := by
    have hz := (hdriftN a).2
    rw [hz]
    have hrate : 0 <=
        APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
          (delta / 16) N
            (APrimeFirstCellDeltaDriftIntegralBudget.endpoint N 0) := by
      have hx : 0 <= APrimeFirstCellLoopCap.xRate
          (APrimeFirstCellDeltaDriftIntegralBudget.endpoint N 0) := by
        rw [show APrimeFirstCellDeltaDriftIntegralBudget.endpoint N 0 = 0 by
          simp [APrimeFirstCellDeltaDriftIntegralBudget.endpoint,
            APrimeFirstCellSampleRegularity.endpoint,
            APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero]]
        norm_num [APrimeFirstCellLoopCap.xRate, etaT, mE_zero]
      unfold APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
            (add_nonneg (Real.sqrt_nonneg 2) zero_le_one))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _))
        (Real.rpow_nonneg hx _)
    simpa only [mul_zero] using
      add_nonneg hrate (Real.rpow_nonneg (Nat.cast_nonneg N) (-delta))
  have hcross : (∫ r in (0 : Real)..endpoint N 0,
      APrimeFirstCellDeltaFullCrossBudget.literalBfull tauPrime delta
        (delta / 16) P0 N (endpoint N 0) r) <=
      APrimeFirstCellDeltaFullCrossBudget.budgetConstant P0 *
        APrimeFirstCellDeltaFullCrossBudget.crossScale delta (delta / 16)
          N (endpoint N 0) := by
    have hz := (hcrossZero N).1
    change (∫ r in (0 : Real)..endpoint N 0,
      APrimeFirstCellDeltaFullCrossBudget.literalBfull tauPrime delta
        (delta / 16) P0 N (endpoint N 0) r) = 0 at hz
    rw [hz]
    exact mul_nonneg
      (APrimeFirstCellDeltaFullCrossBudget.budgetConstant_nonneg P0)
      (APrimeFirstCellDeltaFullCrossBudget.crossScale_nonneg (by
        simp [endpoint, APrimeFirstCellDeltaMinkowskiConsumer.endpoint,
          cutNetPt_zero]))
  have hqv : Real.sqrt ((2 * (P0 : Real) - 1) *
      (∫ r in (0 : Real)..APrimeFirstCellDeltaQVNormBudget.endpoint N 0,
        APrimeFirstCellDeltaQVNormBudget.g tauPrime delta P0 N 0 a r)) <=
      Real.sqrt (2 * (P0 : Real) - 1) *
        (384 * Real.sqrt 3 * (N : Real) ^ ((delta / 16) / 2) *
            APrimeFirstCellLoopCap.xRate
              (APrimeFirstCellDeltaQVNormBudget.endpoint N 0) ^
                (-(2 : Real)) +
          Real.sqrt (APrimeFirstCellDeltaQVNormBudget.endpoint N 0) *
            (N : Real) ^ (-delta / 2)) := by
    rw [(hqvZero N a).2.2]
    rw [APrimeFirstCellDeltaQVNormBudget.endpoint_zero]
    simp only [Real.sqrt_zero, zero_mul, add_zero]
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (Real.rpow_nonneg (by
        norm_num [APrimeFirstCellLoopCap.xRate, etaT, mE_zero]) _)
  exact coordinateBoundAt_of_minkowski_and_budgets
    hTau hDelta hp hN (Nat.zero_le _) a hmink
    (hinitialN 0 (Nat.zero_le _) a) hdrift hcross hqv hnumN.2

/-- T559 contributes only the positive geometry and two weight-one facts;
the coordinate estimate is the uniform deterministic conclusion above. -/
theorem positiveTwoCoordinateMomentPackage_of_plateau
    {tauPrime delta : Real} {p : Nat}
    (hplateau :
      APrimeFirstCellDeltaCommonWeightPlateau.positiveCommonWeightPlateau
        tauPrime delta p)
    (hcoords : actualCoordinateMoments tauPrime delta p) :
    positiveTwoCoordinateMomentPackage tauPrime delta p := by
  filter_upwards [hplateau, hcoords] with N hplateauN hcoordsN
  obtain ⟨omega, homega, hvpos, hk, hvhalf, htarget, hcanonical⟩ :=
    hplateauN
  refine ⟨omega, homega, ?_, hk, ?_, htarget, ?_, ?_⟩
  · simpa [endpoint, APrimeFirstCellDeltaMinkowskiConsumer.endpoint]
      using hvpos
  · simpa [endpoint, APrimeFirstCellDeltaMinkowskiConsumer.endpoint]
      using hvhalf
  · simpa [APrimeFirstCellDeltaTargetWeight.canonicalWeight]
      using hcanonical
  · exact hcoordsN 2 (by norm_num) hk

/-- Closed actual coordinate package using exactly T555's one `tauPrime`. -/
theorem exists_coordinateMomentPackage :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall delta : Real, 0 < delta -> delta <= 1 / 100 ->
      forall p : Nat, 1 <= p ->
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        actualCoordinateMoments tauPrime delta p ∧
        kZeroCoordinateMoments tauPrime delta p ∧
        positiveTwoCoordinateMomentPackage tauPrime delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCommonBudgetPackage.exists_commonBudgetPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  have hpackage := hall delta hDelta hDelta100 p hp
  dsimp only at hpackage
  obtain ⟨hmeas, hprob, _hP, hactive, hzero, hgeometry⟩ := hpackage
  have hnum :=
    APrimeFirstCellDeltaCommonNumericalBudget.eventually_actualNumericalBudgets
      hTau hDelta hp
  have hnumZero :=
    APrimeFirstCellDeltaCommonNumericalBudget.eventually_kZeroNumericalBudget
      hTau hDelta hp
  have hcoords := actualCoordinateMoments_of_common
    hTau hDelta hDelta100 hp hactive hnum
  have hkzero := kZeroCoordinateMoments_of_common
    hTau hDelta hp hactive hzero hnumZero
  have hplateau :=
    APrimeFirstCellDeltaCommonWeightPlateau.positiveCommonWeightPlateau_of_geometry
      hTau hDelta p hgeometry
  exact ⟨hmeas, hprob, hcoords, hkzero,
    positiveTwoCoordinateMomentPackage_of_plateau hplateau hcoords⟩

end

end RBM.APrimeFirstCellDeltaCoordinateMoment

namespace RBM.APrimeFirstCellDeltaCoordinateMoment

#print axioms pointwiseDerivativePremiseAt_of_momFlowDerivBoundAt
#print axioms minkowskiBoundAt_of_momFlowDerivBoundAt
#print axioms coordinateBoundAt_of_minkowski_and_budgets
#print axioms actualCoordinateMoments_of_common
#print axioms kZeroCoordinateMoments_of_common
#print axioms positiveTwoCoordinateMomentPackage_of_plateau
#print axioms exists_coordinateMomentPackage

end RBM.APrimeFirstCellDeltaCoordinateMoment
