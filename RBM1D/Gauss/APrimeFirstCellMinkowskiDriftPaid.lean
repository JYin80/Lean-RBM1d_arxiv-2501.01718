/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellMinkowskiExact
import RBM1D.Gauss.APrimeFirstCellDriftIntegralBudget

/-!
# T502: actual first-cell Minkowski estimate with the drift integral paid

The exact T494 Minkowski inequality is combined with T498's canonical-weight
drift integral budget.  The literal full-cross and uncut quadratic-variation
integrals remain unchanged.
-/

namespace RBM.APrimeFirstCellMinkowskiDriftPaid

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real :=
  APrimeFirstCellDriftIntegralBudget.delta

noncomputable abbrev endpoint (N k : Nat) : Real :=
  APrimeFirstCellMinkowskiExact.endpoint N k

noncomputable abbrev weight (tauPrime : Real) (p N k : Nat) : Ω d -> Real :=
  APrimeFirstCellMinkowskiExact.weight tauPrime p N k

noncomputable abbrev Y (N k : Nat) (a : LoopArg (d.L N) 2)
    (r : Real) : Ω d -> Real :=
  APrimeFirstCellMinkowskiExact.Y N k a r

noncomputable abbrev A (tauPrime : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  APrimeFirstCellMinkowskiExact.A tauPrime p N k a r

noncomputable abbrev B (tauPrime alpha : Real) (p N k : Nat)
    (r : Real) : Real :=
  APrimeFirstCellMinkowskiExact.B tauPrime alpha p N k r

noncomputable abbrev g (tauPrime : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  APrimeFirstCellMinkowskiExact.g tauPrime p N k a r

noncomputable abbrev initial (N k : Nat)
    (a : LoopArg (d.L N) 2) : Ω d -> Real :=
  APrimeFirstCellMinkowskiExact.initial N k a

/-- The exact T494 estimate after paying only its doubled drift integral. -/
def minkowskiDriftPaidAt (tauPrime alpha beta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight tauPrime p N k) p (Y N k a (endpoint N k)) <=
    momNormW (P d) (weight tauPrime p N k) p (initial N k a) +
      APrimeFirstCellDriftCoefficientAbsorbed.absorbedRate
        alpha N (endpoint N k) +
      (N : Real) ^ (-beta) +
      2 * (∫ r in (0 : Real)..endpoint N k,
        B tauPrime alpha p N k r) +
      Real.sqrt ((2 * (p : Real) - 1) *
        ∫ r in (0 : Real)..endpoint N k, g tauPrime p N k a r)

theorem absorbedRate_nonneg {alpha v : Real} {N : Nat} (hv1 : v < 1) :
    0 <= APrimeFirstCellDriftCoefficientAbsorbed.absorbedRate alpha N v := by
  have hxRate : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos
      (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  unfold APrimeFirstCellDriftCoefficientAbsorbed.absorbedRate
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
        (by positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (Real.rpow_nonneg hxRate.le _)

/-- Public integrability of the literal T494 full-cross rate at one active
first-cell endpoint. -/
theorem intervalIntegrable_B
    {tauPrime alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha)
    (hp : 1 <= p) (hN : 1 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    IntervalIntegrable (B tauPrime alpha p N k) volume 0 (endpoint N k) := by
  let v := endpoint N k
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  unfold B APrimeFirstCellMinkowskiExact.B
  unfold APrimeFirstCellFullCrossBudget.literalBfull
  exact (APrimeFirstCellFullCrossIntegrability.intervalIntegrable_Bfull
    APrimeFirstCellFarRowAbsorb.delta_pos.le hAlpha hN hp hv.1
    (hv.2.trans ht.2)
    (APrimeFirstCellFullCrossBudget.prefixRate_nonneg hv.1)
    (by
      unfold APrimeFirstCellCrossBadPayment.jointEnvelope
      positivity)
    ENNReal.toReal_nonneg).1

/-- Fixed-size substitution of T498's drift payment into T494. -/
theorem minkowskiDriftPaidAt_of_bounds
    {tauPrime alpha beta : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha)
    (hp : 1 <= p) (hN : 1 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hmink : APrimeFirstCellMinkowskiExact.minkowskiBoundAt
      tauPrime alpha p N k a)
    (hdrift :
      2 * (∫ r in (0 : Real)..endpoint N k,
        A tauPrime p N k a r) <=
        APrimeFirstCellDriftCoefficientAbsorbed.absorbedRate
          alpha N (endpoint N k) + (N : Real) ^ (-beta)) :
    minkowskiDriftPaidAt tauPrime alpha beta p N k a := by
  have hAint : IntervalIntegrable (A tauPrime p N k a) volume
      0 (endpoint N k) :=
    APrimeFirstCellDriftIntegralBudget.intervalIntegrable_A
      hTau (by omega) hk a
  have hBint : IntervalIntegrable (B tauPrime alpha p N k) volume
      0 (endpoint N k) :=
    intervalIntegrable_B hTau hAlpha hp hN hk
  unfold minkowskiDriftPaidAt
  unfold APrimeFirstCellMinkowskiExact.minkowskiBoundAt at hmink
  rw [intervalIntegral.integral_add hAint hBint] at hmink
  nlinarith

/-- The fixed moment order and both drift exponents precede the eventual
matrix size. -/
def actualMinkowskiDriftPaid
    (tauPrime alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      minkowskiDriftPaidAt tauPrime alpha beta p N k a

theorem actualMinkowskiDriftPaid_of_bounds
    {tauPrime alpha beta : Real} {p : Nat}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha) (hp : 1 <= p)
    (hmink : APrimeFirstCellMinkowskiExact.actualMinkowskiBound
      tauPrime alpha p)
    (hbudget : APrimeFirstCellDriftIntegralBudget.actualDriftIntegralBudget
      tauPrime alpha beta p) :
    actualMinkowskiDriftPaid tauPrime alpha beta p := by
  filter_upwards [hmink, hbudget, eventually_ge_atTop 1] with
    N hminkN hbudgetN hN
  intro k hk1 hk a
  exact minkowskiDriftPaidAt_of_bounds hTau hAlpha hp hN hk a
    (hminkN k hk1 hk a) (hbudgetN k hk1 hk a).2

theorem eventually_minkowskiDriftPaid
    {tauPrime alpha beta : Real}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha)
    (p : Nat) (hp : 1 <= p)
    (hbudget : APrimeFirstCellDriftIntegralBudget.actualDriftIntegralBudget
      tauPrime alpha beta p) :
    actualMinkowskiDriftPaid tauPrime alpha beta p :=
  actualMinkowskiDriftPaid_of_bounds hTau hAlpha hp
    (APrimeFirstCellMinkowskiExact.eventually_minkowskiBoundAt
      hTau hAlpha p hp) hbudget

/-- The zero mesh index is a separate exact zero-time branch. -/
theorem minkowskiDriftPaidAt_k_zero
    (tauPrime alpha beta : Real) (p N : Nat)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧
      minkowskiDriftPaidAt tauPrime alpha beta p N 0 a := by
  have hv : APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 := by
    simp [APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero]
  have hY0 : Y N 0 a 0 = initial N 0 a := by
    exact APrimeFirstCellMinkowskiExact.Y_zero_eq_initial a
      (by rw [hv]) (by rw [hv]; norm_num)
  have hrate : 0 <=
      APrimeFirstCellDriftCoefficientAbsorbed.absorbedRate alpha N 0 :=
    absorbedRate_nonneg (by norm_num)
  have herr : 0 <= (N : Real) ^ (-beta) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  constructor
  · exact hv
  · unfold minkowskiDriftPaidAt
    simp only [endpoint, APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero]
    rw [hY0]
    simp only [intervalIntegral.integral_same, mul_zero, Real.sqrt_zero,
      add_zero]
    nlinarith

def kZeroMinkowskiDriftPaid
    (tauPrime alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧
      minkowskiDriftPaidAt tauPrime alpha beta p N 0 a

theorem eventually_kZeroMinkowskiDriftPaid
    (tauPrime alpha beta : Real) (p : Nat) :
    kZeroMinkowskiDriftPaid tauPrime alpha beta p :=
  Filter.Eventually.of_forall fun N a =>
    minkowskiDriftPaidAt_k_zero tauPrime alpha beta p N a

/-- A positive `k = 2` resident on T498's same literal sharp event. -/
def positiveTwoMinkowskiDriftPaidResident
    (tauPrime alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    let v := endpoint N 2
    0 < v ∧ v <= firstCellT tauPrime N ∧
    ∀ a : LoopArg (d.L N) 2,
      minkowskiDriftPaidAt tauPrime alpha beta p N 2 a

theorem positiveTwoMinkowskiDriftPaidResident_of_inputs
    {tauPrime alpha beta : Real} {p : Nat}
    (hresident :
      APrimeFirstCellDriftIntegralBudget.positiveTwoDriftIntegralResident
        tauPrime alpha beta p)
    (hpaid : actualMinkowskiDriftPaid tauPrime alpha beta p) :
    positiveTwoMinkowskiDriftPaidResident tauPrime alpha beta p := by
  filter_upwards [hresident, hpaid] with N hresidentN hpaidN
  obtain ⟨omega, homega, hk, hvpos, hvle, _hbudget⟩ := hresidentN
  refine ⟨omega, homega, hk, hvpos, hvle, ?_⟩
  intro a
  exact hpaidN 2 (by norm_num) hk a

/-- Closed T502 package.  It retains T498's one measurable high-probability
event and adds only the deterministic T494/T498 substitution. -/
theorem exists_minkowskiDriftPaid_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ alpha : Real, 0 < alpha ->
      ∀ p : Nat, 1 <= p ->
      ∀ beta : Real, 0 < beta ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualMinkowskiDriftPaid tauPrime alpha beta p ∧
        kZeroMinkowskiDriftPaid tauPrime alpha beta p ∧
        positiveTwoMinkowskiDriftPaidResident tauPrime alpha beta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDriftIntegralBudget.exists_actualDriftIntegralBudget_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro alpha hAlpha p hp beta hBeta
  obtain ⟨hmeas, hprob, hbudget, _hkzero, hresident⟩ :=
    hall alpha hAlpha p hp beta hBeta
  have hpaid := eventually_minkowskiDriftPaid
    hTau hAlpha p hp hbudget
  exact ⟨hmeas, hprob, hpaid,
    eventually_kZeroMinkowskiDriftPaid tauPrime alpha beta p,
    positiveTwoMinkowskiDriftPaidResident_of_inputs hresident hpaid⟩

end

end RBM.APrimeFirstCellMinkowskiDriftPaid

namespace RBM.APrimeFirstCellMinkowskiDriftPaid

#print axioms absorbedRate_nonneg
#print axioms intervalIntegrable_B
#print axioms minkowskiDriftPaidAt_of_bounds
#print axioms actualMinkowskiDriftPaid_of_bounds
#print axioms eventually_minkowskiDriftPaid
#print axioms minkowskiDriftPaidAt_k_zero
#print axioms positiveTwoMinkowskiDriftPaidResident_of_inputs
#print axioms exists_minkowskiDriftPaid_with_resident

end RBM.APrimeFirstCellMinkowskiDriftPaid
