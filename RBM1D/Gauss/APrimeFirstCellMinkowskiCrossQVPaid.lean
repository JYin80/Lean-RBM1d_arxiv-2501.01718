/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellMinkowskiDriftPaid
import RBM1D.Gauss.APrimeFirstCellCrossQVCombinedBudget

/-!
# T506: actual first-cell Minkowski estimate with drift, cross, and QV paid

T502 pays the exact drift integral in T494's canonical-weight Minkowski
estimate.  T499 pays the remaining literal full-cross and uncut QV sum.
This module combines them and unfolds the two deterministic scale rates.
-/

namespace RBM.APrimeFirstCellMinkowskiCrossQVPaid

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real :=
  APrimeFirstCellMinkowskiDriftPaid.delta

noncomputable abbrev endpoint (N k : Nat) : Real :=
  APrimeFirstCellMinkowskiExact.endpoint N k

noncomputable abbrev weight (tauPrime : Real) (p N k : Nat) : Ω d -> Real :=
  APrimeFirstCellMinkowskiExact.weight tauPrime p N k

noncomputable abbrev Y (N k : Nat) (a : LoopArg (d.L N) 2)
    (r : Real) : Ω d -> Real :=
  APrimeFirstCellMinkowskiExact.Y N k a r

noncomputable abbrev initial (N k : Nat)
    (a : LoopArg (d.L N) 2) : Ω d -> Real :=
  APrimeFirstCellMinkowskiExact.initial N k a

/-- T502 and T499 use the same literal sharp-event parameter. -/
theorem delta_eq_cross :
    delta = APrimeFirstCellCrossQVCombinedBudget.delta := by
  simpa [delta, APrimeFirstCellMinkowskiDriftPaid.delta,
    APrimeFirstCellCrossQVCombinedBudget.delta] using
    APrimeFirstCellDriftIntegralBudget.minkowski_delta_eq_fixedDelta.symm

/-- T494's exact Minkowski inequality after all three integral contributions
have been paid, while the initial moment remains literal. -/
def minkowskiCrossQVPaidAt
    (tauPrime alpha beta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight tauPrime p N k) p (Y N k a (endpoint N k)) <=
    momNormW (P d) (weight tauPrime p N k) p (initial N k a) +
      APrimeFirstCellDriftCoefficient.coefficientConstant *
        (Real.sqrt 2 + 1) * (N : Real) ^ (2 * alpha) *
          APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : Real)) +
      (N : Real) ^ (-beta) +
      2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
        (N : Real) ^ (alpha - 2 * APrimeFirstCellFullCrossBudget.delta) *
          APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : Real)) +
      Real.sqrt (2 * (p : Real) - 1) *
        (384 * Real.sqrt 3 * (N : Real) ^ (alpha / 2) *
            APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : Real)) +
          Real.sqrt (endpoint N k) * (N : Real) ^ (-beta / 2))

/-- Fixed-size substitution of T499's combined cross/QV budget into T502. -/
theorem minkowskiCrossQVPaidAt_of_bounds
    {tauPrime alpha beta : Real} {p N k : Nat}
    (a : LoopArg (d.L N) 2)
    (hpaid : APrimeFirstCellMinkowskiDriftPaid.minkowskiDriftPaidAt
      tauPrime alpha beta p N k a)
    (hcombined : APrimeFirstCellCrossQVCombinedBudget.combinedBudgetAt
      tauPrime alpha beta p N k a) :
    minkowskiCrossQVPaidAt tauPrime alpha beta p N k a := by
  unfold APrimeFirstCellMinkowskiDriftPaid.minkowskiDriftPaidAt at hpaid
  rw [APrimeFirstCellDriftCoefficientAbsorbed.absorbedRate_eq_paperRate]
    at hpaid
  unfold APrimeFirstCellCrossQVCombinedBudget.combinedBudgetAt at hcombined
  unfold APrimeFirstCellFullCrossBudget.crossScale at hcombined
  unfold minkowskiCrossQVPaidAt
  nlinarith

/-- The moment order and both exponents precede the eventual matrix size. -/
def actualMinkowskiCrossQVPaid
    (tauPrime alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      minkowskiCrossQVPaidAt tauPrime alpha beta p N k a

theorem actualMinkowskiCrossQVPaid_of_bounds
    {tauPrime alpha beta : Real} {p : Nat}
    (hpaid : APrimeFirstCellMinkowskiDriftPaid.actualMinkowskiDriftPaid
      tauPrime alpha beta p)
    (hcombined : APrimeFirstCellCrossQVCombinedBudget.actualCrossQVCombinedBudget
      tauPrime alpha beta p) :
    actualMinkowskiCrossQVPaid tauPrime alpha beta p := by
  filter_upwards [hpaid, hcombined] with N hpaidN hcombinedN
  intro k hk1 hk a
  exact minkowskiCrossQVPaidAt_of_bounds a
    (hpaidN k hk1 hk a) (hcombinedN k hk1 hk a)

/-- The empty prefix is kept as a separate exact zero-cell branch. -/
theorem minkowskiCrossQVPaidAt_k_zero
    (tauPrime alpha beta : Real) (p N : Nat)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧
      minkowskiCrossQVPaidAt tauPrime alpha beta p N 0 a := by
  have hpaid :=
    (APrimeFirstCellMinkowskiDriftPaid.minkowskiDriftPaidAt_k_zero
      tauPrime alpha beta p N a).2
  have hcombined :=
    APrimeFirstCellCrossQVCombinedBudget.combinedBudgetAt_k_zero
      tauPrime alpha beta p N a
  exact ⟨by
    simp [endpoint, APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero],
    minkowskiCrossQVPaidAt_of_bounds a hpaid hcombined⟩

def kZeroMinkowskiCrossQVPaid
    (tauPrime alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧
      minkowskiCrossQVPaidAt tauPrime alpha beta p N 0 a

theorem eventually_kZeroMinkowskiCrossQVPaid
    (tauPrime alpha beta : Real) (p : Nat) :
    kZeroMinkowskiCrossQVPaid tauPrime alpha beta p :=
  Filter.Eventually.of_forall fun N a =>
    minkowskiCrossQVPaidAt_k_zero tauPrime alpha beta p N a

/-- A positive `k = 2` resident on the same literal sharp event. -/
def positiveTwoMinkowskiCrossQVPaidResident
    (tauPrime alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    let v := endpoint N 2
    0 < v ∧ v <= firstCellT tauPrime N ∧
    ∀ a : LoopArg (d.L N) 2,
      minkowskiCrossQVPaidAt tauPrime alpha beta p N 2 a

theorem positiveTwoMinkowskiCrossQVPaidResident_of_inputs
    {tauPrime alpha beta : Real} {p : Nat}
    (hresident :
      APrimeFirstCellMinkowskiDriftPaid.positiveTwoMinkowskiDriftPaidResident
        tauPrime alpha beta p)
    (hpaid : actualMinkowskiCrossQVPaid tauPrime alpha beta p) :
    positiveTwoMinkowskiCrossQVPaidResident tauPrime alpha beta p := by
  filter_upwards [hresident, hpaid] with N hresidentN hpaidN
  obtain ⟨omega, homega, hk, hvpos, hvle, _h502⟩ := hresidentN
  refine ⟨omega, homega, hk, hvpos, hvle, ?_⟩
  intro a
  exact hpaidN 2 (by norm_num) hk a

theorem eventually_sharpCommonEvent_nonempty
    {tauPrime alpha beta : Real} {p : Nat}
    (hresident : positiveTwoMinkowskiCrossQVPaidResident
      tauPrime alpha beta p) :
    ∀ᶠ N : Nat in atTop,
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N).Nonempty := by
  filter_upwards [hresident] with N hN
  obtain ⟨omega, homega, _⟩ := hN
  exact ⟨omega, homega⟩

/-- Closed T506 package with the same measurable high-probability event,
the empty prefix, event nonemptiness, and a positive `k = 2` resident. -/
theorem exists_minkowskiCrossQVPaid_with_resident :
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
        actualMinkowskiCrossQVPaid tauPrime alpha beta p ∧
        kZeroMinkowskiCrossQVPaid tauPrime alpha beta p ∧
        (∀ᶠ N : Nat in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N).Nonempty) ∧
        positiveTwoMinkowskiCrossQVPaidResident
          tauPrime alpha beta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellMinkowskiDriftPaid.exists_minkowskiDriftPaid_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro alpha hAlpha p hp beta hBeta
  obtain ⟨hmeas, hprob, h502, _hkzero, hresident⟩ :=
    hall alpha hAlpha p hp beta hBeta
  have hprobCross : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime
        APrimeFirstCellCrossQVCombinedBudget.delta alpha) := by
    rw [← delta_eq_cross]
    exact hprob
  have h499 :=
    APrimeFirstCellCrossQVCombinedBudget.eventually_combinedBudgetAt_of_highProb
      hTau hAlpha hBeta p hp hprobCross
  have hpaid := actualMinkowskiCrossQVPaid_of_bounds h502 h499
  have htwo :=
    positiveTwoMinkowskiCrossQVPaidResident_of_inputs hresident hpaid
  exact ⟨hmeas, hprob, hpaid,
    eventually_kZeroMinkowskiCrossQVPaid tauPrime alpha beta p,
    eventually_sharpCommonEvent_nonempty htwo, htwo⟩

end

end RBM.APrimeFirstCellMinkowskiCrossQVPaid

namespace RBM.APrimeFirstCellMinkowskiCrossQVPaid

#print axioms delta_eq_cross
#print axioms minkowskiCrossQVPaidAt_of_bounds
#print axioms actualMinkowskiCrossQVPaid_of_bounds
#print axioms minkowskiCrossQVPaidAt_k_zero
#print axioms eventually_kZeroMinkowskiCrossQVPaid
#print axioms positiveTwoMinkowskiCrossQVPaidResident_of_inputs
#print axioms eventually_sharpCommonEvent_nonempty
#print axioms exists_minkowskiCrossQVPaid_with_resident

end RBM.APrimeFirstCellMinkowskiCrossQVPaid
