/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormBadIntegralAllOrders

/-!
# T1207: integrated norm-good reduction of the general-moving cross budget

For each fixed moment order, integrating T1201's pointwise full-budget
reduction leaves the exact T1201 norm-good integral plus the evaluated
inverse-square-root payment. This theorem does not estimate the norm-good
integral.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetGoodIntegralReduction

open Filter MeasureTheory Set Gauss CutHypTheta
open APrimeGeneralMovingCrossBudgetTimeIntegrable
open APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
open APrimeGeneralMovingCrossBudgetGoodReduction

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- For each fixed `p ≥ 1`, one eventual cutoff works uniformly over active
target-mesh cells and outputs. The integral of the full positive-time cross
budget is at most the integral of T1201's literal norm-good restriction plus
the exact integral of its accepted norm-bad payment. -/
theorem eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        (∫ r in (s N)..(cutNetPt s (mesh D) N k),
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r) ≤
          (∫ r in (s N)..(cutNetPt s (mesh D) N k),
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a r) +
            (15 * (p : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
              (√(cutNetPt s (mesh D) N k) - √(s N)) := by
  have hfull :=
    eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hgood :=
    eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hpoint :=
    eventually_positiveTimeCrossBudget_le_normGood_add_normBad
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hfull, hgood, hpoint, eventually_ge_atTop 1]
    with N hfullN hgoodN hpointN hN
  have hNpos : 0 < N := by omega
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  let K : ℝ := (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ))
  let payment : ℝ → ℝ := fun r => K / √r
  have hwindow : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hwindow.1
  have hpaymentInt : IntervalIntegrable payment volume (s N) v := by
    simpa [payment] using
      APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
        K (s N) v (hs0 N) hsv
  have hpointwise :
      ∀ r ∈ Icc (s N) v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r ≤
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r + payment r := by
    intro r hr
    have hr0 : 0 ≤ r := (hs0 N).trans hr.1
    by_cases hrpos : 0 < r
    · have h := hpointN k hk a r hr hrpos
      change
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r ≤
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r + payment r
      simpa [payment, K] using h
    · have hrEq : r = 0 := le_antisymm (le_of_not_gt hrpos) hr0
      have hfull0 :
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r = 0 := by
        simp [APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget,
          hrEq]
      have hgood0 :
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r = 0 := by
        simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget,
          hrEq]
      have hpayment0 : payment r = 0 := by simp [payment, hrEq]
      rw [hfull0, hgood0, hpayment0]
      norm_num
  have hsumInt :
      IntervalIntegrable
        (fun r =>
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a r + payment r)
        volume (s N) v :=
    (hgoodN k hk a).add hpaymentInt
  have hmono := intervalIntegral.integral_mono_on hsv
    (hfullN k hk a) hsumInt hpointwise
  have hpaymentEval :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      K (s N) v (hs0 N) hsv
  calc
    (∫ r in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a r) ≤
        ∫ r in (s N)..v,
          (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a r + payment r) := hmono
    _ = (∫ r in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a r) +
          ∫ r in (s N)..v, payment r :=
      intervalIntegral.integral_add (hgoodN k hk a) hpaymentInt
    _ = (∫ r in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a r) +
          (15 * (p : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
            (√v - √(s N)) := by
      rw [hpaymentEval]
      dsimp [K]
      ring

/-! T1185's explicit active `k=2`, positive-time transition witness records
that the inherited model hypotheses and cell domain are jointly satisfiable. -/

noncomputable abbrev nondegenerate_active_k2_witness :=
  APrimeGeneralMovingCrossBudgetNormBadIntegralAllOrders.nondegenerate_active_k2_witness

#print axioms eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
#print axioms nondegenerate_active_k2_witness

end
end RBM.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
