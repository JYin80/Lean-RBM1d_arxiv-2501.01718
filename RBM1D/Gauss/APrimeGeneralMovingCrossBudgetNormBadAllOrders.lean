/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormBad
import RBM1D.Gauss.APrimeGeneralMovingJointRateNormBadAllOrders

/-!
# T1195: all fixed positive-order norm-bad cross-budget component

This module combines the accepted all-orders bad-event moment payment with
the exact p-dependent coefficient in T1089.  It estimates only the named
norm-bad component at a fixed positive running time.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetNormBadAllOrders

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T1089's exact p-dependent coefficient applied to the T1185 norm-bad
restriction of the literal general-moving joint rate. -/
noncomputable def normBadCrossBudgetAllOrders (E D deltaWeight : ℝ)
    (s t : ℕ → ℝ) (N k p : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
    (4 * (p : ℝ) * √r) *
      MomentDuhamel.momNorm (Gauss.P d) (2 * p)
        (APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
          E D deltaWeight s t N k a r)

/-- T1035's exact fixed-order integrability producer passes to the full-space
power of the T1185 bad-event indicator, uniformly over active cells and their
closed-cell running times. -/
theorem eventually_integrable_normBadJointRate_pow
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
      ∀ r ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        Integrable
          (fun ω =>
            |APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
              E D deltaWeight s t N k a r ω| ^ (2 * p))
          (Gauss.P d) := by
  have hraw :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hraw, eventually_ge_atTop 1] with N hrawN hN
  intro k hk a r hr
  let Z : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω
  let Bbad : Set (Gauss.Ω d) :=
    (APrimeGeneralMovingGoodMesh.good N)ᶜ
  let Zbad : Gauss.Ω d → ℝ := Bbad.indicator Z
  have hNpos : 0 < N := by omega
  have hRawInt : Integrable (fun ω => |Z ω| ^ (2 * p)) (Gauss.P d) := by
    simpa [Z, mesh] using hrawN k hk Step2.sigPM a r hr
  have hBbad : MeasurableSet Bbad := by
    exact (APrimeGeneralMovingGoodMesh.measurableSet_good N).compl
  have hpow : ∀ ω, |Zbad ω| ^ (2 * p) =
      Bbad.indicator (fun ω => |Z ω| ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ Bbad
    · simp [Zbad, hω]
    · have hq : 2 * p ≠ 0 := by omega
      simp [Zbad, hω, hq]
  have hBadInt : Integrable (fun ω => |Zbad ω| ^ (2 * p)) (Gauss.P d) := by
    refine (hRawInt.indicator hBbad).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    exact (hpow ω).symm
  simpa [Bbad, Zbad, Z, mesh,
    APrimeGeneralMovingGoodMesh.good,
    APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate] using hBadInt

/-- For every fixed integer p≥1, one eventual cutoff works uniformly over
all active general-moving target-mesh cells, outputs, and positive running
times in the closed cell.  The bound is exactly the p-dependent norm-bad
component of T1089, with the bad restriction and Gaussian moment norm inherited
from T1185. -/
theorem eventually_normBad_crossBudget_allOrders_le
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
      ∀ r ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        0 < r →
          normBadCrossBudgetAllOrders E D deltaWeight s t N k p a r ≤
            (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by
  have hmoment :=
    APrimeGeneralMovingJointRateNormBadAllOrders.eventually_jointRate_pow_integral_normBad_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hintegrable := eventually_integrable_normBadJointRate_pow
    hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hmoment, hintegrable, eventually_ge_atTop 1]
    with N hmomentN hintegrableN hN
  intro k hk a r hr hr0
  let Z : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω
  let Bbad : Set (Gauss.Ω d) :=
    (APrimeGeneralMovingGoodMesh.good N)ᶜ
  let Zbad : Gauss.Ω d → ℝ := Bbad.indicator Z
  have hNpos : 0 < N := by omega
  have hq : 2 * p ≠ 0 := by omega
  have hBbad : MeasurableSet Bbad := by
    exact (APrimeGeneralMovingGoodMesh.measurableSet_good N).compl
  have hpow : ∀ ω, |Zbad ω| ^ (2 * p) =
      Bbad.indicator (fun ω => |Z ω| ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ Bbad
    · simp [Zbad, hω]
    · simp [Zbad, hω, hq]
  have hIntegral :
      (∫ ω, |Zbad ω| ^ (2 * p) ∂(Gauss.P d)) =
        ∫ ω in Bbad, |Z ω| ^ (2 * p) ∂(Gauss.P d) := by
    rw [← integral_indicator hBbad]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hpow ω
  have hBadMoment :
      ∫ ω in Bbad, |Z ω| ^ (2 * p) ∂(Gauss.P d) ≤
        (N : ℝ) ^ (-(2 * (p : ℝ))) := by
    have h := hmomentN k hk Step2.sigPM a r hr
    simpa [Bbad, Z, mesh, APrimeGeneralMovingGoodMesh.good,
      APrimeGeneralMovingJointRateNormBadAllOrders.normGood] using h
  have hMomPow :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ^ (2 * p) =
        ∫ ω in Bbad, |Z ω| ^ (2 * p) ∂(Gauss.P d) := by
    rw [MomentDuhamel.momNorm_pow (Gauss.P d) hq Zbad, hIntegral]
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hRootPow :
      ((N : ℝ) ^ (-(1 : ℝ))) ^ (2 * p) =
        (N : ℝ) ^ (-(2 * (p : ℝ))) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 : ℝ))) (2 * p),
      ← Real.rpow_mul hNposR.le]
    congr 1
    push_cast
    ring
  have hMomPowBound :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ^ (2 * p) ≤
        ((N : ℝ) ^ (-(1 : ℝ))) ^ (2 * p) := by
    rw [hMomPow, hRootPow]
    exact hBadMoment
  have hnorm :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ≤
        (N : ℝ) ^ (-(1 : ℝ)) :=
    (pow_le_pow_iff_left₀
      (MomentDuhamel.momNorm_nonneg (Gauss.P d) (2 * p) Zbad)
      (by positivity) hq).mp hMomPowBound
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp))
  have hrS : √r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr0)
  have hcoeff :
      APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r) =
        (15 * (p : ℝ) / 8) / √r := by
    unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
    push_cast
    field_simp [hpR, hrS]
    ring
  have hcoeff0 :
      0 ≤ APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r) := by
    rw [hcoeff]
    positivity
  calc
    normBadCrossBudgetAllOrders E D deltaWeight s t N k p a r =
        ((15 * (p : ℝ) / 8) / √r) *
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad := by
      unfold normBadCrossBudgetAllOrders
      change
        (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r)) *
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad = _
      rw [hcoeff]
    _ ≤ ((15 * (p : ℝ) / 8) / √r) * (N : ℝ) ^ (-(1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by ring

/-! T1185's explicit active k=2 first-cell witness shows that the retained
hypotheses have a nondegenerate realization with positive running time and a
sample in the exact strict transition event. -/

noncomputable abbrev nondegenerate_active_k2_witness :=
  APrimeGeneralMovingCrossBudgetNormBad.nondegenerate_active_k2_witness

#print axioms eventually_integrable_normBadJointRate_pow
#print axioms eventually_normBad_crossBudget_allOrders_le
#print axioms nondegenerate_active_k2_witness

end
end RBM.APrimeGeneralMovingCrossBudgetNormBadAllOrders
