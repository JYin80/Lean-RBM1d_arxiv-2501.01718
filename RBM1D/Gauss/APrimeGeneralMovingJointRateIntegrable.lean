/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingJointGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingJointMeasurable
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1035: uniform fixed-order integrability of the literal joint rate

The all-sample polynomial envelope passes through the literal strict
transition indicator.  Together with the canonical general-moving
measurability theorem, this gives the `hZi` input required by
`crossPart_active_le_jointEvent`, uniformly over active target-mesh prefixes
and running times.  No joint-event membership is assumed.
-/

namespace RBM.APrimeGeneralMovingJointRateIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- A polynomial bound on the indicated joint rate follows directly from
T617's all-sample product bound, since the indicator is either one or zero. -/
private theorem jointRate_le_envelope
    {E D c : ℝ} {s t : ℕ → ℝ} {deltaWeight : ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ sigma : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ u ∈ Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      ∀ ω : Ω d,
        APrimeCrossJointSplit.jointRate d E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N)
          sigma a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u ω ≤
          APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
  have hpoly :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  filter_upwards [hpoly] with N hN
  intro k hk sigma a u hu omega
  have h := hN k hk sigma a u hu omega
  by_cases htrans : omega ∈ APrimeCrossJointSplit.transition d E D
      deltaWeight s (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
  · rw [APrimeCrossJointSplit.jointRate,
      Set.indicator_of_mem htrans]
    exact h
  · rw [APrimeCrossJointSplit.jointRate,
      Set.indicator_of_notMem htrans]
    exact APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N

/-- For each fixed integer `p ≥ 1`, the exact literal `jointRate` power in
`crossPart_active_le_jointEvent` is integrable, uniformly for every active
prefix (including zero) and every running time in its closed cell.  All
arguments retain the same target mesh, canonical smoothing order, and sample. -/
theorem eventually_integrable_jointRate_pow
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (_hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ sigma : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ u ∈ Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      Integrable (fun ω =>
        |APrimeCrossJointSplit.jointRate d E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N)
          sigma a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u ω| ^
            (2 * p)) (Gauss.P d) := by
  have hbound := jointRate_le_envelope hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hpos := eventually_ge_atTop 1
  filter_upwards [hbound, hpos] with N hboundN hN
  have hNpos : 0 < N := by omega
  have hN' : 1 ≤ N := by omega
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  intro k hk sigma a u hu
  have hmeas :=
    APrimeGeneralMovingJointMeasurable.measurable_prefixGradient_and_jointRate
      (deltaWeight := deltaWeight) hE hs0 hst ht1 hNpos hk sigma a hu
  have hrateMeas := (continuous_abs.measurable.comp hmeas.2).pow_const (2 * p)
  have hrateNonneg := APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
    (APrimeGeneralMovingMesh.targetMesh D) N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    sigma a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u hNpos
  have hrateBound := hboundN k hk sigma a u hu
  let C := APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p)
  have hC : 0 ≤ C := by
    unfold C APrimeGeneralMovingJointGlobalPoly.jointEnvelope
    positivity
  apply Integrable.of_bound hrateMeas.aestronglyMeasurable C
  filter_upwards [] with omega
  change ‖|APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      sigma a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u omega| ^
        (2 * p)‖ ≤ C
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (abs_nonneg _) _),
    abs_of_nonneg (hrateNonneg omega)]
  dsimp [C]
  exact pow_le_pow_left₀ (hrateNonneg omega) (hrateBound omega) (2 * p)

/-! The positive-cell witness from T995 remains a separate nondegeneracy
context.  It witnesses the scheduled common-event/positive-weight geometry;
it does not assert membership in the strict transition set. -/

noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_integrable_jointRate_pow
#print axioms t995_positive_cell_witness

end
end RBM.APrimeGeneralMovingJointRateIntegrable
