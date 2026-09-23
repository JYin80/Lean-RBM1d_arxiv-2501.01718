/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaDriftCoefficientAbsorbed

/-!
# T546: variable-delta first-cell canonical drift integral budget

The accepted pointwise absorbed drift norm is integrated for the exact
variable-`delta` canonical drift norm needed by a later Minkowski consumer.
-/

namespace RBM.APrimeFirstCellDeltaDriftIntegralBudget

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev endpoint (N k : Nat) : Real :=
  APrimeFirstCellSampleRegularity.endpoint N k

noncomputable abbrev A (tauPrime delta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  momNormW (P d)
    (APrimeFirstCellSampleRegularity.weight tauPrime delta p N k) p
    (APrimeFirstCellSampleRegularity.G N k a r)

/-- Fixed-size time integrability of the variable-`delta` canonical drift norm. -/
theorem intervalIntegrable_A
    {tauPrime delta : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable (A tauPrime delta p N k a) volume 0 (endpoint N k) := by
  let v := endpoint N k
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  let w := APrimeFirstCellSampleRegularity.weight tauPrime delta p N k
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
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
      (APrimeSmoothWeightActual.weightD d 0 60
        delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k m) := by
    dsimp only [w, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight, m]
    exact APrimeSmoothWeightActual.weightC1 d (E := 0) (D := 60)
      (δ := delta) (s := fun _ => 0)
      (t := firstCellT tauPrime)
      (mesh := APrimeSmoothTransition.transitionMesh) (N₀ := 2)
      (p := p) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)
      (by norm_num) (by norm_num) hN hm hu
  have hw0 : ∀ omega, 0 <= w omega := by
    intro omega
    dsimp only [w, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight, m]
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60
      delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega
  have hw1 : ∀ omega, w omega <= 1 := by
    intro omega
    dsimp only [w, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight, m]
    exact APrimeSmoothWeightActual.weight_le_one d 0 60
      delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega
  unfold A APrimeFirstCellSampleRegularity.G
  exact APrimeDriftTimeFamily.intervalIntegrable_momNormW_driftAt
    d 0 60 N Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
    w hwC1.cont.measurable hw0 hw1 p

/-- Integrate one fixed-size pointwise absorbed drift bound, and then use
the first-cell length `v <= 1/2` to remove the factor `2v`. -/
theorem integral_A_le_of_norm
    {tauPrime delta alpha beta : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hN : 1 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hnorm : ∀ r ∈ Icc (0 : Real) (endpoint N k),
      A tauPrime delta p N k a r <=
        APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
          alpha N (endpoint N k) + (N : Real) ^ (-beta)) :
    (∫ r in (0 : Real)..endpoint N k, A tauPrime delta p N k a r) <=
        endpoint N k *
          (APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
            alpha N (endpoint N k) + (N : Real) ^ (-beta)) ∧
      2 * (∫ r in (0 : Real)..endpoint N k, A tauPrime delta p N k a r) <=
        APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
          alpha N (endpoint N k) + (N : Real) ^ (-beta) := by
  let v := endpoint N k
  let C := APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate alpha N v +
    (N : Real) ^ (-beta)
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hvhalf : v <= 1 / 2 := hv.2.trans ht.2
  have hint : IntervalIntegrable (A tauPrime delta p N k a) volume 0 v := by
    exact intervalIntegrable_A hTau (by omega) hk a
  have hI : (∫ r in (0 : Real)..v, A tauPrime delta p N k a r) <= v * C := by
    have hmono := intervalIntegral.integral_mono_on hv.1 hint
      intervalIntegrable_const hnorm
    calc
      (∫ r in (0 : Real)..v, A tauPrime delta p N k a r) <=
          v * APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate alpha N v +
            v * (N : Real) ^ (-beta) := by
        simpa [v, intervalIntegral.integral_const, smul_eq_mul] using hmono
      _ = v * C := by unfold C; ring
  have hrate0 : 0 <=
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate alpha N v := by
    have hxRate : 0 < APrimeFirstCellLoopCap.xRate v := by
      unfold APrimeFirstCellLoopCap.xRate
      exact div_pos
        (Step2.etaT_pos' (by norm_num) (by norm_num))
        (Step2.etaT_pos' (by norm_num) (hvhalf.trans_lt (by norm_num)))
    unfold APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
          (by positivity))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (Real.rpow_nonneg hxRate.le _)
  have hC0 : 0 <= C := by
    exact add_nonneg hrate0 (Real.rpow_nonneg (by positivity) _)
  constructor
  · simpa [v, C] using hI
  · calc
      2 * (∫ r in (0 : Real)..v, A tauPrime delta p N k a r)
          <= 2 * (v * C) := mul_le_mul_of_nonneg_left hI (by norm_num)
      _ = (2 * v) * C := by ring
      _ <= 1 * C := mul_le_mul_of_nonneg_right (by linarith) hC0
      _ = C := one_mul C

/-- The exact eventual drift-integral budget used in the first-cell
Minkowski right-hand side. -/
def actualDriftIntegralBudget
    (tauPrime delta alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      (∫ r in (0 : Real)..endpoint N k, A tauPrime delta p N k a r) <=
          endpoint N k *
            (APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
              alpha N (endpoint N k) + (N : Real) ^ (-beta)) ∧
        2 * (∫ r in (0 : Real)..endpoint N k, A tauPrime delta p N k a r) <=
          APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
            alpha N (endpoint N k) + (N : Real) ^ (-beta)

theorem actualDriftIntegralBudget_of_norm
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hTau : 0 < tauPrime)
    (hnorm : APrimeFirstCellDeltaDriftCoefficientAbsorbed.actualDriftNormAbsorbed
      tauPrime delta alpha beta p) :
    actualDriftIntegralBudget tauPrime delta alpha beta p := by
  filter_upwards [hnorm, eventually_ge_atTop 1] with N hnormN hN
  intro k hk1 hk a
  apply integral_A_le_of_norm hTau hN hk a
  intro r hr
  have h := hnormN k hk1 hk r hr a
  simpa only [A, endpoint] using h

/-- At `k = 0`, the exact T494 drift integral is over the zero interval. -/
theorem integral_A_k_zero (tauPrime delta : Real) (p N : Nat)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧
      (∫ r in (0 : Real)..endpoint N 0, A tauPrime delta p N 0 a r) = 0 := by
  have hv : endpoint N 0 = 0 := by
    simp [endpoint, APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero]
  exact ⟨hv, by rw [hv, intervalIntegral.integral_same]⟩

def kZeroDriftIntegralBudget (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧
      (∫ r in (0 : Real)..endpoint N 0, A tauPrime delta p N 0 a r) = 0

theorem eventually_kZeroDriftIntegralBudget
    (tauPrime delta : Real) (p : Nat) :
    kZeroDriftIntegralBudget tauPrime delta p :=
  Filter.Eventually.of_forall fun N a => integral_A_k_zero tauPrime delta p N a

/-- A positive `k = 2` resident on the same literal sharp event as T541.
Its weight-one field remains the support weight at smoothing order `m = N`. -/
def positiveTwoDriftIntegralResident
    (tauPrime delta alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    APrimeSupportRunning.weight delta (firstCellT tauPrime)
      2 p N 2 N omega = 1 ∧
    let v := endpoint N 2
    0 < v ∧ v <= firstCellT tauPrime N ∧
    ∀ a : LoopArg (d.L N) 2,
      (∫ r in (0 : Real)..v, A tauPrime delta p N 2 a r) <=
          v * (APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
            alpha N v + (N : Real) ^ (-beta)) ∧
        2 * (∫ r in (0 : Real)..v, A tauPrime delta p N 2 a r) <=
          APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate
            alpha N v + (N : Real) ^ (-beta)

theorem positiveTwoDriftIntegralResident_of_inputs
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hresident :
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.positiveActualDriftAbsorbedResident
        tauPrime delta alpha beta p)
    (hbudget : actualDriftIntegralBudget tauPrime delta alpha beta p) :
    positiveTwoDriftIntegralResident tauPrime delta alpha beta p := by
  filter_upwards [hresident, hbudget] with N hresidentN hbudgetN
  obtain ⟨omega, homega, hk, hweight, hvpos, hvle, _hvhalf, _hnorm⟩ :=
    hresidentN
  refine ⟨omega, homega, hk, hweight, hvpos, hvle, ?_⟩
  intro a
  exact hbudgetN 2 (by norm_num) hk a

/-- Closed T546 package.  Integration is deterministic and retains T541's
one literal sharp common event and its probability proof. -/
theorem exists_actualDriftIntegralBudget_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ alpha : Real, 0 < alpha ->
      ∀ p : Nat, 1 <= p ->
      ∀ beta : Real, 0 < beta ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualDriftIntegralBudget tauPrime delta alpha beta p ∧
        kZeroDriftIntegralBudget tauPrime delta p ∧
        positiveTwoDriftIntegralResident tauPrime delta alpha beta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaDriftCoefficientAbsorbed.exists_actualDriftNormAbsorbed_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 alpha hAlpha p hp beta hBeta
  obtain ⟨hmeas, hprob, hnorm, _hcoefficient, _hkzero, hresident⟩ :=
    hall delta hDelta hDelta100 alpha hAlpha p hp beta hBeta
  have hbudget := actualDriftIntegralBudget_of_norm hTau hnorm
  exact ⟨hmeas, hprob, hbudget,
    eventually_kZeroDriftIntegralBudget tauPrime delta p,
    positiveTwoDriftIntegralResident_of_inputs hresident hbudget⟩

end

end RBM.APrimeFirstCellDeltaDriftIntegralBudget

namespace RBM.APrimeFirstCellDeltaDriftIntegralBudget

#print axioms endpoint
#print axioms A
#print axioms intervalIntegrable_A
#print axioms integral_A_le_of_norm
#print axioms actualDriftIntegralBudget
#print axioms actualDriftIntegralBudget_of_norm
#print axioms integral_A_k_zero
#print axioms kZeroDriftIntegralBudget
#print axioms eventually_kZeroDriftIntegralBudget
#print axioms positiveTwoDriftIntegralResident
#print axioms positiveTwoDriftIntegralResident_of_inputs
#print axioms exists_actualDriftIntegralBudget_with_resident

end RBM.APrimeFirstCellDeltaDriftIntegralBudget
