/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyLowMomentSameWeight
import RBM1D.Gauss.APrimeFirstCellCanonicalPlateau

/-!
# T543: variable-delta same-weight Lyapunov wrappers

For a fixed bootstrap exponent `delta` and fixed orders `1 <= p <= P`, the
actual first-cell family maximum at order `p` is bounded by its order-`P`
moment under the identical delta-dependent canonical weight and the identical
Gaussian probability measure.  This module supplies only the analytic
same-weight comparison; it assumes and proves no high-order family estimate.
-/

namespace RBM.APrimeFirstCellDeltaSameWeightLyapunov

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The order-`P` canonical first-cell weight with the bootstrap exponent left
explicit. -/
noncomputable def canonicalHighWeight (tauPrime delta : Real)
    (P N k : Nat) : Ω d -> Real :=
  APrimeFirstCellSampleRegularity.weight tauPrime delta P N k

/-- Continuity of the literal delta-dependent canonical high-order weight. -/
theorem continuous_highWeight {tauPrime delta : Real}
    (htauPrime : 0 < tauPrime) {P N k : Nat} (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Continuous (canonicalHighWeight tauPrime delta P N k) := by
  have hm : 1 <= canonicalM tauPrime N :=
    APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjactive : j <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N := by
      omega
    have ht := APrimeSupportRunning.firstT_bounds htauPrime N
    have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjactive)
    exact hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  unfold canonicalHighWeight APrimeFirstCellSampleRegularity.weight
    APrimeFirstCellGeneratorHle.canonicalWeight
    APrimeFirstCellGeneratorHle.actualWeight
  exact APrimeSmoothWeightActual.continuous_weight d
    (E := 0) (D := 60) (δ := delta) (s := fun _ => 0)
    (t := firstCellT tauPrime) (mesh := APrimeSmoothTransition.transitionMesh)
    (N₀ := 2) (p := P) (N := N) (k := k) (m := canonicalM tauPrime N)
    (by norm_num) (by norm_num) hN hm hu

/-- All three integrability hypotheses for weighted Lyapunov hold for the
actual family maximum and the same order-`P` canonical weight. -/
theorem sameWeight_integrability {tauPrime delta : Real}
    (htauPrime : 0 < tauPrime) {p P N k : Nat}
    (hP : 1 <= P) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega => canonicalHighWeight tauPrime delta P N k omega *
      |familyMax N k omega| ^ (2 * p)) (Gauss.P d) ∧
    Integrable (fun omega => canonicalHighWeight tauPrime delta P N k omega *
      |familyMax N k omega| ^ (2 * P)) (Gauss.P d) ∧
    Integrable (fun omega =>
      |canonicalHighWeight tauPrime delta P N k omega ^
          (((2 * P : Nat) : Real)⁻¹) * familyMax N k omega| ^ (2 * p))
      (Gauss.P d) := by
  have hw0 : ∀ omega, 0 <= canonicalHighWeight tauPrime delta P N k omega :=
    fun omega => APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega
  have hw1 : ∀ omega, canonicalHighWeight tauPrime delta P N k omega <= 1 :=
    fun omega => APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega
  have hwc := continuous_highWeight htauPrime hN hk (P := P) (delta := delta)
  have hfc :=
    APrimeFirstCellFamilyLowMomentSameWeight.continuous_familyMax htauPrime hk
  have hi :=
    APrimeFirstCellFamilyLowMomentSameWeight.integrable_familyMax_pow htauPrime hk p
  have hlo : Integrable
      (fun omega => canonicalHighWeight tauPrime delta P N k omega *
        |familyMax N k omega| ^ (2 * p)) (Gauss.P d) := by
    apply hi.mono' (hwc.mul (hfc.abs.pow (2 * p))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun omega => by
      change ‖canonicalHighWeight tauPrime delta P N k omega *
        |familyMax N k omega| ^ (2 * p)‖ <= |familyMax N k omega| ^ (2 * p)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw0 omega) (by positivity))]
      exact mul_le_of_le_one_left (by positivity) (hw1 omega)
  have hhi : Integrable
      (fun omega => canonicalHighWeight tauPrime delta P N k omega *
        |familyMax N k omega| ^ (2 * P)) (Gauss.P d) := by
    exact APrimeFirstCellFamilyHighMoment.integrable_weighted_finsetMax_pow
      (Gauss.P d) (canonicalHighWeight tauPrime delta P N k)
      (fun a => Y N k a (endpoint N k)) (2 * P) hw0 (fun a => by
        exact
          (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
            (δ := delta) htauPrime hP hN hk a).2.hYi)
  refine ⟨hlo, hhi, ?_⟩
  have hroot : Continuous (fun omega => canonicalHighWeight tauPrime delta P N k omega ^
      (((2 * P : Nat) : Real)⁻¹)) :=
    hwc.rpow_const (fun _ => Or.inr (by positivity))
  apply hi.mono' ((hroot.mul hfc).abs.pow (2 * p)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun omega => by
    change ‖|canonicalHighWeight tauPrime delta P N k omega ^
      (((2 * P : Nat) : Real)⁻¹) * familyMax N k omega| ^ (2 * p)‖ <=
        |familyMax N k omega| ^ (2 * p)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (hw0 omega) _)]
    apply pow_le_pow_left₀
      (mul_nonneg (Real.rpow_nonneg (hw0 omega) _) (abs_nonneg _))
    exact mul_le_of_le_one_left (abs_nonneg _)
      (Real.rpow_le_one (hw0 omega) (hw1 omega) (by positivity))

/-- Coefficient-one Lyapunov lowering under the identical measure and the
identical delta-dependent canonical weight. -/
theorem sameWeight_momNormW_le {tauPrime delta : Real}
    (htauPrime : 0 < tauPrime) {p P N k : Nat}
    (hp : 1 <= p) (hpP : p <= P) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    momNormW (Gauss.P d) (canonicalHighWeight tauPrime delta P N k) p
        (familyMax N k) <=
      momNormW (Gauss.P d) (canonicalHighWeight tauPrime delta P N k) P
        (familyMax N k) := by
  obtain ⟨hlo, hhi, hzlo⟩ :=
    sameWeight_integrability htauPrime (hp.trans hpP) hN hk
      (p := p) (delta := delta)
  exact APrimeInit.momNormW_le_momNormW_of_exponent_le hp hpP
    (fun omega => APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega)
    (fun omega => APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega) hlo hhi hzlo

/-- Fixed `delta`, `p`, and `P` precede the size threshold, which is uniform
over every active first-cell index, including `k = 0`. -/
theorem eventually_sameWeight_momNormW_le (tauPrime delta : Real)
    (htauPrime : 0 < tauPrime) (p P : Nat) (hp : 1 <= p) (hpP : p <= P) :
    ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      momNormW (Gauss.P d) (canonicalHighWeight tauPrime delta P N k) p
          (familyMax N k) <=
        momNormW (Gauss.P d) (canonicalHighWeight tauPrime delta P N k) P
          (familyMax N k) := by
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  intro k hk
  exact sameWeight_momNormW_le htauPrime hp hpP (by omega) hk

/-- At the empty prefix the delta-dependent canonical high-order weight is
exactly one, for every sample and every size. -/
theorem canonicalHighWeight_k_zero (tauPrime delta : Real) (P N : Nat)
    (omega : Ω d) : canonicalHighWeight tauPrime delta P N 0 omega = 1 := by
  simpa only [canonicalHighWeight, APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellCanonicalPlateau.canonicalWeight] using
    (APrimeFirstCellCanonicalPlateau.canonicalWeight_k_zero
      tauPrime delta P N omega)

/-- The exact `k = 0` endpoint, its weight-one identity, and the same-weight
coefficient-one comparison are retained together. -/
theorem eventually_kZero_sameWeight_momNormW_le (tauPrime delta : Real)
    (htauPrime : 0 < tauPrime) (p P : Nat) (hp : 1 <= p) (hpP : p <= P) :
    ∀ᶠ N : Nat in atTop,
      endpoint N 0 = 0 ∧
      (∀ omega : Ω d, canonicalHighWeight tauPrime delta P N 0 omega = 1) ∧
      momNormW (Gauss.P d) (canonicalHighWeight tauPrime delta P N 0) p
          (familyMax N 0) <=
        momNormW (Gauss.P d) (canonicalHighWeight tauPrime delta P N 0) P
          (familyMax N 0) := by
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  refine ⟨by simp [endpoint, cutNetPt_zero],
    canonicalHighWeight_k_zero tauPrime delta P N, ?_⟩
  exact sameWeight_momNormW_le htauPrime hp hpP (by omega) (Nat.zero_le _)

#print axioms continuous_highWeight
#print axioms sameWeight_integrability
#print axioms sameWeight_momNormW_le
#print axioms eventually_sameWeight_momNormW_le
#print axioms canonicalHighWeight_k_zero
#print axioms eventually_kZero_sameWeight_momNormW_le

end

end RBM.APrimeFirstCellDeltaSameWeightLyapunov
