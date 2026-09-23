/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaTargetWeight
import RBM1D.Gauss.APrimeFirstCellDeltaSameWeightLyapunov

/-!
# T550: variable-delta target/canonical family-weight transfer

For the explicit high order from T542, this module compares the order-`p`
family norm under the target weight with the same norm under the canonical
weight, then applies T543's same-weight Lyapunov inequality.  Both steps keep
coefficient one and the Gaussian measure unchanged.
-/

namespace RBM.APrimeFirstCellDeltaFamilyWeightTransfer

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The variable-delta target weight is measurable under the same Gaussian
measure used by every family norm below. -/
theorem targetWeight_aestronglyMeasurable
    (tauPrime delta : ℝ) (p N k : ℕ) :
    AEStronglyMeasurable
      (APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k) (Gauss.P d) := by
  exact APrimeWeight.widenedW_meas
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh
    (fun N u => APrimeSlotFields.measurable_jSnorm
      (sample d) 0 60 (fun _ => 0) N u)
    p delta N k

theorem targetWeight_nonneg (tauPrime delta : ℝ) (p N k : ℕ)
    (omega : Ω d) :
    0 ≤ APrimeFirstCellDeltaTargetWeight.targetWeight
      tauPrime delta p N k omega := by
  exact APrimeWeight.widenedW_nonneg
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh delta p N k omega

theorem targetWeight_le_one (tauPrime delta : ℝ) (p N k : ℕ)
    (omega : Ω d) :
    APrimeFirstCellDeltaTargetWeight.targetWeight
      tauPrime delta p N k omega ≤ 1 := by
  exact APrimeWeight.widenedW_le_one
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh delta p N k omega

/-- Honest integrability of the target-weight order-`p` family integrand. -/
theorem integrable_targetWeight_familyMax_pow {tauPrime delta : ℝ}
    (hTau : 0 < tauPrime) {p N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega =>
      APrimeFirstCellDeltaTargetWeight.targetWeight
          tauPrime delta p N k omega *
        |familyMax N k omega| ^ (2 * p)) (Gauss.P d) := by
  have hi :=
    APrimeFirstCellFamilyLowMomentSameWeight.integrable_familyMax_pow
      hTau hk p
  have hwmeas := targetWeight_aestronglyMeasurable
    tauPrime delta p N k
  have hMmeas : AEStronglyMeasurable
      (fun omega => |familyMax N k omega| ^ (2 * p)) (Gauss.P d) :=
    (APrimeFirstCellFamilyLowMomentSameWeight.continuous_familyMax
      hTau hk).abs.pow (2 * p) |>.aestronglyMeasurable
  apply hi.mono' (hwmeas.mul hMmeas)
  exact Filter.Eventually.of_forall fun omega => by
    change ‖APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k omega *
      |familyMax N k omega| ^ (2 * p)‖ ≤
        |familyMax N k omega| ^ (2 * p)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (targetWeight_nonneg tauPrime delta p N k omega)
        (by positivity))]
    exact mul_le_of_le_one_left (by positivity)
      (targetWeight_le_one tauPrime delta p N k omega)

/-- Increasing a nonnegative weight at a fixed positive order increases the
weighted moment norm with coefficient one. -/
theorem momNormW_mono_weight {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {w W Y : Omega → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hw0 : ∀ omega, 0 ≤ w omega)
    (hwW : ∀ omega, w omega ≤ W omega)
    (hWint : Integrable (fun omega => W omega * |Y omega| ^ (2 * p)) mu) :
    momNormW mu w p Y ≤ momNormW mu W p Y := by
  unfold momNormW
  apply Real.rpow_le_rpow
    (integral_nonneg fun omega => mul_nonneg (hw0 omega) (by positivity))
  · exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega =>
        mul_nonneg (hw0 omega) (pow_nonneg (abs_nonneg _) _))
      hWint
      (Filter.Eventually.of_forall fun omega =>
        mul_le_mul_of_nonneg_right (hwW omega)
          (pow_nonneg (abs_nonneg _) _))
  · have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (show 0 < p by omega)
    positivity

/-- All target and canonical integrands used by the two coefficient-one
comparisons are integrable under exactly `Gauss.P d`. -/
theorem familyWeightTransfer_integrability
    {tauPrime delta : ℝ} (hTau : 0 < tauPrime)
    {p N k : ℕ} (hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    let P := APrimeFirstCellDeltaTargetWeight.highOrder delta p
    Integrable (fun omega =>
      APrimeFirstCellDeltaTargetWeight.targetWeight
          tauPrime delta p N k omega *
        |familyMax N k omega| ^ (2 * p)) (Gauss.P d) ∧
    Integrable (fun omega =>
      APrimeFirstCellDeltaTargetWeight.canonicalWeight
          tauPrime delta P N k omega *
        |familyMax N k omega| ^ (2 * p)) (Gauss.P d) ∧
    Integrable (fun omega =>
      APrimeFirstCellDeltaTargetWeight.canonicalWeight
          tauPrime delta P N k omega *
        |familyMax N k omega| ^ (2 * P)) (Gauss.P d) ∧
    Integrable (fun omega =>
      |APrimeFirstCellDeltaTargetWeight.canonicalWeight
          tauPrime delta P N k omega ^
            (((2 * P : ℕ) : ℝ)⁻¹) * familyMax N k omega| ^ (2 * p))
      (Gauss.P d) := by
  dsimp only
  have hP :=
    (APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp).2.2
  have hcanonical :=
    APrimeFirstCellDeltaSameWeightLyapunov.sameWeight_integrability
      hTau hP hN hk (p := p) (delta := delta)
  refine ⟨integrable_targetWeight_familyMax_pow hTau hk, ?_⟩
  simpa only [
    APrimeFirstCellDeltaSameWeightLyapunov.canonicalHighWeight,
    APrimeFirstCellDeltaTargetWeight.canonicalWeight,
    APrimeFirstCellCanonicalPlateau.canonicalWeight,
    APrimeFirstCellSampleRegularity.weight] using hcanonical

/-- The two coefficient-one comparisons at a fixed active first-cell
endpoint.  The measure and the canonical weight are identical in the second
inequality. -/
def familyWeightTransferAt
    (tauPrime delta : ℝ) (p N k : ℕ) : Prop :=
  let P := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k) p (familyMax N k) ≤
    momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.canonicalWeight
        tauPrime delta P N k) p (familyMax N k) ∧
  momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.canonicalWeight
        tauPrime delta P N k) p (familyMax N k) ≤
    momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.canonicalWeight
        tauPrime delta P N k) P (familyMax N k)

theorem familyWeightTransferAt_of_bounds
    {tauPrime delta : ℝ} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p N k : ℕ} (hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    familyWeightTransferAt tauPrime delta p N k := by
  have hb := APrimeFirstCellDeltaTargetWeight.highOrder_bounds delta hp
  have hint := familyWeightTransfer_integrability
    (delta := delta) hTau hp hN hk
  dsimp only at hint ⊢
  constructor
  · apply momNormW_mono_weight hp
    · exact targetWeight_nonneg tauPrime delta p N k
    · intro omega
      exact APrimeFirstCellDeltaTargetWeight.targetWeight_le_canonicalWeight
        hTau hDelta N p k omega hp
    · exact hint.2.1
  · simpa only [
      APrimeFirstCellDeltaSameWeightLyapunov.canonicalHighWeight,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight,
      APrimeFirstCellCanonicalPlateau.canonicalWeight,
      APrimeFirstCellSampleRegularity.weight] using
      (APrimeFirstCellDeltaSameWeightLyapunov.sameWeight_momNormW_le
        hTau hp hb.2.1 hN hk)

/-- The transfer is uniform over every positive active first-cell index after
`delta` and `p` are fixed. -/
def actualFamilyWeightTransfer
    (tauPrime delta : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N →
    familyWeightTransferAt tauPrime delta p N k

theorem eventually_actualFamilyWeightTransfer
    {tauPrime delta : ℝ} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p : ℕ} (hp : 1 ≤ p) :
    actualFamilyWeightTransfer tauPrime delta p := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro k _hk1 hk
  exact familyWeightTransferAt_of_bounds
    hTau hDelta hp (by omega) hk

/-- The empty-prefix endpoint and both weights are exactly one, while the
same coefficient-one norm chain remains valid. -/
def kZeroFamilyWeightTransfer
    (tauPrime delta : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧
    (∀ omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 0 omega = 1) ∧
    (∀ omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 0 omega = 1) ∧
    familyWeightTransferAt tauPrime delta p N 0

theorem eventually_kZeroFamilyWeightTransfer
    {tauPrime delta : ℝ} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p : ℕ} (hp : 1 ≤ p) :
    kZeroFamilyWeightTransfer tauPrime delta p := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  refine ⟨by simp [endpoint, cutNetPt_zero], ?_, ?_, ?_⟩
  · intro omega
    exact APrimeFirstCellDeltaTargetWeight.targetWeight_k_zero
      tauPrime delta p N omega
  · intro omega
    exact APrimeFirstCellDeltaTargetWeight.canonicalWeight_k_zero
      tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N omega
  · exact familyWeightTransferAt_of_bounds
      hTau hDelta hp (by omega) (Nat.zero_le _)

/-- A positive `k = 2` resident of the literal sharp event carries both
weight-one identities and the deterministic coefficient-one family chain. -/
def positiveTwoFamilyWeightTransferResident
    (tauPrime delta alpha : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    let u2 := endpoint N 2
    0 < u2 ∧ u2 ≤ firstCellT tauPrime N ∧
    firstCellT tauPrime N ≤ 1 / 2 ∧
    APrimeFirstCellDeltaTargetWeight.targetWeight
      tauPrime delta p N 2 omega = 1 ∧
    APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
      (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 2 omega = 1 ∧
    familyWeightTransferAt tauPrime delta p N 2

theorem positiveTwoFamilyWeightTransferResident_of_target
    {tauPrime delta alpha : ℝ}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) {p : ℕ} (hp : 1 ≤ p)
    (hresident : APrimeFirstCellDeltaTargetWeight.positiveTwoWeightResident
      tauPrime delta alpha) :
    positiveTwoFamilyWeightTransferResident tauPrime delta alpha p := by
  filter_upwards [hresident, eventually_ge_atTop 1] with N hr hN
  dsimp only [APrimeFirstCellDeltaTargetWeight.positiveTwoWeightResident]
    at hr
  obtain ⟨omega, homega, hk, hvpos, hvle, hTle, hall⟩ := hr
  have hw := hall p hp
  refine ⟨omega, homega, hk, hvpos, hvle, hTle,
    hw.2.2.1, hw.2.2.2, ?_⟩
  exact familyWeightTransferAt_of_bounds
    hTau hDelta hp (by omega) hk

/-- One first-cell parameter works before every admissible `delta`; no
numerical high-order family bound is assumed or produced. -/
theorem exists_deltaFamilyWeightTransfer_with_resident :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
      ∀ p : ℕ, 1 ≤ p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (Gauss.P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        actualFamilyWeightTransfer tauPrime delta p ∧
        kZeroFamilyWeightTransfer tauPrime delta p ∧
        positiveTwoFamilyWeightTransferResident
          tauPrime delta (delta / 16) p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaTargetWeight.exists_deltaTargetWeight_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  obtain ⟨hmeas, hprob, _hweights, _htzero, _hczero, hresident⟩ :=
    hall delta hDelta hDelta100
  exact ⟨hmeas, hprob,
    eventually_actualFamilyWeightTransfer hTau hDelta hp,
    eventually_kZeroFamilyWeightTransfer hTau hDelta hp,
    positiveTwoFamilyWeightTransferResident_of_target
      hTau hDelta hp hresident⟩

#print axioms targetWeight_aestronglyMeasurable
#print axioms targetWeight_nonneg
#print axioms targetWeight_le_one
#print axioms integrable_targetWeight_familyMax_pow
#print axioms momNormW_mono_weight
#print axioms familyWeightTransfer_integrability
#print axioms familyWeightTransferAt_of_bounds
#print axioms eventually_actualFamilyWeightTransfer
#print axioms eventually_kZeroFamilyWeightTransfer
#print axioms positiveTwoFamilyWeightTransferResident_of_target
#print axioms exists_deltaFamilyWeightTransfer_with_resident

end

end RBM.APrimeFirstCellDeltaFamilyWeightTransfer
