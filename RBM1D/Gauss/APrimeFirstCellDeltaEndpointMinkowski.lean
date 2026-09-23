/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaTargetWeight
import RBM1D.Gauss.APrimeFirstCellEndpointHighMoment
import RBM1D.Gauss.APrimeFirstCellFamilyLowMomentSameWeight

/-!
# T552: variable-delta first-cell endpoint Minkowski adapter

This module isolates the deterministic endpoint step under T542's explicit
delta target weight.  It proves honest weighted endpoint-power integrability,
uses the exact endpoint identity to obtain a coefficient-one Minkowski bound,
and exports only the implication from a supplied target-family bound to the
corresponding endpoint bound.

No coordinate or family estimate, `hfamily`, `APrimeSlot'`, or A-prime
closure is asserted.
-/

namespace RBM.APrimeFirstCellDeltaEndpointMinkowski

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T542's literal explicit-delta widened target weight. -/
noncomputable abbrev targetWeight (tauPrime delta : Real)
    (p N k : Nat) : Ω d -> Real :=
  APrimeFirstCellDeltaTargetWeight.targetWeight tauPrime delta p N k

/-- The actual endpoint bootstrap observable. -/
private noncomputable abbrev endpointJ (N k : Nat) : Ω d -> Real :=
  fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
    N (endpoint N k) omega

/-- The deterministic endpoint baseline `R_v^(-4)`. -/
noncomputable def endpointBaseline (N k : Nat) : Real :=
  1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4

/-- A supplied numerical bound for the target-weight family maximum. -/
def targetFamilyBoundAt (tauPrime delta : Real) (p N k : Nat)
    (C : Real) : Prop :=
  momNormW (P d) (targetWeight tauPrime delta p N k) p
    (familyMax N k) <= C

/-- The corresponding endpoint conclusion, with the deterministic baseline
added with coefficient one. -/
def endpointBoundAt (tauPrime delta : Real) (p N k : Nat)
    (C : Real) : Prop :=
  momNormW (P d) (targetWeight tauPrime delta p N k) p
    (endpointJ N k) <= endpointBaseline N k + C

/-- T542's target weight is measurable for every explicit `delta`. -/
theorem targetWeight_aestronglyMeasurable (tauPrime delta : Real)
    (p N k : Nat) :
    AEStronglyMeasurable (targetWeight tauPrime delta p N k) (P d) := by
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

/-- T542's target weight is pointwise nonnegative. -/
theorem targetWeight_nonneg (tauPrime delta : Real) (p N k : Nat)
    (omega : Ω d) : 0 <= targetWeight tauPrime delta p N k omega := by
  exact APrimeWeight.widenedW_nonneg
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh delta p N k omega

/-- T542's target weight is pointwise at most one. -/
theorem targetWeight_le_one (tauPrime delta : Real) (p N k : Nat)
    (omega : Ω d) : targetWeight tauPrime delta p N k omega <= 1 := by
  exact APrimeWeight.widenedW_le_one
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm
      (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh delta p N k omega

private theorem familyMax_nonneg (N k : Nat) (omega : Ω d) :
    0 <= familyMax N k omega := by
  dsimp [familyMax]
  let a := Classical.choice
    (inferInstance : Nonempty (LoopArg (d.L N) 2))
  exact (abs_nonneg (Y N k a (endpoint N k) omega)).trans
    (Finset.le_sup' (fun a => |Y N k a (endpoint N k) omega|)
      (Finset.mem_univ a))

/-- Honest integrability of the weighted family power under the explicit
delta target weight. -/
theorem integrable_targetWeight_familyMax_pow {tauPrime delta : Real}
    (hTau : 0 < tauPrime) {p N k : Nat}
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega => targetWeight tauPrime delta p N k omega *
      |familyMax N k omega| ^ (2 * p)) (P d) := by
  have hi := APrimeFirstCellFamilyLowMomentSameWeight.integrable_familyMax_pow
    hTau hk p
  have hwmeas := targetWeight_aestronglyMeasurable tauPrime delta p N k
  have hMmeas : AEStronglyMeasurable
      (fun omega => |familyMax N k omega| ^ (2 * p)) (P d) :=
    (APrimeFirstCellFamilyLowMomentSameWeight.continuous_familyMax
      hTau hk).abs.pow (2 * p) |>.aestronglyMeasurable
  apply hi.mono' (hwmeas.mul hMmeas)
  exact Filter.Eventually.of_forall fun omega => by
    have hw0 := targetWeight_nonneg tauPrime delta p N k omega
    have hw1 := targetWeight_le_one tauPrime delta p N k omega
    change ‖targetWeight tauPrime delta p N k omega *
      |familyMax N k omega| ^ (2 * p)‖ <=
      |familyMax N k omega| ^ (2 * p)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (by positivity))]
    exact mul_le_of_le_one_left (by positivity) hw1

/-- The exact pointwise endpoint identity in the vocabulary used here. -/
theorem endpointJ_eq_baseline_add_familyMax {tauPrime : Real}
    (hTau : 0 < tauPrime) (N k : Nat)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    endpointJ N k = fun omega => endpointBaseline N k + familyMax N k omega := by
  funext omega
  exact APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
    hTau N k hk omega

/-- Honest integrability of the untruncated endpoint weighted power.  The
proof uses the exact endpoint identity and an explicit integrable majorant;
it does not appeal to a total-integral convention. -/
theorem integrable_targetWeight_endpoint_pow {tauPrime delta : Real}
    (hTau : 0 < tauPrime) {p N k : Nat}
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun omega => targetWeight tauPrime delta p N k omega *
      |endpointJ N k omega| ^ (2 * p)) (P d) := by
  let w := targetWeight tauPrime delta p N k
  let M := familyMax N k
  let b := endpointBaseline N k
  let q := 2 * p
  have hwmeas : AEStronglyMeasurable w (P d) :=
    targetWeight_aestronglyMeasurable tauPrime delta p N k
  have hw0 : ∀ omega, 0 <= w omega :=
    targetWeight_nonneg tauPrime delta p N k
  have hw1 : ∀ omega, w omega <= 1 :=
    targetWeight_le_one tauPrime delta p N k
  have hwint : Integrable w (P d) := by
    apply Integrable.of_bound hwmeas 1
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 omega)]
      exact hw1 omega
  have hMint : Integrable (fun omega => w omega * |M omega| ^ q) (P d) :=
    integrable_targetWeight_familyMax_pow hTau hk
  have hb0 : 0 <= b := by dsimp [b, endpointBaseline]; positivity
  have hconst : Integrable (fun omega => w omega * |b| ^ q) (P d) := by
    simpa only [mul_comm] using hwint.const_mul (|b| ^ q)
  have hmajor : Integrable (fun omega =>
      2 ^ (q - 1) * (w omega * |b| ^ q + w omega * |M omega| ^ q))
      (P d) := (hconst.add hMint).const_mul _
  have hJmeas : Measurable (endpointJ N k) :=
    APrimeSlotFields.measurable_jSnorm
      (sample d) 0 60 (fun _ => 0) N (endpoint N k)
  apply hmajor.mono' (hwmeas.mul
    ((continuous_abs.measurable.comp hJmeas).pow_const q).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun omega => by
    have hM0 : 0 <= M omega := familyMax_nonneg N k omega
    have hid := congrFun (endpointJ_eq_baseline_add_familyMax hTau N k hk) omega
    change ‖w omega * |endpointJ N k omega| ^ q‖ <=
      2 ^ (q - 1) * (w omega * |b| ^ q + w omega * |M omega| ^ q)
    rw [show endpointJ N k omega = b + M omega by exact hid]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hw0 omega) (by positivity)),
      abs_of_nonneg (add_nonneg hb0 hM0), abs_of_nonneg hb0,
      abs_of_nonneg hM0]
    have hadd := add_pow_le hb0 hM0 q
    calc
      w omega * (b + M omega) ^ q <=
          w omega * (2 ^ (q - 1) * (b ^ q + M omega ^ q)) :=
        mul_le_mul_of_nonneg_left hadd (hw0 omega)
      _ = 2 ^ (q - 1) *
          (w omega * b ^ q + w omega * M omega ^ q) := by ring

/-- The exact identity and weighted Minkowski give the coefficient-one
endpoint estimate before any numerical family bound is supplied. -/
theorem momNormW_endpointJ_le {tauPrime delta : Real}
    (hTau : 0 < tauPrime) {p N k : Nat} (hp : 1 <= p)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N) :
    momNormW (P d) (targetWeight tauPrime delta p N k) p
        (endpointJ N k) <=
      endpointBaseline N k +
        momNormW (P d) (targetWeight tauPrime delta p N k) p
          (familyMax N k) := by
  let w := targetWeight tauPrime delta p N k
  let M := familyMax N k
  let b := endpointBaseline N k
  have hw0 : ∀ omega, 0 <= w omega :=
    targetWeight_nonneg tauPrime delta p N k
  have hw1 : ∀ omega, w omega <= 1 :=
    targetWeight_le_one tauPrime delta p N k
  have hM0 : ∀ omega, 0 <= M omega := familyMax_nonneg N k
  have hMi : Integrable (fun omega => w omega * |M omega| ^ (2 * p))
      (P d) := integrable_targetWeight_familyMax_pow hTau hk
  have hb : 0 <= b := by dsimp [b, endpointBaseline]; positivity
  have htriangle := APrimeFirstCellEndpointHighMoment.momNormW_const_add_le
    hp hw0 hw1 hM0 hMi hb
  rw [endpointJ_eq_baseline_add_familyMax hTau N k hk]
  exact htriangle

/-- A supplied target-family estimate transfers to the endpoint with no
change of measure, weight, order, or coefficient. -/
theorem endpointBoundAt_of_familyBound {tauPrime delta C : Real}
    (hTau : 0 < tauPrime) {p N k : Nat} (hp : 1 <= p)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hfamily : targetFamilyBoundAt tauPrime delta p N k C) :
    endpointBoundAt tauPrime delta p N k C := by
  exact (momNormW_endpointJ_le hTau hp hk).trans
    (add_le_add le_rfl hfamily)

/-- The empty prefix has exact endpoint zero, ratio one, baseline one, and
target weight one. -/
theorem kZero_exact (tauPrime delta : Real) (p N : Nat) :
    endpoint N 0 = 0 ∧
    Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 0) = 1 ∧
    endpointBaseline N 0 = 1 ∧
    (∀ omega : Ω d, targetWeight tauPrime delta p N 0 omega = 1) := by
  have hv : endpoint N 0 = 0 := by simp [endpoint, cutNetPt_zero]
  have hR : Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 0) = 1 := by
    rw [hv]
    unfold Step2Moment.ratR
    exact div_self (Step2.etaT_pos' (E := 0) (by norm_num) (by norm_num)).ne'
  refine ⟨hv, hR, ?_, ?_⟩
  · simp [endpointBaseline, hR]
  · intro omega
    exact APrimeFirstCellDeltaTargetWeight.targetWeight_k_zero
      tauPrime delta p N omega

/-- Exact zero-prefix endpoint identity. -/
theorem kZero_endpointJ_eq {tauPrime : Real} (hTau : 0 < tauPrime)
    (N : Nat) : endpointJ N 0 = fun omega => 1 + familyMax N 0 omega := by
  have hid := endpointJ_eq_baseline_add_familyMax hTau N 0 (Nat.zero_le _)
  have hb := (kZero_exact tauPrime 0 0 N).2.2.1
  simpa only [hb] using hid

/-- The zero-prefix implication retains all exact boundary identities and
adds only the supplied family bound. -/
theorem kZero_endpointBoundAt_of_familyBound
    {tauPrime delta C : Real} (hTau : 0 < tauPrime)
    {p N : Nat} (hp : 1 <= p)
    (hfamily : targetFamilyBoundAt tauPrime delta p N 0 C) :
    endpoint N 0 = 0 ∧
    Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 0) = 1 ∧
    endpointBaseline N 0 = 1 ∧
    (∀ omega : Ω d, targetWeight tauPrime delta p N 0 omega = 1) ∧
    momNormW (P d) (targetWeight tauPrime delta p N 0) p
      (endpointJ N 0) <= 1 + C := by
  obtain ⟨hv, hR, hb, hw⟩ := kZero_exact tauPrime delta p N
  have hend := endpointBoundAt_of_familyBound hTau hp (Nat.zero_le _) hfamily
  refine ⟨hv, hR, hb, hw, ?_⟩
  simpa only [endpointBoundAt, hb] using hend

/-- T542's existing event and positive two-weight resident, projected without
adding any coordinate, family, or endpoint numerical estimate. -/
theorem exists_deltaWeightEventResident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        (∀ p N omega, targetWeight tauPrime delta p N 0 omega = 1) ∧
        APrimeFirstCellDeltaTargetWeight.positiveTwoWeightResident
          tauPrime delta (delta / 16) := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaTargetWeight.exists_deltaTargetWeight_with_resident
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100
  obtain ⟨hmeas, hprob, _hcompare, hzero, _hcanonical, hresident⟩ :=
    hall delta hDelta hDelta100
  exact ⟨hmeas, hprob, hzero, hresident⟩

#print axioms targetWeight_aestronglyMeasurable
#print axioms targetWeight_nonneg
#print axioms targetWeight_le_one
#print axioms integrable_targetWeight_familyMax_pow
#print axioms endpointJ_eq_baseline_add_familyMax
#print axioms integrable_targetWeight_endpoint_pow
#print axioms momNormW_endpointJ_le
#print axioms endpointBoundAt_of_familyBound
#print axioms kZero_exact
#print axioms kZero_endpointJ_eq
#print axioms kZero_endpointBoundAt_of_familyBound
#print axioms exists_deltaWeightEventResident

end

end RBM.APrimeFirstCellDeltaEndpointMinkowski
