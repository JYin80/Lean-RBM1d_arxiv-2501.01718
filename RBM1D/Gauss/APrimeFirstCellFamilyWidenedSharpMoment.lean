/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMomentSharp
import RBM1D.Gauss.APrimeFirstCellFamilySharpArithmetic
import RBM1D.Gauss.APrimeFirstCellFamilyLowMomentSameWeight
import RBM1D.Gauss.APrimeFirstCellFamilyWidenedMoment

/-!
# T533: sharp low-order family moments under the widened target weight

For fixed `1 <= p <= P`, T527's order-`P` coordinate estimate and T529's
single finite-family cost first give the sharp order-`P` family estimate
under the canonical weight.  T521 lowers the moment order without changing
that weight, and T524's coefficient-one weight monotonicity transfers the
result to the literal order-`p` widened target weight.
-/

namespace RBM.APrimeFirstCellFamilyWidenedSharpMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : Real := APrimeFirstCellQuantMomentSharp.delta
noncomputable abbrev alpha : Real := APrimeFirstCellQuantMomentSharp.alpha

/-- The intermediate sharp order-`P` family estimate under the unchanged
canonical order-`P` weight. -/
def canonicalFamilySharpMomentAt (tauPrime : Real) (P N k : Nat) : Prop :=
  momNormW (Gauss.P d) (weight tauPrime P N k) P (familyMax N k) <=
    (N : Real) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))

/-- T512's finite-maximum inequality pays the family-cardinality root once. -/
theorem canonicalFamilySharpMomentAt_of_coords {tauPrime : Real}
    (hTau : 0 < tauPrime) {P N k : Nat}
    (hP : 40000 <= P) (hN : 81 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : forall a : LoopArg (d.L N) 2,
      APrimeFirstCellQuantMomentSharp.quantMomentAt' tauPrime P N k a) :
    canonicalFamilySharpMomentAt tauPrime P N k := by
  have hP1 : 1 <= P := by omega
  have hNpos : (0 : Real) < N := by
    exact_mod_cast (show 0 < N by omega)
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < etaT 0 0 / etaT 0 (endpoint N k) :=
    Step2Moment.ratR_pos (s := fun _ => 0) (N := N)
      (by norm_num) (by norm_num) hv1
  have hc : 0 <= (N : Real) ^ (delta / 5) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real)) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hR.le _)
  have hw0 : forall omega, 0 <= weight tauPrime P N k omega := fun omega =>
    APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM tauPrime N) omega
  have hint : forall a : LoopArg (d.L N) 2,
      Integrable (fun omega => weight tauPrime P N k omega *
        |Y N k a (endpoint N k) omega| ^ (2 * P)) (Gauss.P d) := by
    intro a
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
      (δ := delta) hTau hP1 (by omega) hk a).2.hYi
  have hmax := APrimeFirstCellFamilyHighMoment.momNormW_finsetMax_le
    (Gauss.P d) (weight tauPrime P N k)
      (fun a => Y N k a (endpoint N k)) P hP1 hc hw0 hint hcoords
  change momNormW (Gauss.P d) (weight tauPrime P N k) P (familyMax N k) <= _
    at hmax
  calc
    _ <= (Fintype.card (LoopArg (d.L N) 2) : Real) ^
          ((1 : Real) / (2 * (P : Real))) *
        ((N : Real) ^ (delta / 5) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))) := hmax
    _ <= (N : Real) ^ (delta / 20) *
        ((N : Real) ^ (delta / 5) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))) :=
      mul_le_mul_of_nonneg_right
        (APrimeFirstCellFamilySharpArithmetic.family_card_root_le hN hP) hc
    _ = (N : Real) ^ (delta / 4) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real)) := by
      rw [← mul_assoc,
        APrimeFirstCellFamilySharpArithmetic.sharp_exponent_product_eq
          (show 1 <= N by omega)]

/-- The requested sharp low-order family estimate under the literal
order-`p` widened target weight. -/
def familyWidenedSharpMomentAt
    (tauPrime : Real) (p N k : Nat) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k)
      p (familyMax N k) <=
    (N : Real) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : Real))

/-- Lower the moment order under `weight_P`, then use the pointwise
comparison `targetWeight_p <= weight_P`, with coefficient one throughout. -/
theorem familyWidenedSharpMomentAt_of_canonical {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P N k : Nat}
    (hp : 1 <= p) (hpP : p <= P) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcanonical : canonicalFamilySharpMomentAt tauPrime P N k) :
    familyWidenedSharpMomentAt tauPrime p N k := by
  have hint :=
    (APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_integrability
      hTau (hp.trans hpP) hN hk (p := p)).1
  have htarget : momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k)
      p (familyMax N k) <=
      momNormW (Gauss.P d) (weight tauPrime P N k) p (familyMax N k) := by
    apply APrimeFirstCellFamilyWidenedMoment.momNormW_mono_weight hp
    · intro omega
      exact APrimeWeight.widenedW_nonneg
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u omega => Step2Moment.jSnorm
          (sample d) 0 60 (fun _ => 0) N u omega)
        (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh (1 / 2000) p N k omega
    · intro omega
      exact APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hTau N p P k omega hp hpP
    · exact hint
  have horder :=
    APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_momNormW_le
      hTau hp hpP hN hk
  exact htarget.trans (horder.trans hcanonical)

/-- The complete fixed-size assembly from T527, T529, T521, and T524. -/
theorem familyWidenedSharpMomentAt_of_coords {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P N k : Nat}
    (hp : 1 <= p) (hpP : p <= P) (hP : 40000 <= P)
    (hN : 81 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : forall a : LoopArg (d.L N) 2,
      APrimeFirstCellQuantMomentSharp.quantMomentAt' tauPrime P N k a) :
    familyWidenedSharpMomentAt tauPrime p N k := by
  apply familyWidenedSharpMomentAt_of_canonical hTau hp hpP (by omega) hk
  exact canonicalFamilySharpMomentAt_of_coords hTau hP hN hk hcoords

/-- Both orders are fixed before the common eventual threshold, which is
uniform over every positive active first-cell index. -/
def actualFamilyWidenedSharpMoment (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    familyWidenedSharpMomentAt tauPrime p N k

theorem actualFamilyWidenedSharpMoment_of_coords {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P : Nat}
    (hp : 1 <= p) (hpP : p <= P) (hP : 40000 <= P)
    (hcoords : APrimeFirstCellQuantMomentSharp.actualQuantMoment'
      tauPrime P) : actualFamilyWidenedSharpMoment tauPrime p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  intro k hk1 hk
  exact familyWidenedSharpMomentAt_of_coords hTau hp hpP hP hN hk
    (hcoordsN k hk1 hk)

/-- The zero-index family branch retains its exact ratio-one form. -/
def kZeroFamilyWidenedSharpMoment (tauPrime : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ familyWidenedSharpMomentAt tauPrime p N 0 ∧
      momNormW (Gauss.P d)
        (APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 0)
        p (familyMax N 0) <= (N : Real) ^ (delta / 4)

theorem kZeroFamilyWidenedSharpMoment_of_coords {tauPrime : Real}
    (hTau : 0 < tauPrime) {p P : Nat}
    (hp : 1 <= p) (hpP : p <= P) (hP : 40000 <= P)
    (hzero : APrimeFirstCellQuantMomentSharp.kZeroQuantMoment'
      tauPrime P) : kZeroFamilyWidenedSharpMoment tauPrime p := by
  filter_upwards [hzero, eventually_ge_atTop 81] with N hzeroN hN
  have hv : endpoint N 0 = 0 := (hzeroN
    (Classical.choice (inferInstance : Nonempty (LoopArg (d.L N) 2)))).1
  have hfamily := familyWidenedSharpMomentAt_of_coords hTau hp hpP hP hN
    (Nat.zero_le _) (fun a => (hzeroN a).2.1)
  refine ⟨hv, hfamily, ?_⟩
  simpa [familyWidenedSharpMomentAt, hv, etaT, mE_zero] using hfamily

/-- The same sharp-event positive resident carries both weight plateaus and
the widened sharp family estimate. -/
def positiveTwoFamilyWidenedSharpMomentResident
    (tauPrime : Real) (p P : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 <= firstCellT tauPrime N ∧
    APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 2 omega = 1 ∧
    weight tauPrime P N 2 omega = 1 ∧
    familyWidenedSharpMomentAt tauPrime p N 2

theorem positiveTwoFamilyWidenedSharpMomentResident_of_coords
    {tauPrime : Real} {p P : Nat}
    (hresident :
      APrimeFirstCellQuantMomentSharp.positiveTwoQuantMomentResident'
        tauPrime P)
    (hfamily : actualFamilyWidenedSharpMoment tauPrime p)
    (htarget : ∀ᶠ N : Nat in atTop, ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
      APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 2 omega = 1) :
    positiveTwoFamilyWidenedSharpMomentResident tauPrime p P := by
  filter_upwards [hresident, hfamily, htarget] with N hr hf ht
  obtain ⟨omega, homega, hk, hvpos, hvle, hweight, _hcoords⟩ := hr
  exact ⟨omega, homega, hk, hvpos, hvle, ht omega homega, hweight,
    hf 2 (by norm_num) hk⟩

/-- One T527 parameter and one literal sharp event supply every fixed pair
`1 <= p <= P`, `P >= 40000`, including zero and positive residents. -/
theorem exists_familyWidenedSharpMoment_with_resident :
    exists tauPrime : Real, 0 < tauPrime ∧
      forall p P : Nat, 1 <= p -> p <= P -> 40000 <= P ->
        (forall N k omega,
          APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N k omega <=
            weight tauPrime P N k omega) ∧
        (forall N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (Gauss.P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        (∀ᶠ N : Nat in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N).Nonempty) ∧
        actualFamilyWidenedSharpMoment tauPrime p ∧
        kZeroFamilyWidenedSharpMoment tauPrime p ∧
        positiveTwoFamilyWidenedSharpMomentResident tauPrime p P := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellQuantMomentSharp.exists_quantMoment_with_resident'
  refine ⟨tauPrime, hTau, ?_⟩
  intro p P hp hpP hP
  obtain ⟨hmeas, hprob, hnonempty, hcoords, hzero, hresident⟩ :=
    hall P (by omega)
  have hfamily := actualFamilyWidenedSharpMoment_of_coords
    hTau hp hpP hP hcoords
  have htarget : ∀ᶠ N : Nat in atTop, ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      APrimeFirstCellCrossOrderWeight.targetWeight tauPrime p N 2 omega = 1 := by
    filter_upwards [
      APrimeFirstCellCrossOrderWeight.eventually_targetWeight_two_one_on_sharpCommonEvent
        tauPrime] with N htargetN
    intro omega homega
    exact htargetN omega (by
      simpa only [delta, alpha, APrimeFirstCellQuantMomentSharp.delta,
        APrimeFirstCellQuantMomentSharp.alpha] using homega) p
  exact ⟨fun N k omega =>
      APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hTau N p P k omega hp hpP,
    hmeas, hprob, hnonempty, hfamily,
    kZeroFamilyWidenedSharpMoment_of_coords hTau hp hpP hP hzero,
    positiveTwoFamilyWidenedSharpMomentResident_of_coords
      hresident hfamily htarget⟩

#print axioms canonicalFamilySharpMomentAt_of_coords
#print axioms familyWidenedSharpMomentAt_of_canonical
#print axioms familyWidenedSharpMomentAt_of_coords
#print axioms actualFamilyWidenedSharpMoment_of_coords
#print axioms kZeroFamilyWidenedSharpMoment_of_coords
#print axioms positiveTwoFamilyWidenedSharpMomentResident_of_coords
#print axioms exists_familyWidenedSharpMoment_with_resident

end

end RBM.APrimeFirstCellFamilyWidenedSharpMoment
