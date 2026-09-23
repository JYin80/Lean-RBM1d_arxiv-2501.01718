/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMomentSharp
import RBM1D.Gauss.APrimeFirstCellFamilySharpArithmetic

/-!
# T531: the sharp first-cell coordinate-family maximum

T527 supplies every actual endpoint coordinate at exponent `delta / 5`
under one fixed order-`P` canonical weight.  T512's finite-maximum theorem
costs the exact family-cardinality root, bounded by T529 at exponent
`delta / 20`.  Their product is exactly the target exponent `delta / 4`.
-/

namespace RBM.APrimeFirstCellFamilySharpMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellQuantMomentSharp.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellQuantMomentSharp.alpha

/-- The actual finite-family target under the same canonical order-`P`
weight as every T527 coordinate. -/
def familyMomentAt' (τ' : ℝ) (P N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' P N k) P (familyMax N k) ≤
    (N : ℝ) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- At fixed size, T512's exact finite-maximum inequality and T529's root
cost turn T527's entire coordinate family into the sharp family bound. -/
theorem familyMomentAt_of_coords' {τ' : ℝ} (hτ' : 0 < τ') {P N k : ℕ}
    (hP : 40000 ≤ P) (hN : 81 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellQuantMomentSharp.quantMomentAt' τ' P N k a) :
    familyMomentAt' τ' P N k := by
  have hP1 : 1 ≤ P := by omega
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < etaT 0 0 / etaT 0 (endpoint N k) :=
    Step2Moment.ratR_pos (s := fun _ => 0) (N := N)
      (by norm_num) (by norm_num) hv1
  have hc : 0 ≤ (N : ℝ) ^ (delta / 5) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hR.le _)
  have hw0 : ∀ ω, 0 ≤ weight τ' P N k ω := fun ω =>
    APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω
  have hint : ∀ a : LoopArg (d.L N) 2,
      Integrable (fun ω => weight τ' P N k ω *
        |Y N k a (endpoint N k) ω| ^ (2 * P)) (Gauss.P d) := by
    intro a
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
      (δ := delta) hτ' hP1 (by omega) hk a).2.hYi
  have hmax := APrimeFirstCellFamilyHighMoment.momNormW_finsetMax_le
    (Gauss.P d) (weight τ' P N k)
      (fun a => Y N k a (endpoint N k)) P hP1 hc hw0 hint hcoords
  change momNormW (Gauss.P d) (weight τ' P N k) P (familyMax N k) ≤ _ at hmax
  calc
    _ ≤ (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (P : ℝ))) *
        ((N : ℝ) ^ (delta / 5) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) := hmax
    _ ≤ (N : ℝ) ^ (delta / 20) *
        ((N : ℝ) ^ (delta / 5) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_right
        (APrimeFirstCellFamilySharpArithmetic.family_card_root_le hN hP) hc
    _ = (N : ℝ) ^ (delta / 4) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) := by
      rw [← mul_assoc,
        APrimeFirstCellFamilySharpArithmetic.sharp_exponent_product_eq
          (show 1 ≤ N by omega)]

/-- The sharp family maximum is uniform over all positive active indices
after the high order has been fixed. -/
def actualFamilySharpMoment (τ' : ℝ) (P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N → familyMomentAt' τ' P N k

/-- The order `P` is fixed before the common threshold for all active
indices and all output coordinates. -/
theorem actualFamilySharpMoment_of_coords {τ' : ℝ} (hτ' : 0 < τ')
    (P : ℕ) (hP : 40000 ≤ P)
    (hcoords : APrimeFirstCellQuantMomentSharp.actualQuantMoment' τ' P) :
    actualFamilySharpMoment τ' P := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  intro k hk1 hk
  exact familyMomentAt_of_coords' hτ' hP hN hk (hcoordsN k hk1 hk)

/-- The zero-index family branch retains both the normalized target and its
exact ratio-one form. -/
def kZeroFamilySharpMoment (τ' : ℝ) (P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧ familyMomentAt' τ' P N 0 ∧
      momNormW (Gauss.P d) (weight τ' P N 0) P (familyMax N 0) ≤
        (N : ℝ) ^ (delta / 4)

/-- T527's independent zero-coordinate branch supplies the exact zero
family bound through the same finite-maximum estimate. -/
theorem eventually_kZeroFamilySharpMoment {τ' : ℝ} (hτ' : 0 < τ')
    (P : ℕ) (hP : 40000 ≤ P) : kZeroFamilySharpMoment τ' P := by
  filter_upwards [APrimeFirstCellQuantMomentSharp.eventually_kZeroQuantMoment'
    hτ' P (by omega), eventually_ge_atTop 81] with N hzero hN
  have hv : endpoint N 0 = 0 := by
    simp [endpoint, cutNetPt_zero]
  have hfamily := familyMomentAt_of_coords' hτ' hP hN (Nat.zero_le _)
    (fun a => (hzero a).2.1)
  refine ⟨hv, hfamily, ?_⟩
  simpa [familyMomentAt', hv, etaT, mE_zero] using hfamily

/-- T527's same positive `k = 2` resident carries the sharp family moment
and the same canonical weight equal to one. -/
def positiveTwoFamilySharpMomentResident (τ' : ℝ) (P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    weight τ' P N 2 ω = 1 ∧ familyMomentAt' τ' P N 2

/-- Attach the uniform family estimate to T527's literal resident without
changing its event, sample, weight, or endpoint. -/
theorem positiveTwoFamilySharpMomentResident_of_coords {τ' : ℝ} {P : ℕ}
    (hresident :
      APrimeFirstCellQuantMomentSharp.positiveTwoQuantMomentResident' τ' P)
    (hfamily : actualFamilySharpMoment τ' P) :
    positiveTwoFamilySharpMomentResident τ' P := by
  filter_upwards [hresident, hfamily] with N hr hf
  obtain ⟨ω, hω, hk, hvpos, hvle, hw, _hcoords⟩ := hr
  exact ⟨ω, hω, hk, hvpos, hvle, hw,
    hf 2 (by norm_num) hk⟩

/-- One T527 parameter and literal sharp common event provide the sharp
high-order family moment, its zero branch, and a genuine positive resident. -/
theorem exists_familySharpMoment_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ P : ℕ, 40000 ≤ P →
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          τ' delta alpha N).Nonempty) ∧
      actualFamilySharpMoment τ' P ∧ kZeroFamilySharpMoment τ' P ∧
      positiveTwoFamilySharpMomentResident τ' P := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQuantMomentSharp.exists_quantMoment_with_resident'
  refine ⟨τ', hτ', ?_⟩
  intro P hP
  obtain ⟨hm, hprob, hne, hcoords, _hzero, hresident⟩ :=
    hall P (by omega)
  have hfamily := actualFamilySharpMoment_of_coords hτ' P hP hcoords
  exact ⟨hm, hprob, hne, hfamily,
    eventually_kZeroFamilySharpMoment hτ' P hP,
    positiveTwoFamilySharpMomentResident_of_coords hresident hfamily⟩

#print axioms familyMomentAt_of_coords'
#print axioms actualFamilySharpMoment_of_coords
#print axioms eventually_kZeroFamilySharpMoment
#print axioms positiveTwoFamilySharpMomentResident_of_coords
#print axioms exists_familySharpMoment_with_resident

end

end RBM.APrimeFirstCellFamilySharpMoment
