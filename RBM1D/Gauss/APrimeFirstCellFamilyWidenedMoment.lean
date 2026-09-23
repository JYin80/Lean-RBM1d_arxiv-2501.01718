/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCrossOrderWeight
import RBM1D.Gauss.APrimeFirstCellFamilyLowMomentSameWeight

/-!
# T524: lower family moments under the widened target weight

Pointwise domination of the lower-order target weight by the canonical
order-`P` weight transfers T521's order-`p` family estimate with coefficient
one.
-/

namespace RBM.APrimeFirstCellFamilyWidenedMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ :=
  APrimeFirstCellFamilyLowMomentSameWeight.delta
noncomputable abbrev alpha : ℝ :=
  APrimeFirstCellFamilyLowMomentSameWeight.alpha

/-- Increasing a nonnegative weight at a fixed positive moment order can
only increase `momNormW`.  This uses integral monotonicity followed by
nonnegative real-power monotonicity. -/
theorem momNormW_mono_weight {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {w W Y : Ω → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hw0 : ∀ ω, 0 ≤ w ω) (hwW : ∀ ω, w ω ≤ W ω)
    (hWint : Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P) :
    momNormW P w p Y ≤ momNormW P W p Y := by
  unfold momNormW
  apply Real.rpow_le_rpow
    (integral_nonneg fun ω => mul_nonneg (hw0 ω) (by positivity))
  · exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω =>
        mul_nonneg (hw0 ω) (pow_nonneg (abs_nonneg _) _))
      hWint
      (Filter.Eventually.of_forall fun ω =>
        mul_le_mul_of_nonneg_right (hwW ω) (pow_nonneg (abs_nonneg _) _))
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity

/-- The requested lower family moment under the literal widened target
weight. -/
def familyWidenedMomentAt (τ' : ℝ) (p N k : ℕ) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k)
      p (familyMax N k) ≤
    (N : ℝ) ^ (delta / 2) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T520's pointwise comparison transfers T521's same-order estimate to
the target widened weight without changing its coefficient. -/
theorem familyWidenedMomentAt_of_sameWeight {τ' : ℝ}
    (hτ' : 0 < τ') {p P N k : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hlow : APrimeFirstCellFamilyLowMomentSameWeight.familyLowMomentAt
      τ' p P N k) : familyWidenedMomentAt τ' p N k := by
  have hint :=
    (APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_integrability
      hτ' (hp.trans hpP) hN hk (p := p)).1
  have hmono : momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k)
      p (familyMax N k) ≤
      momNormW (Gauss.P d) (weight τ' P N k) p (familyMax N k) := by
    apply momNormW_mono_weight hp
    · intro ω
      exact APrimeWeight.widenedW_nonneg
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u ω => Step2Moment.jSnorm
          (sample d) 0 60 (fun _ => 0) N u ω)
        (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh (1 / 2000) p N k ω
    · intro ω
      exact APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hτ' N p P k ω hp hpP
    · exact hint
  exact hmono.trans hlow

def actualFamilyWidenedMoment (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
      familyWidenedMomentAt τ' p N k

/-- Both orders remain fixed before the eventual size threshold, which is
uniform over every active first-cell index. -/
theorem actualFamilyWidenedMoment_of_sameWeight {τ' : ℝ}
    (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P)
    (hlow : APrimeFirstCellFamilyLowMomentSameWeight.actualFamilyLowMoment
      τ' p P) : actualFamilyWidenedMoment τ' p := by
  filter_upwards [hlow, eventually_ge_atTop 1] with N hlowN hN
  intro k hk1 hk
  exact familyWidenedMomentAt_of_sameWeight hτ' hp hpP
    (by omega) hk (hlowN k hk1 hk)

def kZeroFamilyWidenedMoment (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧ familyWidenedMomentAt τ' p N 0 ∧
      momNormW (Gauss.P d)
          (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N 0)
          p (familyMax N 0) ≤ (N : ℝ) ^ (delta / 2)

/-- The empty-prefix branch is transferred by the same weight monotonicity
argument and retains the exact ratio-one bound. -/
theorem kZeroFamilyWidenedMoment_of_sameWeight {τ' : ℝ}
    (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P)
    (hzero : APrimeFirstCellFamilyLowMomentSameWeight.kZeroFamilyLowMoment
      τ' p P) : kZeroFamilyWidenedMoment τ' p := by
  filter_upwards [hzero, eventually_ge_atTop 1] with N hz hN
  have hk : 0 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N := Nat.zero_le _
  have hint :=
    (APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_integrability
      hτ' (hp.trans hpP) (show 0 < N by omega) hk (p := p)).1
  have hmono : momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N 0)
      p (familyMax N 0) ≤
      momNormW (Gauss.P d) (weight τ' P N 0) p (familyMax N 0) := by
    apply momNormW_mono_weight hp
    · intro ω
      exact APrimeWeight.widenedW_nonneg
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u ω => Step2Moment.jSnorm
          (sample d) 0 60 (fun _ => 0) N u ω)
        (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh (1 / 2000) p N 0 ω
    · intro ω
      exact APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hτ' N p P 0 ω hp hpP
    · exact hint
  exact ⟨hz.1, familyWidenedMomentAt_of_sameWeight hτ' hp hpP
    (by omega) hk hz.2.1, hmono.trans hz.2.2⟩

def positiveTwoFamilyWidenedMomentResident
    (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    APrimeFirstCellCrossOrderWeight.targetWeight τ' p N 2 ω = 1 ∧
    weight τ' P N 2 ω = 1 ∧
    familyWidenedMomentAt τ' p N 2

/-- T521's resident and T520's target plateau are combined on the identical
sample of the identical sharp event. -/
theorem positiveTwoFamilyWidenedMomentResident_of_sameWeight {τ' : ℝ}
    (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P)
    (hresident :
      APrimeFirstCellFamilyLowMomentSameWeight.positiveTwoFamilyLowMomentResident
        τ' p P) : positiveTwoFamilyWidenedMomentResident τ' p P := by
  filter_upwards [hresident,
    APrimeFirstCellCrossOrderWeight.eventually_targetWeight_two_one_on_sharpCommonEvent τ',
    eventually_ge_atTop 1] with N hr htarget hN
  obtain ⟨ω, hω, hk, hvpos, hvle, hweight, hlow⟩ := hr
  have hwide := familyWidenedMomentAt_of_sameWeight hτ' hp hpP
    (show 0 < N by omega) hk hlow
  exact ⟨ω, hω, hk, hvpos, hvle, htarget ω hω p, hweight, hwide⟩

/-- T521's single parameter and sharp event supply every lower-order widened
moment, the zero branch, and a positive resident where both weights are one. -/
theorem exists_familyWidenedMoment_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ p P : ℕ,
      1 ≤ p → p ≤ P → 8000 ≤ P →
      (∀ N k ω, APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k ω ≤
        weight τ' P N k ω) ∧
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          τ' delta alpha N).Nonempty) ∧
      actualFamilyWidenedMoment τ' p ∧
      kZeroFamilyWidenedMoment τ' p ∧
      positiveTwoFamilyWidenedMomentResident τ' p P := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellFamilyLowMomentSameWeight.exists_familyLowMoment_sameWeight_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro p P hp hpP hP
  obtain ⟨hmeas, hprob, hne, hlow, hzero, hresident⟩ :=
    hall p P hp hpP hP
  exact ⟨fun N k ω =>
      APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hτ' N p P k ω hp hpP,
    hmeas, hprob, hne,
    actualFamilyWidenedMoment_of_sameWeight hτ' hp hpP hlow,
    kZeroFamilyWidenedMoment_of_sameWeight hτ' hp hpP hzero,
    positiveTwoFamilyWidenedMomentResident_of_sameWeight
      hτ' hp hpP hresident⟩

#print axioms momNormW_mono_weight
#print axioms familyWidenedMomentAt_of_sameWeight
#print axioms actualFamilyWidenedMoment_of_sameWeight
#print axioms kZeroFamilyWidenedMoment_of_sameWeight
#print axioms positiveTwoFamilyWidenedMomentResident_of_sameWeight
#print axioms exists_familyWidenedMoment_with_resident

end

end RBM.APrimeFirstCellFamilyWidenedMoment
