/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCrossOrderWeight
import RBM1D.Gauss.APrimeFirstCellCanonicalPlateau

/-!
# T542: variable-delta first-cell target/canonical-weight interface

This module keeps the cutoff loss `delta` explicit.  It chooses the
high moment order needed by the later family maximum, compares the widened
target weight with the actual canonical weight with coefficient one, and
records nondegenerate zero- and positive-prefix branches on the literal
sharp common event.
-/

namespace RBM.APrimeFirstCellDeltaTargetWeight

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The explicit high order used to pay the later `L_N^2` family maximum. -/
noncomputable def highOrder (delta : ℝ) (p : ℕ) : ℕ :=
  max p ⌈20 / delta⌉₊

/-- The variable-`delta` widened target weight. -/
noncomputable def targetWeight (tauPrime delta : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  APrimeWeight.widenedW
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega)
    (fun _ => 0) (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    delta p N k

/-- The variable-`delta` actual canonical smooth weight at order `P`. -/
noncomputable def canonicalWeight (tauPrime delta : ℝ) (P N k : ℕ) : Ω d → ℝ :=
  APrimeFirstCellCanonicalPlateau.canonicalWeight tauPrime delta
    P N k

/-- The low order and the positive canonical order are both bounded by the
explicit high order. -/
theorem highOrder_bounds (delta : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    1 ≤ p ∧ p ≤ highOrder delta p ∧ 1 ≤ highOrder delta p := by
  exact ⟨hp, le_max_left _ _, hp.trans (le_max_left _ _)⟩

/-- The ceiling component is also below the chosen high order. -/
theorem ceil_le_highOrder (delta : ℝ) (p : ℕ) :
    ⌈20 / delta⌉₊ ≤ highOrder delta p :=
  le_max_right _ _

/-- T520's actual cross-order theorem gives coefficient-one domination for
the explicit order `max p ceil(20/delta)`. -/
theorem targetWeight_le_canonicalWeight {tauPrime delta : ℝ}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (N p k : ℕ) (omega : Ω d) (hp : 1 ≤ p) :
    targetWeight tauPrime delta p N k omega ≤
      canonicalWeight tauPrime delta (highOrder delta p) N k omega := by
  change APrimeWeight.widenedW
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega)
      (fun _ => 0) (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      delta p N k omega ≤
    APrimeSmoothWeightActual.weight d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 (highOrder delta p) N k
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega
  exact APrimeFirstCellCrossOrderWeight.exampleGrow_firstCell_cross_order
    hTau hDelta.le N p (highOrder delta p) k omega hp
      (highOrder_bounds delta hp).2.2

/-- The target weight has the exact empty-prefix value one. -/
theorem targetWeight_k_zero (tauPrime delta : ℝ) (p N : ℕ) (omega : Ω d) :
    targetWeight tauPrime delta p N 0 omega = 1 := by
  let J : ℕ → ℝ → Ω d → ℝ := fun N u omega =>
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega
  let s : ℕ → ℝ := fun _ => 0
  let t : ℕ → ℝ := firstCellT tauPrime
  let mesh : ℕ → ℝ := APrimeSmoothTransition.transitionMesh
  have hpref : omega ∈ Step2Bootstrap.prefNet J s mesh
      (fun N _ => (N : ℝ) ^ (2 * delta) * 1) N 0 := by
    intro j hj
    omega
  have hpiece : 1 ≤ APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta N 0 omega :=
    APrimeWeight.piecewiseW_dom_canonical
      (fun N u omega =>
        APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
          d 0 60 (fun _ => 0) N u omega)
      delta N 0 omega hpref
  have hwide := APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
    (J := J) (s := s) (t := t) (mesh := mesh)
    (by norm_num : 1 ≤ (1 : ℕ)) delta p N 0 omega
  have hupp := APrimeWeight.widenedW_le_one
    (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta p N 0 omega
  change APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta p N 0 omega = 1
  exact le_antisymm hupp (hpiece.trans hwide)

/-- T467's canonical weight has the same exact empty-prefix value. -/
theorem canonicalWeight_k_zero (tauPrime delta : ℝ) (P N : ℕ) (omega : Ω d) :
    canonicalWeight tauPrime delta P N 0 omega = 1 := by
  exact APrimeFirstCellCanonicalPlateau.canonicalWeight_k_zero
    tauPrime delta P N omega

/-- On every sample of the literal sharp common event, the variable-`delta`
target weight is one at the positive prefix `k = 2`, for every target order. -/
theorem eventually_targetWeight_two_one_on_sharpCommonEvent
    {tauPrime delta alpha : ℝ} (_hTau : 0 < tauPrime) (hDelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      ∀ p : ℕ, targetWeight tauPrime delta p N 2 omega = 1 := by
  filter_upwards [APrimeFirstCellCommon.eventually_norm_F₂
    (2 * delta) (by positivity)] with N hprefix omega homega p
  have hcommon : omega ∈ APrimeFirstCellMovingSupport.commonEvent tauPrime
      (APrimeFirstCellEGAllOutputRunning.sourceLoss alpha)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss alpha)
      (delta / 16) N := homega.2
  have hdyn := APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hcommon
  have hraw := APrimeSupportRunning.good_subset tauPrime
    (delta / 16) N hdyn
  have hvalues := hprefix omega hraw.1.1.1
  change
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N 0 omega ≤
        (N : ℝ) ^ (2 * delta) ∧
      Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N
          (APrimeSmoothTransition.transitionMesh N)⁻¹ omega ≤
        (N : ℝ) ^ (2 * delta) at hvalues
  have hpref : omega ∈ prefNet
      (fun N u omega =>
        Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega)
      (fun _ => 0) APrimeSmoothTransition.transitionMesh
      (fun N _ => (N : ℝ) ^ (2 * delta) * 1) N 2 := by
    intro j hj
    interval_cases j
    · simpa only [cutNetPt, Nat.cast_zero, zero_div, add_zero, mul_one] using
        hvalues.1
    · simpa only [cutNetPt, Nat.cast_one, zero_add, one_div, mul_one] using
        hvalues.2
  have hpiece := APrimeWeight.piecewiseW_dom_canonical
    (t := firstCellT tauPrime)
    (fun N u omega =>
      APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
        d 0 60 (fun _ => 0) N u omega)
    delta N 2 omega hpref
  have hwide := APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh)
    (J := fun N u omega =>
      Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega)
    (s := fun _ => 0) (t := firstCellT tauPrime)
    (mesh := APrimeSmoothTransition.transitionMesh)
    (by norm_num : 1 ≤ (1 : ℕ)) delta p N 2 omega
  exact le_antisymm
    (APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u omega =>
        Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u omega)
      (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh delta p N 2 omega)
    (hpiece.trans hwide)

/-- A positive `k = 2` resident of the literal sharp event, carrying the
target order, its explicit high order, and both coefficient-one plateaux on
one sample. -/
def positiveTwoWeightResident (tauPrime delta alpha : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧
    u2 ≤ firstCellT tauPrime N ∧
    firstCellT tauPrime N ≤ 1 / 2 ∧
    ∀ p : ℕ, 1 ≤ p →
      1 ≤ highOrder delta p ∧
      p ≤ highOrder delta p ∧
      targetWeight tauPrime delta p N 2 omega = 1 ∧
      canonicalWeight tauPrime delta (highOrder delta p) N 2 omega = 1

/-- T467's resident and the variable-`delta` target plateau give the two
weights on the identical event and sample. -/
theorem positiveTwoWeightResident_of_canonical
    {tauPrime delta alpha : ℝ}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (hresident :
      APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau
        tauPrime delta alpha) :
    positiveTwoWeightResident tauPrime delta alpha := by
  filter_upwards [hresident,
    eventually_targetWeight_two_one_on_sharpCommonEvent
      (alpha := alpha) hTau hDelta] with N hresidentN htarget
  dsimp only [APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau]
    at hresidentN
  obtain ⟨omega, homega, hk, hcanonical, hu2pos, hu2le, hTle,
      _hsource, _hJall, _hJ0, _hJu2⟩ := hresidentN
  refine ⟨omega, homega, hk, hu2pos, hu2le, hTle, ?_⟩
  intro p hp
  have hb := highOrder_bounds delta hp
  exact ⟨hb.2.2, hb.2.1, htarget omega homega p,
    hcanonical (highOrder delta p)⟩

/-- One first-cell parameter works before every admissible positive
`delta`.  The event is the literal sharp common event at
`alpha = delta/16`; all weight comparisons have coefficient one. -/
theorem exists_deltaTargetWeight_with_resident :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16) N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta (delta / 16)) ∧
        (∀ p : ℕ, 1 ≤ p →
          1 ≤ highOrder delta p ∧
          p ≤ highOrder delta p ∧
          ⌈20 / delta⌉₊ ≤ highOrder delta p ∧
          ∀ N k omega,
            targetWeight tauPrime delta p N k omega ≤
              canonicalWeight tauPrime delta (highOrder delta p) N k omega) ∧
        (∀ p N omega,
          targetWeight tauPrime delta p N 0 omega = 1) ∧
        (∀ P N omega,
          canonicalWeight tauPrime delta P N 0 omega = 1) ∧
        positiveTwoWeightResident tauPrime delta (delta / 16) := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellCanonicalPlateau.exists_sharpCommonEvent_with_canonical_plateau
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100
  have hAlpha : 0 < delta / 16 := by positivity
  obtain ⟨hmeas, hprob, hcanonical⟩ :=
    hall delta hDelta hDelta100 (delta / 16) hAlpha
  refine ⟨hmeas, hprob, ?_, ?_, ?_,
    positiveTwoWeightResident_of_canonical hTau hDelta hcanonical⟩
  · intro p hp
    have hb := highOrder_bounds delta hp
    exact ⟨hb.2.2, hb.2.1, ceil_le_highOrder delta p,
      fun N k omega =>
        targetWeight_le_canonicalWeight hTau hDelta N p k omega hp⟩
  · intro p N omega
    exact targetWeight_k_zero tauPrime delta p N omega
  · intro P N omega
    exact canonicalWeight_k_zero tauPrime delta P N omega

#print axioms highOrder_bounds
#print axioms ceil_le_highOrder
#print axioms targetWeight_le_canonicalWeight
#print axioms targetWeight_k_zero
#print axioms canonicalWeight_k_zero
#print axioms eventually_targetWeight_two_one_on_sharpCommonEvent
#print axioms positiveTwoWeightResident_of_canonical
#print axioms exists_deltaTargetWeight_with_resident

end
end RBM.APrimeFirstCellDeltaTargetWeight
