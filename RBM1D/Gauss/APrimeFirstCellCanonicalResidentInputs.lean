/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCanonicalPlateau
import RBM1D.Gauss.APrimeFirstCellDriftBadPayment

/-!
# T471: one-event canonical resident inputs

The canonical `k = 2` resident from T467 is retained while the exact
generator bridge, sample regularity, and the paid moving drift estimate are
assembled at the same first-cell parameter and literal sharp common event.
-/

namespace RBM.APrimeFirstCellCanonicalResidentInputs

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def fixedDelta : ℝ :=
  APrimeFirstCellDriftBadPayment.fixedDelta

/-- The same T467 resident carries the exact canonical generator inequality
and T451 sample fields at every point of its closed moving interval. -/
def positiveCanonicalResidentInputs (τ' α : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' fixedDelta α N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    APrimeFirstCellCanonicalPlateau.canonicalWeight
      τ' fixedDelta p N 2 ω = 1 ∧
    let v := APrimeFirstCellSampleRegularity.endpoint N 2
    0 < v ∧
    v ≤ firstCellT τ' N ∧
    firstCellT τ' N ≤ 1 / 2 ∧
    ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) v,
      APrimeFirstCellGeneratorHle.generatorHle τ' fixedDelta 2 p N 2
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT τ') APrimeSmoothTransition.transitionMesh N) a r ∧
      APrimeFirstCellGeneratorHle.generatorHleAtSample τ' fixedDelta 2 p N 2
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT τ') APrimeSmoothTransition.transitionMesh N) a r ω ∧
      APrimeFirstCellSampleRegularity.GeneratorSampleRegularity p
        (APrimeFirstCellSampleRegularity.weight τ' fixedDelta p N 2)
        (APrimeFirstCellSampleRegularity.Y N 2 a r)
        (APrimeFirstCellSampleRegularity.G N 2 a r)
        (APrimeFirstCellSampleRegularity.Q N 2 a r)

theorem positiveCanonicalResidentInputs_of_plateau {τ' α : ℝ} {p : ℕ}
    (hτ' : 0 < τ') (hp : 1 ≤ p)
    (hresident : APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau
      τ' fixedDelta α) :
    positiveCanonicalResidentInputs τ' α p := by
  filter_upwards [hresident,
    APrimeFirstCellGeneratorHle.eventually_canonicalWeight_generatorHle
      (δ := fixedDelta) hτ' p hp,
    APrimeFirstCellSampleRegularity.eventually_actual_generator_sampleRegularity
      (δ := fixedDelta) hτ' p hp]
      with N hresidentN hhleN hregularN
  obtain ⟨ω, hω, hk, hweight, hvpos, hvle, hTle,
    _hsource, _hJall, _hJ0, _hJv⟩ := hresidentN
  refine ⟨ω, hω, hk, hweight p, hvpos, hvle, hTle, ?_⟩
  intro a r hr
  have hhle := hhleN 2 hk a r hr
  exact ⟨hhle, hhle ω, hregularN 2 hk a r hr⟩

/-- Exact empty-prefix boundary, including canonical weight one, the
generator bridge, sample fields, and the paid drift estimate at `r = 0`. -/
def canonicalZeroInputs (τ' α β : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
    APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
    (∀ ω : Ω d,
      APrimeFirstCellCanonicalPlateau.canonicalWeight
        τ' fixedDelta p N 0 ω = 1) ∧
    APrimeFirstCellGeneratorHle.generatorHle τ' fixedDelta 2 p N 0
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT τ') APrimeSmoothTransition.transitionMesh N) a 0 ∧
    APrimeFirstCellSampleRegularity.GeneratorSampleRegularity p
      (APrimeFirstCellSampleRegularity.weight τ' fixedDelta p N 0)
      (APrimeFirstCellSampleRegularity.Y N 0 a 0)
      (APrimeFirstCellSampleRegularity.G N 0 a 0)
      (APrimeFirstCellSampleRegularity.Q N 0 a 0) ∧
    momNormW (P d)
        (APrimeFirstCellSampleRegularity.weight τ' fixedDelta p N 0) p
        (APrimeFirstCellSampleRegularity.G N 0 a 0) ≤
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          fixedDelta (2 * α) N
            (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
        (N : ℝ) ^ (-β)

theorem canonicalZeroInputs_of_highProb {τ' α β : ℝ} {p : ℕ}
    (hτ' : 0 < τ') (hp : 1 ≤ p) (hβ : 0 < β)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        τ' fixedDelta α)) :
    canonicalZeroInputs τ' α β p := by
  filter_upwards [
    APrimeFirstCellDriftBadPayment.eventually_actualDriftNormPaid_k_zero
      hprob p hp hβ,
    eventually_ge_atTop (1 : ℕ)] with N hpaid hN
  intro a
  obtain ⟨hendpoint, _hweight, hdrift⟩ := hpaid a
  refine ⟨hendpoint, ?_,
    APrimeFirstCellGeneratorHle.canonicalWeight_generatorHle_k_zero
      τ' fixedDelta hp a,
    APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_k_zero
      (δ := fixedDelta) hτ' hp (by omega) a,
    hdrift⟩
  intro ω
  exact APrimeFirstCellCanonicalPlateau.canonicalWeight_k_zero
    τ' fixedDelta p N ω

/-- Closed one-event producer.  `α`, `p`, and `β` are fixed before every
eventual statement, and the only existential sample is T467's resident. -/
theorem exists_canonicalResidentInputs :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ α : ℝ, 0 < α →
      ∀ p : ℕ, 1 ≤ p →
      ∀ β : ℝ, 0 < β →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            τ' fixedDelta α N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            τ' fixedDelta α) ∧
        APrimeFirstCellDriftBadPayment.actualDriftNormPaid τ' α β p ∧
        canonicalZeroInputs τ' α β p ∧
        positiveCanonicalResidentInputs τ' α p := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellCanonicalPlateau.exists_sharpCommonEvent_with_canonical_plateau
  refine ⟨τ', hτ', ?_⟩
  intro α hα p hp β hβ
  have hδ : 0 < fixedDelta := by
    norm_num [fixedDelta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have hδ100 : fixedDelta ≤ 1 / 100 := by
    norm_num [fixedDelta, APrimeFirstCellDriftBadPayment.fixedDelta]
  obtain ⟨hmeas, hprob, hresident⟩ := hall fixedDelta hδ hδ100 α hα
  have habs :=
    APrimeFirstCellDriftAbsorbed.eventually_absorbed_drift_on_active_support
      hτ' hδ hδ100 (show 0 < 2 * α by positivity)
  have hweighted :=
    APrimeFirstCellDriftWeightedGood.weightedDriftGood_of_absorbed habs
  have hglobal :=
    APrimeFirstCellDriftGlobalPoly.eventually_globalMovingDriftPoly hτ'
  have hsplit := APrimeFirstCellDriftNormSplit.actualDriftNormSplit_of_inputs
    hτ' hp hweighted hglobal
  have hpay := APrimeFirstCellDriftBadPayment.eventually_badPayment_le
    hprob p hp β hβ
  have hpaid := APrimeFirstCellDriftBadPayment.actualDriftNormPaid_of_inputs
    hsplit hpay
  exact ⟨hmeas, hprob, hpaid,
    canonicalZeroInputs_of_highProb hτ' hp hβ hprob,
    positiveCanonicalResidentInputs_of_plateau hτ' hp hresident⟩

#print axioms positiveCanonicalResidentInputs_of_plateau
#print axioms canonicalZeroInputs_of_highProb
#print axioms exists_canonicalResidentInputs

end
end RBM.APrimeFirstCellCanonicalResidentInputs
