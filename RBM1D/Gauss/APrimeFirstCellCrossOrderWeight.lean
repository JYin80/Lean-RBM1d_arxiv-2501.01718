/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellTargetWeightWitness
import RBM1D.Gauss.APrimeSupportRunning
import RBM1D.Gauss.APrimeFirstCellQuantMoment

/-!
# T444: positive-order cross-order smooth-weight domination

The widened target weight may be taken at a lower positive moment order than
the canonical actual smooth weight.  Positive support of the former forces
the latter onto its order-independent plateau.  The zero-order target is
excluded.
-/

namespace RBM.APrimeFirstCellCrossOrderWeight

open Filter Gauss CutHypTheta

/-- Pointwise domination of a positive-order widened weight by a canonical
actual smooth weight at any positive order on the same Gaussian sample. -/
theorem widenedW_le_actualWeight_cross_order (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    (N p P k : ℕ) (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hp : 1 ≤ p) (_hP : 1 ≤ P) :
    APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ p N k ω ≤
      APrimeSmoothWeightActual.weight d E D δ s t mesh 2 P N k
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω := by
  let w := APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
    (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
    s t mesh δ p N k ω
  by_cases hw : w = 0
  · rw [show APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ p N k ω = 0 from hw]
    exact APrimeSmoothWeightActual.weight_nonneg d E D δ s t mesh 2 P N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω
  · have hw0 : 0 ≤ w := APrimeWeight.widenedW_nonneg
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω
    have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw)
    have hone := APrimeFirstCellHigherMomentCutoff.weight_eq_one_of_widenedW_pos
      d hE hδ ω hst ht hmesh hp P hwpos
    rw [hone]
    exact APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω

/-- First-cell specialization at the literal moving net and actual growing
Gaussian model.  It includes all active, inactive, small-size and empty-prefix
branches of the two piecewise weights. -/
theorem exampleGrow_firstCell_cross_order {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (N p P k : ℕ)
    (ω : Gauss.Ω Gauss.Dims.exampleGrow) (hp : 1 ≤ p) (hP : 1 ≤ P) :
    APrimeWeight.widenedW
        (APrimeWeight.canonicalR (fun _ => 0) (Gauss.firstCellT τ)
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u ω => Step2Moment.jSnorm
          (Gauss.sample Gauss.Dims.exampleGrow) 0 60 (fun _ => 0) N u ω)
        (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
        δ p N k ω ≤
      APrimeSmoothWeightActual.weight Gauss.Dims.exampleGrow 0 60 δ
        (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
        2 P N k
        (APrimeSmoothWeightActual.canonicalM Gauss.Dims.exampleGrow
          (fun _ => 0) (Gauss.firstCellT τ)
          APrimeSmoothTransition.transitionMesh N) ω := by
  exact widenedW_le_actualWeight_cross_order Gauss.Dims.exampleGrow
    (by norm_num) hδ N p P k ω
    (APrimeSupportRunning.firstT_bounds hτ N).1
    ((APrimeSupportRunning.firstT_bounds hτ N).2.trans_lt (by norm_num))
    (APrimeSupportRunning.mesh_pos N) hp hP

/-- A positive `k=2` first-cell resident: on the same zero scalar sample,
the lower-order widened weight and every positive-order canonical actual
weight are both one. -/
theorem eventually_positive_k2_resident {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ4 : δ < 1 / 4) :
    ∀ᶠ N : ℕ in atTop,
      let ω₀ := APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0
      0 < (APrimeSmoothTransition.transitionMesh N)⁻¹ ∧
      2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ)
        APrimeSmoothTransition.transitionMesh N ∧
      ∀ p P : ℕ, 1 ≤ p → 1 ≤ P →
        APrimeWeight.widenedW
            (APrimeWeight.canonicalR (fun _ => 0) (Gauss.firstCellT τ)
              APrimeSmoothTransition.transitionMesh) 1
            (fun N u ω => Step2Moment.jSnorm
              (Gauss.sample Gauss.Dims.exampleGrow) 0 60 (fun _ => 0) N u ω)
            (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
            δ p N 2 ω₀ = 1 ∧
          APrimeSmoothWeightActual.weight Gauss.Dims.exampleGrow 0 60 δ
            (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
            2 P N 2
            (APrimeSmoothWeightActual.canonicalM Gauss.Dims.exampleGrow
              (fun _ => 0) (Gauss.firstCellT τ)
              APrimeSmoothTransition.transitionMesh N) ω₀ = 1 := by
  filter_upwards [
    APrimeSmoothTransition.eventually_exampleGrow_transition hτ hδ hδ4,
    APrimeFirstCellTargetWeightWitness.eventually_exampleGrow_target_weights_one
      hτ hδ hδ4] with N htransition hweights
  dsimp only
  refine ⟨htransition.1, htransition.2.1, ?_⟩
  intro p P hp hP
  exact ⟨hweights.2.1 p hp, hweights.2.2 P hP⟩

#print axioms widenedW_le_actualWeight_cross_order
#print axioms exampleGrow_firstCell_cross_order
#print axioms eventually_positive_k2_resident

/-! ## T520: literal quantitative-moment weight and its same-event resident -/

open MeasureTheory Set Step2Bootstrap
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The literal target widened weight at the fixed first-cell parameters. -/
def targetWeight (τ' : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  APrimeWeight.widenedW
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh) 1
    (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u ω)
    (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
    (1 / 2000) p N k

theorem minkowski_delta_eq : APrimeFirstCellMinkowskiExact.delta = 1 / 2000 := rfl

/-- Exact specialization to T494's public actual canonical weight, for all
sizes, indices, and samples. The comparison has the requested direction. -/
theorem widenedW_le_minkowskiWeight {τ' : ℝ} (hτ' : 0 < τ')
    (N p P k : ℕ) (ω : Ω d) (hp : 1 ≤ p) (hpP : p ≤ P) :
    APrimeWeight.widenedW
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u ω)
        (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
        (1 / 2000) p N k ω ≤
      APrimeFirstCellMinkowskiExact.weight τ' P N k ω := by
  simpa only [APrimeFirstCellMinkowskiExact.weight,
    APrimeFirstCellMinkowskiExact.canonicalM, minkowski_delta_eq] using
    exampleGrow_firstCell_cross_order hτ' (by norm_num : (0 : ℝ) ≤ 1 / 2000)
      N p P k ω hp (hp.trans hpP)

/-- Positive target support forces the actual weight to one at every
moment order, by the order-independent cutoff plateau. -/
theorem minkowskiWeight_eq_one_of_targetWeight_pos {τ' : ℝ} (hτ' : 0 < τ')
    {p N k : ℕ} (P : ℕ) (ω : Ω d) (hp : 1 ≤ p)
    (hpos : 0 < targetWeight τ' p N k ω) :
    APrimeFirstCellMinkowskiExact.weight τ' P N k ω = 1 := by
  have hone := APrimeFirstCellHigherMomentCutoff.weight_eq_one_of_widenedW_pos
    d (by norm_num : |(0 : ℝ)| < 2) (by norm_num : (0 : ℝ) ≤ 1 / 2000)
    ω (APrimeSupportRunning.firstT_bounds hτ' N).1
    ((APrimeSupportRunning.firstT_bounds hτ' N).2.trans_lt (by norm_num))
    (APrimeSupportRunning.mesh_pos N) hp P hpos
  simpa only [APrimeFirstCellMinkowskiExact.weight,
    APrimeFirstCellMinkowskiExact.canonicalM, minkowski_delta_eq] using hone

/-- The empty-prefix branch of the literal actual weight is one. -/
theorem minkowskiWeight_k_zero (τ' : ℝ) (P N : ℕ) (ω : Ω d) :
    APrimeFirstCellMinkowskiExact.weight τ' P N 0 ω = 1 := by
  exact APrimeSmoothWeightActual.weight_zero_prefix d 0 60
    APrimeFirstCellMinkowskiExact.delta (fun _ => 0) (firstCellT τ')
    APrimeSmoothTransition.transitionMesh 2 P N
    (APrimeFirstCellMinkowskiExact.canonicalM τ' N)
    (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) ω

/-- Sizes below two are in the literal actual weight-one branch. -/
theorem minkowskiWeight_of_lt_two (τ' : ℝ) (P N k : ℕ) (ω : Ω d)
    (hN : N < 2) : APrimeFirstCellMinkowskiExact.weight τ' P N k ω = 1 := by
  simp only [APrimeFirstCellMinkowskiExact.weight, APrimeSmoothWeightActual.weight,
    show ¬ 2 ≤ N by omega, and_false, ↓reduceIte]

/-- On the very same sharp common event used by T509, both prefix values
lie in the ordinary target plateau. Hence every widened target order is one. -/
theorem eventually_targetWeight_two_one_on_sharpCommonEvent (τ' : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ'
        APrimeFirstCellQuantMoment.delta APrimeFirstCellQuantMoment.alpha N,
      ∀ p : ℕ, targetWeight τ' p N 2 ω = 1 := by
  filter_upwards [APrimeFirstCellCommon.eventually_norm_F₂
    (2 * (1 / 2000)) (by norm_num)] with N hprefix ω hω p
  have hcommon : ω ∈ APrimeFirstCellMovingSupport.commonEvent τ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss APrimeFirstCellQuantMoment.alpha)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss APrimeFirstCellQuantMoment.alpha)
      (APrimeFirstCellQuantMoment.delta / 16) N := hω.2
  have hdyn := APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hcommon
  have hraw := APrimeSupportRunning.good_subset τ'
    (APrimeFirstCellQuantMoment.delta / 16) N hdyn
  have hvalues := hprefix ω hraw.1.1.1
  change
    Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N 0 ω ≤
        (N : ℝ) ^ (2 * (1 / 2000 : ℝ)) ∧
      Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N
          (APrimeSmoothTransition.transitionMesh N)⁻¹ ω ≤
        (N : ℝ) ^ (2 * (1 / 2000 : ℝ)) at hvalues
  have hpref : ω ∈ prefNet
      (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u ω)
      (fun _ => 0) APrimeSmoothTransition.transitionMesh
      (fun N _ => (N : ℝ) ^ (2 * (1 / 2000 : ℝ)) * 1) N 2 := by
    intro j hj
    interval_cases j
    · simpa only [cutNetPt, Nat.cast_zero, zero_div, add_zero, mul_one] using hvalues.1
    · simpa only [cutNetPt, Nat.cast_one, zero_add, one_div, mul_one] using hvalues.2
  have hpiece := APrimeWeight.piecewiseW_dom_canonical
    (t := firstCellT τ')
    (fun N u ω => APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
      d 0 60 (fun _ => 0) N u ω) (1 / 2000) N 2 ω hpref
  have hwide := APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh)
    (J := fun N u ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u ω)
    (s := fun _ => 0) (t := firstCellT τ')
    (mesh := APrimeSmoothTransition.transitionMesh)
    (by norm_num : 1 ≤ (1 : ℕ)) (1 / 2000) p N 2 ω
  exact le_antisymm
    (APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N u ω)
      (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
      (1 / 2000) p N 2 ω)
    (hpiece.trans hwide)

/-- A T509 resident carrying both target and actual weights equal to one
on its original event, sample, and positive endpoint. -/
def positiveTwoCrossOrderResident (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ'
        APrimeFirstCellQuantMoment.delta APrimeFirstCellQuantMoment.alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < APrimeFirstCellMinkowskiExact.endpoint N 2 ∧
    APrimeFirstCellMinkowskiExact.endpoint N 2 ≤ firstCellT τ' N ∧
    targetWeight τ' p N 2 ω = 1 ∧
    APrimeFirstCellMinkowskiExact.weight τ' P N 2 ω = 1 ∧
    ∀ a : LoopArg (d.L N) 2, APrimeFirstCellQuantMoment.quantMomentAt τ' P N 2 a

theorem positiveTwoCrossOrderResident_of_quant {τ' : ℝ} (p : ℕ) {P : ℕ}
    (hresident : APrimeFirstCellQuantMoment.positiveTwoQuantMomentResident τ' P) :
    positiveTwoCrossOrderResident τ' p P := by
  filter_upwards [hresident, eventually_targetWeight_two_one_on_sharpCommonEvent τ']
    with N hresidentN htarget
  obtain ⟨ω, hω, hk, hvpos, hvle, hweight, hquant⟩ := hresidentN
  exact ⟨ω, hω, hk, hvpos, hvle, htarget ω hω p, hweight, hquant⟩

/-- T509's single parameter and sharp common event supply the actual
cross-order comparison and a nonempty target plateau at every fixed pair
of positive moment orders in the requested range. -/
theorem exists_cross_order_with_quantMoment_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ p P : ℕ, 1 ≤ p → p ≤ P →
      (∀ N k ω, targetWeight τ' p N k ω ≤
        APrimeFirstCellMinkowskiExact.weight τ' P N k ω) ∧
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ'
          APrimeFirstCellQuantMoment.delta APrimeFirstCellQuantMoment.alpha N)) ∧
      HighProb (Gauss.P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ'
        APrimeFirstCellQuantMoment.delta APrimeFirstCellQuantMoment.alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ'
          APrimeFirstCellQuantMoment.delta APrimeFirstCellQuantMoment.alpha N).Nonempty) ∧
      APrimeFirstCellQuantMoment.actualQuantMoment τ' P ∧
      APrimeFirstCellQuantMoment.kZeroQuantMoment τ' P ∧
      positiveTwoCrossOrderResident τ' p P := by
  obtain ⟨τ', hτ', hall⟩ := APrimeFirstCellQuantMoment.exists_quantMoment_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro p P hp hpP
  obtain ⟨hmeas, hprob, hne, hquant, hzero, hresident⟩ := hall P (hp.trans hpP)
  exact ⟨fun N k ω => widenedW_le_minkowskiWeight hτ' N p P k ω hp hpP,
    hmeas, hprob, hne, hquant, hzero, positiveTwoCrossOrderResident_of_quant p hresident⟩

#print axioms minkowski_delta_eq
#print axioms widenedW_le_minkowskiWeight
#print axioms minkowskiWeight_eq_one_of_targetWeight_pos
#print axioms minkowskiWeight_k_zero
#print axioms minkowskiWeight_of_lt_two
#print axioms eventually_targetWeight_two_one_on_sharpCommonEvent
#print axioms positiveTwoCrossOrderResident_of_quant
#print axioms exists_cross_order_with_quantMoment_resident

end

end RBM.APrimeFirstCellCrossOrderWeight
