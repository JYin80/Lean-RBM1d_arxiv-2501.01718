/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellTargetWeightWitness
import RBM1D.Gauss.APrimeSupportRunning

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

end RBM.APrimeFirstCellCrossOrderWeight
