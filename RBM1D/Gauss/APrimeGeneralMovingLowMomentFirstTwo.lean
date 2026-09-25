/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingLowMomentK0
import RBM1D.Gauss.APrimeGeneralMovingLowMomentK1

/-!
# T1155: common low-order bound at the first two general-moving indices

The empty prefix and the first positive cell use the same parameters, Gaussian
sample, target mesh, endpoint, cutoff, and probability law.  The estimate is
uniform over these two indices, with the positive-cell estimate conditional
on that cell being active.
-/

namespace RBM.APrimeGeneralMovingLowMomentFirstTwo

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- One constant controls the literal widened Gaussian low-order moments at
`k = 0` and at the active first positive index `k = 1`.  The order-zero case
is included.  All parameters and the underlying observable are shared by the
two endpoint estimates. -/
theorem eventually_low_first_two
    {E D c δ₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        (∫ ω, APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t
              (APrimeGeneralMovingMesh.targetMesh D)) 1
            (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh D) δ p N 0 ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (sample d) E D s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * p)
          ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) ∧
        (1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
          ∫ ω, APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh D) δ p N 1 ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * p)
            ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) := by
  intro δ hδ hδ₀ p
  obtain ⟨C0, hC0, hK0⟩ :=
    APrimeGeneralMovingLowMomentK0.eventually_low_k0
      hE hD hs0 hst ht1 hc hreg hB δ hδ hδ₀ p
  obtain ⟨C1, hC1, hK1⟩ :=
    APrimeGeneralMovingLowMomentK1.eventually_selected_low_k1
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p
  refine ⟨C0 + C1, by positivity, ?_⟩
  filter_upwards [hK0, hK1] with N h0 h1
  constructor
  · have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by positivity
    exact h0.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC1.le) hpow)
  · intro hactive
    have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by positivity
    exact (h1 hactive).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC0.le) hpow)

/-- T995's same-resident, positive-first-cell witness for simultaneous
satisfiability of the common moving-window context. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingLowMomentK1.nondegenerate_positive_cell_witness

#print axioms eventually_low_first_two
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingLowMomentFirstTwo
