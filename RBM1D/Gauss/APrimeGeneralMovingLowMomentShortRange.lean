/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingLowMomentAllEarly
import RBM1D.Gauss.APrimeGeneralMovingLowMomentExtended
import RBM1D.Gauss.APrimeGeneralMovingLowMomentTransfer

/-!
# T1183: all low moments on the short-range general-moving mesh

Combine the accepted all-order early-range estimate with the accepted
positive-order estimate on the short extended range.  The order-zero branch
uses the public exact Gaussian producer.
-/

namespace RBM.APrimeGeneralMovingLowMomentShortRange

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- For each fixed admissible loss and every natural order, one constant and
one eventual set bound the literal actual widened Gaussian moment uniformly
for every active target-mesh index with the real-power upper bound
`(k : ℝ) ≤ N^(4+δ/2)`.  Order zero uses the exact probability integral; for
positive orders the early and short extended ranges are joined with one
constant. -/
theorem eventually_low_short_range
    {E D c δ₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∀ k : ℕ, (k : ℝ) ≤ (N : ℝ) ^ (4 + δ / 2) →
            k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
            ∫ ω,
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh D)) 1
                (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
                s t (APrimeGeneralMovingMesh.targetMesh D) δ p N k ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (sample d) E D s N
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^
                  (2 * p)
              ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  intro δ hδ hδ₀ p
  by_cases hp0 : p = 0
  · subst p
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N k _hkhi _hkactive
    rw [APrimeGeneralMovingLowMomentTransfer.actual_zero_order_widened_integral]
    simp
  · have hp : 1 ≤ p := by omega
    obtain ⟨Cearly, hCearly, hearly⟩ :=
      APrimeGeneralMovingLowMomentAllEarly.eventually_low_all_early
        hE hD hs0 hst ht1 hc hreg hB δ hδ hδ₀ p
    obtain ⟨Cext, hCext, hext⟩ :=
      APrimeGeneralMovingLowMomentExtended.eventually_low_extended_moment
        hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp
    refine ⟨Cearly + Cext, by positivity, ?_⟩
    filter_upwards [hearly, hext] with N hearlyN hextN
    intro k hkhi hkactive
    have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by positivity
    by_cases hEarly : k ≤ N ^ 4
    · exact (hearlyN k hEarly hkactive).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCext.le) hpow)
    · have hExtended : N ^ 4 < k := Nat.lt_of_not_ge hEarly
      exact (hextN k hExtended hkhi hkactive).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCearly.le) hpow)

/-- T1145's nonempty extended-range witness, with the active index
`k=N^4+1` eventually satisfying the real-power upper bound. -/
noncomputable abbrev nondegenerate_short_range_witness {δ : ℝ} (hδ : 0 < δ) :=
  APrimeGeneralMovingLowMomentExtended.nondegenerate_extended_witness hδ

#print axioms eventually_low_short_range
#print axioms nondegenerate_short_range_witness

end
end RBM.APrimeGeneralMovingLowMomentShortRange
