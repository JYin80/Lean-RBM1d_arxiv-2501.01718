/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingLowMomentFirstTwo
import RBM1D.Gauss.APrimeGeneralMovingLowMomentEarly

/-!
# T1163: all low moments on the early general-moving mesh

Combine the accepted first-two-index estimate and the accepted later early
index estimate.  The resulting bound uses the same actual widened Gaussian
integral at every active index `k ≤ N^4`, including order zero.
-/

namespace RBM.APrimeGeneralMovingLowMomentAllEarly

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- One positive constant and one eventual set control the literal order-`p`
actual widened Gaussian moment at every active target-mesh index `k ≤ N^4`.
The case `p = 0` is the Gaussian probability integral of one; for positive
orders the statement combines the accepted `k = 0,1` and `2 ≤ k ≤ N^4`
producers without changing their sample, law, cutoff, weight, or endpoint. -/
theorem eventually_low_all_early
    {E D c δ₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∀ k : ℕ, k ≤ N ^ 4 →
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
              ∂(band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  intro δ hδ hδ₀ p
  by_cases hp0 : p = 0
  · subst p
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N k _hk4 _hkactive
    rw [APrimeGeneralMovingLowMomentTransfer.actual_zero_order_widened_integral]
    simp
  · have hp : 1 ≤ p := by omega
    obtain ⟨Csmall, hCsmall, hsmall⟩ :=
      APrimeGeneralMovingLowMomentFirstTwo.eventually_low_first_two
        hE hD hs0 hst ht1 hc hreg hB δ hδ hδ₀ p
    obtain ⟨Clate, hClate, hlate⟩ :=
      APrimeGeneralMovingLowMomentEarly.eventually_low_early_moment
        hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp
    refine ⟨Csmall + Clate, by positivity, ?_⟩
    filter_upwards [hsmall, hlate] with N hsmallN hlateN
    intro k hk4 hkactive
    have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by positivity
    by_cases hk0 : k = 0
    · subst k
      exact (hsmallN.1).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hClate.le) hpow)
    · by_cases hk1 : k = 1
      · subst k
        exact (hsmallN.2 hkactive).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hClate.le) hpow)
      · have hk2 : 2 ≤ k := by omega
        exact (hlateN k hk2 hk4 hkactive).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCsmall.le) hpow)

/-- Re-export the accepted nondegenerate T995 positive-cell witness at `k=2`.
It certifies that the shared context and the early later-index range are
jointly satisfiable with a genuinely active cell. -/
noncomputable abbrev nondegenerate_early_k2_witness :=
  APrimeGeneralMovingLowMomentEarly.nondegenerate_early_k2_witness

#print axioms eventually_low_all_early
#print axioms nondegenerate_early_k2_witness

end
end RBM.APrimeGeneralMovingLowMomentAllEarly
