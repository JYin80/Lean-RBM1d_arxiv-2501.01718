/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQAllEarlyFullFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQExtendedFullFixedOrder

/-!
# T1193: fixed-order full moment on the short range of all active indices

Glue the accepted early-range and extended-range fixed-order estimates. The
same exact full `k=0` premise, model, order, observable, and rate are retained.
-/

namespace RBM.APrimeGeneralMovingHighQShortRangeFullFixedOrder

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- From one exact full order-`q` `k=0` premise, obtain the full order-`q`
Gaussian moment uniformly over every active index up to `N^(4+δ/2)`. The
same fixed model, moving window, Gaussian sample, weight, cutoff, target mesh,
endpoint, and rate occur at every index. -/
theorem eventually_short_range_full_of_exact_k0 {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ) (q : ℕ) (hq : 1 ≤ q)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hbase : ∀ᶠ N : ℕ in atTop,
      ∫ ω,
        APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
          (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
          s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 0 ω *
        |cutTrunc ((N : ℝ) ^ (2 * δ))
          (Step2Moment.jSnorm (sample d) E D s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * q)
        ∂B.P ≤ C₀ * (N : ℝ) ^ (δ / 2 * (q : ℝ))) :
    ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
        ∀ k : ℕ, (k : ℝ) ≤ (N : ℝ) ^ (4 + δ / 2) →
          k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
          ∫ ω,
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh D) δ q N k ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^ (2 * q)
            ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  obtain ⟨C₁, hC₁, hearly⟩ :=
    APrimeGeneralMovingHighQAllEarlyFullFixedOrder.eventually_all_early_full_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hB hδ q hq C₀ hC₀ hbase
  obtain ⟨C₂, hC₂, hextended⟩ :=
    APrimeGeneralMovingHighQExtendedFullFixedOrder.eventually_extended_full_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hB hδ q hq C₀ hC₀ hbase
  let C : ℝ := C₁ + C₂
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ ≤ C := by dsimp [C]; linarith
  have hpow_nonneg : ∀ N : ℕ, 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    intro N
    positivity
  filter_upwards [hearly, hextended, eventually_ge_atTop (1 : ℕ)]
    with N hearlyN hextendedN hN
  intro k hkrange hactive
  by_cases hkearly : k ≤ N ^ 4
  · have hbound := hearlyN k hkearly hactive
    exact le_trans hbound
      (mul_le_mul_of_nonneg_right hC₁C (hpow_nonneg N))
  · have hkextended : N ^ 4 < k := by omega
    have hbound := hextendedN k hkextended hkrange hactive
    exact le_trans hbound
      (mul_le_mul_of_nonneg_right hC₂C (hpow_nonneg N))

/-- T1189/T1190's explicit compatible fixed-order `k=0` premise witness,
including a nonempty positive-index extended-range case. -/
noncomputable abbrev nondegenerate_short_range_fixed_order_witness :=
  @APrimeGeneralMovingHighQExtendedFullFixedOrder.nondegenerate_extended_fixed_order_witness

#print axioms eventually_short_range_full_of_exact_k0
#print axioms nondegenerate_short_range_fixed_order_witness

end
end RBM.APrimeGeneralMovingHighQShortRangeFullFixedOrder
