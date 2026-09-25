/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK1FullFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQEarlyFullFixedOrder

/-!
# T1179: full fixed-order high moment on all early active mesh points

Glue the literal full `k=0` premise, the accepted full `k=1` estimate, and the
accepted full `2 ≤ k ≤ N^4` estimate. The order, rate, sample, weight, cutoff,
mesh, endpoint sequence, and Gaussian law stay fixed throughout.
-/

namespace RBM.APrimeGeneralMovingHighQAllEarlyFullFixedOrder

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- From one exact full order-`q` `k=0` premise, obtain the full order-`q`
Gaussian moment uniformly over every active early index `0 ≤ k ≤ N^4`. The
same fixed `δ`, `q`, model, moving window, Gaussian sample, weight, cutoff,
target mesh, endpoint, and rate occur at every index. -/
theorem eventually_all_early_full_of_exact_k0 {E D c δ : ℝ} {s t : ℕ → ℝ}
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
        ∀ k : ℕ, k ≤ N ^ 4 →
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
  obtain ⟨C₁, hC₁, hk1⟩ :=
    APrimeGeneralMovingHighQK1FullFixedOrder.eventually_k1_full_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hB hδ q hq C₀ hC₀ hbase
  obtain ⟨C₂, hC₂, hearly⟩ :=
    APrimeGeneralMovingHighQEarlyFullFixedOrder.eventually_early_full_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hB hδ q hq C₀ hC₀ hbase
  let C : ℝ := C₀ + C₁ + C₂
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ ≤ C := by dsimp [C]; linarith
  have hpow_nonneg : ∀ N : ℕ, 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    intro N
    positivity
  filter_upwards [hbase, hk1, hearly] with N hbaseN hk1N hearlyN
  intro k hkmax hactive
  by_cases hkzero : k = 0
  · subst k
    have hbound := hbaseN
    exact le_trans hbound
      (mul_le_mul_of_nonneg_right hC₀C (hpow_nonneg N))
  · by_cases hkone : k = 1
    · subst k
      have hbound := hk1N hactive
      exact le_trans hbound
        (mul_le_mul_of_nonneg_right hC₁C (hpow_nonneg N))
    · have hklo : 2 ≤ k := by omega
      have hbound := hearlyN k hklo hkmax hactive
      exact le_trans hbound
        (mul_le_mul_of_nonneg_right hC₂C (hpow_nonneg N))

/-- T1157's explicit compatible full `k=0` premise witness, including a
nondegenerate active `k=2` sample in the same moving Gaussian model. -/
noncomputable abbrev nondegenerate_fixed_order_k0_premise_witness :=
  @APrimeGeneralMovingHighQEarlyGoodFixedOrder.nondegenerate_fixed_order_k0_premise_witness

#print axioms eventually_all_early_full_of_exact_k0
#print axioms nondegenerate_fixed_order_k0_premise_witness

end
end RBM.APrimeGeneralMovingHighQAllEarlyFullFixedOrder
