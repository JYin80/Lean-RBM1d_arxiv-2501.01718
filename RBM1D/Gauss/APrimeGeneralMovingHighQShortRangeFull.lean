/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK0FixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQK1FullFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQEarlyFullFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQExtendedFull

/-!
# T1181: selected-order full Gaussian moment on the short active range

Select the order once from T1165. At that same order, combine the exact
fixed-order k=0 producer with the k=1 and early-index transfers, and use the
selected-order extended-range estimate above N^4. The resulting constant and
eventual threshold are uniform over every active short-range index.
-/

namespace RBM.APrimeGeneralMovingHighQShortRangeFull

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

set_option maxHeartbeats 1000000 in
-- The four producer outputs and four-way index split need a larger heartbeat budget.
/-- For each fixed admissible loss and input order, use the single order
selected by T1165 to bound the full literal T999 Gaussian expectation at every
active mesh index in `(k : ℝ) ≤ N^(4+δ/2)`. This joins k=0, k=1,
`2 ≤ k ≤ N^4`, and the extended strip `N^4 < k` without changing the order,
observable, law, cutoff, mesh, or rate. -/
theorem eventually_selected_high_short_range_full
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ 32 ≤ 3 * δ * (q : ℝ) ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∀ k : ℕ, k ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh D) N →
            (k : ℝ) ≤ (N : ℝ) ^ (4 + δ / 2) →
            ∫ ω,
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh D)) 1
                (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
                s t (APrimeGeneralMovingMesh.targetMesh D) δ q N k ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (sample d) E D s N
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^ (2 * q)
              ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  intro δ hδ hδ₀ p hp
  obtain ⟨q, hpq, hqThreshold, Cext, hCext, hext⟩ :=
    APrimeGeneralMovingHighQExtendedFull.eventually_selected_high_extended_full
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp
  have hq : 1 ≤ q := hp.trans hpq
  obtain ⟨C₀, hC₀, hk0⟩ :=
    APrimeGeneralMovingHighQK0FixedOrder.eventually_fixed_order_high_k0
      hE hD hs0 hst ht1 hc hreg hB δ hδ q hq
  obtain ⟨C₁, hC₁, hk1⟩ :=
    APrimeGeneralMovingHighQK1FullFixedOrder.eventually_k1_full_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hB hδ q hq C₀ hC₀ hk0
  obtain ⟨Cearly, hCearly, hearly⟩ :=
    APrimeGeneralMovingHighQEarlyFullFixedOrder.eventually_early_full_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hB hδ q hq C₀ hC₀ hk0
  let C := C₀ + C₁ + Cearly + Cext
  have hC : 0 < C := by dsimp [C]; linarith [hC₀, hC₁, hCearly, hCext]
  refine ⟨q, hpq, hqThreshold, C, hC, ?_⟩
  filter_upwards [hk0, hk1, hearly, hext, eventually_ge_atTop (1 : ℕ)]
      with N hk0N hk1N hearlyN hextN hN
  intro k hkActive hkUpper
  have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith [hC₁, hCearly, hCext]
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith [hC₀, hCearly, hCext]
  have hCearlyC : Cearly ≤ C := by dsimp [C]; linarith [hC₀, hC₁, hCext]
  have hCextC : Cext ≤ C := by dsimp [C]; linarith [hC₀, hC₁, hCearly]
  by_cases hk0' : k = 0
  · subst k
    calc
      _ ≤ C₀ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := hk0N
      _ ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hC₀C hpow
  · by_cases hk1' : k = 1
    · subst k
      calc
        _ ≤ C₁ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := hk1N hkActive
        _ ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₁C hpow
    · have hkTwo : 2 ≤ k := by omega
      by_cases hkle : k ≤ N ^ 4
      · calc
          _ ≤ Cearly * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
            hearlyN k hkTwo hkle hkActive
          _ ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_right hCearlyC hpow
      · have hkFar : N ^ 4 < k := by omega
        calc
          _ ≤ Cext * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
            hextN k hkFar hkUpper hkActive
          _ ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_right hCextC hpow

/-- T1145's explicit witness with `k=N^4+1` shows that the extended strip,
and hence this short-range index set, is nonempty in a nondegenerate Gaussian
model. -/
noncomputable abbrev nonempty_extended_index_witness {δ : ℝ} (hδ : 0 < δ) :=
  APrimeGeneralMovingHighQExtendedFull.nondegenerate_extended_witness hδ

#print axioms eventually_selected_high_short_range_full
#print axioms nonempty_extended_index_witness

end
end RBM.APrimeGeneralMovingHighQShortRangeFull
