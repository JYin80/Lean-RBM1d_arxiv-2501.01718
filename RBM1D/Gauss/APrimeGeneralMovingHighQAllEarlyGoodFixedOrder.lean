/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK1GoodFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQEarlyGoodFixedOrder

/-!
# T1171: fixed-order norm-good moments on all early active indices

Glue the exact full `k=0` premise to its norm-good restriction at `k=0`, the
fixed-order `k=1` transfer, and the fixed-order `2 ≤ k ≤ N^4` transfer. All
integrals retain the same order, weight, cutoff, Gaussian model, and endpoint.
-/

namespace RBM.APrimeGeneralMovingHighQAllEarlyGoodFixedOrder

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- Transfer one exact full order-`q` `k=0` moment bound to the literal
order-`q` integral restricted to the norm-good event, uniformly over every
active early index `0 ≤ k ≤ N^4`. The same `δ`, `q`, Gaussian sample, moving
window, target mesh, `widenedW`, and `cutTrunc` occur throughout. -/
theorem eventually_all_early_good_of_exact_k0 {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
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
    ∃ C₁ > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
        ∀ k : ℕ, k ≤ N ^ 4 →
          k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
          ∫ ω in APrimeGeneralMovingGoodMesh.good N,
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh D) δ q N k ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^ (2 * q)
            ∂B.P ≤ C₁ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  classical
  letI := B.isProbabilityMeasure
  obtain ⟨Ck1, hCk1, hk1⟩ :=
    APrimeGeneralMovingHighQK1GoodFixedOrder.eventually_k1_good_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hδ q hq C₀ hC₀ hbase
  obtain ⟨Cearly, hCearly, hearly⟩ :=
    APrimeGeneralMovingHighQEarlyGoodFixedOrder.eventually_early_good_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hδ q hq C₀ hC₀ hbase
  let C₁ : ℝ := C₀ + Ck1 + Cearly
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨C₁, hC₁, ?_⟩
  filter_upwards [hbase, hk1, hearly, eventually_ge_atTop 1] with
    N hbaseN hk1N hearlyN hN
  intro k hkhi hactive
  by_cases hk0 : k = 0
  · subst k
    let mesh := APrimeGeneralMovingMesh.targetMesh D
    let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
      Step2Moment.jSnorm (sample d) E D s N u ω
    let r := APrimeWeight.canonicalR s t mesh
    let θ : ℝ := (N : ℝ) ^ (2 * δ)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hθ : 0 < θ := Real.rpow_pos_of_pos hNpos _
    have hJ0 : ∀ ω, 0 ≤ J N (s N) ω := by
      intro ω
      exact Step2Moment.jSnorm_nonneg (sample d) hE
        ((hst N).trans_lt (ht1 N)) ((hst N).trans_lt (ht1 N)) ω
    have hJm : ∀ u, Measurable (J N u) := fun u =>
      APrimeSlotFields.measurable_jSnorm (sample d) E D s N u
    have hW0 : ∀ ω, 0 ≤ APrimeWeight.widenedW r 1 J s t mesh δ q N 0 ω :=
      APrimeWeight.widenedW_nonneg r 1 J s t mesh δ q N 0
    have hW1 : ∀ ω, APrimeWeight.widenedW r 1 J s t mesh δ q N 0 ω ≤ 1 :=
      APrimeWeight.widenedW_le_one r 1 J s t mesh δ q N 0
    have hWm : AEStronglyMeasurable
        (APrimeWeight.widenedW r 1 J s t mesh δ q N 0) B.P :=
      APrimeWeight.widenedW_meas r 1 J s t mesh
        (fun n u => APrimeSlotFields.measurable_jSnorm (sample d) E D s n u) q δ N 0
    let f : Ω d → ℝ := fun ω =>
      APrimeWeight.widenedW r 1 J s t mesh δ q N 0 ω *
        |cutTrunc θ (J N (s N) ω)| ^ (2 * q)
    have hfint : Integrable f B.P := by
      dsimp [f]
      exact Step2Bootstrap.integrable_weight_mul (P := B.P) hθ hW0 hW1 hWm
        hJ0 (hJm (s N)).aestronglyMeasurable (2 * q)
    have hfnonneg : ∀ ω, 0 ≤ f ω := by
      intro ω
      dsimp [f]
      exact mul_nonneg (hW0 ω) (pow_nonneg (abs_nonneg _) _)
    have hrestricted :
        ∫ ω in APrimeGeneralMovingGoodMesh.good N, f ω ∂B.P ≤
          ∫ ω, f ω ∂B.P := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall hfnonneg) hfint
    have hfull : ∫ ω, f ω ∂B.P ≤ C₀ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
      simpa [f, J, r, mesh, θ, cutNetPt_zero] using hbaseN
    have hCbound : C₀ ≤ C₁ := by dsimp [C₁]; linarith [hCk1, hCearly]
    have hrate : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
    have hresult := hrestricted.trans hfull
    calc
      ∫ ω in APrimeGeneralMovingGoodMesh.good N,
          APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
            (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 0 ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (sample d) E D s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * q)
          ∂B.P
          ≤ C₀ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
            simpa [f, J, r, mesh, θ, cutNetPt_zero] using hresult
      _ ≤ C₁ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_right hCbound hrate
  · by_cases hk1eq : k = 1
    · subst k
      have htop : 1 ≤ cutNetTop s t
          (APrimeGeneralMovingMesh.targetMesh D) N := by omega
      have hbound := hk1N htop
      have hCbound : Ck1 ≤ C₁ := by dsimp [C₁]; linarith [hC₀, hCearly]
      have hrate : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
      exact le_trans hbound (mul_le_mul_of_nonneg_right hCbound hrate)
    · have hklo : 2 ≤ k := by omega
      have hbound := hearlyN k hklo hkhi hactive
      have hCbound : Cearly ≤ C₁ := by dsimp [C₁]; linarith [hC₀, hCk1]
      have hrate : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
      exact le_trans hbound (mul_le_mul_of_nonneg_right hCbound hrate)

/-- Reuse T1157's explicit compatible fixed-order premise together with its
nondegenerate active `k=2` norm-good witness on the same moving Gaussian
window. -/
theorem nondegenerate_fixed_order_k0_premise_and_active_k2 {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ C₀ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∃ s t : ℕ → ℝ,
        (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
        Cond272Reg B 0 s t c ∧ BoundsCore (sample d) 0 s ∧
        (∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ APrimeGeneralMovingGoodMesh.good N,
            2 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N) ∧
        ∀ᶠ N : ℕ in atTop,
          ∫ ω,
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh 60) δ q N 0 ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) 0 60 s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh 60) N 0) ω)| ^
                (2 * q) ∂B.P ≤ C₀ * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  exact APrimeGeneralMovingHighQEarlyGoodFixedOrder.nondegenerate_fixed_order_k0_premise_witness
    hδ hδ1

#print axioms eventually_all_early_good_of_exact_k0
#print axioms nondegenerate_fixed_order_k0_premise_and_active_k2

end
end RBM.APrimeGeneralMovingHighQAllEarlyGoodFixedOrder
