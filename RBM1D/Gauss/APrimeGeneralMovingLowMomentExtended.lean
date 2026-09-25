/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingLowMomentTransfer
import RBM1D.Gauss.APrimeGeneralMovingHighQExtendedFull

/-!
# T1175: low moments on the short extended mesh range

Transfer the accepted selected high-order full expectation to each fixed
positive order on the same Gaussian sample, cutoff, endpoint, and law. The
index range is `N^4 < k` and the real-power upper bound.
-/

namespace RBM.APrimeGeneralMovingLowMomentExtended

open Filter MeasureTheory Set Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- For each fixed `δ` and positive integer order `p`, the literal T999 low
moment bound holds uniformly over active target-mesh indices in the short
extended range `N^4 < k ≤ N^(4+δ/2)`. The selected high order is fixed before
eventual `N`. -/
theorem eventually_low_extended_moment
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∀ k : ℕ, N ^ 4 < k →
            (k : ℝ) ≤ (N : ℝ) ^ (4 + δ / 2) →
            k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
            ∫ ω,
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh D)) 1
                (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
                s t (APrimeGeneralMovingMesh.targetMesh D) δ p N k ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (sample d) E D s N
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^ (2 * p)
              ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  intro δ hδ hδ₀ p hp
  obtain ⟨q, hpq, hqThreshold, Chigh, hChigh, hevHigh⟩ :=
    APrimeGeneralMovingHighQExtendedFull.eventually_selected_high_extended_full
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (sample d) E D s N u ω
  let r := APrimeWeight.canonicalR s t mesh
  let χ : ℕ → ℕ → Ω d → ℝ := fun N k ω =>
    APrimeGeneralMovingLowMomentTransfer.baseCutoff r 1 J s t mesh δ N k ω
  let Y : ℕ → ℕ → Ω d → ℝ := fun N k ω =>
    cutTrunc ((N : ℝ) ^ (2 * δ)) (J N (cutNetPt s mesh N k) ω)
  haveI := B.isProbabilityMeasure
  have hJ0 : ∀ N u ω, 0 ≤ J N u ω := by
    intro N u ω
    exact div_nonneg
      (zero_le_one.trans (Step2Moment.one_le_jS (sample d) N u ω)) (by positivity)
  have hJm : ∀ N u, Measurable (J N u) := fun N u =>
    APrimeSlotFields.measurable_jSnorm (sample d) E D s N u
  have hchi0 : ∀ N k ω, 0 ≤ χ N k ω := by
    intro N k ω
    simp only [χ, APrimeGeneralMovingLowMomentTransfer.baseCutoff]
    split_ifs
    · exact softW_nonneg _ _ _ _
    · norm_num
  have hmeshpos : ∀ N, 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos D
  have hendpoint : ∀ N k,
      k ≤ cutNetTop s t mesh N → cutNetPt s mesh N k < 1 := by
    intro N k hk
    have hmem : cutNetPt s mesh N k ∈ Set.Icc (s N) (t N) :=
      netFinset_subset_Icc (hst N) (hmeshpos N) _ (cutNetPt_mem_netFinset hk)
    exact lt_of_le_of_lt hmem.2 (ht1 N)
  have hInt : ∀ N k p, 1 ≤ N → k ≤ cutNetTop s t mesh N →
      Integrable (fun ω => |χ N k ω * Y N k ω| ^ (2 * p)) B.P := by
    intro N k p hN hk
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNr _
    have hJendpoint : ∀ ω, 0 ≤ J N (cutNetPt s mesh N k) ω := by
      intro ω
      exact Step2Moment.jSnorm_nonneg (sample d) hE
        (by linarith [hs0 N, hst N, ht1 N]) (hendpoint N k hk) ω
    have h := Step2Bootstrap.integrable_weight_mul (P := B.P)
      (W := APrimeWeight.widenedW r 1 J s t mesh δ p N k)
      (g := J N (cutNetPt s mesh N k)) hθ
      (APrimeWeight.widenedW_nonneg r 1 J s t mesh δ p N k)
      (APrimeWeight.widenedW_le_one r 1 J s t mesh δ p N k)
      (APrimeWeight.widenedW_meas r 1 J s t mesh (fun N u => hJm N u)
        p δ N k)
      hJendpoint (hJm N _).aestronglyMeasurable (2 * p)
    have hweight : ∀ ω,
        APrimeWeight.widenedW r 1 J s t mesh δ p N k ω = χ N k ω ^ (2 * p) := by
      intro ω
      simpa [χ, APrimeGeneralMovingLowMomentTransfer.baseCutoff] using
        (APrimeGeneralMovingLowMomentTransfer.widenedW_eq_baseCutoff_pow
          r 1 J s t mesh δ p N k ω)
    convert h using 1
    · funext ω
      rw [hweight ω]
      simp [χ, Y, abs_mul, abs_of_nonneg (hchi0 N k ω), mul_pow]
  refine ⟨Chigh ^ ((p : ℝ) / (q : ℝ)),
    Real.rpow_pos_of_pos hChigh ((p : ℝ) / (q : ℝ)), ?_⟩
  filter_upwards [hevHigh, Filter.eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro k hklo hkhi hkactive
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hhigh := hN k hklo hkhi hkactive
  have hχhigh :
      ∫ ω, χ N k ω ^ (2 * q) * |Y N k ω| ^ (2 * q) ∂B.P ≤
        Chigh * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa only [APrimeGeneralMovingLowMomentTransfer.widenedW_eq_baseCutoff_pow,
      χ, Y, J, r, mesh] using hhigh
  have hlow := APrimeGeneralMovingLowMomentTransfer.low_integral_of_high_integral
    hp hpq (fun ω => hchi0 N k ω) (hInt N k p hN1 hkactive)
    (hInt N k q hN1 hkactive) hChigh hNreal hδ hχhigh
  have hweight : ∀ ω,
      APrimeWeight.widenedW r 1 J s t mesh δ p N k ω = χ N k ω ^ (2 * p) := by
    intro ω
    simpa [χ, APrimeGeneralMovingLowMomentTransfer.baseCutoff] using
      (APrimeGeneralMovingLowMomentTransfer.widenedW_eq_baseCutoff_pow
        r 1 J s t mesh δ p N k ω)
  simpa [Y, J, r, mesh, hweight] using hlow

/-- T1165/T1145 provide a compatible nondegenerate Gaussian model and an
active index `k=N^4+1`, so the short extended range is eventually nonempty. -/
noncomputable abbrev nondegenerate_extended_witness {δ : ℝ} (hδ : 0 < δ) :=
  APrimeGeneralMovingHighQExtendedFull.nondegenerate_extended_witness hδ

#print axioms eventually_low_extended_moment
#print axioms nondegenerate_extended_witness

end
end RBM.APrimeGeneralMovingLowMomentExtended
