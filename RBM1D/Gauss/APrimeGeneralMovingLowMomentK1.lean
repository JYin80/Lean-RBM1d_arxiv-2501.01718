/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK1Full
import RBM1D.Gauss.APrimeGeneralMovingLowMomentTransfer

/-!
# T1131: literal low-p actual widened moment at the first positive cell

For the selected high order supplied by T1119, apply the same-measure,
same-cutoff Lyapunov inequality from T999 at the single index `k = 1`.
-/

namespace RBM.APrimeGeneralMovingLowMomentK1

open Filter MeasureTheory Set Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The selected high order from T1119 transfers to every positive order at
the same actual widened cutoff, endpoint, Gaussian sample, and target mesh.
The constant is selected before the eventual index.  Order zero is included
and has integral exactly one. -/
theorem eventually_selected_low_k1
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
          ∫ ω,
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh D) δ p N 1 ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * p)
            ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  intro δ hδ hδ₀ p
  by_cases hp : p = 0
  · subst p
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N hactive
    rw [APrimeGeneralMovingLowMomentTransfer.actual_zero_order_widened_integral]
    simp
  · have hp1 : 1 ≤ p := by omega
    obtain ⟨q, hpq, _hqThreshold, Cq, hCq, hHigh⟩ :=
      APrimeGeneralMovingHighQK1Full.eventually_selected_high_k1_full
        hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp1
    let mesh := APrimeGeneralMovingMesh.targetMesh D
    let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
      Step2Moment.jSnorm (sample d) E D s N u ω
    let r := APrimeWeight.canonicalR s t mesh
    let χ : ℕ → Ω d → ℝ := fun N ω =>
      APrimeGeneralMovingLowMomentTransfer.baseCutoff r 1 J s t mesh δ N 1 ω
    let Y : ℕ → Ω d → ℝ := fun N ω =>
      cutTrunc ((N : ℝ) ^ (2 * δ)) (J N (cutNetPt s mesh N 1) ω)
    letI := B.isProbabilityMeasure
    have hJ0 : ∀ N u ω, 0 ≤ J N u ω := by
      intro N u ω
      exact div_nonneg
        (zero_le_one.trans (Step2Moment.one_le_jS (sample d) N u ω)) (by positivity)
    have hJm : ∀ N u, Measurable (J N u) := fun N u =>
      APrimeSlotFields.measurable_jSnorm (sample d) E D s N u
    have hχ0 : ∀ N ω, 0 ≤ χ N ω := by
      intro N ω
      simp only [χ, APrimeGeneralMovingLowMomentTransfer.baseCutoff]
      split_ifs
      · exact softW_nonneg _ _ _ _
      · norm_num
    have hInt : ∀ (m N : ℕ), 1 ≤ N →
        Integrable (fun ω => |χ N ω * Y N ω| ^ (2 * m)) B.P := by
      intro m N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNr _
      have h := Step2Bootstrap.integrable_weight_mul (P := B.P)
        (W := APrimeWeight.widenedW r 1 J s t mesh δ m N 1)
        (g := J N (cutNetPt s mesh N 1)) hθ
        (APrimeWeight.widenedW_nonneg r 1 J s t mesh δ m N 1)
        (APrimeWeight.widenedW_le_one r 1 J s t mesh δ m N 1)
        (APrimeWeight.widenedW_meas r 1 J s t mesh
          (fun N u => hJm N u) m δ N 1)
        (hJ0 N _) (hJm N _).aestronglyMeasurable (2 * m)
      convert h using 1
      funext ω
      simp [Y, χ, APrimeGeneralMovingLowMomentTransfer.widenedW_eq_baseCutoff_pow,
        abs_mul, abs_of_nonneg (hχ0 N ω), mul_pow]
    refine ⟨Cq ^ ((p : ℝ) / (q : ℝ)),
      Real.rpow_pos_of_pos hCq ((p : ℝ) / (q : ℝ)), ?_⟩
    filter_upwards [hHigh, eventually_ge_atTop (1 : ℕ)]
      with N hHighN hN hactive
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hχp : ∀ ω, 0 ≤ χ N ω := hχ0 N
    have hχq : ∀ ω, 0 ≤ χ N ω := hχ0 N
    have hTransfer := APrimeGeneralMovingLowMomentTransfer.low_integral_of_high_integral
      hp1 hpq hχp (hInt p N hN) (hInt q N hN) hCq hNr hδ
      (by
        simpa [χ, Y, mesh, J, r,
          APrimeGeneralMovingLowMomentTransfer.widenedW_eq_baseCutoff_pow] using
          hHighN hactive)
    simpa [χ, Y, mesh, J, r,
      APrimeGeneralMovingLowMomentTransfer.widenedW_eq_baseCutoff_pow] using hTransfer

/-- T995's explicit same-resident witness: a positive first cell, the literal
common event, and positive actual smooth weight under its admissible schedule. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingHighQK1Full.nondegenerate_positive_cell_witness

#print axioms eventually_selected_low_k1
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingLowMomentK1
