/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK0Repair
import RBM1D.Gauss.APrimeGeneralMovingLowMomentTransfer
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1143: all low orders at the empty-prefix general-moving endpoint

This module lowers the accepted selected high-order estimate at `k = 0` to
all positive orders, and treats order zero as the probability integral of one.
It does not claim any positive-cell or later-time estimate.
-/

namespace RBM.APrimeGeneralMovingLowMomentK0

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal empty-prefix Gaussian moment has the A-prime low-order exponent
for every natural order.  For positive `p`, the high order is selected before
the eventual threshold; order zero is handled separately. -/
theorem eventually_low_k0 {E D c δ₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∫ ω, APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
          (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
          s t (APrimeGeneralMovingMesh.targetMesh D) δ p N 0 ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (sample d) E D s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * p)
          ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  letI := B.isProbabilityMeasure
  intro δ hδ hδ₀ p
  by_cases hp : p = 0
  · subst p
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N
    rw [APrimeGeneralMovingLowMomentTransfer.actual_zero_order_widened_integral]
    simp
  · have hp1 : 1 ≤ p := by omega
    obtain ⟨q, hpq, C, hC, hhigh⟩ :=
      APrimeGeneralMovingHighQK0Repair.eventually_selected_high_k0
        hE (by omega : 60 ≤ D) hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp1
    have hqpos : 0 < q := by omega
    refine ⟨C ^ ((p : ℝ) / (q : ℝ)), Real.rpow_pos_of_pos hC _, ?_⟩
    filter_upwards [hhigh, eventually_ge_atTop 1] with N hhighN hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNr _
    let J : Ω d → ℝ := fun ω =>
      Step2Moment.jSnorm (sample d) E D s N (s N) ω
    let Y : Ω d → ℝ := fun ω => cutTrunc ((N : ℝ) ^ (2 * δ)) (J ω)
    have hJ0 : ∀ ω, 0 ≤ J ω := by
      intro ω
      exact Step2Moment.jSnorm_nonneg (sample d) hE
        ((hst N).trans_lt (ht1 N)) ((hst N).trans_lt (ht1 N)) ω
    have hJm : Measurable J := by
      exact APrimeSlotFields.measurable_jSnorm (sample d) E D s N (s N)
    have hInt : ∀ r : ℕ, Integrable (fun ω => |Y ω| ^ (2 * r)) B.P := by
      intro r
      exact integrable_cutTrunc_pow hθ hJ0 hJm.aestronglyMeasurable (2 * r)
    have hw : ∀ r : ℕ, ∀ ω : Ω d, APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
        (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh D) δ r N 0 ω = 1 := by
      intro r ω
      have hr : 0 < APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D) N := by
        simp [APrimeWeight.canonicalR]
      have hz : softMax
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D) N)
          (Finset.range 0)
          (fun j => Step2Moment.jSnorm (sample d) E D s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) ω) = 0 := by
        simp only [softMax, Finset.range_zero, Finset.sum_empty]
        exact Real.zero_rpow (ne_of_gt (by positivity :
          (0 : ℝ) < 1 / (2 * (APrimeWeight.canonicalR s t
            (APrimeGeneralMovingMesh.targetMesh D) N : ℝ))))
      have hprefix : APrimeWeight.prefixSoftW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D) N)
          (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
          s (APrimeGeneralMovingMesh.targetMesh D) N 0
          (2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N) ω = 1 := by
        unfold APrimeWeight.prefixSoftW softW
        rw [hz]
        simp [Cutoff.cutChi_eq_one]
      simp [APrimeWeight.widenedW, hprefix]
    have hhighY :
        ∫ ω, |Y ω| ^ (2 * q) ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
      calc
        ∫ ω, |Y ω| ^ (2 * q) ∂B.P =
            ∫ ω, APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 0 ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (sample d) E D s N
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * q)
              ∂B.P := by
                apply integral_congr_ae
                filter_upwards [] with ω
                simp [hw, Y, J, cutNetPt_zero]
        _ ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
              simpa [Y, J, cutNetPt_zero] using hhighN
    have htransfer :=
      APrimeGeneralMovingLowMomentTransfer.low_integral_of_high_integral
        hp1 hpq (χ := fun _ : Ω d => (1 : ℝ))
        (Y := Y) (by intro ω; norm_num)
        (by simpa [Y] using hInt p)
        (by simpa [Y] using hInt q)
        hC (N := N) (δ := δ) (by exact_mod_cast hN) hδ (by simpa using hhighY)
    have hmain :
        ∫ ω, |Y ω| ^ (2 * p) ∂B.P ≤
          C ^ ((p : ℝ) / (q : ℝ)) * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
      simpa [Y] using htransfer
    have htarget :
        ∫ ω, APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
          (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
          s t (APrimeGeneralMovingMesh.targetMesh D) δ p N 0 ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (sample d) E D s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * p)
          ∂B.P = ∫ ω, |Y ω| ^ (2 * p) ∂B.P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [hw, Y, J, cutNetPt_zero]
    rw [htarget]
    exact hmain

/-- A genuine positive first-cell T995 model also witnesses the assumptions
and nonempty moving window for this all-orders empty-prefix estimate. -/
theorem nondegenerate_low_k0_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ min 1 (c / 100) →
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm
                (sample d) 0 60 s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh 60) N) ω) ∧
      ∀ δ, 0 < δ → δ ≤ min 1 (c / 100) → ∀ p : ℕ,
        ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
          ∫ ω, APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t
              (APrimeGeneralMovingMesh.targetMesh 60)) 1
            (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh 60) δ p N 0 ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) 0 60 s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh 60) N 0) ω)| ^ (2 * p)
            ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, _hStep, hres⟩ :=
    APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness
  have hδw : 0 < min 1 (c / 100) / 2 := by positivity
  have hδwle : min 1 (c / 100) / 2 ≤ min 1 (c / 100) := by
    have hy : 0 ≤ min 1 (c / 100) := le_min (by norm_num) (by positivity)
    linarith
  have hwindow : ∀ᶠ N : ℕ in atTop, s N < t N := by
    filter_upwards [hres _ hδw hδwle] with N hN
    exact hN.1
  refine ⟨c, hc, s, t, ?_, hwindow, hres, ?_⟩
  · intro N
    exact hsEq N
  · intro δ hδ hδsmall p
    exact eventually_low_k0 (E := 0) (D := 60) (c := c)
      (δ₀ := min 1 (c / 100)) (by norm_num) (by norm_num)
      hs0 hst ht1 hc hreg hB δ hδ hδsmall p

#print axioms eventually_low_k0
#print axioms nondegenerate_low_k0_witness

end
end RBM.APrimeGeneralMovingLowMomentK0
