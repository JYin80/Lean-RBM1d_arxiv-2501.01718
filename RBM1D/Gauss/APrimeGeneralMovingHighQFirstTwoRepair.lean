/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK0Repair
import RBM1D.Gauss.APrimeGeneralMovingHighQK1Full

/-!
# T1135: one selected order for the first two moving mesh points

The empty prefix at `k=0` permits probability-space moment transfer from
T1097's returned order to the order selected by T1119.  The result concerns
only the first two cells and retains T1119's active-cell premise.
-/

namespace RBM.APrimeGeneralMovingHighQFirstTwoRepair

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- T1097 at input `q` returns an order `q₀ ≥ q`.  At the empty prefix,
Lyapunov transfer recovers the sharp exponent at the original fixed `q`. -/
private theorem eventually_fixed_high_k0 {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ δ : ℝ)
    (hδ : 0 < δ) (hδ₀ : δ ≤ δ₀) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∫ ω, APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
        (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 0 ω *
        |cutTrunc ((N : ℝ) ^ (2 * δ))
          (Step2Moment.jSnorm (sample d) E D s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * q)
        ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  letI := B.isProbabilityMeasure
  obtain ⟨q₀, hqq₀, C₀, hC₀, hhigh⟩ :=
    APrimeGeneralMovingHighQK0Repair.eventually_selected_high_k0
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ q hq
  refine ⟨C₀ ^ ((q : ℝ) / (q₀ : ℝ)), Real.rpow_pos_of_pos hC₀ _, ?_⟩
  filter_upwards [hhigh, eventually_ge_atTop (1 : ℕ)] with N hhighN hN
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (sample d) E D s N u ω
  let Y : Ω d → ℝ := fun ω =>
    cutTrunc ((N : ℝ) ^ (2 * δ)) (J N (cutNetPt s mesh N 0) ω)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNpos _
  have hJ0 : ∀ ω, 0 ≤ J N (cutNetPt s mesh N 0) ω := by
    intro ω
    rw [cutNetPt_zero]
    exact Step2Moment.jSnorm_nonneg (sample d) hE
      ((hst N).trans_lt (ht1 N)) ((hst N).trans_lt (ht1 N)) ω
  have hJm : Measurable (J N (cutNetPt s mesh N 0)) :=
    APrimeSlotFields.measurable_jSnorm (sample d) E D s N _
  have hInt (n : ℕ) : Integrable (fun ω => |Y ω| ^ (2 * n)) B.P := by
    exact integrable_cutTrunc_pow hθ hJ0 hJm.aestronglyMeasurable (2 * n)
  have hWeight (n : ℕ) (ω : Ω d) : APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ n N 0 ω = 1 := by
    have hr : 0 < APrimeWeight.canonicalR s t mesh N := by
      simp [APrimeWeight.canonicalR]
    have hz : softMax (APrimeWeight.canonicalR s t mesh N)
        (Finset.range 0) (fun j => J N (cutNetPt s mesh N j) ω) = 0 := by
      simp only [softMax, Finset.range_zero, Finset.sum_empty]
      exact Real.zero_rpow (ne_of_gt (by positivity :
        (0 : ℝ) < 1 / (2 * (APrimeWeight.canonicalR s t mesh N : ℝ))))
    have hprefix : APrimeWeight.prefixSoftW
        (APrimeWeight.canonicalR s t mesh N) J s mesh N 0
        (2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N) ω = 1 := by
      unfold APrimeWeight.prefixSoftW softW
      rw [hz]
      simp [Cutoff.cutChi_eq_one]
    simp [APrimeWeight.widenedW, hprefix]
  have hhigh' : ∫ ω, (1 : ℝ) ^ (2 * q₀) * |Y ω| ^ (2 * q₀) ∂B.P ≤
      C₀ * (N : ℝ) ^ (δ / 2 * (q₀ : ℝ)) := by
    simpa [Y, J, mesh, hWeight] using hhighN
  have hlow := APrimeGeneralMovingLowMomentTransfer.low_integral_of_high_integral
    hq hqq₀ (χ := fun _ : Ω d => (1 : ℝ)) (Y := Y)
    (by intro; norm_num) (by simpa using hInt q) (by simpa using hInt q₀)
    hC₀ hNreal hδ hhigh'
  simpa [Y, J, mesh, hWeight] using hlow

/-- The literal full Gaussian estimate at a common order for `k=0,1`.
The active-cell premise is meaningful only for `k=1`. -/
theorem eventually_selected_high_first_two
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ 32 ≤ 3 * δ * (q : ℝ) ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
          k ≤ 1 → k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
          ∫ ω, APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
            (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh D) δ q N k ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^ (2 * q)
            ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  intro δ hδ hδ₀ p hp
  obtain ⟨q, hpq, hthreshold, C₁, hC₁, hk1⟩ :=
    APrimeGeneralMovingHighQK1Full.eventually_selected_high_k1_full
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp
  obtain ⟨C₀, hC₀, hk0⟩ :=
    eventually_fixed_high_k0 hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ q
      (by omega)
  refine ⟨q, hpq, hthreshold, C₀ + C₁, by positivity, ?_⟩
  filter_upwards [hk0, hk1] with N hk0N hk1N
  intro k hk hkactive
  interval_cases k
  · exact hk0N.trans (by
      have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
      nlinarith [hC₁])
  · exact (hk1N hkactive).trans (by
      have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
      nlinarith [hC₀])

/-- The T995 model realizes the hypotheses and an eventually active first cell. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_selected_high_first_two
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingHighQFirstTwoRepair
