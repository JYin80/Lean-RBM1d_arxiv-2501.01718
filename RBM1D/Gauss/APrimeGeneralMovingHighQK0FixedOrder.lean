/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK0Repair

/-!
# T1159: fixed-order high moment at the general moving left endpoint

This exposes T1097's exact empty-prefix estimate with the moment order fixed
by the caller.  The target mesh, Gaussian sample, moving window, cutoff, and
power of N are unchanged.
-/

namespace RBM.APrimeGeneralMovingHighQK0FixedOrder

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- For every fixed `q ≥ 1` and `δ > 0`, the literal order-`q` Gaussian
expectation at the empty-prefix moving mesh point has the exact
`N^(δq/2)` rate, with its constant chosen before the eventual `N` threshold.
The pointwise selector in T1097 permits choosing its input order to be `q`;
its producer returns that same order. -/
theorem eventually_fixed_order_high_k0 {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ δ : ℝ, 0 < δ → ∀ q : ℕ, 1 ≤ q →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∫ ω, APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
          (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
          s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 0 ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (sample d) E D s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * q)
          ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  intro δ hδ q hq
  letI := B.isProbabilityMeasure
  obtain ⟨q₀, hqq₀, C₀, hC₀, hhigh⟩ :=
    APrimeGeneralMovingHighQK0Repair.eventually_selected_high_k0
      hE hD hs0 hst ht1 hc hreg hB δ δ hδ le_rfl q hq
  refine ⟨C₀ ^ ((q : ℝ) / (q₀ : ℝ)),
    Real.rpow_pos_of_pos hC₀ _, ?_⟩
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
    hq hqq₀ (χ := fun _ : Ω d => (1 : ℝ))
    (Y := Y) (by intro; norm_num) (by simpa using hInt q)
    (by simpa using hInt q₀) hC₀ hNreal hδ hhigh'
  simpa [Y, J, mesh, hWeight] using hlow

#print axioms eventually_fixed_order_high_k0

end
end RBM.APrimeGeneralMovingHighQK0FixedOrder
