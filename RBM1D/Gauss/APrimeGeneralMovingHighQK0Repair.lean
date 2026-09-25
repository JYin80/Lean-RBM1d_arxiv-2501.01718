/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingLowMomentTransfer
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1097: the empty-prefix, moving-left-endpoint high moment

The zeroth net point is `s N`, and its widened prefix weight is identically one.
The model input is the existing `BoundsCore` initial law, with the same
nondegenerate witness as T995.  No later-cell estimate is asserted here.
-/

namespace RBM.APrimeGeneralMovingHighQK0Repair

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private noncomputable def level (δ : ℝ) (N : ℕ) : ℝ :=
  ((max 1 N : ℕ) : ℝ) ^ (2 * δ)

private noncomputable def initialCut (E D δ : ℝ) (s : ℕ → ℝ)
    (N : ℕ) (ω : Ω d) : ℝ :=
  cutTrunc (level δ N) (Step2Moment.jSnorm (sample d) E D s N (s N) ω)

private theorem level_pos (δ : ℝ) (N : ℕ) : 0 < level δ N := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < max 1 N by omega)) _

private theorem initialCut_momentDom {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 0 < D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ : ℝ) (hδ : 0 < δ) :
    Gauss.MomentDom B.P
      (fun N (_ : Unit) ω => initialCut E D δ s N ω)
      (fun _ _ => (1 : ℝ)) := by
  letI := B.isProbabilityMeasure
  let J : ℕ → Ω d → ℝ := fun N ω =>
    Step2Moment.jSnorm (sample d) E D s N (s N) ω
  have hJ0 : ∀ N ω, 0 ≤ J N ω := by
    intro N ω
    exact Step2Moment.jSnorm_nonneg (sample d) hE
      ((hst N).trans_lt (ht1 N)) ((hst N).trans_lt (ht1 N)) ω
  have hJm : ∀ N, Measurable (J N) := fun N =>
    APrimeSlotFields.measurable_jSnorm (sample d) E D s N (s N)
  have hdomJ : StochDom B.P (fun N (_ : Unit) ω => J N ω)
      (fun _ _ _ => (1 : ℝ)) :=
    APrimeSlotFields.stochDom_jSnorm_init_of_boundsCore
      (sample d) hE hst ht1 hreg.toCond272 hB D hD
  have hdom : StochDom B.P
      (fun N (_ : Unit) ω => initialCut E D δ s N ω)
      (fun _ _ _ => (1 : ℝ)) := by
    refine StochDom.of_subset hdomJ fun τ hτ => ⟨τ, hτ, ?_⟩
    exact Filter.Eventually.of_forall fun N ω hω => by
      obtain ⟨u, hu⟩ := hω
      refine ⟨u, ?_⟩
      exact lt_of_lt_of_le hu (cutTrunc_le_self (hJ0 N ω))
  have hY0 : ∀ N (_ : Unit) ω, 0 ≤ initialCut E D δ s N ω := by
    intro N _ ω
    exact cutTrunc_nonneg (hJ0 N ω)
  have hYm : ∀ N (_ : Unit), Measurable (initialCut E D δ s N) := by
    intro N _
    exact (continuous_cutTrunc (level δ N)).measurable.comp (hJm N)
  have hInt : ∀ p N (_ : Unit), Integrable
      (fun ω => |initialCut E D δ s N ω| ^ (2 * p)) B.P := by
    intro p N _
    exact integrable_cutTrunc_pow (level_pos δ N) (hJ0 N)
      (hJm N).aestronglyMeasurable (2 * p)
  let Env : ℕ → ℝ := fun N => 2 * level δ N
  have hEnv0 : ∀ N, 0 ≤ Env N := fun N => by
    dsimp [Env]
    exact mul_nonneg (by norm_num) (level_pos δ N).le
  have hEnv : ∀ N (_ : Unit) ω, initialCut E D δ s N ω ≤ Env N := by
    intro N _ ω
    exact cutTrunc_le_two_mul (level_pos δ N) (hJ0 N ω)
  have hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ (3 * δ) := by
    filter_upwards [eventually_le_rpow 2 hδ, eventually_ge_atTop 1]
      with N htwo hN
    have hm : max 1 N = N := max_eq_right hN
    have hpow0 : 0 ≤ (N : ℝ) ^ (2 * δ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    dsimp [Env, level]
    rw [hm]
    calc
      2 * (N : ℝ) ^ (2 * δ) ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (2 * δ) :=
        mul_le_mul_of_nonneg_right htwo hpow0
      _ = (N : ℝ) ^ (3 * δ) := by rw [← Real.rpow_add hNr]; ring
  exact Gauss.momentDom_of_stochDom_of_nonneg hY0 hYm hInt
    (fun _ _ => by norm_num) (B := 0) (by norm_num)
    (Filter.Eventually.of_forall fun _ _ => by simp)
    hEnv0 (Kenv := 3 * δ) (by linarith) hEnv hEnvpoly hdom

/-- The literal selected-order high moment at the empty-prefix point.  Here
`q=p` works; the selection and constant precede the eventual size threshold. -/
theorem eventually_selected_high_k0 {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∫ ω, APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
            (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 0 ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ω)| ^ (2 * q)
              ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  letI := B.isProbabilityMeasure
  intro δ hδ _ p _
  have hmd := initialCut_momentDom hE (by linarith : 0 < D)
    hs0 hst ht1 hc hreg hB δ hδ
  obtain ⟨C, hC, hCev⟩ := hmd (δ / 2) (by linarith) p
  refine ⟨p, le_rfl, C, hC, ?_⟩
  filter_upwards [hCev, eventually_ge_atTop 1] with N hN hN1
  have hm : max 1 N = N := max_eq_right hN1
  have hw : ∀ ω : Ω d, APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
      (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
      s t (APrimeGeneralMovingMesh.targetMesh D) δ p N 0 ω = 1 := by
    intro ω
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
  convert hN () using 1
  · apply integral_congr_ae
    filter_upwards [] with ω
    simp [hw, initialCut, level, hm, cutNetPt_zero]
  · simp

#print axioms eventually_selected_high_k0

/-- T995's genuine positive first cell realizes all initial-law assumptions
of the zeroth-point estimate on the same Gaussian model. -/
theorem positive_length_k0_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ δ, 0 < δ → δ ≤ (1 : ℝ) → ∀ p : ℕ, 1 ≤ p →
        ∃ q : ℕ, p ≤ q ∧ ∃ C > (0 : ℝ),
          ∀ᶠ N : ℕ in atTop,
            ∫ ω, APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) 0 60 s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh 60) δ q N 0 ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (sample d) 0 60 s N
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh 60) N 0) ω)| ^ (2 * q)
              ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ))) := by
  obtain ⟨c, hc, s, t, _hsEq, hs0, hst, ht1, hreg, hB, _hStep, hres⟩ :=
    APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness
  have hδw : 0 < min 1 (c / 100) / 2 := by positivity
  have hδwle : min 1 (c / 100) / 2 ≤ min 1 (c / 100) := by
    have := hδw
    linarith
  have hpositive : ∀ᶠ N : ℕ in atTop, s N < t N := by
    filter_upwards [hres _ hδw hδwle] with N hN
    exact hN.1
  exact ⟨c, hc, s, t, hpositive,
    eventually_selected_high_k0 (by norm_num) (by norm_num)
      hs0 hst ht1 hc hreg hB 1⟩

#print axioms positive_length_k0_witness

end
end RBM.APrimeGeneralMovingHighQK0Repair
