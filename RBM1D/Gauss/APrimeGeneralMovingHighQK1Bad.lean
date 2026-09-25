/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGoodMesh
import RBM1D.Gauss.APrimeGeneralMovingHighQK0Repair

/-!
# T1105: the complementary event contribution at the first positive mesh point

For any fixed order `q`, the literal Gaussian endpoint integrand on `goodᶜ` is paid for by
`HighProb good` and the deterministic `2 N^(2δ)` cutoff envelope.  The decay exponent is chosen
after `δ` and `q`; it does not depend on the eventual value of `N`.
-/

namespace RBM.APrimeGeneralMovingHighQK1Bad

open Filter MeasureTheory Set Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- For fixed `δ,q`, any sufficiently strong polynomial tail of the concrete good event pays
for the order-`q` truncated endpoint moment on its complement.  This keeps the literal
`widenedW`, `cutTrunc`, `jSnorm`, `cutNetPt`, and Gaussian measure. -/
theorem eventually_bad_k1_for_order
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (_hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ) (q : ℕ) (hq : 1 ≤ q) :
    ∀ᶠ N : ℕ in atTop,
      ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ,
        APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
          (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
          s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω *
        |cutTrunc ((N : ℝ) ^ (2 * δ))
          (Step2Moment.jSnorm (sample d) E D s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q)
        ∂B.P ≤ 2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  letI := B.isProbabilityMeasure
  have hdecay : 0 < (7 / 2 : ℝ) * δ * (q : ℝ) := by positivity
  have hprob := APrimeGeneralMovingGoodMesh.highProb_good ((7 / 2 : ℝ) * δ * (q : ℝ)) hdecay
  have hmesh : ∀ N, 0 < APrimeGeneralMovingMesh.targetMesh D N :=
    APrimeGeneralMovingMesh.targetMesh_pos D
  have hendpoint : ∀ᶠ N : ℕ in atTop,
      cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1 < 1 := by
    filter_upwards [APrimeGeneralMovingWindowFloor.eventually_endpoint_floor
        hE hs0 hst ht1 hc hreg,
      APrimeGeneralMovingMesh.eventually_targetMesh_eq D, eventually_ge_atTop 2] with
      N hfloor hmeshEq hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < N := by linarith
    have hNreal : (1 : ℝ) ≤ N := le_of_lt hNr
    have hexp : (2 : ℝ) ≤ 4 * D + 18 := by linarith [hD]
    have hmeshLower : (N : ℝ) ^ (2 : ℝ) ≤
        APrimeGeneralMovingMesh.targetMesh D N := by
      rw [hmeshEq]
      exact Real.rpow_le_rpow_of_exponent_le hNreal hexp
    have hrecip : (1 : ℝ) / APrimeGeneralMovingMesh.targetMesh D N ≤
        1 / (N : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (hmesh N) (by positivity : 0 < (N : ℝ) ^ 2)).2
      simpa only [one_mul, mul_one, Real.rpow_ofNat] using hmeshLower
    have hstrict : 1 / (N : ℝ) ^ 2 < 1 / (N : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)
        (by positivity : 0 < (N : ℝ))).2
      nlinarith
    have hNinv : (1 : ℝ) / N = (N : ℝ)⁻¹ := by simp [one_div]
    have hdiv : (1 : ℝ) / APrimeGeneralMovingMesh.targetMesh D N < 1 - t N :=
      lt_of_le_of_lt hrecip (lt_of_lt_of_le hstrict (by simpa [hNinv] using hfloor.1))
    rw [CutHypTheta.cutNetPt]
    norm_num
    have hdiv' : (APrimeGeneralMovingMesh.targetMesh D N)⁻¹ < 1 - t N := by
      rw [← one_div]
      exact hdiv
    linarith [hdiv', hst N]
  have hJm : ∀ N, Measurable (fun ω : Ω d => Step2Moment.jSnorm
      (sample d) E D s N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω) := by
    intro N
    exact APrimeSlotFields.measurable_jSnorm (sample d) E D s N
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1)
  filter_upwards [hprob, hendpoint, eventually_ge_atTop 1] with N hprobN hEndN hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNpos _
  have hslt : s N < 1 := by linarith [hs0 N, hst N, ht1 N]
  have hJ0 : ∀ ω, 0 ≤ Step2Moment.jSnorm (sample d) E D s N
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω := by
    intro ω
    exact Step2Moment.jSnorm_nonneg (sample d) hE hslt hEndN ω
  have hmeasure : (B.P).real (APrimeGeneralMovingGoodMesh.good N)ᶜ ≤
      (N : ℝ) ^ (-((7 / 2 : ℝ) * δ * (q : ℝ))) := by
    rw [MeasureTheory.measureReal_def]
    calc
      (B.P (APrimeGeneralMovingGoodMesh.good N)ᶜ).toReal ≤
          (ENNReal.ofReal ((N : ℝ) ^ (-((7 / 2 : ℝ) * δ * (q : ℝ))))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hprobN
      _ = (N : ℝ) ^ (-((7 / 2 : ℝ) * δ * (q : ℝ))) :=
        ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)
  let W : Ω d → ℝ := fun ω => APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
      (fun n u ω => Step2Moment.jSnorm (sample d) E D s n u ω)
      s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω
  let Jval : Ω d → ℝ := fun ω => Step2Moment.jSnorm (sample d) E D s N
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact APrimeWeight.widenedW_nonneg
      (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
      (fun n u ω => Step2Moment.jSnorm (sample d) E D s n u ω)
      s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω
  have hW1 : ∀ ω, W ω ≤ 1 := by
    intro ω
    exact APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
      (fun n u ω => Step2Moment.jSnorm (sample d) E D s n u ω)
      s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω
  have hWm : AEStronglyMeasurable W B.P := by
    exact APrimeWeight.widenedW_meas (P := B.P)
      (r := APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D))
      (N₀ := 1)
      (J := fun n u ω => Step2Moment.jSnorm (sample d) E D s n u ω)
      (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh D)
      (hJ := fun n u => APrimeSlotFields.measurable_jSnorm (sample d) E D s n u)
      (p := q) (δ := δ) (N := N) (k := 1)
  have hInt : Integrable (fun ω => W ω * |cutTrunc ((N : ℝ) ^ (2 * δ)) (Jval ω)| ^ (2 * q)) B.P :=
    Step2Bootstrap.integrable_weight_mul (P := B.P) (W := W) (g := Jval) hθ
      hW0 hW1 hWm hJ0 (hJm N).aestronglyMeasurable (2 * q)
  have hpt : ∀ ω ∈ (APrimeGeneralMovingGoodMesh.good N)ᶜ,
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
        (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ))
        (Step2Moment.jSnorm (sample d) E D s N
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q) ≤
        (2 * (N : ℝ) ^ (2 * δ)) ^ (2 * q) := by
    intro ω hω
    have hcut : |cutTrunc ((N : ℝ) ^ (2 * δ))
        (Step2Moment.jSnorm (sample d) E D s N
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q) ≤
        (2 * (N : ℝ) ^ (2 * δ)) ^ (2 * q) := by
      rw [abs_of_nonneg (cutTrunc_nonneg (hJ0 ω))]
      exact pow_le_pow_left₀ (cutTrunc_nonneg (hJ0 ω))
        (cutTrunc_le_two_mul hθ (hJ0 ω)) _
    calc
      _ ≤ 1 * |cutTrunc ((N : ℝ) ^ (2 * δ))
          (Step2Moment.jSnorm (sample d) E D s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q) :=
        mul_le_mul_of_nonneg_right (hW1 ω) (by positivity)
      _ = _ := one_mul _
      _ ≤ _ := hcut
  have hbad := setIntegral_mono_on hInt.integrableOn integrableOn_const
    (APrimeGeneralMovingGoodMesh.measurableSet_good N).compl hpt
  have hbad' : ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ,
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
        (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ))
        (Step2Moment.jSnorm (sample d) E D s N
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q)
      ∂B.P ≤ (2 * (N : ℝ) ^ (2 * δ)) ^ (2 * q) *
          (B.P).real (APrimeGeneralMovingGoodMesh.good N)ᶜ := by
    calc
      _ ≤ ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ,
          (2 * (N : ℝ) ^ (2 * δ)) ^ (2 * q) ∂B.P := hbad
      _ = (2 * (N : ℝ) ^ (2 * δ)) ^ (2 * q) *
          (B.P).real (APrimeGeneralMovingGoodMesh.good N)ᶜ := by
        rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, mul_comm]
  have hpowid : ((N : ℝ) ^ (2 * δ)) ^ (2 * q) *
      (N : ℝ) ^ (-((7 / 2 : ℝ) * δ * (q : ℝ))) =
      (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (2 * δ)) (2 * q),
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have hpow : (2 * (N : ℝ) ^ (2 * δ)) ^ (2 * q) *
      (N : ℝ) ^ (-((7 / 2 : ℝ) * δ * (q : ℝ))) ≤
      2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    rw [mul_pow, mul_assoc, hpowid]
  exact (hbad'.trans (mul_le_mul_of_nonneg_left hmeasure (by positivity))).trans hpow

/-- Once `δ,p` are fixed, choose a selected order `q ≥ p` large enough for the T999
family-summation threshold.  The bad-event payment chooses its decay order from this fixed `q`
and yields the original `N^(δq/2)` rate before the eventual `N` threshold. -/
theorem eventually_selected_bad_k1
    {E D c δ₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (_hB : BoundsCore (sample d) E s)
    (_hδ₀ : 0 < δ₀) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ 32 ≤ 3 * δ * (q : ℝ) ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ,
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (sample d) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q)
            ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  intro δ hδ hδle p hp
  let q : ℕ := max p ⌈32 / (3 * δ)⌉₊
  have hqP : p ≤ q := Nat.le_max_left _ _
  have hceil : 32 / (3 * δ) ≤ (q : ℝ) := by
    dsimp [q]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_max_right p ⌈32 / (3 * δ)⌉₊))
  have hqbound : 32 ≤ 3 * δ * (q : ℝ) := by
    have hden : 0 < 3 * δ := by positivity
    calc
      32 = (32 / (3 * δ)) * (3 * δ) := by field_simp
      _ ≤ (q : ℝ) * (3 * δ) := mul_le_mul_of_nonneg_right hceil hden.le
      _ = 3 * δ * (q : ℝ) := by ring
  have hqpos : 1 ≤ q := hp.trans hqP
  refine ⟨q, hqP, hqbound, 2 ^ (2 * q), by positivity, ?_⟩
  exact eventually_bad_k1_for_order hE hD hs0 hst ht1 hc hreg _hB hδ q hqpos

/-- T995's same-resident positive-cell witness certifies that the general-moving Gaussian model
hypotheses used by this module are nondegenerate.  It witnesses the assumptions, not the
complementary high-order estimate. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_bad_k1_for_order
#print axioms eventually_selected_bad_k1
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingHighQK1Bad
