/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQEarlyGood
import RBM1D.Gauss.APrimeGeneralMovingHighQFarBad

/-!
# T1141: full selected high moment on early active later mesh points

Choose the order large enough for T999 before applying the good-event producer,
then pay the complementary event at that exact same order.  One measurable
good/good-complement partition gives the full expectation uniformly on the
early active later target mesh.
-/

namespace RBM.APrimeGeneralMovingHighQEarlyFull

open Filter MeasureTheory Set Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

set_option maxHeartbeats 1000000 in
-- The dependent endpoint integral and event split expand the Gaussian
-- observables substantially beyond the default elaboration heartbeat budget.
/-- The full T999 selected-order expectation at every literal early active
later target-mesh point `2 ≤ k ≤ N^4`.  The selected order is chosen before
eventual `N`, and is large enough for T999's `32 ≤ 3δq` threshold. -/
theorem eventually_selected_high_early_full
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ 32 ≤ 3 * δ * (q : ℝ) ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∀ k : ℕ, 2 ≤ k → k ≤ N ^ 4 →
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
  intro δ hδ hδ₀ p hp
  letI := B.isProbabilityMeasure
  let pHigh : ℕ := max p ⌈32 / (3 * δ)⌉₊
  have hpHigh : p ≤ pHigh := Nat.le_max_left _ _
  have hceil : 32 / (3 * δ) ≤ (pHigh : ℝ) := by
    dsimp [pHigh]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_max_right p ⌈32 / (3 * δ)⌉₊))
  have hden : 0 < 3 * δ := by positivity
  have hthreshold : 32 ≤ 3 * δ * (pHigh : ℝ) := by
    calc
      32 = (32 / (3 * δ)) * (3 * δ) := by field_simp
      _ ≤ (pHigh : ℝ) * (3 * δ) := mul_le_mul_of_nonneg_right hceil hden.le
      _ = 3 * δ * (pHigh : ℝ) := by ring
  have hpHighPos : 1 ≤ pHigh := hp.trans hpHigh
  obtain ⟨q, hq, Cgood, hCgood, hgood⟩ :=
    APrimeGeneralMovingHighQEarlyGood.eventually_selected_high_early_good
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ pHigh hpHighPos
  have hqThreshold : 32 ≤ 3 * δ * (q : ℝ) :=
    le_trans hthreshold (by
      have hqreal : (pHigh : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hmul := mul_le_mul_of_nonneg_left hqreal hden.le
      nlinarith)
  have hbad :=
    APrimeGeneralMovingHighQFarBad.eventually_bad_active_for_order
      hE hD hs0 hst ht1 hc hreg hB hδ q (by omega)
  refine ⟨q, le_trans hpHigh hq, hqThreshold, Cgood + 2 ^ (2 * q), by positivity, ?_⟩
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (sample d) E D s N u ω
  let r := APrimeWeight.canonicalR s t mesh
  have hmeshpos : ∀ N, 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos D
  have hendpoint : ∀ N k,
      k ≤ cutNetTop s t mesh N → cutNetPt s mesh N k < 1 := by
    intro N k hk
    have hmem : cutNetPt s mesh N k ∈ Set.Icc (s N) (t N) :=
      netFinset_subset_Icc (hst N) (hmeshpos N) _ (cutNetPt_mem_netFinset hk)
    exact lt_of_le_of_lt hmem.2 (ht1 N)
  have hJmeas : ∀ N u, Measurable (J N u) := fun N u =>
    APrimeSlotFields.measurable_jSnorm (sample d) E D s N u
  filter_upwards [hgood, hbad, eventually_ge_atTop (1 : ℕ)]
    with N hgoodN hbadN hN
  intro k hklo hkhi hactive
  let W : ℕ → Ω d → ℝ := fun N ω => APrimeWeight.widenedW r 1 J s t mesh δ q N k ω
  let f : ℕ → Ω d → ℝ := fun N ω => W N ω *
    |cutTrunc ((N : ℝ) ^ (2 * δ)) (J N (cutNetPt s mesh N k) ω)| ^ (2 * q)
  have hEndN := hendpoint N k hactive
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNpos _
  have hslt : s N < 1 := by linarith [hs0 N, hst N, ht1 N]
  have hJ0 : ∀ ω, 0 ≤ J N (cutNetPt s mesh N k) ω := by
    intro ω
    exact Step2Moment.jSnorm_nonneg (sample d) hE hslt hEndN ω
  have hW0 : ∀ ω, 0 ≤ W N ω := by
    intro ω
    exact APrimeWeight.widenedW_nonneg r 1 J s t mesh δ q N k ω
  have hW1 : ∀ ω, W N ω ≤ 1 := by
    intro ω
    exact APrimeWeight.widenedW_le_one r 1 J s t mesh δ q N k ω
  have hWmeas : AEStronglyMeasurable (W N) B.P := by
    exact APrimeWeight.widenedW_meas (P := B.P) (r := r) (N₀ := 1) (J := J)
      (s := s) (t := t) (mesh := mesh) (hJ := hJmeas) (p := q) (δ := δ) (N := N) (k := k)
  have hJmeasEnd := hJmeas N (cutNetPt s mesh N k)
  have hint : Integrable (f N) B.P := by
    dsimp [f]
    exact Step2Bootstrap.integrable_weight_mul (P := B.P) (W := W N)
      (g := J N (cutNetPt s mesh N k)) hθ hW0 hW1 hWmeas hJ0
      hJmeasEnd.aestronglyMeasurable (2 * q)
  have hGoodMeas : MeasurableSet (APrimeGeneralMovingGoodMesh.good N) :=
    APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hsplit := integral_add_compl hGoodMeas hint
  have hgoodBound : ∫ ω in APrimeGeneralMovingGoodMesh.good N, f N ω ∂B.P ≤
      Cgood * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa [f, W, J, r, mesh] using hgoodN k hklo hkhi hactive
  have hbadBound : ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ, f N ω ∂B.P ≤
      2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa [f, W, J, r, mesh] using hbadN k hklo hactive
  have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
  calc
    ∫ ω, f N ω ∂B.P =
          (∫ ω in APrimeGeneralMovingGoodMesh.good N, f N ω ∂B.P) +
            (∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ, f N ω ∂B.P) := hsplit.symm
    _ ≤ Cgood * (N : ℝ) ^ (δ / 2 * (q : ℝ)) +
            2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := add_le_add hgoodBound hbadBound
    _ = (Cgood + 2 ^ (2 * q)) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by ring

/-- The accepted T1117 witness supplies the same nondegenerate Gaussian
model and an actual early active `k=2` point in the good event. -/
noncomputable abbrev nondegenerate_early_k2_witness :=
  APrimeGeneralMovingHighQEarlyGood.positive_length_k2_good_witness

#print axioms eventually_selected_high_early_full
#print axioms nondegenerate_early_k2_witness

end
end RBM.APrimeGeneralMovingHighQEarlyFull
