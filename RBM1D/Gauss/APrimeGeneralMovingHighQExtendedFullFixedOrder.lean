/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQExtendedGoodFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQFarBad

/-!
# T1189: fixed-order full Gaussian high moment on the extended active range

At one prescribed order q, combine the T1177 norm-good transfer with the
T1115 same-order norm-bad estimate by partitioning the Gaussian law into the
literal good event and its complement. The endpoint integrand and all model
data remain unchanged.
-/

namespace RBM.APrimeGeneralMovingHighQExtendedFullFixedOrder

open Filter MeasureTheory Set Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

set_option maxHeartbeats 1000000 in
/-- For fixed δ and q, the exact full k=0 premise gives the full T999
order-q expectation uniformly on the short extended active range
`N^4 < k ≤ N^(4+δ/2)`. The order and rate remain unchanged. -/
theorem eventually_extended_full_of_exact_k0
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
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
    ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
        ∀ k : ℕ, N ^ 4 < k →
          (k : ℝ) ≤ (N : ℝ) ^ (4 + δ / 2) →
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
  letI := B.isProbabilityMeasure
  obtain ⟨Cgood, hCgood, hgood⟩ :=
    APrimeGeneralMovingHighQExtendedGoodFixedOrder.eventually_extended_good_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hδ q hq C₀ hC₀ hbase
  have hbad := APrimeGeneralMovingHighQFarBad.eventually_bad_active_for_order
    hE hD hs0 hst ht1 hc hreg hB hδ q hq
  refine ⟨Cgood + 2 ^ (2 * q), by positivity, ?_⟩
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
  intro k hklo hkrange hactive
  let W : ℕ → Ω d → ℝ := fun N ω =>
    APrimeWeight.widenedW r 1 J s t mesh δ q N k ω
  let f : ℕ → Ω d → ℝ := fun N ω =>
    W N ω * |cutTrunc ((N : ℝ) ^ (2 * δ))
      (J N (cutNetPt s mesh N k) ω)| ^ (2 * q)
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
      (s := s) (t := t) (mesh := mesh) (hJ := hJmeas) (p := q) (δ := δ)
      (N := N) (k := k)
  have hEndMeas := hJmeas N (cutNetPt s mesh N k)
  have hint : Integrable (f N) B.P := by
    dsimp [f]
    exact Step2Bootstrap.integrable_weight_mul (P := B.P) (W := W N)
      (g := J N (cutNetPt s mesh N k)) hθ hW0 hW1 hWmeas hJ0
      hEndMeas.aestronglyMeasurable (2 * q)
  have hGoodMeas : MeasurableSet (APrimeGeneralMovingGoodMesh.good N) :=
    APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hsplit := integral_add_compl hGoodMeas hint
  have hgoodBound : ∫ ω in APrimeGeneralMovingGoodMesh.good N, f N ω ∂B.P ≤
      Cgood * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa [f, W, J, r, mesh] using hgoodN k hklo hkrange hactive
  have hk2 : 2 ≤ k := by
    have hN4 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hbadBound : ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ, f N ω ∂B.P ≤
      2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa [f, W, J, r, mesh] using hbadN k hk2 hactive
  calc
    ∫ ω, f N ω ∂B.P =
        (∫ ω in APrimeGeneralMovingGoodMesh.good N, f N ω ∂B.P) +
          (∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ, f N ω ∂B.P) := hsplit.symm
    _ ≤ Cgood * (N : ℝ) ^ (δ / 2 * (q : ℝ)) +
        2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) :=
          add_le_add hgoodBound hbadBound
    _ = (Cgood + 2 ^ (2 * q)) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by ring

/-- T1177's explicit fixed-order k0-preamble witness simultaneously supplies
the exact k0 premise and a good resident with active `k=N^4+1`. -/
noncomputable abbrev nondegenerate_extended_fixed_order_witness :=
  @APrimeGeneralMovingHighQExtendedGoodFixedOrder.nondegenerate_extended_fixed_order_witness

#print axioms eventually_extended_full_of_exact_k0
#print axioms nondegenerate_extended_fixed_order_witness

end
end RBM.APrimeGeneralMovingHighQExtendedFullFixedOrder
