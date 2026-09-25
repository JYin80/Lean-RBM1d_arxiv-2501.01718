/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK1GoodFixedOrder
import RBM1D.Gauss.APrimeGeneralMovingHighQK1Bad

/-!
# T1167: fixed-order full first-positive-cell high moment

Compose the fixed-order norm-good transfer with the complementary norm-bad
payment. The integrand remains the literal order-q Gaussian observable.
-/

namespace RBM.APrimeGeneralMovingHighQK1FullFixedOrder

open Filter MeasureTheory Set Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- From the exact fixed-order full `k=0` moment premise, obtain the full
order-`q` Gaussian expectation at `k=1`. The norm-good transfer and bad-event
payment use the same `q`, loss, mesh, sample, endpoint, cutoff and law. -/
theorem eventually_k1_full_of_exact_k0
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
        1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
        ∫ ω,
          APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
            (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh D) δ q N 1 ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (sample d) E D s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 1) ω)| ^ (2 * q)
          ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (sample d) E D s N u ω
  let r := APrimeWeight.canonicalR s t mesh
  let W : ℕ → Ω d → ℝ := fun N ω => APrimeWeight.widenedW r 1 J s t mesh δ q N 1 ω
  let f : ℕ → Ω d → ℝ := fun N ω =>
    W N ω * |cutTrunc ((N : ℝ) ^ (2 * δ)) (J N (cutNetPt s mesh N 1) ω)| ^ (2 * q)
  letI := B.isProbabilityMeasure
  obtain ⟨Cgood, hCgood, hgood⟩ :=
    APrimeGeneralMovingHighQK1GoodFixedOrder.eventually_k1_good_of_exact_k0
      hE hD hs0 hst ht1 hc hreg hδ q hq C₀ hC₀ hbase
  have hbad := APrimeGeneralMovingHighQK1Bad.eventually_bad_k1_for_order
    hE hD hs0 hst ht1 hc hreg hB hδ q hq
  refine ⟨Cgood + 2 ^ (2 * q), by positivity, ?_⟩
  have hmeshpos : ∀ N, 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos D
  have hendpoint : ∀ᶠ N : ℕ in atTop, cutNetPt s mesh N 1 < 1 := by
    have hfloor := APrimeGeneralMovingWindowFloor.eventually_endpoint_floor
      hE hs0 hst ht1 hc hreg
    filter_upwards [hfloor, APrimeGeneralMovingMesh.eventually_targetMesh_eq D,
      eventually_ge_atTop 2] with N hfloorN hmeshEq hN
    have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < N := by linarith
    have hexp : (2 : ℝ) ≤ 4 * D + 18 := by linarith [hD]
    have hmeshLower : (N : ℝ) ^ (2 : ℝ) ≤ mesh N := by
      change (N : ℝ) ^ (2 : ℝ) ≤ APrimeGeneralMovingMesh.targetMesh D N
      rw [hmeshEq]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    have hrecip : 1 / mesh N ≤ 1 / (N : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (hmeshpos N) (by positivity : 0 < (N : ℝ) ^ 2)).2
      simpa only [one_mul, mul_one, Real.rpow_ofNat] using hmeshLower
    have hstrict : 1 / (N : ℝ) ^ 2 < 1 / (N : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)
        (by positivity : (0 : ℝ) < N)).2
      nlinarith
    have hNinv : (1 : ℝ) / N = (N : ℝ)⁻¹ := by simp [one_div]
    have hdiv : 1 / mesh N < 1 - t N :=
      lt_of_le_of_lt hrecip (lt_of_lt_of_le hstrict (by simpa [hNinv] using hfloorN.1))
    rw [CutHypTheta.cutNetPt]
    norm_num
    have hdiv' : (mesh N)⁻¹ < 1 - t N := by rw [← one_div]; exact hdiv
    linarith [hdiv', hst N]
  have hJmeas : ∀ N u, Measurable (J N u) := fun N u =>
    APrimeSlotFields.measurable_jSnorm (sample d) E D s N u
  filter_upwards [hgood, hbad, hendpoint, eventually_ge_atTop (1 : ℕ)]
    with N hgoodN hbadN hEndN hN
  intro hactive
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNpos _
  have hslt : s N < 1 := by linarith [hs0 N, hst N, ht1 N]
  have hJ0 : ∀ ω, 0 ≤ J N (cutNetPt s mesh N 1) ω := by
    intro ω
    exact Step2Moment.jSnorm_nonneg (sample d) hE hslt hEndN ω
  have hW0 : ∀ ω, 0 ≤ W N ω := by
    intro ω
    exact APrimeWeight.widenedW_nonneg r 1 J s t mesh δ q N 1 ω
  have hW1 : ∀ ω, W N ω ≤ 1 := by
    intro ω
    exact APrimeWeight.widenedW_le_one r 1 J s t mesh δ q N 1 ω
  have hWmeas : AEStronglyMeasurable (W N) B.P := by
    exact APrimeWeight.widenedW_meas (P := B.P) (r := r) (N₀ := 1) (J := J)
      (s := s) (t := t) (mesh := mesh) (hJ := hJmeas) (p := q) (δ := δ) (N := N) (k := 1)
  have hint : Integrable (f N) B.P := by
    dsimp [f, W]
    exact Step2Bootstrap.integrable_weight_mul (P := B.P) (W := W N)
      (g := J N (cutNetPt s mesh N 1)) hθ hW0 hW1 hWmeas hJ0
      (hJmeas N (cutNetPt s mesh N 1)).aestronglyMeasurable (2 * q)
  have hGoodMeas : MeasurableSet (APrimeGeneralMovingGoodMesh.good N) :=
    APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hsplit := integral_add_compl hGoodMeas hint
  have hgoodBound : ∫ ω in APrimeGeneralMovingGoodMesh.good N, f N ω ∂B.P ≤
      Cgood * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa [f, W, J, r, mesh] using hgoodN hactive
  have hbadBound : ∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ, f N ω ∂B.P ≤
      2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    simpa [f, W, J, r, mesh] using hbadN
  have hpow : 0 ≤ (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by positivity
  calc
    ∫ ω, f N ω ∂B.P =
        (∫ ω in APrimeGeneralMovingGoodMesh.good N, f N ω ∂B.P) +
          (∫ ω in (APrimeGeneralMovingGoodMesh.good N)ᶜ, f N ω ∂B.P) := hsplit.symm
    _ ≤ Cgood * (N : ℝ) ^ (δ / 2 * (q : ℝ)) +
          2 ^ (2 * q) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := add_le_add hgoodBound hbadBound
    _ = (Cgood + 2 ^ (2 * q)) * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by ring

/-- T995's nondegenerate positive first-cell witness together with the exact
fixed-order premise producer supplied by T1153. -/
noncomputable abbrev fixed_order_premise_with_positive_k1_witness :=
  APrimeGeneralMovingHighQK1GoodFixedOrder.fixed_order_premise_with_positive_k1_witness

#print axioms eventually_k1_full_of_exact_k0
#print axioms fixed_order_premise_with_positive_k1_witness

end
end RBM.APrimeGeneralMovingHighQK1FullFixedOrder
