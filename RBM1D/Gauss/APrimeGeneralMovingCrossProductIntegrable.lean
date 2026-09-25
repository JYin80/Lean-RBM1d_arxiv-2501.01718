/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossYRegularity
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable

/-!
# T1053: general-moving integrability of the literal cross product

At the actual moving target mesh, the full-space `2p`-power integrability
producers for the coordinate observable and the indicated joint rate give the
consumer's product integrability by Hölder, with conjugate exponents
`2p/(2p-1)` and `2p`.  The same sample, prefix, charge, output, endpoint,
time, canonical smoothing order, and probability measure occur throughout.
-/

namespace RBM.APrimeGeneralMovingCrossProductIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta Real

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- For each fixed `p ≥ 1`, the literal cross-product integrand required by
`crossPart_active_le_jointEvent` is integrable on the full Gaussian space,
eventually uniformly over the actual moving target-net prefixes, charges,
outputs, and closed-cell times.  This is the exact `hProdInt` slot; it uses
only the two accepted full-space power-integrability producers and Hölder. -/
theorem eventually_actual_cross_product_integrable
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Set.Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        Integrable
          (fun ω =>
            |APrimeGeneralMovingCrossYRegularity.actualY
                d E D deltaWeight s t N k σ a r ω| ^ (2 * p - 1) *
            |APrimeCrossJointSplit.jointRate d E D deltaWeight s
              (APrimeGeneralMovingMesh.targetMesh D) N k
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh D) N)
              σ a
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r ω|)
          (Gauss.P d) := by
  have hY :=
    APrimeGeneralMovingCrossYRegularity.eventually_actualY_hYm_hYi
      d (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1 p hp
  have hZ :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hY, hZ, eventually_ge_atTop 1] with N hYN hZN hN
  have hNpos : 0 < N := by omega
  intro k hk σ a r hr
  let Y : Gauss.Ω d → ℝ :=
    APrimeGeneralMovingCrossYRegularity.actualY d E D deltaWeight s t N k σ a r
  let Z : Gauss.Ω d → ℝ :=
    APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      σ a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r
  have hYfields := hYN k hk σ a r hr
  have hZint := hZN k hk σ a r hr
  have hZmeas :=
    APrimeGeneralMovingJointMeasurable.measurable_prefixGradient_and_jointRate
      (deltaWeight := deltaWeight) hE hs0 hst ht1 hNpos hk σ a hr
  have hYmeas : AEStronglyMeasurable Y (Gauss.P d) := by
    simpa only [Y] using hYfields.1
  have hZmeas' : AEStronglyMeasurable Z (Gauss.P d) := by
    exact hZmeas.2.aestronglyMeasurable
  have hYint : Integrable (fun ω => |Y ω| ^ (2 * p)) (Gauss.P d) := by
    simpa only [Y] using hYfields.2
  have hZint' : Integrable (fun ω => |Z ω| ^ (2 * p)) (Gauss.P d) := by
    simpa only [Z] using hZint
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2pSub : (0 : ℝ) < 2 * (p : ℝ) - 1 := by linarith
  have hqYpos : (0 : ℝ) <
      2 * (p : ℝ) / (2 * (p : ℝ) - 1) :=
    div_pos (by linarith) h2pSub
  have hcast : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
    have hle : (1 : ℕ) ≤ 2 * p := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hconj :
      Real.HolderConjugate
        (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) (2 * (p : ℝ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ h2pSub]
      linarith
    · field_simp
      ring
  have hpowY : ∀ ω,
      (|Y ω| ^ (2 * p - 1)) ^
        (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) = |Y ω| ^ (2 * p) := by
    intro ω
    rw [← Real.rpow_natCast (|Y ω|) (2 * p - 1),
      ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_natCast (|Y ω|) (2 * p)]
    congr 1
    rw [hcast]
    field_simp
    push_cast
    ring
  have hpowZ : ∀ ω,
      |Z ω| ^ (2 * (p : ℝ)) = |Z ω| ^ (2 * p) := by
    intro ω
    rw [← Real.rpow_natCast (|Z ω|) (2 * p)]
    congr 1
    push_cast
    ring
  have hFmeas : AEStronglyMeasurable
      (fun ω => |Y ω| ^ (2 * p - 1)) (Gauss.P d) :=
    (continuous_pow _).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable hYmeas)
  have hGmeas : AEStronglyMeasurable
      (fun ω => |Z ω|) (Gauss.P d) :=
    continuous_abs.comp_aestronglyMeasurable hZmeas'
  have hFmem : MemLp (fun ω => |Y ω| ^ (2 * p - 1))
      (ENNReal.ofReal (2 * (p : ℝ) / (2 * (p : ℝ) - 1))) (Gauss.P d) := by
    refine MomentDuhamel.memLp_ofReal_of_integrable_rpow hqYpos hFmeas ?_
    have heq :
        (fun ω => |(|Y ω| ^ (2 * p - 1))| ^
          (2 * (p : ℝ) / (2 * (p : ℝ) - 1))) =
        (fun ω => |Y ω| ^ (2 * p)) := by
      funext ω
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), hpowY ω]
    rw [heq]
    exact hYint
  have hGmem : MemLp (fun ω => |Z ω|)
      (ENNReal.ofReal (2 * (p : ℝ))) (Gauss.P d) := by
    refine MomentDuhamel.memLp_ofReal_of_integrable_rpow (by linarith) hGmeas ?_
    have heq : (fun ω => |(|Z ω|)| ^ (2 * (p : ℝ))) =
        (fun ω => |Z ω| ^ (2 * p)) := by
      funext ω
      rw [abs_abs, hpowZ ω]
    rw [heq]
    exact hZint'
  letI : ENNReal.HolderConjugate
      (ENNReal.ofReal (2 * (p : ℝ) / (2 * (p : ℝ) - 1)))
      (ENNReal.ofReal (2 * (p : ℝ))) := hconj.ennrealOfReal
  exact hFmem.integrable_mul hGmem

/-! This remains a separate satisfiability context: the accepted witness gives
a positive-duration active cell and a sample with positive actual smooth
weight, without claiming that the sample belongs to the strict transition. -/

noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_cross_product_integrable
#print axioms t995_positive_cell_witness

end
end RBM.APrimeGeneralMovingCrossProductIntegrable
