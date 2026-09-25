/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingJointRateNormBadPayment
import RBM1D.Gauss.Lemma514QRoute

/-!
# T1191: all fixed positive-order norm-bad payment for the actual joint rate

The literal transition-indicated joint rate has an all-sample polynomial
envelope and an actual fixed-order integrability producer.  T100's Gaussian
norm event has arbitrary polynomial tails, so the complement pays the
envelope's `2p`-th power for every fixed `p`.
-/

namespace RBM.APrimeGeneralMovingJointRateNormBadAllOrders

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The exact norm-good event used by T1173, under the same Gaussian law. -/
noncomputable def normGood (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- For every fixed positive integer `p`, the actual general-moving
transition-indicated joint rate pays its `2p`-th moment on the complement of
the Gaussian norm-good event.  One eventual cutoff works uniformly over all
active target-mesh indices, signs, loop outputs, and closed-cell running
times, with the same sample, law, transition, canonical smoothing order, and
endpoint as the accepted T1173/T1174 second-moment statement. -/
theorem eventually_jointRate_pow_integral_normBad_le
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ u ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        ∫ ω in (normGood N)ᶜ,
          |APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            σ a (cutNetPt s (mesh D) N k) u ω| ^ (2 * p) ∂(Gauss.P d) ≤
          (N : ℝ) ^ (-(2 * (p : ℝ))) := by
  let Env : ℕ → ℝ := fun N =>
    APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p)
  let Ξ : ℕ → Set (Ω d) := normGood
  let P : Measure (Ω d) := Gauss.P d
  let Cenv : ℝ := 2 * (p : ℝ) * (2 * D + 17)
  have hprob : HighProb P Ξ := by
    change HighProb (Gauss.P d)
      (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
    exact Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)
  have hEnvPoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Cenv := by
    have hEnvelope :=
      APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow hD
    filter_upwards [hEnvelope, eventually_ge_atTop 1] with N hJ hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hJ0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
    calc
      Env N = APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p) := rfl
      _ ≤ ((N : ℝ) ^ (2 * D + 17)) ^ (2 * p) :=
        pow_le_pow_left₀ hJ0 hJ (2 * p)
      _ = (N : ℝ) ^ Cenv := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ (2 * D + 17)) (2 * p),
          ← Real.rpow_mul hNpos.le]
        congr 1
        dsimp [Cenv]
        push_cast
        ring
  have hCenv : 0 ≤ Cenv := by
    dsimp [Cenv]
    positivity
  have hTailExponent : 0 < (2 * (p : ℝ)) := by
    exact_mod_cast (show 0 < 2 * p by omega)
  have hpay :=
    Gauss.eventually_env_mul_prob_rpow_le (P := P) (q := 1) (by norm_num)
      hprob (Env := Env) (Cenv := Cenv) hCenv hEnvPoly
      (D := 2 * (p : ℝ)) hTailExponent
  have hProduct :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hEnvelopeNonneg (N : ℕ) :
      0 ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N :=
    APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hIntegrable :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  letI : IsProbabilityMeasure P := Gauss.isProbabilityMeasure_P d
  filter_upwards [hpay, hProduct, hIntegrable, eventually_ge_atTop 1]
    with N hpayN hProductN hIntegrableN hN
  have hNpos : 0 < N := by omega
  have hJ0 := hEnvelopeNonneg N
  have hEnv0 : 0 ≤ Env N := by
    dsimp [Env]
    positivity
  have hGoodMeas : MeasurableSet (Ξ N) := by
    simpa [Ξ, normGood] using Gauss.measurableSet_normX_le d N
  have hpayN' : Env N * (P (Ξ N)ᶜ).toReal ≤
      (N : ℝ) ^ (-(2 * (p : ℝ))) := by
    have hpow : ((P (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (1 : ℕ)) =
        (P (Ξ N)ᶜ).toReal := by norm_num
    simpa only [hpow] using hpayN
  intro k hk σ a u hu
  let v := cutNetPt s (mesh D) N k
  let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
  let Z : Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
      σ a v u ω
  have hZint : Integrable (fun ω => |Z ω| ^ (2 * p)) P := by
    simpa [Z, v, m, mesh] using hIntegrableN k hk σ a u hu
  have hZnonneg : ∀ ω, 0 ≤ Z ω := by
    intro ω
    exact APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
      (mesh D) N k m σ a v u hNpos ω
  have hZbound : ∀ ω, |Z ω| ≤
      APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
    intro ω
    rw [abs_of_nonneg (hZnonneg ω)]
    change APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
      σ a v u ω ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N
    by_cases htrans : ω ∈ APrimeCrossJointSplit.transition d E D deltaWeight
        s (mesh D) N k m
    · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_mem htrans]
      have hp' := hProductN k hk σ a u hu ω
      simpa [m, v, mesh] using hp'
    · rw [APrimeCrossJointSplit.jointRate,
        Set.indicator_of_notMem htrans]
      exact hJ0
  have hZpowBound : ∀ ω, |Z ω| ^ (2 * p) ≤ Env N := by
    intro ω
    dsimp [Env]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZbound ω) (2 * p)
  have hOuter :
      ∫ ω in (Ξ N)ᶜ, |Z ω| ^ (2 * p) ∂P ≤
        Env N * (P (Ξ N)ᶜ).toReal := by
    have hmono :
        ∫ ω in (Ξ N)ᶜ, |Z ω| ^ (2 * p) ∂P ≤
          ∫ ω in (Ξ N)ᶜ, Env N ∂P := by
      refine integral_mono hZint.restrict (integrable_const (Env N)) ?_
      intro ω
      exact hZpowBound ω
    simpa [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm,
      measureReal_def] using hmono
  calc
    ∫ ω in (normGood N)ᶜ, |Z ω| ^ (2 * p) ∂P
        ≤ Env N * (P (Ξ N)ᶜ).toReal := by
          simpa [Ξ, normGood] using hOuter
    _ ≤ (N : ℝ) ^ (-(2 * (p : ℝ))) := hpayN'

/-! This imports T1173's actual positive-duration, active-`k=2` witness,
including a sample in the exact strict transition event for the same
canonical smoothing order and scheduled positive `deltaWeight`. -/

noncomputable abbrev nondegenerate_first_cell_active_k2_witness :=
  APrimeGeneralMovingJointRateNormBadPayment.nondegenerate_first_cell_active_k2_witness

#print axioms eventually_jointRate_pow_integral_normBad_le
#print axioms nondegenerate_first_cell_active_k2_witness

end
end RBM.APrimeGeneralMovingJointRateNormBadAllOrders
