/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingTargetTransitionExists
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.Lemma514QRoute

/-!
# T1173: norm-bad second-moment payment for the general-moving joint rate

The literal transition-indicated product is bounded pointwise by T617's
all-sample envelope and is square-integrable by the fixed-order producer
underlying T1123.  The norm-good event has arbitrary polynomial tails, so the
second moment on its complement pays the square of the envelope.
-/

namespace RBM.APrimeGeneralMovingJointRateNormBadPayment

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The norm-good event supplied by T100's Gaussian norm domination. -/
noncomputable def normGood (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- For every fixed admissible general-moving window and every active target
prefix, sign, output, and running time in its closed cell, the literal
transition-indicated joint rate has second moment at most `N⁻²` on the
complement of the norm-good event. -/
theorem eventually_jointRate_sq_integral_normBad_le
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ u ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        ∫ ω in (normGood N)ᶜ,
          |APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            σ a (cutNetPt s (mesh D) N k) u ω| ^ 2 ∂(Gauss.P d) ≤
          (N : ℝ) ^ (-(2 : ℝ)) := by
  let Env : ℕ → ℝ := fun N =>
    APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ 2
  let Ξ : ℕ → Set (Ω d) := normGood
  let P : Measure (Ω d) := Gauss.P d
  have hprob : HighProb P Ξ := by
    change HighProb (Gauss.P d)
      (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
    exact Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)
  have hEnvPoly : ∀ᶠ N : ℕ in atTop,
      Env N ≤ (N : ℝ) ^ (4 * D + 34) := by
    have hEnvelope :=
      APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow hD
    filter_upwards [hEnvelope, eventually_ge_atTop 1] with N hJ hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hJ0 := APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
    calc
      Env N = APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ 2 := rfl
      _ ≤ ((N : ℝ) ^ (2 * D + 17)) ^ 2 :=
        pow_le_pow_left₀ hJ0 hJ 2
      _ = (N : ℝ) ^ (4 * D + 34) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ (2 * D + 17)) 2,
          ← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have hCenv : 0 ≤ 4 * D + 34 := by linarith
  have hpay :=
    Gauss.eventually_env_mul_prob_rpow_le (P := P) (q := 1) (by norm_num)
      hprob (Env := Env) (Cenv := 4 * D + 34) hCenv hEnvPoly
      (D := 2) (by norm_num)
  have hProduct :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hEnvelopeNonneg (N : ℕ) :
      0 ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N :=
    APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
  have hIntegrable :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
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
  have hpayN' : Env N * (P (Ξ N)ᶜ).toReal ≤ (N : ℝ) ^ (-(2 : ℝ)) := by
    have hpow : ((P (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (1 : ℕ)) =
        (P (Ξ N)ᶜ).toReal := by norm_num
    simpa only [hpow] using hpayN
  intro k hk σ a u hu
  let v := cutNetPt s (mesh D) N k
  let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
  let Z : Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
      σ a v u ω
  have hZint : Integrable (fun ω => |Z ω| ^ 2) P := by
    simpa [Z, v, m, mesh, pow_two] using
      hIntegrableN k hk σ a u hu
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
      have hp := hProductN k hk σ a u hu ω
      simpa [m, v, mesh] using hp
    · rw [APrimeCrossJointSplit.jointRate,
        Set.indicator_of_notMem htrans]
      exact hJ0
  have hZsqBound : ∀ ω, |Z ω| ^ 2 ≤ Env N := by
    intro ω
    dsimp [Env]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZbound ω) 2
  have hOuter :
      ∫ ω in (Ξ N)ᶜ, |Z ω| ^ 2 ∂P ≤
        Env N * (P (Ξ N)ᶜ).toReal := by
    have hmono :
        ∫ ω in (Ξ N)ᶜ, |Z ω| ^ 2 ∂P ≤
          ∫ ω in (Ξ N)ᶜ, Env N ∂P := by
      refine integral_mono hZint.restrict (integrable_const (Env N)) ?_
      intro ω
      exact hZsqBound ω
    simpa [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm,
      measureReal_def] using hmono
  calc
    ∫ ω in (normGood N)ᶜ, |Z ω| ^ 2 ∂P
        ≤ Env N * (P (Ξ N)ᶜ).toReal := by
          simpa [Ξ, normGood] using hOuter
    _ ≤ (N : ℝ) ^ (-(2 : ℝ)) := hpayN'

/-! The hypotheses have a positive-duration realization with an active `k=2`
cell and a sample in the exact strict transition event.  This uses the same
Gaussian law, target mesh, canonical moment order, and loss-weight schedule as
the estimate. -/

theorem nondegenerate_first_cell_active_k2_witness :
    ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg (band d) 0 s t (1 / 2) ∧
      0 < APrimeGeneralMovingSlotLossSchedule.deltaWeight (1 / 200) ∧
      ∀ᶠ N : ℕ in atTop,
        2 ≤ cutNetTop s t (mesh 60) N ∧
        0 < cutNetPt s (mesh 60) N 2 ∧
        ∃ x ∈ Ioo 0 (2 / Real.sqrt ((mesh 60 N)⁻¹)),
          let ω := APrimeSmoothTransition.scalarSample d x
          ω ∈ APrimeCrossJointSplit.transition d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight (1 / 200))
            s (mesh 60) N 2
            (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) := by
  let s : ℕ → ℝ := fun _ => 0
  let t : ℕ → ℝ := Gauss.firstCellT 1
  have hs0 : ∀ N, 0 ≤ s N := by intro N; simp [s]
  have hst : ∀ N, s N ≤ t N := by
    intro N
    simpa [s] using
      (APrimeSupportRunning.firstT_bounds (τ' := (1 : ℝ)) (by norm_num) N).1
  have ht1 : ∀ N, t N < 1 := by
    intro N
    have h :=
      (APrimeSupportRunning.firstT_bounds (τ' := (1 : ℝ)) (by norm_num) N).2
    linarith
  have hreg : Cond272Reg (band d) 0 s t (1 / 2) := by
    dsimp [s, t]
    exact APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg (by norm_num)
  have hdelta : 0 < APrimeGeneralMovingSlotLossSchedule.deltaWeight (1 / 200) :=
    (APrimeGeneralMovingSlotLossSchedule.schedule_room
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 200)
      (by norm_num : (1 / 200 : ℝ) ≤ min 1 ((1 / 2 : ℝ) / 100))).1
  have hT :=
    APrimeGeneralMovingTargetTransitionExists.eventually_exampleGrow_target_transition
      (τ := 1) (c := 1 / 2) (δ := 1 / 200)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨s, t, hs0, hst, ht1, hreg, hdelta, ?_⟩
  filter_upwards [hT] with N hN
  rcases hN with ⟨_hs, _ht, hk, x, hx, htransition, _hbelow, _habove⟩
  refine ⟨hk, ?_, x, ?_, ?_⟩
  · have hmesh : 0 < mesh 60 N :=
      APrimeGeneralMovingMesh.targetMesh_pos 60 N
    have hv : cutNetPt s (mesh 60) N 2 = 2 / (mesh 60 N) := by
      simp [CutHypTheta.cutNetPt, s]
    rw [hv]
    exact div_pos (by norm_num) hmesh
  · simpa [mesh] using hx
  · simpa [s, t, mesh] using htransition

#print axioms eventually_jointRate_sq_integral_normBad_le
#print axioms nondegenerate_first_cell_active_k2_witness

end
end RBM.APrimeGeneralMovingJointRateNormBadPayment
