/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.APrimeGeneralMovingEarlyCrossBadSupport
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeGeneralMovingJointGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingJointMeasurable
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.LkGoodMeasurable
import RBM1D.Gauss.Lemma514QRoute

/-!
# T1187: all fixed positive orders for the first-cell early cross budget

For the literal T995 first cell and `D = 60`, every fixed `p ≥ 1` has an
eventually uniform `N⁻¹` integral bound for the actual positive-time cross
budget over every active prefix `k ≤ N^10`. The proof localizes the actual
rate to the norm-bad set, pays its polynomial envelope by T100's arbitrary
polynomial tail at order `2p`, and integrates the exact `1/√r` coefficient
over the very short early cell.
-/

namespace RBM.APrimeGeneralMovingEarlyCrossBudgetAllOrders

open Filter MeasureTheory Set Gauss CutHypTheta
open APrimeGeneralMovingCrossBudgetTimeIntegrable
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60
private noncomputable abbrev normGood (N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)}
private noncomputable abbrev envelope (N : ℕ) : ℝ :=
  APrimeGeneralMovingJointGlobalPoly.jointEnvelope 60 N

private theorem firstCellS_eq_zero (τ : ℝ) : firstCellS τ = fun _ => 0 := by
  funext N
  unfold firstCellS
  exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem firstCell_hypotheses {τ δ : ℝ} (hτ : 0 < τ)
    (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100)) :
    0 < APrimeGeneralMovingSlotLossSchedule.deltaWeight δ ∧
    Cond272Reg (Gauss.band d) 0 (firstCellS τ) (firstCellT τ) (1 / 2) ∧
    (∀ N, 0 ≤ firstCellS τ N) ∧
    (∀ N, firstCellS τ N ≤ firstCellT τ N) ∧
    (∀ N, firstCellT τ N < 1) := by
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room
    (by norm_num : (0 : ℝ) < 1 / 2) hδ hsmall
  have hsEq := firstCellS_eq_zero τ
  have hreg0 := APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg
    (τ' := τ) hτ
  have hreg0' : Cond272Reg (Gauss.band d) 0 (fun _ => 0)
      (firstCellT τ) (1 / 2) := by
    change Cond272Reg (Gauss.band d) 0 (fun _ => 0)
      (firstCellT τ) (1 / 2) at hreg0
    exact hreg0
  have hreg : Cond272Reg (Gauss.band d) 0 (firstCellS τ)
      (firstCellT τ) (1 / 2) := by
    simpa [hsEq] using hreg0'
  have hs0 : ∀ N, 0 ≤ firstCellS τ N := by
    intro N
    rw [hsEq]
  have hst : ∀ N, firstCellS τ N ≤ firstCellT τ N := by
    intro N
    rw [hsEq]
    have hW : (1 : ℝ) ≤ (Gauss.band d).W N := (Gauss.band d).one_le_W N
    have hm := gridT_mono hW hτ.le (1 / 2 : ℝ)
    have h := hm (show 0 ≤ 1 by norm_num)
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    simpa [firstCellT] using h
  have ht1 : ∀ N, firstCellT τ N < 1 := by
    intro N
    have h := gridT_le (W := (Gauss.band d).W N) (τ' := τ) (1 / 2 : ℝ) 1
    exact lt_of_le_of_lt h (by norm_num)
  exact ⟨hroom.1, hreg, hs0, hst, ht1⟩

/-- For a fixed positive `p`, uniform first-cell control of the actual
`L^(2p)` joint-rate norm. The support set is exactly T1149's fixed norm-good
event, and the charge and canonical smoothing order match T1089's budget. -/
private theorem eventually_jointRate_momNorm_le_inv
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N,
        k ≤ N ^ 10 →
        ∀ a : LoopArg (d.L N) 2,
          ∀ r ∈ Icc (firstCellS τ N)
            (cutNetPt (firstCellS τ) mesh N k),
            MomentDuhamel.momNorm (Gauss.P d) (2 * p)
              (APrimeCrossJointSplit.jointRate d 0 60
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (firstCellS τ) mesh N k
                (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
                  (firstCellT τ) mesh N)
                Step2.sigPM a
                (cutNetPt (firstCellS τ) mesh N k) r) ≤ (N : ℝ) ^ (-1 : ℝ) := by
  let Ξ : ℕ → Set (Gauss.Ω d) := normGood
  let Env : ℕ → ℝ := envelope
  have hGood : HighProb (Gauss.P d) Ξ := by
    simpa [Ξ, normGood] using
      Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)
  have hEnvPoly : ∀ᶠ N : ℕ in atTop,
      Env N ≤ (N : ℝ) ^ (137 : ℝ) := by
    have h := APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow
      (D := 60) (by norm_num)
    have hpower : (2 : ℝ) * 60 + 17 = 137 := by norm_num
    simpa only [Env, envelope, hpower] using h
  have hTail := Gauss.eventually_env_mul_prob_rpow_le
    (P := Gauss.P d) (q := 2 * p) (by omega) hGood
    (Env := Env) (Cenv := 137) (by norm_num) hEnvPoly
    (D := 1) (by norm_num)
  have hregData := firstCell_hypotheses hτ hδ hsmall
  have hpoly := APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
    (E := 0) (D := 60) (c := 1 / 2)
    (by norm_num) (by norm_num) hregData.2.2.1 hregData.2.2.2.1
    hregData.2.2.2.2 (by norm_num) hregData.2.1 hregData.1.le
  have hzero :=
    APrimeGeneralMovingEarlyCrossBadSupport.eventually_jointRate_eq_zero_on_normGood
      hτ hδ hsmall
  have hint :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      (E := 0) (D := 60) (c := 1 / 2)
      (s := firstCellS τ) (t := firstCellT τ)
      (by norm_num) (by norm_num) hregData.2.2.1 hregData.2.2.2.1
      hregData.2.2.2.2 (by norm_num) hregData.2.1
      (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      hregData.1.le p hp
  have hN1 := eventually_ge_atTop (1 : ℕ)
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hTail, hpoly, hzero, hint, hN1]
    with N hTailN hpolyN hzeroN hintN hN1
  have hNpos : 0 < N := by omega
  have hδw := hregData.1
  have hEnv0 : 0 ≤ Env N := by
    dsimp [Env, envelope]
    exact APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg 60 N
  have hGoodMeas : MeasurableSet (Ξ N) := by
    exact Gauss.measurableSet_normX_le d N
  intro k hk hkEarly a r hr
  let v := cutNetPt (firstCellS τ) mesh N k
  let m := APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
    (firstCellT τ) mesh N
  let Z : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d 0 60
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (firstCellS τ) mesh N k m Step2.sigPM a v r ω
  have hZint : Integrable (fun ω => |Z ω| ^ (2 * p)) (Gauss.P d) := by
    simpa [Z, v, m, mesh] using hintN k hk Step2.sigPM a r hr
  have hZzero : ∀ ω ∈ Ξ N, Z ω = 0 := by
    intro ω hω
    exact hzeroN k hk hkEarly Step2.sigPM a r hr ω hω
  have hIndicator : Set.indicator (Ξ N) Z = fun _ => (0 : ℝ) := by
    funext ω
    by_cases hω : ω ∈ Ξ N
    · simp [hω, hZzero ω hω]
    · simp [hω]
  have hZall : ∀ ω, |Z ω| ≤ Env N := by
    intro ω
    have hrateNonneg := APrimeCrossJointSplit.jointRate_nonneg d 0 60
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (firstCellS τ) mesh N k m Step2.sigPM a v r hNpos ω
    have hrateBound : Z ω ≤ Env N := by
      change APrimeCrossJointSplit.jointRate d 0 60
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) mesh N k m Step2.sigPM a v r ω ≤ Env N
      by_cases htrans : ω ∈ APrimeCrossJointSplit.transition d 0 60
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) mesh N k m
      · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_mem htrans]
        simpa [Env, envelope, v, m, mesh] using
          hpolyN k hk Step2.sigPM a r hr ω
      · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_notMem htrans]
        exact hEnv0
    rw [abs_of_nonneg hrateNonneg]
    exact hrateBound
  have hSplit := Gauss.momNorm_le_indicator_add_env
    (P := Gauss.P d) (q := 2 * p) (by omega) hZint hGoodMeas
    hEnv0 (ENNReal.toReal_nonneg)
    hZall (le_rfl : ((Gauss.P d) ((Ξ N)ᶜ)).toReal ≤
      ((Gauss.P d) ((Ξ N)ᶜ)).toReal)
  have hIndicatorNorm : MomentDuhamel.momNorm (Gauss.P d) (2 * p)
      (Set.indicator (Ξ N) Z) = 0 := by
    have hq : (2 * p : ℕ) ≠ 0 := by omega
    rw [hIndicator]
    rw [MomentDuhamel.momNorm]
    simp only [abs_zero, zero_pow hq, integral_zero]
    exact Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.2 hq))
  rw [hIndicatorNorm, zero_add] at hSplit
  have hMoment := hSplit.trans (hTailN)
  simpa [Z, v, m, mesh] using hMoment

private theorem firstCellS_zero_value (τ : ℝ) (N : ℕ) : firstCellS τ N = 0 := by
  have h := congrFun (firstCellS_eq_zero τ) N
  exact h

private theorem early_endpoint_sqrt_bound {τ : ℝ} {N k : ℕ}
    (hN : 2 ≤ N) (hk : k ≤ N ^ 10)
    (hmesh : mesh N = (N : ℝ) ^ (258 : ℕ)) :
    Real.sqrt (cutNetPt (firstCellS τ) mesh N k) ≤
      ((N : ℝ) ^ (124 : ℕ))⁻¹ := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hs : firstCellS τ N = 0 := firstCellS_zero_value τ N
  have hvEq : cutNetPt (firstCellS τ) mesh N k =
      (k : ℝ) / (N : ℝ) ^ (258 : ℕ) := by
    simp [CutHypTheta.cutNetPt, hs, hmesh]
  have hpow258 : (N : ℝ) ^ (258 : ℕ) =
      (N : ℝ) ^ (248 : ℕ) * (N : ℝ) ^ (10 : ℕ) := by
    rw [← pow_add]
  have hpow248 : (N : ℝ) ^ (248 : ℕ) =
      ((N : ℝ) ^ (124 : ℕ)) ^ 2 := by
    rw [← pow_mul]
  have hkR : (k : ℝ) ≤ (N : ℝ) ^ (10 : ℕ) := by exact_mod_cast hk
  have hden : 0 < (N : ℝ) ^ (258 : ℕ) := pow_pos hNpos _
  have htime0 : 0 ≤ (k : ℝ) / (N : ℝ) ^ (258 : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have htime : (k : ℝ) / (N : ℝ) ^ (258 : ℕ) ≤
      ((N : ℝ) ^ (124 : ℕ))⁻¹ ^ 2 := by
    rw [hpow258]
    calc
      (k : ℝ) / ((N : ℝ) ^ (248 : ℕ) * (N : ℝ) ^ (10 : ℕ)) ≤
          (N : ℝ) ^ (10 : ℕ) /
            ((N : ℝ) ^ (248 : ℕ) * (N : ℝ) ^ (10 : ℕ)) :=
        div_le_div_of_nonneg_right hkR (by positivity)
      _ = ((N : ℝ) ^ (124 : ℕ))⁻¹ ^ 2 := by
        rw [hpow248]
        field_simp [ne_of_gt hNpos]
  have hsqrt : Real.sqrt ((k : ℝ) / (N : ℝ) ^ (258 : ℕ)) ≤
      ((N : ℝ) ^ (124 : ℕ))⁻¹ :=
    (Real.sqrt_le_iff).2 ⟨inv_nonneg.mpr (pow_pos hNpos _).le, htime⟩
  rw [hvEq]
  exact hsqrt

/-- On the exact T1149/T1150 first-cell schedule (`E=0`, `D=60`, and the
T995 loss `δ/100`), every fixed `p ≥ 1` has an `N⁻¹` integral bound for the
actual positive-time cross budget, uniformly over active early cells and
every two-loop output. -/
theorem eventually_firstCell_early_cross_budget_integral_le
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N,
        k ≤ N ^ 10 →
        ∀ a : LoopArg (d.L N) 2,
          (∫ r in (firstCellS τ N)..
            cutNetPt (firstCellS τ) mesh N k,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              (firstCellS τ) (firstCellT τ) N k p a r) ≤
            (N : ℝ) ^ (-1 : ℝ) := by
  have hregData := firstCell_hypotheses hτ hδ hsmall
  have hsEq := firstCellS_eq_zero τ
  have hmom := eventually_jointRate_momNorm_le_inv hτ hδ hsmall p hp
  have htime := eventually_intervalIntegrable_positive_time_cross_budget
    (E := 0) (D := 60) (c := 1 / 2)
    (by norm_num) (by norm_num) hregData.2.2.1 hregData.2.2.2.1
    hregData.2.2.2.2 (by norm_num) hregData.2.1
    hregData.1.le p hp
  have hmeshEvent := APrimeGeneralMovingMesh.eventually_targetMesh_eq (60 : ℝ)
  filter_upwards [hmom, htime, hmeshEvent, eventually_ge_atTop (2 : ℕ),
      eventually_ge_atTop p]
    with N hmomN htimeN hmeshN hN2 hNp
  have hNpos : 0 < N := by omega
  have hs0 : 0 ≤ firstCellS τ N := hregData.2.2.1 N
  have hstarget : firstCellS τ N ≤ firstCellT τ N := hregData.2.2.2.1 N
  have htpos : firstCellT τ N < 1 := hregData.2.2.2.2 N
  have hmesh : mesh N = (N : ℝ) ^ (258 : ℕ) := by
    change APrimeGeneralMovingMesh.targetMesh 60 N = (N : ℝ) ^ (258 : ℕ)
    rw [hmeshN]
    norm_num
  intro k hk hkEarly a
  let v := cutNetPt (firstCellS τ) mesh N k
  have hvWindow : v ∈ Icc (firstCellS τ N) (firstCellT τ N) := by
    dsimp [v]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window
      hregData.2.2.2.1 hk
  have hsv : firstCellS τ N ≤ v := hvWindow.1
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hp)
  have hcoeffFormula :
      APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ)) = (15 / 8 : ℝ) * (p : ℝ) := by
    unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
    push_cast
    field_simp [ne_of_gt hpR]
    ring
  let C : ℝ := ((15 / 8 : ℝ) * (p : ℝ)) * (N : ℝ) ^ (-1 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbudgetInt := htimeN k hk a
  have hmajorInt :=
    APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      C (firstCellS τ N) v hs0 hsv
  have hpoint : ∀ r ∈ Icc (firstCellS τ N) v,
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (firstCellS τ) (firstCellT τ) N k p a r ≤ C / √r := by
    intro r hr
    by_cases hrpos : 0 < r
    · have hM := hmomN k hk hkEarly a r hr
      have hcoeff : 0 ≤ ((15 / 8 : ℝ) * (p : ℝ)) / √r := by positivity
      have hbudgetEq :
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (firstCellS τ) (firstCellT τ) N k p a r =
          (((15 / 8 : ℝ) * (p : ℝ)) / √r) *
            MomentDuhamel.momNorm (Gauss.P d) (2 * p)
              (APrimeCrossJointSplit.jointRate d 0 60
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (firstCellS τ) mesh N k
                (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
                  (firstCellT τ) mesh N)
                Step2.sigPM a v r) := by
        unfold APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        rw [← hcoeffFormula]
        field_simp [ne_of_gt hpR, ne_of_gt (Real.sqrt_pos.2 hrpos)]
        ring
      calc
        _ = (((15 / 8 : ℝ) * (p : ℝ)) / √r) *
              MomentDuhamel.momNorm (Gauss.P d) (2 * p)
                (APrimeCrossJointSplit.jointRate d 0 60
                  (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                  (firstCellS τ) mesh N k
                  (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
                    (firstCellT τ) mesh N)
                  Step2.sigPM a v r) := hbudgetEq
        _ ≤ (((15 / 8 : ℝ) * (p : ℝ)) / √r) * (N : ℝ) ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left hM hcoeff
        _ = C / √r := by
          dsimp [C]
          field_simp [ne_of_gt (Real.sqrt_pos.2 hrpos)]
    · have hrnonneg : 0 ≤ r := le_trans hs0 hr.1
      have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) hrnonneg
      subst r
      simp [APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget,
        C]
  have hmono := intervalIntegral.integral_mono_on hsv hbudgetInt hmajorInt hpoint
  have hmono' :
      (∫ r in (firstCellS τ N)..
        cutNetPt (firstCellS τ) mesh N k,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) (firstCellT τ) N k p a r) ≤
      ∫ r in (firstCellS τ N)..v, C / √r := by
    simpa [v] using hmono
  have hmajorEq :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      C (firstCellS τ N) v hs0 hsv
  have hsval := firstCellS_zero_value τ N
  have hvSqrt := early_endpoint_sqrt_bound (τ := τ) hN2 hkEarly hmesh
  have hCmul : 0 ≤ 2 * C := by positivity
  have hNreal2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNreal1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hpowMon : (N : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (124 : ℕ) := by
    exact pow_le_pow_right₀ hNreal1 (by norm_num)
  have hpowLow : 4 ≤ (N : ℝ) ^ (124 : ℕ) := by
    calc
      4 ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith [sq_nonneg ((N : ℝ) - 2)]
      _ ≤ (N : ℝ) ^ (124 : ℕ) := hpowMon
  have hNpReal : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNp
  have hcoeffBound : (15 / 4 : ℝ) * (p : ℝ) ≤ (N : ℝ) ^ (124 : ℕ) := by
    have h15 : (15 / 4 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    have hprod : (15 / 4 : ℝ) * (p : ℝ) ≤
        (N : ℝ) ^ (2 : ℕ) * (N : ℝ) :=
      mul_le_mul h15 hNpReal (by positivity) (by positivity)
    have hpowMon3 : (N : ℝ) ^ (3 : ℕ) ≤ (N : ℝ) ^ (124 : ℕ) := by
      exact pow_le_pow_right₀ hNreal1 (by norm_num)
    calc
      (15 / 4 : ℝ) * (p : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) * (N : ℝ) := hprod
      _ = (N : ℝ) ^ (3 : ℕ) := by ring
      _ ≤ (N : ℝ) ^ (124 : ℕ) := hpowMon3
  have hfrac : ((15 / 4 : ℝ) * (p : ℝ)) / (N : ℝ) ^ (124 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hcoeffBound
  have hNinv : (N : ℝ) ^ (-1 : ℝ) = (N : ℝ)⁻¹ := by
    rw [Real.rpow_neg hNnonneg, Real.rpow_one]
  have hfinish : 2 * C * ((N : ℝ) ^ (124 : ℕ))⁻¹ ≤
      (N : ℝ) ^ (-1 : ℝ) := by
    have hfactor : 2 * C * ((N : ℝ) ^ (124 : ℕ))⁻¹ =
        (((15 / 4 : ℝ) * (p : ℝ)) / (N : ℝ) ^ (124 : ℕ)) *
          (N : ℝ) ^ (-1 : ℝ) := by
      dsimp [C]
      rw [hNinv]
      field_simp [ne_of_gt (show (0 : ℝ) < (N : ℝ) by positivity)]
      ring
    rw [hfactor]
    calc
      _ ≤ 1 * (N : ℝ) ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg (by positivity) _)
      _ = (N : ℝ) ^ (-1 : ℝ) := one_mul _
  calc
    (∫ r in (firstCellS τ N)..
        cutNetPt (firstCellS τ) mesh N k,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) (firstCellT τ) N k p a r)
        ≤ ∫ r in (firstCellS τ N)..v, C / √r := hmono'
    _ = 2 * C * (√v - √(firstCellS τ N)) := hmajorEq
    _ = 2 * C * √v := by rw [hsval, Real.sqrt_zero, sub_zero]
    _ ≤ 2 * C * ((N : ℝ) ^ (124 : ℕ))⁻¹ :=
      mul_le_mul_of_nonneg_left hvSqrt hCmul
    _ ≤ (N : ℝ) ^ (-1 : ℝ) := hfinish

/-- A simultaneous explicit witness for the hypotheses and the transition
range: T1051 supplies an eventually active `k=2` strict-transition sample
with the same first-cell functions and canonical order. -/
theorem nondegenerate_active_k2_transition_witness :
    ∃ τ c δ : ℝ, 0 < τ ∧ 0 < c ∧ 0 < δ ∧
      δ ≤ min 1 (c / 100) ∧
      Cond272Reg (Gauss.band d) 0 (firstCellS τ) (firstCellT τ) c ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ x ∈ Set.Ioo 0 (2 / Real.sqrt ((mesh N)⁻¹)),
          let ω := APrimeSmoothTransition.scalarSample d x
          2 ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N ∧
          ω ∈ APrimeCrossJointSplit.transition d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (firstCellS τ) mesh N 2
            (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
              (firstCellT τ) mesh N) := by
  refine ⟨1, 1 / 2, 1 / 200, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · norm_num
  · exact (firstCell_hypotheses (τ := 1) (δ := 1 / 200)
      (by norm_num) (by norm_num) (by norm_num)).2.1
  · have hsource :=
      APrimeGeneralMovingTargetTransitionExists.eventually_exampleGrow_target_transition
        (τ := 1) (c := 1 / 2) (δ := 1 / 200)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hsEq := firstCellS_eq_zero (1 : ℝ)
    filter_upwards [hsource] with N hN
    obtain ⟨_hs, _ht, hactive, x, hx, htrans, _hratio₁, _hratio₂⟩ := hN
    refine ⟨x, hx, ?_, ?_⟩
    · simpa [hsEq] using hactive
    · simpa [hsEq] using htrans

#print axioms eventually_jointRate_momNorm_le_inv
#print axioms eventually_firstCell_early_cross_budget_integral_le
#print axioms nondegenerate_active_k2_transition_witness

end RBM.APrimeGeneralMovingEarlyCrossBudgetAllOrders
