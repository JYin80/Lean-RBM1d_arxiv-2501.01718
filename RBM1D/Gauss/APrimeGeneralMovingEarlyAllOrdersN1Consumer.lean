/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingEarlyCrossBudgetAllOrders
import RBM1D.Gauss.APrimeGeneralMovingDriftGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeSlotArith

/-!
# T1271: exact all-fixed-order first-cell N1 consumer

For the literal T995 first-cell schedule, the all-sample drift envelope and
the all-fixed-order early cross payment make the combined actual smooth drift
and positive-time cross integral smaller than the exact T230 A-prime drift
slot. This is a fixed-energy, fixed-D, first-cell result.
-/

namespace RBM.APrimeGeneralMovingEarlyAllOrdersN1Consumer

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta Real
open APrimeGeneralMovingCrossBudgetTimeIntegrable

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh 60

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
  have hreg0 := APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg hτ
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

private theorem firstCell_endpoint_length_bound {τ : ℝ} {N k : ℕ}
    (hN : 2 ≤ N) (hk : k ≤ N ^ 10)
    (hmesh : mesh N = (N : ℝ) ^ (258 : ℕ)) :
    cutNetPt (firstCellS τ) mesh N k - firstCellS τ N ≤
      (N : ℝ) ^ (-(248 : ℝ)) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hs : firstCellS τ N = 0 := by
    exact congrFun (firstCellS_eq_zero τ) N
  have hvEq : cutNetPt (firstCellS τ) mesh N k =
      (k : ℝ) / (N : ℝ) ^ (258 : ℕ) := by
    simp [CutHypTheta.cutNetPt, hs, hmesh]
  have hkR : (k : ℝ) ≤ (N : ℝ) ^ (10 : ℕ) := by exact_mod_cast hk
  have hden : 0 < (N : ℝ) ^ (258 : ℕ) := by positivity
  have hsub : (N : ℝ) ^ (10 : ℕ) / (N : ℝ) ^ (258 : ℕ) =
      (N : ℝ) ^ (-(248 : ℝ)) := by
    rw [show (N : ℝ) ^ (10 : ℕ) = (N : ℝ) ^ (10 : ℝ) by
          norm_num [Real.rpow_natCast],
        show (N : ℝ) ^ (258 : ℕ) = (N : ℝ) ^ (258 : ℝ) by
          norm_num [Real.rpow_natCast]]
    rw [← Real.rpow_sub hNpos]
    congr 1
    norm_num
  calc
    cutNetPt (firstCellS τ) mesh N k - firstCellS τ N =
        (k : ℝ) / (N : ℝ) ^ (258 : ℕ) := by rw [hvEq, hs]; ring
    _ ≤ (N : ℝ) ^ (10 : ℕ) / (N : ℝ) ^ (258 : ℕ) :=
      div_le_div_of_nonneg_right hkR (le_of_lt hden)
    _ = (N : ℝ) ^ (-(248 : ℝ)) := hsub

/-- The T995 common-event positive-weight witness, whose prefix and terminal
time are T579's actual `firstCellS τ` and `firstCellT τ`. -/
noncomputable abbrev nondegenerate_common_support_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- T1187's active `k=2` strict-transition witness at the same literal
first-cell schedule and smoothing order. -/
noncomputable abbrev nondegenerate_active_k2_transition_witness :=
  APrimeGeneralMovingEarlyCrossBudgetAllOrders.nondegenerate_active_k2_transition_witness

/-- At the literal `E=0`, `D=60` first-cell schedule, for each fixed `p ≥ 1`
the sum of the actual smooth-weight drift norm budget and the complete
positive-time cross budget fits the exact drift term of `APrimeOneStep`.
The eventual cutoff is taken after `τ`, `δ`, and `p`, uniformly over all
active early cells `k ≤ N^10` and every two-loop output. -/
theorem eventually_integral_firstCell_actual_drift_cross_le_N1_slot
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N,
        k ≤ N ^ 10 →
        ∀ a : LoopArg (d.L N) 2,
          let x := (N : ℝ) ^ (δ / 8)
          let v := cutNetPt (firstCellS τ) mesh N k
          let R := Step2Moment.ratR 0 (firstCellS τ) N v
          2 * (∫ u in (firstCellS τ N)..v,
            APrimeGeneralMovingSmoothDriftNormBudget.g 0 60
              (firstCellS τ) (firstCellT τ)
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u +
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              (firstCellS τ) (firstCellT τ) N k p a u) ≤
            APrimeOneStep.driftTerm (mE 0).im x R
              (APrimeInit.slotXi' x)
              (APrimeSlotArith.slotA x R)
              (APrimeSlotArith.slotEps x R)
              (APrimeSlotArith.slotQ R)
              (APrimeSlotArith.slotBeta x R)
              (APrimeSlotArith.slotGamma x R)
              (APrimeSlotArith.slotJv x R) / R ^ 4 := by
  have hregData := firstCell_hypotheses hτ hδ hsmall
  have henv := APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
    (E := 0) (D := 60) (c := 1 / 2)
    (by norm_num) (by norm_num) hregData.2.2.1 hregData.2.2.2.1
    hregData.2.2.2.2 (by norm_num) hregData.2.1
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq (60 : ℝ)
  have hCross :=
    APrimeGeneralMovingEarlyCrossBudgetAllOrders.eventually_firstCell_early_cross_budget_integral_le
      hτ hδ hsmall p hp
  have hCrossIntegrable :=
    eventually_intervalIntegrable_positive_time_cross_budget
      (E := 0) (D := 60) (c := 1 / 2)
      (by norm_num) (by norm_num) hregData.2.2.1 hregData.2.2.2.1
      hregData.2.2.2.2 (by norm_num) hregData.2.1
      (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      p hp
  filter_upwards [henv, hMesh, hCross, hCrossIntegrable,
      eventually_ge_atTop (8 : ℕ)] with N henvN hMeshN hCrossN hCrossIntN hN8
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNrealPos : (0 : ℝ) < (N : ℝ) := by linarith
  have hs0 := hregData.2.2.1 N
  have hst := hregData.2.2.2.1 N
  have ht1 := hregData.2.2.2.2 N
  have hmesh : mesh N = (N : ℝ) ^ (258 : ℕ) := by
    change APrimeGeneralMovingMesh.targetMesh 60 N = (N : ℝ) ^ (258 : ℕ)
    rw [hMeshN]
    norm_num
  have hmE : (mE 0).im = 1 := by
    rw [mE_im]
    have hrad : (4 : ℝ) - (0 : ℝ) ^ 2 = (2 : ℝ) ^ 2 := by norm_num
    rw [hrad, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hmPos : 0 < (mE 0).im := by rw [hmE]; norm_num
  have hsmallInv : (N : ℝ) ^ (-(1 : ℝ)) ≤ (1 / 8 : ℝ) := by
    rw [Real.rpow_neg_one]
    have hNreal8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
    have hInv := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 8) hNreal8
    simpa only [one_div] using hInv
  have hpow180 : (N : ℝ) ^ (-(180 : ℝ)) ≤ (N : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
  intro k hk hkEarly a
  dsimp only
  let x := (N : ℝ) ^ (δ / 8)
  let v := cutNetPt (firstCellS τ) mesh N k
  let R := Step2Moment.ratR 0 (firstCellS τ) N v
  have hvWindow : v ∈ Icc (firstCellS τ N) (firstCellT τ N) := by
    dsimp [v]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window
      hregData.2.2.2.1 hk
  have hsv : firstCellS τ N ≤ v := hvWindow.1
  have hv1 : v < 1 := hvWindow.2.trans_lt ht1
  have hRpos : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos (by norm_num) (hsv.trans_lt hv1) hv1
  have hRge : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR (by norm_num) hsv hv1
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hNreal (by positivity)
  have hlength := firstCell_endpoint_length_bound (τ := τ) hN2 hkEarly hmesh
  have hDriftInt : IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g 0 60
        (firstCellS τ) (firstCellT τ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a)
      volume (firstCellS τ N) v := by
    simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
      APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      (E := 0) (D := 60) (s := firstCellS τ) (t := firstCellT τ)
      (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (p := p) (N := N) (k := k) (by norm_num) hregData.2.2.1
      hregData.2.2.2.1 hregData.2.2.2.2 hNpos hk a
  have hCrossInt : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (firstCellS τ) (firstCellT τ) N k p a)
      volume (firstCellS τ N) v := by
    simpa [mesh, v] using hCrossIntN k hk a
  have hDriftPoint : ∀ u ∈ Icc (firstCellS τ N) v,
      APrimeGeneralMovingSmoothDriftNormBudget.g 0 60
        (firstCellS τ) (firstCellT τ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u ≤
          (N : ℝ) ^ (68 : ℝ) := by
    intro u hu
    have henvPoint := henvN k hk u hu a
    let : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
    have hnorm := APrimeModel.momNormW_le_of_le_on
      (P := Gauss.P d)
      (W := APrimeGeneralMovingSmoothDriftNormBudget.weight 0 60
        (firstCellS τ) (firstCellT τ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k)
      (Y := APrimeGeneralMovingSmoothDriftNormBudget.drift 0 60
        (firstCellS τ) (firstCellT τ) N k a u)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg 0 60
        (firstCellS τ) (firstCellT τ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one 0 60
        (firstCellS τ) (firstCellT τ)
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k)
      (p := p) (by omega) (c := (N : ℝ) ^ (68 : ℝ)) (by positivity)
      (G := Set.univ)
      (by intro ω _
          simpa [APrimeGeneralMovingSmoothDriftNormBudget.drift,
            APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
            show (60 : ℝ) + 8 = 68 by norm_num] using henvPoint ω)
      (by intro ω hω; exact (hω (Set.mem_univ ω)).elim)
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift] using hnorm
  have hDriftMono := intervalIntegral.integral_mono_on hsv hDriftInt
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (N : ℝ) ^ (68 : ℝ)) volume (firstCellS τ N) v)
    hDriftPoint
  have hDriftBound :
      (∫ u in (firstCellS τ N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g 0 60
          (firstCellS τ) (firstCellT τ)
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
        (N : ℝ) ^ (-(180 : ℝ)) := by
    have hconst := hDriftMono
    rw [intervalIntegral.integral_const, smul_eq_mul] at hconst
    have hN68pos : 0 ≤ (N : ℝ) ^ (68 : ℝ) := by positivity
    have hpowEq : (N : ℝ) ^ (-(248 : ℝ)) * (N : ℝ) ^ (68 : ℝ) =
        (N : ℝ) ^ (-(180 : ℝ)) := by
      rw [← Real.rpow_add hNrealPos]
      congr 1
      norm_num
    calc
      _ ≤ (v - firstCellS τ N) * (N : ℝ) ^ (68 : ℝ) := hconst
      _ ≤ (N : ℝ) ^ (-(248 : ℝ)) * (N : ℝ) ^ (68 : ℝ) :=
        mul_le_mul_of_nonneg_right hlength hN68pos
      _ = (N : ℝ) ^ (-(180 : ℝ)) := hpowEq
  have hCrossBound := hCrossN k hk hkEarly a
  have hadd := intervalIntegral.integral_add hDriftInt hCrossInt
  have hsum :
      (∫ u in (firstCellS τ N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g 0 60
          (firstCellS τ) (firstCellT τ)
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) (firstCellT τ) N k p a u) ≤
      (N : ℝ) ^ (-(180 : ℝ)) + (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [hadd]
    exact add_le_add hDriftBound hCrossBound
  have hsumSmall :
      2 * ((N : ℝ) ^ (-(180 : ℝ)) + (N : ℝ) ^ (-(1 : ℝ))) ≤ 1 / 2 := by
    have hpow180' := hpow180
    have hpow1' := hsmallInv
    calc
      _ ≤ 2 * ((N : ℝ) ^ (-(1 : ℝ)) + (N : ℝ) ^ (-(1 : ℝ))) := by
        gcongr
      _ ≤ 2 * ((1 / 8 : ℝ) + 1 / 8) := by gcongr
      _ = 1 / 2 := by norm_num
  have hRpow4 : R ^ 4 ≠ 0 := ne_of_gt (pow_pos hRpos 4)
  have hApos : 0 < APrimeSlotArith.slotA x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotA
    positivity
  have hEpsNonneg : 0 ≤ APrimeSlotArith.slotEps x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotEps
    positivity
  have hBetaNonneg : 0 ≤ APrimeSlotArith.slotBeta x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotBeta
    positivity
  have hGammaNonneg : 0 ≤ APrimeSlotArith.slotGamma x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotGamma
    positivity
  have hJvNonneg : 0 ≤ APrimeSlotArith.slotJv x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotJv
    positivity
  have hXiNonneg : 0 ≤ APrimeInit.slotXi' x := by
    unfold APrimeInit.slotXi'
    positivity
  have hx0 : 0 ≤ x := by linarith
  have hnear := APrimeSlotArith.driftTerm_ge_near
    (q := APrimeSlotArith.slotQ R)
    hmPos hx0 hRpos.le hXiNonneg hApos hEpsNonneg hBetaNonneg
    hGammaNonneg hJvNonneg
  have hnearEq :
      APrimeInit.slotXi' x *
        (x * (mE 0).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 =
      x ^ (5 / 4 : ℝ) / (2 * (mE 0).im) := by
    have hxpos : 0 < x := by linarith
    rw [show APrimeInit.slotXi' x = x ^ (1 / 4 : ℝ) by rfl,
      show APrimeSlotArith.slotQ R = R ^ 2 / 2 by rfl]
    have hxpow : x ^ (1 / 4 : ℝ) * x = x ^ (5 / 4 : ℝ) := by
      calc
        x ^ (1 / 4 : ℝ) * x = x ^ (1 / 4 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ ((1 / 4 : ℝ) + 1) := by rw [← Real.rpow_add hxpos]
        _ = x ^ (5 / 4 : ℝ) := by congr 1; norm_num
    rw [show x * (mE 0).im⁻¹ * R ^ 2 * (R ^ 2 / 2) =
      (x * (mE 0).im⁻¹ / 2) * R ^ 4 by ring]
    field_simp [ne_of_gt hmPos, ne_of_gt hRpos]
    rw [hxpow]
  have hslotLower :
      (1 / (2 * (mE 0).im) : ℝ) ≤
        APrimeOneStep.driftTerm (mE 0).im x R
          (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R)
          (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R)
          (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R)
          (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    have hnearDiv := div_le_div_of_nonneg_right hnear (le_of_lt (pow_pos hRpos 4))
    rw [hnearEq] at hnearDiv
    have hpow : (1 : ℝ) ≤ x ^ (5 / 4 : ℝ) :=
      Real.one_le_rpow hx (by norm_num)
    exact le_trans
      (div_le_div_of_nonneg_right hpow (by positivity)) hnearDiv
  have hslotLower' :
      (1 / 2 : ℝ) ≤
        APrimeOneStep.driftTerm (mE 0).im x R
          (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R)
          (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R)
          (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R)
          (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    simpa [hmE] using hslotLower
  calc
    2 * (∫ u in (firstCellS τ N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g 0 60
          (firstCellS τ) (firstCellT τ)
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          0 60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) (firstCellT τ) N k p a u)
        ≤ 2 * ((N : ℝ) ^ (-(180 : ℝ)) + (N : ℝ) ^ (-(1 : ℝ)) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 1 / 2 := hsumSmall
    _ ≤ APrimeOneStep.driftTerm (mE 0).im x R
          (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R)
          (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R)
          (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R)
          (APrimeSlotArith.slotJv x R) / R ^ 4 := hslotLower'

#print axioms eventually_integral_firstCell_actual_drift_cross_le_N1_slot
#print axioms nondegenerate_common_support_witness
#print axioms nondegenerate_active_k2_transition_witness

end
end RBM.APrimeGeneralMovingEarlyAllOrdersN1Consumer
