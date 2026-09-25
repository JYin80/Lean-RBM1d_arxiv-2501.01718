/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftCrossP1StrictExponent
import RBM1D.Gauss.APrimeSlotArith
import RBM1D.Gauss.APrimeInit

/-!
# T1291: all-active-cell p=1 N1 drift consumer

The accepted T1265 all-cell integral bound fits the concrete A-prime drift
slot. The power margin is `N^(δ/32)`, after fixing `δ > 0` and before the
eventual cutoff. This is a local consumer estimate only.
-/

namespace RBM.APrimeGeneralMovingAllCellP1N1Consumer

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open _root_.RBM.APrimeGeneralMovingDriftCrossP1StrictExponent

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's same-event, positive-actual-weight witness at `p=1` and a positive
active cell. The same resident also makes all fixed structural inputs of the
all-cell consumer jointly satisfiable. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- The literal p=1 T1265 drift-plus-cross integral fits the concrete N1 drift
slot on every active target-mesh cell, including `k=0`, and every output. -/
theorem eventually_all_cell_p1_N1_consumer
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let x := (N : ℝ) ^ (δ / 8)
          let v := cutNetPt s (mesh D) N k
          let R := Step2Moment.ratR E s N v
          2 * (∫ u in (s N)..v,
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u +
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                s t N k 1 a u) ≤
            APrimeOneStep.driftTerm (mE E).im x R
              (APrimeInit.slotXi' x)
              (APrimeSlotArith.slotA x R)
              (APrimeSlotArith.slotEps x R)
              (APrimeSlotArith.slotQ R)
              (APrimeSlotArith.slotBeta x R)
              (APrimeSlotArith.slotGamma x R)
              (APrimeSlotArith.slotJv x R) / R ^ 4 := by
  have hBudget := eventually_integral_drift_add_cross_p1_le_delta_eighth
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hAbsorb := eventually_le_rpow
    (2 * (mE E).im *
      (combinedBudgetConst E))
    (by positivity : 0 < δ / 32)
  filter_upwards [hBudget, hAbsorb, eventually_ge_atTop 1]
    with N hBudgetN hAbsorbN hN1
  intro k hk a
  let x : ℝ := (N : ℝ) ^ (δ / 8)
  let v : ℝ := cutNetPt s (mesh D) N k
  let R : ℝ := Step2Moment.ratR E s N v
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hNge (by positivity)
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hslotXiPower : APrimeInit.slotXi' x = (N : ℝ) ^ (δ / 32) := by
    dsimp [APrimeInit.slotXi', x]
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hslotXiGap :
      2 * (mE E).im *
          combinedBudgetConst E ≤
        APrimeInit.slotXi' x := by
    rw [hslotXiPower]
    exact hAbsorbN
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hsv : s N ≤ v := hv.1
  have hRpos : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos hE (hsv.trans_lt hv1) hv1
  have hRge : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hsv hv1
  have hBudgetCell := hBudgetN k hk a
  have hBudgetCell :
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u) ≤
        combinedBudgetConst E *
          x * R ^ (-(2 : ℝ)) := by
    simpa [x, v, R] using hBudgetCell
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hXi0 : 0 ≤ APrimeInit.slotXi' x := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (APrimeInit.slotXi'_ge_one hx)
  have hA0 : 0 < APrimeSlotArith.slotA x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotA
    positivity
  have hEps0 : 0 ≤ APrimeSlotArith.slotEps x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotEps
    positivity
  have hBeta0 : 0 ≤ APrimeSlotArith.slotBeta x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotBeta
    positivity
  have hGamma0 : 0 ≤ APrimeSlotArith.slotGamma x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotGamma
    positivity
  have hJv0 : 0 ≤ APrimeSlotArith.slotJv x R := by
    have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
    unfold APrimeSlotArith.slotJv
    positivity
  have hNear := APrimeSlotArith.driftTerm_ge_near
    (m := (mE E).im) (x := x) (R := R)
    (Ξ := APrimeInit.slotXi' x)
    (A := APrimeSlotArith.slotA x R)
    (ε := APrimeSlotArith.slotEps x R)
    (q := APrimeSlotArith.slotQ R)
    (β := APrimeSlotArith.slotBeta x R)
    (γ := APrimeSlotArith.slotGamma x R)
    (Jv := APrimeSlotArith.slotJv x R)
    hm hx0 hRpos.le hXi0 hA0 hEps0 hBeta0 hGamma0 hJv0
  have hxiPow : x * APrimeInit.slotXi' x = x ^ (5 / 4 : ℝ) := by
    unfold APrimeInit.slotXi'
    calc
      x * x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + 1 / 4) :=
        (Real.rpow_add (by linarith [hx]) 1 (1 / 4)).symm
      _ = x ^ (5 / 4 : ℝ) := by
        congr 1
        ring
  have hnearEq :
      APrimeInit.slotXi' x *
          (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 =
        x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    rw [show APrimeSlotArith.slotQ R = R ^ 2 / 2 by rfl]
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hRpos, ne_of_gt hm]
    rw [show APrimeInit.slotXi' x * x = x * APrimeInit.slotXi' x by ring,
      hxiPow]
  have hnearDiv :
      APrimeInit.slotXi' x *
          (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 ≤
        APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
    div_le_div_of_nonneg_right hNear (by positivity : 0 ≤ R ^ 4)
  have hNearLower :
      x ^ (5 / 4 : ℝ) / (2 * (mE E).im) ≤
        APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
    hnearEq ▸ hnearDiv
  have hCoeffGap :
      combinedBudgetConst E * x ≤
        x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    have hgapmul := mul_le_mul_of_nonneg_right hslotXiGap hx0
    have hnum :
        2 * (mE E).im * (combinedBudgetConst E * x) ≤
          x ^ (5 / 4 : ℝ) := by
      calc
        _ = (2 * (mE E).im * combinedBudgetConst E) * x := by
              ring
        _ ≤ APrimeInit.slotXi' x * x := hgapmul
        _ = x * APrimeInit.slotXi' x := by ring
        _ = x ^ (5 / 4 : ℝ) := hxiPow
    have hnum' :
        combinedBudgetConst E * x * (2 * (mE E).im) ≤
          x ^ (5 / 4 : ℝ) := by
      calc
        _ = 2 * (mE E).im * (combinedBudgetConst E * x) := by
              ring
        _ ≤ x ^ (5 / 4 : ℝ) := hnum
    exact (le_div_iff₀ (by positivity : 0 < 2 * (mE E).im)).2 hnum'
  have hRinvNonneg : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hRinvLeOne : R ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRge (by norm_num)
  have hNearCoeffNonneg : 0 ≤ x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    positivity
  have hNearWeighted :
      x ^ (5 / 4 : ℝ) / (2 * (mE E).im) * R ^ (-(2 : ℝ)) ≤
        x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    simpa using mul_le_mul_of_nonneg_left hRinvLeOne hNearCoeffNonneg
  calc
    _ ≤ combinedBudgetConst E * x * R ^ (-(2 : ℝ)) := hBudgetCell
    _ ≤ x ^ (5 / 4 : ℝ) / (2 * (mE E).im) * R ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCoeffGap hRinvNonneg
    _ ≤ x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := hNearWeighted
    _ ≤ APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
      hNearLower

#print axioms eventually_all_cell_p1_N1_consumer
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingAllCellP1N1Consumer
