/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic

/-!
# T1259: full p=1 cross budget on the first positive moving cell

This theorem integrates the exact T1207 full-to-norm-good reduction, then
uses the accepted T1247 norm-good pointwise reduction and T1245 profile bound
on the first positive cell.  The first-cell mesh retains the endpoint factor
and both inverse-N payments.
-/

namespace RBM.APrimeGeneralMovingFirstCellFullCrossMicroscopic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open RBM.APrimeGeneralMovingCrossBudgetGoodReduction
open RBM.APrimeGeneralMovingCrossHcrossPositive
open RBM.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
open RBM.APrimeGeneralMovingCrossEnvelopeIntegral
open RBM.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
open RBM.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's nondegenerate same-event witness, including an eventually active
first positive cell and positive actual smooth weight. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic.nondegenerate_positive_cell_witness

/-- On the active first positive target-mesh cell, the exact full p=1
positive-time cross budget has the microscopic integrated bound.  One
eventual cutoff works for every output loop argument. -/
theorem eventually_integral_firstCell_positiveTimeCrossBudget_le
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        (∫ u in (s N)..(cutNetPt s (mesh D) N 1),
          positiveTimeCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a u) ≤
          (15 / 2 : ℝ) * crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) *
            Step2Moment.ratR E s N
              (cutNetPt s (mesh D) N 1) ^ (-(2 : ℝ)) +
          (15 / 2 : ℝ) * (N : ℝ) ^ (-2 * D - 10) := by
  have hdeltaWeight :
      0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hfull := _root_.RBM.APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
  have hgoodInt := _root_.RBM.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
  have hgoodPoint := _root_.RBM.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic.eventually_normGoodCrossBudget_le_crossProfile_microscopic
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hprofilePoint :=
    _root_.RBM.APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (c := c) (s := s) (t := t) (δ := δ)
      hE (by linarith) hs0 hst ht1 hc hreg hδ hδsmall
  have hmesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hEta :=
    Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  filter_upwards [hfull, hgoodInt, hgoodPoint, hprofilePoint, hmesh,
      hEta, eventually_ge_atTop 1] with
    N hfullN hgoodIntN hgoodPointN hprofilePointN hmeshN hEtaN hN
  have hNnat : 1 ≤ N := by omega
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  intro hk a
  let v := cutNetPt s (mesh D) N 1
  have hvWindow : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hvWindow.1
  have hv1 : v < 1 := hvWindow.2.trans_lt (ht1 N)
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hsv.trans_lt hv1) hv1
  have hR : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hsv hv1
  have hRpow0 :
      0 ≤ Step2Moment.ratR E s N v ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg hRpos.le _
  have hconstPos : 0 < crossProfilePointwiseConst :=
    _root_.RBM.APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hEtaT := hEtaN
  have hEtaTtoS : etaT E (t N) ≤ etaT E (s N) :=
    Gauss.etaT_le_of_le hE (hst N)
  have hEtaS : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (s N) :=
    hEtaT.trans hEtaTtoS
  have hEtaSpos : 0 < etaT E (s N) := by
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hEtaS
  have hEtaInv : (etaT E (s N))⁻¹ ≤ (N : ℝ) := by
    have hi := inv_anti₀
      (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hEtaS
    simpa only [Real.rpow_neg hNpos.le, Real.rpow_one, inv_inv] using hi
  have hEtaInv0 : 0 ≤ (etaT E (s N))⁻¹ := inv_nonneg.mpr hEtaSpos.le
  have hgap0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hvsub : v - s N = 1 / mesh D N := by
    dsimp [v, CutHypTheta.cutNetPt]
    ring
  have hrecip :
      (1 : ℝ) / (N : ℝ) ^ (4 * D + 18) =
        (N : ℝ) ^ (-(4 * D + 18)) := by
    rw [Real.rpow_neg hNpos.le]
    simp only [one_div]
  have hpow :
      ((N : ℝ) ^ (-(2 * D + 9))) ^ 2 =
        (N : ℝ) ^ (-(4 * D + 18)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hroot :
      Real.sqrt ((1 : ℝ) / (N : ℝ) ^ (4 * D + 18)) =
        (N : ℝ) ^ (-(2 * D + 9)) := by
    rw [hrecip, ← hpow]
    exact Real.sqrt_sq (Real.rpow_nonneg hNpos.le _)
  have hgap : Real.sqrt v - Real.sqrt (s N) ≤
      (N : ℝ) ^ (-(2 * D + 9)) := by
    have habs := RBM.abs_sqrt_sub_sqrt_le (le_trans (hs0 N) hsv) (hs0 N)
    have hrootGap :
        Real.sqrt (v - s N) = (N : ℝ) ^ (-(2 * D + 9)) := by
      calc
        Real.sqrt (v - s N) = Real.sqrt (1 / mesh D N) := by rw [hvsub]
        _ = Real.sqrt ((1 : ℝ) / (N : ℝ) ^ (4 * D + 18)) := by
          rw [show mesh D N = (N : ℝ) ^ (4 * D + 18) from hmeshN]
        _ = _ := hroot
    rw [abs_of_nonneg hgap0,
      abs_of_nonneg (sub_nonneg.mpr hsv)] at habs
    calc
      Real.sqrt v - Real.sqrt (s N) ≤ Real.sqrt (v - s N) := habs
      _ = (N : ℝ) ^ (-(2 * D + 9)) := hrootGap
  let R := Step2Moment.ratR E s N v
  let alpha := 13 * δ / 640
  let Cprof := (15 / 4 : ℝ) * crossProfilePointwiseConst *
      (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ))
  let Cbad := (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ))
  let Cgood := Cprof + Cbad
  have hCprof0 : 0 ≤ Cprof := by
    dsimp [Cprof, R, alpha]
    positivity
  have hCbad0 : 0 ≤ Cbad := by dsimp [Cbad]; positivity
  have hCgood0 : 0 ≤ Cgood := add_nonneg hCprof0 hCbad0
  have hgoodPointwise :
      ∀ r ∈ Icc (s N) v,
        normGoodCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a r ≤ Cgood / Real.sqrt r := by
    intro r hr
    have hr0 : 0 ≤ r := (hs0 N).trans hr.1
    by_cases hrpos : 0 < r
    · have hng := hgoodPointN 1 hk a r hr hrpos
      have hprof := hprofilePointN 1 hk a r hr hrpos
      have hprofileScaled :=
        mul_le_mul_of_nonneg_left hprof (by norm_num : (0 : ℝ) ≤ 15 / 4)
      have hprofileScaled' :
          (15 / 4 : ℝ) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a r ≤
            (15 / 4 : ℝ) *
              (crossProfilePointwiseConst * (N : ℝ) ^ alpha *
                (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) / Real.sqrt r) := by
        simpa [R, alpha] using hprofileScaled
      have hprofileC :
          (15 / 4 : ℝ) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a r ≤
            Cprof / Real.sqrt r := by
        calc
          _ ≤ (15 / 4 : ℝ) *
                (crossProfilePointwiseConst * (N : ℝ) ^ alpha *
                  (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) / Real.sqrt r) := hprofileScaled'
          _ = Cprof / Real.sqrt r := by
                dsimp [Cprof]
                ring
      have hsqrtInv : Real.sqrt r⁻¹ = 1 / Real.sqrt r := by simp
      calc
        _ ≤ (15 / 4 : ℝ) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a r +
              (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) * Real.sqrt r⁻¹ := hng
        _ ≤ Cprof / Real.sqrt r + Cbad / Real.sqrt r := by
              dsimp [Cprof, Cbad, R, alpha]
              rw [hsqrtInv]
              exact add_le_add hprofileC (by
                simp only [div_eq_mul_inv, one_mul]
                exact le_rfl)
        _ = Cgood / Real.sqrt r := by
              dsimp [Cgood]
              rw [add_div]
    · have hrEq : r = 0 := le_antisymm (le_of_not_gt hrpos) hr0
      have hgood0 :
          normGoodCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a r = 0 := by
        simp [normGoodCrossBudget,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget, hrEq]
      have hgood0' :
          normGoodCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a 0 = 0 := by simpa [hrEq] using hgood0
      simpa [hrEq, hgood0']
  have hgoodInt := hgoodIntN 1 hk a
  have hEnvelopeInt :
      IntervalIntegrable (fun r => Cgood / Real.sqrt r) volume (s N) v :=
    intervalIntegrable_invSqrtEnvelope Cgood (s N) v (hs0 N) hsv
  have hgoodIntegral :
      (∫ r in (s N)..v,
        normGoodCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a r) ≤
        2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ ∫ r in (s N)..v, Cgood / Real.sqrt r :=
        intervalIntegral.integral_mono_on hsv hgoodInt hEnvelopeInt hgoodPointwise
      _ = 2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) :=
        integral_invSqrtEnvelope Cgood (s N) v (hs0 N) hsv
  have hfullCell := hfullN 1 hk a
  have hcombined :
      (∫ u in (s N)..v,
        positiveTimeCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a u) ≤
        (15 / 2 : ℝ) * crossProfilePointwiseConst *
          (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) := by
    have hfullGood' := hfullCell.trans
      (add_le_add hgoodIntegral (le_of_eq rfl))
    have hfullGoodNorm :
        (∫ u in (s N)..v,
          positiveTimeCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a u) ≤
          2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) +
            (15 * (1 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
              (Real.sqrt v - Real.sqrt (s N)) := by
      simpa [v, mesh] using hfullGood'
    calc
      _ ≤ _ := hfullGoodNorm
      _ = _ := by dsimp [Cgood, Cprof, Cbad, R]; ring
  have hInvGap :
      (etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ) ^ (-2 * D - 8) := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ (-(2 * D + 9)) :=
        mul_le_mul hEtaInv hgap hgap0 (by positivity)
      _ = (N : ℝ) ^ (-2 * D - 8) := by
        calc
          (N : ℝ) * (N : ℝ) ^ (-(2 * D + 9)) =
              (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(2 * D + 9)) := by
                rw [Real.rpow_one]
          _ = (N : ℝ) ^ (1 - (2 * D + 9)) := by
                rw [← Real.rpow_add hNpos]
                congr 1
          _ = (N : ℝ) ^ (-2 * D - 8) := by congr 1 <;> ring
  have hNpowMain :
      (N : ℝ) ^ alpha *
          ((etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N))) ≤
        (N : ℝ) ^ (alpha - 2 * D - 8) := by
    calc
      _ ≤ (N : ℝ) ^ alpha * (N : ℝ) ^ (-2 * D - 8) :=
        mul_le_mul_of_nonneg_left hInvGap (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (alpha - 2 * D - 8) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hNpowBad :
      (N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ) ^ (-2 * D - 10) := by
    calc
      _ ≤ (N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(2 * D + 9)) :=
        mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (-2 * D - 10) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hmainRate :
      crossProfilePointwiseConst * (N : ℝ) ^ alpha *
          (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) ≤
        crossProfilePointwiseConst * (N : ℝ) ^ (alpha - 2 * D - 8) *
          R ^ (-(2 : ℝ)) := by
    have hfactor : 0 ≤ crossProfilePointwiseConst *
        R ^ (-(2 : ℝ)) := mul_nonneg hconstPos.le hRpow0
    calc
      _ = (crossProfilePointwiseConst * R ^ (-(2 : ℝ))) *
          ((N : ℝ) ^ alpha *
            ((etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N)))) := by ring
      _ ≤ (crossProfilePointwiseConst * R ^ (-(2 : ℝ))) *
          (N : ℝ) ^ (alpha - 2 * D - 8) :=
        mul_le_mul_of_nonneg_left hNpowMain hfactor
      _ = _ := by ring
  have hcombinedSmall :
      (15 / 2 : ℝ) * crossProfilePointwiseConst *
          (N : ℝ) ^ alpha * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) ≤
        (15 / 2 : ℝ) * crossProfilePointwiseConst *
          (N : ℝ) ^ (alpha - 2 * D - 8) * R ^ (-(2 : ℝ)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-2 * D - 10) := by
    have hcoef : 0 ≤ (15 / 2 : ℝ) := by norm_num
    exact add_le_add
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hmainRate hcoef)
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hNpowBad hcoef)
  have hfinal := hcombined.trans hcombinedSmall
  simpa [v, mesh, R, alpha, positiveTimeCrossBudget] using hfinal

#print axioms eventually_integral_firstCell_positiveTimeCrossBudget_le
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingFirstCellFullCrossMicroscopic
