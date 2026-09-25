/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic

/-!
# T1257: first-cell microscopic integral for the norm-good cross budget

This is a Lean smooth-prefix auxiliary estimate.  It integrates the exact
T1201 p=1 norm-good cross budget on the active first target-mesh cell, using
the accepted pointwise inputs T1245 and T1247.  It is not a stopped-process
estimate or a paper-level N1 conclusion.
-/

namespace RBM.APrimeGeneralMovingFirstCellNormGoodCrossMicroscopic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's same-event, nondegenerate active first-positive-cell witness. -/
noncomputable abbrev nondegenerate_positive_first_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- The exact p=1 norm-good cross budget on the active first positive cell has
the microscopic integral bound obtained from the accepted T1245 and T1247
pointwise estimates.  The cutoff is uniform over all output loop arguments. -/
theorem eventually_integral_normGoodCrossBudget_le_first_cell_microscopic
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop,
      1 ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N 1
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a u) ≤
          (15 / 2 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real)^(13 * δ / 640 - 2 * D - 8) *
              Step2Moment.ratR E s N v^(-(2 : Real)) +
            (15 / 4 : Real) * (N : Real)^(-2 * D - 10) := by
  have hDeltaWeight : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hIntegral :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      (E := E) (D := D) (s := s) (t := t) hE hD hs0 hst ht1 hc hreg
      hDeltaWeight 1 (by omega)
  have hNormPoint :=
    APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic.eventually_normGoodCrossBudget_le_crossProfile_microscopic
      (E := E) (D := D) (c := c) (δ := δ) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hProfilePoint :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE (le_trans (by norm_num : (0 : Real) ≤ 60) hD) hs0 hst ht1 hc hreg hδ hδsmall
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hDim := B.dim
  have hScaleLower := hreg.2
  filter_upwards [hIntegral, hNormPoint, hProfilePoint, hMesh, hDim,
      hScaleLower, eventually_ge_atTop 1]
    with N hIntegralN hNormPointN hProfilePointN hMeshN hDimN hScaleLowerN hN
  intro hk a
  let v : Real := cutNetPt s (mesh D) N 1
  have hNpos : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset (show 1 ≤ cutNetTop s t (mesh D) N by exact hk))
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hIntBudget : IntervalIntegrable
      (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N 1 1 a)
      volume (s N) v := by
    simpa [v, mesh] using hIntegralN 1 (by simpa [mesh] using hk) a
  have hEtaTpos : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hEtaSpos : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hEtaST : etaT E (t N) ≤ etaT E (s N) :=
    Gauss.etaT_le_of_le hE (hst N)
  have hEllFacts := EEBridge.eeFacts B hE hs0 ht1 N
    ⟨t N, ⟨hst N, le_rfl⟩⟩
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hDimN.1
  have hScaleUpper : B.scale E N (t N) ≤ (N : Real) * etaT E (t N) := by
    change (B.W N : Real) * B.ell N (t N) * etaT E (t N) ≤ _
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * etaT E (t N) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEllFacts.2.2.2.2 (by exact_mod_cast (B.W_pos N).le))
          hEtaTpos.le
      _ ≤ (N : Real) * etaT E (t N) :=
        mul_le_mul_of_nonneg_right hWL hEtaTpos.le
  have hMargin : (N : Real)^c ≤ B.scale E N (t N) := hScaleLowerN
  have hNc : 1 ≤ (N : Real)^c := Real.one_le_rpow hN1 hc.le
  have hScaleGeOne : 1 ≤ (N : Real) * etaT E (t N) :=
    hNc.trans (hMargin.trans hScaleUpper)
  have hEtaLowerT : 1 / (N : Real) ≤ etaT E (t N) := by
    apply (div_le_iff₀ hNpos).2
    nlinarith [hScaleGeOne]
  have hEtaInvT : (etaT E (t N))⁻¹ ≤ (N : Real) := by
    have hInv := one_div_le_one_div_of_le (by positivity : 0 < 1 / (N : Real)) hEtaLowerT
    simpa [one_div] using hInv
  have hEtaInvS : (etaT E (s N))⁻¹ ≤ (N : Real) := by
    have hInvST : (etaT E (s N))⁻¹ ≤ (etaT E (t N))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hEtaTpos hEtaST
    exact hInvST.trans hEtaInvT
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hKpos :
      0 < APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hProfileN := hProfilePointN 1 (by simpa [mesh] using hk) a
  have hNormN := hNormPointN 1 (by simpa [mesh] using hk) a
  let coeff : Real :=
    (15 / 4 : Real) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
        Step2Moment.ratR E s N v^(-(2 : Real)) +
      (15 / 8 : Real) * (N : Real)^(-1 : Real)
  let boundFn : Real → Real := fun u => coeff * Real.sqrt u⁻¹
  have hCoeffNonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hInvSqrtInt : IntervalIntegrable (fun u : Real => Real.sqrt u⁻¹)
      volume (s N) v :=
    APrimeTimeInt.intervalIntegrable_sqrt_inv hv0
      |>.mono_set (by
        rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hv0]
        intro u hu
        exact ⟨(hs0 N).trans hu.1, hu.2⟩)
  have hIntBound : IntervalIntegrable boundFn volume (s N) v := by
    dsimp [boundFn]
    exact hInvSqrtInt.const_mul coeff
  have hPoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N 1 1 a u ≤ boundFn u := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simp [boundFn, coeff,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget]
    · have huPos : 0 < u := lt_of_le_of_ne (hs0 N |>.trans hu.1) (Ne.symm hu0)
      have hvPoint := hNormN u hu huPos
      have hprof := hProfileN u hu huPos
      have hProfCoeff0 : 0 ≤
          (15 / 4 : Real) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
        positivity
      have hProf := mul_le_mul_of_nonneg_left hprof (by norm_num : (0 : Real) ≤ 15 / 4)
      have hProfSqrt :
          (15 / 4 : Real) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u ≤
            ((15 / 4 : Real) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
                Step2Moment.ratR E s N v^(-(2 : Real))) * Real.sqrt u⁻¹ := by
        calc
          _ ≤ ((15 / 4 : Real) *
                (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                  (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
                  Step2Moment.ratR E s N v^(-(2 : Real)) / Real.sqrt u)) := hProf
          _ = _ := by rw [div_eq_mul_inv, Real.sqrt_inv]; ring
      have hPoint' := add_le_add hProfSqrt
        (le_of_eq (show (15 / 8 : Real) * (N : Real)^(-1 : Real) * Real.sqrt u⁻¹ =
          ((15 / 8 : Real) * (N : Real)^(-1 : Real)) * Real.sqrt u⁻¹ by ring))
      have hCoeffEq :
          (15 / 4 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
              Step2Moment.ratR E s N v^(-(2 : Real)) * Real.sqrt u⁻¹ +
            (15 / 8 : Real) * (N : Real)^(-1 : Real) * Real.sqrt u⁻¹ =
          coeff * Real.sqrt u⁻¹ := by
        dsimp [coeff]
        ring
      calc
        _ ≤
            ((15 / 4 : Real) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
                Step2Moment.ratR E s N v^(-(2 : Real))) * Real.sqrt u⁻¹ +
              ((15 / 8 : Real) * (N : Real)^(-1 : Real)) * Real.sqrt u⁻¹ := by
          exact hvPoint.trans hPoint'
        _ = coeff * Real.sqrt u⁻¹ := hCoeffEq
        _ = boundFn u := rfl
  have hMono := intervalIntegral.integral_mono_on hv.1 hIntBudget hIntBound hPoint
  have hSqrtIntegral :
      (∫ u in (s N)..v, Real.sqrt u⁻¹) =
        2 * (Real.sqrt v - Real.sqrt (s N)) := by
    have hZeroS := APrimeTimeInt.integral_sqrt_inv (hs0 N)
    have hZeroV := APrimeTimeInt.integral_sqrt_inv hv0
    have hAdjacent := intervalIntegral.integral_add_adjacent_intervals
      (APrimeTimeInt.intervalIntegrable_sqrt_inv (hs0 N)) hInvSqrtInt
    rw [hZeroS, hZeroV] at hAdjacent
    linarith
  have hMeshCell : v - s N = 1 / mesh D N := by
    dsimp [v, CutHypTheta.cutNetPt]
    norm_num
  have hMeshPow : v - s N = (N : Real)^(-(4 * D + 18)) := by
    rw [hMeshCell]
    change 1 / APrimeGeneralMovingMesh.targetMesh D N = _
    rw [hMeshN, one_div, ← Real.rpow_neg hNpos.le]
  have hSqrtGap : Real.sqrt v - Real.sqrt (s N) ≤ (N : Real)^(-(2 * D + 9)) := by
    have hsqrtMono : Real.sqrt (s N) ≤ Real.sqrt v := Real.sqrt_le_sqrt hv.1
    have habs := RBM.abs_sqrt_sub_sqrt_le (hs0 N) hv0
    have habs' : |Real.sqrt v - Real.sqrt (s N)| ≤ Real.sqrt |v - s N| := by
      calc
        _ = |Real.sqrt (s N) - Real.sqrt v| := abs_sub_comm _ _
        _ ≤ Real.sqrt |s N - v| := habs
        _ = Real.sqrt |v - s N| := by rw [abs_sub_comm]
    rw [abs_of_nonneg (sub_nonneg.mpr hsqrtMono),
      abs_of_nonneg (sub_nonneg.mpr hv.1)] at habs'
    have hSqrtEq : Real.sqrt (v - s N) = (N : Real)^(-(2 * D + 9)) := by
      rw [hMeshPow, Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    exact habs'.trans_eq hSqrtEq
  have hBudgetInt :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a u) ≤
        coeff * (2 * (N : Real)^(-(2 * D + 9))) := by
    calc
      _ ≤ ∫ u in (s N)..v, boundFn u := hMono
      _ = coeff * (∫ u in (s N)..v, Real.sqrt u⁻¹) := by
        dsimp [boundFn]
        rw [intervalIntegral.integral_const_mul]
      _ = coeff * (2 * (Real.sqrt v - Real.sqrt (s N))) := by rw [hSqrtIntegral]
      _ ≤ coeff * (2 * (N : Real)^(-(2 * D + 9))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSqrtGap (by norm_num))
          hCoeffNonneg
  have hFirst :
      ((15 / 4 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : Real))) *
        (2 * (N : Real)^(-(2 * D + 9))) ≤
      (15 / 2 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real)^(13 * δ / 640 - 2 * D - 8) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
    have hShort :
        (N : Real) * (N : Real)^(-(2 * D + 9)) =
          (N : Real)^(-(2 * D + 8)) := by
      calc
        (N : Real) * (N : Real)^(-(2 * D + 9)) =
            (N : Real)^(-(2 * D + 9)) * (N : Real) := by ring
        _ = (N : Real)^(-(2 * D + 9) + 1) :=
          (Real.rpow_add_one hNpos.ne' (-(2 * D + 9))).symm
        _ = (N : Real)^(1 + (-(2 * D + 9))) := by congr 1 <;> ring
        _ = (N : Real)^(-(2 * D + 8)) := by congr 1 <;> ring
    have hPower :
        (N : Real)^(13 * δ / 640) * (N : Real)^(-(2 * D + 8)) =
          (N : Real)^(13 * δ / 640 - 2 * D - 8) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hEtaShort := mul_le_mul_of_nonneg_right hEtaInvS
      (Real.rpow_nonneg hNpos.le (-(2 * D + 9)))
    have hFactor0 : 0 ≤ (15 / 2 : Real) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : Real)^(13 * δ / 640) * Step2Moment.ratR E s N v^(-(2 : Real)) := by
      positivity
    calc
      _ = ((15 / 2 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : Real))) *
          ((N : Real)^(-(2 * D + 9))) := by ring
      _ ≤ ((15 / 2 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real)^(13 * δ / 640) * (N : Real) *
          Step2Moment.ratR E s N v^(-(2 : Real))) *
          ((N : Real)^(-(2 * D + 9))) := by
        calc
          _ = ((15 / 2 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real)^(13 * δ / 640) *
              Step2Moment.ratR E s N v^(-(2 : Real))) *
              ((etaT E (s N))⁻¹ * (N : Real)^(-(2 * D + 9))) := by ring
          _ ≤ ((15 / 2 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real)^(13 * δ / 640) *
              Step2Moment.ratR E s N v^(-(2 : Real))) *
              ((N : Real) * (N : Real)^(-(2 * D + 9))) :=
            mul_le_mul_of_nonneg_left hEtaShort hFactor0
          _ = _ := by ring
      _ = (15 / 2 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real)^(13 * δ / 640 - 2 * D - 8) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
        calc
          _ = ((15 / 2 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              Step2Moment.ratR E s N v^(-(2 : Real))) *
              ((N : Real)^(13 * δ / 640) *
                ((N : Real) * (N : Real)^(-(2 * D + 9)))) := by ring
          _ = ((15 / 2 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              Step2Moment.ratR E s N v^(-(2 : Real))) *
              ((N : Real)^(13 * δ / 640) * (N : Real)^(-(2 * D + 8))) := by
            rw [hShort]
          _ = _ := by rw [hPower]; ring
  have hSecond :
      ((15 / 8 : Real) * (N : Real)^(-1 : Real)) *
        (2 * (N : Real)^(-(2 * D + 9))) ≤
      (15 / 4 : Real) * (N : Real)^(-2 * D - 10) := by
    have hPower : (N : Real)^(-1 : Real) * (N : Real)^(-(2 * D + 9)) =
        (N : Real)^(-2 * D - 10) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [show ((15 / 8 : Real) * (N : Real)^(-1 : Real)) *
        (2 * (N : Real)^(-(2 * D + 9))) =
          (15 / 4 : Real) *
            ((N : Real)^(-1 : Real) * (N : Real)^(-(2 * D + 9))) by ring,
      hPower]
  have hFinal :
      coeff * (2 * (N : Real)^(-(2 * D + 9))) ≤
        (15 / 2 : Real) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real)^(13 * δ / 640 - 2 * D - 8) *
            Step2Moment.ratR E s N v^(-(2 : Real)) +
          (15 / 4 : Real) * (N : Real)^(-2 * D - 10) := by
    dsimp [coeff] at hBudgetInt ⊢
    rw [add_mul] at hBudgetInt
    calc
      _ = ((15 / 4 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real)^(13 * δ / 640) * (etaT E (s N))⁻¹ *
          Step2Moment.ratR E s N v^(-(2 : Real))) *
          (2 * (N : Real)^(-(2 * D + 9))) +
        ((15 / 8 : Real) * (N : Real)^(-1 : Real)) *
          (2 * (N : Real)^(-(2 * D + 9))) := by ring
      _ ≤ _ := add_le_add hFirst hSecond
  simpa [v, mesh] using hBudgetInt.trans hFinal

#print axioms eventually_integral_normGoodCrossBudget_le_first_cell_microscopic
#print axioms nondegenerate_positive_first_cell_witness

end
end RBM.APrimeGeneralMovingFirstCellNormGoodCrossMicroscopic
