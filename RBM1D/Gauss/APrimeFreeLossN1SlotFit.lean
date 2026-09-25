/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingAllOrdersMinkowskiActual
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeSlotArith
import RBM1D.Gauss.APrimeGeneralMovingCommonSources

/-!
# T1319: corrected-loss all-cell N1 drift-slot fit

For a fixed order and the literal actual T615 weight at loss `lambda`, an
explicit all-cell integral bound on the actual drift plus the full positive-
time cross budget fits the exact drift input of
`APrimeInit.coordinate_integral_of_small_slots`. The accepted Minkowski
consumer uses a closed-cell, zero-at-time-zero cross budget; the equality with
the positive-time expression is proved here, including time zero.

This is a conditional slot consumer. It does not prove the integral premise,
the other one-step slots, or a full coordinate/family N1 estimate.
-/

namespace RBM.APrimeFreeLossN1SlotFit

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
  RBM.APrimeGeneralMovingCrossBudgetTimeIntegrable
open scoped NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T1225's closed-cell cross budget equals the literal positive-time budget
even at `r = 0`: both sides are exactly zero there. -/
theorem closedCellCrossBudget_eq_positiveTimeCrossBudget
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k p : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) :
    APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget
        E D deltaWeight s t N k p a r =
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D deltaWeight s t N k p a r := by
  by_cases hr : r = 0
  · subst r
    simp [APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget,
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget]
  · simp [APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget, hr]

theorem eventually_actual_driftCross_le_driftSlot
    {E D c lambda C : ℝ} {s t : ℕ → ℝ}
    (p : ℕ) (_hp : 1 ≤ p)
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hlambda : 0 < lambda)
    (_hC : 0 < C)
    (hbudget : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k →
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        let R := Step2Moment.ratR E s N v
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D lambda s t N k p a u) ≤
          C * (N : ℝ) ^ (4 * (lambda / 1000)) *
            R ^ (-(2 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let x := (N : ℝ) ^ (lambda / 8)
        let v := cutNetPt s (mesh D) N k
        let R := Step2Moment.ratR E s N v
        IntervalIntegrable
          (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a)
          volume (s N) v ∧
        IntervalIntegrable
          (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D lambda s t N k p a)
          volume (s N) v ∧
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm E D s t lambda p N k a u +
            APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget E D lambda s t N k p a u) ≤
          APrimeOneStep.driftTerm (mE E).im x R
            (APrimeInit.slotXi' x)
            (APrimeSlotArith.slotA x R)
            (APrimeSlotArith.slotEps x R)
            (APrimeSlotArith.slotQ R)
            (APrimeSlotArith.slotBeta x R)
            (APrimeSlotArith.slotGamma x R)
            (APrimeSlotArith.slotJv x R) / R ^ 4 := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hexp : 0 < 5 * lambda / 32 - 4 * (lambda / 1000) := by
    nlinarith
  have habsorb := eventually_le_rpow (2 * (mE E).im * C) hexp
  have hCrossInt :=
    eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hlambda.le p _hp
  filter_upwards [hbudget, habsorb, hCrossInt, Filter.eventually_ge_atTop 1]
    with N hbudgetN habsorbN hCrossIntN hN1
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ (lambda / 8) :=
    Real.one_le_rpow hN0 (by linarith)
  intro k hk a
  let x : ℝ := (N : ℝ) ^ (lambda / 8)
  let v : ℝ := cutNetPt s (mesh D) N k
  let R : ℝ := Step2Moment.ratR E s N v
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hRpos : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hv.1 hv1
  have hDriftInt0 :=
    APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      (deltaWeight := lambda) (p := p) hE hs0 hst ht1 hN1 hk a
  have hDriftInt :
      IntervalIntegrable
        (APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
          E D s t lambda p N k a) volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a)
      volume (s N)
      (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k)
    exact hDriftInt0
  have hCrossInt0 := hCrossIntN k hk a
  have hmpos : 0 < (mE E).im := hm
  have hXi0 : 0 ≤ APrimeInit.slotXi' x := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (APrimeInit.slotXi'_ge_one hx1)
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
  have hnear := APrimeSlotArith.driftTerm_ge_near
    (m := (mE E).im) (x := x) (R := R)
    (Ξ := APrimeInit.slotXi' x)
    (A := APrimeSlotArith.slotA x R)
    (ε := APrimeSlotArith.slotEps x R)
    (q := APrimeSlotArith.slotQ R)
    (β := APrimeSlotArith.slotBeta x R)
    (γ := APrimeSlotArith.slotGamma x R)
    (Jv := APrimeSlotArith.slotJv x R)
    hm (by positivity) hRpos.le hXi0 hA0 hEps0 hBeta0 hGamma0 hJv0
  have hpowXi : x * APrimeInit.slotXi' x = x ^ (5 / 4 : ℝ) := by
    unfold APrimeInit.slotXi'
    calc
      x * x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + 1 / 4) :=
        (Real.rpow_add (by linarith [hx1]) 1 (1 / 4)).symm
      _ = x ^ (5 / 4 : ℝ) := by congr 1; ring
  have hnearEq :
      APrimeInit.slotXi' x *
          (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 =
        x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    rw [show APrimeSlotArith.slotQ R = R ^ 2 / 2 by rfl]
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hRpos, ne_of_gt hmpos]
    rw [show APrimeInit.slotXi' x * x = x * APrimeInit.slotXi' x by ring,
      hpowXi]
  have hnearDiv :
      APrimeInit.slotXi' x *
          (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 ≤
        APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
    div_le_div_of_nonneg_right hnear (by positivity : 0 ≤ R ^ 4)
  have hslotLower :
      (N : ℝ) ^ (5 * lambda / 32) / (2 * (mE E).im) ≤
        APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    have hxpow : x ^ (5 / 4 : ℝ) = (N : ℝ) ^ (5 * lambda / 32) := by
      dsimp [x]
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring
    rw [← hxpow, ← hnearEq]
    exact hnearDiv
  by_cases hk0 : k = 0
  · have hv0 : v = s N := by
      dsimp [v, mesh]
      rw [hk0]
      exact cutNetPt_zero s (APrimeGeneralMovingMesh.targetMesh D) N
    have hsmallpos : 0 ≤ (N : ℝ) ^ (5 * lambda / 32) /
        (2 * (mE E).im) := by
      positivity
    have htarget0 :
        0 ≤ APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
      le_trans (by positivity) hslotLower
    have hLHS0 :
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
              E D s t lambda p N k a u +
            APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
              E D lambda s t N k p a u) = 0 := by
      rw [hv0]
      simp
    refine ⟨hDriftInt, hCrossInt0, ?_⟩
    calc
      _ = 0 := hLHS0
      _ ≤ APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
            (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
            (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
            (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
        htarget0
  · have hkpos : 1 ≤ k := by omega
    have hbudgetCell := hbudgetN k hkpos hk a
    have hbudgetCell :
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D lambda s t N k p a u) ≤
          C * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(2 : ℝ)) := by
      simpa only [v, R] using hbudgetCell
    have hclosed :
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
            APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget
              E D lambda s t N k p a u) ≤
          C * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(2 : ℝ)) := by
      have heq :
          (fun u : ℝ =>
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
              APrimeGeneralMovingGeneratorAllOrdersClosedCell.closedCellCrossBudget
                E D lambda s t N k p a u) =
          (fun u : ℝ =>
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
              APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
                E D lambda s t N k p a u) := by
        funext u
        rw [closedCellCrossBudget_eq_positiveTimeCrossBudget]
      simpa only [heq] using hbudgetCell
    have hNpow_nonneg : 0 ≤ (N : ℝ) ^ (4 * (lambda / 1000)) :=
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) _
    have hslotPower :
        2 * (mE E).im * C * (N : ℝ) ^ (4 * (lambda / 1000)) ≤
          (N : ℝ) ^ (5 * lambda / 32) := by
      have hmul := mul_le_mul_of_nonneg_right habsorbN hNpow_nonneg
      have hpow :
          (N : ℝ) ^ (5 * lambda / 32 - 4 * (lambda / 1000)) *
              (N : ℝ) ^ (4 * (lambda / 1000)) =
            (N : ℝ) ^ (5 * lambda / 32) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      calc
        _ ≤ (N : ℝ) ^ (5 * lambda / 32 - 4 * (lambda / 1000)) *
            (N : ℝ) ^ (4 * (lambda / 1000)) := hmul
        _ = (N : ℝ) ^ (5 * lambda / 32) := hpow
    have hCoeff :
        C * (N : ℝ) ^ (4 * (lambda / 1000)) ≤
          (N : ℝ) ^ (5 * lambda / 32) / (2 * (mE E).im) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * (mE E).im)]
      nlinarith [hslotPower]
    have hRinv0 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
    have hRinv1 : R ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
    have hsmall :
        C * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(2 : ℝ)) ≤
          (N : ℝ) ^ (5 * lambda / 32) / (2 * (mE E).im) := by
      calc
        _ = (C * (N : ℝ) ^ (4 * (lambda / 1000))) * R ^ (-(2 : ℝ)) := by ring
        _ ≤ ((N : ℝ) ^ (5 * lambda / 32) / (2 * (mE E).im)) *
            R ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right hCoeff hRinv0
        _ ≤ (N : ℝ) ^ (5 * lambda / 32) / (2 * (mE E).im) := by
          exact mul_le_of_le_one_right (by positivity) hRinv1
    have hbudgetClosed :
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm
              E D s t lambda p N k a u +
            APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget
              E D lambda s t N k p a u) ≤
          C * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(2 : ℝ)) := by
      simpa only [APrimeGeneralMovingAllOrdersMinkowskiActual.driftNorm,
        APrimeGeneralMovingAllOrdersMinkowskiActual.crossBudget,
        APrimeGeneralMovingAllOrdersMinkowskiActual.d,
        APrimeGeneralMovingGeneratorAllOrdersClosedCell.d] using hclosed
    refine ⟨hDriftInt, hCrossInt0, ?_⟩
    calc
      _ ≤ C * (N : ℝ) ^ (4 * (lambda / 1000)) * R ^ (-(2 : ℝ)) := by
        simpa only [x, v, R] using hbudgetClosed
      _ ≤ (N : ℝ) ^ (5 * lambda / 32) / (2 * (mE E).im) := hsmall
      _ ≤ APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
            (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
            (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
            (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
        hslotLower

/-- A positive-length Gaussian first-cell witness for the structural window
and actual-weight hypotheses at the corrected loss schedule. The conditional
quantitative integral premise of the slot theorem remains an explicit input. -/
theorem nondegenerate_positive_cell_witness :
    ∃ c : ℝ, 0 < c ∧
    ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      ∃ lambda : ℝ,
        0 < lambda ∧
        lambda ≤ min (1 / 10000) (c / 10000) ∧
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (lambda / 32) (lambda / 32) (lambda / 16) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            0 < APrimeGeneralMovingSmoothDriftNormBudget.weight
              0 60 s t lambda 1 N 1 omega := by
  rcases APrimeGeneralMovingCommonSources.positive_length_common_support_witness with
    ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      _hStep, hresident⟩
  let lambda : ℝ := min (1 / 10000) (c / 10000) / 2
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambdaSmall : lambda ≤ min (1 / 10000) (c / 10000) := by
    dsimp [lambda]
    have hmin : 0 ≤ min (1 / 10000 : ℝ) (c / 10000) := by positivity
    linarith
  have hzetaSrc : 0 < lambda / 32 := by positivity
  have hzetaCtr : 0 < lambda / 32 := by positivity
  have htauG : 0 < lambda / 16 := by positivity
  have hresidentN := hresident (lambda / 32) (lambda / 32) (lambda / 16)
    lambda hzetaSrc hzetaCtr htauG hlambda
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, lambda,
    hlambda, hlambdaSmall, ?_⟩
  filter_upwards [hresidentN] with N hN
  obtain ⟨hwindow, omega, homega, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (mesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t (mesh 60)
        lambda 1 N 1 omega = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := lambda) (s := s) (t := t) (mesh := mesh 60)
    (by norm_num) hlambda.le N 1 1 omega (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos :
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (mesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t (mesh 60)
        lambda 1 N 1 omega := by
    rw [hwideOne]
    norm_num
  have hweight :
      0 < APrimeGeneralMovingSmoothDriftNormBudget.weight
        0 60 s t lambda 1 N 1 omega := by
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.weight,
      mesh] using hwidePos.trans_le hcompare
  exact ⟨hwindow, omega, homega, hactive, hweight⟩

#print axioms closedCellCrossBudget_eq_positiveTimeCrossBudget
#print axioms eventually_actual_driftCross_le_driftSlot
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeFreeLossN1SlotFit
