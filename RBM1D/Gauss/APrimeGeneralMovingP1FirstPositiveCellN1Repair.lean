/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingFirstCellDriftMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeSlotDriftCore
import RBM1D.Gauss.APrimeInit

/-!
# T1261: the first positive-cell p=1 N1 consumer

On the first positive target-mesh cell, the exact T615 smooth drift integral
and the literal T1089 positive-time cross-budget integral fit the T230A′
one-step drift slot with `APrimeInit.slotXi'`.  This is a local consumer
estimate and does not assert an all-cell or paper-level conclusion.
-/

namespace RBM.APrimeGeneralMovingP1FirstPositiveCellN1Repair

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's same-event, positive-actual-weight witness at `p=1` and the first
positive cell.  It does not assert a strict-transition resident. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingFirstCellDriftMicroscopic.nondegenerate_positive_cell_witness

private theorem eventually_integral_positive_cross_le_first_cell
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
        let v := cutNetPt s (mesh D) N 1
        let R := Step2Moment.ratR E s N v
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a u) ≤
          (15 / 2 : ℝ) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) +
            (15 / 2 : ℝ) * (N : ℝ) ^ (-2 * D - 10) := by
  have hProfile :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      hE (by linarith : 0 ≤ D) hs0 hst ht1 hc hreg hδ hδsmall
  have hGoodPoint :=
    APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic.eventually_normGoodCrossBudget_le_crossProfile_microscopic
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hFullIntegral :=
    APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      hE hD hs0 hst ht1 hc hreg
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      1 (by norm_num)
  have hGoodIntegrable :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      1 (by norm_num)
  have hFullIntegrable :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      1 (by norm_num)
  have hEta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  filter_upwards [hProfile, hGoodPoint, hFullIntegral, hGoodIntegrable,
      hFullIntegrable, hEta, hMesh, eventually_ge_atTop 2]
    with N hProfileN hGoodPointN hFullIntegralN hGoodIntegrableN
      hFullIntegrableN hEtaN hMeshN hN2
  intro hk a
  let v := cutNetPt s (mesh D) N 1
  let R := Step2Moment.ratR E s N v
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hsv : s N ≤ v := hv.1
  have hv0 : 0 ≤ v := (hs0 N).trans hsv
  have hRpos : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos hE (hsv.trans_lt hv1) hv1
  have hRge : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hsv hv1
  have hRpow : R ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRge (by norm_num)
  have hRpow0 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hetaT : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hetaInvT : (etaT E (t N))⁻¹ ≤ (N : ℝ) := by
    have hinv := inv_anti₀
      (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hEtaN
    have hrepr : ((N : ℝ) ^ (-(1 : ℝ)))⁻¹ = (N : ℝ) := by
      rw [Real.rpow_neg_one]
      simp
    simpa only [hrepr] using hinv
  have hetaInvS : (etaT E (s N))⁻¹ ≤ (N : ℝ) := by
    have hmono := inv_anti₀ hetaT (Gauss.etaT_le_of_le hE (hst N))
    exact hmono.trans hetaInvT
  have hgap : v - s N = (N : ℝ) ^ (-(4 * D + 18)) := by
    have hcut : cutNetPt s (mesh D) N 1 - s N =
        1 / APrimeGeneralMovingMesh.targetMesh D N := by
      simp [v, mesh, CutHypTheta.cutNetPt]
    rw [show v - s N = cutNetPt s (mesh D) N 1 - s N by rfl, hcut,
      hMeshN, one_div, ← Real.rpow_neg hNpos.le]
  have hsqrtGap : Real.sqrt v - Real.sqrt (s N) ≤
      (N : ℝ) ^ (-(2 * D + 9)) := by
    have hroot := Gauss.abs_sqrt_sub_sqrt_le v (s N)
    have hdiff0 : 0 ≤ v - s N := sub_nonneg.mpr hsv
    have habs : |v - s N| = v - s N := abs_of_nonneg hdiff0
    have hrootEq : Real.sqrt |v - s N| = (N : ℝ) ^ (-(2 * D + 9)) := by
      rw [habs, hgap, Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    have hdiff := hroot.trans_eq hrootEq
    exact (le_abs_self _).trans hdiff
  have hdeltaSqrt0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hdeltaSqrt := hsqrtGap
  have hgoodInt : IntervalIntegrable
      (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N 1 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hGoodIntegrableN 1 hk a
  have hfullInt : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N 1 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hFullIntegrableN 1 hk a
  let Cgood : ℝ :=
    (15 / 4 : ℝ) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) +
      (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ))
  have hCgood0 : 0 ≤ Cgood := by
    have hconst :=
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
    have hetaS : 0 < etaT E (s N) :=
      Step2.etaT_pos' hE (hsv.trans_lt (hv.2.trans_lt (ht1 N)))
    dsimp [Cgood]
    positivity
  let major : ℝ → ℝ := fun u => Cgood / Real.sqrt u
  have hmajorInt : IntervalIntegrable major volume (s N) v := by
    simpa [major] using
      APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
        Cgood (s N) v (hs0 N) hsv
  have hmajorEval : (∫ u in (s N)..v, major u) =
      2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) := by
    simpa [major] using
      APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
        Cgood (s N) v (hs0 N) hsv
  have hgoodPoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a u ≤ major u := by
    intro u hu
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    by_cases huPos : 0 < u
    · have hgp := hGoodPointN 1 (by simpa [mesh] using hk) a u hu huPos
      have hprof := hProfileN 1 (by simpa [mesh] using hk) a u hu huPos
      have hprof' :
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u ≤
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) /
              Real.sqrt u := by
        simpa [mesh, v, R] using hprof
      have hcoeff : 0 ≤ (15 / 4 : ℝ) := by norm_num
      have hprofMul := mul_le_mul_of_nonneg_left hprof' hcoeff
      have hcross := hgp
      have hsqrtInv : Real.sqrt u⁻¹ = (Real.sqrt u)⁻¹ := Real.sqrt_inv u
      change _ ≤ Cgood / Real.sqrt u
      rw [div_eq_mul_inv]
      dsimp [Cgood]
      rw [hsqrtInv] at hcross
      have hprofEnvelope :
          (15 / 4 : ℝ) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N 1 a u ≤
            ((15 / 4 : ℝ) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ))) *
              (Real.sqrt u)⁻¹ := by
        calc
          _ ≤ (15 / 4 : ℝ) *
              (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) /
                  Real.sqrt u) := hprofMul
          _ = _ := by rw [div_eq_mul_inv]; ring
      have hbadEq :
          (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt u)⁻¹ =
            (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt u)⁻¹ := rfl
      have hsumEnvelope := add_le_add hprofEnvelope (le_of_eq hbadEq)
      have hcrossEnvelope := hcross.trans hsumEnvelope
      rw [div_eq_mul_inv]
      convert hcrossEnvelope using 1 <;> ring
    · have huEq : u = 0 := le_antisymm (le_of_not_gt huPos) hu0
      have hzero :
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a u = 0 := by
        simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget,
          huEq]
      rw [hzero]
      simp [major, huEq]
  have hgoodIntegral := intervalIntegral.integral_mono_on hsv hgoodInt hmajorInt hgoodPoint
  have hfullN := hFullIntegralN 1 hk a
  have hcrossRaw :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a u) ≤
        (15 / 2 : ℝ) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
              (Real.sqrt v - Real.sqrt (s N)) +
          (15 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
              (Real.sqrt v - Real.sqrt (s N)) := by
    have hmain := hfullN.trans (add_le_add hgoodIntegral (le_of_eq rfl))
    rw [hmajorEval] at hmain
    dsimp [Cgood] at hmain
    convert hmain using 1 <;> ring
  have hprofileFactor :
      (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
          R ^ (-(2 : ℝ)) * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) := by
    have hNalpha0 : 0 ≤ (N : ℝ) ^ (13 * δ / 640) := by positivity
    have hpow : (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) *
        (N : ℝ) ^ (-(2 * D + 9)) =
        (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) := by
      have hmul : (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) =
          (N : ℝ) ^ (13 * δ / 640 + 1) := by
        calc
          _ = (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (N : ℝ) ^ (13 * δ / 640 + 1) :=
            (Real.rpow_add hNpos _ _).symm
      calc
        _ = ((N : ℝ) ^ (13 * δ / 640) * (N : ℝ)) *
            (N : ℝ) ^ (-(2 * D + 9)) := by ring
        _ = (N : ℝ) ^ (13 * δ / 640 + 1) *
            (N : ℝ) ^ (-(2 * D + 9)) := by rw [hmul]
        _ = (N : ℝ) ^ (13 * δ / 640 + 1 + -(2 * D + 9)) := by
          rw [← Real.rpow_add hNpos]
        _ = (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) := by
          rw [show 13 * δ / 640 + 1 + -(2 * D + 9) =
            13 * δ / 640 - 2 * D - 8 by ring]
    have hcoef : (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
        R ^ (-(2 : ℝ)) ≤
        (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) * R ^ (-(2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hRpow0
      exact mul_le_mul_of_nonneg_left hetaInvS hNalpha0
    calc
      _ ≤ (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) * R ^ (-(2 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N)) :=
        mul_le_mul_of_nonneg_right hcoef hdeltaSqrt0
      _ ≤ (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) * R ^ (-(2 : ℝ)) *
            (N : ℝ) ^ (-(2 * D + 9)) := by
          exact mul_le_mul_of_nonneg_left hsqrtGap (by positivity)
      _ = (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) := by
          calc
            _ = ((N : ℝ) ^ (13 * δ / 640) * (N : ℝ) *
                (N : ℝ) ^ (-(2 * D + 9))) * R ^ (-(2 : ℝ)) := by ring
            _ = (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) *
                R ^ (-(2 : ℝ)) := by rw [hpow]
  have hbadFactor :
      (N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ) ^ (-2 * D - 10) := by
    calc
      _ ≤ (N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(2 * D + 9)) :=
        mul_le_mul_of_nonneg_left hdeltaSqrt (by positivity)
      _ = (N : ℝ) ^ (-2 * D - 10) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hK0 : 0 ≤
      (15 / 2 : ℝ) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst := by
    exact (mul_nonneg (by norm_num) (le_of_lt
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos))
  have hcross1 := mul_le_mul_of_nonneg_left hprofileFactor hK0
  have hcross2 := mul_le_mul_of_nonneg_left hbadFactor (by norm_num : (0 : ℝ) ≤ 15 / 2)
  calc
    _ ≤ (15 / 2 : ℝ) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) := hcrossRaw
    _ ≤ (15 / 2 : ℝ) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-2 * D - 10) := by
          have hfirst := mul_le_mul_of_nonneg_left hprofileFactor hK0
          have hsecond := mul_le_mul_of_nonneg_left hbadFactor
            (by norm_num : (0 : ℝ) ≤ 15 / 2)
          nlinarith [hfirst, hsecond]

/-- The exact p=1 first-positive-cell drift consumer inequality.  The
parameters are fixed before the eventual cutoff; after it, the claim is
uniform over every output label. -/
theorem eventually_first_positive_cell_N1_consumer
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
        let x := (N : ℝ) ^ (δ / 8)
        let v := cutNetPt s (mesh D) N 1
        let R := Step2Moment.ratR E s N v
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u +
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N 1 1 a u) ≤
          APrimeOneStep.driftTerm (mE E).im x R
            (APrimeInit.slotXi' x)
            (APrimeSlotArith.slotA x R)
            (APrimeSlotArith.slotEps x R)
            (APrimeSlotArith.slotQ R)
            (APrimeSlotArith.slotBeta x R)
            (APrimeSlotArith.slotGamma x R)
            (APrimeSlotArith.slotJv x R) / R ^ 4 := by
  have hDrift :=
    APrimeGeneralMovingFirstCellDriftMicroscopic.eventually_integral_g_le_microscopic
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hCross := eventually_integral_positive_cross_le_first_cell
    hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hCrossIntegrable :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      1 (by norm_num)
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hEta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  let m : ℝ := (mE E).im
  let K : ℝ := 17 + 15 *
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst
  have hm : 0 < m := by
    dsimp [m]
    exact mE_im_pos hE
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos (by norm_num) (mul_pos (by norm_num)
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos)
  have hAbsorb := eventually_le_rpow (2 * m * K) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hDrift, hCross, hCrossIntegrable, hMesh, hEta,
      eventually_ge_atTop 2, hAbsorb]
    with N hDriftN hCrossN hCrossIntegrableN hMeshN hEtaN hN2 hAbsorbN
  intro hk a
  let x := (N : ℝ) ^ (δ / 8)
  let v := cutNetPt s (mesh D) N 1
  let R := Step2Moment.ratR E s N v
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hNinv : (N : ℝ) ^ (-(1 : ℝ)) = 1 / (N : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
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
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hN (by positivity)
  have hmE : 0 < (mE E).im := mE_im_pos hE
  have hetaT : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hetaInvT : (etaT E (t N))⁻¹ ≤ (N : ℝ) := by
    have hinv := inv_anti₀
      (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hEtaN
    have hrepr : ((N : ℝ) ^ (-(1 : ℝ)))⁻¹ = (N : ℝ) := by
      rw [Real.rpow_neg_one]
      simp
    simpa only [hrepr] using hinv
  have hetaInvS : (etaT E (s N))⁻¹ ≤ (N : ℝ) := by
    exact (inv_anti₀ hetaT (Gauss.etaT_le_of_le hE (hst N))).trans hetaInvT
  have hvlength : v - s N = (N : ℝ) ^ (-(4 * D + 18)) := by
    have hcut : cutNetPt s (mesh D) N 1 - s N =
        1 / APrimeGeneralMovingMesh.targetMesh D N := by
      simp [v, mesh, CutHypTheta.cutNetPt]
    rw [show v - s N = cutNetPt s (mesh D) N 1 - s N by rfl, hcut,
      hMeshN, one_div, ← Real.rpow_neg hNpos.le]
  have hgapSqrt : Real.sqrt v - Real.sqrt (s N) ≤
      (N : ℝ) ^ (-(2 * D + 9)) := by
    have hroot := Gauss.abs_sqrt_sub_sqrt_le v (s N)
    have habs : |v - s N| = v - s N := abs_of_nonneg (sub_nonneg.mpr hsv)
    have hrootpow : Real.sqrt (v - s N) = (N : ℝ) ^ (-(2 * D + 9)) := by
      rw [hvlength, Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    calc
      Real.sqrt v - Real.sqrt (s N) ≤ |Real.sqrt v - Real.sqrt (s N)| := le_abs_self _
      _ ≤ Real.sqrt |v - s N| := hroot
      _ = (N : ℝ) ^ (-(2 * D + 9)) := by rw [habs, hrootpow]
  have hdelta0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hgi := hDriftN hk a
  have hgiInt : IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a)
      volume (s N) v := by
    simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hgi.1
  have hgiBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u) ≤
        (N : ℝ) ^ (-3 * D - 10) := by
    simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hgi.2
  have hcrossBound := hCrossN hk a
  have htotalBound :
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a u) ≤
        2 * (N : ℝ) ^ (-3 * D - 10) +
          15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) +
          15 * (N : ℝ) ^ (-2 * D - 10) := by
    have hcrossmul := mul_le_mul_of_nonneg_left hcrossBound (by norm_num : (0 : ℝ) ≤ 2)
    have hcrossInt : IntervalIntegrable
        (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a)
        volume (s N) v := by
      simpa [v, mesh] using hCrossIntegrableN 1 hk a
    have hadd := intervalIntegral.integral_add hgiInt hcrossInt
    have hDriftMul := mul_le_mul_of_nonneg_left hgiBound (by norm_num : (0 : ℝ) ≤ 2)
    rw [hadd]
    dsimp [v, mesh] at hcrossmul ⊢
    nlinarith [hDriftMul, hcrossmul]
  have hRneg : R ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRge (by norm_num)
  have hRneg0 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have he1 : -3 * D - 10 ≤ -1 := by linarith [hD]
  have he2 : 13 * δ / 640 - 2 * D - 8 ≤ -1 := by nlinarith [hD, hδ1]
  have he3 : -2 * D - 10 ≤ -1 := by linarith [hD]
  have hp1 : (N : ℝ) ^ (-3 * D - 10) ≤ (N : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN he1
  have hp2 : (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) ≤
      (N : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN he2
  have hp3 : (N : ℝ) ^ (-2 * D - 10) ≤ (N : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN he3
  have hKsmall :
      2 * (N : ℝ) ^ (-3 * D - 10) +
        15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) +
        15 * (N : ℝ) ^ (-2 * D - 10) ≤ K / (N : ℝ) := by
    have hC0 : 0 ≤ APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
      (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos).le
    have hNexp : 0 ≤ (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) := by positivity
    have hRreduce :
        (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) ≤
          (N : ℝ) ^ (-(1 : ℝ)) := by
      calc
        _ ≤ (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) := by
          simpa using mul_le_mul_of_nonneg_left hRneg hNexp
        _ ≤ (N : ℝ) ^ (-(1 : ℝ)) := hp2
    have hterm1 := mul_le_mul_of_nonneg_left hp1 (by norm_num : (0 : ℝ) ≤ 2)
    have hterm2raw := mul_le_mul_of_nonneg_left hRreduce
      (by positivity : (0 : ℝ) ≤
        15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst)
    have hterm2 :
        15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640 - 2 * D - 8) * R ^ (-(2 : ℝ)) ≤
          15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (-(1 : ℝ)) := by
      simpa [mul_assoc] using hterm2raw
    have hterm3 := mul_le_mul_of_nonneg_left hp3 (by norm_num : (0 : ℝ) ≤ 15)
    calc
      _ ≤ 2 * (N : ℝ) ^ (-(1 : ℝ)) +
          15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (-(1 : ℝ)) +
          15 * (N : ℝ) ^ (-(1 : ℝ)) := by
            exact add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = (17 + 15 *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) *
              (N : ℝ) ^ (-(1 : ℝ)) := by ring
      _ = K / (N : ℝ) := by
            change _ = (17 + 15 *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) /
                (N : ℝ)
            rw [hNinv]
            ring
  have hAbsorb' : 2 * (mE E).im * K ≤ (N : ℝ) := by
    have hle := hAbsorbN
    simpa [m, K, Real.rpow_one, mul_assoc] using hle
  have hKdiv : K / (N : ℝ) ≤ 1 / (2 * (mE E).im) := by
    rw [div_le_div_iff₀ hNpos (by positivity : 0 < 2 * (mE E).im)]
    calc
      K * (2 * (mE E).im) = 2 * (mE E).im * K := by ring
      _ ≤ (N : ℝ) := hAbsorb'
      _ = 1 * (N : ℝ) := by ring
  have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
  have hsqrtcWt : 0 < Real.sqrt StepSideAPrime.cWt := Real.sqrt_pos.2 hcWt
  have hsmall :
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N 1 1 a u) ≤ 1 / (2 * (mE E).im) :=
    htotalBound.trans (hKsmall.trans hKdiv)
  have hA0 : 0 < APrimeSlotArith.slotA x R := by
    unfold APrimeSlotArith.slotA
    positivity
  have hEps0 : 0 ≤ APrimeSlotArith.slotEps x R := by
    unfold APrimeSlotArith.slotEps
    positivity
  have hBeta0 : 0 ≤ APrimeSlotArith.slotBeta x R := by
    unfold APrimeSlotArith.slotBeta
    positivity
  have hGamma0 : 0 ≤ APrimeSlotArith.slotGamma x R := by
    unfold APrimeSlotArith.slotGamma
    positivity
  have hJv0 : 0 ≤ APrimeSlotArith.slotJv x R := by
    unfold APrimeSlotArith.slotJv
    positivity
  have hXi0 : 0 ≤ APrimeInit.slotXi' x := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (APrimeInit.slotXi'_ge_one hx)
  have hNear := RBM.APrimeSlotArith.driftTerm_ge_near
    (m := (mE E).im) (x := x) (R := R)
    (Ξ := APrimeInit.slotXi' x)
    (A := APrimeSlotArith.slotA x R)
    (ε := APrimeSlotArith.slotEps x R)
    (q := APrimeSlotArith.slotQ R)
    (β := APrimeSlotArith.slotBeta x R)
    (γ := APrimeSlotArith.slotGamma x R)
    (Jv := APrimeSlotArith.slotJv x R)
    hmE (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx) hRpos.le
      hXi0 hA0 hEps0 hBeta0 hGamma0 hJv0
  have hxiPow : x * APrimeInit.slotXi' x = x ^ (5 / 4 : ℝ) := by
    unfold APrimeInit.slotXi'
    calc
      x * x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + 1 / 4) := (Real.rpow_add (by linarith [hx]) 1 (1 / 4)).symm
      _ = x ^ (5 / 4 : ℝ) := by congr 1 <;> ring
  have hnearEq :
      APrimeInit.slotXi' x *
          (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 =
        x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    rw [show APrimeSlotArith.slotQ R = R ^ 2 / 2 by rfl]
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hRpos, ne_of_gt hmE]
    rw [show APrimeInit.slotXi' x * x = x * APrimeInit.slotXi' x by ring, hxiPow]
  have hnearDiv :
      APrimeInit.slotXi' x *
          (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) / R ^ 4 ≤
        APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
          (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
          (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
          (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    exact (div_le_div_of_nonneg_right hNear (by positivity : 0 ≤ R ^ 4))
  have hxpow : 1 ≤ x ^ (5 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hconstNear : 1 / (2 * (mE E).im) ≤ x ^ (5 / 4 : ℝ) /
      (2 * (mE E).im) := by
    have h := mul_le_mul_of_nonneg_right hxpow (by positivity : 0 ≤ (2 * (mE E).im)⁻¹)
    simpa [div_eq_mul_inv] using h
  have hconsumer : 1 / (2 * (mE E).im) ≤
      APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
        (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
        (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
        (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    exact hconstNear.trans (hnearEq ▸ hnearDiv)
  simpa [x, v, R, m, mesh] using hsmall.trans hconsumer

#print axioms eventually_integral_positive_cross_le_first_cell
#print axioms eventually_first_positive_cell_N1_consumer
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingP1FirstPositiveCellN1Repair
