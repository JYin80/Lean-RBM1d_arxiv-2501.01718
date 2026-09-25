/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeSlotDriftCore
import RBM1D.Gauss.APrimeInit

/-!
# T1275: exact p=1 N1 consumer on the `N^(3D)` early prefix

The statement uses the actual T615 smooth-weighted drift norm and the full
positive-time cross budget. A global T611 drift envelope pays the drift over
the very short prefix interval; the T1207/T1247/T1245 chain pays the full
cross integral. Both fit the actual APrimeInit small-slot drift term.
-/

namespace RBM.APrimeGeneralMovingEarlyPrefix3DP1N1Consumer

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D

/-- A p=1 weighted norm is below a deterministic envelope when the weight is
between zero and one and the envelope holds at every sample. -/
private theorem momNormW_one_le_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W Y : Ω → Real} {C : Real} (hW0 : ∀ ω, 0 ≤ W ω)
    (hW1 : ∀ ω, W ω ≤ 1) (hC : 0 ≤ C)
    (hY : ∀ ω, |Y ω| ≤ C) :
    MomentDuhamel.momNormW P W 1 Y ≤ C := by
  have hpoint : ∀ ω, W ω * |Y ω| ^ 2 ≤ C ^ 2 := by
    intro ω
    calc
      W ω * |Y ω| ^ 2 ≤ 1 * |Y ω| ^ 2 :=
        mul_le_mul_of_nonneg_right (hW1 ω) (by positivity)
      _ = |Y ω| ^ 2 := by ring
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hY ω) 2
  have hInt : (∫ ω, W ω * |Y ω| ^ 2 ∂P) ≤ C ^ 2 := by
    have h := MeasureTheory.integral_mono_of_nonneg (μ := P)
      (Eventually.of_forall fun ω => mul_nonneg (hW0 ω) (by positivity))
      (integrable_const (μ := P) (C ^ 2))
      (Eventually.of_forall hpoint)
    simpa using h
  have hNorm : MomentDuhamel.momNormW P W 1 Y =
      Real.sqrt (∫ ω, W ω * |Y ω| ^ 2 ∂P) := by
    simp [MomentDuhamel.momNormW, Real.sqrt_eq_rpow]
  rw [hNorm]
  calc
    Real.sqrt (∫ ω, W ω * |Y ω| ^ 2 ∂P) ≤ Real.sqrt (C ^ 2) :=
      Real.sqrt_le_sqrt hInt
    _ = C := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hC]

/-- T995's explicit same-event witness, with the active first cell also in
the `N^(3D)` prefix. -/
theorem nondegenerate_early_prefix_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ δ : Real, 0 < δ → δ ≤ min 1 (c / 100) →
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            (1 : Real) ≤ (N : Real) ^ (3 * 60) ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (mesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u ω)
              s t (mesh 60)
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t
              (mesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hw⟩ :=
    APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro δ hδ hsmall
  have hW := hw δ hδ hsmall
  filter_upwards [hW, eventually_ge_atTop 1] with N hN hN1
  rcases hN with ⟨hwindow, ω, hω, hactive, hwide, hactual⟩
  have hprefix : (1 : Real) ≤ (N : Real) ^ (3 * 60) := by
    have hNR : (1 : Real) ≤ (N : Real) := by exact_mod_cast hN1
    exact one_le_pow₀ hNR
  exact ⟨hwindow, ω, hω, hactive, hprefix, hwide, hactual⟩

/-- The literal full cross budget on every active cell in the `N^(3D)`
prefix. The displayed estimate is for the integral before the outer factor
two used by the one-step drift slot. -/
private theorem eventually_integral_positive_cross_le_prefix
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      1 ≤ k → k ≤ cutNetTop s t (mesh D) N →
      (k : Real) ≤ (N : Real) ^ (3 * D) →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        let R := Step2Moment.ratR E s N v
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u) ≤
          (15 / 2 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real) ^ (13 * δ / 640 - D / 2 - 8) * R ^ (-(2 : Real)) +
            (15 / 2 : Real) * (N : Real) ^ (-D / 2 - 10) := by
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
  intro k hkpos hk hkprefix a
  let v := cutNetPt s (mesh D) N k
  let R := Step2Moment.ratR E s N v
  have hN : (1 : Real) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : Real) < N := by linarith
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
  have hRpow : R ^ (-(2 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRge (by norm_num)
  have hRpow0 : 0 ≤ R ^ (-(2 : Real)) := Real.rpow_nonneg hRpos.le _
  have hetaT : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hetaInvT : (etaT E (t N))⁻¹ ≤ (N : Real) := by
    have hinv := inv_anti₀
      (Real.rpow_pos_of_pos hNpos (-(1 : Real))) hEtaN
    have hrepr : ((N : Real) ^ (-(1 : Real)))⁻¹ = (N : Real) := by
      rw [Real.rpow_neg_one]
      simp
    simpa only [hrepr] using hinv
  have hetaInvS : (etaT E (s N))⁻¹ ≤ (N : Real) := by
    have hmono := inv_anti₀ hetaT (Gauss.etaT_le_of_le hE (hst N))
    exact hmono.trans hetaInvT
  have hmeshpos : 0 < mesh D N := APrimeGeneralMovingMesh.targetMesh_pos D N
  have hmeshEq : mesh D N = (N : Real) ^ (4 * D + 18) := by
    simpa [mesh] using hMeshN
  have hgap : v - s N = (k : Real) / mesh D N := by
    simp [v, CutHypTheta.cutNetPt]
  have hwidth : v - s N ≤ (N : Real) ^ (-D - 18) := by
    rw [hgap]
    have hdiv := div_le_div_of_nonneg_right hkprefix hmeshpos.le
    rw [hmeshEq] at hdiv
    rw [hmeshEq]
    have hpow : (N : Real) ^ (3 * D) / (N : Real) ^ (4 * D + 18) =
        (N : Real) ^ (-D - 18) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hNpos.le]
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    exact hdiv.trans_eq hpow
  have hdeltaSqrt0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hsqrtGap : Real.sqrt v - Real.sqrt (s N) ≤
      (N : Real) ^ (-D / 2 - 9) := by
    have hroot := Gauss.abs_sqrt_sub_sqrt_le v (s N)
    have habs : |v - s N| = v - s N := abs_of_nonneg (sub_nonneg.mpr hsv)
    have hrootLe : Real.sqrt |v - s N| ≤ Real.sqrt ((N : Real) ^ (-D - 18)) := by
      apply Real.sqrt_le_sqrt
      rw [habs]
      exact hwidth
    have hrootEq : Real.sqrt ((N : Real) ^ (-D - 18)) =
        (N : Real) ^ (-D / 2 - 9) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    calc
      Real.sqrt v - Real.sqrt (s N) ≤ |Real.sqrt v - Real.sqrt (s N)| := le_abs_self _
      _ ≤ Real.sqrt |v - s N| := hroot
      _ ≤ Real.sqrt ((N : Real) ^ (-D - 18)) := hrootLe
      _ = (N : Real) ^ (-D / 2 - 9) := hrootEq
  have hgoodInt : IntervalIntegrable
      (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hGoodIntegrableN k hk a
  have hfullInt : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N k 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hFullIntegrableN k hk a
  let Cgood : Real :=
    (15 / 4 : Real) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : Real)) +
      (15 / 8 : Real) * (N : Real) ^ (-(1 : Real))
  have hCgood0 : 0 ≤ Cgood := by
    have hconst :=
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
    have hetaS : 0 < etaT E (s N) :=
      Step2.etaT_pos' hE (hsv.trans_lt (hv.2.trans_lt (ht1 N)))
    dsimp [Cgood]
    positivity
  let major : Real → Real := fun u => Cgood / Real.sqrt u
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
          s t N k 1 a u ≤ major u := by
    intro u hu
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    by_cases huPos : 0 < u
    · have hgp := hGoodPointN k hk a u hu huPos
      have hprof := hProfileN k hk a u hu huPos
      have hprof' :
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
              R ^ (-(2 : Real)) / Real.sqrt u := by
        simpa [mesh, v, R] using hprof
      change _ ≤ Cgood / Real.sqrt u
      rw [div_eq_mul_inv]
      dsimp [Cgood, major]
      have hcross := hgp
      rw [Real.sqrt_inv] at hcross
      have hprofEnvelope :
          (15 / 4 : Real) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
            ((15 / 4 : Real) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                  R ^ (-(2 : Real))) * (Real.sqrt u)⁻¹ := by
        calc
          _ ≤ (15 / 4 : Real) *
              (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                  R ^ (-(2 : Real)) / Real.sqrt u) := by
                    exact mul_le_mul_of_nonneg_left hprof'
                      (by norm_num : (0 : Real) ≤ 15 / 4)
          _ = _ := by rw [div_eq_mul_inv]; ring
      have hsumEnvelope :
          (15 / 4 : Real) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u +
            (15 / 8 : Real) * (N : Real) ^ (-(1 : Real)) *
              (Real.sqrt u)⁻¹ ≤
          ((15 / 4 : Real) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                R ^ (-(2 : Real))) * (Real.sqrt u)⁻¹ +
            (15 / 8 : Real) * (N : Real) ^ (-(1 : Real)) *
              (Real.sqrt u)⁻¹ :=
        add_le_add hprofEnvelope (le_rfl)
      have hcrossEnvelope := hcross.trans hsumEnvelope
      rw [div_eq_mul_inv]
      convert hcrossEnvelope using 1 <;> ring
    · have huEq : u = 0 := le_antisymm (le_of_not_gt huPos) hu0
      have hzero :
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u = 0 := by
        simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget, huEq]
      rw [hzero]
      simp [major, huEq]
  have hgoodIntegral := intervalIntegral.integral_mono_on hsv hgoodInt hmajorInt hgoodPoint
  have hfullN := hFullIntegralN k hk a
  have hcrossRaw :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k 1 a u) ≤
        (15 / 2 : Real) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
              R ^ (-(2 : Real)) * (Real.sqrt v - Real.sqrt (s N)) +
          (15 / 2 : Real) * (N : Real) ^ (-(1 : Real)) *
              (Real.sqrt v - Real.sqrt (s N)) := by
    have hmain := hfullN.trans (add_le_add hgoodIntegral (le_of_eq rfl))
    rw [hmajorEval] at hmain
    dsimp [Cgood] at hmain
    convert hmain using 1 <;> ring
  have hprofileFactor :
      (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
          R ^ (-(2 : Real)) * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : Real) ^ (13 * δ / 640 - D / 2 - 8) * R ^ (-(2 : Real)) := by
    have hNalpha0 : 0 ≤ (N : Real) ^ (13 * δ / 640) := by positivity
    have hpow : (N : Real) ^ (13 * δ / 640) * (N : Real) *
        (N : Real) ^ (-D / 2 - 9) =
          (N : Real) ^ (13 * δ / 640 - D / 2 - 8) := by
      have hmul : (N : Real) ^ (13 * δ / 640) * (N : Real) =
          (N : Real) ^ (13 * δ / 640 + 1) := by
        calc
          (N : Real) ^ (13 * δ / 640) * (N : Real) =
              (N : Real) ^ (13 * δ / 640) * (N : Real) ^ (1 : Real) :=
            congrArg (fun z : Real => (N : Real) ^ (13 * δ / 640) * z)
              (Real.rpow_one (N : Real)).symm
          _ = (N : Real) ^ (13 * δ / 640 + 1) := by
            rw [← Real.rpow_add hNpos]
      calc
        _ = ((N : Real) ^ (13 * δ / 640) * (N : Real)) *
              (N : Real) ^ (-D / 2 - 9) := by ring
        _ = (N : Real) ^ (13 * δ / 640 + 1) *
              (N : Real) ^ (-D / 2 - 9) := by rw [hmul]
        _ = (N : Real) ^ (13 * δ / 640 + 1 + (-D / 2 - 9)) := by
                rw [← Real.rpow_add hNpos]
        _ = (N : Real) ^ (13 * δ / 640 - D / 2 - 8) := by
                congr 1 <;> ring
    have hcoef :
        (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
            R ^ (-(2 : Real)) ≤
          (N : Real) ^ (13 * δ / 640) * (N : Real) * R ^ (-(2 : Real)) := by
      apply mul_le_mul_of_nonneg_right _ hRpow0
      exact mul_le_mul_of_nonneg_left hetaInvS hNalpha0
    calc
      _ ≤ (N : Real) ^ (13 * δ / 640) * (N : Real) *
            R ^ (-(2 : Real)) * (Real.sqrt v - Real.sqrt (s N)) :=
          mul_le_mul_of_nonneg_right hcoef hdeltaSqrt0
      _ ≤ (N : Real) ^ (13 * δ / 640) * (N : Real) *
            R ^ (-(2 : Real)) * (N : Real) ^ (-D / 2 - 9) :=
          mul_le_mul_of_nonneg_left hsqrtGap (by positivity)
      _ = (N : Real) ^ (13 * δ / 640 - D / 2 - 8) *
            R ^ (-(2 : Real)) := by
        calc
          _ = ((N : Real) ^ (13 * δ / 640) * (N : Real) *
                (N : Real) ^ (-D / 2 - 9)) * R ^ (-(2 : Real)) := by ring
          _ = (N : Real) ^ (13 * δ / 640 - D / 2 - 8) *
                R ^ (-(2 : Real)) := by rw [hpow]
  have hbadFactor :
      (N : Real) ^ (-(1 : Real)) * (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : Real) ^ (-D / 2 - 10) := by
    calc
      _ ≤ (N : Real) ^ (-(1 : Real)) * (N : Real) ^ (-D / 2 - 9) :=
        mul_le_mul_of_nonneg_left hsqrtGap (by positivity)
      _ = (N : Real) ^ (-D / 2 - 10) := by
        rw [← Real.rpow_add hNpos]
        congr 1 <;> ring
  have hK0 : 0 ≤
      (15 / 2 : Real) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
    mul_nonneg (by norm_num)
      (le_of_lt APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos)
  have hcross1 := mul_le_mul_of_nonneg_left hprofileFactor hK0
  have hcross2 := mul_le_mul_of_nonneg_left hbadFactor
      (by norm_num : (0 : Real) ≤ 15 / 2)
  calc
    _ ≤ (15 / 2 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
            R ^ (-(2 : Real)) * (Real.sqrt v - Real.sqrt (s N)) +
        (15 / 2 : Real) * (N : Real) ^ (-(1 : Real)) *
          (Real.sqrt v - Real.sqrt (s N)) := hcrossRaw
    _ ≤ (15 / 2 : Real) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : Real) ^ (13 * δ / 640 - D / 2 - 8) * R ^ (-(2 : Real)) +
          (15 / 2 : Real) * (N : Real) ^ (-D / 2 - 10) := by
          nlinarith [hcross1, hcross2]

set_option maxHeartbeats 1000000 in
-- The cross-integral endpoint reductions make elaboration exceed Lean's default heartbeat budget.
/-- The exact p=1 consumer inequality on every active cell in the `N^(3D)`
prefix, uniformly in the output labels after one fixed-parameter cutoff. -/
theorem eventually_early_prefix_3D_p1_N1_consumer
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      1 ≤ k → k ≤ cutNetTop s t (mesh D) N →
      (k : Real) ≤ (N : Real) ^ (3 * D) →
      ∀ a : LoopArg (d.L N) 2,
        let x := (N : Real) ^ (δ / 8)
        let v := cutNetPt s (mesh D) N k
        let R := Step2Moment.ratR E s N v
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u +
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k 1 a u) ≤
          APrimeOneStep.driftTerm (mE E).im x R
            (APrimeInit.slotXi' x) (APrimeSlotArith.slotA x R)
            (APrimeSlotArith.slotEps x R) (APrimeSlotArith.slotQ R)
            (APrimeSlotArith.slotBeta x R) (APrimeSlotArith.slotGamma x R)
            (APrimeSlotArith.slotJv x R) / R ^ 4 := by
  have hDriftEnvelope :=
    APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
      hE hD hs0 hst ht1 hc hreg
  have hCross := eventually_integral_positive_cross_le_prefix
    hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hEta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hRoom := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hRoom with ⟨hDeltaWeight, hXi, hDeltaCap, hTauG, hZetaSrc, hZetaCtr,
    _, _, _, _, _, _, _⟩
  have hDriftInt :=
    APrimeGeneralMovingSmoothDriftNormBudget.eventually_actual_smooth_drift_integral_le_exact_profile
      hE hD hs0 hst ht1 hc hreg hB
      hZetaSrc hZetaCtr hTauG hDeltaWeight hXi
      1 (by norm_num) 1 (by norm_num)
  have hFullIntegrable :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      1 (by norm_num)
  have hKpos :
      0 < APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hmpos : 0 < (mE E).im := mE_im_pos hE
  have hAbsorb := eventually_le_rpow
    (2 * (mE E).im *
      (17 + 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst))
    (by norm_num : (0 : Real) < 1)
  filter_upwards [hDriftEnvelope, hCross, hEta, hMesh, hDriftInt, hFullIntegrable,
      hAbsorb, eventually_ge_atTop 2]
    with N hDriftN hCrossN hEtaN hMeshN hDriftIntN hFullIntegrableN hAbsorbN hN2
  intro k hkpos hk hkprefix a
  let x : Real := (N : Real) ^ (δ / 8)
  let v : Real := cutNetPt s (mesh D) N k
  let R : Real := Step2Moment.ratR E s N v
  have hN : (1 : Real) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : Real) < N := by linarith
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hRpos : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos hE (hsv.trans_lt hv1) hv1
  have hRge : 1 ≤ R := by
    dsimp [R]
    exact Step2Moment.one_le_ratR hE hsv hv1
  have hMeshEq : mesh D N = (N : Real) ^ (4 * D + 18) := by
    simpa [mesh] using hMeshN
  have hMeshTarget : APrimeGeneralMovingMesh.targetMesh D N =
      (N : Real) ^ (4 * D + 18) := hMeshN
  have hwidth : v - s N ≤ (N : Real) ^ (-D - 18) := by
    have hgap : v - s N = (k : Real) / mesh D N := by
      simp [v, CutHypTheta.cutNetPt]
    rw [hgap, hMeshEq]
    have hdiv := div_le_div_of_nonneg_right hkprefix
      (le_of_lt (APrimeGeneralMovingMesh.targetMesh_pos D N))
    rw [hMeshTarget] at hdiv
    have hpow : (N : Real) ^ (3 * D) / (N : Real) ^ (4 * D + 18) =
        (N : Real) ^ (-D - 18) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
      congr 1
      ring
    exact hdiv.trans_eq hpow
  have hgi : IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a)
      volume (s N) v := by
    change IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a)
      volume (s N)
        (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k)
    exact APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      hE hs0 hst ht1 (by omega) hk a
  have hfullInt : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N k 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hFullIntegrableN k hk a
  have hDriftPoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u ≤
          (N : Real) ^ (D + 8) := by
    intro u hu
    have hY : ∀ ω : Gauss.Ω d,
        |APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a (s N) v u ω| ≤
          (N : Real) ^ (D + 8) := by
      intro ω
      have h := hDriftN k hk
      simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
        h u hu a ω
    have hW0 : ∀ ω : Gauss.Ω d,
        0 ≤ APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k ω :=
      APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k
    have hW1 : ∀ ω : Gauss.Ω d,
        APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k ω ≤ 1 :=
      APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k
    have hnorm := momNormW_one_le_of_abs_le
      (P := Gauss.P d)
      (W := APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k)
      (Y := fun ω => APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a (s N) v u ω)
      (by simpa using hW0) (by simpa using hW1) (by positivity) hY
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hnorm
  have hgiConst : IntervalIntegrable
      (fun _ : Real => (N : Real) ^ (D + 8)) volume (s N) v :=
    intervalIntegrable_const
  have hDriftIntegral :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) ≤
        (N : Real) ^ (-10 : Real) := by
    have hmono := intervalIntegral.integral_mono_on hsv hgi hgiConst hDriftPoint
    rw [intervalIntegral.integral_const] at hmono
    have hwidthNonneg : 0 ≤ v - s N := sub_nonneg.mpr hsv
    have hwidthPow : (N : Real) ^ (-D - 18) * (N : Real) ^ (D + 8) =
        (N : Real) ^ (-10 : Real) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc
      _ ≤ (v - s N) * (N : Real) ^ (D + 8) := by simpa [smul_eq_mul] using hmono
      _ ≤ (N : Real) ^ (-D - 18) * (N : Real) ^ (D + 8) :=
        mul_le_mul_of_nonneg_right hwidth (by positivity)
      _ = (N : Real) ^ (-10 : Real) := hwidthPow
  have hCrossN := hCrossN k hkpos hk hkprefix a
  have hq : 13 * δ / 640 - D / 2 - 8 ≤ -1 := by
    have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left 1 (c / 100))
    nlinarith
  have hr : -D / 2 - 10 ≤ -1 := by linarith
  have hpowq : (N : Real) ^ (13 * δ / 640 - D / 2 - 8) ≤ (N : Real) ^ (-1 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hN
      (by
        have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left 1 (c / 100))
        nlinarith [hD])
  have hpowr : (N : Real) ^ (-D / 2 - 10) ≤ (N : Real) ^ (-1 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hN hr
  have hRpow : R ^ (-(2 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRge (by norm_num)
  have hCrossCoeffNonneg : 0 ≤
      15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
    mul_nonneg (by norm_num)
      (le_of_lt APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos)
  have hCrossTimesTwo :
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k 1 a u) ≤
        15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real) ^ (-1 : Real) + 15 * (N : Real) ^ (-1 : Real) := by
    have hbound := mul_le_mul_of_nonneg_left hCrossN (by norm_num : (0 : Real) ≤ 2)
    have hpowBase : 0 ≤ (N : Real) ^ (13 * δ / 640 - D / 2 - 8) := by positivity
    have hprofileR :
        (N : Real) ^ (13 * δ / 640 - D / 2 - 8) * R ^ (-(2 : Real)) ≤
          (N : Real) ^ (13 * δ / 640 - D / 2 - 8) :=
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left hRpow hpowBase
    calc
      _ ≤ 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real) ^ (13 * δ / 640 - D / 2 - 8) * R ^ (-(2 : Real)) +
          15 * (N : Real) ^ (-D / 2 - 10) := by nlinarith [hbound]
      _ ≤ 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real) ^ (13 * δ / 640 - D / 2 - 8) +
          15 * (N : Real) ^ (-D / 2 - 10) := by
            have hleft := mul_le_mul_of_nonneg_left hprofileR hCrossCoeffNonneg
            nlinarith [hleft]
      _ ≤ 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : Real) ^ (-1 : Real) + 15 * (N : Real) ^ (-1 : Real) := by
            have hq' := mul_le_mul_of_nonneg_left hpowq hCrossCoeffNonneg
            have hr' := mul_le_mul_of_nonneg_left hpowr
              (by norm_num : (0 : Real) ≤ 15)
            exact add_le_add hq' hr'
  have hDriftTimesTwo :
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) ≤
        2 * (N : Real) ^ (-1 : Real) := by
    have hpow : (N : Real) ^ (-10 : Real) ≤ (N : Real) ^ (-1 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    nlinarith [hDriftIntegral, hpow]
  have hsumBound :
      2 * ((∫ u in (s N)..v,
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) +
          (∫ u in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k 1 a u)) ≤
        (17 + 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) *
          (N : Real) ^ (-1 : Real) := by
    calc
      _ = 2 * (∫ u in (s N)..v,
              APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) +
            2 * (∫ u in (s N)..v,
              APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
                E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                s t N k 1 a u) := by ring
      _ ≤ 2 * (N : Real) ^ (-1 : Real) +
            (15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real)^(-1 : Real) + 15 * (N : Real)^(-1 : Real)) :=
            add_le_add hDriftTimesTwo hCrossTimesTwo
      _ = _ := by ring
  have hAbsorbN' :
      2 * (mE E).im *
          (17 + 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) ≤
        (N : Real) := by
    simpa only [Real.rpow_one] using hAbsorbN
  have hsmall :
      (17 + 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) *
          (N : Real) ^ (-1 : Real) ≤ 1 / (2 * (mE E).im) := by
    have hNpow : (N : Real) ^ (-1 : Real) = 1 / (N : Real) := by
      rw [Real.rpow_neg (by exact_mod_cast hNpos.le), Real.rpow_one]
      simp
    rw [hNpow, mul_one_div]
    apply (div_le_iff₀ hNpos).2
    have hmpos : 0 < 2 * (mE E).im := by positivity
    have hAbsorb'' :
        (17 + 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) *
            (2 * (mE E).im) ≤ (N : Real) := by
      calc
        _ = 2 * (mE E).im *
            (17 + 15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst) := by ring
        _ ≤ (N : Real) := hAbsorbN'
    calc
      _ ≤ (N : Real) / (2 * (mE E).im) :=
        (le_div_iff₀ hmpos).2 hAbsorb''
      _ = (1 / (2 * (mE E).im)) * (N : Real) := by ring
  have hconsumerLower :
      1 / (2 * (mE E).im) ≤
        APrimeOneStep.driftTerm (mE E).im x R
          (APrimeInit.slotXi' x) (APrimeSlotArith.slotA x R)
          (APrimeSlotArith.slotEps x R) (APrimeSlotArith.slotQ R)
          (APrimeSlotArith.slotBeta x R) (APrimeSlotArith.slotGamma x R)
          (APrimeSlotArith.slotJv x R) / R ^ 4 := by
    have hx0 : 0 ≤ x := by positivity
    have hx : 1 ≤ x := by
      dsimp [x]
      exact Real.one_le_rpow hN (by linarith [hδ])
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hR0 : 0 ≤ R := hRpos.le
    have hside := APrimeInit.slotSide' hx hRge
    have hXi0 : 0 ≤ APrimeInit.slotXi' x := by
      unfold APrimeInit.slotXi'
      positivity
    have hA0 : 0 < APrimeSlotArith.slotA x R := by
      unfold APrimeSlotArith.slotA
      have hcwt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
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
      hmpos hx0 hR0 hXi0 hA0 hside.ε_nonneg hside.β_nonneg
        hside.γ_nonneg hside.Jv_nonneg
    have hNearDiv := div_le_div_of_nonneg_right hnear
      (by positivity : (0 : Real) ≤ R ^ 4)
    have hxy : x * APrimeInit.slotXi' x = x ^ (5 / 4 : Real) := by
      unfold APrimeInit.slotXi'
      calc
        x * x ^ (1 / 4 : Real) = x ^ (1 : Real) * x ^ (1 / 4 : Real) := by
          rw [Real.rpow_one]
        _ = x ^ ((1 : Real) + 1 / 4) := (Real.rpow_add hxpos _ _).symm
        _ = x ^ (5 / 4 : Real) := by congr 1 <;> ring
    have hxy' : APrimeInit.slotXi' x * x = x ^ (5 / 4 : Real) := by
      rw [mul_comm, hxy]
    have hnearEq :
        APrimeInit.slotXi' x * (x * (mE E).im⁻¹ * R ^ 2 * APrimeSlotArith.slotQ R) /
            R ^ 4 = x ^ (5 / 4 : Real) / (2 * (mE E).im) := by
      unfold APrimeSlotArith.slotQ
      rw [div_eq_mul_inv]
      field_simp [ne_of_gt hRpos]
      rw [hxy']
    have hxpow : 1 ≤ x ^ (5 / 4 : Real) := Real.one_le_rpow hx (by norm_num)
    have hfactor : 1 / (2 * (mE E).im) ≤ x ^ (5 / 4 : Real) / (2 * (mE E).im) :=
      div_le_div_of_nonneg_right hxpow (by positivity)
    rw [hnearEq] at hNearDiv
    exact hfactor.trans hNearDiv
  have hsumIntegrable : IntervalIntegrable
      (fun u =>
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u +
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u)
      volume (s N) v := hgi.add hfullInt
  have hsumEq :
      (∫ u in (s N)..v,
        (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u +
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u)) =
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) +
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k 1 a u) :=
    intervalIntegral.integral_add hgi hfullInt
  dsimp [x, v, R]
  rw [hsumEq]
  exact (hsumBound.trans hsmall).trans hconsumerLower

#print axioms nondegenerate_early_prefix_witness
#print axioms eventually_early_prefix_3D_p1_N1_consumer

end
end RBM.APrimeGeneralMovingEarlyPrefix3DP1N1Consumer
