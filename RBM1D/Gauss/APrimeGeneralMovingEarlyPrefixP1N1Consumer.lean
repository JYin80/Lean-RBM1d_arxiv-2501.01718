/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossPointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeSlotArith
import RBM1D.Gauss.APrimeInit

/-!
# T1269: the p=1 N1 consumer on a growing early prefix

On every active target-mesh cell in the growing prefix `1 ≤ k ≤ N^D`, the
literal T615 actual-smooth drift integral plus the full positive-time cross
budget fit the T230 A-prime drift slot with `APrimeInit.slotXi'`. This local
consumer does not assert an all-cell or general A-prime result.
-/

namespace RBM.APrimeGeneralMovingEarlyPrefixP1N1Consumer

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's same-event, positive-actual-weight witness at `p=1` and a positive
cell. The first positive cell is contained in the growing early prefix. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

private theorem eventually_prefix_geometry
    {D : ℝ} {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (N : ℝ) ^ D →
        k ≤ cutNetTop s t (mesh D) N →
        let v := cutNetPt s (mesh D) N k
        v ∈ Icc (s N) (t N) ∧
          v - s N ≤ (N : ℝ) ^ (-3 * D - 18) ∧
          Real.sqrt v - Real.sqrt (s N) ≤ (N : ℝ) ^ (-3 * D / 2 - 9) := by
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  filter_upwards [hMesh, eventually_ge_atTop 2] with N hMeshN hN2
  intro k hkpos hkGrow hkActive
  let v := cutNetPt s (mesh D) N k
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hkActive
  have hkR : (k : ℝ) ≤ (N : ℝ) ^ D := hkGrow
  have hden : 0 < (N : ℝ) ^ (4 * D + 18) :=
    Real.rpow_pos_of_pos hNpos _
  have hpow : (N : ℝ) ^ D =
      (N : ℝ) ^ (4 * D + 18) * (N : ℝ) ^ (-3 * D - 18) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hlength : v - s N ≤ (N : ℝ) ^ (-3 * D - 18) := by
    have hcut : v - s N = (k : ℝ) / (mesh D N) := by
      simp [v, mesh, CutHypTheta.cutNetPt]
    rw [hcut, show mesh D N = APrimeGeneralMovingMesh.targetMesh D N by rfl,
      hMeshN]
    apply (div_le_iff₀ hden).2
    calc
      (k : ℝ) ≤ (N : ℝ) ^ D := hkR
      _ = (N : ℝ) ^ (4 * D + 18) * (N : ℝ) ^ (-3 * D - 18) := hpow
      _ = (N : ℝ) ^ (-3 * D - 18) * (N : ℝ) ^ (4 * D + 18) := by ring
  have hsqrtGap : Real.sqrt v - Real.sqrt (s N) ≤
      (N : ℝ) ^ (-3 * D / 2 - 9) := by
    have hroot := Gauss.abs_sqrt_sub_sqrt_le v (s N)
    have habs : |v - s N| = v - s N :=
      abs_of_nonneg (sub_nonneg.mpr hv.1)
    have hdiff : Real.sqrt v - Real.sqrt (s N) ≤ Real.sqrt (v - s N) := by
      calc
        _ ≤ |Real.sqrt v - Real.sqrt (s N)| := le_abs_self _
        _ ≤ Real.sqrt |v - s N| := hroot
        _ = Real.sqrt (v - s N) := by rw [habs]
    have hrootLe := Real.sqrt_le_sqrt hlength
    have hrootEq : Real.sqrt ((N : ℝ) ^ (-3 * D - 18)) =
        (N : ℝ) ^ (-3 * D / 2 - 9) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    exact hdiff.trans (hrootLe.trans_eq hrootEq)
  exact ⟨hv, hlength, hsqrtGap⟩

/-- The literal T615 actual-smooth p=1 drift integral on each active growing
early-prefix cell. -/
theorem eventually_integral_actual_smooth_g_le_early_prefix
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (_hB : BoundsCore (Gauss.sample d) E s)
    (_hδ : 0 < δ) (_hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (N : ℝ) ^ D →
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          IntervalIntegrable
              (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a)
              volume (s N) (cutNetPt s (mesh D) N k) ∧
            (∫ u in (s N)..(cutNetPt s (mesh D) N k),
              APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) ≤
              (N : ℝ) ^ (-2 * D - 10) := by
  have henv := APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
    hE hD hs0 hst ht1 hc hreg
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  have hGeometry := eventually_prefix_geometry (D := D) hst
  filter_upwards [henv, hMesh, hGeometry, eventually_ge_atTop 2]
    with N henvN hMeshN hGeometryN hN2
  intro k hkpos hkGrow hkActive a
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hkActive
  have hgi := APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
    (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
    (p := 1) hE hs0 hst ht1 (by omega) hkActive a
  have hpoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u ≤
          (N : ℝ) ^ (D + 8) := by
    intro u hu
    have henvPoint := henvN k hkActive u hu a
    letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
    have hnorm := APrimeModel.momNormW_le_of_le_on
      (P := Gauss.P d)
      (W := APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k)
      (Y := APrimeGeneralMovingSmoothDriftNormBudget.drift E D s t N k a u)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k)
      (p := 1) (by norm_num) (c := (N : ℝ) ^ (D + 8)) (by positivity)
      (G := Set.univ)
      (by intro ω _; simpa [APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
        APrimeGeneralMovingSmoothDriftNormBudget.drift] using henvPoint ω)
      (by intro ω hω; exact (hω (Set.mem_univ ω)).elim)
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift] using hnorm
  have hmono := intervalIntegral.integral_mono_on hv.1 hgi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (N : ℝ) ^ (D + 8)) volume (s N) v)
    hpoint
  have hgeometryN := hGeometryN k hkpos hkGrow hkActive
  have hbound : (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u) ≤
      (v - s N) * (N : ℝ) ^ (D + 8) := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hmono
  refine ⟨hgi, ?_⟩
  calc
    _ ≤ (N : ℝ) ^ (-3 * D - 18) * (N : ℝ) ^ (D + 8) := by
      exact hbound.trans (mul_le_mul_of_nonneg_right hgeometryN.2.1 (by positivity))
    _ = (N : ℝ) ^ (-2 * D - 10) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

theorem eventually_integral_full_positive_cross_le_early_prefix
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (N : ℝ) ^ D →
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          (∫ u in (s N)..(cutNetPt s (mesh D) N k),
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                s t N k 1 a u) ≤
            (15 / 2 : ℝ) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) *
                  (Step2Moment.ratR E s N (cutNetPt s (mesh D) N k)) ^ (-(2 : ℝ)) +
              (15 / 2 : ℝ) * (N : ℝ) ^ (-3 * D / 2 - 10) := by
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
  have hGeometry := eventually_prefix_geometry (D := D) hst
  have hMesh := APrimeGeneralMovingMesh.eventually_targetMesh_eq D
  filter_upwards [hProfile, hGoodPoint, hFullIntegral, hGoodIntegrable,
      hFullIntegrable, hEta, hGeometry, hMesh, eventually_ge_atTop 2]
    with N hProfileN hGoodPointN hFullIntegralN hGoodIntegrableN
      hFullIntegrableN hEtaN hGeometryN hMeshN hN2
  intro k hkpos hkGrow hkActive a
  let v := cutNetPt s (mesh D) N k
  let R := Step2Moment.ratR E s N v
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hGeometry' := hGeometryN k hkpos hkGrow hkActive
  have hv := hGeometry'.1
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
  have hgap0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hsqrtGap := hGeometry'.2.2
  have hGoodInt : IntervalIntegrable
      (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hGoodIntegrableN k hkActive a
  have hFullInt : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hFullIntegrableN k hkActive a
  let Cgood : ℝ :=
    (15 / 4 : ℝ) *
        APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
        (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ * R ^ (-(2 : ℝ)) +
      (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ))
  have hCgood0 : 0 ≤ Cgood := by
    have hconst :=
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
    have hetaS : 0 < etaT E (s N) :=
      Step2.etaT_pos' hE (hsv.trans_lt hv1)
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
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a u ≤
          major u := by
    intro u hu
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    by_cases huPos : 0 < u
    · have hgp := hGoodPointN k hkActive a u hu huPos
      have hprof := hProfileN k hkActive a u hu huPos
      have hprof' :
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
              R ^ (-(2 : ℝ)) / Real.sqrt u := by
        simpa [mesh, v, R] using hprof
      have hprofMul := mul_le_mul_of_nonneg_left hprof'
        (by norm_num : (0 : ℝ) ≤ 15 / 4)
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
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
            ((15 / 4 : ℝ) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                  R ^ (-(2 : ℝ))) * (Real.sqrt u)⁻¹ := by
        calc
          _ ≤ (15 / 4 : ℝ) *
              (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                  R ^ (-(2 : ℝ)) / Real.sqrt u) := hprofMul
          _ = _ := by rw [div_eq_mul_inv]; ring
      have hsumEnvelope := add_le_add hprofEnvelope
        (le_of_eq (show
          (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt u)⁻¹ =
            (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) * (Real.sqrt u)⁻¹ by rfl))
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
  have hgoodIntegral := intervalIntegral.integral_mono_on hsv
    hGoodInt hmajorInt hgoodPoint
  have hfullN := hFullIntegralN k hkActive a
  have hcrossRaw :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a u) ≤
        (15 / 2 : ℝ) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                R ^ (-(2 : ℝ)) * (Real.sqrt v - Real.sqrt (s N)) +
          (15 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
              (Real.sqrt v - Real.sqrt (s N)) := by
    have hfull := hFullIntegralN k hkActive a
    have hfull' :
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a r) ≤
          (∫ r in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k 1 a r) +
            (15 * (1 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
              (Real.sqrt v - Real.sqrt (s N)) := by
      simpa [mesh, v] using hfull
    have hPaymentEq :
        (15 * (1 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N)) =
          (15 / 4 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N)) := by norm_num
    have hcomb := hfull'.trans (add_le_add hgoodIntegral (le_of_eq hPaymentEq))
    rw [hmajorEval] at hcomb
    dsimp [Cgood] at hcomb
    convert hcomb using 1 <;> ring
  have hNpow :
      (N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
          (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) := by
    have hpow :
        (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) *
          (N : ℝ) ^ (-3 * D / 2 - 9) =
        (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) := by
      calc
        _ = (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) ^ (1 : ℝ) *
            (N : ℝ) ^ (-3 * D / 2 - 9) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ (13 * δ / 640 + 1 + (-3 * D / 2 - 9)) := by
              rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        _ = _ := by congr 1 <;> ring
    calc
      _ ≤ (N : ℝ) ^ (13 * δ / 640) * (N : ℝ) *
          (N : ℝ) ^ (-3 * D / 2 - 9) := by
        have hprod :
            (etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N)) ≤
              (N : ℝ) * (N : ℝ) ^ (-3 * D / 2 - 9) :=
          mul_le_mul hetaInvS hsqrtGap (by positivity) (by positivity)
        calc
          _ = (N : ℝ) ^ (13 * δ / 640) *
              ((etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N))) := by ring
          _ ≤ (N : ℝ) ^ (13 * δ / 640) *
              ((N : ℝ) * (N : ℝ) ^ (-3 * D / 2 - 9)) :=
                mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = _ := by ring
      _ = _ := hpow
  have herror : (N : ℝ) ^ (-(1 : ℝ)) *
      (Real.sqrt v - Real.sqrt (s N)) ≤
        (N : ℝ) ^ (-3 * D / 2 - 10) := by
    have hpow :
        (N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ (-3 * D / 2 - 9) =
          (N : ℝ) ^ (-3 * D / 2 - 10) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc
      _ ≤ (N : ℝ) ^ (-(1 : ℝ)) *
          (N : ℝ) ^ (-3 * D / 2 - 9) := by
        gcongr
      _ = _ := hpow
  have hmainBound := mul_le_mul_of_nonneg_left hNpow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ (15 / 2 : ℝ))
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos.le)
  have herrBound := mul_le_mul_of_nonneg_left herror
    (by norm_num : (0 : ℝ) ≤ (15 / 2 : ℝ))
  calc
    _ ≤ (15 / 2 : ℝ) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            ((N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
              (Real.sqrt v - Real.sqrt (s N))) * R ^ (-(2 : ℝ)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) := by
      convert hcrossRaw using 1 <;> ring
    _ ≤ (15 / 2 : ℝ) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) * R ^ (-(2 : ℝ)) +
        (15 / 2 : ℝ) * (N : ℝ) ^ (-3 * D / 2 - 10) := by
      have hfirst :
          (15 / 2 : ℝ) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                ((N : ℝ) ^ (13 * δ / 640) * (etaT E (s N))⁻¹ *
                  (Real.sqrt v - Real.sqrt (s N))) * R ^ (-(2 : ℝ)) ≤
            (15 / 2 : ℝ) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) * R ^ (-(2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_right hmainBound hRpow0
        simpa [mul_assoc] using hmul
      exact add_le_add hfirst (by simpa [mul_assoc] using herrBound)
    _ = _ := by ring

/-- Exact p=1 T615 drift plus the full positive-time cross-budget consumer on
every active cell in the growing early prefix, uniformly over all outputs. -/
theorem eventually_early_prefix_N1_consumer
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (N : ℝ) ^ D →
        k ≤ cutNetTop s t (mesh D) N →
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
  have hDrift := eventually_integral_actual_smooth_g_le_early_prefix
    hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hCross := eventually_integral_full_positive_cross_le_early_prefix
    hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hCrossIntegrable :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg
      (show 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ by
        unfold APrimeGeneralMovingSlotLossSchedule.deltaWeight
        positivity)
      1 (by norm_num)
  have hGeometry := eventually_prefix_geometry (D := D) hst
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
  filter_upwards [hDrift, hCross, hCrossIntegrable, hGeometry, hEta,
      APrimeGeneralMovingMesh.eventually_targetMesh_eq D,
      eventually_ge_atTop 2, hAbsorb]
    with N hDriftN hCrossN hCrossIntegrableN hGeometryN hEtaN hMeshN hN2 hAbsorbN
  intro k hkpos hkGrow hkActive a
  let x := (N : ℝ) ^ (δ / 8)
  let v := cutNetPt s (mesh D) N k
  let R := Step2Moment.ratR E s N v
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hv := hGeometryN k hkpos hkGrow hkActive |>.1
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
  have hDriftCell := hDriftN k hkpos hkGrow hkActive a
  have hCrossCell := hCrossN k hkpos hkGrow hkActive a
  have hCrossInt : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a)
      volume (s N) v := by
    simpa [mesh, v] using hCrossIntegrableN k hkActive a
  have hadd := intervalIntegral.integral_add hDriftCell.1 hCrossInt
  have htotalBound :
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k 1 a u) ≤
        2 * (N : ℝ) ^ (-2 * D - 10) +
          15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) * R ^ (-(2 : ℝ)) +
          15 * (N : ℝ) ^ (-3 * D / 2 - 10) := by
    rw [hadd]
    have hDmul := mul_le_mul_of_nonneg_left hDriftCell.2
      (by norm_num : (0 : ℝ) ≤ 2)
    have hCmul := mul_le_mul_of_nonneg_left hCrossCell
      (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hRneg : R ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRge (by norm_num)
  have hRneg0 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have he1 : -2 * D - 10 ≤ -1 := by linarith [hD]
  have he2 : 13 * δ / 640 - 3 * D / 2 - 8 ≤ -1 := by nlinarith [hD, hδ1]
  have he3 : -3 * D / 2 - 10 ≤ -1 := by linarith [hD]
  have hp1 : (N : ℝ) ^ (-2 * D - 10) ≤ (N : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN he1
  have hp2 : (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) ≤
      (N : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN he2
  have hp3 : (N : ℝ) ^ (-3 * D / 2 - 10) ≤ (N : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN he3
  have hSmall :
      2 * (N : ℝ) ^ (-2 * D - 10) +
        15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) * R ^ (-(2 : ℝ)) +
        15 * (N : ℝ) ^ (-3 * D / 2 - 10) ≤ K / (N : ℝ) := by
    have hC0 : 0 ≤ APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos.le
    have hNexp : 0 ≤ (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) := by positivity
    have hRreduce :
        (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) * R ^ (-(2 : ℝ)) ≤
          (N : ℝ) ^ (-(1 : ℝ)) := by
      calc
        _ ≤ (N : ℝ) ^ (13 * δ / 640 - 3 * D / 2 - 8) := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hRneg hNexp
        _ ≤ (N : ℝ) ^ (-(1 : ℝ)) := hp2
    have hterm1 := mul_le_mul_of_nonneg_left hp1
      (by norm_num : (0 : ℝ) ≤ 2)
    have hterm2 := mul_le_mul_of_nonneg_left hRreduce
      (by positivity : (0 : ℝ) ≤
        15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst)
    have hterm3 := mul_le_mul_of_nonneg_left hp3
      (by norm_num : (0 : ℝ) ≤ 15)
    calc
      _ ≤ 2 * (N : ℝ) ^ (-(1 : ℝ)) +
          15 * APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ) ^ (-(1 : ℝ)) +
          15 * (N : ℝ) ^ (-(1 : ℝ)) := by
        exact add_le_add (add_le_add hterm1 (by nlinarith [hterm2])) hterm3
      _ = K / (N : ℝ) := by
        dsimp [K]
        rw [Real.rpow_neg_one]
        ring
  have hAbsorb' : 2 * (mE E).im * K ≤ (N : ℝ) := by
    simpa [m, K, Real.rpow_one, mul_assoc] using hAbsorbN
  have hKdiv : K / (N : ℝ) ≤ 1 / (2 * (mE E).im) := by
    rw [div_le_div_iff₀ hNpos (by positivity : 0 < 2 * (mE E).im)]
    calc
      K * (2 * (mE E).im) = 2 * (mE E).im * K := by ring
      _ ≤ (N : ℝ) := hAbsorb'
      _ = 1 * (N : ℝ) := by ring
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
  have hXi0 : 0 ≤ APrimeInit.slotXi' x := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (APrimeInit.slotXi'_ge_one hx)
  have hNear := APrimeSlotArith.driftTerm_ge_near
    (m := (mE E).im) (x := x) (R := R)
    (Ξ := APrimeInit.slotXi' x)
    (A := APrimeSlotArith.slotA x R)
    (ε := APrimeSlotArith.slotEps x R)
    (q := APrimeSlotArith.slotQ R)
    (β := APrimeSlotArith.slotBeta x R)
    (γ := APrimeSlotArith.slotGamma x R)
    (Jv := APrimeSlotArith.slotJv x R)
    hmE (by positivity) hRpos.le hXi0 hA0 hEps0 hBeta0 hGamma0 hJv0
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
    exact div_le_div_of_nonneg_right hNear (by positivity : 0 ≤ R ^ 4)
  have hxpow : 1 ≤ x ^ (5 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hconstNear : 1 / (2 * (mE E).im) ≤
      x ^ (5 / 4 : ℝ) / (2 * (mE E).im) := by
    have h := mul_le_mul_of_nonneg_right hxpow
      (by positivity : 0 ≤ (2 * (mE E).im)⁻¹)
    simpa [div_eq_mul_inv] using h
  have hconsumer : 1 / (2 * (mE E).im) ≤
      APrimeOneStep.driftTerm (mE E).im x R (APrimeInit.slotXi' x)
        (APrimeSlotArith.slotA x R) (APrimeSlotArith.slotEps x R)
        (APrimeSlotArith.slotQ R) (APrimeSlotArith.slotBeta x R)
        (APrimeSlotArith.slotGamma x R) (APrimeSlotArith.slotJv x R) / R ^ 4 :=
    hconstNear.trans (hnearEq ▸ hnearDiv)
  exact htotalBound.trans (hSmall.trans (hKdiv.trans hconsumer))

#print axioms eventually_integral_actual_smooth_g_le_early_prefix
#print axioms eventually_integral_full_positive_cross_le_early_prefix
#print axioms eventually_early_prefix_N1_consumer
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingEarlyPrefixP1N1Consumer
