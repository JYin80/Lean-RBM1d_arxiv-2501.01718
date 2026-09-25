/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualDriftStrictExponent
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic

/-!
# T1289: strict-exponent actual smooth drift plus full cross budget

This combines the literal T615 actual-smooth drift integral with the full
positive-time cross-budget integral.  The cross estimate uses the T1207
full-to-norm-good integral reduction, the all-order T1277 pointwise bridge,
and the T1245 microscopic bound for the deterministic T1029 cross profile.
It is a smooth-prefix auxiliary estimate, not the stopped stochastic result
of (5.21), (5.24), and (5.40)--(5.43).
-/

namespace RBM.APrimeGeneralMovingDriftCrossAllOrdersStrictExponent

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open APrimeGeneralMovingCrossBudgetGoodIntegralReduction

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D

/-- Fixed constant in the all-order full-cross endpoint estimate. -/
noncomputable def crossAllOrdersBudgetConst (E : Real) (p : Nat) : Real :=
  (15 * (p : Real) / 2) *
    (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
      (mE E).im + 1)

theorem crossAllOrdersBudgetConst_pos {E : Real} (p : Nat) (hp : 1 ≤ p)
    (hE : |E| < 2) :
    0 < crossAllOrdersBudgetConst E p := by
  unfold crossAllOrdersBudgetConst
  have hpR : 0 < (p : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hp)
  have him : 0 < (mE E).im := mE_im_pos hE
  exact mul_pos (by positivity)
    (by positivity [APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos])

private theorem sqrt_gap_le_one_sub_start {s v : Real}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v ≤ 1) :
    0 ≤ Real.sqrt v - Real.sqrt s ∧
      Real.sqrt v - Real.sqrt s ≤ 1 - s := by
  have hs1 : s ≤ 1 := hsv.trans hv1
  have hrootv : Real.sqrt v ≤ 1 := Real.sqrt_le_one.mpr hv1
  have hroots : s ≤ Real.sqrt s := by
    have hroots1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1
    have hmul := mul_nonneg (Real.sqrt_nonneg s)
      (by linarith [hroots1] : 0 ≤ 1 - Real.sqrt s)
    nlinarith [Real.sq_sqrt hs0]
  constructor
  · exact sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  · linarith

set_option maxHeartbeats 1000000 in
private theorem eta_start_inv_mul_sqrt_gap_le_inv_im
    {E s v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsv : s ≤ v) (hv1 : v ≤ 1) :
    (etaT E s)⁻¹ * (Real.sqrt v - Real.sqrt s) ≤ (mE E).im⁻¹ := by
  have him : 0 < (mE E).im := mE_im_pos hE
  have hgap := sqrt_gap_le_one_sub_start hs0 hsv hv1
  have hfrac : (Real.sqrt v - Real.sqrt s) / (1 - s) ≤ 1 := by
    apply (div_le_iff₀ (sub_pos.mpr hs1)).2
    linarith [hgap.2]
  have heq : (etaT E s)⁻¹ * (Real.sqrt v - Real.sqrt s) =
      ((Real.sqrt v - Real.sqrt s) / (1 - s)) * (mE E).im⁻¹ := by
    rw [Step2.etaT_eq]
    field_simp [ne_of_gt (sub_pos.mpr hs1), ne_of_gt him]
  rw [heq]
  calc
    _ ≤ 1 * (mE E).im⁻¹ :=
      mul_le_mul_of_nonneg_right hfrac (inv_nonneg.mpr him.le)
    _ = _ := by ring

/-- For each fixed `p ≥ 1`, the literal unrestricted T1201 positive-time
cross budget has a strict `δ/8` endpoint-scale integral bound on every active
T995 target cell, including `k = 0`.  The same eventual cutoff works for all
outputs. -/
theorem eventually_integral_positiveTimeCrossBudget_le_delta_eighth
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        IntervalIntegrable
          (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a)
          volume (s N) v ∧
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r) ≤
          crossAllOrdersBudgetConst E p * (N : Real)^(δ / 8) *
            Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  let zetaSrc := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ
  let tauG := APrimeGeneralMovingSlotLossSchedule.tauG δ
  let deltaCap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  have hrooms := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hrooms with ⟨hdw, _hxi, _hcap, htau, hzsrc, _hzctr, _hbuffer,
      _hzsrcTau, _htauCap, _hcapC, _hcapRoom, _, _⟩
  have hFullInt :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg hdw.le p hp
  have hGoodInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdw.le p hp
  have hReduction :=
    eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      hE hD hs0 hst ht1 hc hreg hdw.le p hp
  have hBridge := _root_.RBM.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise.eventually_normGoodCrossBudget_le_crossProfile_add_bad_allOrders_pointwise
        hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hMicro :=
    _root_.RBM.APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
        hE (le_trans (by norm_num : (0 : Real) ≤ 60) hD) hs0 hst ht1 hc hreg hδ hδsmall
  have hMargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hFullInt, hGoodInt, hReduction, hBridge, hMicro,
      hMargin, (Gauss.band d).dim, eventually_ge_atTop 1]
    with N hFullIntN hGoodIntN hReductionN hBridgeN hMicroN hMarginN hdim hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNnonneg : 0 ≤ (N : Real) := by linarith
  have him : 0 < (mE E).im := mE_im_pos hE
  have halpha : 13 * δ / 640 ≤ δ / 8 := by nlinarith [hδ]
  have hpow : (N : Real)^(13 * δ / 640) ≤ (N : Real)^(δ / 8) :=
    Real.rpow_le_rpow_of_exponent_le hNreal halpha
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hsv : s N ≤ v := hv.1
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hsv hv1
  let vv : TimeIcc s t N := ⟨v, hv⟩
  have hR30 : Step2Moment.ratR E s N v ^ (30 : Nat) ≤
      (Gauss.band d).scale E N v := by
    have hm := hMarginN vv
    simpa [vv, Step2Moment.ratR] using hm
  have hScaleN : (Gauss.band d).scale E N v ≤ (N : Real) := by
    obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts (Gauss.band d) hE hs0 ht1 N vv
    have hWL : ((Gauss.band d).W N : Real) * (Gauss.band d).L N ≤ (N : Real) := by
      exact_mod_cast hdim.1
    change ((Gauss.band d).W N : Real) * (Gauss.band d).ell N v * etaT E v ≤ (N : Real)
    calc
      _ ≤ ((Gauss.band d).W N : Real) * (Gauss.band d).L N * 1 := by gcongr
      _ = ((Gauss.band d).W N : Real) * (Gauss.band d).L N := by ring
      _ ≤ (N : Real) := hWL
  have hR28 : 1 ≤ Step2Moment.ratR E s N v ^ (28 : Nat) := one_le_pow₀ hR1
  have hR2nat : Step2Moment.ratR E s N v ^ (2 : Nat) ≤ (N : Real) := by
    calc
      _ ≤ Step2Moment.ratR E s N v ^ (30 : Nat) := by
        rw [show (Step2Moment.ratR E s N v) ^ 30 =
          (Step2Moment.ratR E s N v) ^ 2 * (Step2Moment.ratR E s N v) ^ 28 by ring]
        nlinarith [sq_nonneg (Step2Moment.ratR E s N v)]
      _ ≤ (Gauss.band d).scale E N v := hR30
      _ ≤ (N : Real) := hScaleN
  have hR2 : Step2Moment.ratR E s N v ^ (2 : Real) ≤ (N : Real) := by
    have heq : Step2Moment.ratR E s N v ^ (2 : Real) =
        Step2Moment.ratR E s N v ^ (2 : Nat) := by
      simpa only [Nat.cast_ofNat] using
        (Real.rpow_natCast (Step2Moment.ratR E s N v) 2)
    rw [heq]
    exact hR2nat
  have hRinv : ((N : Real)⁻¹) ≤
      Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
    have hinv := inv_anti₀ (Real.rpow_pos_of_pos hRpos 2) hR2
    have hpowinv : (Step2Moment.ratR E s N v ^ (2 : Real))⁻¹ =
        Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
      rw [Real.rpow_neg hRpos.le]
    have hNinv : ((N : Real)⁻¹) = (N : Real)^(-(1 : Real)) := by
      rw [Real.rpow_neg hNnonneg]
      norm_num
    simpa [hNinv, hpowinv] using hinv
  have hgap := sqrt_gap_le_one_sub_start (hs0 N) hsv (le_of_lt hv1)
  have hEtaGap := eta_start_inv_mul_sqrt_gap_le_inv_im hE (hs0 N) hs1 hsv (le_of_lt hv1)
  have hgoodI := hGoodIntN k hk a
  have hfullI := hFullIntN k hk a
  have hred := hReductionN k hk a
  have hcrossPoint := hBridgeN k hk a
  have hprofilePoint := hMicroN k hk a
  let R : Real := Step2Moment.ratR E s N v
  let etaS : Real := etaT E (s N)
  let α : Real := 13 * δ / 640
  let Cprofile : Real := (15 * (p : Real) / 4) *
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
      (N : Real)^α * etaS⁻¹ * R^(-(2 : Real))
  let Cbad : Real := (15 * (p : Real) / 8) * (N : Real)^(-(1 : Real))
  let Cmajor : Real := Cprofile + Cbad
  let major : Real → Real := fun r => Cmajor / Real.sqrt r
  have hmajorInt : IntervalIntegrable major volume (s N) v := by
    simpa [major] using
      APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
        Cmajor (s N) v (hs0 N) hsv
  have hmajorPoint : ∀ r ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D deltaWeight s t N k p a r ≤ major r := by
    intro r hr
    by_cases hrpos : 0 < r
    · have hbridge := hcrossPoint r hr hrpos
      have hmicro := hprofilePoint r hr hrpos
      have hscaledProfile :
          (15 * (p : Real) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                zetaSrc tauG deltaWeight deltaCap N k a r ≤
            Cprofile / Real.sqrt r := by
        calc
          _ ≤ (15 * (p : Real) / 4) *
              (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : Real)^α * (etaT E (s N))⁻¹ * R^(-(2 : Real)) /
                  Real.sqrt r) := by
            exact mul_le_mul_of_nonneg_left hmicro (by positivity)
          _ = Cprofile / Real.sqrt r := by
            dsimp [Cprofile, α, R]
            ring
      have hscaledBad :
          (15 * (p : Real) / 8) * (N : Real)^(-(1 : Real)) / Real.sqrt r =
            Cbad / Real.sqrt r := by
        dsimp [Cbad]
      calc
        _ ≤ (15 * (p : Real) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                zetaSrc tauG deltaWeight deltaCap N k a r +
            (15 * (p : Real) / 8) * (N : Real)^(-(1 : Real)) / Real.sqrt r := hbridge
        _ ≤ Cprofile / Real.sqrt r + Cbad / Real.sqrt r :=
          add_le_add hscaledProfile (le_of_eq hscaledBad)
        _ = major r := by
          dsimp [major, Cmajor]
          rw [← add_div]
    · have hr0 : r = 0 := le_antisymm (le_of_not_gt hrpos) (hs0 N |>.trans hr.1)
      have hzero :
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a r = 0 := by
        simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate,
          hr0]
      rw [hzero]
      simp [major, hr0]
  have hgoodle := intervalIntegral.integral_mono_on hsv hgoodI hmajorInt hmajorPoint
  have hmajorEval :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      Cmajor (s N) v (hs0 N) hsv
  have hgap0 := hgap.1
  have hgap1 := hgap.2
  have hgoodBound :
      (∫ r in (s N)..v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k p a r) ≤
        (15 * (p : Real) / 2) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
            (mE E).im *
            (N : Real)^α * R^(-(2 : Real)) +
          (15 * (p : Real) / 4) * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ ∫ r in (s N)..v, major r := hgoodle
      _ = 2 * Cmajor * (Real.sqrt v - Real.sqrt (s N)) := hmajorEval
      _ = 2 * (Cprofile + Cbad) * (Real.sqrt v - Real.sqrt (s N)) := by rfl
      _ ≤ 2 * Cprofile * (Real.sqrt v - Real.sqrt (s N)) +
          2 * Cbad * (Real.sqrt v - Real.sqrt (s N)) := le_of_eq (by ring)
      _ ≤ (15 * (p : Real) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
              (mE E).im * (N : Real)^α * R^(-(2 : Real)) +
          (15 * (p : Real) / 4) * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N)) := by
        have hprofCoeff : 0 ≤ (15 * (p : Real) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : Real)^α * R^(-(2 : Real)) := by
          have hK := APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
          have hNα : 0 ≤ (N : Real)^α := Real.rpow_nonneg hNnonneg _
          have hRpow : 0 ≤ R^(-(2 : Real)) := Real.rpow_nonneg hRpos.le _
          positivity
        have hprofTerm : 2 * Cprofile * (Real.sqrt v - Real.sqrt (s N)) ≤
            (15 * (p : Real) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                (mE E).im * (N : Real)^α * R^(-(2 : Real)) := by
          dsimp [Cprofile]
          have he := hEtaGap
          dsimp [etaS, R, α] at he ⊢
          calc
            _ = ((15 * (p : Real) / 2) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : Real)^(13 * δ / 640) *
                ((etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N))) *
                Step2Moment.ratR E s N v^(-(2 : Real))) := by ring
            _ ≤ _ := by
              have hcoef : 0 ≤ (15 * (p : Real) / 2) *
                  APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                    (N : Real)^(13 * δ / 640) := by
                have hK := APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
                have hNα : 0 ≤ (N : Real)^(13 * δ / 640) :=
                  Real.rpow_nonneg hNnonneg _
                positivity
              have hRpow : 0 ≤ (Step2Moment.ratR E s N v)^(-(2 : Real)) :=
                Real.rpow_nonneg hRpos.le _
              calc
                _ = (((15 * (p : Real) / 2) *
                      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                      (N : Real)^(13 * δ / 640)) *
                    ((etaT E (s N))⁻¹ * (Real.sqrt v - Real.sqrt (s N)))) *
                    (Step2Moment.ratR E s N v)^(-(2 : Real)) := by ring
                _ ≤ (((15 * (p : Real) / 2) *
                      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                      (N : Real)^(13 * δ / 640)) * (mE E).im⁻¹) *
                    (Step2Moment.ratR E s N v)^(-(2 : Real)) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left he hcoef) hRpow
                _ = _ := by ring
        have hbadTerm : 2 * Cbad * (Real.sqrt v - Real.sqrt (s N)) =
            (15 * (p : Real) / 4) * (N : Real)^(-(1 : Real)) *
              (Real.sqrt v - Real.sqrt (s N)) := by
          dsimp [Cbad]
          ring
        exact add_le_add hprofTerm (le_of_eq hbadTerm)
      _ = _ := by ring
  have hcrossFinal :
      (∫ r in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a r) ≤
        crossAllOrdersBudgetConst E p * (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
    calc
      _ ≤ (∫ r in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a r) +
          (15 * (p : Real) / 4) * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N)) := hred
      _ ≤ ((15 * (p : Real) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
              (mE E).im * (N : Real)^α * R^(-(2 : Real)) +
          (15 * (p : Real) / 4) * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N))) +
          (15 * (p : Real) / 4) * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N)) := by
        exact add_le_add hgoodBound (le_of_eq rfl)
      _ ≤ ((15 * (p : Real) / 2) *
            (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
              (mE E).im + 1)) *
            (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
        have hconst : 0 ≤ (15 * (p : Real) / 2) := by positivity
        have hNpow0 : 0 ≤ (N : Real)^(δ / 8) := Real.rpow_nonneg hNnonneg _
        have hRpow0 : 0 ≤ R^(-(2 : Real)) := Real.rpow_nonneg hRpos.le _
        have hNpow1 : 1 ≤ (N : Real)^(δ / 8) := Real.one_le_rpow hNreal (by positivity)
        have hRinvN : (N : Real)^(-(1 : Real)) ≤ R^(-(2 : Real)) := by
          have hinv := inv_anti₀ (Real.rpow_pos_of_pos hRpos 2) hR2
          have hpowinv : (R ^ (2 : Real))⁻¹ = R ^ (-(2 : Real)) := by
            rw [Real.rpow_neg hRpos.le]
          have hNinv : (N : Real)⁻¹ = (N : Real)^(-(1 : Real)) := by
            rw [Real.rpow_neg hNnonneg]
            norm_num
          simpa [hNinv, hpowinv] using hinv
        have hprofilePow : (N : Real)^α ≤ (N : Real)^(δ / 8) := hpow
        have hgapBound : 0 ≤ Real.sqrt v - Real.sqrt (s N) := hgap0
        have hpR : 0 < (p : Real) := by exact_mod_cast (lt_of_lt_of_le (by omega) hp)
        have hK : 0 < APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
        have him : 0 < (mE E).im := mE_im_pos hE
        have hprofileCoeff : 0 ≤ (15 * (p : Real) / 2) *
            (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
              (mE E).im) := by positivity
        have hprofileAbsorb :
            (15 * (p : Real) / 2) *
              APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                (mE E).im * (N : Real)^α * R^(-(2 : Real)) ≤
              (15 * (p : Real) / 2) *
                (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                  (mE E).im) *
                (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
          have hRpow : 0 ≤ R^(-(2 : Real)) := Real.rpow_nonneg hRpos.le _
          calc
            _ = ((15 * (p : Real) / 2) *
                (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                  (mE E).im)) * (N : Real)^α * R^(-(2 : Real)) := by ring
            _ ≤ ((15 * (p : Real) / 2) *
                (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                  (mE E).im)) * (N : Real)^(δ / 8) * R^(-(2 : Real)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hprofilePow hprofileCoeff) hRpow
            _ = _ := by ring
        have hpaymentAbsorb :
            (15 * (p : Real) / 2) * (N : Real)^(-(1 : Real)) *
              (Real.sqrt v - Real.sqrt (s N)) ≤
            (15 * (p : Real) / 2) * (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
          have hsmall : (N : Real)^(-(1 : Real)) *
              (Real.sqrt v - Real.sqrt (s N)) ≤
              (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
            have hgaple1 : Real.sqrt v - Real.sqrt (s N) ≤ 1 := by
              linarith [hgap1, hs0 N]
            calc
              _ ≤ (N : Real)^(-(1 : Real)) := by
                exact mul_le_of_le_one_right (Real.rpow_nonneg hNnonneg _) hgaple1
              _ ≤ R^(-(2 : Real)) := hRinvN
              _ ≤ (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
                calc
                  _ = 1 * R^(-(2 : Real)) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_right hNpow1 hRpow0
          calc
            _ = (15 * (p : Real) / 2) *
                ((N : Real)^(-(1 : Real)) *
                  (Real.sqrt v - Real.sqrt (s N))) := by ring
            _ ≤ (15 * (p : Real) / 2) *
                ((N : Real)^(δ / 8) * R^(-(2 : Real))) :=
              mul_le_mul_of_nonneg_left hsmall hconst
            _ = _ := by ring
        have hsum :
            (15 * (p : Real) / 2) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                  (mE E).im * (N : Real)^α * R^(-(2 : Real)) +
              (15 * (p : Real) / 2) * (N : Real)^(-(1 : Real)) *
                (Real.sqrt v - Real.sqrt (s N)) ≤
            (15 * (p : Real) / 2) *
                (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
                  (mE E).im) *
                (N : Real)^(δ / 8) * R^(-(2 : Real)) +
              (15 * (p : Real) / 2) *
                (N : Real)^(δ / 8) * R^(-(2 : Real)) :=
          add_le_add hprofileAbsorb hpaymentAbsorb
        convert hsum using 1 <;> ring
      _ = crossAllOrdersBudgetConst E p * (N : Real)^(δ / 8) * R^(-(2 : Real)) := by
        rw [crossAllOrdersBudgetConst]
  exact ⟨hfullI, hcrossFinal⟩

/-- The T995 same-event resident with positive actual smooth weight is
retained unchanged, giving a nondegenerate model for the combined theorem. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingActualDriftStrictExponent.nondegenerate_positive_cell_witness

/-- T1207's stronger active `k=2` transition witness, retained as a witness
for the full positive-time cross-budget input. -/
noncomputable abbrev nondegenerate_active_k2_cross_witness :=
  APrimeGeneralMovingCrossBudgetGoodIntegralReduction.nondegenerate_active_k2_witness

/-- T1263's actual-smooth `g` integral and the unrestricted full cross
integral share one eventual cutoff. The result keeps the exact endpoint
factor `R_v^(-2)` and the strict exponent `δ/8`. -/
theorem eventually_integral_actual_smooth_g_add_full_cross_le_delta_eighth
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        IntervalIntegrable
          (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            p N k a)
          volume (s N) v ∧
        IntervalIntegrable
          (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a)
          volume (s N) v ∧
        (∫ r in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            p N k a r) +
        (∫ r in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a r) ≤
          ((12 / (mE E).im + 2) +
            crossAllOrdersBudgetConst E p) *
            (N : Real)^(δ / 8) *
            Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  have hDrift := _root_.RBM.APrimeGeneralMovingActualDriftStrictExponent.eventually_actual_smooth_g_integral_le_delta_eighth
        hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hCross := eventually_integral_positiveTimeCrossBudget_le_delta_eighth
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  filter_upwards [hDrift, hCross] with N hDriftN hCrossN
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hd := hDriftN k hk a
  have hc' := hCrossN k hk a
  rcases hd with ⟨hgi, hg⟩
  rcases hc' with ⟨hci, hcross⟩
  have hgi' :
      IntervalIntegrable
        (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a)
        volume (s N) v := by
    simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hgi
  have hg' :
      (∫ r in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t deltaWeight p N k a r) ≤
        (12 / (mE E).im + 2) * (N : Real)^(δ / 8) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
    simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hg
  refine ⟨hgi', hci, ?_⟩
  have hsum := add_le_add hg' hcross
  calc
    _ ≤ (12 / (mE E).im + 2) * (N : Real)^(δ / 8) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) +
        crossAllOrdersBudgetConst E p * (N : Real)^(δ / 8) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) := hsum
    _ = ((12 / (mE E).im + 2) + crossAllOrdersBudgetConst E p) *
        (N : Real)^(δ / 8) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) := by ring

#print axioms crossAllOrdersBudgetConst_pos
#print axioms eventually_integral_positiveTimeCrossBudget_le_delta_eighth
#print axioms nondegenerate_positive_cell_witness
#print axioms nondegenerate_active_k2_cross_witness
#print axioms eventually_integral_actual_smooth_g_add_full_cross_le_delta_eighth

end
end RBM.APrimeGeneralMovingDriftCrossAllOrdersStrictExponent
