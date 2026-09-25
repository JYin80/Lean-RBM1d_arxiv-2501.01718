/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingFullDriftStrictExponent
import RBM1D.Gauss.APrimeGeneralMovingDriftErrorAnyD
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-! # T1263: strict exponent for the exact actual-smooth drift integral

This is the local smooth-prefix replacement obtained by combining T615's
actual weighted drift integral with the exact deterministic profile bound.
It is not the paper's stopped-process estimate. -/

namespace RBM.APrimeGeneralMovingActualDriftStrictExponent

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open APrimeGeneralMovingSmoothDriftNormBudget

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

private theorem complement_payment_strict
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hreg : Cond272Reg (band d) E s t c)
    (hδ : 0 < δ)
    : ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      (endpoint s t D N k - s N) * (N : Real) ^ (-1 : Real) ≤
        (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real) := by
  have hmargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hmargin, (band d).dim, eventually_ge_atTop 1] with N hmarginN hdim hN
  intro k hk
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) := by
    simpa only [endpoint] using
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  let v := endpoint s t D N k
  have hvIcc : v ∈ Icc (s N) (t N) := hv
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hvIcc.1.trans_lt (hvIcc.2.trans_lt (ht1 N)))
      (hvIcc.2.trans_lt (ht1 N))
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hvIcc.1 (hvIcc.2.trans_lt (ht1 N))
  have hR30 : (Step2Moment.ratR E s N v) ^ (30 : Nat) ≤ (band d).scale E N v := by
    have hh := hmarginN ⟨v, hvIcc⟩
    simpa only [Step2Moment.ratR] using hh
  have hscaleN : (band d).scale E N v ≤ (N : Real) := by
    obtain ⟨_, _, heta1, _, hellL⟩ := EEBridge.eeFacts (band d) hE hs0 ht1 N ⟨v, hvIcc⟩
    change ((band d).W N : Real) * (band d).ell N v * etaT E v ≤ (N : Real)
    have hWL : ((band d).W N : Real) * (band d).L N ≤ (N : Real) := by
      exact_mod_cast hdim.1
    calc
      _ ≤ ((band d).W N : Real) * (band d).L N * 1 := by gcongr
      _ = ((band d).W N : Real) * (band d).L N := by ring
      _ ≤ (N : Real) := hWL
  have hR28 : 1 ≤ (Step2Moment.ratR E s N v) ^ (28 : Nat) := one_le_pow₀ hR1
  have hR2nat : (Step2Moment.ratR E s N v) ^ (2 : Nat) ≤ (N : Real) := by
    calc
      _ ≤ (Step2Moment.ratR E s N v) ^ 30 := by
        rw [show (Step2Moment.ratR E s N v) ^ 30 =
          (Step2Moment.ratR E s N v) ^ 2 * (Step2Moment.ratR E s N v) ^ 28 by ring]
        nlinarith [sq_nonneg (Step2Moment.ratR E s N v)]
      _ ≤ (band d).scale E N v := hR30
      _ ≤ (N : Real) := hscaleN
  have hR2 : (Step2Moment.ratR E s N v) ^ (2 : Real) ≤ (N : Real) := by
    have heq : (Step2Moment.ratR E s N v) ^ (2 : Real) =
        (Step2Moment.ratR E s N v) ^ (2 : Nat) := by
      simpa only [Nat.cast_ofNat] using
        (Real.rpow_natCast (Step2Moment.ratR E s N v) 2)
    rw [heq]
    exact hR2nat
  have hlen : v - s N ≤ 1 := by linarith [hvIcc.1, hvIcc.2, hs0 N, ht1 N]
  have hcross : (v - s N) * Step2Moment.ratR E s N v ^ (2 : Real) ≤ (N : Real) :=
    calc
      _ ≤ 1 * Step2Moment.ratR E s N v ^ (2 : Real) :=
        mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hRpos.le _)
      _ ≤ (N : Real) := by simpa using hR2
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hR2pos : 0 < Step2Moment.ratR E s N v ^ (2 : Real) := Real.rpow_pos_of_pos hRpos _
  have hdiv : (v - s N) / (N : Real) ≤
      1 / (Step2Moment.ratR E s N v ^ (2 : Real)) :=
    (div_le_div_iff₀ hNpos hR2pos).2 (by simpa [mul_comm] using hcross)
  have hNinv : (N : Real)⁻¹ = (N : Real) ^ (-1 : Real) := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_one]
  have hRinv : (Step2Moment.ratR E s N v ^ (2 : Real))⁻¹ =
      Step2Moment.ratR E s N v ^ (-2 : Real) := by rw [Real.rpow_neg hRpos.le]
  have hweak : (v - s N) * (N : Real) ^ (-1 : Real) ≤
      Step2Moment.ratR E s N v ^ (-2 : Real) := by
    simpa [div_eq_mul_inv, hNinv, hRinv, v] using hdiv
  have hpow : (1 : Real) ≤ (N : Real) ^ (δ / 8) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hfinal : (v - s N) * (N : Real) ^ (-1 : Real) ≤
      (N : Real) ^ (δ / 8) *
        Step2Moment.ratR E s N v ^ (-2 : Real) := by
    calc
      _ ≤ Step2Moment.ratR E s N v ^ (-2 : Real) := hweak
      _ = 1 * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hRpos.le _)
  simpa [v] using hfinal

/-- The T995 same-event nondegenerate witness is retained unchanged. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingDriftErrorAnyD.scheduled_positive_cell_witness

/-- T615's literal actual-smooth weighted-`g` integral, sharpened to the
strict `δ/8` exponent using the full exact-profile estimate. The cutoff is
chosen before all active cells and output coordinates, including `k = 0`.
-/
theorem eventually_actual_smooth_g_integral_le_delta_eighth
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg ((d.L) N) 2,
        IntervalIntegrable
          (g E D s t (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            p N k a) volume (s N) (endpoint s t D N k) ∧
        (∫ u in (s N)..(endpoint s t D N k),
          g E D s t (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            p N k a u) ≤
          (12 / (mE E).im + 2) * (N : Real) ^ (δ / 8) *
            Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real) := by
  have hsched :=
    APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hsched with ⟨hdw, hxi, _hcap, htau, hsrc, hctr, hbuffer,
    _hsrcTau, _htauCap, _hcapC, _hcapRoom, _hsrcPower, _hsrcCtrPower⟩
  have hT615 := eventually_actual_smooth_drift_integral_le_exact_profile
    hE hD hs0 hst ht1 hc hreg hB hsrc hctr htau hdw hxi p hp 1 (by norm_num)
  have hProfile :=
    APrimeGeneralMovingFullDriftStrictExponent.eventually_full_profile_integral_le_delta_eighth
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hPayment := complement_payment_strict (D := D) (δ := δ)
    hE hs0 hst ht1 hreg hδ
  filter_upwards [hT615, hProfile, hPayment, eventually_ge_atTop 1] with
    N hT615N hProfileN hPaymentN hN
  intro k hk a
  obtain ⟨hgi, _hprofilei, hactual⟩ := hT615N k hk a
  simp only [APrimeGeneralMovingSmoothDriftNormBudget.deltaCap] at hactual
  rw [hbuffer] at hactual
  have hprof := hProfileN k hk
  have hRpos : 0 < Step2Moment.ratR E s N (endpoint s t D N k) := by
    have hv := MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
    exact Step2Moment.ratR_pos hE (hv.1.trans_lt (hv.2.trans_lt (ht1 N)))
      (hv.2.trans_lt (ht1 N))
  have hRinv : 0 < Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real) :=
    Real.rpow_pos_of_pos hRpos _
  have hpay' := hPaymentN k hk
  have hprof' :
      (∫ u in (s N)..(endpoint s t D N k),
        profile E D s t (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N
          (endpoint s t D N k) u) ≤
        (12 / (mE E).im + 1) * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real) := by
    simpa only [APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hprof
  refine ⟨hgi, ?_⟩
  calc
    _ ≤ (∫ u in (s N)..(endpoint s t D N k),
        profile E D s t (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N
          (endpoint s t D N k) u) +
        (endpoint s t D N k - s N) * (N : Real) ^ (-1 : Real) := hactual
    _ ≤ ((12 / (mE E).im + 1) * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real)) +
        (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real) :=
      add_le_add hprof' hpay'
    _ = (12 / (mE E).im + 2) * (N : Real) ^ (δ / 8) *
          Step2Moment.ratR E s N (endpoint s t D N k) ^ (-2 : Real) := by ring

#print axioms eventually_actual_smooth_g_integral_le_delta_eighth
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingActualDriftStrictExponent
