/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingFullDriftProfileSlotRepair
import RBM1D.Gauss.APrimeGeneralMovingDriftErrorSlot
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1061: actual weighted-drift integral at fixed `D = 60`

This module combines the T615 actual-smooth `g` integral inequality with the
accepted full-profile slot and the `β = 1` complement payment, using T995's
single loss schedule.  The conclusion is a local actual-drift slot only.
-/

namespace RBM.APrimeGeneralMovingActualDriftSlot60

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open APrimeGeneralMovingSmoothDriftNormBudget

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The T995 same-resident witness for a nondegenerate actual-smooth window. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- At fixed `D = 60`, T615's literal actual weighted-`g` integral fits the
T995 small slot after adding the deterministic profile budget and its
`β = 1` common-event complement payment.  The cutoff is common to every
active cell and output coordinate; `k = 0` is included. -/
theorem eventually_actual_weighted_g_integral_le_small_slot
    {E c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ)
    (hδsmall : δ ≤ min 1 (c / 100))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N →
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (APrimeGeneralMovingSmoothDriftNormBudget.g E 60 s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a)
          volume (s N)
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k) ∧
        (∫ u in (s N)..
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k),
          APrimeGeneralMovingSmoothDriftNormBudget.g E 60 s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
          (11 / (mE E).im + 3) * (N : Real) ^ (5 * δ / 32) *
            (Step2Moment.ratR E s N
              (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
              (-2 : Real) := by
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hroom with ⟨hdw, hxi, hcap, htau, hsrc, hctr, hbuffer,
    _hsrcTau, _htauCap, _hcapC, _hcapRoom, _hsrcPower, _hsrcCtrPower⟩
  have hdeltaCap :
      APrimeGeneralMovingSmoothDriftNormBudget.deltaCap
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (APrimeGeneralMovingSlotLossSchedule.xi δ) =
        APrimeGeneralMovingSlotLossSchedule.deltaCap δ := by
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.deltaCap] using hbuffer
  have hT615 :=
    eventually_actual_smooth_drift_integral_le_exact_profile
      (D := 60) hE (by norm_num) hs0 hst ht1 hc hreg hB
      hsrc hctr htau hdw hxi
      p hp 1 (by norm_num)
  have hProfile :=
    APrimeGeneralMovingFullDriftProfileSlotRepair.eventually_full_profile_integral_le_small_slot
      (E := E) (D := 60) hE (by norm_num) hs0 hst ht1 hc hreg hδ hδsmall
  have hPayment :=
    APrimeGeneralMovingDriftErrorSlot.eventually_complement_payment_le_small_slot
      (E := E) (c := c) (δ := δ) (s := s) (t := t)
      hE hs0 hst ht1 hc hreg hδ hδsmall
  filter_upwards [hT615, hProfile, hPayment] with N hT615N hProfileN hPaymentN
  intro k hk a
  obtain ⟨hgi, _hprofilei, hactual⟩ := hT615N k hk a
  rw [hdeltaCap] at hactual
  have hprofile := hProfileN k hk
  have hpayment := hPaymentN k hk
  simpa only [APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
    (show
      IntervalIntegrable
          (APrimeGeneralMovingSmoothDriftNormBudget.g E 60 s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a)
          volume (s N)
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k) ∧
        (∫ u in (s N)..
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k),
          APrimeGeneralMovingSmoothDriftNormBudget.g E 60 s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
          (11 / (mE E).im + 3) * (N : Real) ^ (5 * δ / 32) *
            (Step2Moment.ratR E s N
              (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
              (-2 : Real) from by
      refine ⟨hgi, ?_⟩
      have hprofile' :
          (∫ u in (s N)..
              (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k),
            APrimeGeneralMovingSmoothDriftNormBudget.profile E 60 s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N
              (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k) u) ≤
            (11 / (mE E).im + 2) * (N : Real) ^ (5 * δ / 32) *
              (Step2Moment.ratR E s N
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
                (-2 : Real) := by
        simpa only [APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hprofile
      have hpayment' :
          (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k - s N) *
              (N : Real) ^ (-1 : Real) ≤
            (N : Real) ^ (5 * δ / 32) *
              (Step2Moment.ratR E s N
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
                (-2 : Real) := by
        simpa only [APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hpayment
      calc
        _ ≤
            (∫ u in (s N)..
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k),
              APrimeGeneralMovingSmoothDriftNormBudget.profile E 60 s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k) u) +
              (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k - s N) *
                (N : Real) ^ (-1 : Real) := hactual
        _ ≤
            (11 / (mE E).im + 2) * (N : Real) ^ (5 * δ / 32) *
                (Step2Moment.ratR E s N
                  (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
                  (-2 : Real) +
              (N : Real) ^ (5 * δ / 32) *
                (Step2Moment.ratR E s N
                  (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
                  (-2 : Real) :=
          add_le_add hprofile' hpayment'
        _ = (11 / (mE E).im + 3) * (N : Real) ^ (5 * δ / 32) *
              (Step2Moment.ratR E s N
                (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
                (-2 : Real) := by ring)

#print axioms eventually_actual_weighted_g_integral_le_small_slot
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingActualDriftSlot60
