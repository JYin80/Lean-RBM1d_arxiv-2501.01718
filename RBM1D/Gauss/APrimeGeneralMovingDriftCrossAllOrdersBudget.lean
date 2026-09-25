/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualDriftSlotAnyD
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetAllOrdersSlot
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetTimeIntegrable

/-!
# T1229: combined actual weighted-drift and full cross budget at every fixed p

This composes the accepted T1073 actual weighted-drift slot with the accepted
T1227 all-fixed-order full cross-budget slot. T1123 supplies interval
integrability of that same literal cross budget. The result is only the stated
combined smooth-prefix integral slot.
-/

namespace RBM.APrimeGeneralMovingDriftCrossAllOrdersBudget

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- Under T995's shared loss schedule, for each fixed `p ≥ 1` the sum of the
literal actual-smooth weighted drift and literal positive-time full cross
budgets has the desired small-slot integral bound. One eventual cutoff works
for every active target-mesh cell and output coordinate, including the zero
prefix. -/
theorem eventually_integral_drift_add_cross_allOrders_le_small_slot
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          2 * (∫ u in (s N)..v,
            APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              p N k a u +
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k p a u) ≤
            C * (N : ℝ) ^ (5 * δ / 32) *
              Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := by
  have hDrift :=
    APrimeGeneralMovingActualDriftSlotAnyD.eventually_actual_weighted_g_integral_le_small_slot_anyD
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hCross :=
    APrimeGeneralMovingCrossBudgetAllOrdersSlot.eventually_integral_positiveTimeCrossBudget_allOrders_le_small_slot
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  obtain ⟨Ccross, hCcross, hCross⟩ := hCross
  have hCrossInt :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg
      (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (by dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]; positivity)
      p hp
  let q : ℝ := 11 / (mE E).im + 3
  let C : ℝ := 2 * (|q| + Ccross + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hDrift, hCross, hCrossInt] with N hDriftN hCrossN hCrossIntN
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hDcell := hDriftN k hk a
  have hDint : IntervalIntegrable
      (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a)
      volume (s N) v := by
    simpa [v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hDcell.1
  have hDbound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
        q * (N : ℝ) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := by
    simpa [q, v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hDcell.2
  have hCbound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u) ≤
        Ccross * (N : ℝ) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := by
    simpa [mesh, v] using hCrossN k hk a
  have hCint : IntervalIntegrable
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t N k p a)
      volume (s N) v := by
    simpa [mesh, v] using hCrossIntN k hk a
  have hTarget : 0 ≤
      (N : ℝ) ^ (5 * δ / 32) *
        Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := by
    have hv : v ∈ Icc (s N) (t N) :=
      APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
    have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
    have hRpos : 0 < Step2Moment.ratR E s N v :=
      Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
    apply mul_nonneg
    · exact Real.rpow_nonneg (by positivity) _
    · exact Real.rpow_nonneg hRpos.le _
  let T : ℝ := (N : ℝ) ^ (5 * δ / 32) *
    Step2Moment.ratR E s N v ^ (-(2 : ℝ))
  have hDnorm :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
        q * T := by
    calc
      _ ≤ q * (N : ℝ) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := hDbound
      _ = q * T := by dsimp [T]; ring
  have hCnorm :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u) ≤ Ccross * T := by
    calc
      _ ≤ Ccross * (N : ℝ) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := hCbound
      _ = Ccross * T := by dsimp [T]; ring
  have hsum :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) +
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u) ≤
        (|q| + Ccross + 1) * T := by
    calc
      _ ≤ q * T + Ccross * T := add_le_add hDnorm hCnorm
      _ ≤ (|q| + Ccross + 1) * T := by
        have hq : q ≤ |q| + 1 := by
          have hqabs : q ≤ |q| := le_abs_self q
          linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hq) hTarget]
  calc
    2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u) =
        2 * ((∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) +
          (∫ u in (s N)..v,
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a u)) := by
      rw [intervalIntegral.integral_add hDint hCint]
    _ ≤ 2 * ((|q| + Ccross + 1) * T) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = C * (N : ℝ) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : ℝ)) := by
      dsimp [C]
      ring

end
end RBM.APrimeGeneralMovingDriftCrossAllOrdersBudget

#print axioms RBM.APrimeGeneralMovingDriftCrossAllOrdersBudget.eventually_integral_drift_add_cross_allOrders_le_small_slot
