/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualDriftSlotAnyD
import RBM1D.Gauss.APrimeGeneralMovingCrossProfileSlot

/-!
# T1147: joint actual-drift and favorable-cross integral slot

This file adds the two already-proved integral estimates under their common
T995 loss schedule.  The cross term is the deterministic favorable profile,
not the actual cross budget.
-/

namespace RBM.APrimeGeneralMovingDriftCrossProfileJointSlot

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- T995's explicit nondegenerate same-resident positive-cell context. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- Under the T995 schedule, the actual weighted-drift integral and the
deterministic favorable-cross-profile integral have the stated common bound.
The actual-drift term is integrable; no actual-cross budget is asserted. -/
theorem eventually_actual_drift_add_favorable_cross_integral_le
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        IntervalIntegrable
          (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a)
          volume (s N) v ∧
        (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) +
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) ≤
          (11 / (mE E).im + 3 +
            APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E) *
            (N : Real) ^ (5 * δ / 32) *
              Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
  have hActual :=
    APrimeGeneralMovingActualDriftSlotAnyD.eventually_actual_weighted_g_integral_le_small_slot_anyD
      hE hD hs0 hst ht1 hc hreg hB
      hδ hδsmall p hp
  have hCross :=
    APrimeGeneralMovingCrossProfileSlot.eventually_integral_crossProfile_le_small_slot
      hE (le_trans (by norm_num : (0 : Real) ≤ 60) hD) hs0 hst ht1 hc hreg
      hδ hδsmall
  filter_upwards [hActual, hCross] with N hActualN hCrossN
  intro k hk a
  obtain ⟨hInt, hDrift⟩ := hActualN k hk a
  have hCrossBound := hCrossN k hk a
  dsimp
  have hSum :
      (∫ u in (s N)..cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) +
      (∫ u in (s N)..cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k,
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) ≤
      ((11 / (mE E).im + 3) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ^ (-(2 : Real))) +
        APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ^ (-(2 : Real)) :=
    add_le_add hDrift hCrossBound
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ((11 / (mE E).im + 3) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ^ (-(2 : Real))) +
        APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ^ (-(2 : Real)) := hSum
    _ = (11 / (mE E).im + 3 +
          APrimeGeneralMovingCrossProfileSlot.crossProfileBudgetConst E) *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ^ (-(2 : Real)) := by ring

#print axioms eventually_actual_drift_add_favorable_cross_integral_le
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingDriftCrossProfileJointSlot
