/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingInitialActualSmoothSlot
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVSlot

/-!
# T1031: joint actual-smooth initial and QV slots

This module places the accepted initial hinit and QV N2 estimates under one
fixed moment order, actual smooth weight, loss schedule, active-cell cutoff,
and endpoint. It makes no drift/cross, family, or full A-prime claim.
-/

namespace RBM.APrimeGeneralMovingInitialQVJointSlots

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The exact T1019 initial hinit estimate and T1011 QV N2 estimate hold
simultaneously at the same target-mesh endpoint, actual smooth weight,
δ-dependent T995 schedule, and fixed `p`, uniformly over all active cells
and output coordinates. -/
theorem eventually_joint_actual_smooth_initial_qv_slots
    {E D c δ : Real} {s t : Nat → Real} {p : Nat}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hsmall : δ ≤ min 1 (c / 100)) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        MomentDuhamel.momNormW (P d)
          (APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k) p
          (APrimeAssembly.initialEvolvedNormAt (sample d) E D s N
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k) a) ≤
        APrimeOneStep.initTerm ((N : Real) ^ (δ / 8))
          (etaT E (s N) /
            etaT E (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k))
          (APrimeInit.slotXi' ((N : Real) ^ (δ / 8))) /
          (etaT E (s N) /
            etaT E (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k)) ^ (4 : Nat) ∧
        Real.sqrt ((2 * (p : Real) - 1) *
          (∫ u in s N..APrimeGeneralMovingActualSmoothQVNormBudget.endpoint
              s t D N k,
            APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u)) ≤
          APrimeOneStep.tailTerm ((N : Real) ^ (δ / 8))
            (Step2Moment.ratR E s N
              (APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t D N k))
            (APrimeInit.slotKappa' ((N : Real) ^ (δ / 8))) /
            (Step2Moment.ratR E s N
              (APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t D N k)) ^ (4 : Nat) := by
  have hinit := APrimeGeneralMovingInitialActualSmoothSlot.eventually_actual_smooth_initial_hinit
    hE hD hs0 hst ht1 hc hreg hB hδ p hp
    (δWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
  have hqv := APrimeGeneralMovingActualSmoothQVSlot.eventually_actual_smooth_qv_N2_slot
    hE hD hs0 hst ht1 hc hreg hB hδ hsmall hp
  filter_upwards [hinit, hqv] with N hinitN hqvN
  intro k hk a
  have hi := hinitN k hk a
  have hq := hqvN k hk a
  refine ⟨?_, ?_⟩
  · simpa [APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hi
  · simpa [APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingQVNormBudget.endpoint] using hq

/-- One T995 same-resident positive-cell witness also carries the joint
uniform initial/QV slot conclusions, at `p = 1` and the same scheduled `δ`. -/
theorem scheduled_positive_cell_joint_slots_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (Gauss.sample d) 0 s ∧
      ∃ δ : Real, 0 < δ ∧ δ ≤ min 1 (c / 100) ∧
        ∀ᶠ N : Nat in atTop,
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            0 < APrimeGeneralMovingSmoothDriftNormBudget.weight
              0 60 s t (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              1 N 1 ω ∧
            (∀ k : Nat,
              k ≤ cutNetTop s t
                (APrimeGeneralMovingMesh.targetMesh 60) N →
              ∀ a : LoopArg (d.L N) 2,
                MomentDuhamel.momNormW (P d)
                  (APrimeGeneralMovingSmoothDriftNormBudget.weight 0 60 s t
                    (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k) 1
                  (APrimeAssembly.initialEvolvedNormAt (sample d) 0 60 s N
                    (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k) a) ≤
                APrimeOneStep.initTerm ((N : Real) ^ (δ / 8))
                  (etaT 0 (s N) /
                    etaT 0 (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k))
                  (APrimeInit.slotXi' ((N : Real) ^ (δ / 8))) /
                  (etaT 0 (s N) /
                    etaT 0 (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k)) ^
                    (4 : Nat) ∧
                Real.sqrt ((2 * (1 : Real) - 1) *
                  (∫ u in s N..APrimeGeneralMovingActualSmoothQVNormBudget.endpoint
                      s t 60 N k,
                    APrimeGeneralMovingActualSmoothQVNormBudget.g 0 60 s t
                      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N k a u)) ≤
                  APrimeOneStep.tailTerm ((N : Real) ^ (δ / 8))
                    (Step2Moment.ratR 0 s N
                      (APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t 60 N k))
                    (APrimeInit.slotKappa' ((N : Real) ^ (δ / 8))) /
                    (Step2Moment.ratR 0 s N
                      (APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t 60 N k)) ^ (4 : Nat)) := by
  rcases APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness with
    ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, _hStep, hw⟩
  let δ : Real := min 1 (c / 100) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ ≤ min 1 (c / 100) := by
    dsimp [δ]
    have hmin : 0 ≤ min 1 (c / 100) := by positivity
    linarith
  have hpos := hw δ hδ hsmall
  have hslots := eventually_joint_actual_smooth_initial_qv_slots
    (E := 0) (D := 60) (c := c) (δ := δ) (s := s) (t := t) (p := 1)
    (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB hδ hsmall (by norm_num)
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, δ, hδ, hsmall, ?_⟩
  filter_upwards [hpos, hslots] with N hposN hslotsN
  obtain ⟨_hlen, ω, hω, hk, _hwide, hweight⟩ := hposN
  have hweight' :
      0 < APrimeGeneralMovingSmoothDriftNormBudget.weight
        0 60 s t (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 ω := by
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.weight,
      APrimeGeneralMovingSlotLossSchedule.deltaWeight] using hweight
  exact ⟨ω, hω, hk, hweight', by simpa using hslotsN⟩

#print axioms eventually_joint_actual_smooth_initial_qv_slots
#print axioms scheduled_positive_cell_joint_slots_witness

end
end RBM.APrimeGeneralMovingInitialQVJointSlots
