/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget

/-!
# T1019: the general-moving initial slot for T615's actual smooth weight

The paper's (5.39) is the propagator estimate for `U_{s,t} ∘ (L-K)_s`;
it is not an initial-moment formula. This module transfers the exact T488
initial slot to T615's literal smooth weight. The transfer uses only the
pointwise bound `0 ≤ weight ≤ 1`: one unweighted T488 cutoff works for every
active cell and output coordinate at once, after which weighted moment
monotonicity applies without choosing a new eventual cutoff for each cell.

This is a smooth-weight initial-slot result. It proves no drift or cross
estimate and makes no claim to replace paper (5.39).
-/

namespace RBM.APrimeGeneralMovingInitialActualSmoothSlot

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The exact T488 initial slot for T615's literal actual smooth weight,
uniformly over every active target-net cell and every two-loop output
coordinate. The slot exponent and actual-weight exponent are fixed before
the eventual quantifier in `N`. -/
theorem eventually_actual_smooth_initial_hinit
    {E D c δ δWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ) (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        MomentDuhamel.momNormW (P d)
          (APrimeGeneralMovingSmoothDriftNormBudget.weight
            E D s t δWeight p N k) p
          (APrimeAssembly.initialEvolvedNormAt (sample d) E D s N
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k) a) ≤
        APrimeOneStep.initTerm ((N : Real) ^ (δ / 8))
          (etaT E (s N) /
            etaT E (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k))
          (APrimeInit.slotXi' ((N : Real) ^ (δ / 8))) /
          (etaT E (s N) /
            etaT E (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k)) ^ 4 := by
  let W : ∀ N, (TimeIcc s t N × LoopArg (d.L N) 2) → Ω d → Real :=
    fun _ _ _ => 1
  have hWm : ∀ N va, AEStronglyMeasurable (W N va) (P d) := by
    intro N va
    exact (measurable_const : Measurable (fun _ : Ω d => (1 : Real))).aestronglyMeasurable
  have hW0 : ∀ N va ω, 0 ≤ W N va ω := by simp [W]
  have hW1 : ∀ N va ω, W N va ω ≤ 1 := by simp [W]
  have hunweighted := APrimeGeneralMovingInitialHinit.eventually_initial_hinit
    hE hD hs0 hst ht1 hc hreg hB hδ p hp W hWm hW0 hW1
  filter_upwards [hunweighted, eventually_ge_atTop 1] with N hN hN1
  intro k hk a
  have hactive := MomentDuhamelCut.netFinset_subset_Icc (hst N)
    (APrimeGeneralMovingMesh.targetMesh_pos D N) _
    (cutNetPt_mem_netFinset hk)
  let v : TimeIcc s t N := ⟨
    APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k, hactive⟩
  have hYint : Integrable
      (fun ω => |APrimeAssembly.initialEvolvedNormAt
        (sample d) E D s N v a ω| ^ (2 * p)) (P d) :=
    APrimeAssembly.integrable_initialEvolvedNormAt_pow_gauss
      d hE hs0 hst ht1 p N v D a
  have hmono := APrimeFirstCellInitialMomentBudget.momNormW_le_one_weight
    (P d)
    (APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t δWeight p N k)
    (APrimeAssembly.initialEvolvedNormAt (sample d) E D s N v a) p
    (fun ω => APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t δWeight p N k ω)
    (fun ω => APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one
      E D s t δWeight p N k ω)
    hYint
  have hunweightedAt := hN ⟨v, a⟩
  have hbound := hmono.trans (by simpa [W, B] using hunweightedAt)
  simpa [v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hbound

/-- T995 supplies a genuine same-event positive first cell on which the
actual T615 smooth weight is positive, together with the uniformly valid
initial slot for every active cell and output coordinate. -/
theorem scheduled_positive_cell_initial_hinit_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (sample d) 0 s ∧
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
                  (APrimeGeneralMovingSmoothDriftNormBudget.weight
                    0 60 s t (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                    1 N k) 1
                  (APrimeAssembly.initialEvolvedNormAt (sample d) 0 60 s N
                    (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k) a) ≤
                APrimeOneStep.initTerm ((N : Real) ^ (δ / 8))
                  (etaT 0 (s N) /
                    etaT 0 (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k))
                  (APrimeInit.slotXi' ((N : Real) ^ (δ / 8))) /
                  (etaT 0 (s N) /
                    etaT 0
                      (APrimeGeneralMovingSmoothDriftNormBudget.endpoint
                        s t 60 N k)) ^ 4) := by
  rcases APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness with
    ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, _hStep, hw⟩
  let δ : Real := min 1 (c / 100) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ ≤ min 1 (c / 100) := by
    dsimp [δ]
    have hmin : 0 ≤ min 1 (c / 100) := by positivity
    linarith
  have hpositive := hw δ hδ hsmall
  have hslot := eventually_actual_smooth_initial_hinit
    (E := 0) (D := 60) (c := c) (δ := δ)
    (δWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
    (s := s) (t := t) (by norm_num) (by norm_num)
    hs0 hst ht1 hc hreg hB hδ 1 (by norm_num)
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, δ, hδ, hsmall, ?_⟩
  filter_upwards [hpositive, hslot] with N hpos hslotN
  obtain ⟨_hlen, ω, hω, hk, _hwide, hweight⟩ := hpos
  have hweight' :
      0 < APrimeGeneralMovingSmoothDriftNormBudget.weight
        0 60 s t (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        1 N 1 ω := by
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.weight,
      APrimeGeneralMovingSlotLossSchedule.deltaWeight] using hweight
  exact ⟨ω, hω, hk, hweight', hslotN⟩

#print axioms eventually_actual_smooth_initial_hinit
#print axioms scheduled_positive_cell_initial_hinit_witness

end
end RBM.APrimeGeneralMovingInitialActualSmoothSlot
