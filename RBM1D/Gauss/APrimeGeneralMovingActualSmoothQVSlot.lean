/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingQVSlotFit

/-!
# T1011: actual-smooth weighted QV in the general-moving N2 slot

For a fixed small-slot exponent and moment order, compose T993's actual
smooth-weight integral comparison (with the exact `β = 1` complement) and
T997's deterministic N2 fit. The same literal smooth weight, active cells,
output coordinates, and eventual `N` are retained throughout.
-/

namespace RBM.APrimeGeneralMovingActualSmoothQVSlot

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The actual-smooth weighted QV integral occupies the T997 N2 slot,
under the same `BoundsCore` premise used by the actual-smooth producer. -/
theorem eventually_actual_smooth_qv_N2_slot
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
        let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
        let R := Step2Moment.ratR E s N v
        let x := (N : Real) ^ (δ / 8)
        Real.sqrt ((2 * (p : Real) - 1) *
          (∫ u in s N..v,
            RBM.APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u)) ≤
          APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hsmall
  rcases hroom with
    ⟨hweight, hxi, hcap, htau, hzetaSrc, hzetaCtr, hbuffer,
      hzetaTau, htauCap, hcapC, hcapRoom, _, _⟩
  have hxiPos : 0 < APrimeGeneralMovingSlotLossSchedule.xi δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.xi]
    positivity
  have hcapEq :
      APrimeGeneralMovingSlotLossSchedule.deltaWeight δ +
          APrimeGeneralMovingSlotLossSchedule.xi δ =
        APrimeGeneralMovingSlotLossSchedule.deltaCap δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight,
      APrimeGeneralMovingSlotLossSchedule.xi,
      APrimeGeneralMovingSlotLossSchedule.deltaCap]
    ring
  have hcapPos : 0 <
      APrimeGeneralMovingSlotLossSchedule.deltaWeight δ +
        APrimeGeneralMovingSlotLossSchedule.xi δ := by
    rw [hcapEq]
    exact hcap
  have hcapRoom' :
      APrimeGeneralMovingSlotLossSchedule.tauG δ +
          2 * (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ +
            APrimeGeneralMovingSlotLossSchedule.xi δ) +
          (2 : Real) / 15 < 1 := by
    rw [hcapEq]
    exact hcapRoom
  have hactual := _root_.RBM.APrimeGeneralMovingActualSmoothQVNormBudget.eventually_actual_smooth_qv_integral_le_exact_profile
    hE hD hs0 hst ht1 hc hreg hB
    hzetaSrc hzetaCtr htau hxiPos hcapPos hcapRoom' p hp 1
    (by norm_num : (0 : Real) < 1)
  have hfit := APrimeGeneralMovingQVSlotFit.eventually_Qexact_N2_slot
    hE hD hs0 hst ht1 hc hreg hδ hsmall hp
  have hfactor0 : 0 ≤ 2 * (p : Real) - 1 := by
    have hpR : (1 : Real) ≤ p := by exact_mod_cast hp
    linarith
  filter_upwards [hactual, hfit] with N hactualN hfitN
  intro k hk a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let R := Step2Moment.ratR E s N v
  let x := (N : Real) ^ (δ / 8)
  have hactualCell := hactualN k hk a
  have hfitCell := hfitN k hk a
  have hintegral :
      (∫ u in s N..v,
        RBM.APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
        (∫ u in s N..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ +
              APrimeGeneralMovingSlotLossSchedule.xi δ) N k a u) +
          (v - s N) * (N : Real) ^ (-(1 : Real)) := by
    simpa only [RBM.APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingSlotLossSchedule.zetaSrc,
      APrimeGeneralMovingSlotLossSchedule.tauG,
      APrimeGeneralMovingSlotLossSchedule.deltaWeight,
      APrimeGeneralMovingSlotLossSchedule.xi] using hactualCell.2.2
  have hscaled := mul_le_mul_of_nonneg_left hintegral hfactor0
  have hscaledCap :
      (2 * (p : Real) - 1) *
          (∫ u in s N..v,
            RBM.APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) p N k a u) ≤
        (2 * (p : Real) - 1) *
          ((∫ u in s N..v,
            APrimeGeneralMovingQVNormBudget.Qexact E D s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) +
            (v - s N) * (N : Real) ^ (-(1 : Real))) := by
    simpa only [hbuffer] using hscaled
  have hfitRewritten :
      Real.sqrt ((2 * (p : Real) - 1) *
          ((∫ u in s N..v,
            APrimeGeneralMovingQVNormBudget.Qexact E D s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) +
            (v - s N) * (N : Real) ^ (-(1 : Real)))) ≤
        APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
    simpa only [v, R, x,
      APrimeGeneralMovingSlotLossSchedule.zetaSrc,
      APrimeGeneralMovingSlotLossSchedule.tauG,
      APrimeGeneralMovingSlotLossSchedule.deltaCap] using hfitCell
  calc
    _ ≤ Real.sqrt ((2 * (p : Real) - 1) *
        ((∫ u in s N..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) +
          (v - s N) * (N : Real) ^ (-(1 : Real)))) := by
      exact Real.sqrt_le_sqrt hscaledCap
    _ ≤ APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) :=
      hfitRewritten

/-- T995's same-resident positive-cell witness supplies a nondegenerate
realization of the schedule and BoundsCore hypotheses used above. -/
theorem scheduled_positive_cell_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (Gauss.sample d) 0 s ∧
      ∃ δ : Real, 0 < δ ∧ δ ≤ min 1 (c / 100) ∧
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t (APrimeGeneralMovingMesh.targetMesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh 60) N) ω := by
  rcases APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness with
    ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, _hStep, hw⟩
  let δ : Real := min 1 (c / 100) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hsmall : δ ≤ min 1 (c / 100) := by
    dsimp [δ]
    have hmin : 0 ≤ min 1 (c / 100) := by positivity
    linarith
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, δ, hδ, hsmall, ?_⟩
  have hwδ := hw δ hδ hsmall
  filter_upwards [hwδ] with N hN
  obtain ⟨hwindow, ω, hω, hactive, hwide, hweight⟩ := hN
  exact ⟨hwindow, ω, hω, hactive, hwide, hweight⟩

#print axioms eventually_actual_smooth_qv_N2_slot
#print axioms scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingActualSmoothQVSlot
