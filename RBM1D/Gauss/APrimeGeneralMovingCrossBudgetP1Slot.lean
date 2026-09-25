/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodP1Slot

/-!
# T1217: full literal p=1 general-moving cross-budget small slot

This combines the accepted T1207 integrated reduction with the accepted
T1211 p=1 norm-good bound, and absorbs the explicit inverse-N payment using
the T995 Cond272 scale margin.  It concerns the smooth-prefix auxiliary
budget only; it makes no claim about the paper's stopped process.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetP1Slot

open Filter MeasureTheory Set Gauss CutHypTheta
open APrimeGeneralMovingCrossBudgetGoodIntegralReduction
open APrimeGeneralMovingCrossBudgetNormGoodP1Slot

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D

/-- For each fixed `δ` in the T995 range, the literal p=1 full cross-budget
integral is bounded on every active target-mesh cell by the T1211 small-slot
scale.  The cutoff is uniform over cells and outputs. -/
theorem eventually_integral_positiveTimeCrossBudget_p1_le_small_slot
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in atTop, ∀ k : Nat,
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ u in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k 1 a u) ≤
            C * (N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
  have hGoodRaw :=
    eventually_integral_normGoodCrossBudget_le_small_slot
      (E := E) (D := D) (c := c) (δ := δ) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall
  have hGood : ∃ Cgood : Real, 0 < Cgood ∧
      ∀ᶠ N : Nat in atTop, ∀ k : Nat,
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ u in (s N)..v,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k 1 a u) ≤
            Cgood * (N : Real)^(5 * δ / 32) *
              Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
    convert hGoodRaw using 1 <;> rfl
  obtain ⟨Cgood, hCgood, hGood⟩ := hGood
  have hDeltaWeight : 0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hReducedRaw :=
    eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hDeltaWeight 1 (by omega)
  have hReduced : ∀ᶠ N : Nat in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        (∫ u in (s N)..(cutNetPt s (mesh D) N k),
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u) ≤
        (∫ u in (s N)..(cutNetPt s (mesh D) N k),
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k 1 a u) +
        (15 / 4 : Real) * (N : Real)^(-1 : Real) *
          (Real.sqrt (cutNetPt s (mesh D) N k) -
            Real.sqrt (s N)) := by
    convert hReducedRaw using 1 <;> norm_num [mesh, d]
  have hThirty := hreg.1.pow_thirty_le hE hst ht1
  let C : Real := Cgood + 15 / 4
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hGood, hReduced, hThirty, B.dim,
    eventually_ge_atTop 1] with N hGoodN hReducedN hThirtyN hdim hN
  have hNpos : 0 < N := by omega
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hv.1 hv1
  let vv : TimeIcc s t N := ⟨v, hv⟩
  have hscale : B.scale E N v ≤ (N : Real) := by
    obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N vv
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast hdim.1
    change (B.W N : Real) * B.ell N v * etaT E v ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hR30 : Step2Moment.ratR E s N v ^ (30 : Nat) ≤ (N : Real) := by
    have hmargin := hThirtyN vv
    simpa [vv, Step2Moment.ratR] using hmargin.trans hscale
  have hR28 : 1 ≤ Step2Moment.ratR E s N v ^ (28 : Nat) :=
    one_le_pow₀ hR1
  have hR2Nat : Step2Moment.ratR E s N v ^ (2 : Nat) ≤
      Step2Moment.ratR E s N v ^ (30 : Nat) := by
    calc
      _ = Step2Moment.ratR E s N v ^ 2 * 1 := by simp
      _ ≤ Step2Moment.ratR E s N v ^ 2 *
          Step2Moment.ratR E s N v ^ 28 :=
        mul_le_mul_of_nonneg_left hR28 (sq_nonneg _)
      _ = Step2Moment.ratR E s N v ^ 30 := by rw [← pow_add]
  have hR2 : Step2Moment.ratR E s N v ^ (2 : Nat) ≤ (N : Real) :=
    hR2Nat.trans hR30
  have hNinv : (N : Real)^(-1 : Real) ≤
      Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
    have hdiv := one_div_le_one_div_of_le (sq_pos_of_pos hRpos) hR2
    have hNpow : (N : Real)^(-1 : Real) = 1 / (N : Real) := by
      rw [Real.rpow_neg (by exact_mod_cast hNpos.le), Real.rpow_one]
      simp [one_div]
    have hRpow : Step2Moment.ratR E s N v ^ (-(2 : Real)) =
        1 / Step2Moment.ratR E s N v ^ (2 : Nat) := by
      rw [Real.rpow_neg hRpos.le]
      simp [one_div]
    rw [hNpow, hRpow]
    exact hdiv
  have hNpow1 : 1 ≤ (N : Real)^(5 * δ / 32) :=
    Real.one_le_rpow hN1 (by positivity)
  have hTargetNonneg : 0 ≤ (N : Real)^(5 * δ / 32) *
      Step2Moment.ratR E s N v ^ (-(2 : Real)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hRpos.le _)
  have hNinvTarget : (N : Real)^(-1 : Real) ≤
      (N : Real)^(5 * δ / 32) *
        Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
    calc
      _ ≤ Step2Moment.ratR E s N v ^ (-(2 : Real)) := hNinv
      _ ≤ (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hNpow1
            (Real.rpow_nonneg hRpos.le _))
  have hsqrtGap : Real.sqrt v - Real.sqrt (s N) ≤ 1 := by
    have hsqrtv : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv1.le
    nlinarith [Real.sqrt_nonneg (s N)]
  have hError : (15 / 4 : Real) * (N : Real)^(-1 : Real) *
      (Real.sqrt v - Real.sqrt (s N)) ≤
      (15 / 4 : Real) * ((N : Real)^(5 * δ / 32) *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) := by
    have hcoef : 0 ≤ (15 / 4 : Real) * (N : Real)^(-1 : Real) := by
      positivity
    calc
      _ = ((15 / 4 : Real) * (N : Real)^(-1 : Real)) *
          (Real.sqrt v - Real.sqrt (s N)) := by ring
      _ ≤ ((15 / 4 : Real) * (N : Real)^(-1 : Real)) * 1 :=
        mul_le_mul_of_nonneg_left hsqrtGap hcoef
      _ = (15 / 4 : Real) * (N : Real)^(-1 : Real) := by ring
      _ ≤ (15 / 4 : Real) *
          ((N : Real)^(5 * δ / 32) *
            Step2Moment.ratR E s N v ^ (-(2 : Real))) := by
        exact mul_le_mul_of_nonneg_left hNinvTarget (by norm_num)
  have hGoodBound := hGoodN k hk a
  have hReduction := hReducedN k hk a
  change (∫ u in (s N)..v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N k 1 a u) ≤
      Cgood * (N : Real)^(5 * δ / 32) *
        Step2Moment.ratR E s N v ^ (-(2 : Real)) at hGoodBound
  change (∫ u in (s N)..v,
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s t N k 1 a u) ≤
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k 1 a u) +
      (15 / 4 : Real) * (N : Real)^(-1 : Real) *
        (Real.sqrt v - Real.sqrt (s N)) at hReduction
  dsimp [C]
  nlinarith [hGoodBound, hReduction, hError]

/-- The T995 model context has an actual positive scheduled cell and a common
event sample.  This witness makes no transition-residence or nonzero-rate
claim. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_integral_positiveTimeCrossBudget_p1_le_small_slot
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingCrossBudgetP1Slot
