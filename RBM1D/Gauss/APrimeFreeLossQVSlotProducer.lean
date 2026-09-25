/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossQVRoot
import RBM1D.Gauss.APrimeFreeLossQVSlotFit

/-!
# T1329: actual-weight QV producer for the literal N2 coordinate slot

Compose the accepted actual-weight QV integral estimate with its accepted
small-slot fit, then identify that fit with T1323's exact `LiteralN2Slot`.
The joint witness below specializes the accepted positive-window witness to
`E = 0`, `D = 60` and retains its noncollapsed first active cell.
-/

namespace RBM.APrimeFreeLossQVSlotProducer

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- For each fixed `q ≥ 1`, the accepted actual-smooth QV integral producer
and accepted slot-fit consumer compose into the exact literal N2 input of
T1323. The eventual cutoff is uniform over every active cell, including
`k = 0`, and every output coordinate. -/
theorem eventually_literal_n2_slot_of_actual_qv_integral
    {E D c lambda : ℝ} {s t : ℕ → ℝ} {q : ℕ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hlambda : 0 < lambda)
    (hlambdaSmall : lambda ≤ min (1 / 10000) (c / 10000))
    (hq : 1 ≤ q) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        Real.sqrt ((2 * (q : ℝ) - 1) *
          (∫ u in (s N)..APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint
              s t D N k,
            APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
              E D s t lambda q N k a u)) ≤
          APrimeOneStep.tailTerm ((N : ℝ) ^ (lambda / 8))
            (Step2Moment.ratR E s N
              (APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k))
            (APrimeInit.slotKappa' ((N : ℝ) ^ (lambda / 8))) /
          (Step2Moment.ratR E s N
            (APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k)) ^ 4 := by
  have hQV :=
    RBM.APrimeFreeLossQVRoot.eventually_actual_weight_qv_integral_le_budget
      hE hD hs0 hst ht1 hc hreg hB hlambda hlambdaSmall q hq
  have hC : 0 < RBM.APrimeFreeLossQVRoot.actualQVIntegralConst E :=
    RBM.APrimeFreeLossQVRoot.actualQVIntegralConst_pos E hE
  have hFit :=
    RBM.APrimeFreeLossQVSlotFit.eventually_actual_qv_integral_fits_small_slot
      hE hs0 hst ht1 hlambda hlambdaSmall hq hC hQV
  filter_upwards [hFit] with N hFitN
  intro k hk a
  have hFitAt := hFitN k hk a
  simpa [APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm,
    APrimeGeneralMovingActualSmoothQVNormBudget.g,
    APrimeGeneralMovingActualSmoothQVNormBudget.endpoint] using hFitAt

/-- A joint nondegeneracy witness for the quantitative N2 conclusion: the
shared regularity and `BoundsCore` data have a positive-length window, and
for each fixed `q ≥ 1` its first positive active cell satisfies the exact
literal N2 slot eventually. -/
theorem positive_window_joint_literal_n2_witness (q : ℕ) (hq : 1 ≤ q) :
    ∃ c : ℝ, 0 < c ∧
    ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      ∃ lambda : ℝ,
        0 < lambda ∧
        lambda ≤ min (1 / 10000) (c / 10000) ∧
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧
          1 ≤ cutNetTop s t
            (APrimeGeneralMovingMesh.targetMesh 60) N ∧
          ∀ k : ℕ,
            k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N →
            ∀ a : LoopArg (d.L N) 2,
              Real.sqrt ((2 * (q : ℝ) - 1) *
                (∫ u in (s N)..APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint
                    s t 60 N k,
                  APrimeGeneralMovingAllOrdersMinkowskiActual.qvNorm
                    0 60 s t lambda q N k a u)) ≤
                APrimeOneStep.tailTerm ((N : ℝ) ^ (lambda / 8))
                  (Step2Moment.ratR 0 s N
                    (APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t 60 N k))
                  (APrimeInit.slotKappa' ((N : ℝ) ^ (lambda / 8))) /
                (Step2Moment.ratR 0 s N
                  (APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t 60 N k)) ^ 4 := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, _hStep,
      lambda, hlambda, hsmall, _hh, _hcap, _heq, _hcapTau, _hcapC,
      _hroom, hpositive⟩ :=
    RBM.APrimeFreeLossQVRoot.free_loss_hypotheses_witness
  have hN2 := eventually_literal_n2_slot_of_actual_qv_integral
    (E := 0) (D := 60) (c := c) (lambda := lambda) (s := s) (t := t)
    (q := q) (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
    hlambda hsmall hq
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
    lambda, hlambda, hsmall, ?_⟩
  filter_upwards [hpositive, hN2, Filter.eventually_ge_atTop 1]
    with N hpositiveN hN2N hN
  rcases hpositiveN with ⟨hlen, _omega, _hresident, hactive, _hplateau⟩
  refine ⟨hlen, ?_, ?_⟩
  · simpa using hactive
  · exact hN2N

#print axioms eventually_literal_n2_slot_of_actual_qv_integral
#print axioms positive_window_joint_literal_n2_witness

end
end RBM.APrimeFreeLossQVSlotProducer
