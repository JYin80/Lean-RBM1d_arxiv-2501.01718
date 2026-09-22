/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellBlockNetTail
import RBM1D.Gauss.APrimeFirstCellBlockUnionPrep

/-!
# Actual first-cell adjacent-block event and all-time `jG` bound (T428)

This file assembles the actual Gaussian per-block tail, the cyclic forward-edge reduction, and
the deterministic first-cell Combes--Thomas estimate on one common event.
-/

namespace RBM.APrimeFirstCellJGActual

open Filter Real MeasureTheory Gauss Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow

/-- The assembled event is T407's existing measurable adjacent-block event. -/
theorem measurableSet_adjacentBlockEvent (N : ℕ) :
    MeasurableSet (APrimeFirstCellJGAllTime.adjacentBlockEvent N) :=
  APrimeFirstCellJGAllTime.measurableSet_adjacentBlockEvent N

/-- The entropy factor in the quarter-net bound is absorbed by the strict exponent margin. -/
theorem per_forward_edge_real_tail (N : ℕ) (x : ZMod (d.L N)) :
    (Gauss.P d).real (APrimeFirstCellBlockUnionPrep.forwardEdgeBad N x) ≤
      4 * Real.exp (-15 * (d.W N : ℝ)) := by
  have hxy : x ≠ x + 1 := by
    intro h
    have h01 : (0 : ZMod (d.L N)) = 1 := by
      have hx : x + (0 : ZMod (d.L N)) = x + 1 := (add_zero x).trans h
      exact add_left_cancel hx
    exact one_ne_zero_zmod (d.L N) (d.three_le_L N) h01.symm
  have hadj : zdist (d.L N) (x - (x + 1)) ≤ 1 := by
    have heq : x - (x + 1) = (-1 : ZMod (d.L N)) := by abel
    rw [heq]
    exact zdist_neg_one_le (d.L N) (d.three_le_L N)
  have htail := APrimeFirstCellBlockNetTail.block_opNorm_tail N hxy hadj
  have hcoef : 4 * Real.log 9 - 24 ≤ (-15 : ℝ) := by
    linarith [APrimeFirstCellBlockUnionPrep.fifteen_lt_twentyfour_sub_four_log_nine]
  have hW0 : (0 : ℝ) ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have hexponent :
      ((4 * d.W N : ℕ) : ℝ) * Real.log 9 + -24 * (d.W N : ℝ) ≤
        -15 * (d.W N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hcoef hW0
    norm_num at hm ⊢
    nlinarith [hm]
  have hexp :
      (9 : ℝ) ^ (4 * d.W N) * Real.exp (-24 * (d.W N : ℝ)) ≤
        Real.exp (-15 * (d.W N : ℝ)) := by
    calc
      (9 : ℝ) ^ (4 * d.W N) * Real.exp (-24 * (d.W N : ℝ)) =
          Real.exp (((4 * d.W N : ℕ) : ℝ) * Real.log 9 +
            -24 * (d.W N : ℝ)) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 9)]
      _ ≤ Real.exp (-15 * (d.W N : ℝ)) := Real.exp_le_exp.mpr hexponent
  change (Gauss.P d).real
      {ω | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x
        (x + 1 : ZMod (d.L N))‖} ≤ _
  calc
    (Gauss.P d).real
        {ω | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x
          (x + 1 : ZMod (d.L N))‖} ≤
        4 * ((9 : ℝ) ^ (4 * d.W N) * Real.exp (-24 * (d.W N : ℝ))) := by
      simpa only [mul_assoc] using htail
    _ ≤ 4 * Real.exp (-15 * (d.W N : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- The union of all forward-edge failures has the required stretched-exponential bound. -/
theorem forwardEdgeBadUnion_real_le (N : ℕ) :
    (Gauss.P d).real (APrimeFirstCellBlockUnionPrep.forwardEdgeBadUnion N) ≤
      4 * (d.L N : ℝ) * Real.exp (-15 * (d.W N : ℝ)) := by
  calc
    (Gauss.P d).real (APrimeFirstCellBlockUnionPrep.forwardEdgeBadUnion N) =
        (Gauss.P d).real
          (⋃ x : ZMod (d.L N), APrimeFirstCellBlockUnionPrep.forwardEdgeBad N x) := rfl
    _ ≤ ∑ x : ZMod (d.L N),
        (Gauss.P d).real (APrimeFirstCellBlockUnionPrep.forwardEdgeBad N x) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : ZMod (d.L N), 4 * Real.exp (-15 * (d.W N : ℝ)) := by
      exact Finset.sum_le_sum fun x _ => per_forward_edge_real_tail N x
    _ = 4 * (d.L N : ℝ) * Real.exp (-15 * (d.W N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change (Fintype.card (ZMod (d.L N)) : ℝ) *
          (4 * Real.exp (-15 * (d.W N : ℝ))) = _
      rw [ZMod.card]
      ring

/-- The literal adjacent-block event of T407 holds with high probability under the actual
`exampleGrow` Gaussian law. -/
theorem highProb_adjacentBlockEvent :
    HighProb (Gauss.P d) APrimeFirstCellJGAllTime.adjacentBlockEvent := by
  intro D hD
  filter_upwards
    [APrimeFirstCellBlockUnionPrep.eventually_four_mul_L_exp_neg_fifteen_W_le_rpow_neg D hD]
      with N hN
  have hreal :
      (Gauss.P d).real (APrimeFirstCellJGAllTime.adjacentBlockEvent N)ᶜ ≤
        (N : ℝ) ^ (-D) := by
    calc
      (Gauss.P d).real (APrimeFirstCellJGAllTime.adjacentBlockEvent N)ᶜ ≤
          (Gauss.P d).real (APrimeFirstCellBlockUnionPrep.forwardEdgeBadUnion N) :=
        measureReal_mono
          (APrimeFirstCellBlockUnionPrep.compl_adjacentBlockEvent_subset_forwardEdgeBadUnion N)
          (measure_ne_top _ _)
      _ ≤ 4 * (d.L N : ℝ) * Real.exp (-15 * (d.W N : ℝ)) :=
        forwardEdgeBadUnion_real_le N
      _ ≤ (N : ℝ) ^ (-D) := hN
  calc
    (Gauss.P d) (APrimeFirstCellJGAllTime.adjacentBlockEvent N)ᶜ =
        ENNReal.ofReal
          ((Gauss.P d).real (APrimeFirstCellJGAllTime.adjacentBlockEvent N)ᶜ) :=
      (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hreal

/-- T407's probability-one off-band event and the actual adjacent-block event hold on the same
high-probability event. -/
theorem highProb_good :
    HighProb (Gauss.P d) APrimeFirstCellJGAllTime.good :=
  APrimeFirstCellJGAllTime.highProb_good_of_adjacent highProb_adjacentBlockEvent

/-- Actual all-real-time first-cell closure, with the literal choices `E = 0` and `D = 60`. -/
theorem highProb_all_time_jG_le_two :
    HighProb (Gauss.P d) (fun N =>
      {ω | ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        APrimeJG.jG (Gauss.sample d) 0 N u ω
          ((Gauss.band d).ell N u) (etaT 0 u) 60 ≤ 2}) := by
  exact HighProb.mono highProb_good
    APrimeFirstCellCTDecay.eventually_all_time_jG_le_two_on_good

/-- The same deterministic good event has a nonzero sample carrying the terminal bound at the
positive time `u = 1/4`. -/
theorem eventually_exists_nonzero_good_at_quarter_time :
    ∀ᶠ N : ℕ in atTop, ∃ ω : Gauss.Ω d,
      ω ∈ APrimeFirstCellJGAllTime.good N ∧ Xmat d N ω ≠ 0 ∧
        APrimeJG.jG (Gauss.sample d) 0 N (1 / 4 : ℝ) ω
          ((Gauss.band d).ell N (1 / 4 : ℝ)) (etaT 0 (1 / 4 : ℝ)) 60 ≤ 2 := by
  filter_upwards [APrimeFirstCellCTDecay.eventually_all_time_jG_le_two_on_good] with N hN
  obtain ⟨ω, hω, hX⟩ := APrimeFirstCellBlockUnionPrep.exists_nonzero_mem_good N
  refine ⟨ω, hω, hX, hN ω hω (1 / 4 : ℝ) ?_⟩
  constructor <;> norm_num

#print axioms measurableSet_adjacentBlockEvent
#print axioms per_forward_edge_real_tail
#print axioms forwardEdgeBadUnion_real_le
#print axioms highProb_adjacentBlockEvent
#print axioms highProb_good
#print axioms highProb_all_time_jG_le_two
#print axioms eventually_exists_nonzero_good_at_quarter_time

end

end RBM.APrimeFirstCellJGActual
