/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCTDecay

/-!
# Orientation and asymptotic preparation for the first-cell block union (T425)

This file is independent of the finite-net probability union.  It identifies the two ordered
orientations of a cyclic edge, reduces all adjacent block failures to the forward edges, and proves
the deterministic exponential-to-polynomial comparison needed after that finite union is supplied.
-/

namespace RBM.APrimeFirstCellBlockUnionPrep

open Filter Real MeasureTheory Gauss Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow

/-! ## Opposite orientations are adjoints -/

/-- Reversing the ordered blocks gives the conjugate transpose pointwise. -/
theorem xBlock_swap (N : ℕ) (ω : Gauss.Ω d) (x y : ZMod (d.L N)) :
    APrimeFirstCellJGAllTime.xBlock N ω y x =
      (APrimeFirstCellJGAllTime.xBlock N ω x y)ᴴ := by
  ext p q
  change Xentry d N ω (y, p) (x, q) =
    (starRingEnd ℂ) (Xentry d N ω (x, q) (y, p))
  exact Xentry_swap d N ω (x, q) (y, p)

/-- In particular, the two orientations have the same `ℓ² → ℓ²` operator norm. -/
theorem norm_xBlock_swap (N : ℕ) (ω : Gauss.Ω d) (x y : ZMod (d.L N)) :
    ‖APrimeFirstCellJGAllTime.xBlock N ω y x‖ =
      ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖ := by
  rw [xBlock_swap, Matrix.l2_opNorm_conjTranspose]

/-! ## Cyclic orientation reduction -/

/-- A distinct pair at cyclic distance at most one is one of the two orientations of an edge. -/
theorem adjacent_pair_eq_forward_or_reverse (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {x y : ZMod L} (hxy : x ≠ y) (hadj : zdist L (x - y) ≤ 1) :
    y = x + 1 ∨ x = y + 1 := by
  rcases APrimeFirstCellCTDecay.eq_zero_or_eq_one_or_eq_neg_one_of_zdist_le_one
      L hL (x - y) hadj with hzero | hone | hneg
  · exact absurd (sub_eq_zero.mp hzero) hxy
  · right
    have h := congrArg (fun z : ZMod L => z + y) hone
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  · left
    have h := congrArg (fun z : ZMod L => -z + x) hneg
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- The classification includes the smallest allowed cycle, `L = 3`. -/
theorem adjacent_pair_three {x y : ZMod 3} (hxy : x ≠ y)
    (hadj : zdist 3 (x - y) ≤ 1) : y = x + 1 ∨ x = y + 1 := by
  exact adjacent_pair_eq_forward_or_reverse 3 (by norm_num) hxy hadj

/-- Failure of the block norm bound on the forward cyclic edge starting at `x`. -/
def forwardEdgeBad (N : ℕ) (x : ZMod (d.L N)) : Set (Gauss.Ω d) :=
  {ω | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x
    (x + 1 : ZMod (d.L N))‖}

/-- The union of the `L_N` forward-edge failures. -/
def forwardEdgeBadUnion (N : ℕ) : Set (Gauss.Ω d) :=
  ⋃ x : ZMod (d.L N), forwardEdgeBad N x

theorem measurableSet_forwardEdgeBad (N : ℕ) (x : ZMod (d.L N)) :
    MeasurableSet (forwardEdgeBad N x) := by
  exact measurableSet_lt measurable_const
    (APrimeFirstCellJGAllTime.measurable_xBlock N x
      (x + 1 : ZMod (d.L N))).norm

theorem measurableSet_forwardEdgeBadUnion (N : ℕ) :
    MeasurableSet (forwardEdgeBadUnion N) := by
  exact MeasurableSet.iUnion fun x => measurableSet_forwardEdgeBad N x

/-- There are exactly `L_N` forward-edge indices, including exactly three when `L_N = 3`. -/
theorem card_forward_edges (N : ℕ) :
    (Finset.univ : Finset (ZMod (d.L N))).card = d.L N := by
  change Fintype.card (ZMod (d.L N)) = d.L N
  exact ZMod.card (d.L N)

/-- Every failure of T407's full ordered adjacent-block event occurs on a forward edge. -/
theorem compl_adjacentBlockEvent_subset_forwardEdgeBadUnion (N : ℕ) :
    (APrimeFirstCellJGAllTime.adjacentBlockEvent N)ᶜ ⊆ forwardEdgeBadUnion N := by
  letI : NeZero (d.L N) :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) (d.three_le_L N))⟩
  intro ω hω
  change ¬(∀ (x y : ZMod (d.L N)), x ≠ y →
    zdist (d.L N) (x - y) ≤ 1 →
      ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖ ≤ 8) at hω
  obtain ⟨x, hx⟩ := not_forall.mp hω
  obtain ⟨y, hy⟩ := not_forall.mp hx
  obtain ⟨hxy, hy⟩ := not_imp.mp hy
  obtain ⟨hadj, hbad⟩ := not_imp.mp hy
  have hbad : 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖ := lt_of_not_ge hbad
  rcases adjacent_pair_eq_forward_or_reverse (d.L N) (d.three_le_L N) hxy hadj with
      hforward | hreverse
  · subst y
    exact Set.mem_iUnion_of_mem x hbad
  · have hbad' : 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω y x‖ := by
      rw [norm_xBlock_swap]
      exact hbad
    subst x
    exact Set.mem_iUnion_of_mem y hbad'

/-! ## Numerical margin and eventual exponential absorption -/

/-- The net entropy leaves more than the advertised exponent margin `15`. -/
theorem fifteen_lt_twentyfour_sub_four_log_nine :
    (15 : ℝ) < 24 - 4 * Real.log 9 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4) 6
  have hnine : (9 : ℝ) <
      ∑ i ∈ Finset.range 6, ((9 : ℝ) / 4) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hlog : Real.log 9 < (9 : ℝ) / 4 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 (hnine.trans_le hsum)
  linarith

/-- The exampleGrow bandwidth absorbs the forward-edge factor and every polynomial target. -/
theorem eventually_four_mul_L_exp_neg_fifteen_W_le_rpow_neg (D : ℝ) (_hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      4 * (d.L N : ℝ) * Real.exp (-15 * (d.W N : ℝ)) ≤ (N : ℝ) ^ (-D) := by
  have hexp := SumZeroDyn.eventually_exp_small 4 (D + 1) 15
    (by norm_num : (0 : ℝ) < 15) (by norm_num : (0 : ℝ) < (5 : ℝ) / 8)
  filter_upwards [Gauss.Dims.bandwidth_grow, d.dim, hexp, eventually_ge_atTop 1] with
      N hW hdim hexpN hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hLN : (d.L N : ℝ) ≤ (N : ℝ) := by
    have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
    nlinarith [mul_le_mul_of_nonneg_right hW1 (Nat.cast_nonneg (d.L N))]
  have hW' : (N : ℝ) ^ ((5 : ℝ) / 8) ≤
      (Gauss.Dims.growW N : ℝ) := by
    simpa only [show (1 : ℝ) / 2 + 1 / 8 = 5 / 8 by norm_num] using hW
  have hdW : d.W N = Gauss.Dims.growW N := rfl
  have hW'' : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ) := by
    rw [hdW]
    exact hW'
  have hexpMono : Real.exp (-15 * (d.W N : ℝ)) ≤
      Real.exp (-15 * (N : ℝ) ^ ((5 : ℝ) / 8)) := by
    rw [Real.exp_le_exp]
    nlinarith [hW'']
  have hpre : 4 * (d.L N : ℝ) * Real.exp (-15 * (d.W N : ℝ)) ≤
      4 * (N : ℝ) * Real.exp (-15 * (N : ℝ) ^ ((5 : ℝ) / 8)) := by
    gcongr
  have hpowD : 0 < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 D
  have hpoly : 4 * (N : ℝ) * Real.exp (-15 * (N : ℝ) ^ ((5 : ℝ) / 8)) ≤
      (N : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hN0.le]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hpowD).2
    calc
      4 * (N : ℝ) * Real.exp (-15 * (N : ℝ) ^ ((5 : ℝ) / 8)) *
          (N : ℝ) ^ D =
          4 * (N : ℝ) ^ (D + 1) *
            Real.exp (-(15 * (N : ℝ) ^ ((5 : ℝ) / 8))) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
        ring
      _ ≤ 1 := hexpN
  exact hpre.trans hpoly

/-! The deterministic event remains nonempty on an actual nonzero sample, inherited from T414. -/

theorem exists_nonzero_mem_good (N : ℕ) :
    ∃ ω : Gauss.Ω d, ω ∈ APrimeFirstCellJGAllTime.good N ∧ Xmat d N ω ≠ 0 :=
  ⟨APrimeFirstCellCTDecay.diagonalWitness,
    APrimeFirstCellCTDecay.diagonalWitness_mem_good N,
    APrimeFirstCellCTDecay.Xmat_diagonalWitness_ne_zero N⟩

#print axioms xBlock_swap
#print axioms norm_xBlock_swap
#print axioms adjacent_pair_eq_forward_or_reverse
#print axioms adjacent_pair_three
#print axioms compl_adjacentBlockEvent_subset_forwardEdgeBadUnion
#print axioms fifteen_lt_twentyfour_sub_four_log_nine
#print axioms eventually_four_mul_L_exp_neg_fifteen_W_le_rpow_neg
#print axioms exists_nonzero_mem_good

end

end RBM.APrimeFirstCellBlockUnionPrep
