/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowGridCount

/-!
# Exact exponent and numerical bound for the Fourier threshold

These deterministic lemmas use the threshold `64 * sqrt (log N / W)`.
The eventual specialization consumes the accepted exact clipped-grid count
for `Dims.exampleGrow`.
-/

namespace RBM.Gauss

open Filter

/-- The exponential in the finite Fourier tail is exactly `N⁻¹⁶` at the
chosen threshold. -/
theorem permutationFourierThreshold_exp_eq_rpow (N W : ℕ)
    (hN : 2 ≤ N) (hW : 0 < W) (hlog : 0 < Real.log N) :
    Real.exp (-(W : ℝ) *
      (64 * Real.sqrt (Real.log N / (W : ℝ))) ^ 2 / 256) =
        (N : ℝ) ^ (-16 : ℝ) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hq : 0 ≤ Real.log N / (W : ℝ) := (div_pos hlog hWr).le
  have harg : -(W : ℝ) *
      (64 * Real.sqrt (Real.log N / (W : ℝ))) ^ 2 / 256 =
        -16 * Real.log N := by
    rw [mul_pow, Real.sq_sqrt hq]
    field_simp
    ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [harg, Real.rpow_def_of_pos hNr]
  congr 1
  ring

/-- The conservative count `K ≤ 2N²` makes the Fourier union-bound
coefficient strictly smaller than one at exponent `-16`. -/
theorem permutationFourierConstraintCount_rpow_bound (N K : ℕ)
    (hN : 2 ≤ N) (hK : K ≤ 2 * N ^ 2) :
    4 * (K : ℝ) * (N : ℝ) ^ (-16 : ℝ) ≤
      8 * (N : ℝ) ^ (-14 : ℝ) ∧
      8 * (N : ℝ) ^ (-14 : ℝ) < 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKr : (K : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast hK
  constructor
  · calc
      4 * (K : ℝ) * (N : ℝ) ^ (-16 : ℝ) ≤
          4 * (2 * (N : ℝ) ^ 2) * (N : ℝ) ^ (-16 : ℝ) := by
            gcongr
      _ = 8 * (N : ℝ) ^ (-14 : ℝ) := by
        rw [show (-14 : ℝ) = 2 + -16 by norm_num, Real.rpow_add hNr]
        have hpow2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ (2 : ℕ) := by
          exact Real.rpow_natCast _ 2
        rw [hpow2]
        ring_nf
  · rw [show (-14 : ℝ) = -(14 : ℝ) by norm_num, Real.rpow_neg hNr.le]
    have hpow : (2 : ℝ) ^ 14 ≤ (N : ℝ) ^ 14 :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hN) _
    have hlarge : (8 : ℝ) < (N : ℝ) ^ 14 := by
      have : (8 : ℝ) < (2 : ℝ) ^ 14 := by norm_num
      exact this.trans_le hpow
    have hpos : (0 : ℝ) < (N : ℝ) ^ 14 := by positivity
    simpa [div_eq_mul_inv] using (div_lt_one hpos).2 hlarge

/-- The exact threshold for the growing dimension witness. -/
noncomputable def permutationFourierExampleGrowThreshold (N : ℕ) : ℝ :=
  64 * Real.sqrt (Real.log N / (Dims.exampleGrow.W N : ℝ))

/-- On one eventual set, the growing model has real nonzero Fourier modes and
time nodes; the exponential is exactly `N⁻¹⁶`, the conservative `L_N`-block
count is small, and the smaller one-permutation premise of the finite
existence theorem is strictly below one. -/
theorem permutationFourierExampleGrow_eventually_exponent_and_premise :
    ∀ᶠ N : ℕ in atTop,
      3 ≤ Dims.exampleGrow.L N ∧
      2 ≤ Dims.exampleGrow.W N ∧
      0 < permutationFourierExampleGrowGridCount N ∧
      0 < permutationFourierExampleGrowConstraintCount N ∧
      0 < permutationFourierExampleGrowThreshold N ∧
      Real.exp (-(Dims.exampleGrow.W N : ℝ) *
        (permutationFourierExampleGrowThreshold N) ^ 2 / 256) =
          (N : ℝ) ^ (-16 : ℝ) ∧
      4 * (permutationFourierExampleGrowConstraintCount N : ℝ) *
        Real.exp (-(Dims.exampleGrow.W N : ℝ) *
          (permutationFourierExampleGrowThreshold N) ^ 2 / 256) ≤
            8 * (N : ℝ) ^ (-14 : ℝ) ∧
      8 * (N : ℝ) ^ (-14 : ℝ) < 1 ∧
      4 * ((permutationFourierExampleGrowGridCount N *
        (Dims.exampleGrow.W N - 1) : ℕ) : ℝ) *
          Real.exp (-(Dims.exampleGrow.W N : ℝ) *
            (permutationFourierExampleGrowThreshold N) ^ 2 / 256) < 1 := by
  filter_upwards [permutationFourierExampleGrow_eventually_bounds,
    permutationFourierExampleGrow_eventually_nondegenerate,
    eventually_ge_atTop 2] with N hall hnd hN
  have hW : 0 < Dims.exampleGrow.W N := Dims.exampleGrow.W_pos N
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have hid : Real.exp (-(Dims.exampleGrow.W N : ℝ) *
      (permutationFourierExampleGrowThreshold N) ^ 2 / 256) =
        (N : ℝ) ^ (-16 : ℝ) := by
    simpa only [permutationFourierExampleGrowThreshold] using
      permutationFourierThreshold_exp_eq_rpow N (Dims.exampleGrow.W N) hN hW hlog
  have hbounds := permutationFourierConstraintCount_rpow_bound N
    (permutationFourierExampleGrowConstraintCount N) hN hall.2.2.2
  have hr : 0 < permutationFourierExampleGrowThreshold N := by
    unfold permutationFourierExampleGrowThreshold
    have hWr : (0 : ℝ) < Dims.exampleGrow.W N := by exact_mod_cast hW
    positivity
  have hL : 1 ≤ Dims.exampleGrow.L N := by omega
  have hKone : permutationFourierExampleGrowGridCount N *
      (Dims.exampleGrow.W N - 1) ≤
        permutationFourierExampleGrowConstraintCount N := by
    unfold permutationFourierExampleGrowConstraintCount
    calc
      permutationFourierExampleGrowGridCount N * (Dims.exampleGrow.W N - 1) =
          1 * ((Dims.exampleGrow.W N - 1) *
            permutationFourierExampleGrowGridCount N) := by ring
      _ ≤ Dims.exampleGrow.L N * ((Dims.exampleGrow.W N - 1) *
          permutationFourierExampleGrowGridCount N) :=
        Nat.mul_le_mul_right _ hL
      _ = Dims.exampleGrow.L N * (Dims.exampleGrow.W N - 1) *
          permutationFourierExampleGrowGridCount N := by ring
  have hKoner : ((permutationFourierExampleGrowGridCount N *
      (Dims.exampleGrow.W N - 1) : ℕ) : ℝ) ≤
        (permutationFourierExampleGrowConstraintCount N : ℝ) := by
    exact_mod_cast hKone
  refine ⟨hnd.1, hnd.2.1, hnd.2.2.1, hnd.2.2.2,
    hr, hid, ?_, hbounds.2, ?_⟩
  · simpa only [hid] using hbounds.1
  · calc
      4 * ((permutationFourierExampleGrowGridCount N *
            (Dims.exampleGrow.W N - 1) : ℕ) : ℝ) *
          Real.exp (-(Dims.exampleGrow.W N : ℝ) *
            (permutationFourierExampleGrowThreshold N) ^ 2 / 256)
        ≤ 4 * (permutationFourierExampleGrowConstraintCount N : ℝ) *
          Real.exp (-(Dims.exampleGrow.W N : ℝ) *
            (permutationFourierExampleGrowThreshold N) ^ 2 / 256) := by
          gcongr
      _ ≤ 8 * (N : ℝ) ^ (-14 : ℝ) := by
        simpa only [hid] using hbounds.1
      _ < 1 := hbounds.2

#print axioms permutationFourierThreshold_exp_eq_rpow
#print axioms permutationFourierConstraintCount_rpow_bound
#print axioms permutationFourierExampleGrow_eventually_exponent_and_premise

end RBM.Gauss
