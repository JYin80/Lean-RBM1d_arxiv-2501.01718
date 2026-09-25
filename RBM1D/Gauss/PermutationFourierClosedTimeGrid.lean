/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib

/-!
# A finite clipped grid for the closed time interval

For a positive mesh size `h`, this grid includes both endpoints of `[0, 1/2]`,
clips its final regular mesh point to `1/2`, and covers the interval to within
distance `h`.

This is a deterministic arithmetic auxiliary. It does not assert a Gaussian
local law or any probabilistic estimate from paper equations (2.3)--(2.4).
-/

namespace RBM.Gauss

/-- Number of nodes in the clipped mesh of `[0, 1/2]` with step `h`. -/
noncomputable def permutationFourierClosedTimeGridCount (h : ℝ) : ℕ :=
  Nat.ceil ((1 / 2 : ℝ) / h) + 1

/-- The `j`th clipped mesh point in `[0, 1/2]`. -/
noncomputable def permutationFourierClosedTimeGrid (h : ℝ)
    (j : Fin (permutationFourierClosedTimeGridCount h)) : ℝ :=
  min ((j.val : ℝ) * h) (1 / 2 : ℝ)

theorem permutationFourierClosedTimeGrid_zero (h : ℝ) :
    permutationFourierClosedTimeGrid h ⟨0, Nat.zero_lt_succ _⟩ = 0 := by
  simp [permutationFourierClosedTimeGrid]

theorem permutationFourierClosedTimeGrid_range (h : ℝ) (hh : 0 < h)
    (j : Fin (permutationFourierClosedTimeGridCount h)) :
    0 ≤ permutationFourierClosedTimeGrid h j ∧
      permutationFourierClosedTimeGrid h j ≤ 1 / 2 := by
  constructor
  · apply le_min
    · exact mul_nonneg (Nat.cast_nonneg _) hh.le
    · norm_num
  · exact min_le_right _ _

theorem permutationFourierClosedTimeGrid_last (h : ℝ) (hh : 0 < h) :
    permutationFourierClosedTimeGrid h
      ⟨Nat.ceil ((1 / 2 : ℝ) / h), Nat.lt_succ_self _⟩ = 1 / 2 := by
  apply min_eq_right
  have hceil := Nat.le_ceil ((1 / 2 : ℝ) / h)
  rw [div_le_iff₀ hh] at hceil
  exact_mod_cast hceil

/-- Every point of `[0, 1/2]` lies within one mesh step of a clipped grid node.
The proof chooses the floor index, so the estimate is in fact strict. -/
theorem permutationFourierClosedTimeGrid_coverage (h u : ℝ) (hh : 0 < h)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ∃ j : Fin (permutationFourierClosedTimeGridCount h),
      |u - permutationFourierClosedTimeGrid h j| < h := by
  let k : ℕ := Nat.floor (u / h)
  have huv : u / h ≤ (1 / 2 : ℝ) / h :=
    (div_le_div_iff_of_pos_right hh).2 hu1
  have hk : k ≤ Nat.ceil ((1 / 2 : ℝ) / h) := by
    dsimp [k]
    exact (Nat.floor_mono huv).trans (Nat.floor_le_ceil _)
  let j : Fin (permutationFourierClosedTimeGridCount h) :=
    ⟨k, Nat.lt_succ_of_le (by simpa [permutationFourierClosedTimeGridCount] using hk)⟩
  have hkh : (k : ℝ) * h ≤ u := by
    have hf : (Nat.floor (u / h) : ℝ) ≤ u / h :=
      Nat.floor_le (div_nonneg hu0 hh.le)
    calc
      (k : ℝ) * h = (Nat.floor (u / h) : ℝ) * h := by rfl
      _ ≤ (u / h) * h := mul_le_mul_of_nonneg_right hf hh.le
      _ = u := by field_simp [ne_of_gt hh]
  have huk : u < (k : ℝ) * h + h := by
    dsimp [k]
    have hf := Nat.lt_floor_add_one (u / h)
    have hf' : u / h < (Nat.floor (u / h) : ℝ) + 1 := by
      exact_mod_cast hf
    have := (div_lt_iff₀ hh).1 hf'
    nlinarith
  have hnode : permutationFourierClosedTimeGrid h j = (k : ℝ) * h := by
    apply min_eq_left
    simpa [j] using hkh.trans hu1
  refine ⟨j, ?_⟩
  rw [hnode, abs_of_nonneg (sub_nonneg.mpr hkh)]
  linarith

theorem permutationFourierClosedTimeGrid_coverage_le (h u : ℝ) (hh : 0 < h)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ∃ j : Fin (permutationFourierClosedTimeGridCount h),
      |u - permutationFourierClosedTimeGrid h j| ≤ h := by
  obtain ⟨j, hj⟩ := permutationFourierClosedTimeGrid_coverage h u hh hu0 hu1
  exact ⟨j, hj.le⟩

/-- At an integer mesh boundary that is still inside the interval, the grid
contains the point exactly. -/
theorem permutationFourierClosedTimeGrid_mesh_boundary (h : ℝ) (n : ℕ)
    (hh : 0 < h) (hnh : (n : ℝ) * h ≤ 1 / 2) :
    ∃ j : Fin (permutationFourierClosedTimeGridCount h),
      permutationFourierClosedTimeGrid h j = (n : ℝ) * h := by
  have hn : n ≤ Nat.ceil ((1 / 2 : ℝ) / h) := by
    have hnreal : (n : ℝ) ≤ Nat.ceil ((1 / 2 : ℝ) / h) := by
      calc
        (n : ℝ) ≤ (1 / 2 : ℝ) / h := (le_div_iff₀ hh).2 hnh
        _ ≤ Nat.ceil ((1 / 2 : ℝ) / h) := Nat.le_ceil _
    exact_mod_cast hnreal
  refine ⟨⟨n, Nat.lt_succ_of_le (by
    simpa [permutationFourierClosedTimeGridCount] using hn)⟩, ?_⟩
  exact min_eq_left hnh

theorem permutationFourierClosedTimeGrid_card (h : ℝ) :
    (Finset.univ : Finset
      (Fin (permutationFourierClosedTimeGridCount h))).card =
        permutationFourierClosedTimeGridCount h := by
  simp

/-- For mesh `a/W`, with `W ≥ 1` and `a ≥ 1`, the closed-time grid has at most
`2W` nodes. -/
theorem permutationFourierClosedTimeGridCount_div_le_two_width
    (W : ℕ) (a : ℝ) (hW : 1 ≤ W) (ha : 1 ≤ a) :
    permutationFourierClosedTimeGridCount (a / (W : ℝ)) ≤ 2 * W := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have ha_pos : 0 < a := by linarith
  have hmesh : 0 < a / (W : ℝ) := div_pos ha_pos hWpos
  have hratio : (1 / 2 : ℝ) / (a / (W : ℝ)) ≤ (W : ℝ) := by
    rw [div_div]
    have hden : 0 < 2 * (a / (W : ℝ)) := by positivity
    apply (div_le_iff₀ hden).2
    field_simp [ne_of_gt hWpos]
    nlinarith [ha]
  have hceil : Nat.ceil ((1 / 2 : ℝ) / (a / (W : ℝ))) ≤ W := by
    exact Nat.ceil_le.mpr hratio
  dsimp [permutationFourierClosedTimeGridCount]
  omega

/-! Concrete mesh checks exercise the exact endpoint and clipped-final-node cases. -/

theorem permutationFourierClosedTimeGrid_half_step_count :
    permutationFourierClosedTimeGridCount (1 / 2 : ℝ) = 2 := by
  norm_num [permutationFourierClosedTimeGridCount]

theorem permutationFourierClosedTimeGrid_half_step_nodes :
    permutationFourierClosedTimeGrid (1 / 2 : ℝ) ⟨0, by norm_num
      [permutationFourierClosedTimeGridCount]⟩ = 0 ∧
    permutationFourierClosedTimeGrid (1 / 2 : ℝ) ⟨1, by norm_num
      [permutationFourierClosedTimeGridCount]⟩ = 1 / 2 := by
  constructor <;> norm_num [permutationFourierClosedTimeGrid,
    permutationFourierClosedTimeGridCount]

theorem permutationFourierClosedTimeGrid_third_step_count :
    permutationFourierClosedTimeGridCount (1 / 3 : ℝ) = 3 := by
  norm_num [permutationFourierClosedTimeGridCount]

theorem permutationFourierClosedTimeGrid_third_step_last_clipped :
    permutationFourierClosedTimeGrid (1 / 3 : ℝ) ⟨2, by norm_num
      [permutationFourierClosedTimeGridCount]⟩ = 1 / 2 := by
  norm_num [permutationFourierClosedTimeGrid,
    permutationFourierClosedTimeGridCount]

theorem permutationFourierClosedTimeGrid_coverage_endpoints (h : ℝ)
    (hh : 0 < h) :
    (∃ j : Fin (permutationFourierClosedTimeGridCount h),
      |(0 : ℝ) - permutationFourierClosedTimeGrid h j| ≤ h) ∧
    (∃ j : Fin (permutationFourierClosedTimeGridCount h),
      |(1 / 2 : ℝ) - permutationFourierClosedTimeGrid h j| ≤ h) := by
  constructor
  · exact permutationFourierClosedTimeGrid_coverage_le h 0 hh le_rfl (by norm_num)
  · exact permutationFourierClosedTimeGrid_coverage_le h (1 / 2) hh (by norm_num) le_rfl

#print axioms permutationFourierClosedTimeGrid_zero
#print axioms permutationFourierClosedTimeGrid_range
#print axioms permutationFourierClosedTimeGrid_last
#print axioms permutationFourierClosedTimeGrid_coverage
#print axioms permutationFourierClosedTimeGrid_coverage_le
#print axioms permutationFourierClosedTimeGrid_mesh_boundary
#print axioms permutationFourierClosedTimeGrid_card
#print axioms permutationFourierClosedTimeGridCount_div_le_two_width
#print axioms permutationFourierClosedTimeGrid_half_step_count
#print axioms permutationFourierClosedTimeGrid_half_step_nodes
#print axioms permutationFourierClosedTimeGrid_third_step_count
#print axioms permutationFourierClosedTimeGrid_third_step_last_clipped
#print axioms permutationFourierClosedTimeGrid_coverage_endpoints

end RBM.Gauss
