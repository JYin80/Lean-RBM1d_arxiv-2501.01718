/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Block

/-!
# Graph distance on the cycle `ZMod L`

The paper writes `dist_{ZMod L}(a,b)` and `‖a - b‖` for the graph distance on the
cycle of length `L`, i.e. `min(|a-b|, L - |a-b|)`.  This file introduces it as
`RBM.zdist` and proves the facts needed to see that `S^(B)` is a band matrix.
-/

namespace RBM

variable (L : ℕ) [NeZero L]

/-- Graph distance from `u` to `0` on the cycle `ZMod L`. -/
def zdist (u : ZMod L) : ℕ := min u.val (L - u.val)

omit [NeZero L] in
@[simp] theorem zdist_zero : zdist L 0 = 0 := by
  simp [zdist]

omit [NeZero L] in
theorem ne_zero_of_zdist_ne_zero {u : ZMod L} (h : zdist L u ≠ 0) : u ≠ 0 := by
  intro hu
  rw [hu, zdist_zero] at h
  exact h rfl

theorem zdist_add_le (u v : ZMod L) : zdist L (u + v) ≤ zdist L u + zdist L v := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hu : u.val < L := ZMod.val_lt u
  have hv : v.val < L := ZMod.val_lt v
  have hadd : (u + v).val = (u.val + v.val) % L := ZMod.val_add u v
  rcases lt_or_ge (u.val + v.val) L with h | h
  · rw [Nat.mod_eq_of_lt h] at hadd
    simp only [zdist, hadd]
    omega
  · have hmod : (u.val + v.val) % L = u.val + v.val - L := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hadd
    simp only [zdist, hadd]
    omega

omit [NeZero L] in
theorem zdist_one_le (hL : 3 ≤ L) : zdist L (1 : ZMod L) ≤ 1 := by
  have hval : (1 : ZMod L).val = 1 := by
    have : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
    simpa using this
  simp only [zdist, hval]
  omega

theorem zdist_neg_one_le (hL : 3 ≤ L) : zdist L (-1 : ZMod L) ≤ 1 := by
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hval : (1 : ZMod L).val = 1 := by
    have : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
    simpa using this
  have hneg : (-1 : ZMod L).val = L - 1 := by
    rw [ZMod.neg_val, ite_eq_right h1, hval]
  simp only [zdist, hneg]
  omega

/-- `S^(B)` is supported on the nearest-neighbour band. -/
theorem zdist_le_one_of_mem_sbSupport (hL : 3 ≤ L) {u : ZMod L} (h : u ∈ sbSupport L) :
    zdist L u ≤ 1 := by
  simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h
  · simp [h]
  · rw [h]; exact zdist_one_le L hL
  · rw [h]; exact zdist_neg_one_le L hL

theorem sbKernel_eq_zero (hL : 3 ≤ L) {u : ZMod L} (h : 1 < zdist L u) : sbKernel L u = 0 := by
  rw [sbKernel, ite_eq_right]
  intro hmem
  exact absurd (zdist_le_one_of_mem_sbSupport L hL hmem) (by omega)

theorem SB_apply_eq_zero (hL : 3 ≤ L) {x y : ZMod L} (h : 1 < zdist L (x - y)) :
    SB L x y = 0 := by
  rw [SB_apply]
  exact sbKernel_eq_zero L hL h

end RBM
