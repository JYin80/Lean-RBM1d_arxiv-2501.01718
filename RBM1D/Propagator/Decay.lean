/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Root
import RBM1D.Defs.Dist

/-!
# The closed form of the propagator, towards (2.52)

For the nearest-neighbour `S^(B)` in `d = 1` the circulant inverse
`Θ_ξ = (1 - ξ S^(B))⁻¹` has a closed form in terms of the characteristic root
`ρ(ξ)` of `RBM1D.Propagator.Root`:

  `(Θ_ξ)_{xy} = A(ξ) (ρ^d + ρ^{L-d})`,  `d = (x - y).val`,
  `A(ξ) = 3ρ / [ξ (ρ^L - 1)(ρ² - 1)]`.

This file builds the pieces: the arithmetic of `val` under `±1` on `ZMod L`, and
the homogeneous three-term recursion satisfied by `n ↦ ρ^n + ρ^{L-n}` on the
range `0 ≤ n ≤ L`.

The symmetric shape `ρ^n + ρ^{L-n}` is not cosmetic: it is exactly what makes
the wrap-around at `d = L-1` work, because the formula at `n = L` agrees with
the formula at `n = 0`.  Only `d = 0` is then a genuinely special case, and the
defect there is what pins down the constant `A(ξ)`.
-/

namespace RBM

open Matrix

section Val

variable (L : ℕ) [NeZero L]

theorem val_one_eq (hL : 3 ≤ L) : (1 : ZMod L).val = 1 := by
  have h : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
  simpa using h

theorem val_neg_one_eq (hL : 3 ≤ L) : (-1 : ZMod L).val = L - 1 := by
  rw [ZMod.neg_val, if_neg (one_ne_zero_zmod L hL), val_one_eq L hL]

theorem val_add_one (hL : 3 ≤ L) (u : ZMod L) : (u + 1).val = (u.val + 1) % L := by
  rw [ZMod.val_add, val_one_eq L hL]

theorem val_sub_one (hL : 3 ≤ L) (u : ZMod L) : (u - 1).val = (u.val + (L - 1)) % L := by
  rw [sub_eq_add_neg, ZMod.val_add, val_neg_one_eq L hL]

theorem val_add_one_of_lt (hL : 3 ≤ L) {u : ZMod L} (h : u.val + 1 < L) :
    (u + 1).val = u.val + 1 := by
  rw [val_add_one L hL, Nat.mod_eq_of_lt h]

theorem val_add_one_of_top (hL : 3 ≤ L) {u : ZMod L} (h : u.val + 1 = L) :
    (u + 1).val = 0 := by
  rw [val_add_one L hL, h, Nat.mod_self]

theorem val_sub_one_of_pos (hL : 3 ≤ L) {u : ZMod L} (h : 0 < u.val) :
    (u - 1).val = u.val - 1 := by
  have hlt : u.val < L := ZMod.val_lt u
  rw [val_sub_one L hL]
  have : u.val + (L - 1) = L + (u.val - 1) := by omega
  rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem val_sub_one_of_zero (hL : 3 ≤ L) {u : ZMod L} (h : u.val = 0) :
    (u - 1).val = L - 1 := by
  rw [val_sub_one L hL, h, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

end Val

section Kernel

variable (L : ℕ) {ξ : ℂ}

/-- The constant in the closed form, `A(ξ) = 3ρ / [ξ (ρ^L - 1)(ρ² - 1)]`. -/
noncomputable def AA (L : ℕ) (ξ : ℂ) : ℂ :=
  3 * rho ξ / (ξ * (rho ξ ^ L - 1) * (rho ξ ^ 2 - 1))

/-- The closed-form kernel as a function of the representative `n ∈ [0, L]`. -/
noncomputable def kern (L : ℕ) (ξ : ℂ) (n : ℕ) : ℂ :=
  AA L ξ * (rho ξ ^ n + rho ξ ^ (L - n))

/-- At the two ends the kernel agrees: `kern L ξ 0 = kern L ξ L`.  This is what
makes the wrap-around at `d = L - 1` work. -/
theorem kern_zero_eq_kern_L : kern L ξ 0 = kern L ξ L := by
  unfold kern
  rw [Nat.sub_zero, Nat.sub_self, pow_zero]
  ring

/-- The homogeneous three-term recursion, valid whenever `m + 2 ≤ L`. -/
theorem kern_rec {m : ℕ} (hm : m + 2 ≤ L) :
    kern L ξ m + kern L ξ (m + 2) = cc ξ * kern L ξ (m + 1) := by
  obtain ⟨j, hj⟩ : ∃ j, L - m = j + 2 := ⟨L - m - 2, by omega⟩
  have h1 : L - (m + 1) = j + 1 := by omega
  have h2 : L - (m + 2) = j := by omega
  have hr : rho ξ ^ 2 + 1 = cc ξ * rho ξ := by linear_combination rho_eq ξ
  unfold kern
  rw [hj, h1, h2]
  linear_combination (AA L ξ * (rho ξ ^ m + rho ξ ^ j)) * hr

end Kernel

end RBM
