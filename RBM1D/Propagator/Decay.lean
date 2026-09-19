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

section NeZero

variable {ξ : ℂ}

theorem rho_pow_ne_one (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    rho ξ ^ n ≠ 1 := by
  intro h
  have h1 : ‖rho ξ‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  have h2 : ‖rho ξ‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg _) (norm_rho_lt_one hξ0 hξ) hn
  linarith

theorem rho_pow_sub_one_ne_zero (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    rho ξ ^ n - 1 ≠ 0 := sub_ne_zero_of_ne (rho_pow_ne_one hξ0 hξ hn)

end NeZero

section Pointwise

variable (L : ℕ) [NeZero L] {ξ : ℂ}

/-- The closed-form kernel as a function on `ZMod L`. -/
noncomputable def thetaKernel (L : ℕ) [NeZero L] (ξ : ℂ) (u : ZMod L) : ℂ :=
  kern L ξ u.val

/-- The defect of the homogeneous recursion at `n = 0`.  This single computation
is what pins down the constant `A(ξ)`. -/
theorem kern_defect (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    kern L ξ (L - 1) + kern L ξ 1 - cc ξ * kern L ξ 0 = -(3 / ξ) := by
  have hρ0 : rho ξ ≠ 0 := rho_ne_zero hξ0 hξ
  have hρ2 : rho ξ ^ 2 - 1 ≠ 0 := rho_pow_sub_one_ne_zero hξ0 hξ two_ne_zero
  have hρL : rho ξ ^ L - 1 ≠ 0 := rho_pow_sub_one_ne_zero hξ0 hξ (by omega)
  have hr : rho ξ ^ 2 + 1 = cc ξ * rho ξ := by linear_combination rho_eq ξ
  have h1 : L - (L - 1) = 1 := by omega
  have hLp : rho ξ ^ (L - 1) * rho ξ = rho ξ ^ L := by
    rw [← pow_succ]; congr 1; omega
  have bracket :
      (rho ξ ^ (L - 1) + rho ξ) + (rho ξ + rho ξ ^ (L - 1)) - cc ξ * (1 + rho ξ ^ L)
        = (1 - rho ξ ^ 2) * (rho ξ ^ L - 1) / rho ξ := by
    rw [← hLp]
    field_simp
    linear_combination (1 + rho ξ ^ (L - 1) * rho ξ) * hr
  calc kern L ξ (L - 1) + kern L ξ 1 - cc ξ * kern L ξ 0
      = AA L ξ * ((rho ξ ^ (L - 1) + rho ξ) + (rho ξ + rho ξ ^ (L - 1))
          - cc ξ * (1 + rho ξ ^ L)) := by
        simp only [kern, h1, Nat.sub_zero, pow_one, pow_zero]; ring
    _ = AA L ξ * ((1 - rho ξ ^ 2) * (rho ξ ^ L - 1) / rho ξ) := by rw [bracket]
    _ = -(3 / ξ) := by unfold AA; field_simp; ring

/-- The defining recursion of the propagator kernel, in the normalized form
`k(u-1) + k(u+1) - c k(u) = -(3/ξ) δ_{u,0}`.

Only `u = 0` is special: the wrap-around at `u.val = L - 1` is absorbed by
`kern_zero_eq_kern_L`. -/
theorem thetaKernel_rec (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (u : ZMod L) :
    thetaKernel L ξ (u - 1) + thetaKernel L ξ (u + 1) - cc ξ * thetaKernel L ξ u
      = if u = 0 then -(3 / ξ) else 0 := by
  have hlt : u.val < L := ZMod.val_lt u
  by_cases h0 : u = 0
  · subst h0
    rw [if_pos rfl]
    have hv : (0 : ZMod L).val = 0 := ZMod.val_zero
    have e1 : ((0 : ZMod L) - 1).val = L - 1 := val_sub_one_of_zero L hL hv
    have e2 : ((0 : ZMod L) + 1).val = 1 := by
      rw [val_add_one_of_lt L hL (u := 0) (by rw [hv]; omega), hv]
    simp only [thetaKernel, e1, e2, hv]
    exact kern_defect L hL hξ0 hξ
  · rw [if_neg h0]
    have hpos : 0 < u.val := Nat.pos_of_ne_zero fun h => h0 ((ZMod.val_eq_zero u).mp h)
    obtain ⟨m, hm⟩ : ∃ m, u.val = m + 1 := ⟨u.val - 1, by omega⟩
    have e1 : (u - 1).val = m := by rw [val_sub_one_of_pos L hL hpos, hm]; omega
    by_cases hd : u.val + 1 < L
    · have e2 : (u + 1).val = m + 2 := by
        rw [val_add_one_of_lt L hL hd, hm]
      have hrec := kern_rec L (ξ := ξ) (m := m) (by omega)
      simp only [thetaKernel, e1, e2, hm]
      linear_combination hrec
    · have hd' : u.val + 1 = L := by omega
      have h2 : m + 2 = L := by omega
      have e2 : (u + 1).val = 0 := val_add_one_of_top L hL hd'
      have hrec := kern_rec L (ξ := ξ) (m := m) (by omega)
      rw [h2] at hrec
      simp only [thetaKernel, e1, e2, hm]
      rw [kern_zero_eq_kern_L]
      linear_combination hrec

/-- The recursion, cleared of the division by `ξ`. -/
theorem thetaKernel_rec' (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (u : ZMod L) :
    ξ * (thetaKernel L ξ (u - 1) + thetaKernel L ξ (u + 1) - cc ξ * thetaKernel L ξ u)
      = if u = 0 then -3 else 0 := by
  rw [thetaKernel_rec L hL hξ0 hξ u]
  split_ifs
  · field_simp
  · ring

/-- The pointwise form of `(1 - ξ S^(B)) Θ = 1` for the closed-form kernel. -/
theorem thetaKernel_eq (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (u : ZMod L) :
    thetaKernel L ξ u
        - ξ * ((3 : ℂ)⁻¹ * (thetaKernel L ξ u + thetaKernel L ξ (u - 1) + thetaKernel L ξ (u + 1)))
      = if u = 0 then 1 else 0 := by
  have hrec := thetaKernel_rec' L hL hξ0 hξ u
  have hc : ξ * cc ξ = 3 - ξ := by unfold cc; field_simp
  by_cases h0 : u = 0
  · rw [if_pos h0] at hrec ⊢
    linear_combination (-(1 : ℂ) / 3) * hrec + (-(thetaKernel L ξ u) / 3) * hc
  · rw [if_neg h0] at hrec ⊢
    linear_combination (-(1 : ℂ) / 3) * hrec + (-(thetaKernel L ξ u) / 3) * hc

theorem circulant_mulVec_sbKernel (hL : 3 ≤ L) (k : ZMod L → ℂ) (u : ZMod L) :
    (Matrix.circulant k *ᵥ sbKernel L) u = (3 : ℂ)⁻¹ * (k u + k (u - 1) + k (u + 1)) := by
  have hsplit : ∀ v : ZMod L, k (u - v) * sbKernel L v
      = if v ∈ sbSupport L then k (u - v) * (3 : ℂ)⁻¹ else 0 := by
    intro v
    rw [sbKernel]
    split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hsplit]
  rw [Finset.sum_ite_mem, Finset.univ_inter, sum_over_sbSupport L hL]
  simp only [sub_zero, sub_neg_eq_add]
  ring

/-- **The closed form.** For `0 < ‖ξ‖ < 1`,
`(Θ_ξ)_{xy} = A(ξ) (ρ^d + ρ^{L-d})` with `d = (x - y).val`. -/
theorem theta_eq_circulant (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    Theta L ξ = Matrix.circulant (thetaKernel L ξ) := by
  refine (eq_Theta_of_mul L hL hξ ?_).symm
  have hmul : Matrix.circulant (thetaKernel L ξ) * SB L
      = Matrix.circulant (Matrix.circulant (thetaKernel L ξ) *ᵥ sbKernel L) := by
    rw [SB, Matrix.circulant_mul]
  rw [mul_sub, mul_one, Matrix.mul_smul, hmul, ← Matrix.circulant_smul,
    ← Matrix.circulant_sub, ← Matrix.circulant_single_one ℂ (ZMod L), Matrix.circulant_inj]
  funext u
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    circulant_mulVec_sbKernel L hL (thetaKernel L ξ) u, Pi.single_apply]
  exact thetaKernel_eq L hL hξ0 hξ u

theorem theta_apply_closed_form (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    Theta L ξ x y = AA L ξ * (rho ξ ^ (x - y).val + rho ξ ^ (L - (x - y).val)) := by
  rw [theta_eq_circulant L hL hξ0 hξ, Matrix.circulant_apply]
  rfl

/-- **Exponential decay from the closed form.**  Since `‖ρ(ξ)‖ < 1` and the
kernel is `A(ρ^d + ρ^{L-d})`, the entries decay like `‖ρ‖^{dist(x,y)}`, where the
distance is the graph distance `min(d, L-d)` on the cycle.

This is (2.52) up to identifying the rate: `1 - ‖ρ‖ ≍ |1 - ξ|^{1/2}`, so the
decay length is `min(|1-ξ|^{-1/2}, L)`, in contrast with the cruder bound of
`RBM1D.Propagator.Support`, whose rate is governed by `1 - ‖ξ‖`. -/
theorem norm_theta_apply_le_rho_pow (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    ‖Theta L ξ x y‖ ≤ 2 * ‖AA L ξ‖ * ‖rho ξ‖ ^ zdist L (x - y) := by
  have hr1 : ‖rho ξ‖ ≤ 1 := (norm_rho_lt_one hξ0 hξ).le
  have hr0 : (0 : ℝ) ≤ ‖rho ξ‖ := norm_nonneg _
  set d := (x - y).val with hd
  have hmin1 : zdist L (x - y) ≤ d := by
    rw [zdist]; exact min_le_left _ _
  have hmin2 : zdist L (x - y) ≤ L - d := by
    rw [zdist]; exact min_le_right _ _
  have e1 : ‖rho ξ‖ ^ d ≤ ‖rho ξ‖ ^ zdist L (x - y) :=
    pow_le_pow_of_le_one hr0 hr1 hmin1
  have e2 : ‖rho ξ‖ ^ (L - d) ≤ ‖rho ξ‖ ^ zdist L (x - y) :=
    pow_le_pow_of_le_one hr0 hr1 hmin2
  rw [theta_apply_closed_form L hL hξ0 hξ x y, norm_mul]
  calc ‖AA L ξ‖ * ‖rho ξ ^ d + rho ξ ^ (L - d)‖
      ≤ ‖AA L ξ‖ * (‖rho ξ‖ ^ d + ‖rho ξ‖ ^ (L - d)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖rho ξ ^ d + rho ξ ^ (L - d)‖
            ≤ ‖rho ξ ^ d‖ + ‖rho ξ ^ (L - d)‖ := norm_add_le _ _
          _ = ‖rho ξ‖ ^ d + ‖rho ξ‖ ^ (L - d) := by rw [norm_pow, norm_pow]
    _ ≤ 2 * ‖AA L ξ‖ * ‖rho ξ‖ ^ zdist L (x - y) := by nlinarith [norm_nonneg (AA L ξ)]

end Pointwise

section Rate

variable {ξ : ℂ}

/-- The inverse of the map `ξ ↦ ρ(ξ)`: `ξ (1 + ρ + ρ²) = 3ρ`. -/
theorem xi_mul_poly (hξ0 : ξ ≠ 0) : ξ * (1 + rho ξ + rho ξ ^ 2) = 3 * rho ξ := by
  have h := rho_eq ξ
  have hc : ξ * cc ξ = 3 - ξ := by unfold cc; field_simp
  linear_combination ξ * h + rho ξ * hc

/-- **The source of the square root in the decay length.**
`(1 - ξ) · 3ρ = ξ (1 - ρ)²`, i.e. `1 - ξ = (1-ρ)² / (1 + ρ + ρ²)`.

`ξ = 1` corresponds to `ρ = 1`, and it is a *double* zero.  That is exactly why
the decay length `1/(1 - ρ)` scales like `|1 - ξ|^{-1/2}` rather than
`|1 - ξ|^{-1}`, and it is an exact identity, not an asymptotic one. -/
theorem one_sub_xi_mul (hξ0 : ξ ≠ 0) : (1 - ξ) * (3 * rho ξ) = ξ * (1 - rho ξ) ^ 2 := by
  linear_combination (-(1 : ℂ)) * xi_mul_poly hξ0

/-- The identity above, in norms. -/
theorem norm_one_sub_rho_sq (hξ0 : ξ ≠ 0) :
    ‖ξ‖ * ‖1 - rho ξ‖ ^ 2 = 3 * ‖1 - ξ‖ * ‖rho ξ‖ := by
  have h := one_sub_xi_mul hξ0
  have := congrArg (‖·‖) h
  simpa [norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using this.symm

/-- `ρ(ξ) → 1` as `ξ → 1`, quantitatively: `‖1 - ρ‖² ≤ 3 ‖1 - ξ‖ / ‖ξ‖`. -/
theorem norm_one_sub_rho_le (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    ‖ξ‖ * ‖1 - rho ξ‖ ^ 2 ≤ 3 * ‖1 - ξ‖ := by
  rw [norm_one_sub_rho_sq hξ0]
  have h1 : ‖rho ξ‖ ≤ 1 := (norm_rho_lt_one hξ0 hξ).le
  have h2 : (0 : ℝ) ≤ 3 * ‖1 - ξ‖ := by positivity
  nlinarith [norm_nonneg (1 - ξ)]

end Rate

end RBM
