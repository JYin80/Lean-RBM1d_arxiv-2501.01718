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

/-- `(1 − ρ)² = (1 − ξ)(1 + ρ + ρ²)`, the form used for the two-sided bound. -/
theorem one_sub_rho_sq (hξ0 : ξ ≠ 0) :
    (1 - rho ξ) ^ 2 = (1 - ξ) * (1 + rho ξ + rho ξ ^ 2) := by
  apply mul_left_cancel₀ hξ0
  have h := xi_mul_poly hξ0
  have h2 := one_sub_xi_mul hξ0
  linear_combination (-1 : ℂ) * h2 - (1 - ξ) * h

end Rate

section Geom

/-! ### An elementary lower bound for `1 - r^L`

The prefactor of (2.52) is `1/(|1-ξ| ℓ̂)` with `ℓ̂ = min(|1-ξ|^{-1/2}, L)`, and the
`ℓ̂` in it comes entirely from the factor `1 - ρ^L` in `AA_eq`: it interpolates
between `1` (when `L(1-ρ) ≳ 1`) and `L(1-ρ)` (when `L(1-ρ) ≲ 1`).  The
following two lemmas are that interpolation, with no exponentials: Bernoulli
`1 + Lx ≤ (1+x)^L` plus `(1-x)(1+x) ≤ 1` give `(1-x)^L (1 + Lx) ≤ 1`. -/

theorem pow_mul_one_add_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (L : ℕ) :
    (1 - x) ^ L * (1 + L * x) ≤ 1 := by
  have h1 : (1 : ℝ) + L * x ≤ (1 + x) ^ L := one_add_mul_le_pow (by linarith) L
  have h2 : (0 : ℝ) ≤ (1 - x) ^ L := pow_nonneg (by linarith) L
  calc (1 - x) ^ L * (1 + L * x) ≤ (1 - x) ^ L * (1 + x) ^ L :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = ((1 - x) * (1 + x)) ^ L := (mul_pow _ _ _).symm
    _ = (1 - x ^ 2) ^ L := by ring_nf
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- `1 - r^L ≥ L(1-r) / (1 + L(1-r))`.  The right-hand side is `≍ min(1, L(1-r))`. -/
theorem le_one_sub_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (L : ℕ) :
    (L : ℝ) * (1 - r) / (1 + L * (1 - r)) ≤ 1 - r ^ L := by
  have hx0 : (0 : ℝ) ≤ 1 - r := by linarith
  have hd : (0 : ℝ) < 1 + L * (1 - r) := by positivity
  rw [div_le_iff₀ hd]
  have h := pow_mul_one_add_le hx0 (by linarith) L
  have hr : (1 : ℝ) - (1 - r) = r := by ring
  rw [hr] at h
  nlinarith [h]

end Geom

section Constant

variable {L : ℕ} {ξ : ℂ}

/-- **The constant `A(ξ)` in simplified form.**

Substituting the identity `(1-ξ)·3ρ = ξ(1-ρ)²` of `one_sub_xi_mul` into
`A = 3ρ / [ξ(ρ^L-1)(ρ²-1)]` cancels one power of `1-ρ` against the factor
`ρ² - 1 = (ρ-1)(ρ+1)` and turns the `1/ξ` into a `1/(1-ξ)`:

  `A(ξ) = (1 - ρ) / [(1 - ξ)(1 - ρ^L)(1 + ρ)]`.

This is the form that makes `(2.52)` readable.  In the long-edge regime the
three factors downstairs are, in order, the `|1-ξ|` of the denominator of
(2.52), the factor that interpolates between `1` and `L(1-ρ)` -- i.e. the
`ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)` -- and a harmless `1 + ρ ≈ 2`.  The `1 - ρ`
upstairs is of size `|1-ξ|^{1/2}` by `rho_real_bounds`. -/
theorem AA_eq (hL : L ≠ 0) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    AA L ξ = (1 - rho ξ) / ((1 - ξ) * (1 - rho ξ ^ L) * (1 + rho ξ)) := by
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hρ1 : rho ξ ≠ 1 := by
    intro h; rw [h, norm_one] at hnr; exact absurd hnr (lt_irrefl 1)
  have hρm1 : 1 + rho ξ ≠ 0 := by
    intro h
    have : rho ξ = -1 := by linear_combination h
    rw [this] at hnr
    simp at hnr
  have hρL : 1 - rho ξ ^ L ≠ 0 := by
    intro h
    exact rho_pow_sub_one_ne_zero hξ0 hξ hL (by linear_combination -h)
  have hρL' : rho ξ ^ L - 1 ≠ 0 := rho_pow_sub_one_ne_zero hξ0 hξ hL
  have hρ2 : rho ξ ^ 2 - 1 ≠ 0 := rho_pow_sub_one_ne_zero hξ0 hξ two_ne_zero
  have hξ1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ; exact absurd hξ (lt_irrefl 1)
  unfold AA
  rw [div_eq_div_iff (by simp [hξ0, hρL', hρ2]) (by simp [hξ1, hρL, hρm1])]
  linear_combination ((1 - rho ξ ^ L) * (1 + rho ξ)) * one_sub_xi_mul hξ0

end Constant

section RealXi

/-! ### Real spectral parameter

For `ξ = t` real with `0 < t < 1` — the *long edge* `ξ = t|m|²` of the paper,
where `|m| = 1` makes `ξ` real — the discriminant is a positive real, so both
roots are real and `ρ ∈ (0,1)`.  Then `1 - ‖ρ‖ = 1 - ρ` and the identity
`(1-ρ)² = (1-ξ)(1+ρ+ρ²)` with `1 < 1+ρ+ρ² < 3` gives the two-sided bound

  `√(1-t) ≤ 1 - ρ ≤ √3 · √(1-t)`,

i.e. the decay length is exactly of order `(1-t)^{-1/2}`, as in (2.52). -/

/-- A complex number whose square is a positive real is itself real. -/
theorem im_eq_zero_of_sq_eq_real {w : ℂ} {r : ℝ} (hr : 0 < r) (h : w ^ 2 = (r : ℂ)) :
    w.im = 0 := by
  by_contra him
  have h1 : (w ^ 2).im = 0 := by rw [h]; simp
  have h2 : (w ^ 2).re = r := by rw [h]; simp
  rw [pow_two, Complex.mul_im] at h1
  rw [pow_two, Complex.mul_re] at h2
  have hre : w.re = 0 := by
    have : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' him
  rw [hre] at h2
  nlinarith [sq_nonneg w.im]

theorem cc_ofReal {t : ℝ} (ht : t ≠ 0) : cc (t : ℂ) = ((3 / t - 1 : ℝ) : ℂ) := by
  unfold cc
  push_cast
  ring

theorem exists_real_of_im_eq_zero {z : ℂ} (h : z.im = 0) : ∃ r : ℝ, z = (r : ℂ) :=
  ⟨z.re, Complex.ext rfl (by simp [h])⟩

/-- **The two-sided bound on the decay rate for real spectral parameter.**
For `0 < t < 1`, `ρ(t)` is a real number in `(0,1)` and

  `√(1-t) ≤ 1 - ρ(t) ≤ √3 · √(1-t)`.

So the decay length `1/(1 - ρ)` is of order `(1-t)^{-1/2}`, exactly the
`ℓ̂(ξ) = |1-ξ|^{-1/2}` of (2.52).  The lower bound on `1 - ρ` is what the decay
estimate needs; it is available here because `ρ` is real, so `1 - ‖ρ‖ = 1 - ρ`.

This is the long-edge case `ξ = t|m|²` of the paper: `|m| = 1` makes `ξ` real. -/
theorem rho_real_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ r : ℝ, rho (t : ℂ) = (r : ℂ) ∧ 0 < r ∧ r < 1 ∧
      Real.sqrt (1 - t) ≤ 1 - r ∧ 1 - r ≤ Real.sqrt 3 * Real.sqrt (1 - t) := by
  have htne' : t ≠ 0 := ne_of_gt ht0
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htne'
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  have hcgt : (3 : ℝ) / t - 1 > 2 := by
    have : (3 : ℝ) / t > 3 := by rw [gt_iff_lt, lt_div_iff₀ ht0]; linarith
    linarith
  -- the discriminant is a positive real, so `disc` is real, hence so is `ρ`
  have hdpos : 0 < (3 / t - 1 : ℝ) ^ 2 - 4 := by nlinarith
  have hdi : (disc (t : ℂ)).im = 0 := by
    refine im_eq_zero_of_sq_eq_real hdpos ?_
    rw [disc_sq, cc_ofReal htne']
    push_cast
    ring
  obtain ⟨d, hd⟩ := exists_real_of_im_eq_zero hdi
  obtain ⟨c0, hc0⟩ := exists_real_of_im_eq_zero
    (show (cc (t : ℂ)).im = 0 by rw [cc_ofReal htne']; simp)
  have h1 : root1 (t : ℂ) = (((c0 + d) / 2 : ℝ) : ℂ) := by
    unfold root1; rw [hc0, hd]; push_cast; ring
  have h2 : root2 (t : ℂ) = (((c0 - d) / 2 : ℝ) : ℂ) := by
    unfold root2; rw [hc0, hd]; push_cast; ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, rho (t : ℂ) = (r : ℂ) := by
    unfold rho; split_ifs
    · exact ⟨_, h1⟩
    · exact ⟨_, h2⟩
  -- the division-free characteristic relation, in reals
  have hpoly : t * (1 + r + r ^ 2) = 3 * r := by
    have h := xi_mul_poly htne
    rw [hr] at h
    exact_mod_cast h
  have hquad : 0 < 1 + r + r ^ 2 := by nlinarith [sq_nonneg (r + 1), sq_nonneg r]
  have hrpos : 0 < r := by nlinarith
  have habs : |r| < 1 := by
    have := norm_rho_lt_one htne hnorm
    rwa [hr, Complex.norm_real, Real.norm_eq_abs] at this
  have hrlt : r < 1 := (abs_lt.mp habs).2
  have hsq : (1 - r) ^ 2 = (1 - t) * (1 + r + r ^ 2) := by
    apply mul_left_cancel₀ htne'
    linear_combination t * hpoly
  have h1t : 0 < 1 - t := by linarith
  have h3 : 1 + r + r ^ 2 ≤ 3 := by nlinarith
  have h1le : (1 : ℝ) ≤ 1 + r + r ^ 2 := by nlinarith
  have hlow : 1 - t ≤ (1 - r) ^ 2 := by
    rw [hsq]; nlinarith [mul_le_mul_of_nonneg_left h1le h1t.le]
  have hhigh : (1 - r) ^ 2 ≤ 3 * (1 - t) := by
    rw [hsq]; nlinarith [mul_le_mul_of_nonneg_left h3 h1t.le]
  have hpos : 0 < 1 - r := by linarith
  refine ⟨r, hr, hrpos, hrlt, ?_, ?_⟩
  · calc Real.sqrt (1 - t) ≤ Real.sqrt ((1 - r) ^ 2) := Real.sqrt_le_sqrt hlow
      _ = 1 - r := Real.sqrt_sq hpos.le
  · calc 1 - r = Real.sqrt ((1 - r) ^ 2) := (Real.sqrt_sq hpos.le).symm
      _ ≤ Real.sqrt (3 * (1 - t)) := Real.sqrt_le_sqrt hhigh
      _ = Real.sqrt 3 * Real.sqrt (1 - t) := Real.sqrt_mul (by norm_num) _

end RealXi

section EllHat

/-! ### The decay length `ℓ̂(ξ)` and the bound on the constant

`ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)` is the length scale of (2.52).  In the closed form
it is produced entirely by the factor `1 - ρ^L` of `AA_eq`.  We prove the
prefactor bound `‖A(ξ)‖ ≤ 4 / (|1-ξ| ℓ̂(ξ))` for real `ξ = t ∈ (0,1)`, which is
the long-edge case `ξ = t|m|²` of the paper. -/

/-- `ℓ̂(ξ) = min(|1 - ξ|^{-1/2}, L)`, the decay length of (2.52). -/
noncomputable def ellHat (L : ℕ) (ξ : ℂ) : ℝ := min (1 / Real.sqrt ‖1 - ξ‖) (L : ℝ)

theorem ellHat_ofReal (L : ℕ) {t : ℝ} (ht1 : t < 1) :
    ellHat L (t : ℂ) = min (1 / Real.sqrt (1 - t)) (L : ℝ) := by
  have h : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [ellHat, h]

/-- **The core inequality behind the prefactor of (2.52).**
`ℓ̂ · (1 - ρ) ≤ 4 (1 - ρ^L)`.  Both regimes of the `min` are used:

* `ℓ̂ = L`: then `L√(1-t) ≤ 1`, so `y := L(1-ρ) ≤ √3 · L√(1-t) ≤ √3 ≤ 3`,
  and `1 - ρ^L ≥ y/(1+y) ≥ y/4`.
* `ℓ̂ = (1-t)^{-1/2}`: then `L√(1-t) ≥ 1`, so `y ≥ 1` and `1 - ρ^L ≥ 1/2`,
  while the left-hand side is `(1-ρ)/√(1-t) ≤ √3 ≤ 2`. -/
theorem ellHat_mul_one_sub_le {t r : ℝ} (ht1 : t < 1) {L : ℕ} (hL : 1 ≤ L)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hlow : Real.sqrt (1 - t) ≤ 1 - r) (hhigh : 1 - r ≤ Real.sqrt 3 * Real.sqrt (1 - t)) :
    min (1 / Real.sqrt (1 - t)) (L : ℝ) * (1 - r) ≤ 4 * (1 - r ^ L) := by
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have h3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hLpos : (0:ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hpow1 : r ^ L ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hgeom := le_one_sub_pow hr0.le hr1.le L
  have h1 : (L : ℝ) * (1 - r) ≤ (1 - r ^ L) * (1 + (L : ℝ) * (1 - r)) := by
    rw [div_le_iff₀ (by nlinarith)] at hgeom
    linarith
  rcases le_total ((L : ℝ)) (1 / Real.sqrt (1 - t)) with hcase | hcase
  · rw [min_eq_right hcase]
    have hLs : (L : ℝ) * Real.sqrt (1 - t) ≤ 1 := (le_div_iff₀ hs).mp hcase
    have hy3 : (L : ℝ) * (1 - r) ≤ 3 := by
      have hstep : (L : ℝ) * (1 - r) ≤ (L : ℝ) * (Real.sqrt 3 * Real.sqrt (1 - t)) :=
        mul_le_mul_of_nonneg_left hhigh hLpos
      nlinarith [Real.sqrt_nonneg 3, mul_nonneg hLpos hs.le]
    nlinarith [h1, hpow1]
  · rw [min_eq_left hcase]
    have hLs : (1 : ℝ) ≤ (L : ℝ) * Real.sqrt (1 - t) := (div_le_iff₀ hs).mp hcase
    have hy1 : (1 : ℝ) ≤ (L : ℝ) * (1 - r) :=
      le_trans hLs (mul_le_mul_of_nonneg_left hlow hLpos)
    have hu : (1 : ℝ) / 2 ≤ 1 - r ^ L := by nlinarith [h1, hy1]
    have hleft : 1 / Real.sqrt (1 - t) * (1 - r) ≤ 2 := by
      rw [one_div, inv_mul_eq_div, div_le_iff₀ hs]
      nlinarith [hs.le]
    linarith

/-- **The prefactor of (2.52), for real `ξ = t ∈ (0,1)`.**
`‖A(t)‖ ≤ 4 / ((1-t) · ℓ̂(t))`. -/
theorem norm_AA_le_of_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {L : ℕ} (hL : 3 ≤ L) :
    ‖AA L (t : ℂ)‖ ≤ 4 / ((1 - t) * ellHat L (t : ℂ)) := by
  obtain ⟨r, hrho, hr0, hr1, hlow, hhigh⟩ := rho_real_bounds ht0 ht1
  have htne' : t ≠ 0 := ne_of_gt ht0
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htne'
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  have hL0 : L ≠ 0 := by omega
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hrL : r ^ L < 1 := pow_lt_one₀ hr0.le hr1 hL0
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hAA : AA L (t : ℂ) = (((1 - r) / ((1 - t) * (1 - r ^ L) * (1 + r)) : ℝ) : ℂ) := by
    rw [AA_eq hL0 htne hnorm, hrho]; push_cast; ring
  have hdenpos : (0 : ℝ) < (1 - t) * (1 - r ^ L) * (1 + r) :=
    mul_pos (mul_pos h1t (by linarith)) (by linarith)
  have hell : (0 : ℝ) < min (1 / Real.sqrt (1 - t)) (L : ℝ) := by
    refine lt_min (by positivity) ?_
    exact_mod_cast Nat.pos_of_ne_zero hL0
  have key := ellHat_mul_one_sub_le ht1 (by omega : 1 ≤ L) hr0 hr1 hlow hhigh
  rw [hAA, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by linarith) hdenpos), ellHat_ofReal L ht1,
    div_le_div_iff₀ hdenpos (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key h1t.le,
    mul_nonneg (mul_nonneg h1t.le (sub_nonneg.mpr hrL.le)) hr0.le]

end EllHat

section Decay52

variable {L : ℕ} [NeZero L]

theorem zdist_le (u : ZMod L) : zdist L u ≤ L :=
  le_trans (min_le_left _ _) (ZMod.val_lt u).le

/-- **Lemma 2.14 (4) / equation (2.52), for real `ξ = t ∈ (0,1)`.**

`|(Θ_t)_{xy}| ≤ C · exp(-‖x-y‖ / ℓ̂(t)) / ((1-t) · ℓ̂(t))` with `C = 8e` and `c = 1`,
where `ℓ̂(t) = min((1-t)^{-1/2}, L)` and `‖x-y‖` is the distance on the cycle.

This is the long-edge case `ξ = t|m|² = t` of the paper (`|m| = 1` makes `ξ` real),
which is the case that needs the sharp length scale.  Two regimes:

* `(1-t)^{-1/2} ≤ L`: the exponential does the work, because
  `ρ ≤ e^{-(1-ρ)} ≤ e^{-√(1-t)} = e^{-1/ℓ̂}`;
* `L ≤ (1-t)^{-1/2}`: the exponential is useless (`e^{-d/L} ≥ e^{-1}` for `d ≤ L`)
  and the prefactor `‖A‖ ≤ 4/((1-t)L)` carries the estimate on its own.

No contour shift and no Poisson summation: the closed form plus `1 - ρ ≍ √(1-t)`. -/
theorem norm_Theta_apply_le_of_real (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x y : ZMod L) :
    ‖Theta L (t : ℂ) x y‖ ≤
      8 * Real.exp 1 * Real.exp (-(zdist L (x - y) : ℝ) / ellHat L (t : ℂ)) /
        ((1 - t) * ellHat L (t : ℂ)) := by
  obtain ⟨r, hrho, hr0, hr1, hlow, hhigh⟩ := rho_real_bounds ht0 ht1
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by omega
    exact_mod_cast this
  set d := zdist L (x - y) with hd
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast zdist_le (x - y)
  have hell : ellHat L (t : ℂ) = min (1 / Real.sqrt (1 - t)) (L : ℝ) := ellHat_ofReal L ht1
  have hellpos : 0 < ellHat L (t : ℂ) := by
    rw [hell]; exact lt_min (by positivity) hLpos
  have hnr : ‖rho (t : ℂ)‖ = r := by
    rw [hrho, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  -- `ρ^d ≤ e · exp(-d/ℓ̂)`
  have hrd : r ^ d ≤ Real.exp (-(d : ℝ) * (1 - r)) := by
    have hre : r ≤ Real.exp (-(1 - r)) := by
      have := Real.add_one_le_exp (-(1 - r)); linarith
    calc r ^ d ≤ Real.exp (-(1 - r)) ^ d := pow_le_pow_left₀ hr0.le hre d
      _ = Real.exp ((d : ℝ) * -(1 - r)) := (Real.exp_nat_mul _ d).symm
      _ = Real.exp (-(d : ℝ) * (1 - r)) := by ring_nf
  have step3 : r ^ d ≤ Real.exp 1 * Real.exp (-(d : ℝ) / ellHat L (t : ℂ)) := by
    rcases le_total (1 / Real.sqrt (1 - t)) ((L : ℝ)) with hcase | hcase
    · rw [hell, min_eq_left hcase]
      have hx : -(d : ℝ) / (1 / Real.sqrt (1 - t)) = -(d : ℝ) * Real.sqrt (1 - t) := by
        field_simp
      rw [hx]
      calc r ^ d ≤ Real.exp (-(d : ℝ) * (1 - r)) := hrd
        _ ≤ Real.exp (-(d : ℝ) * Real.sqrt (1 - t)) := by
            refine Real.exp_le_exp.mpr ?_
            nlinarith [mul_le_mul_of_nonneg_left hlow hdnn]
        _ = 1 * Real.exp (-(d : ℝ) * Real.sqrt (1 - t)) := (one_mul _).symm
        _ ≤ Real.exp 1 * Real.exp (-(d : ℝ) * Real.sqrt (1 - t)) :=
            mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
    · rw [hell, min_eq_right hcase]
      have hratio : (d : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hLpos).mpr hdL
      have hexp : Real.exp (-1 : ℝ) ≤ Real.exp (-(d : ℝ) / (L : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [neg_div]; linarith
      calc r ^ d ≤ 1 := pow_le_one₀ hr0.le hr1.le
        _ = Real.exp 1 * Real.exp (-1 : ℝ) := by
            rw [← Real.exp_add]; norm_num
        _ ≤ Real.exp 1 * Real.exp (-(d : ℝ) / (L : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos 1).le
  -- assemble
  have step2 := norm_AA_le_of_real ht0 ht1 hL
  have hdenpos : (0 : ℝ) < (1 - t) * ellHat L (t : ℂ) := mul_pos h1t hellpos
  calc ‖Theta L (t : ℂ) x y‖ ≤ 2 * ‖AA L (t : ℂ)‖ * ‖rho (t : ℂ)‖ ^ d :=
        norm_theta_apply_le_rho_pow L hL htne hnorm x y
    _ = 2 * ‖AA L (t : ℂ)‖ * r ^ d := by rw [hnr]
    _ ≤ 2 * (4 / ((1 - t) * ellHat L (t : ℂ))) *
          (Real.exp 1 * Real.exp (-(d : ℝ) / ellHat L (t : ℂ))) := by
        refine mul_le_mul (by linarith) step3 (pow_nonneg hr0.le d) ?_
        positivity
    _ = 8 * Real.exp 1 * Real.exp (-(d : ℝ) / ellHat L (t : ℂ)) /
          ((1 - t) * ellHat L (t : ℂ)) := by
        field_simp
        ring

end Decay52

section Differences

variable {L : ℕ} {ξ : ℂ}

/-! ### (2.53)(2.54): the differences of the closed-form kernel

Writing `L = n + 1 + j`, so that the two exponents of `kern` at `n` are `n` and
`j + 1`, the differences telescope against the factor `1 - ρ`:

* first difference  → one factor `1 - ρ`, hence `≍ |1-ξ|^{1/2}`;
* second difference → two factors, hence `≍ |1-ξ|`.

That is the whole content of (2.53) and (2.54): each lattice difference costs
exactly one power of `1 - ρ ≍ |1-ξ|^{1/2}`, i.e. one inverse decay length. -/

/-- The first difference of the kernel. -/
theorem kern_succ_sub (n j : ℕ) (hL : L = n + 1 + j) :
    kern L ξ (n + 1) - kern L ξ n = AA L ξ * (1 - rho ξ) * (rho ξ ^ j - rho ξ ^ n) := by
  subst hL
  have e1 : n + 1 + j - (n + 1) = j := by omega
  have e2 : n + 1 + j - n = j + 1 := by omega
  unfold kern
  rw [e1, e2]
  ring

/-- The second difference of the kernel. -/
theorem kern_second_diff (m j : ℕ) (hL : L = m + 2 + j) :
    kern L ξ (m + 2) + kern L ξ m - 2 * kern L ξ (m + 1)
      = AA L ξ * (1 - rho ξ) ^ 2 * (rho ξ ^ m + rho ξ ^ j) := by
  subst hL
  have e1 : m + 2 + j - (m + 2) = j := by omega
  have e2 : m + 2 + j - m = j + 2 := by omega
  have e3 : m + 2 + j - (m + 1) = j + 1 := by omega
  unfold kern
  rw [e1, e2, e3]
  ring

/-- **The cost of one lattice difference**: `‖A(1-ρ)‖ ≤ 4√3 / (ℓ̂ · √(1-t))`.
This is the right-hand side of (2.53). -/
theorem norm_AA_mul_one_sub_rho_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hL : 3 ≤ L) :
    ‖AA L (t : ℂ) * (1 - rho (t : ℂ))‖ ≤
      4 * Real.sqrt 3 / (ellHat L (t : ℂ) * Real.sqrt (1 - t)) := by
  obtain ⟨r, hrho, hr0, hr1, hlow, hhigh⟩ := rho_real_bounds ht0 ht1
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hsq : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t := Real.mul_self_sqrt h1t.le
  have hell : 0 < ellHat L (t : ℂ) := by
    rw [ellHat_ofReal L ht1]
    refine lt_min (by positivity) ?_
    have : 0 < L := by omega
    exact_mod_cast this
  have hA := norm_AA_le_of_real ht0 ht1 hL
  have hApos : (0 : ℝ) ≤ ‖AA L (t : ℂ)‖ := norm_nonneg _
  have hrn : ‖1 - rho (t : ℂ)‖ = 1 - r := by
    rw [hrho, show (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [norm_mul, hrn]
  have key : ‖AA L (t : ℂ)‖ * (1 - r) ≤
      (4 / ((1 - t) * ellHat L (t : ℂ))) * (Real.sqrt 3 * Real.sqrt (1 - t)) :=
    mul_le_mul hA hhigh (by linarith) (by positivity)
  refine key.trans (le_of_eq ?_)
  field_simp
  nlinarith [hsq, Real.sqrt_nonneg 3, hs.le, hell.le]

/-- **The cost of two lattice differences**: `‖A(1-ρ)²‖ ≤ 12 / ℓ̂`.
The `(1-t)` of the prefactor is cancelled exactly, which is why (2.54) has no
`|1-ξ|` left in it. -/
theorem norm_AA_mul_one_sub_rho_sq_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hL : 3 ≤ L) :
    ‖AA L (t : ℂ) * (1 - rho (t : ℂ)) ^ 2‖ ≤ 12 / ellHat L (t : ℂ) := by
  obtain ⟨r, hrho, hr0, hr1, hlow, hhigh⟩ := rho_real_bounds ht0 ht1
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hsq : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t := Real.mul_self_sqrt h1t.le
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hell : 0 < ellHat L (t : ℂ) := by
    rw [ellHat_ofReal L ht1]
    refine lt_min (by positivity) ?_
    have : 0 < L := by omega
    exact_mod_cast this
  have hA := norm_AA_le_of_real ht0 ht1 hL
  have hrn : ‖1 - rho (t : ℂ)‖ = 1 - r := by
    rw [hrho, show (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hsq2 : (1 - r) ^ 2 ≤ 3 * (1 - t) := by nlinarith [hhigh, hs.le, hsq, h3]
  rw [norm_mul, norm_pow, hrn]
  have key : ‖AA L (t : ℂ)‖ * (1 - r) ^ 2 ≤
      (4 / ((1 - t) * ellHat L (t : ℂ))) * (3 * (1 - t)) :=
    mul_le_mul hA hsq2 (by positivity) (by positivity)
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

end Differences

end RBM
