/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Decay

/-!
# Sharp lattice differences of the long-edge propagator

For real `ξ = t ∈ (0,1)` (the long edge `ξ = t|m|²` of the paper) the closed form
`(Θ_t)_{xy} = A(ρ^d + ρ^{L-d})` has an exact first difference

  `Θ_{x,y} - Θ_{x,y+1} = A(1-ρ)(ρ^{L-1-n} - ρ^n)`,   `A(1-ρ) = (1+ρ+ρ²)/((1+ρ)(1-ρ^L))`,

and `|ρ^j - ρ^n| ≤ 1 - ρ^L`.  Hence the gradient is bounded **uniformly** (by `3/2`), in both
regimes of `ℓ̂(t) = min((1-t)^{-1/2}, L)`.  The bound `C/(ℓ̂ √(1-t))` of (2.53) is sharp only
when `ℓ̂ = (1-t)^{-1/2}`; the uniform one is what the proof of Lemma 3.11 needs.

Summed over `y`, the first difference is `≤ 3 ℓ̂(t)` and the second difference is `≤ 6`.
-/

namespace RBM

section LongDiff

variable (L : ℕ) [NeZero L]

omit [NeZero L] in
/-- `A(1-ρ) = (1+ρ+ρ²)/((1+ρ)(1-ρ^L))`: the cost of one lattice difference, exactly. -/
theorem AA_mul_one_sub_rho_eq {ξ : ℂ} (hL : L ≠ 0) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) :
    AA L ξ * (1 - rho ξ) = (1 + rho ξ + rho ξ ^ 2) / ((1 + rho ξ) * (1 - rho ξ ^ L)) := by
  have hnr : ‖rho ξ‖ < 1 := norm_rho_lt_one hξ0 hξ
  have hρm1 : 1 + rho ξ ≠ 0 := by
    intro h
    have : rho ξ = -1 := by linear_combination h
    rw [this] at hnr
    simp at hnr
  have hρL : 1 - rho ξ ^ L ≠ 0 := by
    intro h
    exact rho_pow_sub_one_ne_zero hξ0 hξ hL (by linear_combination -h)
  have hξ1 : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  rw [AA_eq hL hξ0 hξ, div_mul_eq_mul_div, ← sq, one_sub_rho_sq hξ0]
  field_simp

omit [NeZero L] in
/-- `|r^j - r^n| ≤ 1 - r^L` for `0 ≤ r ≤ 1` and `j, n ≤ L`. -/
theorem abs_pow_sub_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {j n : ℕ} (hj : j ≤ L)
    (hn : n ≤ L) : |r ^ j - r ^ n| ≤ 1 - r ^ L := by
  have key : ∀ a b : ℕ, a ≤ b → b ≤ L → |r ^ a - r ^ b| ≤ 1 - r ^ L := by
    intro a b hab hb
    have hpa : r ^ b ≤ r ^ a := pow_le_pow_of_le_one hr0 hr1 hab
    rw [abs_of_nonneg (by linarith)]
    have e : r ^ b = r ^ a * r ^ (b - a) := by rw [← pow_add]; congr 1; omega
    have hL' : r ^ L ≤ r ^ (b - a) := pow_le_pow_of_le_one hr0 hr1 (by omega)
    have ha1 : r ^ a ≤ 1 := pow_le_one₀ hr0 hr1
    have hba : 0 ≤ 1 - r ^ (b - a) := by linarith [pow_le_one₀ hr0 hr1 (n := b - a)]
    rw [e]
    nlinarith [pow_nonneg hr0 a]
  rcases le_total j n with h | h
  · exact key j n h hn
  · rw [abs_sub_comm]
    exact key n j h hj

/-- The first difference read on the kernel: with `u = x - y - 1`,
`Θ_{x,y} - Θ_{x,y+1} = kern(u.val + 1) - kern(u.val)` (the wrap-around uses `kern 0 = kern L`). -/
theorem Theta_sub_shift_eq_kern (hL : 3 ≤ L) {ξ : ℂ} (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    Theta L ξ x y - Theta L ξ x (y + 1)
      = kern L ξ ((x - y - 1).val + 1) - kern L ξ (x - y - 1).val := by
  rw [Theta_apply_eq_kern L hL hξ0 hξ x y, Theta_apply_eq_kern L hL hξ0 hξ x (y + 1),
    show x - (y + 1) = x - y - 1 by ring]
  congr 1
  have e : (x - y).val = ((x - y - 1) + 1).val := by rw [sub_add_cancel]
  rw [e]
  generalize x - y - 1 = u
  rw [val_add_one L hL]
  have hlt := ZMod.val_lt u
  rcases Nat.lt_or_ge (u.val + 1) L with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have h' : u.val + 1 = L := by omega
    rw [h', Nat.mod_self, kern_zero_eq_kern_L]

/-- The first difference, fully explicit: `A(1-ρ)(ρ^{L-1-n} - ρ^n)` with `n = (x-y-1).val`. -/
theorem Theta_sub_shift_eq (hL : 3 ≤ L) {ξ : ℂ} (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    Theta L ξ x y - Theta L ξ x (y + 1) = AA L ξ * (1 - rho ξ) *
      (rho ξ ^ (L - 1 - (x - y - 1).val) - rho ξ ^ (x - y - 1).val) := by
  rw [Theta_sub_shift_eq_kern L hL hξ0 hξ]
  have hlt := ZMod.val_lt (x - y - 1)
  exact kern_succ_sub (L := L) (ξ := ξ) _ _ (by omega)

omit [NeZero L] in
/-- The real form of the one-difference cost: `A(1-ρ) = (1+r+r²)/((1+r)(1-r^L))`,
with `r = ρ(t) ∈ (0,1)`. -/
theorem AA_mul_one_sub_rho_real (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {r : ℝ}
    (hr : rho (t : ℂ) = (r : ℂ)) :
    AA L (t : ℂ) * (1 - rho (t : ℂ)) = (((1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)) : ℝ) : ℂ) := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  rw [AA_mul_one_sub_rho_eq L (by omega) htne hnorm, hr]
  push_cast
  rfl

theorem one_add_sq_div_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 + r + r ^ 2) / (1 + r) ≤ 3 / 2 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The gradient of the long-edge propagator is bounded uniformly**:
`|(Θ_t)_{x,y} - (Θ_t)_{x,y+1}| ≤ 3/2` for all `0 < t < 1`, `L ≥ 3`. -/
theorem norm_Theta_sub_shift_le_uniform (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x y : ZMod L) : ‖Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1)‖ ≤ 3 / 2 := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  obtain ⟨r, hr, hr0, hr1, -, -⟩ := rho_real_bounds ht0 ht1
  rw [Theta_sub_shift_eq L hL htne hnorm, AA_mul_one_sub_rho_real L hL ht0 ht1 hr, hr]
  set n := (x - y - 1).val
  have hn : n < L := ZMod.val_lt _
  have hrL : r ^ L < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hrL' : 0 < 1 - r ^ L := by linarith
  have hd := abs_pow_sub_pow_le L hr0.le hr1.le (j := L - 1 - n) (n := n) (by omega) hn.le
  rw [show ((r : ℂ) ^ (L - 1 - n) - (r : ℂ) ^ n) = ((r ^ (L - 1 - n) - r ^ n : ℝ) : ℂ) by
    push_cast; ring, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)))]
  have hne : 1 - r ^ L ≠ 0 := hrL'.ne'
  have h32 := one_add_sq_div_le hr0.le hr1.le
  calc (1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)) * |r ^ (L - 1 - n) - r ^ n|
      ≤ (1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)) * (1 - r ^ L) := by gcongr
    _ = (1 + r + r ^ 2) / (1 + r) := by field_simp
    _ ≤ 3 / 2 := h32

/-- The first difference as a real function of `n = (x-y-1).val`:
`Θ_{x,y} - Θ_{x,y+1} = gradK L r n := c (r^{L-1-n} - r^n)`, `c = (1+r+r²)/((1+r)(1-r^L))`. -/
noncomputable def gradK (L : ℕ) (r : ℝ) (n : ℕ) : ℝ :=
  (1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)) * (r ^ (L - 1 - n) - r ^ n)

theorem Theta_sub_shift_real (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {r : ℝ}
    (hr : rho (t : ℂ) = (r : ℂ)) (x y : ZMod L) :
    Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1) = (gradK L r (x - y - 1).val : ℂ) := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  rw [Theta_sub_shift_eq L hL htne hnorm, AA_mul_one_sub_rho_real L hL ht0 ht1 hr, hr, gradK]
  push_cast
  ring

/-- Reindexing a sum over `ZMod L` by `val`. -/
theorem sum_val_eq_sum_range (F : ℕ → ℝ) :
    ∑ u : ZMod L, F u.val = ∑ n ∈ Finset.range L, F n := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by have := NeZero.pos L; omega⟩
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- Reindexing the rows: `∑_y F((x-y-1).val) = ∑_{n<L} F n`. -/
theorem sum_row_val_eq (F : ℕ → ℝ) (x : ZMod L) :
    ∑ y : ZMod L, F (x - y - 1).val = ∑ n ∈ Finset.range L, F n := by
  rw [← sum_val_eq_sum_range L]
  exact Fintype.sum_equiv (Equiv.subLeft (x - 1)) _ _ fun y => by
    simp only [Equiv.subLeft_apply]
    congr 2
    ring

omit [NeZero L] in
/-- `∑_{n<L} r^n = (1 - r^L)/(1 - r)`. -/
theorem sum_range_pow_eq {r : ℝ} (hr1 : r < 1) (L : ℕ) :
    ∑ n ∈ Finset.range L, r ^ n = (1 - r ^ L) / (1 - r) := by
  rw [geom_sum_eq (by linarith : r ≠ 1)]
  have : r - 1 ≠ 0 := by linarith
  have : 1 - r ≠ 0 := by linarith
  field_simp
  ring

omit [NeZero L] in
/-- `∑_{n<L} |r^{L-1-n} - r^n| ≤ min(2(1-r^L)/(1-r), L(1-r^L))`, split in its two halves. -/
theorem sum_abs_pow_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ n ∈ Finset.range L, |r ^ (L - 1 - n) - r ^ n| ≤ 2 * ((1 - r ^ L) / (1 - r)) ∧
      ∑ n ∈ Finset.range L, |r ^ (L - 1 - n) - r ^ n| ≤ L * (1 - r ^ L) := by
  constructor
  · calc ∑ n ∈ Finset.range L, |r ^ (L - 1 - n) - r ^ n|
        ≤ ∑ n ∈ Finset.range L, (r ^ (L - 1 - n) + r ^ n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h1 : 0 ≤ r ^ (L - 1 - n) := pow_nonneg hr0 _
          have h2 : 0 ≤ r ^ n := pow_nonneg hr0 _
          rw [abs_le]
          constructor <;> linarith
      _ = 2 * ((1 - r ^ L) / (1 - r)) := by
          rw [Finset.sum_add_distrib, Finset.sum_range_reflect (fun n => r ^ n) L,
            sum_range_pow_eq hr1]
          ring
  · calc ∑ n ∈ Finset.range L, |r ^ (L - 1 - n) - r ^ n|
        ≤ ∑ _n ∈ Finset.range L, (1 - r ^ L) :=
          Finset.sum_le_sum fun n hn => abs_pow_sub_pow_le L hr0 hr1.le (by omega)
            (Finset.mem_range.1 hn).le
      _ = L * (1 - r ^ L) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`ℓ¹` of the gradient**: `∑_y |(Θ_t)_{x,y} - (Θ_t)_{x,y+1}| ≤ 3 ℓ̂(t)`. -/
theorem sum_norm_Theta_sub_shift_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x : ZMod L) :
    ∑ y : ZMod L, ‖Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1)‖ ≤ 3 * ellHat L (t : ℂ) := by
  obtain ⟨r, hr, hr0, hr1, hlow, -⟩ := rho_real_bounds ht0 ht1
  have hrL : r ^ L < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hrL' : 0 < 1 - r ^ L := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  set c := (1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)) with hc
  have hc0 : 0 ≤ c := by positivity
  have e : ∀ y, ‖Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1)‖
      = c * |r ^ (L - 1 - (x - y - 1).val) - r ^ (x - y - 1).val| := by
    intro y
    rw [Theta_sub_shift_real L hL ht0 ht1 hr, Complex.norm_real, Real.norm_eq_abs, gradK, abs_mul,
      abs_of_nonneg hc0]
  simp only [e]
  rw [sum_row_val_eq L (fun n => c * |r ^ (L - 1 - n) - r ^ n|) x, ← Finset.mul_sum]
  obtain ⟨hA, hB⟩ := sum_abs_pow_sub_le (L := L) hr0.le hr1
  have h32 := one_add_sq_div_le hr0.le hr1.le
  have hne : 1 - r ^ L ≠ 0 := hrL'.ne'
  rw [ellHat_ofReal L ht1, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
  apply le_min
  · calc c * ∑ n ∈ Finset.range L, |r ^ (L - 1 - n) - r ^ n|
        ≤ c * (2 * ((1 - r ^ L) / (1 - r))) := by gcongr
      _ = 2 * ((1 + r + r ^ 2) / (1 + r)) / (1 - r) := by rw [hc]; field_simp
      _ ≤ 2 * (3 / 2) / (1 - r) := by gcongr
      _ ≤ 3 * (1 / Real.sqrt (1 - t)) := by
          rw [show 2 * (3 / 2 : ℝ) / (1 - r) = 3 * (1 / (1 - r)) by ring]
          gcongr
  · calc c * ∑ n ∈ Finset.range L, |r ^ (L - 1 - n) - r ^ n|
        ≤ c * (L * (1 - r ^ L)) := by gcongr
      _ = L * ((1 + r + r ^ 2) / (1 + r)) := by rw [hc]; field_simp
      _ ≤ L * (3 / 2) := by gcongr
      _ ≤ 3 * L := by nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

/-- The second difference is the difference of two first differences. -/
theorem Theta_second_diff_eq (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {r : ℝ}
    (hr : rho (t : ℂ) = (r : ℂ)) (x y : ZMod L) :
    2 * Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1) - Theta L (t : ℂ) x (y - 1)
      = ((gradK L r (x - y - 1).val - gradK L r (((x - y - 1).val + 1) % L) : ℝ) : ℂ) := by
  have h1 := Theta_sub_shift_real L hL ht0 ht1 hr x y
  have h2 := Theta_sub_shift_real L hL ht0 ht1 hr x (y - 1)
  rw [sub_add_cancel, show x - (y - 1) - 1 = (x - y - 1) + 1 by ring, val_add_one L hL] at h2
  push_cast
  linear_combination h1 - h2

/-- **The uniform bound on the second difference** (it is `O(1)`, and `O(1/ℓ̂)` off the
diagonal by `norm_Theta_second_diff_le`): `|2Θ_{x,y} - Θ_{x,y+1} - Θ_{x,y-1}| ≤ 3`. -/
theorem norm_Theta_second_diff_le_three (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x y : ZMod L) :
    ‖2 * Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1) - Theta L (t : ℂ) x (y - 1)‖ ≤ 3 := by
  have e : 2 * Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1) - Theta L (t : ℂ) x (y - 1)
      = (Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1))
        - (Theta L (t : ℂ) x (y - 1) - Theta L (t : ℂ) x (y - 1 + 1)) := by
    rw [sub_add_cancel]; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_Theta_sub_shift_le_uniform L hL ht0 ht1 x y
  have := norm_Theta_sub_shift_le_uniform L hL ht0 ht1 x (y - 1)
  linarith

/-- **`ℓ¹` of the second difference**: `∑_y |2Θ_{x,y} - Θ_{x,y+1} - Θ_{x,y-1}| ≤ 6`,
uniformly in `t` and `L`. -/
theorem sum_norm_Theta_second_diff_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x : ZMod L) :
    ∑ y : ZMod L,
      ‖2 * Theta L (t : ℂ) x y - Theta L (t : ℂ) x (y + 1) - Theta L (t : ℂ) x (y - 1)‖ ≤ 6 := by
  obtain ⟨r, hr, hr0, hr1, -, -⟩ := rho_real_bounds ht0 ht1
  have hrL : r ^ L < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hrL' : 0 < 1 - r ^ L := by linarith
  have h1r : 0 < 1 - r := by linarith
  set c := (1 + r + r ^ 2) / ((1 + r) * (1 - r ^ L)) with hc
  have hc0 : 0 ≤ c := by positivity
  simp only [Theta_second_diff_eq L hL ht0 ht1 hr, Complex.norm_real, Real.norm_eq_abs]
  rw [sum_row_val_eq L (fun n => |gradK L r n - gradK L r ((n + 1) % L)|) x]
  obtain ⟨k, hk⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  rw [hk, Finset.sum_range_succ, ← hk]
  have hinner : ∀ n ∈ Finset.range k, |gradK L r n - gradK L r ((n + 1) % L)|
      = c * (1 - r) * (r ^ n + r ^ (k - 1 - n)) := by
    intro n hn
    have hn' := Finset.mem_range.1 hn
    rw [Nat.mod_eq_of_lt (by omega), gradK, gradK, ← hc,
      show L - 1 - n = (k - 1 - n) + 1 by omega, show L - 1 - (n + 1) = k - 1 - n by omega]
    rw [show c * (r ^ (k - 1 - n + 1) - r ^ n) - c * (r ^ (k - 1 - n) - r ^ (n + 1))
        = -(c * (1 - r) * (r ^ n + r ^ (k - 1 - n))) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  have hlast : |gradK L r k - gradK L r (L % L)| = 2 * c * (1 - r ^ k) := by
    rw [Nat.mod_self, gradK, gradK, ← hc,
      show L - 1 - k = 0 by omega, show L - 1 - 0 = k by omega, pow_zero]
    rw [show c * (1 - r ^ k) - c * (r ^ k - 1) = 2 * c * (1 - r ^ k) by ring,
      abs_of_nonneg (by have := pow_le_one₀ hr0.le hr1.le (n := k); positivity)]
  rw [Finset.sum_congr rfl hinner, hlast, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_range_reflect (fun n => r ^ n) k, sum_range_pow_eq hr1]
  have hk1 : r ^ L ≤ r ^ k := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  have h32 := one_add_sq_div_le hr0.le hr1.le
  have hne : 1 - r ^ L ≠ 0 := hrL'.ne'
  have hkey : c * (1 - r ^ L) = (1 + r + r ^ 2) / (1 + r) := by rw [hc]; field_simp
  calc c * (1 - r) * ((1 - r ^ k) / (1 - r) + (1 - r ^ k) / (1 - r)) + 2 * c * (1 - r ^ k)
      = 4 * (c * (1 - r ^ k)) := by field_simp; ring
    _ ≤ 4 * (c * (1 - r ^ L)) := by gcongr
    _ ≤ 4 * (3 / 2) := by rw [hkey]; gcongr
    _ = 6 := by norm_num

end LongDiff

end RBM
