/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Semicircle
import RBM1D.Propagator.DecayComplex
import RBM1D.Defs.Sums

/-!
# Short and long edges: the two spectral parameters of (3.35)--(3.36)

The paper uses the propagator at `xi = t m^2` (short edge) and at `xi = t |m|^2 = t`
(long edge).  A uniform bound in terms of `1 - |xi|` cannot tell them apart: both have
`|xi| = t -> 1`.  What separates them is `|1 - xi|`, computed exactly here.
-/

namespace RBM

open Complex

section ShortEdge

/-- **The exact modulus of `1 - t m^2`**: `|1 - t m^2|^2 = (1-t)^2 + t(4 - E^2)`.
At `E = ±2` the second term vanishes and the short edge degenerates into the long one;
the paper's hypothesis `|E| <= 2 - k` is exactly what keeps it away from that. -/
theorem normSq_one_sub_mul_sq_mE {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    Complex.normSq (1 - (t : ℂ) * (mE E) ^ 2) = (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have h4 : (0 : ℝ) ≤ 4 - E ^ 2 := by
    have hb := abs_le.mp hE
    nlinarith [hb.1, hb.2]
  have hss : Real.sqrt (4 - E ^ 2) * Real.sqrt (4 - E ^ 2) = 4 - E ^ 2 :=
    Real.mul_self_sqrt h4
  have hre : ((mE E) ^ 2).re = (2 * E ^ 2 - 4) / 4 := by
    rw [pow_two, Complex.mul_re, mE_re, mE_im]
    linear_combination (-1/4 : ℝ) * hss
  have him : ((mE E) ^ 2).im = -(E * Real.sqrt (4 - E ^ 2)) / 2 := by
    rw [pow_two, Complex.mul_im, mE_re, mE_im]
    ring
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination (t ^ 2 * E ^ 2 / 4) * hss

/-- `|1 - t m^2|^2 >= 2 t k` under the paper's hypothesis `|E| <= 2 - k`. -/
theorem two_mul_mul_le_normSq_one_sub {E k t : ℝ} (hk0 : 0 < k) (hk2 : k ≤ 2)
    (hE : |E| ≤ 2 - k) (ht0 : 0 ≤ t) :
    2 * t * k ≤ Complex.normSq (1 - (t : ℂ) * (mE E) ^ 2) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hb := abs_le.mp hE
  have h4 : 2 * k ≤ 4 - E ^ 2 := by nlinarith [hb.1, hb.2]
  rw [normSq_one_sub_mul_sq_mE hE2 t]
  nlinarith [sq_nonneg (1 - t), ht0, h4]

end ShortEdge

section Dictionary

/-- `eta_t <= 1 - t`. -/
theorem zt_im_le {E : ℝ} (hE : |E| ≤ 2) {t : ℝ} (ht : t ≤ 1) : (zt E t).im ≤ 1 - t := by
  have h4 : (0 : ℝ) ≤ 4 - E ^ 2 := by
    have hb := abs_le.mp hE
    nlinarith [hb.1, hb.2]
  have h4' : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    have hmono : Real.sqrt (4 - E ^ 2) ≤ Real.sqrt 4 :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
    rw [h4'] at hmono
    exact hmono
  rw [zt_im, mE_im]
  nlinarith [hs, ht]

/-- `eta_t >= (1-t) sqrt(2k)/2` when `|E| <= 2 - k`; together with `zt_im_le` this is
the dictionary `eta_t ≍ 1 - t`.  It needs only Definition 2.7, not (2.40). -/
theorem le_zt_im {E k : ℝ} (hk0 : 0 < k) (hk2 : k ≤ 2) (hE : |E| ≤ 2 - k) {t : ℝ}
    (ht : t ≤ 1) : (1 - t) * (Real.sqrt (2 * k) / 2) ≤ (zt E t).im := by
  have hb := abs_le.mp hE
  have h4 : 2 * k ≤ 4 - E ^ 2 := by nlinarith [hb.1, hb.2]
  have hs : Real.sqrt (2 * k) ≤ Real.sqrt (4 - E ^ 2) := Real.sqrt_le_sqrt h4
  rw [zt_im, mE_im]
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  exact mul_le_mul_of_nonneg_left (by linarith) h1t

end Dictionary

section ShortEdgeBound

variable (L : ℕ) [NeZero L]

/-- The short-edge parameter has modulus `t`, since `|m^{(E)}| = 1`. -/
theorem norm_short_edge {E : ℝ} (hE : |E| ≤ 2) {t : ℝ} (ht0 : 0 ≤ t) :
    ‖(t : ℂ) * (mE E) ^ 2‖ = t := by
  rw [norm_mul, norm_pow, norm_mE hE, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0]

/-- `|1 - t m^2|^2 >= k` for **every** `t` in `[0,1]`, not just `t` bounded away from `0`:
the minimum of `(1-t)^2 + 2tk` over `t` is `2k - k^2 >= k` when `k <= 1`. -/
theorem le_normSq_one_sub_short {E k t : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hE : |E| ≤ 2 - k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    k ≤ Complex.normSq (1 - (t : ℂ) * (mE E) ^ 2) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hb := abs_le.mp hE
  have h4 : 2 * k ≤ 4 - E ^ 2 := by nlinarith [hb.1, hb.2]
  rw [normSq_one_sub_mul_sq_mE hE2 t]
  nlinarith [sq_nonneg (t - (1 - k)), ht0, h4]

theorem sqrt_le_norm_one_sub_short {E k t : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hE : |E| ≤ 2 - k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt k ≤ ‖1 - (t : ℂ) * (mE E) ^ 2‖ := by
  have h := le_normSq_one_sub_short hk0 hk1 hE ht0 ht1
  rw [← Complex.sq_norm] at h
  calc Real.sqrt k ≤ Real.sqrt (‖1 - (t : ℂ) * (mE E) ^ 2‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖1 - (t : ℂ) * (mE E) ^ 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- `ℓ̂(ξ) ≥ 1/2` for every `‖ξ‖ < 1`: the decay length is never shorter than one block. -/
theorem half_le_ellHat (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : 1 / 2 ≤ ellHat L ξ := by
  have hne : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have h0 : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hne
  have h4 : ‖1 - ξ‖ ≤ 4 := by
    calc ‖1 - ξ‖ ≤ ‖(1 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ ≤ 4 := by norm_num
  have hs : Real.sqrt ‖1 - ξ‖ ≤ 2 := by
    have hmono : Real.sqrt ‖1 - ξ‖ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h4
    have h4' : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4'] at hmono
    exact hmono
  have hspos : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.mpr h0
  rw [ellHat]
  refine le_min (one_div_le_one_div_of_le hspos hs) ?_
  have : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  linarith

/-- **(3.35) and (3.36), short edge: the `max` bound.**
`|(Θ_{t m²})_{xy}| ≤ 2C/√κ` uniformly in `t ∈ [0,1)`, `L` and `x, y`, where `C` is the
constant of (2.52).  The uniform bound `(1-‖ξ‖)^{-1}` cannot give this: it blows up as
`t → 1`.  What saves the short edge is that `|1 - t m²|` stays bounded below, which is
`le_normSq_one_sub_short`. -/
theorem norm_Theta_short_edge_le (hL : 3 ≤ L) {E k t : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hE : |E| ≤ 2 - k) (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : ZMod L) :
    ‖Theta L ((t : ℂ) * (mE E) ^ 2) x y‖ ≤ 2 * cTwo52 / Real.sqrt k := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hξ : ‖(t : ℂ) * (mE E) ^ 2‖ < 1 := by
    rw [norm_short_edge hE2 ht0]; exact ht1
  have hmain := norm_Theta_apply_le_complex hL hξ x y
  have hk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hden1 : Real.sqrt k ≤ ‖1 - (t : ℂ) * (mE E) ^ 2‖ :=
    sqrt_le_norm_one_sub_short hk0 hk1 hE ht0 ht1.le
  have hden2 : 1 / 2 ≤ ellHat L ((t : ℂ) * (mE E) ^ 2) := half_le_ellHat L hL hξ
  have hexp : Real.exp (-(cZero * (zdist L (x - y) : ℝ)
      / ellHat L ((t : ℂ) * (mE E) ^ 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hpos : 0 < ellHat L ((t : ℂ) * (mE E) ^ 2) := lt_of_lt_of_le (by norm_num) hden2
    have : 0 ≤ cZero * (zdist L (x - y) : ℝ) / ellHat L ((t : ℂ) * (mE E) ^ 2) :=
      div_nonneg (mul_nonneg cZero_pos.le (Nat.cast_nonneg _)) hpos.le
    linarith
  have hdenpos : 0 < ‖1 - (t : ℂ) * (mE E) ^ 2‖ * ellHat L ((t : ℂ) * (mE E) ^ 2) := by
    have : 0 < ellHat L ((t : ℂ) * (mE E) ^ 2) := lt_of_lt_of_le (by norm_num) hden2
    have h1 : 0 < ‖1 - (t : ℂ) * (mE E) ^ 2‖ := lt_of_lt_of_le hk hden1
    positivity
  have hC := cTwo52_pos
  set ee := Real.exp (-(cZero * (zdist L (x - y) : ℝ)
      / ellHat L ((t : ℂ) * (mE E) ^ 2))) with hee
  have hee0 : 0 < ee := Real.exp_pos _
  refine hmain.trans ?_
  rw [div_le_div_iff₀ hdenpos hk]
  have hprod : Real.sqrt k * (1 / 2)
      ≤ ‖1 - (t : ℂ) * (mE E) ^ 2‖ * ellHat L ((t : ℂ) * (mE E) ^ 2) :=
    mul_le_mul hden1 hden2 (by norm_num) (le_trans hk.le hden1)
  have hleft : cTwo52 * ee * Real.sqrt k ≤ cTwo52 * Real.sqrt k := by
    have h1 : cTwo52 * ee ≤ cTwo52 := by nlinarith [hexp, hC]
    nlinarith [hk.le, h1]
  have hright : cTwo52 * Real.sqrt k
      ≤ 2 * cTwo52 * (‖1 - (t : ℂ) * (mE E) ^ 2‖ * ellHat L ((t : ℂ) * (mE E) ^ 2)) := by
    have hcoef : (0 : ℝ) ≤ 2 * cTwo52 := by linarith
    have := mul_le_mul_of_nonneg_left hprod hcoef
    nlinarith [this]
  linarith

end ShortEdgeBound

section L1Edge

variable (L : ℕ) [NeZero L]

/-- **The `ℓ¹` bound implied by (2.52)**, for every `‖ξ‖ < 1`:
`∑_b |(Θ_ξ)_{ab}| ≤ 2C(1/c + 2)/|1 - ξ|`.

Summing the exponential of (2.52) over the cycle costs a factor `ℓ̂`, which cancels the
`ℓ̂` in the denominator of (2.52) and leaves `1/|1-ξ|`.  For the long edge `ξ = t` this is
`1/(1-t) ≍ 1/η_t`, the second half of (3.36); for the short edge `|1-ξ|` is bounded
below, so the same bound is `O(1)`, the first half. -/
theorem sum_norm_Theta_row_le_complex (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a : ZMod L) :
    ∑ b : ZMod L, ‖Theta L ξ a b‖ ≤ 2 * cTwo52 * (1 / cZero + 2) / ‖1 - ξ‖ := by
  have hell : 1 / 2 ≤ ellHat L ξ := half_le_ellHat L hL hξ
  have hellpos : 0 < ellHat L ξ := lt_of_lt_of_le (by norm_num) hell
  have hne : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have : ξ = 1 := by linear_combination -h
    rw [this, norm_one] at hξ
    exact absurd hξ (lt_irrefl 1)
  have hD : 0 < ‖1 - ξ‖ := norm_pos_iff.mpr hne
  have hC := cTwo52_pos
  set lam := cZero / ellHat L ξ with hlamdef
  have hlam : 0 < lam := div_pos cZero_pos hellpos
  have hpt : ∀ b : ZMod L, ‖Theta L ξ a b‖
      ≤ cTwo52 / (‖1 - ξ‖ * ellHat L ξ) * Real.exp (-(lam * (zdist L (a - b) : ℝ))) := by
    intro b
    have h := norm_Theta_apply_le_complex hL hξ a b
    have hexparg : -(cZero * (zdist L (a - b) : ℝ) / ellHat L ξ)
        = -(lam * (zdist L (a - b) : ℝ)) := by
      rw [hlamdef]; ring
    rw [hexparg] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  have hcoef : (0 : ℝ) ≤ cTwo52 / (‖1 - ξ‖ * ellHat L ξ) := by positivity
  calc ∑ b : ZMod L, ‖Theta L ξ a b‖
      ≤ ∑ b : ZMod L, cTwo52 / (‖1 - ξ‖ * ellHat L ξ)
          * Real.exp (-(lam * (zdist L (a - b) : ℝ))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = cTwo52 / (‖1 - ξ‖ * ellHat L ξ)
          * ∑ b : ZMod L, Real.exp (-(lam * (zdist L (a - b) : ℝ))) := by
        rw [← Finset.mul_sum]
    _ = cTwo52 / (‖1 - ξ‖ * ellHat L ξ)
          * ∑ u : ZMod L, Real.exp (-(lam * (zdist L u : ℝ))) := by
        congr 1
        exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => rfl
    _ ≤ cTwo52 / (‖1 - ξ‖ * ellHat L ξ) * (2 * ((1 + lam) / lam)) :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_zdist_le L hlam) hcoef
    _ = 2 * cTwo52 * (1 / cZero + 1 / ellHat L ξ) / ‖1 - ξ‖ := by
        have hc0 : cZero ≠ 0 := ne_of_gt cZero_pos
        rw [hlamdef]
        field_simp
    _ ≤ 2 * cTwo52 * (1 / cZero + 2) / ‖1 - ξ‖ := by
        have h1l : 1 / ellHat L ξ ≤ 2 := by
          rw [div_le_iff₀ hellpos]; linarith
        gcongr

/-- **(3.36), short edge**: `∑_b |(Θ_{t m²})_{ab}| = O_κ(1)`, uniformly in `t` and `L`. -/
theorem sum_norm_Theta_short_edge_le (hL : 3 ≤ L) {E k t : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hE : |E| ≤ 2 - k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : ZMod L) :
    ∑ b : ZMod L, ‖Theta L ((t : ℂ) * (mE E) ^ 2) a b‖
      ≤ 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt k := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hξ : ‖(t : ℂ) * (mE E) ^ 2‖ < 1 := by
    rw [norm_short_edge hE2 ht0]; exact ht1
  have hk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hden : Real.sqrt k ≤ ‖1 - (t : ℂ) * (mE E) ^ 2‖ :=
    sqrt_le_norm_one_sub_short hk0 hk1 hE ht0 ht1.le
  refine (sum_norm_Theta_row_le_complex L hL hξ a).trans ?_
  have hC := cTwo52_pos
  have hnum : (0 : ℝ) ≤ 2 * cTwo52 * (1 / cZero + 2) := by
    have := cZero_pos
    positivity
  gcongr

end L1Edge

section LongEdge

variable (L : ℕ) [NeZero L]

/-- **(3.35), long edge**: `|(Θ_t)_{xy}| ≤ 8e/(η_t · ℓ̂(t))`.
The paper writes the right-hand side as `1/(ℓ_t η_t)`; the dictionary `η_t ≤ 1-t` of
`zt_im_le` turns our `(1-t)` into the paper's `η_t`. -/
theorem norm_Theta_long_edge_le (hL : 3 ≤ L) {E k t : ℝ} (hk0 : 0 < k) (hk2 : k ≤ 2)
    (hE : |E| ≤ 2 - k) (ht0 : 0 < t) (ht1 : t < 1) (x y : ZMod L) :
    ‖Theta L (t : ℂ) x y‖ ≤ 8 * Real.exp 1 / ((zt E t).im * ellHat L (t : ℂ)) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hell : 1 / 2 ≤ ellHat L (t : ℂ) := half_le_ellHat L hL (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1)
  have hellpos : 0 < ellHat L (t : ℂ) := lt_of_lt_of_le (by norm_num) hell
  have heta_le : (zt E t).im ≤ 1 - t := zt_im_le hE2 ht1.le
  have heta_pos : 0 < (zt E t).im := by
    have h := le_zt_im hk0 hk2 hE ht1.le
    have hsq : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by linarith)
    nlinarith [h, h1t, hsq]
  have hmain := norm_Theta_apply_le_of_real hL ht0 ht1 x y
  have hexp : Real.exp (-(zdist L (x - y) : ℝ) / ellHat L (t : ℂ)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    have : (0 : ℝ) ≤ (zdist L (x - y) : ℝ) / ellHat L (t : ℂ) := by positivity
    linarith
  refine hmain.trans ?_
  set ee := Real.exp (-(zdist L (x - y) : ℝ) / ellHat L (t : ℂ)) with hee
  have h3 : (0 : ℝ) ≤ 8 * Real.exp 1 := by positivity
  have h4 : (0 : ℝ) ≤ (zt E t).im * ellHat L (t : ℂ) := by positivity
  have h2 : (zt E t).im * ellHat L (t : ℂ) ≤ (1 - t) * ellHat L (t : ℂ) :=
    mul_le_mul_of_nonneg_right heta_le hellpos.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 8 * Real.exp 1 * ee * ((zt E t).im * ellHat L (t : ℂ))
      ≤ 8 * Real.exp 1 * 1 * ((zt E t).im * ellHat L (t : ℂ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h3) h4
    _ = 8 * Real.exp 1 * ((zt E t).im * ellHat L (t : ℂ)) := by ring
    _ ≤ 8 * Real.exp 1 * ((1 - t) * ellHat L (t : ℂ)) := mul_le_mul_of_nonneg_left h2 h3

/-- **(3.36), long edge**: `∑_b |(Θ_t)_{ab}| = (1-t)^{-1} ≤ 1/η_t`. -/
theorem sum_norm_Theta_long_edge_le (hL : 3 ≤ L) {E k t : ℝ} (hk0 : 0 < k) (hk2 : k ≤ 2)
    (hE : |E| ≤ 2 - k) (ht0 : 0 < t) (ht1 : t < 1) (a : ZMod L) :
    ∑ b : ZMod L, ‖Theta L (t : ℂ) a b‖ ≤ ((zt E t).im)⁻¹ := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have heta_le : (zt E t).im ≤ 1 - t := zt_im_le hE2 ht1.le
  have heta_pos : 0 < (zt E t).im := by
    have h := le_zt_im hk0 hk2 hE ht1.le
    have hsq : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by linarith)
    nlinarith [h, h1t, hsq]
  rw [sum_norm_Theta_row_of_real L hL ht0 ht1 a, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le heta_pos heta_le

end LongEdge

end RBM
