/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Semicircle
import RBM1D.Propagator.DecayComplex

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

section Summation

variable (L : ℕ) [NeZero L]

/-- `ZMod.val` identifies `ZMod L` with `Finset.range L`. -/
theorem image_val_eq_range :
    (Finset.univ : Finset (ZMod L)).image ZMod.val = Finset.range L := by
  refine Finset.eq_of_subset_of_card_le (fun v hv => ?_) ?_
  · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_range.mpr (ZMod.val_lt u)
  · rw [Finset.card_range, Finset.card_image_of_injective _ (ZMod.val_injective L),
      Finset.card_univ, ZMod.card]

theorem sum_zmod_val (f : ℕ → ℝ) :
    ∑ u : ZMod L, f u.val = ∑ v ∈ Finset.range L, f v := by
  rw [← image_val_eq_range L,
    Finset.sum_image (fun a _ b _ h => ZMod.val_injective L h)]

/-- A geometric sum over `ZMod L`, indexed by `val`. -/
theorem sum_pow_val_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ u.val ≤ (1 - r)⁻¹ := by
  rw [sum_zmod_val L fun v => r ^ v]
  refine (Summable.sum_le_tsum _ (fun i _ => by positivity)
    (summable_geometric_of_lt_one hr0 hr1)).trans ?_
  rw [tsum_geometric_of_lt_one hr0 hr1]

/-- The same sum with the reflected exponent `L - val`. -/
theorem sum_pow_sub_val_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ (L - u.val) ≤ (1 - r)⁻¹ := by
  rw [sum_zmod_val L fun v => r ^ (L - v)]
  have hstep : ∀ v ∈ Finset.range L, r ^ (L - v) ≤ r ^ (L - 1 - v) := by
    intro v hv
    exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_range_reflect (fun v => r ^ v) L]
  refine (Summable.sum_le_tsum _ (fun i _ => by positivity)
    (summable_geometric_of_lt_one hr0 hr1)).trans ?_
  rw [tsum_geometric_of_lt_one hr0 hr1]

/-- The key splitting: a function of the cycle distance is bounded by the sum of the two
one-sided terms, because the distance is one of them and both are nonnegative. -/
theorem pow_zdist_le_add {r : ℝ} (hr0 : 0 ≤ r) (u : ZMod L) :
    r ^ zdist L u ≤ r ^ u.val + r ^ (L - u.val) := by
  rcases min_cases u.val (L - u.val) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    · rw [zdist, h]
      have h1 : (0 : ℝ) ≤ r ^ u.val := by positivity
      have h2 : (0 : ℝ) ≤ r ^ (L - u.val) := by positivity
      linarith

/-- `∑_u r^{dist(u)} ≤ 2/(1-r)` on the cycle. -/
theorem sum_pow_zdist_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ zdist L u ≤ 2 * (1 - r)⁻¹ := by
  have h1 : ∑ u : ZMod L, r ^ zdist L u
      ≤ ∑ u : ZMod L, (r ^ u.val + r ^ (L - u.val)) :=
    Finset.sum_le_sum fun u _ => pow_zdist_le_add L hr0 u
  rw [Finset.sum_add_distrib] at h1
  have h2 := sum_pow_val_le L hr0 hr1
  have h3 := sum_pow_sub_val_le L hr0 hr1
  linarith

/-- `1/(1 - e^{-λ}) ≤ (1 + λ)/λ`, the elementary bound behind summing an exponential
decay of length `1/λ`. -/
theorem one_sub_exp_neg_ge {lam : ℝ} (hlam : 0 < lam) :
    lam / (1 + lam) ≤ 1 - Real.exp (-lam) := by
  have hexp : (1 : ℝ) + lam ≤ Real.exp lam := by
    have := Real.add_one_le_exp lam; linarith
  have hpos : 0 < Real.exp lam := Real.exp_pos _
  have hkey : (1 + lam) * Real.exp (-lam) ≤ 1 := by
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ hpos]
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hkey]

end Summation

end RBM
