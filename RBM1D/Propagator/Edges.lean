/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Semicircle

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

end RBM
