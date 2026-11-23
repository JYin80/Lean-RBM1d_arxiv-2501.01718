/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

module

public import RBM1D.MainDefs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The semicircle Stieltjes transform and the `z_t` flow

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.7 and the
algebraic part of Lemma 2.8.

* `m^{(E)}` is the solution of `m (m + E) = -1` with `Im m > 0`; for `|E| < 2` it is
  `(-E + i√(4 - E²))/2` and has modulus `1`.
* `m_sc(z)` is the root of `m² + z m + 1 = 0` with `Im m > 0`, for `Im z > 0`.
* Definition 2.7: `z_t^{(E)} = E + (1 - t) m^{(E)}`.
* Lemma 2.8: for `Im z > 0` put `E = -2 Re m_sc(z)/|m_sc(z)|` and `t = |m_sc(z)|²`.  Then
  `m^{(E)} = m_sc(z)/|m_sc(z)|`, `t = m_sc(z)²/(m^{(E)})²`, `0 < t < 1`, `|E| < 2`,
  (2.38) `m_sc(z) = t^{1/2} m^{(E)}` and (2.37) `z = t^{-1/2} z_t^{(E)}`.

The quantitative part (2.40) holds with explicit constants independent of `κ`:
`|E| ≤ |Re z|`, `t ≥ (1 + |z|)⁻²` and `Im z_t = t^{1/2} Im z` (`lemma28_quant`).
-/

namespace RBM

open Complex

section mE

theorem mE_re (E : ℝ) : (mE E).re = -E / 2 := by simp [mE]

/-- `|m^{(E)}| = 1` for `|E| ≤ 2`. -/
theorem norm_mE {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1 := by
  have h2 : ‖mE E‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mE_re, mE_im]
    have := sq_sqrt_four_sub hE
    nlinarith
  have := norm_nonneg (mE E)
  nlinarith

/-- The paper's `m(σ)` of (2.42) at energy `E`: `m(+) = m^{(E)}`, `m(-) = conj m^{(E)}`. -/
noncomputable def mSigma (E : ℝ) (s : Bool) : ℂ := if s then mE E else (starRingEnd ℂ) (mE E)

theorem norm_mSigma {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSigma E s‖ = 1 := by
  cases s <;> simp [mSigma, norm_mE hE]

/-- The hypothesis of Example 2.15 holds for `0 ≤ t < 1`: `‖t m₁ m₂‖ = t < 1`. -/
theorem norm_mul_mSigma_lt_one {E t : ℝ} (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s₁ s₂ : Bool) : ‖(t : ℂ) * (mSigma E s₁ * mSigma E s₂)‖ < 1 := by
  rw [norm_mul, norm_mul, norm_mSigma hE, norm_mSigma hE, Complex.norm_real,
    Real.norm_of_nonneg ht0]
  linarith

end mE

section msc

/-- `|m_sc(z)| < 1` for `Im z > 0`. -/
theorem norm_msc_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ < 1 := by
  have hm := msc_mul z
  have him := msc_im_pos hz
  set m := msc z
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at him
    exact lt_irrefl _ him
  have hinv : m + z = -m⁻¹ := by
    field_simp
    linear_combination hm
  have hN : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm0
  have key : (m.im + z.im) * Complex.normSq m = m.im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  have hN1 : Complex.normSq m < 1 := by nlinarith
  have h2 : ‖m‖ ^ 2 < 1 := by rwa [Complex.sq_norm]
  have := norm_nonneg m
  nlinarith

end msc

section Flow

/-- (2.35): `Im z_t^{(E)} = (1 - t) Im m^{(E)}`. -/
theorem zt_im (E t : ℝ) : (zt E t).im = (1 - t) * (mE E).im := by
  simp [zt]

end Flow

section Lemma28

variable {z : ℂ} (hz : 0 < z.im)
include hz

theorem lemT_lt_one : lemT z < 1 := by
  have := norm_msc_lt_one hz
  have := norm_nonneg (msc z)
  unfold lemT
  nlinarith

/-- (2.38): `m_sc(z) = t^{1/2} m^{(E)}`. -/
theorem msc_eq_sqrt_mul_mE : msc z = (Real.sqrt (lemT z) : ℂ) * mE (lemE z) := by
  have hr : (‖msc z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_msc_pos hz).ne'
  rw [mE_lemE hz, lemT, Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-! ### The quantitative part (2.40)

Write `m = m_sc(z) = r e^{iθ}`.  From `m + m⁻¹ = -z`: `(r + r⁻¹) cos θ = -Re z`, so
`|E| = 2|cos θ| ≤ |Re z|`; and `r⁻¹ = |m + z| < 1 + |z|`, so `t = r² > (1 + |z|)⁻²`.
With (2.37), `Im z_t = t^{1/2} Im z`.  None of this needs `κ` beyond `|Re z| ≤ 2 - κ` itself. -/

/-- `m_sc(z) + z = -m_sc(z)⁻¹`. -/
theorem msc_add_eq_neg_inv : msc z + z = -(msc z)⁻¹ := by
  have hm0 : msc z ≠ 0 := norm_pos_iff.mp (norm_msc_pos hz)
  field_simp
  linear_combination msc_mul z

/-- `|E| ≤ |Re z|`: the energy of Lemma 2.8 is no closer to the edge than `Re z`. -/
theorem abs_lemE_le : |lemE z| ≤ |z.re| := by
  set m := msc z
  set r := ‖m‖ with hr_def
  have hr : 0 < r := norm_msc_pos hz
  have hN : Complex.normSq m = r ^ 2 := by rw [hr_def, Complex.sq_norm]
  have hre : m.re + z.re = -(m.re / r ^ 2) := by
    have := congrArg Complex.re (msc_add_eq_neg_inv hz)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at this
    have h' : m.re + z.re = -(m.re / Complex.normSq m) := this
    rwa [hN] at h'
  have hzre : z.re = -m.re * (r ^ 2 + 1) / r ^ 2 := by
    have hc : m.re / r ^ 2 * r ^ 2 = m.re := div_mul_cancel₀ _ (by positivity)
    rw [eq_div_iff (by positivity)]
    linear_combination r ^ 2 * hre - hc
  have e : lemE z = -2 * m.re / r := rfl
  rw [e, hzre, abs_div, abs_div, abs_mul, abs_mul, abs_neg, abs_neg, abs_of_pos hr,
    abs_of_pos (by positivity : (0 : ℝ) < r ^ 2 + 1), abs_of_pos (by positivity : (0 : ℝ) < r ^ 2),
    abs_two, div_le_div_iff₀ hr (by positivity)]
  have := abs_nonneg m.re
  nlinarith [mul_nonneg this (sq_nonneg (r - 1))]

/-- `t ≥ (1 + |z|)⁻²`. -/
theorem lemT_ge : ((1 + ‖z‖) ^ 2)⁻¹ ≤ lemT z := by
  have hr : 0 < ‖msc z‖ := norm_msc_pos hz
  have hinv : ‖msc z‖⁻¹ ≤ ‖msc z‖ + ‖z‖ := by
    rw [← norm_inv, ← norm_neg, ← msc_add_eq_neg_inv hz]
    exact norm_add_le _ _
  have h1 : 1 ≤ ‖msc z‖ * (1 + ‖z‖) := by
    have h := norm_msc_lt_one hz
    have := (inv_le_iff_one_le_mul₀' hr).1 (hinv.trans (by linarith : ‖msc z‖ + ‖z‖ ≤ 1 + ‖z‖))
    linarith
  rw [lemT, inv_le_iff_one_le_mul₀ (by positivity)]
  nlinarith [norm_nonneg z]

/-- (2.37) read on imaginary parts: `Im z_t = t^{1/2} Im z`. -/
theorem zt_im_lemma28 : (zt (lemE z) (lemT z)).im = Real.sqrt (lemT z) * z.im := by
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (lemT_pos hz)).ne'
  have h := eq_inv_sqrt_mul_zt hz
  have e : zt (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z :=
    calc zt (lemE z) (lemT z)
        = (Real.sqrt (lemT z) : ℂ) * ((Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      _ = _ := by rw [← h]
  rw [e]
  simp [Complex.mul_im]

omit hz in
/-- **Lemma 2.8, the quantitative part**: for `0 < Im z ≤ 1` and `|Re z| ≤ 2 - κ`,
`|E| ≤ 2 - κ` and, with `c_κ = 1/16`, `t ≥ c_κ` and (2.40) `c_κ Im z ≤ Im z_t ≤ c_κ⁻¹ Im z`. -/
theorem lemma28_quant {κ : ℝ} (hκ0 : 0 < κ) (hz0 : 0 < z.im) (hz1 : z.im ≤ 1)
    (hκ : |z.re| ≤ 2 - κ) :
    |lemE z| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧
      (1 / 16 : ℝ) * z.im ≤ (zt (lemE z) (lemT z)).im ∧
      (zt (lemE z) (lemT z)).im ≤ (1 / 16 : ℝ)⁻¹ * z.im := by
  have hnorm : ‖z‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz0] at this
    linarith
  have ht : (1 / 16 : ℝ) ≤ lemT z := by
    refine le_trans ?_ (lemT_ge hz0)
    rw [one_div]
    exact inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.mpr (lemT_lt_one hz0).le
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht
  refine ⟨(abs_lemE_le hz0).trans hκ, ht, ?_, ?_⟩ <;> rw [zt_im_lemma28 hz0] <;> nlinarith

end Lemma28

end RBM
