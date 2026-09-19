/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

The quantitative bounds `|E| ≤ 2 - cκ`, `t ≥ c_κ` and (2.40) depend on `κ` and are only
used in the stochastic layer; they are deferred (see the note at the end of the file).
-/

namespace RBM

open Complex

section mE

/-- `m^{(E)} = (-E + i√(4 - E²))/2`, the root of `m(m + E) = -1` with `Im m > 0` when
`|E| < 2`. -/
noncomputable def mE (E : ℝ) : ℂ := (-E + Real.sqrt (4 - E ^ 2) * I) / 2

theorem mE_re (E : ℝ) : (mE E).re = -E / 2 := by simp [mE]

theorem mE_im (E : ℝ) : (mE E).im = Real.sqrt (4 - E ^ 2) / 2 := by simp [mE]

theorem sq_sqrt_four_sub {E : ℝ} (hE : |E| ≤ 2) : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := by
  refine Real.sq_sqrt ?_
  have := abs_le.mp hE
  nlinarith

theorem mE_mul {E : ℝ} (hE : |E| ≤ 2) : mE E * (mE E + E) = -1 := by
  have hs : ((Real.sqrt (4 - E ^ 2) : ℝ) : ℂ) ^ 2 = 4 - (E : ℂ) ^ 2 := by
    exact_mod_cast sq_sqrt_four_sub hE
  have hI : I ^ 2 = -1 := I_sq
  simp only [mE]
  linear_combination ((Real.sqrt (4 - E ^ 2) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs

theorem mE_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (mE E).im := by
  rw [mE_im]
  have := abs_lt.mp hE
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

/-- `|m^{(E)}| = 1` for `|E| ≤ 2`. -/
theorem norm_mE {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1 := by
  have h2 : ‖mE E‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mE_re, mE_im]
    have := sq_sqrt_four_sub hE
    nlinarith
  have := norm_nonneg (mE E)
  nlinarith

/-- Uniqueness: `m^{(E)}` is the only root of `m(m + E) = -1` with `Im m > 0`. -/
theorem eq_mE {E : ℝ} (hE : |E| < 2) {m : ℂ} (hm : m * (m + E) = -1) (him : 0 < m.im) :
    m = mE E := by
  have h0 := mE_mul hE.le
  have h : (m - mE E) * (m + mE E + E) = 0 := by linear_combination hm - h0
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have him' := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at him'
    have := mE_im_pos hE
    linarith

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

/-- A square root of `z² - 4`. -/
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

theorem mscDisc_sq (z : ℂ) : mscDisc z ^ 2 = z ^ 2 - 4 :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

/-- The two roots of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2

noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2

/-- The Stieltjes transform of the semicircle law: the root of `m² + z m + 1 = 0` with
positive imaginary part (for `Im z > 0`). -/
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z

theorem msc_mul (z : ℂ) : msc z * (msc z + z) = -1 := by
  have hd := mscDisc_sq z
  unfold msc mscRoot₁ mscRoot₂
  split_ifs <;> linear_combination (1 / 4 : ℂ) * hd

theorem msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im := by
  have hd := mscDisc_sq z
  unfold msc
  split_ifs with h
  · exact h
  · push Not at h
    set r₁ := mscRoot₁ z
    set r₂ := mscRoot₂ z
    have hmul : r₁ * r₂ = 1 := by
      simp only [r₁, r₂, mscRoot₁, mscRoot₂]
      linear_combination (-1 / 4 : ℂ) * hd
    have hsum : r₁.im + r₂.im = -z.im := by
      have : r₁ + r₂ = -z := by simp only [r₁, r₂, mscRoot₁, mscRoot₂]; ring
      simpa using congrArg Complex.im this
    have hr₁ : r₁ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    have hr₂ : r₂ = r₁⁻¹ := eq_inv_of_mul_eq_one_right hmul
    have hN : 0 < Complex.normSq r₁ := Complex.normSq_pos.mpr hr₁
    have him : r₂.im * Complex.normSq r₁ = -r₁.im := by
      rw [hr₂, Complex.inv_im]
      field_simp
    by_contra hneg
    push Not at hneg
    have h1 : r₂.im * Complex.normSq r₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hN.le
    have h2 : r₁.im = 0 := by linarith
    have h3 : r₂.im < 0 := by linarith
    have h4 : r₂.im * Complex.normSq r₁ < 0 := mul_neg_of_neg_of_pos h3 hN
    linarith

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

/-- Definition 2.7: `z_t^{(E)} = E + (1 - t) m^{(E)}`. -/
noncomputable def zt (E t : ℝ) : ℂ := E + (1 - t) * mE E

/-- (2.35): `Im z_t^{(E)} = (1 - t) Im m^{(E)}`. -/
theorem zt_im (E t : ℝ) : (zt E t).im = (1 - t) * (mE E).im := by
  simp [zt]

end Flow

section Lemma28

/-- The energy of Lemma 2.8: `E = -2 Re m_sc(z) / |m_sc(z)|`. -/
noncomputable def lemE (z : ℂ) : ℝ := -2 * (msc z).re / ‖msc z‖

/-- The time of Lemma 2.8: `t = |m_sc(z)|²`. -/
noncomputable def lemT (z : ℂ) : ℝ := ‖msc z‖ ^ 2

variable {z : ℂ} (hz : 0 < z.im)
include hz

theorem norm_msc_pos : 0 < ‖msc z‖ :=
  norm_pos_iff.mpr fun h => by
    have := msc_im_pos hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this

theorem lemT_pos : 0 < lemT z := by
  have := norm_msc_pos hz
  unfold lemT
  positivity

theorem lemT_lt_one : lemT z < 1 := by
  have := norm_msc_lt_one hz
  have := norm_nonneg (msc z)
  unfold lemT
  nlinarith

/-- Real and imaginary parts of `u = m_sc(z)/|m_sc(z)|`, and `|u| = 1`. -/
theorem msc_div_norm_facts :
    let r := ‖msc z‖
    ((msc z / r).re ^ 2 + (msc z / r).im ^ 2 = 1) ∧ 0 < (msc z / r).im := by
  intro r
  have hr : 0 < r := norm_msc_pos hz
  have hr2 : r ^ 2 = (msc z).re ^ 2 + (msc z).im ^ 2 := by
    simp only [r, Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im]
  refine ⟨?_, div_pos (msc_im_pos hz) hr⟩
  field_simp
  linarith

theorem abs_lemE_lt_two : |lemE z| < 2 := by
  obtain ⟨h1, h2⟩ := msc_div_norm_facts hz
  have hre : lemE z = -2 * (msc z / (‖msc z‖ : ℂ)).re := by
    rw [lemE, Complex.div_ofReal_re]
    ring
  rw [hre, abs_lt]
  constructor <;> nlinarith

/-- The key step of Lemma 2.8: `m^{(E)} = m_sc(z) / |m_sc(z)|`. -/
theorem mE_lemE : mE (lemE z) = msc z / (‖msc z‖ : ℂ) := by
  obtain ⟨h1, h2⟩ := msc_div_norm_facts hz
  symm
  refine eq_mE (abs_lemE_lt_two hz) ?_ h2
  set u := msc z / (‖msc z‖ : ℂ) with hu
  have hre : lemE z = -2 * u.re := by
    rw [lemE, hu, Complex.div_ofReal_re]
    ring
  rw [hre]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, Complex.neg_re, Complex.one_re]
    nlinarith
  · simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, Complex.neg_im, Complex.one_im]
    ring

/-- Lemma 2.8: `t = m_sc(z)² / (m^{(E)})²`. -/
theorem lemT_eq : (lemT z : ℂ) = msc z ^ 2 / mE (lemE z) ^ 2 := by
  have hr : (‖msc z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_msc_pos hz).ne'
  have hm : msc z ≠ 0 := norm_pos_iff.mp (norm_msc_pos hz)
  rw [mE_lemE hz, lemT]
  push_cast
  field_simp

/-- (2.38): `m_sc(z) = t^{1/2} m^{(E)}`. -/
theorem msc_eq_sqrt_mul_mE : msc z = (Real.sqrt (lemT z) : ℂ) * mE (lemE z) := by
  have hr : (‖msc z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_msc_pos hz).ne'
  rw [mE_lemE hz, lemT, Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-- (2.37): `z = t^{-1/2} z_t^{(E)}`. -/
theorem eq_inv_sqrt_mul_zt : z = (Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z) := by
  set r := ‖msc z‖ with hr_def
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_msc_pos hz).ne'
  set u := mE (lemE z) with hu_def
  set E := lemE z
  have hu : u * (u + E) = -1 := mE_mul (abs_lemE_lt_two hz).le
  have hmu : msc z = r * u := by
    rw [hu_def, mE_lemE hz, ← hr_def]
    field_simp
  have hm := msc_mul z
  rw [hmu] at hm
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hsqrt : Real.sqrt (lemT z) = r := by rw [lemT, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, zt, lemT, ← hr_def]
  push_cast
  have key : (z * r - (E + (1 - r ^ 2) * u)) * u = 0 := by
    linear_combination hm - hu
  have h2 : z * r = E + (1 - r ^ 2) * u := by
    have := (mul_eq_zero.mp key).resolve_right hu0
    linear_combination this
  field_simp
  linear_combination h2

/-
Deferred: the `κ`-dependent part of Lemma 2.8 — `|E| ≤ 2 - cκ`, `t ≥ c_κ`, and (2.40)
`c_κ Im z ≤ Im z_t ≤ c_κ⁻¹ Im z` for `|Re z| ≤ 2 - κ`, `0 < Im z ≤ 1`.  These are real
analysis estimates used only in the stochastic layer (Sections 2.6-2.7, 5-7); they will be
added when that layer is started.
-/

end Lemma28

end RBM
