/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.BandLocalLawReg
import RBM1D.Flow.GUEBandL3
import RBM1D.Flow.EigenInterlacing
import RBM1D.Defs.MatrixMeasurable

/-!
# The averaged GUE local law from the `L ≡ 3` band local law

Formalization support for Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Theorem 2.6 Step 1.

## Main declaration

* `RBM.Gauss.gueLocalLaw_of_band` — the averaged band local law at the `L ≡ 3` dimensions `dL3`
  (`BandTracialLocalLaw dL3 κ` for every `κ > 0`) gives the averaged GUE local law
  `GUELocalLaw d` for every `Dims` `d`.

## Route

For the `d`-index `N` let `M = L·W`, `N' = 3⌈M/3⌉`, so that `M' = ouMatrixSize dL3 N' ∈ [M, M+2]`.
The GUE matrix of size `M` has the law of `c·B`, `c = √(M'/M) ≥ 1`, where `B` is a principal
`M × M` minor of the `L ≡ 3` band matrix of size `M'` (`gueMeasure_map_submatrix`,
`P_map_Xmat_dL3`). Cauchy interlacing (`trace_green_submatrix_sub_le`) compares the
traces of the resolvents of `B` and of the full matrix at `w = z/c`; `m_sc` is Lipschitz in the
bulk with constant `12/min κ 1` (copy of `step1_msc_lip_bulk`, `Flow/Step1Regularity.lean`). The
deterministic error `(2π + 4 + 72/κ' + 3 W'^{τ'/2})/(M Im z)` is absorbed by `N^{τ'}/(M Im z)`.

The sequence bookkeeping: with `τ', D` fixed, for each `N'` choose (classically) a "bad" index
`N₀` with `N₀ ↦ N'` if one exists (bad: the GUE probability exceeds `N₀^{-D}`) and put
`w N' = z N₀ / c`; otherwise `w N' = i`. The band law along `w` then rules out bad indices
eventually.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ### Bulk Lipschitz bound for `m_sc` (copies of `Flow/Step1Regularity.lean`) -/

private lemma gll_quad_diff {a z : ℂ} (ha : a * (a + z) = -1) (z' : ℂ) :
    (msc z' - a) * (a + msc z' + z') = -((z' - z) * a) := by
  have h := msc_mul z'
  linear_combination h - ha

private lemma gll_im_le_denom (a : ℂ) {z' : ℂ} (hz' : 0 < z'.im) :
    a.im ≤ (a + msc z' + z').im := by
  have h := msc_add_eq_neg_inv hz'
  have hm := msc_im_pos hz'
  have hne : msc z' ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hm; exact lt_irrefl _ hm
  have hpos : 0 < (msc z' + z').im := by
    rw [h, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hm (Complex.normSq_pos.mpr hne)
  have : (a + msc z' + z').im = a.im + (msc z' + z').im := by
    simp only [Complex.add_im]; ring
  linarith

private lemma gll_msc_sub_mul_im_le {a z z' : ℂ} (ha : a * (a + z) = -1)
    (hz' : 0 < z'.im) : ‖msc z' - a‖ * a.im ≤ ‖z' - z‖ * ‖a‖ := by
  have h1 : a.im ≤ ‖a + msc z' + z'‖ :=
    (gll_im_le_denom a hz').trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  calc ‖msc z' - a‖ * a.im ≤ ‖msc z' - a‖ * ‖a + msc z' + z'‖ :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖z' - z‖ * ‖a‖ := by
        rw [← norm_mul, gll_quad_diff ha z', norm_neg, norm_mul]

private lemma gll_msc_lip {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖msc z' - msc z‖ * (msc z).im ≤ ‖z' - z‖ := by
  refine (gll_msc_sub_mul_im_le (msc_mul z) hz').trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_msc_lt_one hz).le

/-- **Bulk lower bound**: `Im m_sc(z) ≥ κ'/12` for `|Re z| ≤ 2 - κ'/2`, `0 < Im z ≤ 3`. -/
private lemma gll_msc_im_ge {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (him0 : 0 < z.im) (him1 : z.im ≤ 3) :
    κ' / 12 ≤ (msc z).im := by
  set a := msc z with ha_def
  have hapos : 0 < a.im := msc_im_pos him0
  have hne : a ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hapos; exact lt_irrefl _ hapos
  have hnz : ‖z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him0] at this
    have h2 : |z.re| ≤ 2 := by linarith
    linarith
  set R := Complex.normSq a with hR_def
  have hRpos : 0 < R := Complex.normSq_pos.mpr hne
  have hR : (1 : ℝ) / 36 ≤ R := by
    have h1 := lemT_ge him0
    unfold lemT at h1
    rw [hR_def, Complex.normSq_eq_norm_sq]
    have h2 : ((1 + 5 : ℝ) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    calc (1 : ℝ) / 36 = ((1 + 5 : ℝ) ^ 2)⁻¹ := by norm_num
      _ ≤ ((1 + ‖z‖) ^ 2)⁻¹ := h2
      _ ≤ ‖msc z‖ ^ 2 := h1
  have hre_rel : z.re * R = -(a.re * (R + 1)) := by
    have h := congrArg Complex.re (msc_add_eq_neg_inv him0)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at h
    rw [← ha_def, ← hR_def] at h
    field_simp at h
    linear_combination h
  have hsq : z.re ^ 2 * R ^ 2 = a.re ^ 2 * (R + 1) ^ 2 := by
    have := congrArg (· ^ 2) hre_rel
    linear_combination this
  have hx : a.re ^ 2 * (4 * R) ≤ z.re ^ 2 * R ^ 2 := by
    rw [hsq]
    have : 4 * R ≤ (R + 1) ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hx2 : a.re ^ 2 * 4 ≤ z.re ^ 2 * R := by
    have h := hx
    have : a.re ^ 2 * (4 * R) = (a.re ^ 2 * 4) * R := by ring
    rw [this, show z.re ^ 2 * R ^ 2 = (z.re ^ 2 * R) * R by ring] at h
    exact le_of_mul_le_mul_right h hRpos
  have hzre2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    have := mul_le_mul hre hre h0 (by linarith)
    rw [← sq, sq_abs] at this
    simpa [sq] using this
  have hRdef : R = a.re ^ 2 + a.im ^ 2 := by
    rw [hR_def, Complex.normSq_apply]; ring
  have hy2 : κ' ^ 2 / 144 ≤ a.im ^ 2 := by
    have h1 : a.re ^ 2 * 4 ≤ (2 - κ' / 2) ^ 2 * R :=
      hx2.trans (mul_le_mul_of_nonneg_right hzre2 hRpos.le)
    have h2 : R * (κ' / 4) ≤ a.im ^ 2 := by nlinarith
    have h3 : κ' / 144 ≤ R * (κ' / 4) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : a.im ^ 2 < (κ' / 12) ^ 2 := by
    have := mul_lt_mul'' hcon hcon hapos.le hapos.le
    nlinarith
  nlinarith

/-- `msc` is Lipschitz on the bulk domain, with the bulk lower bound in place of `Im msc`
(copy of `step1_msc_lip_bulk`, `Flow/Step1Regularity.lean`). -/
private theorem gll_msc_lip_bulk {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z z' : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (hz0 : 0 < z.im) (hz1 : z.im ≤ 3) (hz'0 : 0 < z'.im) :
    ‖msc z' - msc z‖ ≤ ‖z' - z‖ * (12 / κ') := by
  have hb := gll_msc_im_ge hκ0 hκ1 hre hz0 hz1
  have hl := gll_msc_lip hz0 hz'0
  have h1 : ‖msc z' - msc z‖ * (κ' / 12) ≤ ‖msc z' - msc z‖ * (msc z).im :=
    mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have h2 : ‖msc z' - msc z‖ * (κ' / 12) ≤ ‖z' - z‖ := h1.trans hl
  have h3 : ‖msc z' - msc z‖ ≤ ‖z' - z‖ / (κ' / 12) := (le_div_iff₀ (by positivity)).mpr h2
  calc ‖msc z' - msc z‖ ≤ ‖z' - z‖ / (κ' / 12) := h3
    _ = ‖z' - z‖ * (12 / κ') := by field_simp

/-! ### Scaling and measurability of the resolvent trace -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem gll_inv_smul (c : ℂ) (hc : c ≠ 0) (X : Matrix n n ℂ) :
    (c • X)⁻¹ = c⁻¹ • X⁻¹ := by
  by_cases h : IsUnit X.det
  · have := Matrix.inv_smul' X (Units.mk0 c hc) h
    simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    exact this
  · have h' : ¬ IsUnit (c • X).det := by
      rw [Matrix.det_smul, isUnit_iff_ne_zero, mul_ne_zero_iff, not_and_or, not_not, not_not]
      right; exact not_not.mp (fun h2 => h (isUnit_iff_ne_zero.mpr h2))
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

/-- `(cA − z)⁻¹ = c⁻¹ (A − z/c)⁻¹`, for every matrix `A` and every `c ≠ 0`. -/
private theorem gll_green_smul (c : ℂ) (hc : c ≠ 0) (A : Matrix n n ℂ) (z : ℂ) :
    RBM.green (c • A) z = c⁻¹ • RBM.green A (z / c) := by
  unfold RBM.green
  have : c • A - z • (1 : Matrix n n ℂ) = c • (A - (z / c) • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ z hc]
  rw [this, gll_inv_smul c hc]

private theorem gll_trace_green_smul (c : ℂ) (hc : c ≠ 0) (A : Matrix n n ℂ) (z : ℂ) :
    (RBM.green (c • A) z).trace = c⁻¹ * (RBM.green A (z / c)).trace := by
  rw [gll_green_smul c hc, Matrix.trace_smul, smul_eq_mul]

private theorem gll_measurable_trace_green {Θ : Type*} [MeasurableSpace Θ]
    {g : Θ → Matrix n n ℂ} (hg : Measurable g) (z : ℂ) :
    Measurable fun x => (RBM.green (g x) z).trace := by
  unfold Matrix.trace
  refine Finset.measurable_sum _ fun i _ => ?_
  have hsub : Measurable fun x => g x - z • (1 : Matrix n n ℂ) :=
    ((continuous_id.sub continuous_const).measurable).comp hg
  exact measurable_matrix_inv_apply hsub i i

end Resolvent

/-! ### The deterministic core: one index `N`, one sample -/

/-- **Deterministic absorption.** `X = tr G_B(w)`, `Y = tr G_{A'}(w)` with `w = z/c`,
`‖Y − X‖ ≤ 2(π+1)/Im w` (interlacing, `r ≤ 2`), and the band-good bound on `Y/M'`, give the
GUE-scale bound on `M⁻¹ c⁻¹ X = s_{cB}(z)`. -/
private theorem gll_core {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz0 : 0 < z.im) (hz1 : z.im ≤ 1)
    (hre : |z.re| ≤ 2 - κ) {M M' c : ℝ} (hM : 0 < M) (hc1 : 1 ≤ c) (hcsq : c ^ 2 * M = M')
    (hr : M' ≤ M + 2) {X Y : ℂ}
    (hXY : ‖Y - X‖ ≤ 2 * (Real.pi + 1) / (z / (c : ℂ)).im)
    {V : ℝ} (hY : ‖(M' : ℂ)⁻¹ * Y - msc (z / (c : ℂ))‖ ≤ 3 * c * V / (M' * z.im)) :
    ‖(M : ℂ)⁻¹ * ((c : ℂ)⁻¹ * X) - msc z‖ ≤
      (2 * Real.pi + 4 + 72 / min κ 1 + 3 * V) / (M * z.im) := by
  set η := z.im with hη
  set κ' := min κ 1 with hκ'
  set w := z / (c : ℂ) with hw
  have hc0 : 0 < c := by linarith
  have hM' : 0 < M' := by rw [← hcsq]; positivity
  have hwim : w.im = η / c := by rw [hw, Complex.div_ofReal_im]
  have hw0 : 0 < w.im := by rw [hwim]; positivity
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hcm1 : c - 1 ≤ 2 / M := by
    rw [le_div_iff₀ hM]
    nlinarith
  -- the algebraic decomposition
  have hM'c : ((M' : ℝ) : ℂ) = (c : ℂ) ^ 2 * (M : ℂ) := by
    rw [← hcsq]; push_cast; ring
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hdec : (M : ℂ)⁻¹ * ((c : ℂ)⁻¹ * X) - msc z =
      ((M : ℂ)⁻¹ * (c : ℂ)⁻¹) * (X - Y) + (c : ℂ) * ((M' : ℂ)⁻¹ * Y - msc w) +
        ((c : ℂ) - 1) * msc w + (msc w - msc z) := by
    rw [hM'c]
    field_simp
    ring
  -- term 1: interlacing
  have ht1 : ‖((M : ℂ)⁻¹ * (c : ℂ)⁻¹) * (X - Y)‖ ≤ 2 * (Real.pi + 1) / (M * η) := by
    rw [norm_mul, norm_sub_rev, norm_mul, norm_inv, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hM.le, Real.norm_of_nonneg hc0.le]
    calc M⁻¹ * c⁻¹ * ‖Y - X‖ ≤ M⁻¹ * c⁻¹ * (2 * (Real.pi + 1) / w.im) :=
          mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = 2 * (Real.pi + 1) / (M * η) := by
          rw [hwim]; field_simp
  -- term 2: the band law
  have ht2 : ‖(c : ℂ) * ((M' : ℂ)⁻¹ * Y - msc w)‖ ≤ 3 * V / (M * η) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    calc c * ‖(M' : ℂ)⁻¹ * Y - msc w‖ ≤ c * (3 * c * V / (M' * η)) :=
          mul_le_mul_of_nonneg_left hY hc0.le
      _ = 3 * V / (M * η) := by
          rw [← hcsq]; field_simp
  -- term 3: `|c − 1|·|msc|`
  have ht3 : ‖((c : ℂ) - 1) * msc w‖ ≤ 2 / M := by
    rw [norm_mul]
    have h1 : ‖(c : ℂ) - 1‖ = c - 1 := by
      rw [show (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    rw [h1]
    calc (c - 1) * ‖msc w‖ ≤ (c - 1) * 1 :=
          mul_le_mul_of_nonneg_left (norm_msc_lt_one hw0).le (by linarith)
      _ ≤ 2 / M := by linarith
  -- term 4: bulk Lipschitz bound for `msc`
  have ht4 : ‖msc w - msc z‖ ≤ 72 / κ' / M := by
    have hre' : |z.re| ≤ 2 - κ' / 2 := by
      have : κ' ≤ κ := min_le_left _ _
      linarith
    have hlip := gll_msc_lip_bulk hκ'0 hκ'1 hre' hz0 (by linarith) hw0
    have hnz : ‖z‖ ≤ 3 := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz0] at this
      have : κ ≥ 0 := hκ.le
      linarith
    have hwz : ‖w - z‖ ≤ 3 * (2 / M) := by
      have heq : w - z = z * (((c⁻¹ - 1 : ℝ)) : ℂ) := by
        rw [hw]; push_cast; field_simp
      rw [heq, norm_mul, Complex.norm_real]
      have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      have hci' : 1 - c⁻¹ ≤ c - 1 := by
        have : c⁻¹ * c = 1 := inv_mul_cancel₀ hc0.ne'
        nlinarith [sq_nonneg (c - 1), inv_pos.mpr hc0]
      rw [Real.norm_of_nonpos (by linarith)]
      calc ‖z‖ * -(c⁻¹ - 1) ≤ 3 * (c - 1) := by
            apply mul_le_mul hnz (by linarith) (by linarith) (by norm_num)
        _ ≤ 3 * (2 / M) := by linarith
    calc ‖msc w - msc z‖ ≤ ‖w - z‖ * (12 / κ') := hlip
      _ ≤ 3 * (2 / M) * (12 / κ') := mul_le_mul_of_nonneg_right hwz (by positivity)
      _ = 72 / κ' / M := by field_simp; ring
  -- assemble
  have hMη : M * η ≤ M := by nlinarith
  have hsmall : (2 + 72 / κ') / M ≤ (2 + 72 / κ') / (M * η) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hMη
  rw [hdec]
  calc ‖((M : ℂ)⁻¹ * (c : ℂ)⁻¹) * (X - Y) + (c : ℂ) * ((M' : ℂ)⁻¹ * Y - msc w) +
        ((c : ℂ) - 1) * msc w + (msc w - msc z)‖
      ≤ ‖((M : ℂ)⁻¹ * (c : ℂ)⁻¹) * (X - Y)‖ + ‖(c : ℂ) * ((M' : ℂ)⁻¹ * Y - msc w)‖ +
        ‖((c : ℂ) - 1) * msc w‖ + ‖msc w - msc z‖ := norm_add₄_le
    _ ≤ 2 * (Real.pi + 1) / (M * η) + 3 * V / (M * η) + 2 / M + 72 / κ' / M := by
        linarith
    _ = (2 * Real.pi + 2 + 3 * V) / (M * η) + (2 + 72 / κ') / M := by
        field_simp; ring
    _ ≤ (2 * Real.pi + 2 + 3 * V) / (M * η) + (2 + 72 / κ') / (M * η) := by linarith
    _ = (2 * Real.pi + 4 + 72 / κ' + 3 * V) / (M * η) := by
        field_simp; ring

/-! ### Index bookkeeping: `N ↦ N' = 3⌈M/3⌉` and the scale `c = √(M'/M)` -/

/-- The `dL3`-index attached to the `d`-index `N`: `N' = 3⌈M/3⌉`, `M = ouMatrixSize d N`. -/
private def gllN' (d : Dims) (N : ℕ) : ℕ := 3 * ((ouMatrixSize d N + 2) / 3)

/-- The scale `c = √(M'/M) ≥ 1`, written as `(√(M/M'))⁻¹` to match `gueMeasure_map_submatrix`. -/
private noncomputable def gllc (d : Dims) (N : ℕ) : ℝ :=
  (Real.sqrt ((ouMatrixSize d N : ℝ) / (ouMatrixSize dL3 (gllN' d N) : ℝ)))⁻¹

private theorem gll_W' (d : Dims) (N : ℕ) :
    dL3.W (gllN' d N) = (ouMatrixSize d N + 2) / 3 := by
  have hM := ouMatrixSize_pos d N
  rw [dL3_W, gllN']
  have h1 : 3 * ((ouMatrixSize d N + 2) / 3) / 3 = (ouMatrixSize d N + 2) / 3 := by omega
  rw [h1]
  exact max_eq_right (by omega)

private theorem gll_M' (d : Dims) (N : ℕ) :
    ouMatrixSize dL3 (gllN' d N) = 3 * dL3.W (gllN' d N) := by
  rw [ouMatrixSize, dL3_L]

private theorem gll_M'_eq (d : Dims) (N : ℕ) : ouMatrixSize dL3 (gllN' d N) = gllN' d N := by
  rw [gll_M', gll_W', gllN']

private theorem gll_M_le (d : Dims) (N : ℕ) : ouMatrixSize d N ≤ ouMatrixSize dL3 (gllN' d N) := by
  rw [gll_M'_eq, gllN']; omega

private theorem gll_M'_le (d : Dims) (N : ℕ) :
    ouMatrixSize dL3 (gllN' d N) ≤ ouMatrixSize d N + 2 := by
  rw [gll_M'_eq, gllN']; omega

private theorem gll_card (d : Dims) (N : ℕ) : Fintype.card (d.Idx N) = ouMatrixSize d N := by
  simp [Dims.Idx, ZMod.card, ouMatrixSize]

private theorem gllc_one_le (d : Dims) (N : ℕ) : 1 ≤ gllc d N := by
  have hM : (0 : ℝ) < ouMatrixSize d N := by exact_mod_cast ouMatrixSize_pos d N
  have hM' : (0 : ℝ) < ouMatrixSize dL3 (gllN' d N) := by
    exact_mod_cast ouMatrixSize_pos dL3 _
  have hle : (ouMatrixSize d N : ℝ) ≤ ouMatrixSize dL3 (gllN' d N) := by
    exact_mod_cast gll_M_le d N
  unfold gllc
  apply one_le_inv_iff₀.mpr
  refine ⟨Real.sqrt_pos.mpr (by positivity), ?_⟩
  rw [Real.sqrt_le_one]
  exact (div_le_one hM').mpr hle

private theorem gllc_sq (d : Dims) (N : ℕ) :
    gllc d N ^ 2 * (ouMatrixSize d N : ℝ) = ouMatrixSize dL3 (gllN' d N) := by
  have hM : (0 : ℝ) < ouMatrixSize d N := by exact_mod_cast ouMatrixSize_pos d N
  have hM' : (0 : ℝ) < ouMatrixSize dL3 (gllN' d N) := by
    exact_mod_cast ouMatrixSize_pos dL3 _
  unfold gllc
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-! ### The transfer at one index `N` -/

/-- **Transfer at one index.** The GUE bad event at `(N, z)` with any threshold `A` dominating
the deterministic error is contained, in law, in the band bad event at `(N', z/c)`. -/
private theorem gll_transfer (d : Dims) (N : ℕ) {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz0 : 0 < z.im)
    (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 2 - κ) {A τb : ℝ}
    (hA : (2 * Real.pi + 4 + 72 / min κ 1 + 3 * ((dL3.W (gllN' d N) : ℝ) ^ τb)) /
      (msize d N * z.im) ≤ A) :
    gueMeasure d N {ω | A < ‖RBM.stieltjes (Xmat d N ω) z - msc z‖} ≤
      (Gauss.band dL3).P {ω | ∃ _u : Unit,
        ((Gauss.band dL3).W (gllN' d N) : ℝ) ^ τb *
            ((Gauss.band dL3).zScale (gllN' d N) (z / (gllc d N : ℂ)))⁻¹ <
          ‖(((Gauss.band dL3).L (gllN' d N) * (Gauss.band dL3).W (gllN' d N) : ℕ) : ℂ)⁻¹ *
              (green (Xmat dL3 (gllN' d N) ω) (z / (gllc d N : ℂ))).trace -
            msc (z / (gllc d N : ℂ))‖} := by
  classical
  set N' := gllN' d N with hN'
  set c := gllc d N with hc
  set w := z / (c : ℂ) with hw
  set Mn := ouMatrixSize d N with hMn
  set Mn' := ouMatrixSize dL3 N' with hMn'
  set c₀ := Real.sqrt ((Mn : ℝ) / (Mn' : ℝ)) with hc₀
  set thr := ((Gauss.band dL3).W N' : ℝ) ^ τb * ((Gauss.band dL3).zScale N' w)⁻¹ with hthr
  have hc1 : 1 ≤ c := gllc_one_le d N
  have hc0 : 0 < c := by linarith
  have hcc₀ : (c : ℂ) * (c₀ : ℂ) = 1 := by
    have : c * c₀ = 1 := by rw [hc, gllc, ← hc₀]; exact inv_mul_cancel₀ (by
      have := hc0; rw [hc, gllc, ← hc₀] at this; exact (inv_pos.mp this).ne')
    exact_mod_cast this
  have hM : (0 : ℝ) < Mn := by exact_mod_cast ouMatrixSize_pos d N
  have hMM' : Mn ≤ Mn' := gll_M_le d N
  have hM'le : Mn' ≤ Mn + 2 := gll_M'_le d N
  obtain ⟨e, he⟩ := exists_idxKey_strictMono_embedding d dL3 N N' hMM'
  have hmap := gueMeasure_map_submatrix d dL3 N N' e he
  -- the matrix sets
  let S : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
    {B | A < ‖RBM.stieltjes ((c : ℂ) • B) z - msc z‖}
  let T : Set (Matrix (dL3.Idx N') (dL3.Idx N') ℂ) :=
    {A' | thr < ‖((Mn' : ℕ) : ℂ)⁻¹ * (green A' w).trace - msc w‖}
  have hS : MeasurableSet S := by
    refine measurableSet_lt measurable_const ?_
    refine Measurable.norm (Measurable.sub ?_ measurable_const)
    unfold RBM.stieltjes
    exact measurable_const.mul
      (gll_measurable_trace_green (continuous_const_smul _).measurable z)
  have hT : MeasurableSet T := by
    refine measurableSet_lt measurable_const ?_
    refine Measurable.norm (Measurable.sub ?_ measurable_const)
    exact measurable_const.mul (gll_measurable_trace_green measurable_id w)
  have hXm : ∀ (d' : Dims) (K : ℕ), Measurable (Xmat d' K) := fun d' K =>
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => measurable_Xentry d' K i j
  have hφ : Measurable fun ω : Ω d => ((c₀ : ℝ) : ℂ) • Xmat d N ω :=
    (continuous_const_smul _).measurable.comp (hXm d N)
  have hsub : Measurable fun ω : Ω dL3 => (Xmat dL3 N' ω).submatrix e e := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact measurable_Xentry dL3 N' (e i) (e j)
  -- the GUE bad event is a preimage of `S`
  have hbad : {ω | A < ‖RBM.stieltjes (Xmat d N ω) z - msc z‖} =
      (fun ω : Ω d => ((c₀ : ℝ) : ℂ) • Xmat d N ω) ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, smul_smul, hcc₀, one_smul]
  -- the band bad event is a preimage of `T`
  have hband : {ω | ∃ _u : Unit, thr <
      ‖(((Gauss.band dL3).L N' * (Gauss.band dL3).W N' : ℕ) : ℂ)⁻¹ *
          (green (Xmat dL3 N' ω) w).trace - msc w‖} = Xmat dL3 N' ⁻¹' T := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, T, exists_const]
    rfl
  -- deterministic inclusion
  have hincl : (fun ω : Ω dL3 => (Xmat dL3 N' ω).submatrix e e) ⁻¹' S ⊆ Xmat dL3 N' ⁻¹' T := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, S, T] at hω ⊢
    by_contra hgood
    push Not at hgood
    set A' := Xmat dL3 N' ω
    have hA' : A'.IsHermitian := Xmat_isHermitian dL3 N' ω
    set B := A'.submatrix e e
    have hwim : w.im = z.im / c := by rw [hw, Complex.div_ofReal_im]
    have hw0 : 0 < w.im := by rw [hwim]; positivity
    have hint := trace_green_submatrix_sub_le hA' e hw0
    have hcards : ((Fintype.card (dL3.Idx N') - Fintype.card (d.Idx N) : ℕ) : ℝ) ≤ 2 := by
      rw [gll_card, gll_card]
      have : Mn' - Mn ≤ 2 := by omega
      exact_mod_cast this
    have hXY : ‖(green A' w).trace - (green B w).trace‖ ≤ 2 * (Real.pi + 1) / w.im := by
      refine hint.trans ?_
      apply div_le_div_of_nonneg_right _ hw0.le
      exact mul_le_mul_of_nonneg_right hcards (by positivity)
    -- the band threshold
    have hW'pos : (0 : ℝ) < ((Gauss.band dL3).W N' : ℝ) := by
      exact_mod_cast dL3.W_pos N'
    have hM'W : (Mn' : ℝ) = 3 * ((Gauss.band dL3).W N' : ℝ) := by
      rw [hMn', gll_M']; push_cast; rfl
    have hthr_le : thr ≤ 3 * c * (((Gauss.band dL3).W N' : ℝ) ^ τb) / ((Mn' : ℝ) * z.im) := by
      rw [hthr, RBM.Band.zScale]
      have hell := RBM.Band.one_le_ellZ ((Gauss.band dL3).L N') w
      have hV : 0 ≤ ((Gauss.band dL3).W N' : ℝ) ^ τb := Real.rpow_nonneg hW'pos.le _
      have hden : ((Gauss.band dL3).W N' : ℝ) * w.im ≤
          ((Gauss.band dL3).W N' : ℝ) * RBM.ellZ ((Gauss.band dL3).L N') w * w.im := by
        have : ((Gauss.band dL3).W N' : ℝ) * 1 ≤
            ((Gauss.band dL3).W N' : ℝ) * RBM.ellZ ((Gauss.band dL3).L N') w :=
          mul_le_mul_of_nonneg_left hell hW'pos.le
        nlinarith
      calc ((Gauss.band dL3).W N' : ℝ) ^ τb *
            (((Gauss.band dL3).W N' : ℝ) * RBM.ellZ ((Gauss.band dL3).L N') w * w.im)⁻¹
          ≤ ((Gauss.band dL3).W N' : ℝ) ^ τb * (((Gauss.band dL3).W N' : ℝ) * w.im)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hden) hV
        _ = 3 * c * (((Gauss.band dL3).W N' : ℝ) ^ τb) / ((Mn' : ℝ) * z.im) := by
            rw [hwim, hM'W]; field_simp
    have hY : ‖((Mn' : ℝ) : ℂ)⁻¹ * (green A' w).trace - msc w‖ ≤
        3 * c * (((Gauss.band dL3).W N' : ℝ) ^ τb) / ((Mn' : ℝ) * z.im) := by
      have : ((Mn' : ℝ) : ℂ) = ((Mn' : ℕ) : ℂ) := by push_cast; rfl
      rw [this]; exact hgood.trans hthr_le
    have hcore := gll_core hκ hz0 hz1 hre hM hc1 (gllc_sq d N) (by exact_mod_cast hM'le)
      (X := (green B w).trace) (Y := (green A' w).trace) hXY hY
    have hst : RBM.stieltjes ((c : ℂ) • B) z = ((Mn : ℝ) : ℂ)⁻¹ * ((c : ℂ)⁻¹ *
        (green B w).trace) := by
      unfold RBM.stieltjes
      rw [gll_trace_green_smul (c : ℂ) (by exact_mod_cast hc0.ne') B z, gll_card]
      push_cast; rfl
    rw [hst] at hω
    have hA2 : (2 * Real.pi + 4 + 72 / min κ 1 + 3 * ((Gauss.band dL3).W N' : ℝ) ^ τb) /
        ((Mn : ℝ) * z.im) ≤ A := hA
    linarith
  rw [hbad]
  calc gueMeasure d N ((fun ω : Ω d => ((c₀ : ℝ) : ℂ) • Xmat d N ω) ⁻¹' S)
      = (gueMeasure d N).map (fun ω : Ω d => ((c₀ : ℝ) : ℂ) • Xmat d N ω) S :=
        (Measure.map_apply hφ hS).symm
    _ = (gueMeasure dL3 N').map (fun ω => (Xmat dL3 N' ω).submatrix e e) S := by rw [hmap]
    _ = gueMeasure dL3 N' ((fun ω => (Xmat dL3 N' ω).submatrix e e) ⁻¹' S) :=
        Measure.map_apply hsub hS
    _ ≤ gueMeasure dL3 N' (Xmat dL3 N' ⁻¹' T) := measure_mono hincl
    _ = (gueMeasure dL3 N').map (Xmat dL3 N') T := (Measure.map_apply (hXm dL3 N') hT).symm
    _ = (P dL3).map (Xmat dL3 N') T := by rw [P_map_Xmat_dL3]
    _ = P dL3 (Xmat dL3 N' ⁻¹' T) := Measure.map_apply (hXm dL3 N') hT
    _ = _ := by rw [← hband]; rfl

/-! ### Exponent bookkeeping (real inequalities) -/

/-- Lower bound transfer: `N₀^{-1+τ₀} ≤ x`, `N₀ ≤ 2N'`, `c ≤ 2`, `4 ≤ N'^{τ₀/2}` give
`N'^{-1+τ₀/2} ≤ x/c`. -/
private theorem gll_lower {τ₀ x N₀ N' c : ℝ} (hτ₀ : 0 < τ₀) (hτ₀1 : τ₀ ≤ 1 / 2) (hN₀ : 1 ≤ N₀)
    (hN₀N' : N₀ ≤ 2 * N') (hc : 1 ≤ c) (hc2 : c ≤ 2) (hx : N₀ ^ (-1 + τ₀) ≤ x)
    (h4 : 4 ≤ N' ^ (τ₀ / 2)) : N' ^ (-1 + τ₀ / 2) ≤ x / c := by
  have hN'0 : 0 < N' := by linarith
  have h1 : (2 * N') ^ (-1 + τ₀) ≤ N₀ ^ (-1 + τ₀) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hN₀N' (by linarith)
  have h2 : (2 * N') ^ (-1 + τ₀) = (2 : ℝ) ^ (-1 + τ₀) * N' ^ (-1 + τ₀) :=
    Real.mul_rpow (by norm_num) hN'0.le
  have h3 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-1 + τ₀) := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (-1 : ℝ) ≤ -1 + τ₀ by linarith)
    rw [Real.rpow_neg_one] at this
    linarith
  have h5 : N' ^ (-1 + τ₀) = N' ^ (-1 + τ₀ / 2) * N' ^ (τ₀ / 2) := by
    rw [← Real.rpow_add hN'0]; ring_nf
  have hp : 0 ≤ N' ^ (-1 + τ₀ / 2) := Real.rpow_nonneg hN'0.le _
  have hp' : 0 ≤ N' ^ (-1 + τ₀) := Real.rpow_nonneg hN'0.le _
  have hx2 : 2 * N' ^ (-1 + τ₀ / 2) ≤ x := by
    have : 1 / 2 * N' ^ (-1 + τ₀) ≤ x := by
      calc 1 / 2 * N' ^ (-1 + τ₀) ≤ (2 : ℝ) ^ (-1 + τ₀) * N' ^ (-1 + τ₀) :=
            mul_le_mul_of_nonneg_right h3 hp'
        _ ≤ x := by rw [← h2]; exact h1.trans hx
    rw [h5] at this
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Probability transfer: `N'^{-2D} ≤ N₀^{-D}` for `4 ≤ N₀ ≤ 2N'`. -/
private theorem gll_prob {D N₀ N' : ℝ} (hD : 0 < D) (h4 : 4 ≤ N₀) (hN : N₀ ≤ 2 * N') :
    N' ^ (-(2 * D)) ≤ N₀ ^ (-D) := by
  have hN'0 : 0 < N' := by linarith
  have hsq : N₀ ≤ N' ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  rw [show -(2 * D) = 2 * (-D) by ring, Real.rpow_mul hN'0.le]
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hsq (by linarith)

/-- Absorption: the deterministic error is below the GUE threshold. -/
private theorem gll_absorb {K τ' W N₀ Mη : ℝ} (hτ' : 0 < τ') (hMη : 0 < Mη) (hW0 : 0 ≤ W)
    (hN₀ : 0 < N₀)
    (hWN : W ≤ N₀) (hK : K ≤ N₀ ^ τ' / 2) (h6 : 6 ≤ N₀ ^ (τ' / 2)) :
    (K + 3 * W ^ (τ' / 2)) / Mη ≤ N₀ ^ τ' * Mη⁻¹ := by
  have hsplit : N₀ ^ τ' = N₀ ^ (τ' / 2) * N₀ ^ (τ' / 2) := by
    rw [← Real.rpow_add hN₀]; ring_nf
  have hW : W ^ (τ' / 2) ≤ N₀ ^ (τ' / 2) := Real.rpow_le_rpow hW0 hWN (by positivity)
  have hnum : K + 3 * W ^ (τ' / 2) ≤ N₀ ^ τ' := by
    rw [hsplit] at hK ⊢
    nlinarith
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hnum hMη.le

private theorem gllc_le_two (d : Dims) (N : ℕ) : gllc d N ≤ 2 := by
  have hsq := gllc_sq d N
  have hc1 := gllc_one_le d N
  have hM : (1 : ℝ) ≤ ouMatrixSize d N := by exact_mod_cast ouMatrixSize_pos d N
  have hle : (ouMatrixSize dL3 (gllN' d N) : ℝ) ≤ ouMatrixSize d N + 2 := by
    exact_mod_cast gll_M'_le d N
  by_contra hc
  push Not at hc
  have h4 : 4 < gllc d N ^ 2 := by nlinarith
  have : 4 * (ouMatrixSize d N : ℝ) < gllc d N ^ 2 * ouMatrixSize d N :=
    mul_lt_mul_of_pos_right h4 (by linarith)
  linarith

/-! ### Step 0 (b): the hypothesis `hL3` is a real input -/

/-! ### The main theorem -/

/-- **G4-7c.** The averaged band local law at the `L ≡ 3` dimensions `dL3`, for every `κ > 0`,
gives the averaged GUE local law for every `Dims` `d`. Parameters: `τ₀ = min τ (1/2)`,
band `τ = τ₀/2`, band `τ' = τ'/2`, band `D = 2D`; the band spectral sequence `w` is built from
`κ, τ', D, z` (a bad representative per `dL3`-index, default `i`). -/
theorem gueLocalLaw_of_band (d : Dims) (hL3 : ∀ κ > (0 : ℝ), BandTracialLocalLaw dL3 κ) :
    GUELocalLaw d := by
  classical
  intro κ hκ τ hτ z him_pos him_le_one habs_re him_ge τ' hτ' D hD
  -- `κ > 2`: the hypotheses are contradictory
  by_cases hκ2 : 2 < κ
  · exfalso
    have h0 := habs_re 0
    have := abs_nonneg (z 0).re
    linarith
  push Not at hκ2
  set τ₀ : ℝ := min τ (1 / 2) with hτ₀
  have hτ₀0 : 0 < τ₀ := lt_min hτ (by norm_num)
  have hτ₀1 : τ₀ ≤ 1 / 2 := min_le_right _ _
  have him_ge' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ₀) ≤ (z N).im := by
    filter_upwards [him_ge, eventually_ge_atTop 1] with N hN hN1
    refine le_trans ?_ hN
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
      (by linarith [min_le_left τ (1 / 2)])
  -- bad indices and the band spectral sequence
  set bad : ℕ → Prop := fun N => ENNReal.ofReal ((N : ℝ) ^ (-D)) <
      gueMeasure d N {ω | (N : ℝ) ^ τ' * (msize d N * (z N).im)⁻¹ <
        ‖RBM.stieltjes (Xmat d N ω) (z N) - msc (z N)‖} with hbad
  set w : ℕ → ℂ := fun N' => if h : ∃ N₀, bad N₀ ∧ gllN' d N₀ = N' then
      z (Classical.choose h) / (gllc d (Classical.choose h) : ℂ) else Complex.I with hw
  -- index thresholds
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp d.dim
  obtain ⟨Nz, hNz⟩ := eventually_atTop.mp him_ge'
  set F := (Finset.range N1).sup (gllN' d) with hF
  have hlarge : ∀ N₀, F < gllN' d N₀ → N1 ≤ N₀ := by
    intro N₀ h
    by_contra hlt
    push Not at hlt
    have : gllN' d N₀ ≤ F := Finset.le_sup (f := gllN' d) (Finset.mem_range.mpr hlt)
    omega
  have hsize : ∀ N₀, N1 ≤ N₀ →
      ouMatrixSize d N₀ ≤ N₀ ∧ N₀ ≤ 2 * ouMatrixSize d N₀ ∧
        ouMatrixSize d N₀ ≤ gllN' d N₀ ∧ gllN' d N₀ ≤ ouMatrixSize d N₀ + 2 := by
    intro N₀ h
    obtain ⟨h1, h2⟩ := hN1 N₀ h
    have h3 := gll_M_le d N₀
    have h4 := gll_M'_le d N₀
    rw [gll_M'_eq] at h3 h4
    refine ⟨?_, ?_, h3, h4⟩
    · rw [ouMatrixSize, Nat.mul_comm (d.L N₀)]; exact h1
    · rw [ouMatrixSize, Nat.mul_comm (d.L N₀)]; exact h2
  -- the properties of `w`
  have hw_pos : ∀ N', 0 < (w N').im := by
    intro N'
    simp only [hw]
    split_ifs with h
    · rw [Complex.div_ofReal_im]
      exact div_pos (him_pos _) (by linarith [gllc_one_le d (Classical.choose h)])
    · simp
  have hw_le : ∀ N', (w N').im ≤ 1 := by
    intro N'
    simp only [hw]
    split_ifs with h
    · rw [Complex.div_ofReal_im]
      exact (div_le_self (him_pos _).le (gllc_one_le d _)).trans (him_le_one _)
    · simp
  have hw_re : ∀ N', |(w N').re| ≤ 2 - κ := by
    intro N'
    simp only [hw]
    split_ifs with h
    · rw [Complex.div_ofReal_re, abs_div,
        abs_of_pos (by linarith [gllc_one_le d (Classical.choose h)] : (0 : ℝ) < gllc d _)]
      exact (div_le_self (abs_nonneg _) (gllc_one_le d _)).trans (habs_re _)
    · simp; linarith
  obtain ⟨Nw, hNw⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (half_pos hτ₀0)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (4 : ℝ))
  have hw_ge : ∀ᶠ N' : ℕ in atTop, (N' : ℝ) ^ (-1 + τ₀ / 2) ≤ (w N').im := by
    refine eventually_atTop.mpr ⟨max (F + 1) (max (Nz + 2) (max Nw 3)), fun N' hN' => ?_⟩
    have hF1 : F + 1 ≤ N' := le_of_max_le_left hN'
    have hNz2 : Nz + 2 ≤ N' := le_of_max_le_left (le_of_max_le_right hN')
    have hNw' : Nw ≤ N' := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hN'))
    have h3 : 3 ≤ N' := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hN'))
    simp only [hw]
    split_ifs with h
    · obtain ⟨-, hf⟩ := Classical.choose_spec h
      set N₀ := Classical.choose h
      have hN1₀ : N1 ≤ N₀ := hlarge N₀ (by omega)
      obtain ⟨hs1, hs2, hs3, hs4⟩ := hsize N₀ hN1₀
      rw [Complex.div_ofReal_im]
      refine gll_lower hτ₀0 hτ₀1 (by exact_mod_cast (show 1 ≤ N₀ by omega))
        (by exact_mod_cast (show N₀ ≤ 2 * N' by omega)) (gllc_one_le d N₀) (gllc_le_two d N₀)
        (hNz N₀ (by omega)) (hNw N' hNw')
    · simp only [Complex.I_im]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ N' by omega))
        (by linarith)
  -- the band law along `w`
  have hB := hL3 κ hκ (τ₀ / 2) (half_pos hτ₀0) w hw_pos hw_le hw_re hw_ge (τ' / 2)
    (half_pos hτ') (2 * D) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hB
  -- absorption thresholds in the `d`-index
  set K : ℝ := 2 * Real.pi + 4 + 72 / min κ 1 with hK
  have hKev : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ τ' / 2 := by
    filter_upwards [((tendsto_rpow_atTop hτ').comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (2 * K)] with N hN
    simp only [Function.comp] at hN
    linarith
  have h6ev : ∀ᶠ N : ℕ in atTop, (6 : ℝ) ≤ (N : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ')).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 6
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp (hKev.and (h6ev.and (eventually_ge_atTop 4)))
  set Nthr := max (F + 1) (max N2 (Na + 2)) with hNthr
  refine eventually_atTop.mpr ⟨max N1 (2 * Nthr), fun N hN => ?_⟩
  have hN1N : N1 ≤ N := le_of_max_le_left hN
  have hNthr : 2 * Nthr ≤ N := le_of_max_le_right hN
  by_contra hcon
  have hbN : bad N := not_le.mp hcon
  obtain ⟨-, hsN2, hsN3, -⟩ := hsize N hN1N
  have hN'big : Nthr ≤ gllN' d N := by omega
  have hF1 : F + 1 ≤ gllN' d N := le_trans (le_max_left _ _) hN'big
  have hN2' : N2 ≤ gllN' d N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN'big
  have hNa2 : Na + 2 ≤ gllN' d N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN'big
  have h : ∃ N₀, bad N₀ ∧ gllN' d N₀ = gllN' d N := ⟨N, hbN, rfl⟩
  have hwN : w (gllN' d N) = z (Classical.choose h) / (gllc d (Classical.choose h) : ℂ) := by
    simp only [hw]; rw [dite_eq_left h]
  obtain ⟨hbad0, hf0⟩ := Classical.choose_spec h
  set N₀ := Classical.choose h with hN₀
  have hN1₀ : N1 ≤ N₀ := hlarge N₀ (by omega)
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hsize N₀ hN1₀
  have hNa₀ : Na ≤ N₀ := by omega
  obtain ⟨hKN, h6N, h4N⟩ := hNa N₀ hNa₀
  -- the transfer at `N₀`
  have hMη : 0 < msize d N₀ * (z N₀).im := by
    have : 0 < msize d N₀ := by unfold msize; exact_mod_cast ouMatrixSize_pos d N₀
    exact mul_pos this (him_pos N₀)
  have hWle : ((dL3.W (gllN' d N₀) : ℕ) : ℝ) ≤ (N₀ : ℝ) := by
    have := gll_W' d N₀
    have hMpos := ouMatrixSize_pos d N₀
    exact_mod_cast (show dL3.W (gllN' d N₀) ≤ N₀ by omega)
  have hA := gll_absorb (K := K) hτ' hMη (Nat.cast_nonneg _)
    (by exact_mod_cast (show 0 < N₀ by omega)) hWle hKN h6N
  have htr := gll_transfer d N₀ hκ (him_pos N₀) (him_le_one N₀) (habs_re N₀)
    (A := (N₀ : ℝ) ^ τ' * (msize d N₀ * (z N₀).im)⁻¹) (τb := τ' / 2) hA
  have hBN := hN2 (gllN' d N) hN2'
  rw [hwN, ← hf0] at hBN
  have hprob : ENNReal.ofReal (((gllN' d N₀ : ℕ) : ℝ) ^ (-(2 * D))) ≤
      ENNReal.ofReal ((N₀ : ℝ) ^ (-D)) :=
    ENNReal.ofReal_le_ofReal (gll_prob hD (by exact_mod_cast h4N)
      (by exact_mod_cast (show N₀ ≤ 2 * gllN' d N₀ by omega)))
  exact absurd hbad0 (not_lt.mpr (htr.trans (hBN.trans hprob)))

end RBM.Gauss
