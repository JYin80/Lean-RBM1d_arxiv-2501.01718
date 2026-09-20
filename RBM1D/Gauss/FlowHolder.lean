/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma41Glue

/-!
# The Hölder modulus of the flow in the time variable — T106

`RBM.Lemma41Flow` quantifies over `u ∈ [s_N, t_N]` **inside** the index set of `≺`, while
`RBM.Gauss.stochDom_indicator_llMax_sq` (T102) is a statement at one fixed `u`.  The bridge
`RBM.stochDom_timeIcc_of_holder` (and its high-probability variant of T101) needs a Hölder
modulus in `u`.  This file supplies the deterministic half of it.

Everything here is an identity or an operator-norm estimate; no probability is used, and in
particular **`‖X‖ ≺ 1` (T100) is not needed** — it only enters when the constant produced here
is fed to the time-net bridge.

## The estimate

Both the matrix and the spectral parameter move with `u`:

`G_u - G_{u'} = G_u\,\bigl((H_{u'} - z_{u'}) - (H_u - z_u)\bigr)\,G_{u'}`,

so with `‖G_u‖ ≤ η_u^{-1}`, `‖H_u - H_{u'}‖ = |√u - √u'|\,‖X‖` and
`|z_u - z_{u'}| = |η_u - η_{u'}|`,

`‖G_u - G_{u'}‖ ≤ η_u^{-1}η_{u'}^{-1}\bigl(|√u-√u'|\,‖X‖ + |η_u - η_{u'}|\bigr)`.

## Main statements

* `RBM.green_sub_eq`       : the resolvent identity for two different matrices *and* parameters
* `RBM.norm_green_sub_le`  : the operator-norm form
-/

namespace RBM

open MeasureTheory Matrix

open scoped Matrix.Norms.L2Operator

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The resolvent identity**, with both the matrix and the spectral parameter moving:
`A⁻¹ - B⁻¹ = A⁻¹ (B - A) B⁻¹`. -/
theorem green_sub_eq {H H' : Matrix n n ℂ} {z z' : ℂ}
    (hA : IsUnit (H - z • (1 : Matrix n n ℂ)).det)
    (hB : IsUnit (H' - z' • (1 : Matrix n n ℂ)).det) :
    green H z - green H' z'
      = green H z * ((H' - z' • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ)))
          * green H' z' := by
  have hAinv : (H - z • (1 : Matrix n n ℂ))⁻¹ * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ hA
  have hBinv : (H' - z' • (1 : Matrix n n ℂ)) * (H' - z' • (1 : Matrix n n ℂ))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hB
  show (H - z • (1 : Matrix n n ℂ))⁻¹ - (H' - z' • (1 : Matrix n n ℂ))⁻¹ = _
  show _ = (H - z • (1 : Matrix n n ℂ))⁻¹ *
    ((H' - z' • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ))) *
    (H' - z' • (1 : Matrix n n ℂ))⁻¹
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hBinv, hAinv, Matrix.mul_one,
    Matrix.one_mul]

variable [Nonempty n]

/-- **The operator-norm form of the resolvent identity.**  For Hermitian `H`, `H'` and spectral
parameters off the real axis,
`‖G_u - G_{u'}‖ ≤ ‖G_u‖ (‖H - H'‖ + |z - z'|) ‖G_{u'}‖`. -/
theorem norm_green_sub_le {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    ‖green H z - green H' z'‖
      ≤ ‖green H z‖ * (‖H - H'‖ + ‖z - z'‖) * ‖green H' z'‖ := by
  have hA : IsUnit (H - z • (1 : Matrix n n ℂ)).det := isUnit_det_sub_smul_one hH hz
  have hB : IsUnit (H' - z' • (1 : Matrix n n ℂ)).det := isUnit_det_sub_smul_one hH' hz'
  rw [green_sub_eq hA hB]
  refine (norm_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    (norm_nonneg _)
  have hsub : (H' - z' • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ))
      = -(H - H') + (z - z') • (1 : Matrix n n ℂ) := by
    rw [sub_smul]
    abel
  rw [hsub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_smul, norm_one, mul_one]

end Resolvent

/-! ### Two elementary estimates -/

/-- `|√x - √y| ≤ √|x - y|`. -/
theorem abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  rcases le_total y x with h | h
  · have hs : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h)]
    have key : (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x - y := by
      have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
      have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
      have hxy : Real.sqrt y * Real.sqrt y ≤ Real.sqrt x * Real.sqrt y :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg y)
      nlinarith [hxx, hyy, hxy]
    have h2 := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (sub_nonneg.2 hs)] at h2
  · have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt h
    rw [abs_sub_comm, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h)]
    have key : (Real.sqrt y - Real.sqrt x) ^ 2 ≤ y - x := by
      have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
      have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
      have hxy : Real.sqrt x * Real.sqrt x ≤ Real.sqrt y * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
      nlinarith [hxx, hyy, hxy]
    have h2 := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (sub_nonneg.2 hs)] at h2

/-- `‖z_u - z_{u'}‖ = |u - u'|`, because `z_t = E + (1-t)m(E)` and `‖m(E)‖ = 1`. -/
theorem norm_zt_sub {E : ℝ} (hE : |E| ≤ 2) (u u' : ℝ) :
    ‖zt E u - zt E u'‖ = |u - u'| := by
  have hsub : zt E u - zt E u' = ((u' - u : ℝ) : ℂ) * mE E := by
    simp only [zt]
    push_cast
    ring
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mE hE, mul_one,
    abs_sub_comm]

end RBM

namespace RBM.Gauss

open MeasureTheory Matrix

open scoped Matrix.Norms.L2Operator

/-! ### The Hölder estimate for the Gaussian flow -/

/-- **The resolvent of the flow moves by at most `η^{-2}(‖X‖+1)|u-u'|^{1/2}`.**  Both the
matrix and the spectral parameter contribute: `‖H_u - H_{u'}‖ = |√u-√u'|‖X‖` and
`‖z_u - z_{u'}‖ = |u-u'|`. -/
theorem norm_green_flow_sub_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {u u' : ℝ}
    (hu1 : u < 1) (hu'1 : u' < 1) (ω : Ω d) :
    ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u')‖
      ≤ (etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|)
          * (etaT E u')⁻¹ := by
  have hη : 0 < etaT E u := by
    show 0 < (1 - u) * (mE E).im
    exact mul_pos (by linarith) (mE_im_pos hE)
  have hη' : 0 < etaT E u' := by
    show 0 < (1 - u') * (mE E).im
    exact mul_pos (by linarith) (mE_im_pos hE)
  have hzim : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact ne_of_gt hη
  have hzim' : (zt E u').im ≠ 0 := by rw [← etaT_eq_zt_im]; exact ne_of_gt hη'
  have hG : ‖green (Hflow d N u ω) (zt E u)‖ ≤ (etaT E u)⁻¹ :=
    norm_green_le (Hflow_isHermitian d N u ω) hη
      (by rw [← etaT_eq_zt_im, abs_of_pos hη])
  have hG' : ‖green (Hflow d N u' ω) (zt E u')‖ ≤ (etaT E u')⁻¹ :=
    norm_green_le (Hflow_isHermitian d N u' ω) hη'
      (by rw [← etaT_eq_zt_im, abs_of_pos hη'])
  refine (norm_green_sub_le (Hflow_isHermitian d N u ω) (Hflow_isHermitian d N u' ω)
    hzim hzim').trans ?_
  rw [norm_Hflow_sub, norm_zt_sub hE.le]
  have hmid : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'| := by
    have : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
    positivity
  gcongr

/-! ### Transfer to `llErr`, `llMax` and its square -/

/-- Each entry of `G_u - m` moves by at most `‖G_u - G_{u'}‖`. -/
theorem abs_llErr_sub_le (d : Dims) (N : ℕ) (E u u' : ℝ) (ω : Ω d)
    (ij : (band d).Idx N × (band d).Idx N) :
    |(sample d).llErr E N u ω ij - (sample d).llErr E N u' ω ij|
      ≤ ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u')‖ := by
  have hGG : (sample d).G E N u ω - (sample d).G E N u' ω
      = green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u') := rfl
  have hentry : ((sample d).G E N u ω
        - mE E • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2
      - ((sample d).G E N u' ω
        - mE E • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2
      = ((sample d).G E N u ω - (sample d).G E N u' ω) ij.1 ij.2 := by
    simp only [Matrix.sub_apply]
    ring
  rw [← hGG]
  calc |(sample d).llErr E N u ω ij - (sample d).llErr E N u' ω ij|
      ≤ ‖((sample d).G E N u ω
            - mE E • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2
          - ((sample d).G E N u' ω
            - mE E • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖((sample d).G E N u ω - (sample d).G E N u' ω) ij.1 ij.2‖ := by rw [hentry]
    _ ≤ ‖(sample d).G E N u ω - (sample d).G E N u' ω‖ := norm_apply_le_l2_opNorm _ _ _

/-- `‖G_u - m‖_max` is Lipschitz in the resolvent. -/
theorem abs_llMax_sub_le (d : Dims) (N : ℕ) (E u u' : ℝ) (ω : Ω d) :
    |Step1.llMax (sample d) E N u ω - Step1.llMax (sample d) E N u' ω|
      ≤ ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u')‖ := by
  set C : ℝ := ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u')‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have h1 : Step1.llMax (sample d) E N u ω ≤ Step1.llMax (sample d) E N u' ω + C := by
    refine Step1.llMax_le _ fun ij => ?_
    have h := abs_llErr_sub_le d N E u u' ω ij
    have h2 := Step1.llErr_le_llMax (E := E) (sample d) N u' ω ij
    have h3 := (abs_le.1 h).2
    linarith
  have h2 : Step1.llMax (sample d) E N u' ω ≤ Step1.llMax (sample d) E N u ω + C := by
    refine Step1.llMax_le _ fun ij => ?_
    have h := abs_llErr_sub_le d N E u u' ω ij
    have h2 := Step1.llErr_le_llMax (E := E) (sample d) N u ω ij
    have h3 := (abs_le.1 h).1
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- `‖G_u - m‖_max ≤ η_u^{-1} + 1`. -/
theorem llMax_le_inv_etaT (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu1 : u < 1)
    (ω : Ω d) : Step1.llMax (sample d) E N u ω ≤ (etaT E u)⁻¹ + 1 := by
  have hη : 0 < etaT E u := by
    show 0 < (1 - u) * (mE E).im
    exact mul_pos (by linarith) (mE_im_pos hE)
  have hG : ‖green (Hflow d N u ω) (zt E u)‖ ≤ (etaT E u)⁻¹ :=
    norm_green_le (Hflow_isHermitian d N u ω) hη (by rw [← etaT_eq_zt_im, abs_of_pos hη])
  refine Step1.llMax_le _ fun ij => ?_
  rw [(sample d).llErr_eq N u ω ij]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(sample d).G E N u ω ij.1 ij.2‖ ≤ (etaT E u)⁻¹ :=
    (norm_apply_le_l2_opNorm _ _ _).trans hG
  have h2 : ‖(if ij.1 = ij.2 then mE E else 0)‖ ≤ 1 := by
    split_ifs
    · exact le_of_eq (norm_mE hE.le)
    · simp
  exact add_le_add h1 h2

/-- **The Hölder estimate for `‖G_u - m‖²_max`.** -/
theorem abs_llMax_sq_sub_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {u u' : ℝ}
    (hu1 : u < 1) (hu'1 : u' < 1) (ω : Ω d) :
    |Step1.llMax (sample d) E N u ω ^ 2 - Step1.llMax (sample d) E N u' ω ^ 2|
      ≤ ((etaT E u)⁻¹ + (etaT E u')⁻¹ + 2) *
        ((etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|)
          * (etaT E u')⁻¹) := by
  set a : ℝ := Step1.llMax (sample d) E N u ω with ha
  set b : ℝ := Step1.llMax (sample d) E N u' ω with hb
  have ha0 : 0 ≤ a := Step1.llMax_nonneg _ N u ω
  have hb0 : 0 ≤ b := Step1.llMax_nonneg _ N u' ω
  have haU : a ≤ (etaT E u)⁻¹ + 1 := llMax_le_inv_etaT d N hE hu1 ω
  have hbU : b ≤ (etaT E u')⁻¹ + 1 := llMax_le_inv_etaT d N hE hu'1 ω
  have hdiff : |a - b|
      ≤ (etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|)
          * (etaT E u')⁻¹ :=
    (abs_llMax_sub_le d N E u u' ω).trans (norm_green_flow_sub_le d N hE hu1 hu'1 ω)
  have hD0 : (0 : ℝ) ≤ (etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|)
      * (etaT E u')⁻¹ := le_trans (abs_nonneg _) hdiff
  have hsq : |a ^ 2 - b ^ 2| = (a + b) * |a - b| := by
    rw [show a ^ 2 - b ^ 2 = (a + b) * (a - b) from by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + b)]
  have hηu : 0 < etaT E u := by
    show 0 < (1 - u) * (mE E).im
    exact mul_pos (by linarith) (mE_im_pos hE)
  have hηu' : 0 < etaT E u' := by
    show 0 < (1 - u') * (mE E).im
    exact mul_pos (by linarith) (mE_im_pos hE)
  rw [hsq]
  refine mul_le_mul ?_ hdiff (abs_nonneg _) (by positivity)
  linarith

end RBM.Gauss
