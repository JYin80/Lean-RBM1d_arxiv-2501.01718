/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.StieltjesEtaMonotone
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Poisson smoothing of test functions (Theorem 2.6, Step 2)

The Poisson (Cauchy) kernel `poissonKernel ε x = ε/(π(x²+ε²))` smooths a compactly supported
smooth test function `O : (Fin k → ℝ) → ℝ` at scale `ε`. This file proves the smoothing-error
bound and the two exact identities connecting the smoothed sums of eigenvalue tuples to
Stieltjes transforms (and the level-set analogue used in the exponent bookkeeping).
-/

namespace RBM

open MeasureTheory Real Set

/-- The (paper-sign) Poisson/Cauchy kernel `θ_ε(x) = ε/(π(x²+ε²))`. -/
noncomputable def poissonKernel (ε x : ℝ) : ℝ := ε / (Real.pi * (x ^ 2 + ε ^ 2))

/-- The Poisson smoothing of `O` at scale `ε`, `O * P_ε`. -/
noncomputable def poissonSmooth {k : ℕ} (ε : ℝ) (O : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  ∫ y, O y * ∏ j, poissonKernel ε (x j - y j)

private lemma poissonKernel_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 < poissonKernel ε x := by
  unfold poissonKernel; positivity

private lemma poissonKernel_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (poissonKernel ε) := by
  unfold poissonKernel
  apply Continuous.div continuous_const (by fun_prop)
  intro x
  have := poissonKernel_pos hε x
  unfold poissonKernel at this
  positivity

/-- `poissonKernel ε` shifted at `c` is Mathlib's Cauchy pdf at location `c`, scale `ε`. -/
private lemma poissonKernel_eq_cauchyPDFReal {ε : ℝ} (hε : 0 < ε) (c y : ℝ) :
    poissonKernel ε (c - y) = ProbabilityTheory.cauchyPDFReal c (Real.toNNReal ε) y := by
  have hcoe : ((Real.toNNReal ε : NNReal) : ℝ) = ε := Real.coe_toNNReal ε hε.le
  unfold poissonKernel ProbabilityTheory.cauchyPDFReal
  rw [hcoe]
  have h1 : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 : (c - y) ^ 2 + ε ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma poissonKernel_integrable {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (fun y => poissonKernel ε (c - y)) := by
  simpa [poissonKernel_eq_cauchyPDFReal hε c] using
    ProbabilityTheory.integrable_cauchyPDFReal c (γ := Real.toNNReal ε)

private lemma poissonKernel_integral_eq_one {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∫ y, poissonKernel ε (c - y) = 1 := by
  have hγ : Real.toNNReal ε ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero]
    linarith
  simpa [poissonKernel_eq_cauchyPDFReal hε c] using
    ProbabilityTheory.integral_cauchyPDFReal_eq_one c hγ

/-- Exact near-field mass of the kernel within radius `d` of its center. -/
private lemma poissonKernel_near_integral {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (c : ℝ) :
    ∫ y in Set.Ioc (c - d) (c + d), poissonKernel ε (c - y) =
      (2 / Real.pi) * Real.arctan (d / ε) := by
  rw [← intervalIntegral.integral_of_le (by linarith : c - d ≤ c + d)]
  rw [intervalIntegral.integral_comp_sub_left (poissonKernel ε) c]
  have hshift1 : c - (c + d) = -d := by ring
  have hshift2 : c - (c - d) = d := by ring
  rw [hshift1, hshift2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [show (poissonKernel ε) = (fun x => Real.pi⁻¹ * (ε / (ε ^ 2 + x ^ 2))) from by
    funext x; unfold poissonKernel; field_simp; ring]
  rw [intervalIntegral.integral_const_mul, integral_div_sq_add_sq]
  rw [show -d / ε = -(d / ε) from by ring, Real.arctan_neg]
  ring

/-- Tail-mass bound for the kernel at radius `d` from its center, `Icc` version. -/
private lemma poissonKernel_tail_Icc_le {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (c : ℝ) :
    ∫ y in (Set.Icc (c - d) (c + d))ᶜ, poissonKernel ε (c - y) ≤ (2 / Real.pi) * (ε / d) := by
  have htotal := poissonKernel_integral_eq_one hε c
  have hnear : ∫ y in Set.Icc (c - d) (c + d), poissonKernel ε (c - y) =
      (2 / Real.pi) * Real.arctan (d / ε) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]; exact poissonKernel_near_integral hε hd c
  have hsplit := MeasureTheory.integral_add_compl (μ := volume)
    (measurableSet_Icc (a := c - d) (b := c + d)) (poissonKernel_integrable hε c)
  rw [htotal, hnear] at hsplit
  have htail_eq : ∫ y in (Set.Icc (c - d) (c + d))ᶜ, poissonKernel ε (c - y) =
      1 - (2 / Real.pi) * Real.arctan (d / ε) := by linarith
  rw [htail_eq]
  have harctan : Real.arctan (d / ε) = Real.pi / 2 - Real.arctan (ε / d) := by
    have h := Real.arctan_inv_of_pos (show (0:ℝ) < d / ε by positivity)
    rw [inv_div] at h
    linarith
  rw [harctan]
  have hb : Real.arctan (ε / d) ≤ ε / d := Real.arctan_le_self (by positivity)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hrw : (1:ℝ) - (2 / Real.pi) * (Real.pi / 2 - Real.arctan (ε / d)) =
      (2 / Real.pi) * Real.arctan (ε / d) := by field_simp; ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Pointwise kernel bound away from the singularity. -/
private lemma poissonKernel_le_of_ne {ε u : ℝ} (hε : 0 < ε) (hu : u ≠ 0) :
    poissonKernel ε u ≤ ε / (Real.pi * u ^ 2) := by
  unfold poissonKernel
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  apply div_le_div_of_nonneg_left hε.le (mul_pos Real.pi_pos hu2)
  nlinarith [sq_nonneg ε, Real.pi_pos]

/-- Mass of the kernel over the fixed bounded region `[-R,R]`, for `t` **far** from it
(`|t| > 2R`): sharp `O(ε(1+t²)⁻¹)` bound, via the pointwise kernel estimate (no need for
`ε ≤ 1`). -/
private lemma poissonKernel_mass_Icc_far_le {ε R t : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ht : 2 * R < |t|) :
    ∫ y in Set.Icc (-R) R, poissonKernel ε (t - y) ≤
      (8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi) * ε * (1 + t ^ 2)⁻¹ := by
  have htpos : (0:ℝ) < |t| := by linarith
  have ht0 : t ≠ 0 := abs_pos.mp htpos
  have ht2pos : (0:ℝ) < t ^ 2 := by positivity
  have ht2 : 4 * R ^ 2 < t ^ 2 := by
    have h := mul_lt_mul'' ht ht (by positivity) (by positivity)
    rw [← sq_abs t]; nlinarith
  have hfar : ∀ y ∈ Set.Icc (-R) R, poissonKernel ε (t - y) ≤ 4 * ε / (Real.pi * t ^ 2) := by
    intro y hy
    have h2 : |y| ≤ R := abs_le.2 hy
    have hty : |t| / 2 ≤ |t - y| := by
      have h1 : |t| - |y| ≤ |t - y| := by linarith [abs_sub_abs_le_abs_sub t y]
      linarith
    have hne : t - y ≠ 0 := by
      intro h; rw [h, abs_zero] at hty; linarith
    have hsq : t ^ 2 / 4 ≤ (t - y) ^ 2 := by
      have h1 : (|t| / 2) ^ 2 ≤ |t - y| ^ 2 := pow_le_pow_left₀ (by positivity) hty 2
      calc t ^ 2 / 4 = (|t| / 2) ^ 2 := by rw [div_pow, sq_abs]; norm_num
        _ ≤ |t - y| ^ 2 := h1
        _ = (t - y) ^ 2 := sq_abs _
    calc poissonKernel ε (t - y) ≤ ε / (Real.pi * (t - y) ^ 2) := poissonKernel_le_of_ne hε hne
      _ ≤ ε / (Real.pi * (t ^ 2 / 4)) := by
          apply div_le_div_of_nonneg_left hε.le (mul_pos Real.pi_pos (by positivity))
          nlinarith [Real.pi_pos]
      _ = 4 * ε / (Real.pi * t ^ 2) := by ring
  have hIntKernel : IntegrableOn (fun y => poissonKernel ε (t - y)) (Set.Icc (-R) R) :=
    ((poissonKernel_continuous hε).comp (continuous_const.sub continuous_id)).integrableOn_Icc
  have hIntConst : IntegrableOn (fun _ : ℝ => 4 * ε / (Real.pi * t ^ 2)) (Set.Icc (-R) R) :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have ht2' : (0:ℝ) < 1 + t ^ 2 := by positivity
  have h4R2 : (0:ℝ) < 4 * R ^ 2 := by positivity
  have hexp : 1 + t ^ 2 ≤ t ^ 2 * (1 + (4 * R ^ 2)⁻¹) := by
    have hdiv : (1:ℝ) ≤ t ^ 2 * (4 * R ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h4R2]; nlinarith
    nlinarith [hdiv]
  calc (∫ y in Set.Icc (-R) R, poissonKernel ε (t - y))
      ≤ ∫ _y in Set.Icc (-R) R, 4 * ε / (Real.pi * t ^ 2) :=
        MeasureTheory.setIntegral_mono_on hIntKernel hIntConst measurableSet_Icc hfar
    _ = (volume.real (Set.Icc (-R) R)) * (4 * ε / (Real.pi * t ^ 2)) := by
        rw [MeasureTheory.setIntegral_const]; rfl
    _ = (2 * R) * (4 * ε / (Real.pi * t ^ 2)) := by
        rw [Measure.real, Real.volume_Icc, show R - -R = 2 * R from by ring,
          ENNReal.toReal_ofReal (by positivity)]
    _ = (8 * R * ε) / (Real.pi * t ^ 2) := by ring
    _ ≤ (8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi) * ε * (1 + t ^ 2)⁻¹ := by
        have heq : (8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi) * ε * (1 + t ^ 2)⁻¹ =
            (8 * R * ε * (1 + (4 * R ^ 2)⁻¹)) / (Real.pi * (1 + t ^ 2)) := by
          field_simp
        rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
        have hh := mul_le_mul_of_nonneg_left hexp
          (show (0:ℝ) ≤ 8 * R * ε * Real.pi by positivity)
        nlinarith [hh]

/-- Mass of the kernel over the fixed bounded region `[-R,R]`, uniformly bounded (given `ε ≤ 1`)
by `D(R)·(1+t²)⁻¹`: `O(1)` near `t = 0` and pointwise `O(ε/t²) = O((1+t²)⁻¹)` far away. -/
private lemma poissonKernel_mass_Icc_le {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (t : ℝ) :
    ∫ y in Set.Icc (-R) R, poissonKernel ε (t - y) ≤
      (1 + 4 * R ^ 2 + 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi) * (1 + t ^ 2)⁻¹ := by
  have hDfar : (0:ℝ) ≤ 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi := by positivity
  by_cases ht : |t| ≤ 2 * R
  · have hmono : (∫ y in Set.Icc (-R) R, poissonKernel ε (t - y)) ≤ 1 := by
      have hnonneg : (0:ℝ) ≤ ∫ y in (Set.Icc (-R) R)ᶜ, poissonKernel ε (t - y) :=
        MeasureTheory.integral_nonneg (fun y => (poissonKernel_pos hε _).le)
      have hsplit := MeasureTheory.integral_add_compl (μ := volume)
        (measurableSet_Icc (a := -R) (b := R)) (poissonKernel_integrable hε t)
      rw [poissonKernel_integral_eq_one hε t] at hsplit
      linarith
    have ht2 : t ^ 2 ≤ 4 * R ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
      rw [sq_abs] at h
      nlinarith
    have hbound : (1:ℝ) ≤ (1 + 4 * R ^ 2) * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0:ℝ) < 1 + t ^ 2)]
      nlinarith
    calc (∫ y in Set.Icc (-R) R, poissonKernel ε (t - y)) ≤ 1 := hmono
      _ ≤ (1 + 4 * R ^ 2) * (1 + t ^ 2)⁻¹ := hbound
      _ ≤ (1 + 4 * R ^ 2 + 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi) * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · push_neg at ht
    have htpos : (0:ℝ) < |t| := by linarith
    have ht0 : t ≠ 0 := abs_pos.mp htpos
    have ht2pos : (0:ℝ) < t ^ 2 := by positivity
    have ht2 : 4 * R ^ 2 < t ^ 2 := by
      have h := mul_lt_mul'' ht ht (by positivity) (by positivity)
      rw [← sq_abs t]
      nlinarith
    have hfar : ∀ y ∈ Set.Icc (-R) R, poissonKernel ε (t - y) ≤ 4 * ε / (Real.pi * t ^ 2) := by
      intro y hy
      have h2 : |y| ≤ R := abs_le.2 hy
      have hty : |t| / 2 ≤ |t - y| := by
        have h1 : |t| - |y| ≤ |t - y| := by linarith [abs_sub_abs_le_abs_sub t y]
        linarith
      have hne : t - y ≠ 0 := by
        intro h
        rw [h, abs_zero] at hty
        linarith
      have hsq : t ^ 2 / 4 ≤ (t - y) ^ 2 := by
        have h1 : (|t| / 2) ^ 2 ≤ |t - y| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hty 2
        calc t ^ 2 / 4 = (|t| / 2) ^ 2 := by rw [div_pow, sq_abs]; norm_num
          _ ≤ |t - y| ^ 2 := h1
          _ = (t - y) ^ 2 := sq_abs _
      calc poissonKernel ε (t - y) ≤ ε / (Real.pi * (t - y) ^ 2) := poissonKernel_le_of_ne hε hne
        _ ≤ ε / (Real.pi * (t ^ 2 / 4)) := by
            apply div_le_div_of_nonneg_left hε.le (mul_pos Real.pi_pos (by positivity))
            nlinarith [Real.pi_pos]
        _ = 4 * ε / (Real.pi * t ^ 2) := by ring
    have hIntKernel : IntegrableOn (fun y => poissonKernel ε (t - y)) (Set.Icc (-R) R) :=
      ((poissonKernel_continuous hε).comp (continuous_const.sub continuous_id)).integrableOn_Icc
    have hIntConst : IntegrableOn (fun _ : ℝ => 4 * ε / (Real.pi * t ^ 2)) (Set.Icc (-R) R) :=
      integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    calc (∫ y in Set.Icc (-R) R, poissonKernel ε (t - y))
        ≤ ∫ _y in Set.Icc (-R) R, 4 * ε / (Real.pi * t ^ 2) :=
          MeasureTheory.setIntegral_mono_on hIntKernel hIntConst measurableSet_Icc hfar
      _ = (volume.real (Set.Icc (-R) R)) * (4 * ε / (Real.pi * t ^ 2)) := by
          rw [MeasureTheory.setIntegral_const]; rfl
      _ = (2 * R) * (4 * ε / (Real.pi * t ^ 2)) := by
          rw [Measure.real, Real.volume_Icc, show R - -R = 2 * R from by ring,
            ENNReal.toReal_ofReal (by positivity)]
      _ ≤ (1 + 4 * R ^ 2 + 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi) * (1 + t ^ 2)⁻¹ := by
          have hπ : (0:ℝ) < Real.pi := Real.pi_pos
          have ht2' : (0:ℝ) < 1 + t ^ 2 := by positivity
          have h4R2 : (0:ℝ) < 4 * R ^ 2 := by positivity
          have hexp : 1 + t ^ 2 ≤ t ^ 2 * (1 + (4 * R ^ 2)⁻¹) := by
            have hdiv : (1:ℝ) ≤ t ^ 2 * (4 * R ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, le_div_iff₀ h4R2]
              nlinarith
            nlinarith [hdiv]
          have hkey : (2 * R) * (4 * ε / (Real.pi * t ^ 2)) ≤
              8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi * (1 + t ^ 2)⁻¹ := by
            have hlhs : (2 * R) * (4 * ε / (Real.pi * t ^ 2)) =
                (8 * R * ε) / (Real.pi * t ^ 2) := by ring
            have hrhs : 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi * (1 + t ^ 2)⁻¹ =
                (8 * R * (1 + (4 * R ^ 2)⁻¹)) / (Real.pi * (1 + t ^ 2)) := by
              rw [eq_div_iff (by positivity)]
              field_simp
            rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
            have hstep1 : ε * (Real.pi * (1 + t ^ 2)) ≤ 1 * (Real.pi * (1 + t ^ 2)) :=
              mul_le_mul_of_nonneg_right hε1 (by positivity)
            have hstep2 : (1:ℝ) * (Real.pi * (1 + t ^ 2)) ≤ (t ^ 2 * (1 + (4 * R ^ 2)⁻¹)) * Real.pi := by
              nlinarith [mul_le_mul_of_nonneg_left hexp hπ.le]
            nlinarith [hstep1, hstep2]
          nlinarith [hDfar, inv_nonneg.2 (show (0:ℝ) ≤ 1 + t ^ 2 by positivity)]

/-- At the constant scale `η ≡ 1/N`, the sum of products of Lorentzians is a power of `Im m`:
`∑_g ∏_b (1+λ̂_{g_b}²)⁻¹ = (Im m(E+i/N))^k`. -/
theorem sum_prod_lorentz_eq {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Hm : Matrix n n ℂ) (hH : Hm.IsHermitian) (k : ℕ) (E : ℝ) :
    ∑ g : Fin k → n, ∏ j, (1 + ((Fintype.card n : ℝ) * (hH.eigenvalues (g j) - E)) ^ 2)⁻¹ =
      (stieltjes Hm ((E : ℂ) + (((Fintype.card n : ℝ))⁻¹ : ℂ) * Complex.I)).im ^ k := by
  have hNpos : 0 < (Fintype.card n : ℝ) := by
    have := Fintype.card_pos (α := n); exact_mod_cast this
  have hNne : (Fintype.card n : ℝ) ≠ 0 := hNpos.ne'
  have hη : (0:ℝ) < (Fintype.card n : ℝ)⁻¹ := by positivity
  have hformula := stieltjes_im_eq_normalized_specWeight Hm hH E
    (Fintype.card n : ℝ)⁻¹ hη
  rw [show (((Fintype.card n : ℝ))⁻¹ : ℂ) = (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  rw [hformula]
  have hterm : ∀ l : n, (Fintype.card n : ℝ)⁻¹ /
      ((hH.eigenvalues l - E) ^ 2 + ((Fintype.card n : ℝ)⁻¹) ^ 2) =
      (Fintype.card n : ℝ) * (1 + ((Fintype.card n : ℝ) * (hH.eigenvalues l - E)) ^ 2)⁻¹ := by
    intro l
    field_simp
    ring
  rw [show (Fintype.card n : ℝ)⁻¹ * ∑ l : n, (Fintype.card n : ℝ)⁻¹ /
      ((hH.eigenvalues l - E) ^ 2 + ((Fintype.card n : ℝ)⁻¹) ^ 2) =
      ∑ l : n, (1 + ((Fintype.card n : ℝ) * (hH.eigenvalues l - E)) ^ 2)⁻¹ from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hterm l]
    field_simp]
  exact (Fintype.sum_pow
    (fun l : n => (1 + ((Fintype.card n : ℝ) * (hH.eigenvalues l - E)) ^ 2)⁻¹) k).symm

/-- The exact identity behind Step 2's Poisson smoothing:
`∑_g (O_π*P_{ε'})(λ̂_g) = ∫ O_π(y) ∏_b π⁻¹ Im m(E+y_b/N+iε'/N) dy`. -/
theorem sum_poissonSmooth_eq {n : Type*} [Fintype n] [DecidableEq n] (Hm : Matrix n n ℂ)
    (hH : Hm.IsHermitian) {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∑ g : Fin k → n, poissonSmooth ε O
        (fun j => (Fintype.card n : ℝ) * (hH.eigenvalues (g j) - E)) =
      ∫ y, O y * ∏ j, Real.pi⁻¹ *
        (stieltjes Hm (((E + y j / Fintype.card n : ℝ) : ℂ) +
          ((ε / Fintype.card n : ℝ) : ℂ) * Complex.I)).im := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp [poissonSmooth]
  · rcases isEmpty_or_nonempty n with hn | hn
    · haveI : IsEmpty (Fin k → n) := ⟨fun g => hn.false (g ⟨0, hkpos⟩)⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      have hstiel : ∀ z : ℂ, (stieltjes Hm z).im = 0 := by
        intro z; simp [stieltjes, Fintype.card_eq_zero]
      simp only [hstiel, mul_zero]
      rw [show (∏ _j : Fin k, (0:ℝ)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ (⟨0, hkpos⟩ : Fin k)) rfl]
      simp
    · have hNpos : 0 < (Fintype.card n : ℝ) := by
        have := Fintype.card_pos (α := n); exact_mod_cast this
      have hNne : (Fintype.card n : ℝ) ≠ 0 := hNpos.ne'
      have hcont : ∀ g : Fin k → n, Continuous (fun y : Fin k → ℝ =>
          O y * ∏ j, poissonKernel ε
            ((Fintype.card n : ℝ) * (hH.eigenvalues (g j) - E) - y j)) := by
        intro g
        apply hO.1.continuous.mul
        apply continuous_finsetProd
        intro j _
        exact (poissonKernel_continuous hε).comp (by fun_prop)
      have hsupp : ∀ g : Fin k → n, HasCompactSupport (fun y : Fin k → ℝ =>
          O y * ∏ j, poissonKernel ε
            ((Fintype.card n : ℝ) * (hH.eigenvalues (g j) - E) - y j)) :=
        fun g => hO.2.mul_right
      have hint : ∀ g : Fin k → n, Integrable (fun y : Fin k → ℝ =>
          O y * ∏ j, poissonKernel ε
            ((Fintype.card n : ℝ) * (hH.eigenvalues (g j) - E) - y j)) :=
        fun g => (hcont g).integrable_of_hasCompactSupport (hsupp g)
      unfold poissonSmooth
      rw [← MeasureTheory.integral_finsetSum Finset.univ (fun g _ => hint g)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [← Finset.mul_sum]
      congr 1
      have hswap : ∑ g : Fin k → n, ∏ j : Fin k, poissonKernel ε
          ((Fintype.card n : ℝ) * (hH.eigenvalues (g j) - E) - y j) =
          ∏ j : Fin k, ∑ l : n, poissonKernel ε
            ((Fintype.card n : ℝ) * (hH.eigenvalues l - E) - y j) :=
        (Fintype.prod_sum (fun j (l : n) => poissonKernel ε
          ((Fintype.card n : ℝ) * (hH.eigenvalues l - E) - y j))).symm
      rw [hswap]
      apply Finset.prod_congr rfl
      intro j _
      have hη' : (0:ℝ) < ε / (Fintype.card n : ℝ) := by positivity
      have hformula := stieltjes_im_eq_normalized_specWeight Hm hH
        (E + y j / (Fintype.card n : ℝ)) (ε / (Fintype.card n : ℝ)) hη'
      have hcast : (((E + y j / Fintype.card n : ℝ) : ℂ) +
          ((ε / Fintype.card n : ℝ) : ℂ) * Complex.I) =
          ((E + y j / (Fintype.card n : ℝ) : ℝ) : ℂ) +
            ((ε / (Fintype.card n : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, hformula, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      unfold poissonKernel
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring

private lemma poissonKernel_even (ε x : ℝ) : poissonKernel ε (-x) = poissonKernel ε x := by
  unfold poissonKernel; ring_nf

/-- The odd-symmetric near integral of `t ↦ t * θ_ε(t)` vanishes exactly. -/
private lemma poissonKernel_odd_near_integral_zero {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (c : ℝ) :
    ∫ y in Set.Icc (c - d) (c + d), (c - y) * poissonKernel ε (c - y) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : c - d ≤ c + d)]
  rw [intervalIntegral.integral_comp_sub_left (fun u => u * poissonKernel ε u) c]
  have hshift1 : c - (c + d) = -d := by ring
  have hshift2 : c - (c - d) = d := by ring
  rw [hshift1, hshift2]
  have hodd : ∀ u : ℝ, (fun u => u * poissonKernel ε u) (-u) =
      -(fun u => u * poissonKernel ε u) u := by
    intro u; simp only [poissonKernel_even]; ring
  have hneg := intervalIntegral.integral_comp_neg (a := -d) (b := d)
    (fun u => u * poissonKernel ε u)
  simp only [hodd, neg_neg] at hneg
  rw [intervalIntegral.integral_neg] at hneg
  linarith [hneg]

/-- Second-moment bound for the near-field mass of the kernel, radius `d`. -/
private lemma poissonKernel_second_moment_near_le {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (c : ℝ) :
    ∫ y in Set.Icc (c - d) (c + d), (c - y) ^ 2 * poissonKernel ε (c - y) ≤ 2 * d * ε / Real.pi := by
  have hbound : ∀ y ∈ Set.Icc (c - d) (c + d),
      (c - y) ^ 2 * poissonKernel ε (c - y) ≤ ε / Real.pi := by
    intro y _
    unfold poissonKernel
    rw [show (c - y) ^ 2 * (ε / (Real.pi * ((c - y) ^ 2 + ε ^ 2))) =
        ε / Real.pi * ((c - y) ^ 2 / ((c - y) ^ 2 + ε ^ 2)) from by field_simp]
    have hle1 : (c - y) ^ 2 / ((c - y) ^ 2 + ε ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg ε]
    calc ε / Real.pi * ((c - y) ^ 2 / ((c - y) ^ 2 + ε ^ 2)) ≤ ε / Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = ε / Real.pi := by ring
  have hIntF : IntegrableOn (fun y => (c - y) ^ 2 * poissonKernel ε (c - y))
      (Set.Icc (c - d) (c + d)) := by
    apply Continuous.integrableOn_Icc
    exact ((continuous_const.sub continuous_id).pow 2).mul
      ((poissonKernel_continuous hε).comp (continuous_const.sub continuous_id))
  have hIntConst : IntegrableOn (fun _ : ℝ => ε / Real.pi) (Set.Icc (c - d) (c + d)) :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  calc ∫ y in Set.Icc (c - d) (c + d), (c - y) ^ 2 * poissonKernel ε (c - y)
      ≤ ∫ _y in Set.Icc (c - d) (c + d), ε / Real.pi :=
        MeasureTheory.setIntegral_mono_on hIntF hIntConst measurableSet_Icc hbound
    _ = (volume.real (Set.Icc (c - d) (c + d))) * (ε / Real.pi) := by
        rw [MeasureTheory.setIntegral_const]; rfl
    _ = (2 * d) * (ε / Real.pi) := by
        rw [Measure.real, Real.volume_Icc, show (c + d) - (c - d) = 2 * d from by ring,
          ENNReal.toReal_ofReal (by positivity)]
    _ = 2 * d * ε / Real.pi := by ring

/-- The kernel mass over any measurable subset of `ℝ` is at most `1`. -/
private lemma poissonKernel_setIntegral_le_one {ε : ℝ} (hε : 0 < ε) (c : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) : ∫ y in S, poissonKernel ε (c - y) ≤ 1 := by
  have hnonneg : (0 : ℝ) ≤ ∫ y in Sᶜ, poissonKernel ε (c - y) :=
    MeasureTheory.integral_nonneg (fun y => (poissonKernel_pos hε _).le)
  have hsplit := MeasureTheory.integral_add_compl (μ := volume) hS (poissonKernel_integrable hε c)
  rw [poissonKernel_integral_eq_one hε c] at hsplit
  linarith

/-- A bounded continuous function with compact support attains a global bound. -/
private lemma exists_bound_of_hasCompactSupport {k : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : (Fin k → ℝ) → F} (hf : Continuous f) (hsupp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖f z‖ ≤ M := by
  rcases (tsupport f).eq_empty_or_nonempty with he | hne
  · refine ⟨0, le_refl 0, fun z => ?_⟩
    have hz : f z = 0 := by
      by_contra hcon
      exact absurd (subset_tsupport f (Function.mem_support.mpr hcon)) (by simp [he])
    simp [hz]
  · obtain ⟨_z0, _hz0mem, hz0max⟩ := hsupp.exists_isMaxOn hne hf.norm.continuousOn
    refine ⟨‖f _z0‖, norm_nonneg _, fun z => ?_⟩
    by_cases hzmem : z ∈ tsupport f
    · exact hz0max hzmem
    · have hz : f z = 0 := by
        by_contra hcon
        exact hzmem (subset_tsupport f (Function.mem_support.mpr hcon))
      simp [hz]

/-- A continuous linear functional on `Fin k → ℝ` is the coordinate sum against its values on the
standard basis. -/
private lemma clm_apply_eq_sum {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    L v = ∑ j, v j * L (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])

/-- Pointwise degree-1 Taylor remainder bound for a globally `C²`-bounded function on
`Fin k → ℝ`, via composition with the segment `s ↦ x - s•(x-y)` and the FTC. -/
private lemma poisson_taylor_bound {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hDiff : Differentiable ℝ O)
    (hFcont : Continuous (fderiv ℝ O)) {M2 : ℝ} (hM2nn : 0 ≤ M2)
    (hgradLip : ∀ z w : Fin k → ℝ, ‖fderiv ℝ O z - fderiv ℝ O w‖ ≤ M2 * ‖z - w‖)
    (x y : Fin k → ℝ) :
    |O x - O y - (fderiv ℝ O x) (x - y)| ≤ M2 * ‖x - y‖ ^ 2 := by
  set t : Fin k → ℝ := x - y with ht_def
  set γ : ℝ → (Fin k → ℝ) := fun s => x - s • t with hγ_def
  have hγ0 : γ 0 = x := by simp [hγ_def]
  have hγ1 : γ 1 = y := by simp [hγ_def, ht_def]
  have hγderiv : ∀ s, HasDerivAt γ (-t) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => u • t) t s := by
      simpa using (hasDerivAt_id s).smul_const t
    have h2 : HasDerivAt (fun u : ℝ => x - u • t) (0 - t) s := (hasDerivAt_const s x).sub h1
    simpa [hγ_def] using h2
  set ψ : ℝ → ℝ := fun s => (fderiv ℝ O (γ s)) t with hψ_def
  have hψcont : Continuous ψ := by
    apply Continuous.clm_apply
    · exact hFcont.comp (by fun_prop)
    · fun_prop
  have hφderiv : ∀ s, HasDerivAt (O ∘ γ) (-(ψ s)) s := by
    intro s
    have h1 := (hDiff (γ s)).hasFDerivAt.comp_hasDerivAt s (hγderiv s)
    simpa [hψ_def, map_neg] using h1
  have hFTC : ∫ s in (0 : ℝ)..1, -(ψ s) = (O ∘ γ) 1 - (O ∘ γ) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφderiv s)
      (hψcont.neg.intervalIntegrable _ _)
  have hFTC' : ∫ s in (0 : ℝ)..1, ψ s = O x - O y := by
    rw [intervalIntegral.integral_neg] at hFTC
    rw [Function.comp_apply, Function.comp_apply, hγ0, hγ1] at hFTC
    linarith [hFTC]
  have hconst : ∫ _s in (0 : ℝ)..1, ψ 0 = ψ 0 := by simp
  have hψ0 : ψ 0 = (fderiv ℝ O x) t := by simp [hψ_def, hγ0]
  have hdiff_eq : O x - O y - (fderiv ℝ O x) t = ∫ s in (0 : ℝ)..1, (ψ s - ψ 0) := by
    rw [intervalIntegral.integral_sub (hψcont.intervalIntegrable 0 1) intervalIntegrable_const,
      hFTC', hconst, hψ0]
  rw [hdiff_eq]
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖ψ s - ψ 0‖ ≤ M2 * ‖t‖ ^ 2 := by
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
      rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Set.uIoc_subset_uIcc hs
    have hsabs : |s| ≤ 1 := abs_le.2 ⟨by linarith [hs01.1], hs01.2⟩
    have hval : ψ s - ψ 0 = (fderiv ℝ O (γ s) - fderiv ℝ O x) t := by
      simp [hψ_def, ContinuousLinearMap.sub_apply, hγ0]
    rw [hval]
    calc ‖(fderiv ℝ O (γ s) - fderiv ℝ O x) t‖
        ≤ ‖fderiv ℝ O (γ s) - fderiv ℝ O x‖ * ‖t‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M2 * ‖γ s - x‖) * ‖t‖ :=
          mul_le_mul_of_nonneg_right (hgradLip (γ s) x) (norm_nonneg _)
      _ = M2 * (|s| * ‖t‖) * ‖t‖ := by
          rw [hγ_def]
          simp only [show x - s • t - x = -(s • t) from by abel, norm_neg, norm_smul,
            Real.norm_eq_abs]
      _ ≤ M2 * ‖t‖ ^ 2 := by
          have h1 : |s| * ‖t‖ ≤ ‖t‖ := by
            nlinarith [mul_le_mul_of_nonneg_right hsabs (norm_nonneg t)]
          nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hM2nn)
            (norm_nonneg t)]
  have hnormbound := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc |∫ s in (0 : ℝ)..1, (ψ s - ψ 0)| = ‖∫ s in (0 : ℝ)..1, (ψ s - ψ 0)‖ := rfl
    _ ≤ M2 * ‖t‖ ^ 2 * |1 - 0| := hnormbound
    _ = M2 * ‖t‖ ^ 2 := by norm_num

/-- Pointwise identity: a product of kernels with one factor multiplied by `h(y j)` equals
`h(y j)` times the plain kernel product. -/
private lemma pointwise_prod_update_mul_eq {k : ℕ} (ε : ℝ) (x : Fin k → ℝ) (j : Fin k)
    (h : ℝ → ℝ) (y : Fin k → ℝ) :
    (∏ l, (if l = j then h (y l) * poissonKernel ε (x j - y l) else poissonKernel ε (x l - y l))) =
      h (y j) * ∏ l, poissonKernel ε (x l - y l) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun l => (if l = j then h (y l) * poissonKernel ε (x j - y l)
      else poissonKernel ε (x l - y l))) (Finset.mem_univ j)]
  rw [if_pos rfl]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => poissonKernel ε (x l - y l))
    (Finset.mem_univ j)]
  have hrest : ∏ l ∈ Finset.univ.erase j,
      (if l = j then h (y l) * poissonKernel ε (x j - y l) else poissonKernel ε (x l - y l)) =
      ∏ l ∈ Finset.univ.erase j, poissonKernel ε (x l - y l) :=
    Finset.prod_congr rfl (fun l hl => by rw [if_neg (Finset.ne_of_mem_erase hl)])
  rw [hrest]; ring

/-- Box-indicator as product of per-coordinate indicators, over `Fin k`. -/
private lemma prod_indicator_eq_indicator_univ_pi {k : ℕ} (s : Fin k → Set ℝ) (g : Fin k → ℝ → ℝ)
    (y : Fin k → ℝ) :
    ∏ j, (s j).indicator (g j) (y j) =
      (Set.univ.pi s).indicator (fun z => ∏ j, g j (z j)) y := by
  by_cases h : ∀ j, y j ∈ s j
  · rw [Set.indicator_of_mem (Set.mem_univ_pi.mpr h)]
    exact Finset.prod_congr rfl (fun j _ => Set.indicator_of_mem (h j) _)
  · push_neg at h
    obtain ⟨j0, hj0⟩ := h
    rw [Set.indicator_of_notMem (fun hc => hj0 (Set.mem_univ_pi.mp hc j0))]
    exact Finset.prod_eq_zero (Finset.mem_univ j0) (Set.indicator_of_notMem hj0 _)

/-- Fubini for a box `Set.univ.pi s` against a product integrand, on `Fin k → ℝ`. -/
private lemma integral_indicator_univ_pi_prod_eq_prod {k : ℕ} (s : Fin k → Set ℝ)
    (hs : ∀ j, MeasurableSet (s j)) (g : Fin k → ℝ → ℝ) :
    ∫ y : Fin k → ℝ, (Set.univ.pi s).indicator (fun z => ∏ j, g j (z j)) y
      = ∏ j, ∫ t in s j, g j t := by
  simp_rw [← prod_indicator_eq_indicator_univ_pi]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (fun j t => (s j).indicator (g j) t)]
  exact Finset.prod_congr rfl (fun j _ => MeasureTheory.integral_indicator (hs j))

/-- Set-integral form of `integral_indicator_univ_pi_prod_eq_prod`. -/
private lemma setIntegral_univ_pi_prod_eq_prod {k : ℕ} (s : Fin k → Set ℝ)
    (hs : ∀ j, MeasurableSet (s j)) (g : Fin k → ℝ → ℝ) :
    ∫ y in Set.univ.pi s, ∏ j, g j (y j) = ∏ j, ∫ t in s j, g j t := by
  rw [← MeasureTheory.integral_indicator (MeasurableSet.univ_pi hs)]
  exact integral_indicator_univ_pi_prod_eq_prod s hs g

/-- The near-field linear term integrates to exactly zero on the coordinate-`j` box. -/
private lemma poissonSmooth_near_linear_zero {k : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin k → ℝ)
    (j : Fin k) :
    ∫ y in Set.univ.pi (fun l : Fin k => Set.Icc (x l - 1) (x l + 1)),
      (x j - y j) * ∏ l, poissonKernel ε (x l - y l) = 0 := by
  rw [← MeasureTheory.integral_indicator
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))]
  have heq : (fun z : Fin k → ℝ => (x j - z j) * ∏ l, poissonKernel ε (x l - z l)) =
      (fun z : Fin k → ℝ => ∏ l, (if l = j then (x j - z l) * poissonKernel ε (x j - z l)
        else poissonKernel ε (x l - z l))) := by
    funext z; exact (pointwise_prod_update_mul_eq ε x j (fun t => x j - t) z).symm
  rw [heq, integral_indicator_univ_pi_prod_eq_prod _
    (fun _ => measurableSet_Icc)
    (fun l t => if l = j then (x j - t) * poissonKernel ε (x j - t) else poissonKernel ε (x l - t))]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp only [if_pos]
  exact poissonKernel_odd_near_integral_zero hε one_pos (x j)

/-- The near-field quadratic remainder mass on the coordinate-`j` box is `O(ε)`. -/
private lemma poissonSmooth_near_quadratic_le {k : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin k → ℝ)
    (j : Fin k) :
    ∫ y in Set.univ.pi (fun l : Fin k => Set.Icc (x l - 1) (x l + 1)),
      (x j - y j) ^ 2 * ∏ l, poissonKernel ε (x l - y l) ≤ 2 * ε / Real.pi := by
  rw [← MeasureTheory.integral_indicator
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))]
  have heq : (fun z : Fin k → ℝ => (x j - z j) ^ 2 * ∏ l, poissonKernel ε (x l - z l)) =
      (fun z : Fin k → ℝ => ∏ l, (if l = j then (x j - z l) ^ 2 * poissonKernel ε (x j - z l)
        else poissonKernel ε (x l - z l))) := by
    funext z; exact (pointwise_prod_update_mul_eq ε x j (fun t => (x j - t) ^ 2) z).symm
  rw [heq, integral_indicator_univ_pi_prod_eq_prod _
    (fun _ => measurableSet_Icc)
    (fun l t => if l = j then (x j - t) ^ 2 * poissonKernel ε (x j - t)
      else poissonKernel ε (x l - t))]
  calc ∏ l, ∫ t in Set.Icc (x l - 1) (x l + 1),
        (if l = j then (x j - t) ^ 2 * poissonKernel ε (x j - t) else poissonKernel ε (x l - t))
      ≤ ∏ l : Fin k, (if l = j then 2 * ε / Real.pi else (1 : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro l _
          split_ifs
          · exact MeasureTheory.integral_nonneg
              (fun t => mul_nonneg (sq_nonneg _) (poissonKernel_pos hε _).le)
          · exact MeasureTheory.integral_nonneg (fun t => (poissonKernel_pos hε _).le)
        · intro l _
          split_ifs with hl
          · rw [hl]; simpa using poissonKernel_second_moment_near_le hε one_pos (x j)
          · exact poissonKernel_setIntegral_le_one hε (x l) measurableSet_Icc
    _ = 2 * ε / Real.pi := Fintype.prod_ite_eq' j (fun _ : Fin k => (2 * ε / Real.pi))

set_option maxHeartbeats 1000000 in
-- `Fin k → ℝ` carries both a `Pi.normedAddCommGroup`-derived and a `Pi.normedRing`-derived norm
-- instance (defeq but reached via different structure paths); the `pi_norm_le_iff_of_nonneg`
-- step below needs the slow defeq unifier to bridge them, hence the raised heartbeat limit.
/-- **Step 1**: the smoothing error at `x` is `O(ε)`, uniformly over every `x` and every
`ε ∈ (0,1]` (no decay in `x` yet; that is supplied separately by `poissonSmooth_escaping_bound`
when `x` lies outside the support box). -/
private lemma poissonSmooth_uniform_bound {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin k → ℝ,
      |O x - poissonSmooth ε O x| ≤ C * ε := by
  obtain ⟨M0, hM00, hM0⟩ := exists_bound_of_hasCompactSupport hO.1.continuous hO.2
  have hd1 := contDiff_infty_iff_fderiv.mp hO.1
  have hd2 := contDiff_infty_iff_fderiv.mp hd1.2
  have hFcont : Continuous (fderiv ℝ O) := hd1.2.continuous
  have hcont2 : Continuous (fderiv ℝ (fderiv ℝ O)) := hd2.2.continuous
  have hsupp2 : HasCompactSupport (fderiv ℝ (fderiv ℝ O)) :=
    IsCompact.of_isClosed_subset hO.2 (isClosed_tsupport _)
      ((tsupport_fderiv_subset ℝ).trans (tsupport_fderiv_subset ℝ))
  obtain ⟨M2, hM2nn, hM2⟩ := exists_bound_of_hasCompactSupport hcont2 hsupp2
  have hgradLip : ∀ z w : Fin k → ℝ, ‖fderiv ℝ O z - fderiv ℝ O w‖ ≤ M2 * ‖z - w‖ := fun z w =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun u _ => hd2.1.differentiableAt)
      (fun u _ => hM2 u) (Set.mem_univ w) (Set.mem_univ z)
  have hTaylor : ∀ x y : Fin k → ℝ, |O x - O y - (fderiv ℝ O x) (x - y)| ≤ M2 * ‖x - y‖ ^ 2 :=
    fun x y => poisson_taylor_bound hd1.1 hFcont hM2nn hgradLip x y
  refine ⟨(k : ℝ) * (2 * M2 + 4 * M0) / Real.pi, by positivity, ?_⟩
  intro ε hε hε1 x
  set A : Set (Fin k → ℝ) := Set.univ.pi (fun l : Fin k => Set.Icc (x l - 1) (x l + 1)) with hA_def
  have hAmeas : MeasurableSet A := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hAcompact : IsCompact A := by
    rw [hA_def]; exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKintegrable : Integrable (fun y : Fin k → ℝ => ∏ j, poissonKernel ε (x j - y j)) :=
    Integrable.fintype_prod (fun j => poissonKernel_integrable hε (x j))
  have hOKintegrable : Integrable (fun y : Fin k → ℝ =>
      O y * ∏ j, poissonKernel ε (x j - y j)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hO.1.continuous.mul (continuous_finsetProd Finset.univ
        (fun j _ => (poissonKernel_continuous hε).comp (by fun_prop)))
    · exact hO.2.mul_right
  have hmass1 : ∫ y : Fin k → ℝ, ∏ j, poissonKernel ε (x j - y j) = 1 := by
    rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
      (fun j t => poissonKernel ε (x j - t))]
    simp_rw [poissonKernel_integral_eq_one hε]
    simp
  have hDintegrable : Integrable (fun y : Fin k → ℝ =>
      (O x - O y) * ∏ j, poissonKernel ε (x j - y j)) := by
    have heq : (fun y : Fin k → ℝ => (O x - O y) * ∏ j, poissonKernel ε (x j - y j)) =
        (fun y => O x * ∏ j, poissonKernel ε (x j - y j)) -
          (fun y => O y * ∏ j, poissonKernel ε (x j - y j)) := by
      funext y; simp only [Pi.sub_apply]; ring
    rw [heq]; exact (hKintegrable.const_mul (O x)).sub hOKintegrable
  have hdiff : O x - poissonSmooth ε O x =
      ∫ y : Fin k → ℝ, (O x - O y) * ∏ j, poissonKernel ε (x j - y j) := by
    unfold poissonSmooth
    have hint_eq : ∫ y : Fin k → ℝ, (O x - O y) * ∏ j, poissonKernel ε (x j - y j) =
        (∫ y : Fin k → ℝ, O x * ∏ j, poissonKernel ε (x j - y j)) -
          ∫ y : Fin k → ℝ, O y * ∏ j, poissonKernel ε (x j - y j) := by
      rw [← MeasureTheory.integral_sub (hKintegrable.const_mul (O x)) hOKintegrable]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    rw [hint_eq, MeasureTheory.integral_const_mul, hmass1, mul_one]
  rw [hdiff]
  have hsplit := MeasureTheory.integral_add_compl hAmeas hDintegrable
  rw [← hsplit]
  have hKernelProdNonneg : ∀ y : Fin k → ℝ, 0 ≤ ∏ l, poissonKernel ε (x l - y l) :=
    fun y => Finset.prod_nonneg (fun l _ => (poissonKernel_pos hε _).le)
  have hpkcont : ∀ j : Fin k, Continuous fun y : Fin k → ℝ => poissonKernel ε (x j - y j) :=
    fun j => (poissonKernel_continuous hε).comp (by fun_prop)
  have hKcont : Continuous fun y : Fin k → ℝ => ∏ l, poissonKernel ε (x l - y l) :=
    continuous_finsetProd Finset.univ (fun j _ => hpkcont j)
  rw [show (k : ℝ) * (2 * M2 + 4 * M0) / Real.pi * ε =
      M2 * (k : ℝ) * (2 * ε / Real.pi) + 4 * M0 * (k : ℝ) / Real.pi * ε from by ring]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- near bound: |∫_A (O x - O y) K| ≤ M2 * k * (2ε/π)
    have hcont_lin : Continuous (fun y : Fin k → ℝ =>
        (fderiv ℝ O x) (x - y) * ∏ l, poissonKernel ε (x l - y l)) :=
      ((fderiv ℝ O x).continuous.comp (continuous_const.sub continuous_id)).mul hKcont
    have hcont_rem : Continuous (fun y : Fin k → ℝ =>
        (O x - O y - (fderiv ℝ O x) (x - y)) * ∏ l, poissonKernel ε (x l - y l)) :=
      ((continuous_const.sub hO.1.continuous).sub
        ((fderiv ℝ O x).continuous.comp (continuous_const.sub continuous_id))).mul hKcont
    have hsplit2 : ∫ y in A, (O x - O y) * ∏ l, poissonKernel ε (x l - y l) =
        (∫ y in A, (fderiv ℝ O x) (x - y) * ∏ l, poissonKernel ε (x l - y l)) +
          ∫ y in A, (O x - O y - (fderiv ℝ O x) (x - y)) * ∏ l, poissonKernel ε (x l - y l) := by
      rw [← MeasureTheory.integral_add (hcont_lin.continuousOn.integrableOn_compact hAcompact)
        (hcont_rem.continuousOn.integrableOn_compact hAcompact)]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
    have hlin_zero : ∫ y in A, (fderiv ℝ O x) (x - y) * ∏ l, poissonKernel ε (x l - y l) = 0 := by
      have hpteq : (fun y : Fin k → ℝ =>
          (fderiv ℝ O x) (x - y) * ∏ l, poissonKernel ε (x l - y l)) =
          (fun y => ∑ j, (fderiv ℝ O x) (Pi.single j 1) *
            ((x j - y j) * ∏ l, poissonKernel ε (x l - y l))) := by
        funext y
        rw [clm_apply_eq_sum (fderiv ℝ O x) (x - y), Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by simp only [Pi.sub_apply]; ring)
      have hcont_j : ∀ j : Fin k, Continuous
          (fun y : Fin k → ℝ => (x j - y j) * ∏ l, poissonKernel ε (x l - y l)) :=
        fun j => (continuous_const.sub (continuous_apply j)).mul hKcont
      rw [hpteq]
      rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ =>
        ((hcont_j j).continuousOn.integrableOn_compact hAcompact).const_mul _)]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [MeasureTheory.integral_const_mul, poissonSmooth_near_linear_zero hε x j, mul_zero]
    have hRembound : |∫ y in A, (O x - O y - (fderiv ℝ O x) (x - y)) *
        ∏ l, poissonKernel ε (x l - y l)| ≤ M2 * (k : ℝ) * (2 * ε / Real.pi) := by
      have hquadint : ∀ j : Fin k, Integrable
          (fun y : Fin k → ℝ => (x j - y j) ^ 2 * ∏ l, poissonKernel ε (x l - y l))
          (volume.restrict A) :=
        fun j => (((continuous_const.sub (continuous_apply j)).pow 2).mul hKcont)
          |>.continuousOn.integrableOn_compact hAcompact
      have hmajorant : Integrable (fun y : Fin k → ℝ =>
          M2 * ∑ l, (x l - y l) ^ 2 * ∏ m, poissonKernel ε (x m - y m)) (volume.restrict A) :=
        (MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hquadint j)).const_mul _
      have hptbound : ∀ᵐ y ∂(volume.restrict A), ‖(O x - O y - (fderiv ℝ O x) (x - y)) *
          ∏ l, poissonKernel ε (x l - y l)‖ ≤
          M2 * ∑ l, (x l - y l) ^ 2 * ∏ m, poissonKernel ε (x m - y m) := by
        refine MeasureTheory.ae_restrict_of_forall_mem hAmeas (fun y _ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKernelProdNonneg y)]
        have h1 := hTaylor x y
        have h2 : ‖x - y‖ ^ 2 ≤ ∑ l, (x l - y l) ^ 2 := by
          have hSnn : (0 : ℝ) ≤ ∑ l, (x l - y l) ^ 2 := Finset.sum_nonneg (fun l _ => sq_nonneg _)
          have hle : ‖x - y‖ ≤ Real.sqrt (∑ l, (x l - y l) ^ 2) :=
            (pi_norm_le_iff_of_nonneg (x := x - y) (r := Real.sqrt (∑ l, (x l - y l) ^ 2))
              (Real.sqrt_nonneg _)).mpr (fun l => by
              rw [Pi.sub_apply, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
              exact Real.sqrt_le_sqrt
                (Finset.single_le_sum (f := fun l => (x l - y l) ^ 2)
                  (fun i _ => sq_nonneg _) (Finset.mem_univ l)))
          calc ‖x - y‖ ^ 2 ≤ (Real.sqrt (∑ l, (x l - y l) ^ 2)) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) hle 2
            _ = ∑ l, (x l - y l) ^ 2 := Real.sq_sqrt hSnn
        calc |O x - O y - (fderiv ℝ O x) (x - y)| * ∏ l, poissonKernel ε (x l - y l)
            ≤ M2 * ‖x - y‖ ^ 2 * ∏ l, poissonKernel ε (x l - y l) :=
              mul_le_mul_of_nonneg_right h1 (hKernelProdNonneg y)
          _ ≤ M2 * (∑ l, (x l - y l) ^ 2) * ∏ l, poissonKernel ε (x l - y l) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h2 hM2nn) (hKernelProdNonneg y)
          _ = M2 * ∑ l, (x l - y l) ^ 2 * ∏ m, poissonKernel ε (x m - y m) := by
              rw [mul_assoc, Finset.sum_mul]
      have hstep := MeasureTheory.norm_integral_le_of_norm_le hmajorant hptbound
      refine hstep.trans (le_of_eq_of_le (by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hquadint j)]) ?_)
      calc M2 * ∑ j, ∫ y in A, (x j - y j) ^ 2 * ∏ l, poissonKernel ε (x l - y l)
          ≤ M2 * ∑ _j : Fin k, (2 * ε / Real.pi) := by
            apply mul_le_mul_of_nonneg_left _ hM2nn
            exact Finset.sum_le_sum (fun j _ => poissonSmooth_near_quadratic_le hε x j)
        _ = M2 * (k : ℝ) * (2 * ε / Real.pi) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            push_cast; ring
    calc |∫ y in A, (O x - O y) * ∏ l, poissonKernel ε (x l - y l)|
        = |(∫ y in A, (fderiv ℝ O x) (x - y) * ∏ l, poissonKernel ε (x l - y l)) +
            ∫ y in A, (O x - O y - (fderiv ℝ O x) (x - y)) *
              ∏ l, poissonKernel ε (x l - y l)| := by rw [hsplit2]
      _ = |∫ y in A, (O x - O y - (fderiv ℝ O x) (x - y)) *
            ∏ l, poissonKernel ε (x l - y l)| := by rw [hlin_zero, zero_add]
      _ ≤ M2 * (k : ℝ) * (2 * ε / Real.pi) := hRembound
  · -- far bound: |∫_{Aᶜ} (O x - O y) K| ≤ 4 * M0 * k / π * ε
    have hnormle : ∀ y : Fin k → ℝ, ‖(O x - O y) * ∏ l, poissonKernel ε (x l - y l)‖ ≤
        (2 * M0) * ∏ l, poissonKernel ε (x l - y l) := by
      intro y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKernelProdNonneg y)]
      refine mul_le_mul_of_nonneg_right ?_ (hKernelProdNonneg y)
      calc |O x - O y| ≤ |O x| + |O y| := abs_sub _ _
        _ ≤ M0 + M0 := add_le_add (hM0 x) (hM0 y)
        _ = 2 * M0 := by ring
    have hcov : ∀ y : Fin k → ℝ, y ∈ Aᶜ → ∃ j : Fin k,
        y ∈ Set.univ.pi (fun l : Fin k =>
          if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ)) := by
      intro y hy
      rw [Set.mem_compl_iff, hA_def, Set.mem_univ_pi] at hy
      push_neg at hy
      obtain ⟨j, hj⟩ := hy
      refine ⟨j, Set.mem_univ_pi.mpr (fun l => ?_)⟩
      by_cases hlj : l = j
      · subst hlj; simpa using hj
      · simp [hlj]
    have hboxmeas : ∀ j : Fin k, ∀ l : Fin k, MeasurableSet
        (if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ)) := by
      intro j l; by_cases hlj : l = j <;> simp [hlj, measurableSet_Icc.compl]
    have hCj_bound : ∀ j : Fin k, ∫ y in Set.univ.pi
        (fun l : Fin k => if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ)),
        ∏ l, poissonKernel ε (x l - y l) ≤ 2 * ε / Real.pi := by
      intro j
      rw [← MeasureTheory.integral_indicator (MeasurableSet.univ_pi (hboxmeas j)),
        integral_indicator_univ_pi_prod_eq_prod _ (hboxmeas j)
          (fun l t => poissonKernel ε (x l - t))]
      calc ∏ l, ∫ t in (if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ)),
            poissonKernel ε (x l - t)
          ≤ ∏ l : Fin k, (if l = j then 2 * ε / Real.pi else (1 : ℝ)) := by
            apply Finset.prod_le_prod₀
            · intro l _
              split_ifs
              all_goals exact MeasureTheory.integral_nonneg (fun t => (poissonKernel_pos hε _).le)
            · intro l _
              split_ifs with hl
              · rw [hl, show (2 : ℝ) * ε / Real.pi = 2 / Real.pi * (ε / 1) from by ring]
                exact poissonKernel_tail_Icc_le hε one_pos (x j)
              · rw [MeasureTheory.setIntegral_univ]
                exact (poissonKernel_integral_eq_one hε (x l)).le
        _ = 2 * ε / Real.pi := Fintype.prod_ite_eq' j (fun _ : Fin k => (2 * ε / Real.pi))
    have hKcompl_bound : ∫ y in Aᶜ, ∏ l, poissonKernel ε (x l - y l) ≤
        (k : ℝ) * (2 * ε / Real.pi) := by
      have hle_indicator : ∀ y : Fin k → ℝ,
          Aᶜ.indicator (fun z => ∏ l, poissonKernel ε (x l - z l)) y ≤
          ∑ j, (Set.univ.pi (fun l : Fin k =>
            if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ))).indicator
            (fun z => ∏ l, poissonKernel ε (x l - z l)) y := by
        intro y
        by_cases hy : y ∈ Aᶜ
        · obtain ⟨j0, hj0⟩ := hcov y hy
          rw [Set.indicator_of_mem hy]
          calc ∏ l, poissonKernel ε (x l - y l)
              = (Set.univ.pi (fun l : Fin k => if l = j0 then (Set.Icc (x l - 1) (x l + 1))ᶜ
                  else (Set.univ : Set ℝ))).indicator
                  (fun z => ∏ l, poissonKernel ε (x l - z l)) y :=
                (Set.indicator_of_mem hj0 (fun z => ∏ l, poissonKernel ε (x l - z l))).symm
            _ ≤ _ := Finset.single_le_sum
                (f := fun j => (Set.univ.pi (fun l : Fin k =>
                    if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ))).indicator
                  (fun z => ∏ l, poissonKernel ε (x l - z l)) y)
                (fun j _ => Set.indicator_nonneg (fun z _ => hKernelProdNonneg z) y)
                (Finset.mem_univ j0)
        · rw [Set.indicator_of_notMem hy]
          exact Finset.sum_nonneg (fun j _ =>
            Set.indicator_nonneg (fun z _ => hKernelProdNonneg z) y)
      have hAcmeas : MeasurableSet Aᶜ := hAmeas.compl
      calc ∫ y in Aᶜ, ∏ l, poissonKernel ε (x l - y l)
          = ∫ y, Aᶜ.indicator (fun z => ∏ l, poissonKernel ε (x l - z l)) y :=
            (MeasureTheory.integral_indicator hAcmeas).symm
        _ ≤ ∫ y, ∑ j, (Set.univ.pi (fun l : Fin k =>
              if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ))).indicator
              (fun z => ∏ l, poissonKernel ε (x l - z l)) y :=
            MeasureTheory.integral_mono
              ((MeasureTheory.integrable_indicator_iff hAcmeas).mpr hKintegrable.integrableOn)
              (MeasureTheory.integrable_finsetSum Finset.univ (fun j _ =>
                (MeasureTheory.integrable_indicator_iff
                  (MeasurableSet.univ_pi (hboxmeas j))).mpr hKintegrable.integrableOn))
              hle_indicator
        _ = ∑ j, ∫ y in Set.univ.pi (fun l : Fin k =>
              if l = j then (Set.Icc (x l - 1) (x l + 1))ᶜ else (Set.univ : Set ℝ)),
              ∏ l, poissonKernel ε (x l - y l) := by
            rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ =>
              (MeasureTheory.integrable_indicator_iff
                (MeasurableSet.univ_pi (hboxmeas j))).mpr hKintegrable.integrableOn)]
            exact Finset.sum_congr rfl
              (fun j _ => MeasureTheory.integral_indicator (MeasurableSet.univ_pi (hboxmeas j)))
        _ ≤ ∑ _j : Fin k, 2 * ε / Real.pi := Finset.sum_le_sum (fun j _ => hCj_bound j)
        _ = (k : ℝ) * (2 * ε / Real.pi) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
    calc |∫ y in Aᶜ, (O x - O y) * ∏ l, poissonKernel ε (x l - y l)|
        = ‖∫ y in Aᶜ, (O x - O y) * ∏ l, poissonKernel ε (x l - y l)‖ := rfl
      _ ≤ ∫ y in Aᶜ, (2 * M0) * ∏ l, poissonKernel ε (x l - y l) :=
          MeasureTheory.norm_integral_le_of_norm_le
            (hKintegrable.integrableOn.const_mul _) (Filter.Eventually.of_forall hnormle)
      _ = 2 * M0 * ∫ y in Aᶜ, ∏ l, poissonKernel ε (x l - y l) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 2 * M0 * ((k : ℝ) * (2 * ε / Real.pi)) :=
          mul_le_mul_of_nonneg_left hKcompl_bound (by positivity)
      _ = 4 * M0 * (k : ℝ) / Real.pi * ε := by ring

/-- **Step 2**: for `x` outside the fixed `2R`-enlarged support box of `O`, the smoothing error
decays like `ε · ∏_j (1+x_j²)⁻¹` directly, since `O x = 0` there. -/
private lemma poissonSmooth_escaping_bound {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O)
    {R M0 : ℝ} (hR : 1 ≤ R) (hM0 : ∀ y, |O y| ≤ M0)
    (hOsupp : ∀ y : Fin k → ℝ, O y ≠ 0 → ∀ l, y l ∈ Set.Icc (-R) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin k → ℝ,
      (∃ j, x j ∉ Set.Icc (-(2 * R)) (2 * R)) →
      |O x - poissonSmooth ε O x| ≤ C * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
  set D : ℝ := 1 + 4 * R ^ 2 + 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi with hD_def
  set Dfar : ℝ := 8 * R * (1 + (4 * R ^ 2)⁻¹) / Real.pi with hDfar_def
  have hDnn : 0 ≤ D := by rw [hD_def]; positivity
  have hDfarnn : 0 ≤ Dfar := by rw [hDfar_def]; positivity
  have hM00 : 0 ≤ M0 := le_trans (abs_nonneg (O (fun _ => 0))) (hM0 (fun _ => 0))
  refine ⟨M0 * Dfar * D ^ (k - 1), by positivity, ?_⟩
  intro ε hε hε1 x ⟨j0, hj0⟩
  have h2R : 2 * R < |x j0| := by
    rw [Set.mem_Icc, not_and_or] at hj0
    rcases hj0 with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hOx : O x = 0 := by
    by_contra hcon
    have hmem := hOsupp x hcon j0
    rw [Set.mem_Icc] at hmem
    have : |x j0| ≤ R := abs_le.2 hmem
    linarith
  rw [hOx, zero_sub, abs_neg]
  unfold poissonSmooth
  have hKintegrable : Integrable (fun y : Fin k → ℝ => ∏ j, poissonKernel ε (x j - y j)) :=
    Integrable.fintype_prod (fun j => poissonKernel_integrable hε (x j))
  have hOKintegrable : Integrable (fun y : Fin k → ℝ =>
      O y * ∏ j, poissonKernel ε (x j - y j)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hO.1.continuous.mul (continuous_finsetProd Finset.univ
        (fun j _ => (poissonKernel_continuous hε).comp (by fun_prop)))
    · exact hO.2.mul_right
  have hmeasBox : MeasurableSet (Set.univ.pi (fun _ : Fin k => Set.Icc (-R) R)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hnormle : ∀ y : Fin k → ℝ, ‖O y * ∏ l, poissonKernel ε (x l - y l)‖ ≤
      (Set.univ.pi (fun _ : Fin k => Set.Icc (-R) R)).indicator
        (fun z => M0 * ∏ l, poissonKernel ε (x l - z l)) y := by
    intro y
    have hKnn : (0:ℝ) ≤ ∏ l, poissonKernel ε (x l - y l) :=
      Finset.prod_nonneg (fun l _ => (poissonKernel_pos hε _).le)
    by_cases hy : y ∈ Set.univ.pi (fun _ : Fin k => Set.Icc (-R) R)
    · rw [Set.indicator_of_mem hy, Real.norm_eq_abs, abs_mul, abs_of_nonneg hKnn]
      exact mul_le_mul_of_nonneg_right (hM0 y) hKnn
    · rw [Set.indicator_of_notMem hy]
      have hOy : O y = 0 := by
        by_contra hcon
        exact hy (Set.mem_univ_pi.mpr (hOsupp y hcon))
      simp [hOy]
  have hmajor_integrable : Integrable (fun y : Fin k → ℝ =>
      (Set.univ.pi (fun _ : Fin k => Set.Icc (-R) R)).indicator
        (fun z => M0 * ∏ l, poissonKernel ε (x l - z l)) y) := by
    rw [MeasureTheory.integrable_indicator_iff hmeasBox]
    exact (hKintegrable.const_mul M0).integrableOn
  refine (MeasureTheory.norm_integral_le_of_norm_le hmajor_integrable
    (Filter.Eventually.of_forall hnormle)).trans
    (le_of_eq_of_le (b := M0 * ∏ j, ∫ t in Set.Icc (-R) R, poissonKernel ε (x j - t)) ?_ ?_)
  · rw [MeasureTheory.integral_indicator hmeasBox, MeasureTheory.integral_const_mul,
      setIntegral_univ_pi_prod_eq_prod (fun _ : Fin k => Set.Icc (-R) R)
        (fun _ => measurableSet_Icc) (fun j t => poissonKernel ε (x j - t))]
  · have hcard : (Finset.univ.erase j0).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
    have hIntNonneg : ∀ j : Fin k, (0:ℝ) ≤ ∫ t in Set.Icc (-R) R, poissonKernel ε (x j - t) :=
      fun j => MeasureTheory.integral_nonneg (fun t => (poissonKernel_pos hε _).le)
    calc M0 * ∏ j, ∫ t in Set.Icc (-R) R, poissonKernel ε (x j - t)
        = (M0 * ∫ t in Set.Icc (-R) R, poissonKernel ε (x j0 - t)) *
            ∏ l ∈ Finset.univ.erase j0, ∫ t in Set.Icc (-R) R, poissonKernel ε (x l - t) := by
          rw [← Finset.mul_prod_erase Finset.univ
            (fun j => ∫ t in Set.Icc (-R) R, poissonKernel ε (x j - t)) (Finset.mem_univ j0),
            mul_assoc]
      _ ≤ (M0 * (Dfar * ε * (1 + x j0 ^ 2)⁻¹)) *
            ∏ l ∈ Finset.univ.erase j0, ∫ t in Set.Icc (-R) R, poissonKernel ε (x l - t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (poissonKernel_mass_Icc_far_le hε (by linarith) h2R) hM00)
            (Finset.prod_nonneg (fun l _ => hIntNonneg l))
      _ ≤ (M0 * (Dfar * ε * (1 + x j0 ^ 2)⁻¹)) *
            ∏ l ∈ Finset.univ.erase j0, (D * (1 + x l ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun l _ => hIntNonneg l)
              (fun l _ => poissonKernel_mass_Icc_le hε hε1 (by linarith) (x l)))
            (by positivity)
      _ = M0 * Dfar * D ^ (k - 1) * ε *
            ((1 + x j0 ^ 2)⁻¹ * ∏ l ∈ Finset.univ.erase j0, (1 + x l ^ 2)⁻¹) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]; ring
      _ = M0 * Dfar * D ^ (k - 1) * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
          rw [Finset.mul_prod_erase Finset.univ (fun j => (1 + x j ^ 2)⁻¹) (Finset.mem_univ j0)]

theorem poissonSmooth_error {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin k → ℝ,
      |O x - poissonSmooth ε O x| ≤ C * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
  obtain ⟨R, hR1, hRsupp⟩ : ∃ R : ℝ, 1 ≤ R ∧
      tsupport O ⊆ Set.univ.pi (fun _ : Fin k => Set.Icc (-R) R) := by
    obtain ⟨R0, _hR0pos, hR0⟩ := hO.2.isBounded.subset_closedBall_lt 0 (0 : Fin k → ℝ)
    refine ⟨max R0 1, le_max_right _ _, hR0.trans (fun z hz => ?_)⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    refine Set.mem_univ_pi.mpr (fun l => Set.mem_Icc.mpr (abs_le.mp ?_))
    calc |z l| = ‖z l‖ := rfl
      _ ≤ ‖z‖ := norm_le_pi_norm z l
      _ ≤ R0 := hz
      _ ≤ max R0 1 := le_max_left _ _
  have hOsupp : ∀ y : Fin k → ℝ, O y ≠ 0 → ∀ l, y l ∈ Set.Icc (-R) R := by
    intro y hy l
    have : y ∈ tsupport O := subset_tsupport O (Function.mem_support.mpr hy)
    exact Set.mem_univ_pi.mp (hRsupp this) l
  obtain ⟨M0, hM00, hM0⟩ := exists_bound_of_hasCompactSupport hO.1.continuous hO.2
  obtain ⟨C1, hC1nn, hC1⟩ := poissonSmooth_uniform_bound hO
  obtain ⟨C2, hC2nn, hC2⟩ := poissonSmooth_escaping_bound hO hR1 hM0 hOsupp
  refine ⟨max (C1 * (1 + 4 * R ^ 2) ^ k) C2, le_max_of_le_right hC2nn, ?_⟩
  intro ε hε hε1 x
  by_cases hxbox : ∀ j, x j ∈ Set.Icc (-(2 * R)) (2 * R)
  · have hprodnn : ∀ j, 0 < (1 + x j ^ 2)⁻¹ := fun j => by positivity
    have hprodge : (1 + 4 * R ^ 2) ^ k * ∏ j, (1 + x j ^ 2)⁻¹ ≥ 1 := by
      have hterm : ∀ j, (1 + x j ^ 2) ≤ (1 + 4 * R ^ 2) := by
        intro j
        have := hxbox j
        rw [Set.mem_Icc] at this
        nlinarith [this.1, this.2]
      have hprod_le : ∏ j, (1 + x j ^ 2) ≤ ∏ j : Fin k, (1 + 4 * R ^ 2) :=
        Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hterm j)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod_le
      have hpos : (0:ℝ) < ∏ j, (1 + x j ^ 2) :=
        Finset.prod_pos (fun j _ => by positivity)
      have hinv : ((1 + 4 * R ^ 2) ^ k)⁻¹ ≤ (∏ j, (1 + x j ^ 2))⁻¹ :=
        inv_anti₀ hpos hprod_le
      have heqprod : ∏ j, (1 + x j ^ 2)⁻¹ = (∏ j, (1 + x j ^ 2))⁻¹ := by
        rw [← Finset.prod_inv_distrib]
      rw [heqprod]
      have hfin : ((1 + 4 * R ^ 2) ^ k)⁻¹ * (1 + 4 * R ^ 2) ^ k = 1 := by
        field_simp
      nlinarith [hinv, hfin, mul_le_mul_of_nonneg_right hinv
        (show (0:ℝ) ≤ (1 + 4 * R ^ 2) ^ k by positivity)]
    calc |O x - poissonSmooth ε O x| ≤ C1 * ε := hC1 ε hε hε1 x
      _ ≤ C1 * (1 + 4 * R ^ 2) ^ k * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
          nlinarith [hprodge, hC1nn, hε.le,
            mul_le_mul_of_nonneg_left hprodge (mul_nonneg hC1nn hε.le)]
      _ ≤ max (C1 * (1 + 4 * R ^ 2) ^ k) C2 * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
          gcongr
          exact le_max_left _ _
  · push_neg at hxbox
    calc |O x - poissonSmooth ε O x| ≤ C2 * ε * ∏ j, (1 + x j ^ 2)⁻¹ := hC2 ε hε hε1 x hxbox
      _ ≤ max (C1 * (1 + 4 * R ^ 2) ^ k) C2 * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => by positivity))
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hε.le

end RBM
