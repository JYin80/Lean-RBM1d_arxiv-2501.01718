/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.StieltjesEtaMonotone
import RBM1D.Flow.OUComparisonProductContraction

/-!
# Pointwise absolute-kernel bound for the centered product contraction

This module takes the signed deterministic identity and bounds it by the positive-weight
`paperL1Kernel` and `paperL2Kernel` from (2.25). It makes no assertion about an OU expectation,
time integral, or stochastic process.
-/

namespace RBM

open Matrix
open scoped ComplexConjugate

private theorem stieltjes_im_nonneg_of_upper {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (stieltjes H z).im := by
  have hformula := stieltjes_im_eq_normalized_specWeight H hH z.re z.im hz
  have hz_eq : z.re + z.im * Complex.I = z := by
    apply Complex.ext <;> simp
  rw [hz_eq] at hformula
  have hformula' : (stieltjes H z).im =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ l : n, specWeight hH z.re z.im l := by
    simpa [specWeight] using hformula
  rw [hformula']
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg fun l _ => specWeight_nonneg hH z.re hz.le l

private theorem stieltjes_im_prod_nonneg {ι : Type*}
    {d : Gauss.Dims} {N : ℕ} {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) (z : ι → ℂ) (t : Finset ι)
    (hz : ∀ i ∈ t, 0 < (z i).im) :
    0 ≤ ∏ i ∈ t, (stieltjes H (z i)).im := by
  exact Finset.prod_nonneg fun i hi => stieltjes_im_nonneg_of_upper hH (hz i hi)

private theorem paperK1_conj_eq_false_false {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) (z : ℂ) :
    conj (paperK1Contraction N H z true true) =
      paperK1Contraction N H z false false := by
  have hG : signedGreen H z false = (signedGreen H z true)ᴴ := by
    simpa [signedGreen, Gsig] using (Gsig_conjTranspose hH z true).symm
  have hSq (a : d.Idx N) :
      conj ((signedGreen H z true * signedGreen H z true) a a) =
        (signedGreen H z false * signedGreen H z false) a a := by
    calc
      _ = ((signedGreen H z true * signedGreen H z true)ᴴ) a a := by
        simp [Matrix.conjTranspose_apply]
      _ = ((signedGreen H z true)ᴴ * (signedGreen H z true)ᴴ) a a := by
        rw [Matrix.conjTranspose_mul]
      _ = _ := by rw [← hG]
  have hDiag (b : d.Idx N) :
      conj (signedGreen H z true b b) = signedGreen H z false b b := by
    calc
      _ = ((signedGreen H z true)ᴴ) b b := by
        simp [Matrix.conjTranspose_apply]
      _ = _ := by rw [hG]
  simp only [paperK1Contraction, map_mul, map_sum, map_inv₀, map_natCast,
    Complex.conj_ofReal, hSq, hDiag]

private theorem paperK1_im_abs_le {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) (z : ℂ) :
    ‖((2 * (paperK1Contraction N H z true true).im : ℝ) : ℂ)‖ ≤
      paperL1Kernel d N H z := by
  let K := paperK1Contraction N H z true true
  let Kbar := paperK1Contraction N H z false false
  have hconj : conj K = Kbar := paperK1_conj_eq_false_false hH z
  have him : (K - conj K).im = 2 * K.im := by
    simp [Complex.sub_im, Complex.conj_im]
    ring
  rw [Complex.norm_real, Real.norm_eq_abs, ← him, hconj]
  have htriangle : |(K - Kbar).im| ≤ |K.im| + |Kbar.im| := by
    simpa only [Complex.sub_im] using (abs_sub (K.im) (Kbar.im))
  have htoNorm : |K.im| + |Kbar.im| ≤ ‖K‖ + ‖Kbar‖ :=
    add_le_add (Complex.abs_im_le_norm K) (Complex.abs_im_le_norm Kbar)
  have hsum : ‖K‖ + ‖Kbar‖ ≤ paperL1Kernel d N H z := by
    change ‖paperK1Contraction N H z true true‖ +
        ‖paperK1Contraction N H z false false‖ ≤
      ∑ σ : Bool, ∑ τ : Bool, ‖paperK1Contraction N H z σ τ‖
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    nlinarith [norm_nonneg (paperK1Contraction N H z true false),
      norm_nonneg (paperK1Contraction N H z false true)]
  exact htriangle.trans (htoNorm.trans hsum)

private theorem paperK2_abs_le {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (z₁ z₂ : ℂ) :
    ‖-(1 / 4 : ℂ) *
        (paperK2Contraction N H z₁ z₂ true true -
          paperK2Contraction N H z₁ z₂ true false -
          paperK2Contraction N H z₁ z₂ false true +
          paperK2Contraction N H z₁ z₂ false false)‖ ≤
      paperL2Kernel d N H z₁ z₂ := by
  let A := paperK2Contraction N H z₁ z₂ true true
  let B := paperK2Contraction N H z₁ z₂ true false
  let C := paperK2Contraction N H z₁ z₂ false true
  let D := paperK2Contraction N H z₁ z₂ false false
  have hcomb : ‖A - B - C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    calc
      ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
      _ ≤ (‖A - B‖ + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
  have hsum : ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤ paperL2Kernel d N H z₁ z₂ := by
    change ‖paperK2Contraction N H z₁ z₂ true true‖ +
        ‖paperK2Contraction N H z₁ z₂ true false‖ +
        ‖paperK2Contraction N H z₁ z₂ false true‖ +
        ‖paperK2Contraction N H z₁ z₂ false false‖ ≤
      ∑ σ : Bool, ∑ τ : Bool, ‖paperK2Contraction N H z₁ z₂ σ τ‖
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    exact le_of_eq (by ring)
  rw [norm_mul]
  have hfour : 0 ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by positivity
  have hnormquarter : ‖-(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
  rw [hnormquarter]
  exact (mul_le_mul_of_nonneg_left hcomb (by norm_num)).trans <|
    by nlinarith [hsum]

/-- **Pointwise deterministic kernel bound behind (2.25).** For a Hermitian matrix and any finite
family of spectral parameters in the upper half-plane, the norm of the full signed centered
double-sum contraction is bounded by the positive-weight `paperL1Kernel` and ordered
`paperL2Kernel` sums. The sequence index `N` remains distinct from the physical dimension
`Fintype.card (d.Idx N)` used by the kernels. -/
theorem centeredVariance_wirtProduct_kernel_bound {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, 0 < (z i).im) :
    ‖∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) *
          Gauss.wirtSecond d N
            (fun K => ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)) H a b‖ ≤
      (∑ i ∈ s,
        (∏ j ∈ s.erase i, (stieltjes H (z j)).im) * paperL1Kernel d N H (z i)) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im) *
          paperL2Kernel d N H (z i) (z j) := by
  have hz0 : ∀ i ∈ s, (z i).im ≠ 0 := fun i hi => (ne_of_gt (hz i hi))
  rw [centeredVariance_wirtProduct_contraction_eq s hH z hz0]
  have hfirst :
      ‖∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
          ((2 * (paperK1Contraction N H (z i) true true).im : ℝ) : ℂ)‖ ≤
      ∑ i ∈ s,
        (∏ j ∈ s.erase i, (stieltjes H (z j)).im) * paperL1Kernel d N H (z i) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hprod := stieltjes_im_prod_nonneg hH z (s.erase i)
      (fun j hj => hz j (Finset.mem_of_mem_erase hj))
    have hterm := paperK1_im_abs_le hH (z i)
    have hmul := mul_le_mul_of_nonneg_left hterm hprod
    calc
      _ = (∏ j ∈ s.erase i, (stieltjes H (z j)).im) *
          ‖((2 * (paperK1Contraction N H (z i) true true).im : ℝ) : ℂ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
      _ ≤ _ := hmul
  have hsecond :
      ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
          (-(1 / 4 : ℂ) *
            (paperK2Contraction N H (z i) (z j) true true -
              paperK2Contraction N H (z i) (z j) true false -
              paperK2Contraction N H (z i) (z j) false true +
              paperK2Contraction N H (z i) (z j) false false))‖ ≤
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im) *
          paperL2Kernel d N H (z i) (z j) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    have hprod := stieltjes_im_prod_nonneg hH z ((s.erase i).erase j)
      (fun k hk => hz k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))
    have hterm := paperK2_abs_le (d := d) (N := N) (H := H) (z i) (z j)
    have hmul := mul_le_mul_of_nonneg_left hterm hprod
    calc
      _ = (∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im) *
          ‖-(1 / 4 : ℂ) *
            (paperK2Contraction N H (z i) (z j) true true -
              paperK2Contraction N H (z i) (z j) true false -
              paperK2Contraction N H (z i) (z j) false true +
              paperK2Contraction N H (z i) (z j) false false)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
      _ ≤ _ := hmul
  calc
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hfirst hsecond)

#print axioms centeredVariance_wirtProduct_kernel_bound

end RBM
