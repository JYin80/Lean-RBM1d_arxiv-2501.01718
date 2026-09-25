/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUComparisonContraction

/-!
# Centered product-Hessian contraction

This module reuses the T1409/T1426 deterministic contraction lemmas and proves the full finite-
product identity.  The statement is pointwise in the Hermitian matrix and spectral parameters; it
does not include an absolute-value kernel bound, an OU expectation, a time integral, or a pathwise
claim.
-/

namespace RBM

open Matrix
open scoped ComplexConjugate

private def productEntryMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) : Matrix n n ℂ := Matrix.single i j 1

private theorem product_matrix_mul_entry_apply {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j a b : n) :
    (X * productEntryMatrix i j) a b = if b = j then X a i else 0 := by
  by_cases hb : b = j
  · subst b
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [productEntryMatrix]
    · intro x hx hxi
      simp [productEntryMatrix, hxi.symm]
    · simp
  · simp [productEntryMatrix, Matrix.mul_apply, Matrix.single_apply, hb, Ne.symm hb]

private theorem product_matrix_mul_entry_mul_apply {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) (i j a b : n) :
    (X * productEntryMatrix i j * Y) a b = X a i * Y j b := by
  rw [Matrix.mul_apply]
  simp_rw [product_matrix_mul_entry_apply]
  simp

private theorem product_trace_green_single {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (a b : n) :
    (G * productEntryMatrix a b * G).trace = (G * G) b a := by
  calc
    (G * productEntryMatrix a b * G).trace =
        (G * (productEntryMatrix a b * G)).trace := by
          congr 1
          simp [Matrix.mul_assoc]
    _ = ((productEntryMatrix a b * G) * G).trace := Matrix.trace_mul_comm _ _
    _ = (productEntryMatrix a b * (G * G)).trace := by
          congr 1 <;> simp [Matrix.mul_assoc]
    _ = (G * G) b a := by
          simpa [productEntryMatrix] using Matrix.trace_single_mul a b (1 : ℂ) (G * G)

private theorem product_Bmat_real_eq_entryMatrices {d : Gauss.Dims} {N : ℕ}
    {i j : d.Idx N} (hij : i ≠ j) :
    Gauss.Bmat d N i j true = productEntryMatrix i j + productEntryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply,
        h1, h2, h1', h2', and_comm]

private theorem product_Bmat_imag_eq_entryMatrices {d : Gauss.Dims} {N : ℕ}
    {i j : d.Idx N} (hij : i ≠ j) :
    Gauss.Bmat d N i j false =
      Complex.I • productEntryMatrix i j - Complex.I • productEntryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply,
        h1, h2, h1', h2', and_comm]

private theorem product_Bmat_diag_eq_entryMatrix {d : Gauss.Dims} {N : ℕ}
    (i : d.Idx N) :
    Gauss.Bmat d N i i true = productEntryMatrix i i := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply]
  · have h' : ¬ (i = k ∧ i = l) := by
      rintro ⟨hik, hil⟩
      exact h ⟨hik.symm, hil.symm⟩
    simp [Gauss.Bmat, productEntryMatrix, Matrix.single_apply, h, h']

private theorem product_trace_green_Bmat_real {d : Gauss.Dims} {N : ℕ}
    (G : Matrix (d.Idx N) (d.Idx N) ℂ) {i j : d.Idx N} (hij : i ≠ j) :
    (G * Gauss.Bmat d N i j true * G).trace = (G * G) j i + (G * G) i j := by
  rw [product_Bmat_real_eq_entryMatrices hij, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add, product_trace_green_single, product_trace_green_single]

private theorem product_trace_green_Bmat_imag {d : Gauss.Dims} {N : ℕ}
    (G : Matrix (d.Idx N) (d.Idx N) ℂ) {i j : d.Idx N} (hij : i ≠ j) :
    (G * Gauss.Bmat d N i j false * G).trace =
      Complex.I * ((G * G) j i - (G * G) i j) := by
  rw [product_Bmat_imag_eq_entryMatrices hij]
  have hmul :
      G * (Complex.I • productEntryMatrix i j - Complex.I • productEntryMatrix j i) * G =
        Complex.I • (G * productEntryMatrix i j * G) -
          Complex.I • (G * productEntryMatrix j i * G) := by
    calc
      _ = (Complex.I • (G * productEntryMatrix i j) -
          Complex.I • (G * productEntryMatrix j i)) * G := by
            simp [Matrix.mul_sub, Matrix.mul_smul]
      _ = _ := by rw [Matrix.sub_mul, smul_mul_assoc, smul_mul_assoc]
  rw [hmul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    product_trace_green_single, product_trace_green_single]
  simp only [smul_eq_mul]
  ring

private theorem product_lineFirst_wirtinger {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : d.Idx N) :
    stieltjesImWirtingerFirst H z a b =
      if a = b then
        (stieltjesImLineFirst H (Gauss.Bmat d N a a true) z 0 : ℂ)
      else
        (1 / 2 : ℂ) *
          ((stieltjesImLineFirst H (Gauss.Bmat d N a b true) z 0 : ℂ) -
            Complex.I * (stieltjesImLineFirst H (Gauss.Bmat d N a b false) z 0 : ℂ)) := by
  by_cases hab : a = b
  · subst b
    rw [stieltjesImWirtingerFirst_entry_formula hH z hz a a]
    let q : ℂ := (Fintype.card (d.Idx N) : ℂ)⁻¹
    have hline : stieltjesImLineFirst H (Gauss.Bmat d N a a true) z 0 =
        (-q * (green H z * green H z) a a).im := by
      simp [stieltjesImLineFirst, q, zero_smul, add_zero,
        product_Bmat_diag_eq_entryMatrix, product_trace_green_single]
    have hq : q.im = 0 := by simp [q]
    rw [if_pos rfl, hline]
    apply Complex.ext <;>
      simp [q, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, hq] <;> ring_nf
  · rw [stieltjesImWirtingerFirst_entry_formula hH z hz a b, if_neg hab]
    let q : ℂ := (Fintype.card (d.Idx N) : ℂ)⁻¹
    have hreal : stieltjesImLineFirst H (Gauss.Bmat d N a b true) z 0 =
        (-q * ((green H z * green H z) b a + (green H z * green H z) a b)).im := by
      simp [stieltjesImLineFirst, q, zero_smul, add_zero,
        product_trace_green_Bmat_real (green H z) hab]
    have himag : stieltjesImLineFirst H (Gauss.Bmat d N a b false) z 0 =
        (-q * (Complex.I * ((green H z * green H z) b a -
          (green H z * green H z) a b))).im := by
      simp [stieltjesImLineFirst, q, zero_smul, add_zero,
        product_trace_green_Bmat_imag (green H z) hab]
    have hq : q.im = 0 := by simp [q]
    rw [hreal, himag]
    apply Complex.ext <;>
      simp [q, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, hq] <;> ring_nf

private theorem product_lineFirst_neg {n : Type*} [Fintype n] [DecidableEq n]
    (H A : Matrix n n ℂ) (z : ℂ) :
    stieltjesImLineFirst H (-A) z 0 = -stieltjesImLineFirst H A z 0 := by
  simp [stieltjesImLineFirst, Matrix.mul_neg, Matrix.neg_mul]

private noncomputable def productCrossCoord {d : Gauss.Dims} {N : ℕ}
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z₁ z₂ : ℂ)
    (a b : d.Idx N) : ℂ :=
  if a = b then
    (stieltjesImLineFirst H (Gauss.Bmat d N a a true) z₂ 0 : ℂ) *
      (stieltjesImLineFirst H (Gauss.Bmat d N a a true) z₁ 0 : ℂ)
  else
    (1 / 4 : ℂ) *
      ((stieltjesImLineFirst H (Gauss.Bmat d N a b true) z₂ 0 : ℂ) *
          (stieltjesImLineFirst H (Gauss.Bmat d N a b true) z₁ 0 : ℂ) +
        (stieltjesImLineFirst H (Gauss.Bmat d N a b false) z₂ 0 : ℂ) *
          (stieltjesImLineFirst H (Gauss.Bmat d N a b false) z₁ 0 : ℂ))

private theorem productCrossCoord_eq_symmWirtinger {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (a b : d.Idx N) :
    productCrossCoord H z₁ z₂ a b =
      (1 / 2 : ℂ) *
        (stieltjesImWirtingerFirst H z₁ a b * stieltjesImWirtingerFirst H z₂ b a +
          stieltjesImWirtingerFirst H z₁ b a * stieltjesImWirtingerFirst H z₂ a b) := by
  by_cases hab : a = b
  · subst b
    simp [productCrossCoord, product_lineFirst_wirtinger hH z₁ hz₁,
      product_lineFirst_wirtinger hH z₂ hz₂]
    ring
  · have h₁ := product_lineFirst_wirtinger hH z₁ hz₁ a b
    have h₂ := product_lineFirst_wirtinger hH z₂ hz₂ a b
    have h₁' := product_lineFirst_wirtinger hH z₁ hz₁ b a
    have h₂' := product_lineFirst_wirtinger hH z₂ hz₂ b a
    rw [if_neg hab] at h₁ h₂
    rw [if_neg (Ne.symm hab)] at h₁' h₂'
    have htrue : Gauss.Bmat d N b a true = Gauss.Bmat d N a b true :=
      Gauss.Bmat_swap_true d N a b
    have hfalse : Gauss.Bmat d N b a false = -Gauss.Bmat d N a b false :=
      Gauss.Bmat_swap_false d N hab
    rw [htrue, hfalse, product_lineFirst_neg] at h₁' h₂'
    simp only [Complex.ofReal_neg] at h₁' h₂'
    simp only [productCrossCoord, if_neg hab, h₁, h₂, h₁', h₂']
    ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
    ring_nf

private theorem product_cross_contraction_eq {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
    (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) * productCrossCoord H z₁ z₂ a b) =
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) *
          stieltjesImWirtingerFirst H z₁ a b * stieltjesImWirtingerFirst H z₂ b a := by
  let F : d.Idx N → d.Idx N → ℂ := fun a b =>
    (centeredVarianceEntry d N a b : ℂ) *
      stieltjesImWirtingerFirst H z₁ a b * stieltjesImWirtingerFirst H z₂ b a
  let G : d.Idx N → d.Idx N → ℂ := fun a b =>
    (centeredVarianceEntry d N a b : ℂ) *
      stieltjesImWirtingerFirst H z₁ b a * stieltjesImWirtingerFirst H z₂ a b
  have hswap : (∑ a : d.Idx N, ∑ b : d.Idx N, G a b) =
      ∑ a : d.Idx N, ∑ b : d.Idx N, F a b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [F, G]
    rw [centeredVarianceEntry_symm]
  have hadd : (∑ a : d.Idx N, ∑ b : d.Idx N, (F a b + G a b)) =
      (∑ a : d.Idx N, ∑ b : d.Idx N, F a b) +
        ∑ a : d.Idx N, ∑ b : d.Idx N, G a b := by
    simp only [Finset.sum_add_distrib]
  calc
    _ = ∑ a : d.Idx N, ∑ b : d.Idx N,
          (1 / 2 : ℂ) * (F a b + G a b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [productCrossCoord_eq_symmWirtinger hH z₁ z₂ hz₁ hz₂]
          dsimp [F, G]
          ring
    _ = (1 / 2 : ℂ) *
          (∑ a : d.Idx N, ∑ b : d.Idx N, (F a b + G a b)) := by
          calc
            _ = ∑ a : d.Idx N,
                  ((1 / 2 : ℂ) * ∑ b : d.Idx N, (F a b + G a b)) := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]
    _ = (1 / 2 : ℂ) *
          ((∑ a : d.Idx N, ∑ b : d.Idx N, F a b) +
            ∑ a : d.Idx N, ∑ b : d.Idx N, G a b) := by rw [hadd]
    _ = _ := by rw [hswap]; ring

private noncomputable def productSingleCoord {d : Gauss.Dims} {N : ℕ}
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ℂ)
    (a b : d.Idx N) : ℂ :=
  if a = b then
    (stieltjesImLineSecond H (Gauss.Bmat d N a a true) z : ℂ)
  else
    (1 / 4 : ℂ) *
      ((stieltjesImLineSecond H (Gauss.Bmat d N a b true) z : ℂ) +
        (stieltjesImLineSecond H (Gauss.Bmat d N a b false) z : ℂ))

private theorem productSingleCoord_eq_wirtSecond {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : d.Idx N) :
    productSingleCoord H z a b =
      Gauss.wirtSecond d N (fun K => (stieltjes K z).im) H a b := by
  let u : Unit := ()
  have h := wirtSecond_stieltjesImProduct_expansion
    (d := d) (N := N) (s := ({u} : Finset Unit)) (H := H) hH
    (fun _ : Unit => z) (by intro i hi; simpa using hz) a b
  convert h.symm using 1 <;>
    simp [productSingleCoord, stieltjesImProductLineSecond] <;> ring

private theorem product_lineSecond_rearrange {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (single : ι → ℝ) (cross : ι → ι → ℝ) (deriv : ι → ℝ) :
    s.sum (fun i => single i + (s.erase i).sum (fun j => cross i j) * deriv i) =
      s.sum single + s.sum (fun i =>
        (s.erase i).sum (fun j => cross i j * deriv i)) := by
  calc
    _ = s.sum single + s.sum (fun i => (s.erase i).sum (fun j => cross i j) * deriv i) := by
          rw [Finset.sum_add_distrib]
    _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]

private theorem product_lineSecond_complex_split {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (H A : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ι → ℂ) :
    (stieltjesImProductLineSecond s H A z : ℂ) =
      ∑ i ∈ s,
        ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0 : ℝ) : ℂ) *
          (stieltjesImLineSecond H A (z i) : ℂ) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0 : ℝ) : ℂ) *
          (stieltjesImLineFirst H A (z j) 0 : ℂ) *
          (stieltjesImLineFirst H A (z i) 0 : ℂ) := by
  classical
  exact_mod_cast product_lineSecond_rearrange s
    (fun i => (∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
      stieltjesImLineSecond H A (z i))
    (fun i j => (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
      stieltjesImLineFirst H A (z j) 0)
    (fun i => stieltjesImLineFirst H A (z i) 0)

private theorem product_sum_weighted_double {α β ι : Type*}
    [Fintype α] [Fintype β] [DecidableEq ι]
    (s : Finset ι) (V : α → β → ℂ) (w : ι → ℂ)
    (f : ι → α → β → ℂ) :
    (∑ a : α, ∑ b : β, V a b * (∑ i ∈ s, w i * f i a b)) =
      ∑ i ∈ s, w i * (∑ a : α, ∑ b : β, V a b * f i a b) := by
  classical
  calc
    _ = ∑ a : α, ∑ b : β, ∑ i ∈ s, w i * (V a b * f i a b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ a : α, ∑ i ∈ s, ∑ b : β, w i * (V a b * f i a b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ a : α, ∑ b : β, w i * (V a b * f i a b) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, w i * (∑ a : α, ∑ b : β, V a b * f i a b) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            _ = ∑ a : α, w i * ∑ b : β, V a b * f i a b := by
                  apply Finset.sum_congr rfl
                  intro a _
                  exact (Finset.mul_sum _ _ _).symm
            _ = _ := (Finset.mul_sum _ _ _).symm

private theorem product_wirtSecond_leibniz {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0)
    (a b : d.Idx N) :
    Gauss.wirtSecond d N
      (fun K => ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)) H a b =
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
          Gauss.wirtSecond d N (fun K => (stieltjes K (z i)).im) H a b) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
          productCrossCoord H (z i) (z j) a b := by
  classical
  have hsingle :
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
          Gauss.wirtSecond d N (fun K => (stieltjes K (z i)).im) H a b) =
      ∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
          productSingleCoord H (z i) a b := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← productSingleCoord_eq_wirtSecond hH (z i) (hz i hi) a b]
  rw [wirtSecond_stieltjesImProduct_expansion s H hH z hz a b]
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl]
    rw [hsingle]
    have hline := product_lineSecond_complex_split s H (Gauss.Bmat d N a a true) z
    simp only [stieltjesImAlong, Complex.ofReal_zero, zero_smul, add_zero] at hline
    have hassoc :
        (∑ i ∈ s, ∑ j ∈ s.erase i,
          ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
            (stieltjesImLineFirst H (Gauss.Bmat d N a a true) (z j) 0 : ℂ) *
            (stieltjesImLineFirst H (Gauss.Bmat d N a a true) (z i) 0 : ℂ)) =
        ∑ i ∈ s, ∑ j ∈ s.erase i,
          ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
            ((stieltjesImLineFirst H (Gauss.Bmat d N a a true) (z j) 0 : ℂ) *
              (stieltjesImLineFirst H (Gauss.Bmat d N a a true) (z i) 0 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hline' :
        (stieltjesImProductLineSecond s H (Gauss.Bmat d N a a true) z : ℂ) =
          (∑ i ∈ s,
            ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
              (stieltjesImLineSecond H (Gauss.Bmat d N a a true) (z i) : ℂ)) +
          ∑ i ∈ s, ∑ j ∈ s.erase i,
            ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
              ((stieltjesImLineFirst H (Gauss.Bmat d N a a true) (z j) 0 : ℂ) *
                (stieltjesImLineFirst H (Gauss.Bmat d N a a true) (z i) 0 : ℂ)) := by
      calc
        _ = _ := hline
        _ = _ := congrArg (fun x : ℂ =>
          (∑ i ∈ s,
            ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
              (stieltjesImLineSecond H (Gauss.Bmat d N a a true) (z i) : ℂ)) + x) hassoc
    simpa only [productSingleCoord, productCrossCoord, ite_true] using hline'
  · simp only [if_neg hab, smul_eq_mul]
    rw [hsingle]
    have htrue := product_lineSecond_complex_split s H (Gauss.Bmat d N a b true) z
    have hfalse := product_lineSecond_complex_split s H (Gauss.Bmat d N a b false) z
    simp only [stieltjesImAlong, Complex.ofReal_zero, zero_smul, add_zero] at htrue hfalse
    let c : ℂ := (1 / 4 : ℂ)
    let ST : ℂ := ∑ i ∈ s,
      ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
        (stieltjesImLineSecond H (Gauss.Bmat d N a b true) (z i) : ℂ)
    let SF : ℂ := ∑ i ∈ s,
      ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
        (stieltjesImLineSecond H (Gauss.Bmat d N a b false) (z i) : ℂ)
    let XT : ℂ := ∑ i ∈ s, ∑ j ∈ s.erase i,
      ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
        (stieltjesImLineFirst H (Gauss.Bmat d N a b true) (z j) 0 : ℂ) *
        (stieltjesImLineFirst H (Gauss.Bmat d N a b true) (z i) 0 : ℂ)
    let XF : ℂ := ∑ i ∈ s, ∑ j ∈ s.erase i,
      ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
        (stieltjesImLineFirst H (Gauss.Bmat d N a b false) (z j) 0 : ℂ) *
        (stieltjesImLineFirst H (Gauss.Bmat d N a b false) (z i) 0 : ℂ)
    have hsingleCoord :
        (∑ i ∈ s,
          ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
            productSingleCoord H (z i) a b) = c * (ST + SF) := by
      simp only [productSingleCoord, if_neg hab]
      calc
        _ = ∑ i ∈ s,
              c * (((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
                (stieltjesImLineSecond H (Gauss.Bmat d N a b true) (z i) : ℂ) +
                ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
                (stieltjesImLineSecond H (Gauss.Bmat d N a b false) (z i) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = c * (ST + SF) := by
              simp only [mul_add, Finset.sum_add_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hcrossCoord :
        (∑ i ∈ s, ∑ j ∈ s.erase i,
          ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
            productCrossCoord H (z i) (z j) a b) = c * (XT + XF) := by
      simp only [productCrossCoord, if_neg hab]
      calc
        _ = ∑ i ∈ s, ∑ j ∈ s.erase i,
              ((c * (((∏ k ∈ (s.erase i).erase j,
                  (stieltjes H (z k)).im : ℝ) : ℂ) *
                    (stieltjesImLineFirst H (Gauss.Bmat d N a b true) (z j) 0 : ℂ) *
                    (stieltjesImLineFirst H (Gauss.Bmat d N a b true) (z i) 0 : ℂ))) +
                c * (((∏ k ∈ (s.erase i).erase j,
                  (stieltjes H (z k)).im : ℝ) : ℂ) *
                    (stieltjesImLineFirst H (Gauss.Bmat d N a b false) (z j) 0 : ℂ) *
                    (stieltjesImLineFirst H (Gauss.Bmat d N a b false) (z i) 0 : ℂ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = c * (XT + XF) := by
              simp only [Finset.sum_add_distrib]
              simp only [← Finset.mul_sum]
              change c * XT + c * XF = c * (XT + XF)
              ring
    rw [hsingleCoord, hcrossCoord, htrue, hfalse]
    simp only [Complex.real_smul]
    rw [show ((1 / 4 : ℝ) : ℂ) = c by norm_num [c]]
    ring

theorem centeredVariance_wirtProduct_contraction_eq {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        Gauss.wirtSecond d N
          (fun K => ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)) H a b) =
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ) *
          ((2 * (paperK1Contraction N H (z i) true true).im : ℝ) : ℂ)) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ) *
          (-(1 / 4 : ℂ) *
            (paperK2Contraction N H (z i) (z j) true true -
              paperK2Contraction N H (z i) (z j) true false -
              paperK2Contraction N H (z i) (z j) false true +
              paperK2Contraction N H (z i) (z j) false false)) := by
  classical
  let V : d.Idx N → d.Idx N → ℂ := fun a b => centeredVarianceEntry d N a b
  let rem1 : ι → ℂ := fun i =>
    ((∏ j ∈ s.erase i, (stieltjes H (z j)).im : ℝ) : ℂ)
  let rem2 : ι → ι → ℂ := fun i j =>
    ((∏ k ∈ (s.erase i).erase j, (stieltjes H (z k)).im : ℝ) : ℂ)
  let single : ι → d.Idx N → d.Idx N → ℂ := fun i a b =>
    Gauss.wirtSecond d N (fun K => (stieltjes K (z i)).im) H a b
  let cross : ι → ι → d.Idx N → d.Idx N → ℂ := fun i j a b =>
    productCrossCoord H (z i) (z j) a b
  have hpoint (a b : d.Idx N) := product_wirtSecond_leibniz s hH z hz a b
  have hsplit :
      (∑ a : d.Idx N, ∑ b : d.Idx N,
        V a b * Gauss.wirtSecond d N
          (fun K => ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)) H a b) =
        (∑ a : d.Idx N, ∑ b : d.Idx N,
          V a b * (∑ i ∈ s, rem1 i * single i a b)) +
        ∑ a : d.Idx N, ∑ b : d.Idx N,
          V a b * (∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j * cross i j a b) := by
    simp_rw [hpoint]
    simp only [V, rem1, rem2, single, cross, mul_add, Finset.sum_add_distrib]
  have hfirst := product_sum_weighted_double s V rem1 single
  have hcross₁ := product_sum_weighted_double s V (fun _ => (1 : ℂ))
    (fun i a b => ∑ j ∈ s.erase i, rem2 i j * cross i j a b)
  have hcross₂ (i : ι) :
      (∑ a : d.Idx N, ∑ b : d.Idx N,
        V a b * (∑ j ∈ s.erase i, rem2 i j * cross i j a b)) =
        ∑ j ∈ s.erase i, rem2 i j *
          (∑ a : d.Idx N, ∑ b : d.Idx N, V a b * cross i j a b) :=
    product_sum_weighted_double (s.erase i) V (rem2 i) (cross i)
  have hcross :
      (∑ a : d.Idx N, ∑ b : d.Idx N,
        V a b * (∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j * cross i j a b)) =
      ∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j *
        (∑ a : d.Idx N, ∑ b : d.Idx N, V a b * cross i j a b) := by
    simpa only [one_mul] using hcross₁.trans (by
      apply Finset.sum_congr rfl
      intro i hi
      rw [one_mul]
      exact hcross₂ i)
  calc
    _ = (∑ i ∈ s, rem1 i *
          (∑ a : d.Idx N, ∑ b : d.Idx N, V a b * single i a b)) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j *
          (∑ a : d.Idx N, ∑ b : d.Idx N, V a b * cross i j a b) := by
          rw [hsplit, hfirst, hcross]
    _ = _ := by
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro i hi
            simpa [V, single, rem1] using congrArg (fun x : ℂ => rem1 i * x)
              (centeredVariance_single_contraction_eq hH (z i) (hz i hi))
          · apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            have hcrossContract := product_cross_contraction_eq hH (z i) (z j)
              (hz i hi) (hz j (Finset.mem_of_mem_erase hj))
            have hpair := centeredVariance_wirtingerFirst_product_eq hH
              (z i) (z j) (hz i hi) (hz j (Finset.mem_of_mem_erase hj))
            simpa [V, cross, rem2] using congrArg (fun x : ℂ => rem2 i j * x)
              (hcrossContract.trans hpair)

theorem centeredVariance_wirtProduct_empty {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} {H : Matrix (d.Idx N) (d.Idx N) ℂ} (z : ι → ℂ) :
    (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        Gauss.wirtSecond d N
          (fun K => ((∏ i ∈ (∅ : Finset ι), (stieltjes K (z i)).im : ℝ) : ℂ)) H a b) = 0 := by
  simp [Gauss.wirtSecond, Gauss.coordD2]

theorem centeredVariance_wirtProduct_singleton_eq {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} (u : ι)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) (z : ι → ℂ)
    (hz : ∀ i ∈ ({u} : Finset ι), (z i).im ≠ 0) :
    (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        Gauss.wirtSecond d N
          (fun K => ((∏ i ∈ ({u} : Finset ι), (stieltjes K (z i)).im : ℝ) : ℂ)) H a b) =
      ((2 * (paperK1Contraction N H (z u) true true).im : ℝ) : ℂ) := by
  classical
  simpa using centeredVariance_single_contraction_eq hH (z u) (hz u (by simp))

end RBM
