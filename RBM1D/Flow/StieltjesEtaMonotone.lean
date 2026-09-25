/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Universality

/-!
# Monotonicity of the finite-matrix Stieltjes transform in the spectral scale

For a finite Hermitian matrix, `η Im m(E + iη)` is the normalized sum of
`η² / ((λ - E)² + η²)`. Each summand is nondecreasing for `η > 0`.
This is the deterministic estimate used after (2.27) in the proof of (2.28).
-/

namespace RBM

open Matrix

/-- For a finite Hermitian matrix, the paper-sign Stieltjes transform has the spectral formula
`Im m(E+iη) = |n|⁻¹ ∑ₗ η / ((λₗ-E)²+η²)`, for positive `η`. -/
theorem stieltjes_im_eq_normalized_specWeight {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) :
    (stieltjes H (E + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ l : n,
        (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
  classical
  let U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  let d : n → ℂ := fun l => ((hH.eigenvalues l : ℂ) - (E + η * Complex.I))⁻¹
  have hz (l : n) : (hH.eigenvalues l : ℂ) ≠ E + η * Complex.I := by
    intro h
    have him := congrArg Complex.im h
    have : 0 = η := by simpa using him
    exact (ne_of_gt hη) this.symm
  have hgreen : green H (E + η * Complex.I) = U * diagonal d * star U := by
    exact green_eq_spectral hH hz
  have htrace : (green H (E + η * Complex.I)).trace = ∑ l : n, d l := by
    rw [hgreen]
    calc
      (U * diagonal d * star U).trace = (diagonal d * (star U * U)).trace := by
        calc
          (U * diagonal d * star U).trace = (U * (diagonal d * star U)).trace := by
            rw [Matrix.mul_assoc]
          _ = ((diagonal d * star U) * U).trace := by rw [Matrix.trace_mul_comm]
          _ = (diagonal d * (star U * U)).trace := by rw [Matrix.mul_assoc]
      _ = (diagonal d).trace := by rw [Unitary.coe_star_mul_self, Matrix.mul_one]
      _ = ∑ l : n, d l := Matrix.trace_diagonal d
  have himag (l : n) : (d l).im = η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
    have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)) =
        (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]
      simp
      ring
    have hi : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
    simp only [d, Complex.inv_im, hi, hn]
    ring
  rw [stieltjes, htrace]
  rw [Complex.mul_im]
  simp [Complex.im_sum, himag]

/-- **Paper's monotonicity used between (2.27) and (2.28).** If `0 < η ≤ ηTilde`, then
`η Im m(E+iη) ≤ ηTilde Im m(E+iηTilde)` for the finite-Hermitian Stieltjes transform
`m(z) = |n|⁻¹ Tr (H-z)⁻¹`. This is the upper-half-plane sign convention of `RBM.stieltjes`. -/
theorem stieltjes_eta_mul_im_mono {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ηTilde : ℝ)
    (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjes H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjes H (E + ηTilde * Complex.I)).im := by
  have hformula := stieltjes_im_eq_normalized_specWeight H hH E η hη
  have hformulaT := stieltjes_im_eq_normalized_specWeight H hH E ηTilde (by linarith)
  rw [hformula, hformulaT]
  have hterm (l : n) :
      η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) ≤
        ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
    let x := (hH.eigenvalues l - E) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hy : 0 < x + η ^ 2 := by positivity
    have hηT : 0 < ηTilde := lt_of_lt_of_le hη hηTilde
    have hyt : 0 < x + ηTilde ^ 2 := by positivity
    have hsquares : η ^ 2 ≤ ηTilde ^ 2 := by nlinarith [sq_nonneg (ηTilde - η)]
    have hfrac : η ^ 2 / (x + η ^ 2) ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := by
      rw [div_le_div_iff₀ hy hyt]
      have hdiff : 0 ≤ ηTilde ^ 2 - η ^ 2 := by linarith
      nlinarith [mul_nonneg hx hdiff]
    calc
      η * (η / (x + η ^ 2)) = η ^ 2 / (x + η ^ 2) := by field_simp
      _ ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := hfrac
      _ = ηTilde * (ηTilde / (x + ηTilde ^ 2)) := by field_simp
  have hc : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  calc
    η * ((Fintype.card n : ℝ)⁻¹ * ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
        = (Fintype.card n : ℝ)⁻¹ *
            ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
          calc
            η * ((Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
                = η * ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by rw [Finset.mul_sum]
            _ = ∑ l : n, η * ((Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by rw [Finset.mul_sum]
            _ = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = (Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
                      rw [Finset.mul_sum]
    _ ≤ (Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun l _ => hterm l) hc
    _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          calc
            (Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))
                = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      rw [Finset.mul_sum]
            _ = ∑ l : n, ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
                      rw [Finset.mul_sum, Finset.mul_sum]


/-- Consumer form for (2.28): an upper bound at the coarser scale transfers to every smaller
positive spectral scale. In applications `upperBound` is supplied by the local law at `ηTilde`. -/
theorem stieltjes_eta_mul_im_le_of_upper_bound {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ηTilde upperBound : ℝ)
    (hη : 0 < η) (hηTilde : η ≤ ηTilde)
    (hUpper : ηTilde * (stieltjes H (E + ηTilde * Complex.I)).im ≤ upperBound) :
    η * (stieltjes H (E + η * Complex.I)).im ≤ upperBound :=
  (stieltjes_eta_mul_im_mono H hH E η ηTilde hη hηTilde).trans hUpper

/-- The actual finite index type of a band matrix has cardinality `B.size N`. -/
theorem band_idx_card_eq_size {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ) :
    Fintype.card (B.Idx N) = B.size N := by
  simp [Band.Idx, Band.size]

/-- The band-index form applies to the matrix of size `B.size N = B.L N * B.W N`.
The sequence index `N` remains an index, not a substitute for the matrix dimension. -/
theorem stieltjes_eta_mul_im_mono_band {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω) (N : ℕ) (H : Matrix (B.Idx N) (B.Idx N) ℂ)
    (hH : H.IsHermitian) (E η ηTilde : ℝ) (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjes H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjes H (E + ηTilde * Complex.I)).im := by
  exact stieltjes_eta_mul_im_mono H hH E η ηTilde hη hηTilde

/-- A concrete nondegenerate finite-Hermitian instance of the scale hypotheses: the zero
`1 × 1` matrix at `E=1`, with `η=1/2` and `ηTilde=1`. -/
theorem stieltjes_eta_mul_im_mono_nondegenerate_example :
    (1 / 2 : ℝ) *
        (stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ) (1 + (1 / 2 : ℝ) * Complex.I)).im <
      1 * (stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ) (1 + (1 : ℝ) * Complex.I)).im := by
  let hH : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := Matrix.isHermitian_zero
  have hev : hH.eigenvalues 0 = 0 := by
    have h := (Matrix.IsHermitian.eigenvalues_eq_zero_iff (hA := hH)).2 rfl
    exact congrFun h 0
  have hstrict :
      (stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ)
        ((1 : ℝ) + (1 / 2 : ℝ) * Complex.I)).im = 2 / 5 := by
    rw [stieltjes_im_eq_normalized_specWeight (0 : Matrix (Fin 1) (Fin 1) ℂ) hH 1 (1 / 2)
      (by norm_num)]
    rw [Fin.sum_univ_one, hev]
    norm_num
  have hstrictT :
      (stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ) ((1 : ℝ) + (1 : ℝ) * Complex.I)).im = 1 / 2 := by
    rw [stieltjes_im_eq_normalized_specWeight (0 : Matrix (Fin 1) (Fin 1) ℂ) hH 1 1
      (by norm_num)]
    rw [Fin.sum_univ_one, hev]
    norm_num
  change (1 / 2 : ℝ) *
      (stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ) ((1 : ℝ) + (1 / 2 : ℝ) * Complex.I)).im <
    1 * (stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ) ((1 : ℝ) + (1 : ℝ) * Complex.I)).im
  rw [hstrict, hstrictT]
  norm_num

#print axioms stieltjes_im_eq_normalized_specWeight
#print axioms stieltjes_eta_mul_im_mono
#print axioms stieltjes_eta_mul_im_le_of_upper_bound
#print axioms stieltjes_eta_mul_im_mono_band
#print axioms stieltjes_eta_mul_im_mono_nondegenerate_example

end RBM
