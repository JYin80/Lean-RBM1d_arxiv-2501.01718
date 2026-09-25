/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.StieltjesEtaMonotone

/-!
# The finite-Hermitian spectral product and its collision split

The product of one-point Stieltjes imaginary parts expands over all eigenvalue
tuples. The injective tuples are the tuples occurring in `corrPairing`; the
remaining terms are the collision contribution.
-/

namespace RBM

/-- The unnormalized weight of an eigenvalue tuple in a product of Stieltjes
imaginary parts. -/
noncomputable def spectralProductWeight {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (k : ℕ)
    (E η : Fin k → ℝ) (f : Fin k → n) : ℝ :=
  ∏ i : Fin k, η i / ((hH.eigenvalues (f i) - E i) ^ 2 + (η i) ^ 2)

/-- Product spectral formula: the product of `k` imaginary parts is the normalized
sum over every eigenvalue tuple, including tuples with repeated indices. -/
theorem stieltjes_im_product_eq_normalized_spectral_sum {n : Type*} [Fintype n]
    [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (k : ℕ)
    (E η : Fin k → ℝ) (hη : ∀ i, 0 < η i) :
    (∏ i : Fin k, (stieltjes H (E i + η i * Complex.I)).im) =
      (Fintype.card n : ℝ) ^ (-k : ℤ) *
        ∑ f : Fin k → n, spectralProductWeight H hH k E η f := by
  classical
  have hformula (i : Fin k) :=
    stieltjes_im_eq_normalized_specWeight H hH (E i) (η i) (hη i)
  simp_rw [hformula]
  calc
    (∏ i : Fin k, (Fintype.card n : ℝ)⁻¹ *
        ∑ l : n, η i / ((hH.eigenvalues l - E i) ^ 2 + (η i) ^ 2)) =
      (∏ _i : Fin k, (Fintype.card n : ℝ)⁻¹) *
        ∏ i : Fin k, ∑ l : n,
          η i / ((hH.eigenvalues l - E i) ^ 2 + (η i) ^ 2) := by
            rw [Finset.prod_mul_distrib]
    _ = (Fintype.card n : ℝ) ^ (-k : ℤ) *
        ∑ f : Fin k → n, ∏ i : Fin k,
          η i / ((hH.eigenvalues (f i) - E i) ^ 2 + (η i) ^ 2) := by
            rw [Finset.prod_const, Fintype.prod_sum]
            simp [Finset.card_univ, Fintype.card_fin, zpow_neg, zpow_natCast, inv_pow]

/-- Sum of tuple weights over injective eigenvalue tuples. This is the summation
index used by the density-free `corrPairing` definition. -/
noncomputable def injectiveSpectralProductSum {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (k : ℕ) (E η : Fin k → ℝ) : ℝ :=
  ∑ f ∈ (Finset.univ : Finset (Fin k → n)).filter Function.Injective,
    spectralProductWeight H hH k E η f

/-- Sum of tuple weights over noninjective eigenvalue tuples, i.e. the collision
contribution omitted by the injective index. -/
noncomputable def collisionSpectralProductSum {n : Type*} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (hH : H.IsHermitian) (k : ℕ) (E η : Fin k → ℝ) : ℝ :=
  ∑ f ∈ (Finset.univ : Finset (Fin k → n)).filter (fun f => ¬ Function.Injective f),
    spectralProductWeight H hH k E η f

/-- Exact partition of the full spectral sum into injective and colliding tuples. -/
theorem spectralProductSum_eq_injective_add_collision {n : Type*} [Fintype n]
    [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (k : ℕ)
    (E η : Fin k → ℝ) :
    (∑ f : Fin k → n, spectralProductWeight H hH k E η f) =
      injectiveSpectralProductSum H hH k E η + collisionSpectralProductSum H hH k E η := by
  classical
  simp only [injectiveSpectralProductSum, collisionSpectralProductSum]
  symm
  exact Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun f : Fin k → n => Function.Injective f)
    (fun f => spectralProductWeight H hH k E η f)

/-- The normalized product formula with the two disjoint contributions displayed
separately. In particular, no factorial or normalization is absorbed into either sum. -/
theorem stieltjes_im_product_eq_injective_add_collision {n : Type*} [Fintype n]
    [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (k : ℕ)
    (E η : Fin k → ℝ) (hη : ∀ i, 0 < η i) :
    (∏ i : Fin k, (stieltjes H (E i + η i * Complex.I)).im) =
      (Fintype.card n : ℝ) ^ (-k : ℤ) *
        (injectiveSpectralProductSum H hH k E η +
          collisionSpectralProductSum H hH k E η) := by
  rw [stieltjes_im_product_eq_normalized_spectral_sum H hH k E η hη,
    spectralProductSum_eq_injective_add_collision]

/-- On the zero Hermitian `2 × 2` matrix, for two factors at zero energy and unit
broadening, both injective and collision contributions are strictly positive on the
same matrix sample. -/
theorem spectralProduct_injective_and_collision_positive_example :
    0 < injectiveSpectralProductSum (0 : Matrix (Fin 2) (Fin 2) ℂ)
      Matrix.isHermitian_zero 2 (fun _ => 0) (fun _ => 1) ∧
    0 < collisionSpectralProductSum (0 : Matrix (Fin 2) (Fin 2) ℂ)
      Matrix.isHermitian_zero 2 (fun _ => 0) (fun _ => 1) := by
  classical
  have hzero : ∀ i : Fin 2,
      (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian).eigenvalues i = 0 := by
    intro i
    have h := (Matrix.IsHermitian.eigenvalues_eq_zero_iff
      (hA := (Matrix.isHermitian_zero : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian))).2 rfl
    exact congrFun h i
  have hweight (f : Fin 2 → Fin 2) :
      0 < spectralProductWeight (0 : Matrix (Fin 2) (Fin 2) ℂ)
        Matrix.isHermitian_zero 2 (fun _ => 0) (fun _ => 1) f := by
    simp only [spectralProductWeight]
    apply Finset.prod_pos
    intro i hi
    rw [hzero]
    norm_num
  constructor
  · simp only [injectiveSpectralProductSum]
    apply Finset.sum_pos
    · intro f hf
      exact hweight f
    · exact ⟨(fun i : Fin 2 => i), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Function.injective_id⟩⟩
  · simp only [collisionSpectralProductSum]
    apply Finset.sum_pos
    · intro f hf
      exact hweight f
    · refine ⟨(fun _ : Fin 2 => (0 : Fin 2)), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩⟩
      intro hinj
      have h01 := hinj (a₁ := (0 : Fin 2)) (a₂ := (1 : Fin 2)) (by rfl)
      exact (by decide : (0 : Fin 2) ≠ 1) h01

#print axioms stieltjes_im_product_eq_normalized_spectral_sum
#print axioms spectralProductSum_eq_injective_add_collision
#print axioms stieltjes_im_product_eq_injective_add_collision
#print axioms spectralProduct_injective_and_collision_positive_example

end RBM
