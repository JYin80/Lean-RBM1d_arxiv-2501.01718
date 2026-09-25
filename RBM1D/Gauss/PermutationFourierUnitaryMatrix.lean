/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierCharacter
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.UnitaryGroup
import RBM1D.Defs.SemicircleQuantileReflection

/-!
# The positive-phase finite Fourier matrix

The row is the sample index `j` and the column is the Fourier mode `a`.
The phase agrees literally with `permutationFourierCharacter`, so the
`(a,b)` entry of a conjugated diagonal has mode `b-a`.
-/

open Matrix
namespace RBM.Gauss

theorem permutationFourierCharacter_zmod (W : ℕ) [NeZero W] (q j : Fin W) :
    permutationFourierCharacter W q j =
      ZMod.stdAddChar ((q.val * j.val : ℕ) : ZMod W) := by
  have h := ZMod.stdAddChar_coe (N := W) (q.val * j.val : ℤ)
  convert h.symm using 1
  · unfold permutationFourierCharacter
    push_cast
    congr 1
    ring
  · norm_cast

theorem permutationFourierCharacter_star (W : ℕ) [NeZero W] (q j : Fin W) :
    star (permutationFourierCharacter W q j) =
      ZMod.stdAddChar (-(q.val * j.val : ZMod W)) := by
  rw [permutationFourierCharacter_zmod]
  rw [AddChar.map_neg_eq_inv]
  simpa only [ZMod.stdAddChar_apply, Complex.star_def, Nat.cast_mul] using
    (Complex.inv_eq_conj
      (ZMod.toCircle ((q.val * j.val : ℕ) : ZMod W)).norm_coe).symm

theorem permutationFourierFin_sub_zmod (W : ℕ) [NeZero W] (a b : Fin W) :
    (((b - a : Fin W).val : ℕ) : ZMod W) = (b.val : ZMod W) - (a.val : ZMod W) := by
  rw [Fin.val_sub]
  simp
  abel

/-- Conjugating the row-`a` character gives exactly positive-phase mode `b-a`. -/
theorem permutationFourierCharacter_product (W : ℕ) [NeZero W] (a b j : Fin W) :
    permutationFourierCharacter W b j * star (permutationFourierCharacter W a j) =
      permutationFourierCharacter W (b - a) j := by
  rw [permutationFourierCharacter_zmod, permutationFourierCharacter_star,
    permutationFourierCharacter_zmod]
  simp only [Nat.cast_mul]
  rw [← AddChar.map_add_eq_mul]
  rw [permutationFourierFin_sub_zmod]
  congr 1
  ring

theorem permutationFourierCharacter_sum (W : ℕ) (hW : 1 ≤ W) (q : Fin W) :
    (∑ j : Fin W, permutationFourierCharacter W q j) =
      if q.val = 0 then (W : ℂ) else 0 := by
  split_ifs with hq
  · simp [permutationFourierCharacter, hq]
  · have hW2 : 2 ≤ W := by
      by_contra h
      have hW1 : W = 1 := by omega
      subst W
      have := q.isLt
      omega
    have hq0 : q ≠ (⟨0, by omega⟩ : Fin W) := by
      intro heq
      exact hq (congrArg Fin.val heq)
    exact permutationFourierCharacter_sum_zero W hW2 q hq0

/-- The complex scalar `1 / sqrt W` used to normalize the matrix. -/
noncomputable def permutationFourierNorm (W : ℕ) : ℂ := ((Real.sqrt (W : ℝ) : ℂ))⁻¹
/-- The normalized positive-phase Fourier matrix on `Fin W`. -/
noncomputable def permutationFourierMatrix (W : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  fun j a => permutationFourierNorm W * permutationFourierCharacter W a j

theorem permutationFourierNorm_star_mul (W : ℕ) (hW : 1 ≤ W) :
    star (permutationFourierNorm W) * permutationFourierNorm W = (W : ℂ)⁻¹ := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have hsq : (Real.sqrt (W : ℝ) : ℂ) ^ 2 = (W : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ (W : ℝ))
  simp only [permutationFourierNorm, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  calc
    (↑(Real.sqrt (W : ℝ)) : ℂ)⁻¹ * (↑(Real.sqrt (W : ℝ)) : ℂ)⁻¹ =
        ((↑(Real.sqrt (W : ℝ)) : ℂ) ^ 2)⁻¹ := by rw [pow_two, _root_.mul_inv_rev]
    _ = (W : ℂ)⁻¹ := by rw [hsq]

/-- Column orthogonality of the literal Fourier matrix. -/
theorem permutationFourierMatrix_conjTranspose_mul (W : ℕ) (hW : 1 ≤ W) :
    (permutationFourierMatrix W)ᴴ * permutationFourierMatrix W = 1 := by
  classical
  letI : NeZero W := ⟨by omega⟩
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  change (∑ j : Fin W,
    star (permutationFourierNorm W * permutationFourierCharacter W a j) *
      (permutationFourierNorm W * permutationFourierCharacter W b j)) =
    (1 : Matrix (Fin W) (Fin W) ℂ) a b
  calc
    _ = (star (permutationFourierNorm W) * permutationFourierNorm W) *
        ∑ j : Fin W, permutationFourierCharacter W (b - a) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← permutationFourierCharacter_product]
      simp only [star_mul]
      ring
    _ = (W : ℂ)⁻¹ * (if (b - a : Fin W).val = 0 then (W : ℂ) else 0) := by
      rw [permutationFourierNorm_star_mul W hW, permutationFourierCharacter_sum W hW]
    _ = (1 : Matrix (Fin W) (Fin W) ℂ) a b := by
      by_cases hab : a = b
      · subst b
        simp
      · have hval : (b - a : Fin W).val ≠ 0 := by
          intro h0
          have hz : b - a = (0 : Fin W) := Fin.ext h0
          exact hab (sub_eq_zero.mp hz).symm
        simp [hab, hval]

/-- Row orthogonality, hence two-sided unitarity. -/
theorem permutationFourierMatrix_mul_conjTranspose (W : ℕ) (hW : 1 ≤ W) :
    permutationFourierMatrix W * (permutationFourierMatrix W)ᴴ = 1 := by
  exact mul_eq_one_comm.mp (permutationFourierMatrix_conjTranspose_mul W hW)

/-- Exact diagonal-conjugation entry with positive-phase mode `b-a`. -/
theorem permutationFourierMatrix_diagonal_entry (W : ℕ) (hW : 1 ≤ W)
    (v : Fin W → ℂ) (a b : Fin W) :
    ((permutationFourierMatrix W)ᴴ * Matrix.diagonal v * permutationFourierMatrix W) a b =
      (W : ℂ)⁻¹ * ∑ j : Fin W,
        permutationFourierCharacter W (b - a) j * v j := by
  classical
  letI : NeZero W := ⟨by omega⟩
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.conjTranspose_apply]
  change star (permutationFourierNorm W * permutationFourierCharacter W a j) * v j *
    (permutationFourierNorm W * permutationFourierCharacter W b j) =
    (W : ℂ)⁻¹ * (permutationFourierCharacter W (b - a) j * v j)
  rw [← permutationFourierCharacter_product, ← permutationFourierNorm_star_mul W hW]
  simp only [star_mul]
  ring

/-- The actual two-point semicircle quantiles give a nonzero off-diagonal. -/
theorem permutationFourierMatrix_quantile_two_offdiag :
    ((permutationFourierMatrix 2)ᴴ *
      Matrix.diagonal (fun j : Fin 2 =>
        ((RBM.semicircleLambda 2 (by norm_num) j.val j.isLt : ℝ) : ℂ)) *
      permutationFourierMatrix 2) 0 1 ≠ 0 := by
  let lam : Fin 2 → ℝ := fun j =>
    RBM.semicircleLambda 2 (by norm_num) j.val j.isLt
  have hlt : lam 0 < lam 1 := RBM.semicircleQuantileReflection_witness_two.1
  have hne : ((lam 0 : ℂ) - (lam 1 : ℂ)) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt hlt))
  have hentry :
      ((permutationFourierMatrix 2)ᴴ * Matrix.diagonal (fun j : Fin 2 => (lam j : ℂ)) *
        permutationFourierMatrix 2) 0 1 = ((lam 0 : ℂ) - (lam 1 : ℂ)) / 2 := by
    rw [permutationFourierMatrix_diagonal_entry 2 (by norm_num)]
    norm_num [Fin.sum_univ_two, permutationFourierCharacter_two, lam]
    ring
  rw [hentry]
  exact div_ne_zero hne (by norm_num)

theorem permutationFourierMatrix_one_check :
    (permutationFourierMatrix 1)ᴴ * permutationFourierMatrix 1 = 1 ∧
      permutationFourierMatrix 1 * (permutationFourierMatrix 1)ᴴ = 1 :=
  ⟨permutationFourierMatrix_conjTranspose_mul 1 (by norm_num),
    permutationFourierMatrix_mul_conjTranspose 1 (by norm_num)⟩

/-- The one-cell semicircle midpoint is zero, so its Fourier block is zero. -/
theorem permutationFourierMatrix_quantile_one_check :
    ((permutationFourierMatrix 1)ᴴ *
      Matrix.diagonal (fun j : Fin 1 =>
        ((RBM.semicircleLambda 1 (by norm_num) j.val j.isLt : ℝ) : ℂ)) *
      permutationFourierMatrix 1) 0 0 = 0 := by
  have hzero : ∀ j : Fin 1,
      RBM.semicircleLambda 1 (by norm_num) j.val j.isLt = 0 := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa using RBM.semicircleLambda_odd_center 0
  rw [permutationFourierMatrix_diagonal_entry 1 (by norm_num)]
  have hz :
      ((RBM.semicircleLambda 1 (by norm_num) (0 : Fin 1).val (0 : Fin 1).isLt : ℝ) : ℂ)
        = 0 := by exact_mod_cast hzero 0
  simp only [Fin.sum_univ_one]
  rw [hz]
  ring

theorem permutationFourierMatrix_two_check :
    (permutationFourierMatrix 2)ᴴ * permutationFourierMatrix 2 = 1 ∧
      permutationFourierMatrix 2 * (permutationFourierMatrix 2)ᴴ = 1 :=
  ⟨permutationFourierMatrix_conjTranspose_mul 2 (by norm_num),
    permutationFourierMatrix_mul_conjTranspose 2 (by norm_num)⟩

#print axioms permutationFourierCharacter_zmod
#print axioms permutationFourierCharacter_star
#print axioms permutationFourierFin_sub_zmod
#print axioms permutationFourierCharacter_sum
#print axioms permutationFourierNorm_star_mul
#print axioms permutationFourierMatrix_diagonal_entry
#print axioms permutationFourierMatrix_quantile_two_offdiag
#print axioms permutationFourierMatrix_one_check
#print axioms permutationFourierMatrix_quantile_one_check
#print axioms permutationFourierMatrix_two_check
#print axioms permutationFourierCharacter_product
#print axioms permutationFourierMatrix_conjTranspose_mul
#print axioms permutationFourierMatrix_mul_conjTranspose

end RBM.Gauss
