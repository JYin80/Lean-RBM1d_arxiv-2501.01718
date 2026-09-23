/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierMean
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Finite nonzero Fourier characters

The canonical `Fin W` character has zero sum at every nonzero mode. This supplies
the weight hypothesis of the finite uniform-permutation mean theorem.
-/

namespace RBM.Gauss

/-- The Fourier character of mode `q` at the canonical representative `j`. -/
noncomputable def permutationFourierCharacter (W : ℕ) (q j : Fin W) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (q.val : ℂ) * (j.val : ℂ) / (W : ℂ))

/-- A nonzero mode has exactly zero total character weight. -/
theorem permutationFourierCharacter_sum_zero (W : ℕ) (hW : 2 ≤ W)
    (q : Fin W) (hq : q ≠ (⟨0, by omega⟩ : Fin W)) :
    (∑ j : Fin W, permutationFourierCharacter W q j) = 0 := by
  classical
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q.val : ℂ) / (W : ℂ))
  have hW0 : W ≠ 0 := by omega
  have hzW : z ^ W = 1 := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    have hroot := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := q.val * W) hW0).2
      ⟨q.val, by ring⟩
    convert hroot using 1 <;> push_cast <;> field_simp <;> ring
  have hz1 : z ≠ 1 := by
    intro h
    have hdiv : Complex.exp (2 * Real.pi * Complex.I * (q.val : ℂ) / (W : ℂ)) = 1 := by
      simpa [z] using h
    have hdiv' : W ∣ q.val :=
      (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := q.val) hW0).1 hdiv
    have hzero : q.val = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' q.isLt
    exact hq (Fin.ext hzero)
  have hchar (j : Fin W) : permutationFourierCharacter W q j = z ^ j.val := by
    dsimp [permutationFourierCharacter, z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : (∑ n ∈ Finset.range W, z ^ n) = 0 := by
    have hgeom : (∑ n ∈ Finset.range W, z ^ n) * (z - 1) = 0 := by
      rw [geom_sum_mul z W, hzW]
      simp
    rcases mul_eq_zero.mp hgeom with hs | hz
    · exact hs
    · exact False.elim (hz1 (sub_eq_zero.mp hz))
  calc
    (∑ j : Fin W, permutationFourierCharacter W q j) =
        ∑ j : Fin W, z ^ j.val := by
          apply Finset.sum_congr rfl
          intro j _
          exact hchar j
    _ = ∑ n ∈ Finset.range W, z ^ n :=
      Fin.sum_univ_eq_sum_range (fun n => z ^ n) W
    _ = 0 := hsum

/-- The exact `W⁻¹` normalized Fourier sum has zero uniform permutation mean
for each nonzero mode, for every complex table `x`. -/
theorem permutationFourierCharacter_mean_zero (W : ℕ) (hW : 2 ≤ W)
    (q : Fin W) (hq : q ≠ (⟨0, by omega⟩ : Fin W)) (x : Fin W → ℂ) :
    (∑ π : Equiv.Perm (Fin W),
        permutationFourierSum W x (permutationFourierCharacter W q) π) /
      (Fintype.card (Equiv.Perm (Fin W)) : ℂ) = 0 :=
  permutationFourierSum_mean_zero W hW x (permutationFourierCharacter W q)
    (permutationFourierCharacter_sum_zero W hW q hq)

/-- At `W = 2`, the unique nonzero mode is the nonconstant character `(1,-1)`. -/
theorem permutationFourierCharacter_two :
    permutationFourierCharacter 2 1 0 = 1 ∧
      permutationFourierCharacter 2 1 1 = -1 := by
  constructor
  · norm_num [permutationFourierCharacter]
  · norm_num [permutationFourierCharacter]
    rw [show (2 * Real.pi * Complex.I / 2 : ℂ) = Real.pi * Complex.I by ring,
      Complex.exp_pi_mul_I]

/-- The zero mode is constant, so its character sum is nonzero for `W ≥ 2`. -/
theorem permutationFourierCharacter_zero_mode (W : ℕ) (hW : 2 ≤ W) :
    (∑ j : Fin W, permutationFourierCharacter W ⟨0, by omega⟩ j) = (W : ℂ) ∧
      (W : ℂ) ≠ 0 := by
  constructor
  · simp [permutationFourierCharacter]
  · exact_mod_cast (by omega : W ≠ 0)

/-- There is no nonzero Fourier mode when `W = 1`. -/
theorem permutationFourierCharacter_no_nonzero_mode_one :
    ¬ ∃ q : Fin 1, q ≠ 0 := by
  rintro ⟨q, hq⟩
  exact hq (Fin.eq_zero q)

#print axioms permutationFourierCharacter
#print axioms permutationFourierCharacter_sum_zero
#print axioms permutationFourierCharacter_mean_zero
#print axioms permutationFourierCharacter_two
#print axioms permutationFourierCharacter_zero_mode
#print axioms permutationFourierCharacter_no_nonzero_mode_one

end RBM.Gauss
