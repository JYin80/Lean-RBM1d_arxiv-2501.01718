/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFiberCount

/-!
# Mean range across positive permutation-prefix fibers

This is an exact finite counting estimate for two next-image completion fibers.
The positive-cardinality premise ensures that both normalized sums are genuine
finite means. It is not a probability or concentration theorem.
-/

namespace RBM.Gauss

/-- The two finite Fourier means differ by at most the inherited `8/W` swap bound,
provided the fibers are nonempty. -/
theorem norm_permutationFourierSum_prefixFiber_mean_sub_le
    (W : ℕ) (hW : 2 ≤ W) (k : Fin W) (p : Fin W → Fin W)
    (a b : Fin W) (hab : a ≠ b)
    (ha : ∀ i, i < k → p i ≠ a) (hb : ∀ i, i < k → p i ≠ b)
    (hpos : 0 < Fintype.card (permutationPrefixFiber W k p a))
    (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) :
    ‖((∑ π : permutationPrefixFiber W k p a,
          permutationFourierSum W x χ π.1) /
        (Fintype.card (permutationPrefixFiber W k p a) : ℂ)) -
      ((∑ ρ : permutationPrefixFiber W k p b,
          permutationFourierSum W x χ ρ.1) /
        (Fintype.card (permutationPrefixFiber W k p b) : ℂ))‖ ≤
      8 / (W : ℝ) := by
  classical
  let A := permutationPrefixFiber W k p a
  let B := permutationPrefixFiber W k p b
  let n := Fintype.card A
  have hcard : Fintype.card A = Fintype.card B :=
    permutationPrefixFiber_card_eq W hW k p a b hab ha hb
  have hcardB : Fintype.card B = n := by simpa [A, B, n] using hcard.symm
  have htransport :
      (∑ π : A, permutationFourierSum W x χ (permutationCodomainSwap W a b π.1)) =
        ∑ ρ : B, permutationFourierSum W x χ ρ.1 := by
    simpa [A, B] using
      (permutationPrefixFiber_sum_codomainSwap W hW k p a b hab ha hb
        (fun π => permutationFourierSum W x χ π))
  have hsum :
      (∑ π : A, permutationFourierSum W x χ π.1) -
          ∑ ρ : B, permutationFourierSum W x χ ρ.1 =
        ∑ π : A, (permutationFourierSum W x χ π.1 -
          permutationFourierSum W x χ (permutationCodomainSwap W a b π.1)) := by
    calc
      _ = (∑ π : A, permutationFourierSum W x χ π.1) -
          ∑ π : A, permutationFourierSum W x χ
            (permutationCodomainSwap W a b π.1) := by rw [← htransport]
      _ = _ := by rw [← Finset.sum_sub_distrib]
  have hpoint (π : A) :
      ‖permutationFourierSum W x χ π.1 -
        permutationFourierSum W x χ (permutationCodomainSwap W a b π.1)‖ ≤
        8 / (W : ℝ) := by
    rw [norm_sub_rev]
    exact norm_permutationFourierSum_codomainSwap_le W hW x χ hx hχ π.1 a b
  have hnumer :
      ‖∑ π : A, (permutationFourierSum W x χ π.1 -
        permutationFourierSum W x χ (permutationCodomainSwap W a b π.1))‖ ≤
        (n : ℝ) * (8 / (W : ℝ)) := by
    calc
      _ ≤ ∑ π : A, ‖permutationFourierSum W x χ π.1 -
          permutationFourierSum W x χ (permutationCodomainSwap W a b π.1)‖ := norm_sum_le _ _
      _ ≤ ∑ _π : A, (8 / (W : ℝ)) := Finset.sum_le_sum fun π _ => hpoint π
      _ = (n : ℝ) * (8 / (W : ℝ)) := by simp [n, mul_comm]
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by simpa [A, n] using hpos)
  have hrewrite :
      ((∑ π : A, permutationFourierSum W x χ π.1) / (n : ℂ)) -
        ((∑ ρ : B, permutationFourierSum W x χ ρ.1) / (n : ℂ)) =
      (∑ π : A, (permutationFourierSum W x χ π.1 -
        permutationFourierSum W x χ (permutationCodomainSwap W a b π.1))) / (n : ℂ) := by
    rw [← hsum]
    rw [← sub_div]
  rw [show (Fintype.card A : ℂ) = (n : ℂ) by rfl,
    show (Fintype.card B : ℂ) = (n : ℂ) by exact_mod_cast hcardB]
  rw [hrewrite, norm_div, Complex.norm_natCast]
  have hdiv :
      ‖∑ π : A, (permutationFourierSum W x χ π.1 -
        permutationFourierSum W x χ (permutationCodomainSwap W a b π.1))‖ /
          (n : ℝ) ≤ 8 / (W : ℝ) := by
    rw [div_le_iff₀ hnreal]
    simpa [mul_comm] using hnumer
  exact hdiv

/-- Concrete nonempty, admissible two-point data for the endpoint case `W=2`.
The fiber cards are positive and the prescribed tables are the sharp pointwise
swap example from T676. -/
theorem permutationPrefixFiber_meanRange_two_witness :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 0) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 1) ∧
      x 0 = 2 ∧ x 1 = -2 ∧ χ 0 = 1 ∧ χ 1 = -1 := by
  classical
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 else -2
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  rcases permutationPrefixFiber_two_card_pos with ⟨hpos0, hpos1⟩
  refine ⟨x, χ, ?_, ?_, hpos0, hpos1, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x]
  · intro i
    fin_cases i <;> norm_num [χ]
  · norm_num [x]
  · norm_num [x]
  · norm_num [χ]
  · norm_num [χ]

#print axioms norm_permutationFourierSum_prefixFiber_mean_sub_le
#print axioms permutationPrefixFiber_meanRange_two_witness

end RBM.Gauss
