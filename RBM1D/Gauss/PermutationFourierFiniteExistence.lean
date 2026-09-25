/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierComplexConcentration
import RBM1D.Gauss.PermutationFourierCharacter

/-!
# Finite simultaneous Fourier bounds for one permutation

For a bounded time-indexed table, the accepted one-mode complex tail and a
finite union bound produce one permutation that works at every time and every
nonzero canonical Fourier mode.
-/

open MeasureTheory

namespace RBM.Gauss

theorem permutationFourierCharacter_norm_eq_one (W : ℕ) (q j : Fin W) :
    ‖permutationFourierCharacter W q j‖ = 1 := by
  rw [permutationFourierCharacter, Complex.norm_exp]
  have hre :
      (2 * Real.pi * Complex.I * (q.val : ℂ) * (j.val : ℂ) / (W : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.div_re]
  rw [hre, Real.exp_zero]

noncomputable def permutationFourierBadSet (W : ℕ)
    (x : Fin W → ℂ) (q : Fin W) (r : ℝ) : Set (PermΩ W) :=
  {π | r ≤ ‖permutationFourierSum W x (permutationFourierCharacter W q) π‖}

/-- One permutation simultaneously makes all nonzero Fourier modes smaller
than r at all T times, provided the sum of the accepted one-mode tail
bounds is strictly below one. -/
theorem exists_permutationFourierSum_norm_lt_of_union_bound
    (W T : ℕ) (hW : 2 ≤ W) (_hT : 1 ≤ T)
    (x : Fin T → Fin W → ℂ) (hx : ∀ t j, ‖x t j‖ ≤ 2)
    (r : ℝ) (hr : 0 < r)
    (hprem : 4 * ((T * (W - 1) : ℕ) : ℝ) *
      Real.exp (-(W : ℝ) * r ^ 2 / 256) < 1) :
    ∃ π : PermΩ W, ∀ t : Fin T, ∀ q : Fin W,
      q ≠ (⟨0, by omega⟩ : Fin W) →
        ‖permutationFourierSum W (x t) (permutationFourierCharacter W q) π‖ < r := by
  classical
  let q0 : Fin W := ⟨0, by omega⟩
  let I : Finset (Fin T × Fin W) :=
    Finset.univ.product ((Finset.univ : Finset (Fin W)).erase q0)
  let bad : Fin T × Fin W → Set (PermΩ W) :=
    fun p => permutationFourierBadSet W (x p.1) p.2 r
  let badUnion : Set (PermΩ W) := ⋃ p ∈ I, bad p
  have hq0 : q0 ∈ (Finset.univ : Finset (Fin W)) := Finset.mem_univ _
  have hIcard : I.card = T * (W - 1) := by
    simp [I, Finset.card_erase_of_mem hq0, Fintype.card_fin]
  have hbad (p : Fin T × Fin W) (hp : p ∈ I) :
      (uniformPerm W).real (bad p) ≤
        4 * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
    have hp' : p.2 ∈ (Finset.univ : Finset (Fin W)).erase q0 := by
      have hp'' : p ∈ Finset.univ.product
          ((Finset.univ : Finset (Fin W)).erase q0) := by simpa [I] using hp
      exact (Finset.mem_product.mp hp'').2
    have hq : p.2 ≠ q0 := (Finset.mem_erase.mp hp').1
    have htail := uniformPerm_permutationFourierSum_zeroCharacter_complex_tail
      W hW (x p.1) (permutationFourierCharacter W p.2)
      (fun j => hx p.1 j)
      (fun j => by rw [permutationFourierCharacter_norm_eq_one])
      (permutationFourierCharacter_sum_zero W hW p.2 (by simpa [q0] using hq))
      r hr.le
    simpa [bad, permutationFourierBadSet] using htail
  have hsum :
      (∑ p ∈ I, (uniformPerm W).real (bad p)) < 1 := by
    calc
      _ ≤ ∑ _p ∈ I, 4 * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hbad p hp
      _ = 4 * (I.card : ℝ) * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = 4 * ((T * (W - 1) : ℕ) : ℝ) *
          Real.exp (-(W : ℝ) * r ^ 2 / 256) := by rw [hIcard]
      _ < 1 := hprem
  have hmeasure : (uniformPerm W).real badUnion < 1 := by
    calc
      (uniformPerm W).real badUnion ≤ ∑ p ∈ I, (uniformPerm W).real (bad p) := by
        simpa [badUnion] using
          (measureReal_biUnion_finset_le (μ := uniformPerm W) I bad)
      _ < 1 := hsum
  have hnotall : ¬ ∀ π : PermΩ W, π ∈ badUnion := by
    intro hall
    have huniv : (Set.univ : Set (PermΩ W)) ⊆ badUnion := by
      intro π _
      exact hall π
    have h1 : (1 : ℝ) ≤ (uniformPerm W).real badUnion := by
      have hmono :
          (uniformPerm W).real Set.univ ≤ (uniformPerm W).real badUnion :=
        measureReal_mono huniv (measure_ne_top (uniformPerm W) badUnion)
      simpa [probReal_univ] using hmono
    linarith
  obtain ⟨π, hπ⟩ := not_forall.mp hnotall
  refine ⟨π, ?_⟩
  intro t q hq
  have hp : (t, q) ∈ I := by
    simp [I, q0, hq]
  have hout : π ∉ bad (t, q) := by
    intro hbadπ
    apply hπ
    rw [Set.mem_iUnion]
    refine ⟨(t, q), ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hp, hbadπ⟩
  have hnot : ¬ r ≤
      ‖permutationFourierSum W (x t) (permutationFourierCharacter W q) π‖ := by
    simpa [bad, permutationFourierBadSet] using hout
  exact lt_of_not_ge hnot

/-- The strict union premise has an explicit nonconstant width-512 witness.
At the identity permutation the mode-one Fourier sum equals the threshold 2,
so the corresponding weak bad event is genuinely nonempty. -/
 theorem permutationFourierFiniteExistence_nonempty_bad_witness :
    ∃ x : Fin 1 → Fin 8192 → ℂ, ∃ r : ℝ,
      0 < r ∧
      (∀ t j, ‖x t j‖ ≤ 2) ∧
      (∃ i j : Fin 8192, x 0 i ≠ x 0 j) ∧
      4 * ((1 * (8192 - 1) : ℕ) : ℝ) * Real.exp (-(8192 : ℝ) * r ^ 2 / 256) < 1 ∧
      ∃ q : Fin 8192, q ≠ (⟨0, by omega⟩ : Fin 8192) ∧
        (Equiv.refl (Fin 8192) : PermΩ 8192) ∈
          permutationFourierBadSet 8192 (x 0) q r := by
  classical
  let q : Fin 8192 := ⟨1, by omega⟩
  let χ : Fin 8192 → ℂ := permutationFourierCharacter 8192 q
  let x : Fin 1 → Fin 8192 → ℂ := fun _ j => 2 * star (χ j)
  have hχnorm (j : Fin 8192) : ‖χ j‖ = 1 := by
    exact permutationFourierCharacter_norm_eq_one 8192 q j
  have hbound (t : Fin 1) (j : Fin 8192) : ‖x t j‖ ≤ 2 := by
    simp only [x, norm_mul, Complex.norm_ofNat, norm_star, hχnorm]
    norm_num
  have hsum : (∑ j : Fin 8192, χ j) = 0 := by
    exact permutationFourierCharacter_sum_zero 8192 (by omega) q (by decide)
  have hzero : χ 0 = 1 := by
    norm_num [χ, permutationFourierCharacter]
  have hnonconstant : ∃ i j : Fin 8192, x 0 i ≠ x 0 j := by
    by_contra h
    push_neg at h
    have hconst : ∀ j : Fin 8192, χ j = χ 0 := by
      intro j
      have hxj := h j 0
      have hxj' : 2 * star (χ j) = 2 * star (χ 0) := by simpa [x] using hxj
      have hstar : star (χ j) = star (χ 0) :=
        mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hxj'
      exact star_injective hstar
    have hsum' : (∑ j : Fin 8192, χ j) = 8192 := by
      calc
        _ = ∑ _j : Fin 8192, χ 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact hconst j
        _ = 8192 := by simp [hzero]
    norm_num [hsum] at hsum'
  have hidentity :
      permutationFourierSum 8192 (x 0) χ (Equiv.refl (Fin 8192)) = 2 := by
    rw [permutationFourierSum]
    have hterm (j : Fin 8192) :
      χ j * x 0 ((Equiv.refl (Fin 8192)) j) = 2 := by
      simp only [Equiv.refl_apply, x]
      have hnormsq : χ j * star (χ j) = 1 := by
        calc
          χ j * star (χ j) = (‖χ j‖ : ℝ) ^ 2 := by
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
            push_cast
            ring
          _ = 1 := by rw [hχnorm j]; norm_num
      calc
        χ j * (2 * star (χ j)) = 2 * (χ j * star (χ j)) := by ring
        _ = 2 := by rw [hnormsq]; norm_num
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  refine ⟨x, 1, by norm_num, hbound, hnonconstant, ?_, q, by decide, ?_⟩
  · have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have he32 : (2 : ℝ) ^ 32 ≤ Real.exp 32 := by
      calc
        (2 : ℝ) ^ 32 ≤ Real.exp 1 ^ 32 :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 32
        _ = Real.exp 32 := by
          rw [show (32 : ℝ) = (32 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    have hlarge : (4 : ℝ) * 8191 < Real.exp 32 := by
      have : (4 : ℝ) * 8191 < (2 : ℝ) ^ 32 := by norm_num
      exact this.trans_le he32
    have hexp : Real.exp (-32) = (Real.exp 32)⁻¹ := by
      exact Real.exp_neg 32
    rw [show (-(8192 : ℝ) * (1 : ℝ) ^ 2 / 256) = -32 by norm_num, hexp]
    have hpos : 0 < Real.exp 32 := Real.exp_pos _
    rw [show ((1 * (8192 - 1) : ℕ) : ℝ) = 8191 by norm_num]
    exact (div_lt_one hpos).2 hlarge
  · change 1 ≤ ‖permutationFourierSum 8192 (x 0)
      (permutationFourierCharacter 8192 q) (Equiv.refl (Fin 8192))‖
    rw [hidentity]
    norm_num

#print axioms permutationFourierCharacter_norm_eq_one
#print axioms exists_permutationFourierSum_norm_lt_of_union_bound
#print axioms permutationFourierFiniteExistence_nonempty_bad_witness

end RBM.Gauss
