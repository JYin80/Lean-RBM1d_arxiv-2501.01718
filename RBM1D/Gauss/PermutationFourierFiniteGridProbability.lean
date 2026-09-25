/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierFiniteExistence

/-!
# Probability of simultaneous finite-grid Fourier bounds

For a finite time-indexed table, the accepted one-mode tail and an exact
finite union bound give a lower bound on the uniform-permutation probability
that every time node and every nonzero canonical mode is strictly below the
threshold. This is a finite-permutation statement only.
-/

open MeasureTheory

namespace RBM.Gauss

/-- The event that one permutation obeys every strict nonzero-mode Fourier
bound on the finite time grid. -/
def permutationFourierGridGoodSet (W T : ℕ) (hW : 2 ≤ W)
    (x : Fin T → Fin W → ℂ) (r : ℝ) : Set (PermΩ W) :=
  {π | ∀ t : Fin T, ∀ q : Fin W,
    q ≠ (⟨0, by omega⟩ : Fin W) →
      ‖permutationFourierSum W (x t) (permutationFourierCharacter W q) π‖ < r}

/-- The finite union of weak bad events; weak inequality is the exact
complement of the strict good event. -/
def permutationFourierGridBadUnion (W T : ℕ) (hW : 2 ≤ W)
    (x : Fin T → Fin W → ℂ) (r : ℝ) : Set (PermΩ W) :=
  ⋃ p ∈ (Finset.univ : Finset (Fin T)).product
      ((Finset.univ : Finset (Fin W)).erase (⟨0, by omega⟩ : Fin W)),
    permutationFourierBadSet W (x p.1) p.2 r

theorem permutationFourierGridGoodSet_measurable
    (W T : ℕ) (hW : 2 ≤ W) (x : Fin T → Fin W → ℂ) (r : ℝ) :
    MeasurableSet (permutationFourierGridGoodSet W T hW x r) := by
  exact MeasurableSpace.measurableSet_top

theorem permutationFourierGridBadUnion_measurable
    (W T : ℕ) (hW : 2 ≤ W) (x : Fin T → Fin W → ℂ) (r : ℝ) :
    MeasurableSet (permutationFourierGridBadUnion W T hW x r) := by
  exact MeasurableSpace.measurableSet_top

/-- The good set is exactly the complement of the union of weak bad events.
In particular, equality at the threshold belongs to the bad event. -/
theorem permutationFourierGridGoodSet_eq_compl_badUnion
    (W T : ℕ) (hW : 2 ≤ W) (x : Fin T → Fin W → ℂ) (r : ℝ) :
    permutationFourierGridGoodSet W T hW x r =
      (permutationFourierGridBadUnion W T hW x r)ᶜ := by
  classical
  ext π
  constructor
  · intro hg hb
    rcases Set.mem_iUnion.mp hb with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpI, hbad⟩
    have hp' : p.2 ∈ (Finset.univ : Finset (Fin W)).erase
        (⟨0, by omega⟩ : Fin W) := (Finset.mem_product.mp hpI).2
    have hq : p.2 ≠ (⟨0, by omega⟩ : Fin W) :=
      (Finset.mem_erase.mp hp').1
    exact (not_lt_of_ge hbad) (hg p.1 p.2 hq)
  · intro hnot t q hq
    apply lt_of_not_ge
    intro hbad
    apply hnot
    refine Set.mem_iUnion.mpr ⟨(t, q), Set.mem_iUnion.mpr ⟨?_, hbad⟩⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hq, Finset.mem_univ _⟩⟩

/-- Exact cardinality of the time/mode index set used in the union bound. -/
theorem permutationFourierGridIndexSet_card
    (W T : ℕ) (hW : 2 ≤ W) :
    ((Finset.univ : Finset (Fin T)).product
      ((Finset.univ : Finset (Fin W)).erase (⟨0, by omega⟩ : Fin W))).card =
      T * (W - 1) := by
  have hq0 : (⟨0, by omega⟩ : Fin W) ∈ (Finset.univ : Finset (Fin W)) :=
    Finset.mem_univ _
  simp [Finset.card_product, Finset.card_erase_of_mem hq0, Fintype.card_fin]

/-- Under the exact uniform measure on all `W!` permutations, the probability
of the simultaneous strict event is at least
`1 - 4 T (W-1) exp(-W r²/256)`. -/
theorem uniformPerm_permutationFourierGridGoodSet_prob_lower_bound
    (W T : ℕ) (hW : 2 ≤ W) (_hT : 1 ≤ T)
    (x : Fin T → Fin W → ℂ) (hx : ∀ t j, ‖x t j‖ ≤ 2)
    (r : ℝ) (hr : 0 < r) :
    1 - 4 * ((T * (W - 1) : ℕ) : ℝ) *
        Real.exp (-(W : ℝ) * r ^ 2 / 256) ≤
      (uniformPerm W).real (permutationFourierGridGoodSet W T hW x r) := by
  classical
  let q0 : Fin W := ⟨0, by omega⟩
  let I : Finset (Fin T × Fin W) :=
    (Finset.univ : Finset (Fin T)).product
      ((Finset.univ : Finset (Fin W)).erase q0)
  let bad : Fin T × Fin W → Set (PermΩ W) :=
    fun p => permutationFourierBadSet W (x p.1) p.2 r
  let badUnion : Set (PermΩ W) := ⋃ p ∈ I, bad p
  have hq0 : q0 ∈ (Finset.univ : Finset (Fin W)) := Finset.mem_univ _
  have hcard : I.card = T * (W - 1) := by
    simp [I, Finset.card_product, Finset.card_erase_of_mem hq0, Fintype.card_fin]
  have hbad (p : Fin T × Fin W) (hp : p ∈ I) :
      (uniformPerm W).real (bad p) ≤
        4 * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
    have hp' : p.2 ∈ (Finset.univ : Finset (Fin W)).erase q0 := by
      have hp'' : p ∈ (Finset.univ : Finset (Fin T)).product
          ((Finset.univ : Finset (Fin W)).erase q0) := by
        simpa [I] using hp
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
      (∑ p ∈ I, (uniformPerm W).real (bad p)) ≤
        4 * ((T * (W - 1) : ℕ) : ℝ) *
          Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
    calc
      _ ≤ ∑ _p ∈ I, 4 * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hbad p hp
      _ = 4 * (I.card : ℝ) * Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = 4 * ((T * (W - 1) : ℕ) : ℝ) *
          Real.exp (-(W : ℝ) * r ^ 2 / 256) := by rw [hcard]
  have hbadbound : (uniformPerm W).real badUnion ≤
      4 * ((T * (W - 1) : ℕ) : ℝ) *
        Real.exp (-(W : ℝ) * r ^ 2 / 256) := by
    calc
      (uniformPerm W).real badUnion ≤
          ∑ p ∈ I, (uniformPerm W).real (bad p) := by
        simpa [badUnion] using
          (measureReal_biUnion_finset_le (μ := uniformPerm W) I bad)
      _ ≤ 4 * ((T * (W - 1) : ℕ) : ℝ) *
          Real.exp (-(W : ℝ) * r ^ 2 / 256) := hsum
  have hUnion : badUnion = permutationFourierGridBadUnion W T hW x r := by
    simp [badUnion, bad, I, permutationFourierGridBadUnion, q0]
  have hgood : permutationFourierGridGoodSet W T hW x r = badUnionᶜ := by
    rw [permutationFourierGridGoodSet_eq_compl_badUnion W T hW, hUnion]
  rw [hgood, probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top :
        MeasurableSet badUnion)]
  linarith

/-- A nonconstant `W=2` table gives a nonempty strict-good event at threshold
3 and a nonempty weak-bad event at threshold 2. Both contain the identity
permutation with positive uniform mass. -/
theorem permutationFourierGridProbability_two_nonvacuous_witness :
    ∃ x : Fin 1 → Fin 2 → ℂ,
      (∃ i j : Fin 2, x 0 i ≠ x 0 j) ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ∈
        permutationFourierGridGoodSet 2 1 (by omega) x 3 ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ∈
        permutationFourierBadSet 2 (x 0) (⟨1, by omega⟩ : Fin 2) 2 ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} := by
  classical
  let x : Fin 1 → Fin 2 → ℂ := fun _ j => if j.val = 0 then 2 else -2
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    norm_num [x]
  · intro t q hq
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    have hq : q = ⟨1, by omega⟩ := by
      fin_cases q <;> simp_all
    subst q
    have hval : permutationFourierSum 2 (x 0)
        (permutationFourierCharacter 2 ⟨1, by omega⟩)
        (Equiv.refl (Fin 2)) = 2 := by
      have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 2) = -1 := by
        have harg : 2 * (Real.pi : ℂ) * Complex.I / 2 = (Real.pi : ℂ) * Complex.I := by ring
        rw [harg, Complex.exp_pi_mul_I]
      norm_num [permutationFourierSum, permutationFourierCharacter, x,
        Fin.sum_univ_two, hexp]
    rw [hval]
    norm_num
  · change 2 ≤ ‖permutationFourierSum 2 (x 0)
      (permutationFourierCharacter 2 ⟨1, by omega⟩)
      (Equiv.refl (Fin 2))‖
    have hval : permutationFourierSum 2 (x 0)
        (permutationFourierCharacter 2 ⟨1, by omega⟩)
        (Equiv.refl (Fin 2)) = 2 := by
      have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 2) = -1 := by
        have harg : 2 * (Real.pi : ℂ) * Complex.I / 2 = (Real.pi : ℂ) * Complex.I := by ring
        rw [harg, Complex.exp_pi_mul_I]
      norm_num [permutationFourierSum, permutationFourierCharacter, x,
        Fin.sum_univ_two, hexp]
    rw [hval]
    norm_num
  · rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    norm_num [Fintype.card_perm]

#print axioms permutationFourierGridGoodSet_eq_compl_badUnion
#print axioms uniformPerm_permutationFourierGridGoodSet_prob_lower_bound
#print axioms permutationFourierGridProbability_two_nonvacuous_witness

end RBM.Gauss
