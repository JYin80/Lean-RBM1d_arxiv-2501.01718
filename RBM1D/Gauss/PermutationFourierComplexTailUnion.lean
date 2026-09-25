/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
# Finite complex event bridge for uniform permutations

This module converts four signed scalar coordinate tail bounds into a bound
for a complex norm event. It is a deterministic finite-space bridge; it does
not supply any scalar tail estimate or Gaussian local law. It is stated for
every `W`, including `W=0` and `W=1`: those permutation spaces are singletons,
and the bridge has no division by `W` or nontrivial reveal assumption.
-/

open MeasureTheory

namespace RBM.Gauss

/-- The four signed real-coordinate events at threshold `s`. -/
def complexCoordEvents (W : ℕ) (s : ℝ) (Z : PermΩ W → ℂ) :
    Set (PermΩ W) × Set (PermΩ W) × Set (PermΩ W) × Set (PermΩ W) :=
  ({π | s ≤ (Z π).re}, {π | s ≤ -(Z π).re},
    {π | s ≤ (Z π).im}, {π | s ≤ -(Z π).im})

/-- The norm event and all four coordinate events are measurable in the
discrete finite permutation sample space. -/
theorem uniformPerm_complexCoordEvents_measurable
    (W : ℕ) (Z : PermΩ W → ℂ) (r : ℝ) :
    MeasurableSet {π | r ≤ ‖Z π‖} ∧
      let (A, B, C, D) := complexCoordEvents W (r / Real.sqrt 2) Z
      MeasurableSet A ∧ MeasurableSet B ∧ MeasurableSet C ∧ MeasurableSet D := by
  dsimp [complexCoordEvents]
  exact ⟨MeasurableSpace.measurableSet_top, MeasurableSpace.measurableSet_top,
    MeasurableSpace.measurableSet_top, MeasurableSpace.measurableSet_top,
    MeasurableSpace.measurableSet_top⟩

/-- The complex norm event is covered by the four signed coordinate events
at scale `r / √2`. -/
theorem complexNormEvent_subset_signedCoordinates
    (W : ℕ) (Z : PermΩ W → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    {π | r ≤ ‖Z π‖} ⊆
      let (A, B, C, D) := complexCoordEvents W (r / Real.sqrt 2) Z
      (A ∪ B) ∪ (C ∪ D) := by
  intro π hπ
  dsimp [complexCoordEvents]
  have hs : 0 ≤ r / Real.sqrt 2 := by positivity
  have hscale : 2 * (r / Real.sqrt 2) ^ 2 = r ^ 2 := by
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, hsqrt]
    field_simp
  have hcoords : r / Real.sqrt 2 ≤ |(Z π).re| ∨
      r / Real.sqrt 2 ≤ |(Z π).im| := by
    by_contra h
    push_neg at h
    have hnormSq : ‖Z π‖ ^ 2 = (Z π).re ^ 2 + (Z π).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hreal : (Z π).re ^ 2 < (r / Real.sqrt 2) ^ 2 := by
      calc
        (Z π).re ^ 2 = |(Z π).re| ^ 2 := (sq_abs _).symm
        _ < (r / Real.sqrt 2) ^ 2 := by
          have hspos : 0 < r / Real.sqrt 2 := lt_of_le_of_lt (abs_nonneg _) h.1
          have hsum : 0 < r / Real.sqrt 2 + |(Z π).re| := by positivity
          have hprod : 0 < (r / Real.sqrt 2 - |(Z π).re|) *
              (r / Real.sqrt 2 + |(Z π).re|) :=
            mul_pos (sub_pos.mpr h.1) hsum
          nlinarith [hprod]
    have himag : (Z π).im ^ 2 < (r / Real.sqrt 2) ^ 2 := by
      calc
        (Z π).im ^ 2 = |(Z π).im| ^ 2 := (sq_abs _).symm
        _ < (r / Real.sqrt 2) ^ 2 := by
          have hspos : 0 < r / Real.sqrt 2 := lt_of_le_of_lt (abs_nonneg _) h.2
          have hsum : 0 < r / Real.sqrt 2 + |(Z π).im| := by positivity
          have hprod : 0 < (r / Real.sqrt 2 - |(Z π).im|) *
              (r / Real.sqrt 2 + |(Z π).im|) :=
            mul_pos (sub_pos.mpr h.2) hsum
          nlinarith [hprod]
    have hnorm : ‖Z π‖ ^ 2 < r ^ 2 := by nlinarith
    have hnormnonneg : 0 ≤ ‖Z π‖ := norm_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ) (add_nonneg hnormnonneg hr)]
  rcases hcoords with hre | him
  · rcases le_total 0 (Z π).re with hpos | hneg
    · left
      left
      simp only [Set.mem_setOf_eq]
      simpa [abs_of_nonneg hpos] using hre
    · left
      right
      simp only [Set.mem_setOf_eq]
      have habs : |(Z π).re| = - (Z π).re := abs_of_nonpos hneg
      simpa [habs] using hre
  · rcases le_total 0 (Z π).im with hpos | hneg
    · right
      left
      simp only [Set.mem_setOf_eq]
      simpa [abs_of_nonneg hpos] using him
    · right
      right
      simp only [Set.mem_setOf_eq]
      have habs : |(Z π).im| = - (Z π).im := abs_of_nonpos hneg
      simpa [habs] using him

/-- If each signed coordinate event has measure at most `E`, the complex
norm event has measure at most `4E`. All events are measurable because the
permutation sample space has the discrete finite sigma algebra. -/
theorem uniformPerm_complexNorm_tail_of_signedCoordinate_tails
    (W : ℕ) (Z : PermΩ W → ℂ) (r E : ℝ) (hr : 0 ≤ r)
    (hRe : (uniformPerm W).real {π | r / Real.sqrt 2 ≤ (Z π).re} ≤ E)
    (hNegRe : (uniformPerm W).real {π | r / Real.sqrt 2 ≤ -(Z π).re} ≤ E)
    (hIm : (uniformPerm W).real {π | r / Real.sqrt 2 ≤ (Z π).im} ≤ E)
    (hNegIm : (uniformPerm W).real {π | r / Real.sqrt 2 ≤ -(Z π).im} ≤ E) :
    (uniformPerm W).real {π | r ≤ ‖Z π‖} ≤ 4 * E := by
  let A : Set (PermΩ W) := {π | r / Real.sqrt 2 ≤ (Z π).re}
  let B : Set (PermΩ W) := {π | r / Real.sqrt 2 ≤ -(Z π).re}
  let C : Set (PermΩ W) := {π | r / Real.sqrt 2 ≤ (Z π).im}
  let D : Set (PermΩ W) := {π | r / Real.sqrt 2 ≤ -(Z π).im}
  have hsub : {π | r ≤ ‖Z π‖} ⊆ (A ∪ B) ∪ (C ∪ D) :=
    complexNormEvent_subset_signedCoordinates W Z r hr
  calc
    (uniformPerm W).real {π | r ≤ ‖Z π‖} ≤
        (uniformPerm W).real ((A ∪ B) ∪ (C ∪ D)) := measureReal_mono hsub
    _ ≤ (uniformPerm W).real (A ∪ B) + (uniformPerm W).real (C ∪ D) :=
      measureReal_union_le _ _
    _ ≤ ((uniformPerm W).real A + (uniformPerm W).real B) +
        ((uniformPerm W).real C + (uniformPerm W).real D) :=
      add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)
    _ ≤ 4 * E := by
      change (uniformPerm W).real A ≤ E at hRe
      change (uniformPerm W).real B ≤ E at hNegRe
      change (uniformPerm W).real C ≤ E at hIm
      change (uniformPerm W).real D ≤ E at hNegIm
      linarith

/-- A nonconstant width-two example: identity and swap have values `2` and
`-2`, each with positive uniform mass; for `r=1`, all four signed event
probabilities are at most `E=1/2`. -/
private theorem permFinTwo_eq_refl_of_apply_zero_eq_zero
    (σ : PermΩ 2) (h : σ 0 = 0) : σ = Equiv.refl (Fin 2) := by
  apply Equiv.Perm.ext
  intro i
  fin_cases i
  · exact h
  · have hne : σ 1 ≠ (0 : Fin 2) := by
      intro h10
      have hneq : (0 : Fin 2) ≠ 1 := by decide
      exact hneq (σ.injective (h.trans h10.symm))
    rcases Fin.eq_zero_or_eq_succ (σ 1) with hzero | ⟨j, hj⟩
    · exact (hne hzero).elim
    · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simpa using hj

private theorem permFinTwo_eq_swap_of_apply_zero_eq_one
    (σ : PermΩ 2) (h : σ 0 = 1) : σ = Equiv.swap (0 : Fin 2) 1 := by
  apply Equiv.Perm.ext
  intro i
  fin_cases i
  · exact h
  · have hne : σ 1 ≠ (1 : Fin 2) := by
      intro h11
      have hneq : (0 : Fin 2) ≠ 1 := by decide
      exact hneq (σ.injective (h.trans h11.symm))
    rcases Fin.eq_zero_or_eq_succ (σ 1) with hzero | ⟨j, hj⟩
    · exact hzero
    · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact (hne (by simpa using hj)).elim

theorem uniformPerm_complexNorm_tail_two_witness :
    ∃ Z : PermΩ 2 → ℂ,
      Z (Equiv.refl (Fin 2)) = 2 ∧
      Z (Equiv.swap 0 1) = -2 ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ≠ Equiv.swap 0 1 ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} ∧
      (uniformPerm 2).real {π | (1 : ℝ) / Real.sqrt 2 ≤ (Z π).re} ≤ 1 / 2 ∧
      (uniformPerm 2).real {π | (1 : ℝ) / Real.sqrt 2 ≤ -(Z π).re} ≤ 1 / 2 ∧
      (uniformPerm 2).real {π | (1 : ℝ) / Real.sqrt 2 ≤ (Z π).im} ≤ 1 / 2 ∧
      (uniformPerm 2).real {π | (1 : ℝ) / Real.sqrt 2 ≤ -(Z π).im} ≤ 1 / 2 := by
  classical
  let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
  let swapPerm : PermΩ 2 := Equiv.swap 0 1
  let Z : PermΩ 2 → ℂ := fun π => if π = idPerm then 2 else -2
  have hIdMass : uniformPerm 2 {idPerm} = (1 : ENNReal) / 2 := by
    rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    simp [Fintype.card_perm]
  have hSwapMass : uniformPerm 2 {swapPerm} = (1 : ENNReal) / 2 := by
    rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    simp [Fintype.card_perm]
  have hIdReal : (uniformPerm 2).real {idPerm} = (1 : ℝ) / 2 := by
    rw [measureReal_def, uniformPerm, ProbabilityTheory.uniformOn_univ,
      Measure.count_singleton]
    simp [Fintype.card_perm]
  have hSwapReal : (uniformPerm 2).real {swapPerm} = (1 : ℝ) / 2 := by
    rw [measureReal_def, uniformPerm, ProbabilityTheory.uniformOn_univ,
      Measure.count_singleton]
    simp [Fintype.card_perm]
  have hA : ({π | (1 : ℝ) / Real.sqrt 2 ≤ (Z π).re} : Set (PermΩ 2)) ⊆ {idPerm} := by
    intro π hπ
    rcases Fin.eq_zero_or_eq_succ (π 0) with hzero | ⟨j, hj⟩
    · have heq := permFinTwo_eq_refl_of_apply_zero_eq_zero π hzero
      subst π
      simpa [idPerm]
    · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      have heq := permFinTwo_eq_swap_of_apply_zero_eq_one π (by simpa using hj)
      subst π
      have hpos : 0 < (1 : ℝ) / Real.sqrt 2 := by positivity
      have hfalse : (1 : ℝ) / Real.sqrt 2 ≤ -2 := by simpa [Z, idPerm] using hπ
      have hfalse' : (1 : ℝ) / Real.sqrt 2 ≤ 0 := by linarith
      exact (not_le_of_gt hpos hfalse').elim
  have hB : ({π | (1 : ℝ) / Real.sqrt 2 ≤ -(Z π).re} : Set (PermΩ 2)) ⊆ {swapPerm} := by
    intro π hπ
    rcases Fin.eq_zero_or_eq_succ (π 0) with hzero | ⟨j, hj⟩
    · have heq := permFinTwo_eq_refl_of_apply_zero_eq_zero π hzero
      subst π
      have hpos : 0 < (1 : ℝ) / Real.sqrt 2 := by positivity
      have hfalse : (1 : ℝ) / Real.sqrt 2 ≤ -2 := by simpa [Z, idPerm] using hπ
      have hfalse' : (1 : ℝ) / Real.sqrt 2 ≤ 0 := by linarith
      exact (not_le_of_gt hpos hfalse').elim
    · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      have heq := permFinTwo_eq_swap_of_apply_zero_eq_one π (by simpa using hj)
      subst π
      simpa [swapPerm]
  have hC : ({π | (1 : ℝ) / Real.sqrt 2 ≤ (Z π).im} : Set (PermΩ 2)) = ∅ := by
    ext π
    constructor
    · intro hπ
      have hpos : 0 < (1 : ℝ) / Real.sqrt 2 := by positivity
      rcases Fin.eq_zero_or_eq_succ (π 0) with hzero | ⟨j, hj⟩
      · have heq := permFinTwo_eq_refl_of_apply_zero_eq_zero π hzero
        subst π
        have hfalse : (1 : ℝ) / Real.sqrt 2 ≤ 0 := by simpa [Z, idPerm] using hπ
        exact (not_le_of_gt hpos hfalse).elim
      · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        have heq := permFinTwo_eq_swap_of_apply_zero_eq_one π (by simpa using hj)
        subst π
        have hfalse : (1 : ℝ) / Real.sqrt 2 ≤ 0 := by simpa [Z, idPerm] using hπ
        exact (not_le_of_gt hpos hfalse).elim
    · intro h
      cases h
  have hD : ({π | (1 : ℝ) / Real.sqrt 2 ≤ -(Z π).im} : Set (PermΩ 2)) = ∅ := by
    ext π
    constructor
    · intro hπ
      have hpos : 0 < (1 : ℝ) / Real.sqrt 2 := by positivity
      rcases Fin.eq_zero_or_eq_succ (π 0) with hzero | ⟨j, hj⟩
      · have heq := permFinTwo_eq_refl_of_apply_zero_eq_zero π hzero
        subst π
        have hfalse : (1 : ℝ) / Real.sqrt 2 ≤ 0 := by simpa [Z, idPerm] using hπ
        exact (not_le_of_gt hpos hfalse).elim
      · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        have heq := permFinTwo_eq_swap_of_apply_zero_eq_one π (by simpa using hj)
        subst π
        have hfalse : (1 : ℝ) / Real.sqrt 2 ≤ 0 := by simpa [Z, idPerm] using hπ
        exact (not_le_of_gt hpos hfalse).elim
    · intro h
      cases h
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Z, idPerm]
  · have hne : swapPerm ≠ idPerm := by decide
    simp [Z, swapPerm, idPerm, hne]
  · exact by decide
  · rw [hIdMass]
    norm_num
  · rw [hSwapMass]
    norm_num
  · calc
      (uniformPerm 2).real {π | (1 : ℝ) / Real.sqrt 2 ≤ (Z π).re} ≤
          (uniformPerm 2).real {idPerm} := measureReal_mono hA
      _ = 1 / 2 := hIdReal
  · calc
      (uniformPerm 2).real {π | (1 : ℝ) / Real.sqrt 2 ≤ -(Z π).re} ≤
          (uniformPerm 2).real {swapPerm} := measureReal_mono hB
      _ = 1 / 2 := hSwapReal
  · rw [hC]
    simp
  · rw [hD]
    simp

#print axioms complexNormEvent_subset_signedCoordinates
#print axioms uniformPerm_complexNorm_tail_of_signedCoordinate_tails
#print axioms uniformPerm_complexNorm_tail_two_witness
#print axioms complexCoordEvents
#print axioms uniformPerm_complexCoordEvents_measurable

end RBM.Gauss
