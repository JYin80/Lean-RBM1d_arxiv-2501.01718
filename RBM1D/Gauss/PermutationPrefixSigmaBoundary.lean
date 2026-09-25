import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
Boundary behavior of the finite permutation prefix filtration.  At time zero there is no
coordinate information; at width two, revealing the first coordinate strictly refines it.
This module makes no claim about conditional distributions.
-/

namespace RBM.Gauss

open MeasureTheory

/-- With no revealed coordinates, the generated prefix sigma-algebra is bottom. -/
theorem prefixSigma_zero_eq_bot (W : ℕ) : prefixSigma W 0 = ⊥ := by
  have hCylinders : prefixCylinders W 0 = ∅ := by
    ext s
    simp only [prefixCylinders, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨i, v, hi, _⟩
    omega
  rw [prefixSigma, hCylinders, MeasurableSpace.generateFrom_empty]

/-- At width zero, the time-zero prefix sigma-algebra is still bottom. -/
theorem prefixSigma_zero_width_eq_bot : prefixSigma 0 0 = ⊥ :=
  prefixSigma_zero_eq_bot 0

/-- The event that the first position maps to zero in a width-two permutation. -/
def firstCoordinateZeroEvent : Set (PermΩ 2) := {π | π 0 = 0}

/-- The first-coordinate event is measurable once the first coordinate is revealed. -/
theorem firstCoordinateZeroEvent_measurable_one :
    MeasurableSet[prefixSigma 2 1] firstCoordinateZeroEvent := by
  apply MeasurableSpace.measurableSet_generateFrom
  refine ⟨0, 0, by decide, ?_⟩
  rfl

/-- The first-coordinate event is not measurable before any coordinate is revealed. -/
theorem firstCoordinateZeroEvent_not_measurable_zero :
    ¬ MeasurableSet[prefixSigma 2 0] firstCoordinateZeroEvent := by
  rw [prefixSigma_zero_eq_bot]
  intro h
  rcases MeasurableSpace.measurableSet_bot_iff.mp h with hEmpty | hUniv
  · have hid : (Equiv.refl (Fin 2) : PermΩ 2) ∈ firstCoordinateZeroEvent := by
      simp [firstCoordinateZeroEvent]
    rw [hEmpty] at hid
    exact hid
  · have hswap : (Equiv.swap (0 : Fin 2) 1 : PermΩ 2) ∉ firstCoordinateZeroEvent := by
      simp [firstCoordinateZeroEvent]
    rw [hUniv] at hswap
    exact hswap (Set.mem_univ _)

/-- Identity is inside and the transposition is outside the first-coordinate event. -/
theorem firstCoordinateZeroEvent_two_witness :
    (Equiv.refl (Fin 2) : PermΩ 2) ∈ firstCoordinateZeroEvent ∧
      (Equiv.swap (0 : Fin 2) 1 : PermΩ 2) ∉ firstCoordinateZeroEvent := by
  constructor
  · simp [firstCoordinateZeroEvent]
  · simp [firstCoordinateZeroEvent]

/-- Revealing the first coordinate strictly increases the width-two prefix information. -/
theorem prefixSigma_two_zero_lt_one : prefixSigma 2 0 < prefixSigma 2 1 := by
  change prefixSigma 2 0 ≤ prefixSigma 2 1 ∧ ¬ prefixSigma 2 1 ≤ prefixSigma 2 0
  constructor
  · exact prefixSigma_mono 2 (by omega)
  · intro hle
    exact firstCoordinateZeroEvent_not_measurable_zero
      ((hle firstCoordinateZeroEvent) firstCoordinateZeroEvent_measurable_one)

#print axioms prefixSigma_zero_eq_bot
#print axioms prefixSigma_zero_width_eq_bot
#print axioms firstCoordinateZeroEvent
#print axioms firstCoordinateZeroEvent_measurable_one
#print axioms firstCoordinateZeroEvent_not_measurable_zero
#print axioms firstCoordinateZeroEvent_two_witness
#print axioms prefixSigma_two_zero_lt_one

end RBM.Gauss
