import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
The permutation prefix filtration stops gaining information after every coordinate has been
revealed. This module only records stabilization of the generated sigma-algebras.
-/

namespace RBM.Gauss

/-- Once `k` covers the width, the coordinate-cylinder generators are exactly those at width. -/
theorem prefixCylinders_eq_of_width_le (W k : ℕ) (hWk : W ≤ k) :
    prefixCylinders W k = prefixCylinders W W := by
  ext s
  constructor
  · rintro ⟨i, v, hik, rfl⟩
    exact ⟨i, v, i.isLt, rfl⟩
  · rintro ⟨i, v, hiW, rfl⟩
    exact ⟨i, v, Nat.lt_of_lt_of_le hiW hWk, rfl⟩

/-- The prefix sigma-algebra stabilizes as soon as the whole width is revealed. -/
theorem prefixSigma_eq_of_width_le (W k : ℕ) (hWk : W ≤ k) :
    prefixSigma W k = prefixSigma W W := by
  unfold prefixSigma
  rw [prefixCylinders_eq_of_width_le W k hWk]

/-- At width zero, the cylinder family is empty for every revelation time. -/
theorem prefixCylinders_zero_eq_empty_stable (k : ℕ) :
    prefixCylinders 0 k = ∅ := by
  simp [prefixCylinders]

/-- At width zero, every prefix sigma-algebra is bottom, including time zero. -/
theorem prefixSigma_zero_eq_bottom_stable (k : ℕ) :
    prefixSigma 0 k = ⊥ := by
  rw [prefixSigma, prefixCylinders_zero_eq_empty_stable]
  exact MeasurableSpace.generateFrom_empty

/-- The width-two prefix sigma-algebra is stable at every time `k ≥ 2`. -/
theorem prefixSigma_two_stable (k : ℕ) (h₂k : 2 ≤ k) :
    prefixSigma 2 k = prefixSigma 2 2 :=
  prefixSigma_eq_of_width_le 2 k h₂k

/-- The width-two sigma-algebra at time two equals that at time three. -/
theorem prefixSigma_two_two_eq_three : prefixSigma 2 2 = prefixSigma 2 3 := by
  exact (prefixSigma_two_stable 3 (by omega)).symm

/-- The zero-width, zero-time boundary case: the generated sigma-algebra is bottom. -/
theorem prefixSigma_zero_zero_eq_bottom : prefixSigma 0 0 = ⊥ :=
  prefixSigma_zero_eq_bottom_stable 0

#print axioms prefixCylinders_eq_of_width_le
#print axioms prefixSigma_eq_of_width_le
#print axioms prefixCylinders_zero_eq_empty_stable
#print axioms prefixSigma_zero_eq_bottom_stable
#print axioms prefixSigma_two_stable
#print axioms prefixSigma_two_two_eq_three
#print axioms prefixSigma_zero_zero_eq_bottom

end RBM.Gauss
