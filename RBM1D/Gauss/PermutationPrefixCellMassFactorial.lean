import RBM1D.Gauss.PermutationPrefixCellMass
import RBM1D.Gauss.PermutationPrefixCellCard

/-!
Exact factorial-ratio mass of every actual-prefix cell under the uniform
permutation measure.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

/-- The uniform mass of an actual-prefix cell is the factorial ratio given by
the number of free positions and the total number of permutations. -/
theorem uniformPerm_prefixCell_factorial_mass (W k : ℕ) (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k π} =
      ((W - min k W).factorial : ENNReal) / (W.factorial : ENNReal) := by
  rw [uniformPerm_prefixCell_event, prefixCell_card_eq_factorial,
    Fintype.card_perm, Fintype.card_fin]

/-- The denominator in the factorial-ratio formula is strictly positive. -/
theorem factorial_ennreal_pos (W : ℕ) :
    0 < (W.factorial : ENNReal) := by
  exact_mod_cast Nat.factorial_pos W

/-- At zero revealed coordinates the factorial ratio is one. -/
theorem uniformPerm_prefixCell_factorial_zero (W : ℕ) (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W 0 π} = 1 := by
  exact uniformPerm_prefixCell_zero_mass W π

/-- Revealing all coordinates leaves mass `1 / W!`. -/
theorem uniformPerm_prefixCell_factorial_full (W k : ℕ) (hWk : W ≤ k)
    (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k π} =
      (1 : ENNReal) / (W.factorial : ENNReal) := by
  rw [uniformPerm_prefixCell_factorial_mass]
  simp [Nat.min_eq_right hWk]

/-- At width zero, every actual-prefix cell has mass one. -/
theorem uniformPerm_prefixCell_factorial_zero_width (k : ℕ) (π : PermΩ 0) :
    uniformPerm 0 {ρ | ρ ∈ prefixCell 0 k π} = 1 := by
  exact uniformPerm_prefixCell_zero_width_mass k π

/-- At width two, a one-coordinate prefix has mass one half. -/
theorem uniformPerm_prefixCell_factorial_two_one (π : PermΩ 2) :
    uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 π} = (1 : ENNReal) / 2 := by
  rw [uniformPerm_prefixCell_factorial_mass]
  norm_num

/-- Identity and swap give distinct actual-prefix cells of mass one half at
width two and prefix length one. -/
theorem uniformPerm_prefixCell_factorial_two_one_witness :
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    prefixCell 2 1 idPerm ≠ prefixCell 2 1 swapPerm ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 idPerm} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 swapPerm} = (1 : ENNReal) / 2 := by
  rcases uniformPerm_prefixCell_two_one_witness with ⟨_, _, hne, hid, hswap⟩
  exact ⟨hne, hid, hswap⟩

#print axioms uniformPerm_prefixCell_factorial_mass
#print axioms factorial_ennreal_pos
#print axioms uniformPerm_prefixCell_factorial_zero
#print axioms uniformPerm_prefixCell_factorial_full
#print axioms uniformPerm_prefixCell_factorial_zero_width
#print axioms uniformPerm_prefixCell_factorial_two_one
#print axioms uniformPerm_prefixCell_factorial_two_one_witness

end RBM.Gauss
