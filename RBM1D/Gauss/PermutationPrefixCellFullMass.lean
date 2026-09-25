import RBM1D.Gauss.PermutationPrefixCellMass

/-!
Exact uniform mass of a fully revealed actual-prefix cell.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

/-- Once the prefix covers the full width, its actual-prefix cell has mass
exactly the reciprocal of the total number `W!` of permutations. -/
theorem uniformPerm_prefixCell_full_mass (W k : ℕ) (hWk : W ≤ k)
    (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k π} =
      (1 : ENNReal) / (Nat.factorial W : ENNReal) := by
  have _hfactorial_pos : 0 < Nat.factorial W := Nat.factorial_pos W
  rw [uniformPerm_prefixCell_event,
    prefixCell_eq_singleton_of_width_le W k hWk π,
    Finset.card_singleton, Fintype.card_perm]
  rw [Fintype.card_fin]
  norm_num

/-- Widths zero and one have full-reveal mass one; at width two it is one half. -/
theorem uniformPerm_prefixCell_full_mass_small_widths :
    (∀ k (π : PermΩ 0),
      uniformPerm 0 {ρ | ρ ∈ prefixCell 0 k π} = 1) ∧
    (∀ k (_hk : 1 ≤ k) (π : PermΩ 1),
      uniformPerm 1 {ρ | ρ ∈ prefixCell 1 k π} = 1) ∧
    (∀ k (_hk : 2 ≤ k) (π : PermΩ 2),
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 k π} = (1 : ENNReal) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k π
    simpa using uniformPerm_prefixCell_full_mass 0 k (Nat.zero_le k) π
  · intro k hk π
    simpa using uniformPerm_prefixCell_full_mass 1 k hk π
  · intro k hk π
    simpa using uniformPerm_prefixCell_full_mass 2 k hk π

/-- The width-two examples retain the nondegenerate distinction visible at
zero reveal time, while each fully revealed cell has mass one half. -/
theorem uniformPerm_prefixCell_full_mass_two_witness :
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 idPerm} = 1 ∧
    idPerm ≠ swapPerm ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 idPerm} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 swapPerm} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 2 idPerm} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 2 swapPerm} = (1 : ENNReal) / 2 := by
  dsimp
  have h := uniformPerm_prefixCell_two_one_witness
  rcases h with ⟨_, _, _, hIdHalf, hSwapHalf⟩
  refine ⟨uniformPerm_prefixCell_zero_mass 2 (Equiv.refl (Fin 2)), ?_,
    hIdHalf, hSwapHalf, ?_, ?_⟩
  · decide
  · simpa [Nat.factorial] using uniformPerm_prefixCell_full_mass 2 2
      (Nat.le_refl 2) (Equiv.refl (Fin 2) : PermΩ 2)
  · simpa [Nat.factorial] using uniformPerm_prefixCell_full_mass 2 2
      (Nat.le_refl 2) (Equiv.swap 0 1 : PermΩ 2)

#print axioms uniformPerm_prefixCell_full_mass
#print axioms uniformPerm_prefixCell_full_mass_small_widths
#print axioms uniformPerm_prefixCell_full_mass_two_witness

end RBM.Gauss
