import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
Actual-prefix cells decrease as more permutation coordinates are revealed.
This is a finite support statement only; no conditional distribution is asserted.
-/

namespace RBM.Gauss

/-- Revealing a longer prefix can only shrink the actual-prefix cell. -/
theorem prefixCell_subset_of_le (W k l : ℕ) (hkl : k ≤ l) (π : PermΩ W) :
    prefixCell W l π ⊆ prefixCell W k π := by
  classical
  intro ρ hρ
  simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  intro i hik
  exact hρ i (Nat.lt_of_lt_of_le hik hkl)

/-- Cardinality of an actual-prefix cell is antitone in the reveal time. -/
theorem prefixCell_card_antitone (W k l : ℕ) (hkl : k ≤ l)
    (π : PermΩ W) :
    (prefixCell W l π).card ≤ (prefixCell W k π).card := by
  exact Finset.card_le_card (prefixCell_subset_of_le W k l hkl π)

/-- At reveal time zero the cell is the full permutation space. -/
theorem prefixCell_zero_eq_univ (W : ℕ) (π : PermΩ W) :
    prefixCell W 0 π = Finset.univ :=
  prefixCell_eq_univ_of_zero W π

/-- Once all `W` coordinates are revealed, the actual-prefix cell is the
singleton containing its reference permutation. -/
theorem prefixCell_eq_singleton_after_width (W l : ℕ) (hWl : W ≤ l)
    (π : PermΩ W) : prefixCell W l π = {π} :=
  prefixCell_eq_singleton_of_width_le W l hWl π

/-- At width zero there is a unique permutation, so all actual-prefix cells
are equal, regardless of their reveal times or reference labels. -/
theorem prefixCell_zero_width_eq (k l : ℕ) (π ρ : PermΩ 0) :
    prefixCell 0 k π = prefixCell 0 l ρ := by
  have hπρ : π = ρ := Subsingleton.elim _ _
  subst ρ
  rw [prefixCell_eq_singleton_of_width_le 0 k (Nat.zero_le k) π,
    prefixCell_eq_singleton_of_width_le 0 l (Nat.zero_le l) π]

/-- At width two, revealing the first coordinate loses the transposition from
the identity's cell while retaining the identity. This witnesses strict
inclusion from reveal time zero to reveal time one. -/
theorem prefixCell_two_id_strict_shrink :
    prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2) ⊆
        prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2) ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ∈
        prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2) ∧
      (Equiv.swap 0 1 : PermΩ 2) ∈
        prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2) ∧
      (Equiv.swap 0 1 : PermΩ 2) ∉
        prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2) := by
  refine ⟨prefixCell_subset_of_le 2 0 1 (by omega) _, ?_, ?_, ?_⟩
  · exact mem_prefixCell 2 1 _
  · simp [prefixCell]
  · simp [prefixCell]

#print axioms prefixCell_subset_of_le
#print axioms prefixCell_card_antitone
#print axioms prefixCell_zero_eq_univ
#print axioms prefixCell_eq_singleton_after_width
#print axioms prefixCell_zero_width_eq
#print axioms prefixCell_two_id_strict_shrink

end RBM.Gauss
