import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
Clean replacement for the finite actual-prefix cell stabilization result.
This statement is downstream of the paper's local laws (2.3)--(2.4) and makes
no conditional-distribution claim.
-/

namespace RBM.Gauss

/-- Once the reveal length covers the width, the actual-prefix cell agrees
with the cell at the full-width reveal time. -/
theorem prefixCell_eq_at_width_of_le_clean (W k : ℕ) (hWk : W ≤ k)
    (π : PermΩ W) :
    prefixCell W k π = prefixCell W W π := by
  rw [prefixCell_eq_singleton_of_width_le W k hWk π,
    prefixCell_eq_singleton_of_width_le W W le_rfl π]

/-- Once the reveal length covers the width, the actual-prefix cell has one
element. -/
theorem prefixCell_card_eq_one_of_width_le_clean (W k : ℕ) (hWk : W ≤ k)
    (π : PermΩ W) :
    (prefixCell W k π).card = 1 := by
  rw [prefixCell_eq_singleton_of_width_le W k hWk π]
  simp

/-- Boundary checks: zero width at `k=0`, width one at full reveal, and width
two after full reveal are singletons; before any width-two reveal, identity
and swap are distinct members of the same cell. -/
theorem prefixCell_stable_boundary_cases_clean :
    prefixCell 0 0 (Equiv.refl (Fin 0) : PermΩ 0) =
        {(Equiv.refl (Fin 0) : PermΩ 0)} ∧
      (prefixCell 0 0 (Equiv.refl (Fin 0) : PermΩ 0)).card = 1 ∧
      prefixCell 1 1 (Equiv.refl (Fin 1) : PermΩ 1) =
        {(Equiv.refl (Fin 1) : PermΩ 1)} ∧
      (prefixCell 1 1 (Equiv.refl (Fin 1) : PermΩ 1)).card = 1 ∧
      (∀ k : ℕ, 2 ≤ k →
        prefixCell 2 k (Equiv.refl (Fin 2) : PermΩ 2) =
            {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
          (prefixCell 2 k (Equiv.refl (Fin 2) : PermΩ 2)).card = 1) ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ∈
          prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2) ∧
        (Equiv.swap 0 1 : PermΩ 2) ∈
          prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2) ∧
        (Equiv.swap 0 1 : PermΩ 2) ≠ (Equiv.refl (Fin 2) : PermΩ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact prefixCell_eq_singleton_of_width_le 0 0 (by omega) _
  · exact prefixCell_card_eq_one_of_width_le_clean 0 0 (by omega) _
  · exact prefixCell_eq_singleton_of_width_le 1 1 (by omega) _
  · exact prefixCell_card_eq_one_of_width_le_clean 1 1 (by omega) _
  · intro k hk
    exact ⟨prefixCell_eq_singleton_of_width_le 2 k (by omega) _,
      prefixCell_card_eq_one_of_width_le_clean 2 k (by omega) _⟩
  · exact mem_prefixCell 2 0 _
  · exact prefixCell_two_support_witness.2.1
  · exact prefixCell_two_support_witness.2.2

#print axioms prefixCell_eq_at_width_of_le_clean
#print axioms prefixCell_card_eq_one_of_width_le_clean
#print axioms prefixCell_stable_boundary_cases_clean

end RBM.Gauss
