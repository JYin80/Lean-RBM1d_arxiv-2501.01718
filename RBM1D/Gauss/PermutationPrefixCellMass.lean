import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
Exact counting probabilities of actual-prefix cells under the uniform
permutation measure.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

/-- The uniform permutation measure of an actual-prefix cell is its relative
cardinality in the finite permutation space. -/
theorem uniformPerm_prefixCell_event (W k : ℕ) (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k π} =
      (prefixCell W k π).card / Fintype.card (PermΩ W) := by
  classical
  rw [uniformPerm, ProbabilityTheory.uniformOn_univ]
  change Measure.count (prefixCell W k π : Set (PermΩ W)) / _ = _
  rw [Measure.count_apply_finset]

/-- Every actual-prefix cell has strictly positive mass under the uniform
permutation measure. -/
theorem uniformPerm_prefixCell_event_pos (W k : ℕ) (π : PermΩ W) :
    0 < uniformPerm W {ρ | ρ ∈ prefixCell W k π} := by
  rw [uniformPerm_prefixCell_event]
  apply ENNReal.div_pos
  · exact_mod_cast (Nat.ne_of_gt (prefixCell_card_pos W k π))
  · exact ENNReal.natCast_ne_top _

/-- At prefix length zero, the cell is the whole space and has mass one. -/
theorem uniformPerm_prefixCell_zero_mass (W : ℕ) (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W 0 π} = 1 := by
  rw [uniformPerm_prefixCell_event, prefixCell_eq_univ_of_zero]
  rw [Finset.card_univ]
  apply ENNReal.div_self
  · exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (PermΩ W)))
  · exact ENNReal.natCast_ne_top _

/-- When the prefix covers the full index set, the cell is a singleton and
its mass is positive. -/
theorem uniformPerm_prefixCell_full_mass_pos (W k : ℕ) (hWk : W ≤ k)
    (π : PermΩ W) :
    prefixCell W k π = {π} ∧
      0 < uniformPerm W {ρ | ρ ∈ prefixCell W k π} := by
  exact ⟨prefixCell_eq_singleton_of_width_le W k hWk π,
    uniformPerm_prefixCell_event_pos W k π⟩

/-- At width zero there is one permutation, and its unique actual-prefix cell
has mass one for every prefix length. -/
theorem uniformPerm_prefixCell_zero_width_mass (k : ℕ) (π : PermΩ 0) :
    uniformPerm 0 {ρ | ρ ∈ prefixCell 0 k π} = 1 := by
  rw [uniformPerm_prefixCell_event, prefixCell_eq_singleton_of_width_le 0 k
    (Nat.zero_le k), Fintype.card_perm]
  simp

/-- For width two and a one-coordinate prefix, identity and swap give the two
distinct singleton cells, each of mass one half. -/
theorem uniformPerm_prefixCell_two_one_witness :
    let idPerm : PermΩ 2 := Equiv.refl (Fin 2)
    let swapPerm : PermΩ 2 := Equiv.swap 0 1
    prefixCell 2 1 idPerm = {idPerm} ∧
      prefixCell 2 1 swapPerm = {swapPerm} ∧
    prefixCell 2 1 idPerm ≠ prefixCell 2 1 swapPerm ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 idPerm} = (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 swapPerm} = (1 : ENNReal) / 2 := by
  classical
  dsimp
  have hId : prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2) =
      {(Equiv.refl (Fin 2) : PermΩ 2)} := by decide
  have hSwap : prefixCell 2 1 (Equiv.swap 0 1 : PermΩ 2) =
      {(Equiv.swap 0 1 : PermΩ 2)} := by decide
  have hne : (Equiv.refl (Fin 2) : PermΩ 2) ≠ Equiv.swap 0 1 := by decide
  refine ⟨hId, hSwap, ?_, ?_, ?_⟩
  · rw [hId, hSwap]
    intro heq
    have hmem : (Equiv.refl (Fin 2) : PermΩ 2) ∈
        ({(Equiv.swap 0 1 : PermΩ 2)} : Finset (PermΩ 2)) := by
      rw [← heq]
      simp
    exact hne (Finset.mem_singleton.mp hmem)
  · rw [hId]
    rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
    norm_num [Fintype.card_perm]
  · rw [hSwap]
    rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
    norm_num [Fintype.card_perm]

#print axioms uniformPerm_prefixCell_event
#print axioms uniformPerm_prefixCell_event_pos
#print axioms uniformPerm_prefixCell_zero_mass
#print axioms uniformPerm_prefixCell_full_mass_pos
#print axioms uniformPerm_prefixCell_zero_width_mass
#print axioms uniformPerm_prefixCell_two_one_witness

end RBM.Gauss
