import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
Actual-prefix cells of the finite permutation space form a partition up to
repeated names: two cells are equal precisely when their prefixes agree, and
otherwise they are disjoint. This is a finite combinatorial statement only.
-/

namespace RBM.Gauss

/-- Two actual-prefix cells are equal exactly when their defining permutations
agree on every coordinate revealed by the prefix. -/
theorem prefixCell_eq_iff_agree (W k : ℕ) (π ρ : PermΩ W) :
    prefixCell W k π = prefixCell W k ρ ↔
      ∀ i : Fin W, i.val < k → π i = ρ i := by
  classical
  constructor
  · intro h i hik
    have hρ : ρ ∈ prefixCell W k ρ := mem_prefixCell W k ρ
    rw [← h] at hρ
    simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    exact (hρ i hik).symm
  · intro h
    ext σ
    simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hσ i hik
      calc
        σ i = π i := hσ i hik
        _ = ρ i := h i hik
    · intro hσ i hik
      calc
        σ i = ρ i := hσ i hik
        _ = π i := (h i hik).symm

/-- If two prefixes differ at a revealed coordinate, their actual-prefix
cells are disjoint. -/
theorem prefixCell_disjoint_of_disagree (W k : ℕ) (π ρ : PermΩ W)
    (i : Fin W) (hik : i.val < k) (hneq : π i ≠ ρ i) :
    Disjoint (prefixCell W k π) (prefixCell W k ρ) := by
  classical
  rw [Finset.disjoint_left]
  intro σ hπ hρ
  simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and] at hπ hρ
  have hσπ : σ i = π i := hπ i hik
  have hσρ : σ i = ρ i := hρ i hik
  exact hneq (hσπ.symm.trans hσρ)

/-- Every permutation belongs to its own cell, and any two indexed cells are
equal or disjoint. Thus the distinct actual-prefix cells cover the permutation
space and form a genuine finite partition. -/
theorem prefixCell_partition (W k : ℕ) :
    (∀ π : PermΩ W, π ∈ prefixCell W k π) ∧
      (∀ π ρ : PermΩ W,
        prefixCell W k π = prefixCell W k ρ ∨
          Disjoint (prefixCell W k π) (prefixCell W k ρ)) := by
  constructor
  · exact fun π => mem_prefixCell W k π
  · intro π ρ
    by_cases hagree : ∀ i : Fin W, i.val < k → π i = ρ i
    · exact Or.inl ((prefixCell_eq_iff_agree W k π ρ).2 hagree)
    · push Not at hagree
      obtain ⟨i, hik, hneq⟩ := hagree
      exact Or.inr (prefixCell_disjoint_of_disagree W k π ρ i hik hneq)

/-- The union of all actual-prefix cells is the whole permutation space. -/
theorem prefixCell_iUnion_eq_univ (W k : ℕ) :
    (⋃ π : PermΩ W, (prefixCell W k π : Set (PermΩ W))) = Set.univ := by
  ext σ
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨σ, mem_prefixCell W k σ⟩

/-- At prefix length zero every actual-prefix cell is the full permutation
space, so identity and transposition label the same cell at width two. -/
theorem prefixCell_two_id_swap_eq_zero :
    prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2) =
      prefixCell 2 0 (Equiv.swap 0 1 : PermΩ 2) := by
  rw [prefixCell_eq_univ_of_zero, prefixCell_eq_univ_of_zero]

/-- At prefix length one, identity and transposition at width two define
distinct actual-prefix cells. -/
theorem prefixCell_two_id_swap_ne_one :
    prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2) ≠
      prefixCell 2 1 (Equiv.swap 0 1 : PermΩ 2) := by
  intro heq
  have hagree := (prefixCell_eq_iff_agree 2 1
    (Equiv.refl (Fin 2) : PermΩ 2) (Equiv.swap 0 1 : PermΩ 2)).1 heq
  have h0 := hagree (0 : Fin 2) (by decide)
  have hcontra : (0 : Fin 2) = 1 := h0
  exact (by decide : (0 : Fin 2) ≠ 1) hcontra

/-- The width-zero space has one permutation, hence one nonempty actual-prefix
cell at every prefix length. -/
theorem prefixCell_zero_width_singleton (k : ℕ) (π : PermΩ 0) :
    prefixCell 0 k π = {(Equiv.refl (Fin 0) : PermΩ 0)} := by
  have hπ : π = (Equiv.refl (Fin 0) : PermΩ 0) := Subsingleton.elim _ _
  rw [hπ]
  exact prefixCell_eq_singleton_of_width_le 0 k (Nat.zero_le k) _

#print axioms prefixCell_eq_iff_agree
#print axioms prefixCell_disjoint_of_disagree
#print axioms prefixCell_partition
#print axioms prefixCell_iUnion_eq_univ
#print axioms prefixCell_two_id_swap_eq_zero
#print axioms prefixCell_two_id_swap_ne_one
#print axioms prefixCell_zero_width_singleton

end RBM.Gauss
