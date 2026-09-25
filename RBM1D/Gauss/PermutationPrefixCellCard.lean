import RBM1D.Gauss.PermutationPrefixFiltrationCore

/-!
Exact cardinality of an actual permutation prefix cell. The unrevealed positions
carry an arbitrary permutation; the prescribed prefix is supplied by the
reference permutation itself.
-/

namespace RBM.Gauss

open Equiv

private theorem prefixCell_iff (W k : ℕ) (π ρ : PermΩ W) :
    ρ ∈ prefixCell W k π ↔ ∀ i : Fin W, i.val < k → ρ i = π i := by
  classical
  simp [prefixCell]

/-- A cell is equivalent to the permutation group on its unrevealed positions. -/
noncomputable def prefixCellEquivFree (W k : ℕ) (π : PermΩ W) :
    Equiv.Perm {i : Fin W // k ≤ i.val} ≃ ↥(prefixCell W k π) := by
  classical
  let f : Equiv.Perm {i : Fin W // k ≤ i.val} → ↥(prefixCell W k π) :=
    fun τ => ⟨π * Equiv.Perm.ofSubtype τ, by
      apply (prefixCell_iff W k π _).2
      intro i hi
      rw [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_not_mem τ (by omega)]⟩
  apply Equiv.ofBijective f
  constructor
  · intro τ υ h
    apply Equiv.Perm.ofSubtype_injective
    have hh : π * Equiv.Perm.ofSubtype τ = π * Equiv.Perm.ofSubtype υ :=
      congrArg Subtype.val h
    exact mul_left_cancel hh
  · intro ρ
    let g : PermΩ W := π⁻¹ * ρ.1
    have hfix : ∀ i : Fin W, i.val < k → g i = i := by
      intro i hi
      have hρ := (prefixCell_iff W k π ρ.1).1 ρ.2 i hi
      simp [g, Equiv.Perm.mul_apply, hρ]
    have hrange : g ∈ (Equiv.Perm.ofSubtype :
        Equiv.Perm {i : Fin W // k ≤ i.val} →* PermΩ W).range := by
      apply Equiv.Perm.mem_range_ofSubtype_iff.mpr
      intro i hi
      by_contra hnot
      have hik : i.val < k := Nat.lt_of_not_ge hnot
      have hne : g i ≠ i := Equiv.Perm.mem_support.mp hi
      exact hne (hfix i hik)
    obtain ⟨τ, hτ⟩ := hrange
    refine ⟨τ, Subtype.ext ?_⟩
    change π * Equiv.Perm.ofSubtype τ = ρ.1
    rw [hτ]
    dsimp [g]
    simp

/-- The number of unrevealed positions is `W - min k W`. -/
theorem prefixFree_card (W k : ℕ) :
    Fintype.card {i : Fin W // k ≤ i.val} = W - min k W := by
  classical
  simpa only [not_lt, Fintype.card_fin, Fintype.card_subtype,
    Fin.card_filter_val_lt, Nat.min_comm W k] using
    (Fintype.card_subtype_compl (fun i : Fin W => i.val < k))

/-- Every actual prefix cell has the factorial number of unrestricted completions. -/
theorem prefixCell_card_eq_factorial (W k : ℕ) (π : PermΩ W) :
    (prefixCell W k π).card = (W - min k W).factorial := by
  classical
  rw [← Fintype.card_coe (prefixCell W k π)]
  rw [← Fintype.card_congr (prefixCellEquivFree W k π)]
  rw [Fintype.card_perm, prefixFree_card]

/-- At width zero there is exactly one completion. -/
theorem prefixCell_card_zero (k : ℕ) (π : PermΩ 0) :
    (prefixCell 0 k π).card = 1 := by
  simpa using prefixCell_card_eq_factorial 0 k π

/-- With an empty prefix, every permutation remains possible. -/
theorem prefixCell_card_at_zero (W : ℕ) (π : PermΩ W) :
    (prefixCell W 0 π).card = W.factorial := by
  simpa using prefixCell_card_eq_factorial W 0 π

/-- Once the whole width is revealed, only the reference permutation remains. -/
theorem prefixCell_card_after_width (W k : ℕ) (h : W ≤ k) (π : PermΩ W) :
    (prefixCell W k π).card = 1 := by
  rw [prefixCell_eq_singleton_of_width_le W k h π]
  simp

/-- The two-permutation width has a nontrivial empty-prefix cell. -/
theorem prefixCell_card_two_zero (π : PermΩ 2) :
    (prefixCell 2 0 π).card = 2 := by
  simpa using prefixCell_card_at_zero 2 π

/-- Revealing one position at width two leaves one completion. -/
theorem prefixCell_card_two_one (π : PermΩ 2) :
    (prefixCell 2 1 π).card = 1 := by
  simpa using prefixCell_card_eq_factorial 2 1 π

#print axioms prefixCellEquivFree
#print axioms prefixFree_card
#print axioms prefixCell_card_eq_factorial
#print axioms prefixCell_card_zero
#print axioms prefixCell_card_at_zero
#print axioms prefixCell_card_after_width
#print axioms prefixCell_card_two_zero
#print axioms prefixCell_card_two_one

end RBM.Gauss
