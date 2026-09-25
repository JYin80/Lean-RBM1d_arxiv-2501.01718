/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationPrefixFiltrationCore
import RBM1D.Gauss.PermutationFiberCount

/-!
# The actual-prefix cell and next-image fiber have the same support

The cell fixes the values below the revealed coordinate, and the fiber fixes
those same values together with the next image. This is a finite deterministic
identification; it does not assert a conditional law.
-/

namespace RBM.Gauss

/-- The part of an actual prefix cell whose next image is `v`. -/
def prefixCellNextFiber (W : ℕ) (k : Fin W) (π : PermΩ W) (v : Fin W) : Type :=
  {ρ : PermΩ W // ρ ∈ prefixCell W k.val π ∧ ρ k = v}

/-- The subfiber is finite as a subtype of the finite permutation space. -/
noncomputable instance prefixCellNextFiberFintype (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) : Fintype (prefixCellNextFiber W k π v) := by
  classical
  letI : Finite (PermΩ W) :=
    Finite.of_injective (fun σ : PermΩ W => (σ : Fin W → Fin W))
      (by
        intro σ τ h
        ext i
        exact congrArg Fin.val (congrFun h i))
  unfold prefixCellNextFiber
  exact Fintype.ofFinite _

private theorem prefixCell_mem_iff_prefix (W : ℕ) (k : Fin W)
    (π ρ : PermΩ W) :
    ρ ∈ prefixCell W k.val π ↔ ∀ i : Fin W, i < k → ρ i = π i := by
  classical
  constructor
  · intro h i hi
    have hi' : i.val < k.val := by omega
    have h' := (Finset.mem_filter.mp h).2 i hi'
    exact h'
  · intro h
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · intro i hi
      exact h i (by omega)

/-- Exact equivalence between the actual-cell subfiber and T694's prefix fiber. -/
noncomputable def prefixCellNextFiberEquiv (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) :
    prefixCellNextFiber W k π v ≃
      permutationPrefixFiber W k (fun i => π i) v where
  toFun ρ := ⟨ρ.1, (prefixCell_mem_iff_prefix W k π ρ.1).1 ρ.2.1, ρ.2.2⟩
  invFun ρ := ⟨ρ.1, (prefixCell_mem_iff_prefix W k π ρ.1).2 ρ.2.1, ρ.2.2⟩
  left_inv ρ := by rfl
  right_inv ρ := by rfl

/-- The two finite supports have exactly the same cardinality. -/
theorem prefixCellNextFiber_card_eq (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) :
    Fintype.card (prefixCellNextFiber W k π v) =
      Fintype.card (permutationPrefixFiber W k (fun i => π i) v) := by
  classical
  exact Fintype.card_congr (prefixCellNextFiberEquiv W k π v)

/-- At width one, the only next-image subfiber is a singleton. -/
theorem prefixCellNextFiber_one_card :
    Fintype.card (prefixCellNextFiber 1 0 (Equiv.refl _) 0) = 1 := by
  classical
  have hcard := prefixCellNextFiber_card_eq 1 0 (Equiv.refl _) 0
  rw [hcard]
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨Equiv.refl _, ?_⟩, ?_⟩
  · constructor
    · intro i hi
      exact (Fin.not_lt_zero i hi).elim
    · rfl
  · intro y
    apply Subtype.ext
    exact Subsingleton.elim _ _

/-- At width two and empty prefix, identity and swap lie in different positive
next-image subfibers. -/
theorem prefixCellNextFiber_two_witness :
    Nonempty (prefixCellNextFiber 2 0 (Equiv.refl _) 0) ∧
      Nonempty (prefixCellNextFiber 2 0 (Equiv.refl _) 1) ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ≠ Equiv.swap 0 1 ∧
      0 < Fintype.card (prefixCellNextFiber 2 0 (Equiv.refl _) 0) ∧
      0 < Fintype.card (prefixCellNextFiber 2 0 (Equiv.refl _) 1) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨Equiv.refl _, ?_⟩⟩
    exact ⟨mem_prefixCell 2 0 _, rfl⟩
  · refine ⟨⟨Equiv.swap 0 1, ?_⟩⟩
    exact ⟨by simp [prefixCell], by simp⟩
  · intro h
    have h01 : (Equiv.refl (Fin 2) : PermΩ 2) 0 = Equiv.swap 0 1 0 :=
      congrArg (fun e : Equiv.Perm (Fin 2) => e 0) h
    have : (0 : Fin 2) = 1 := by simpa using h01
    exact (by decide : (0 : Fin 2) ≠ 1) this
  · exact Fintype.card_pos_iff.mpr ⟨⟨Equiv.refl _,
      ⟨mem_prefixCell 2 0 _, rfl⟩⟩⟩
  · exact Fintype.card_pos_iff.mpr ⟨⟨Equiv.swap 0 1,
      ⟨by simp [prefixCell], by simp⟩⟩⟩

#print axioms prefixCellNextFiber
#print axioms prefixCellNextFiberFintype
#print axioms prefixCellNextFiberEquiv
#print axioms prefixCellNextFiber_card_eq
#print axioms prefixCellNextFiber_one_card
#print axioms prefixCellNextFiber_two_witness

end RBM.Gauss
