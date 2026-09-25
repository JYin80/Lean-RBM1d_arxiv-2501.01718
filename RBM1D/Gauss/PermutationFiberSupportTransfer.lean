/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFiberCount

/-!
# Positive support transfer for permutation prefix fibers

Equal finite completion counts transfer positive support in both directions.
An inconsistent prescribed prefix can still make both fibers empty; this module
records an explicit example as well as a positive-support witness.
-/

namespace RBM.Gauss

/-- Equal completion counts give equivalent positive-support conditions. -/
theorem permutationPrefixFiber_card_pos_iff (W : ℕ) (hW : 2 ≤ W)
    (k : Fin W) (p : Fin W → Fin W) (a b : Fin W) (hab : a ≠ b)
    (ha : ∀ i, i < k → p i ≠ a) (hb : ∀ i, i < k → p i ≠ b) :
    0 < Fintype.card (permutationPrefixFiber W k p a) ↔
      0 < Fintype.card (permutationPrefixFiber W k p b) := by
  rw [permutationPrefixFiber_card_eq W hW k p a b hab ha hb]

/-- The two distinct candidate images at `W=2` both have positive support. -/
theorem permutationPrefixFiber_two_support_transfer_witness :
    0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 0) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 1) :=
  permutationPrefixFiber_two_card_pos

private theorem repeatedPrefixFiber_isEmpty (v : Fin 3) :
    IsEmpty (permutationPrefixFiber 3 2 (fun _ : Fin 3 => (0 : Fin 3)) v) := by
  refine ⟨?_⟩
  rintro ⟨π, hp, _⟩
  have h0 : π (0 : Fin 3) = (0 : Fin 3) := by
    simpa using hp (0 : Fin 3) (by decide)
  have h1 : π (1 : Fin 3) = (0 : Fin 3) := by
    simpa using hp (1 : Fin 3) (by decide)
  have h01 : (0 : Fin 3) = (1 : Fin 3) := π.injective (h0.trans h1.symm)
  exact (by decide : (0 : Fin 3) ≠ (1 : Fin 3)) h01

/--
For the repeated prefix `p 0 = p 1 = 0`, both unused images have empty fibers.
The hypotheses hold, but neither fiber has positive support, so unconditional
positivity cannot be inferred from unusedness alone.
-/
theorem permutationPrefixFiber_repeatedPrefix_empty_witness :
    (2 : ℕ) ≤ 3 ∧
      (1 : Fin 3) ≠ 2 ∧
      (∀ i : Fin 3, i < (2 : Fin 3) →
        (fun _ : Fin 3 => (0 : Fin 3)) i ≠ (1 : Fin 3)) ∧
      (∀ i : Fin 3, i < (2 : Fin 3) →
        (fun _ : Fin 3 => (0 : Fin 3)) i ≠ 2) ∧
      Fintype.card
          (permutationPrefixFiber 3 2 (fun _ : Fin 3 => (0 : Fin 3)) 1) = 0 ∧
        Fintype.card
          (permutationPrefixFiber 3 2 (fun _ : Fin 3 => (0 : Fin 3)) 2) = 0 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro i _
    simp
  · intro i _
    simp
  · exact Fintype.card_eq_zero_iff.mpr (repeatedPrefixFiber_isEmpty 1)
  · exact Fintype.card_eq_zero_iff.mpr (repeatedPrefixFiber_isEmpty 2)

#print axioms permutationPrefixFiber_card_pos_iff
#print axioms permutationPrefixFiber_two_support_transfer_witness
#print axioms repeatedPrefixFiber_isEmpty
#print axioms permutationPrefixFiber_repeatedPrefix_empty_witness

end RBM.Gauss
