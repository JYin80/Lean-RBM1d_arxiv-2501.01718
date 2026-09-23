/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFiberSwap

/-!
# Exact counting transport between permutation prefix fibers

The finite equivalence from `PermutationFiberSwap` transports arbitrary sums and
cardinalities. This deterministic statement is a counting input toward conditional
exposure; it is not itself a probability or concentration estimate.
-/

namespace RBM.Gauss

/-- A prefix fiber is finite because it is a subtype of the finite permutation type. -/
noncomputable instance permutationPrefixFiberFintype (W : ℕ) (k : Fin W)
    (p : Fin W → Fin W) (v : Fin W) :
    Fintype (permutationPrefixFiber W k p v) := by
  classical
  letI : Finite (Equiv.Perm (Fin W)) :=
    Finite.of_injective (fun σ : Equiv.Perm (Fin W) => (σ : Fin W → Fin W))
      (by
        intro σ τ h
        ext i
        exact congrArg Fin.val (congrFun h i))
  unfold permutationPrefixFiber
  exact Fintype.ofFinite _

/-- Sum transport along the exact codomain-swap equivalence of prefix fibers. -/
theorem permutationPrefixFiber_sum_codomainSwap (W : ℕ) (hW : 2 ≤ W)
    (k : Fin W) (p : Fin W → Fin W) (a b : Fin W) (hab : a ≠ b)
    (ha : ∀ i, i < k → p i ≠ a) (hb : ∀ i, i < k → p i ≠ b)
    (F : Equiv.Perm (Fin W) → ℂ) :
    (∑ π : permutationPrefixFiber W k p a,
        F (permutationCodomainSwap W a b π.1)) =
      ∑ ρ : permutationPrefixFiber W k p b, F ρ.1 := by
  classical
  exact Fintype.sum_equiv
    (permutationPrefixFiberSwap W hW k p a b hab ha hb)
    (fun π => F (permutationCodomainSwap W a b π.1))
    (fun ρ => F ρ.1)
    (fun π => rfl)

/-- The two completion fibers have the same finite cardinality. -/
theorem permutationPrefixFiber_card_eq (W : ℕ) (hW : 2 ≤ W)
    (k : Fin W) (p : Fin W → Fin W) (a b : Fin W) (hab : a ≠ b)
    (ha : ∀ i, i < k → p i ≠ a) (hb : ∀ i, i < k → p i ≠ b) :
    Fintype.card (permutationPrefixFiber W k p a) =
      Fintype.card (permutationPrefixFiber W k p b) := by
  classical
  exact Fintype.card_congr
    (permutationPrefixFiberSwap W hW k p a b hab ha hb)

/-- At `W=2`, both fibers in T694's identity-prefix example have positive size. -/
theorem permutationPrefixFiber_two_card_pos :
    0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 0) ∧
      0 < Fintype.card (permutationPrefixFiber 2 0 (fun i => i) 1) := by
  classical
  rcases permutationPrefixFiberSwap_two_nonempty with ⟨ha, hb⟩
  exact ⟨Fintype.card_pos_iff.mpr ha, Fintype.card_pos_iff.mpr hb⟩

#print axioms permutationPrefixFiber_sum_codomainSwap
#print axioms permutationPrefixFiber_card_eq
#print axioms permutationPrefixFiber_two_card_pos
#print axioms permutationPrefixFiberFintype

end RBM.Gauss
