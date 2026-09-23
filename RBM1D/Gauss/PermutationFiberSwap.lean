/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierSwap

/-!
# Swapping unused images in a finite permutation prefix fiber

The map below couples completions with two different next images. It is purely finite;
there is no probability or concentration assertion.
-/

namespace RBM.Gauss

/-- Permutations with a prescribed revealed prefix and next image. -/
def permutationPrefixFiber (W : ℕ) (k : Fin W) (p : Fin W → Fin W)
    (v : Fin W) : Type :=
  {π : Equiv.Perm (Fin W) // (∀ i, i < k → π i = p i) ∧ π k = v}

/-- Postcompose a permutation with a transposition of two values. -/
def permutationCodomainSwap (W : ℕ) (a b : Fin W)
    (π : Equiv.Perm (Fin W)) : Equiv.Perm (Fin W) :=
  π.trans (Equiv.swap a b)

@[simp] theorem permutationCodomainSwap_apply (W : ℕ) (a b : Fin W)
    (π : Equiv.Perm (Fin W)) (i : Fin W) :
    permutationCodomainSwap W a b π i = Equiv.swap a b (π i) := rfl

/-- Swapping the same two images twice restores the original permutation. -/
theorem permutationCodomainSwap_involutive (W : ℕ) (a b : Fin W) :
    Function.Involutive (permutationCodomainSwap W a b) := by
  intro π
  ext i
  simp [permutationCodomainSwap]

/-- The codomain transposition fixes every previously revealed value. -/
theorem permutationCodomainSwap_prefix (W : ℕ) (k : Fin W)
    (p : Fin W → Fin W) (a b : Fin W)
    (ha : ∀ i, i < k → p i ≠ a) (hb : ∀ i, i < k → p i ≠ b)
    (π : Equiv.Perm (Fin W)) (hπ : ∀ i, i < k → π i = p i) :
    ∀ i, i < k → permutationCodomainSwap W a b π i = p i := by
  intro i hi
  rw [permutationCodomainSwap_apply, hπ i hi]
  exact Equiv.swap_apply_of_ne_of_ne (ha i hi) (hb i hi)

/-- The image-swap is an exact equivalence between the two completion fibers. -/
def permutationPrefixFiberSwap (W : ℕ) (_hW : 2 ≤ W) (k : Fin W)
    (p : Fin W → Fin W) (a b : Fin W) (_hab : a ≠ b)
    (ha : ∀ i, i < k → p i ≠ a) (hb : ∀ i, i < k → p i ≠ b) :
    permutationPrefixFiber W k p a ≃ permutationPrefixFiber W k p b where
  toFun π := ⟨permutationCodomainSwap W a b π.1,
    permutationCodomainSwap_prefix W k p a b ha hb π.1 π.2.1,
    by simp [π.2.2]⟩
  invFun π := ⟨permutationCodomainSwap W a b π.1,
    permutationCodomainSwap_prefix W k p a b ha hb π.1 π.2.1,
    by simp [π.2.2]⟩
  left_inv π := by
    apply Subtype.ext
    exact permutationCodomainSwap_involutive W a b π.1
  right_inv π := by
    apply Subtype.ext
    exact permutationCodomainSwap_involutive W a b π.1

/-- At `W=2`, the identity and the transposition inhabit the two fibers. -/
theorem permutationPrefixFiberSwap_two_nonempty :
    Nonempty (permutationPrefixFiber 2 0 (fun i => i) 0) ∧
      Nonempty (permutationPrefixFiber 2 0 (fun i => i) 1) := by
  constructor
  · refine ⟨⟨Equiv.refl _, ?_, ?_⟩⟩
    · intro i hi
      exact (Fin.not_lt_zero i hi).elim
    · rfl
  · refine ⟨⟨Equiv.swap (0 : Fin 2) 1, ?_, ?_⟩⟩
    · intro i hi
      exact (Fin.not_lt_zero i hi).elim
    · simp

/-- A swap of two images is a swap of their two preimages in the domain. -/
theorem permutationCodomainSwap_eq_domainSwap (W : ℕ) (a b : Fin W)
    (π : Equiv.Perm (Fin W)) :
    permutationCodomainSwap W a b π =
      (Equiv.swap (π.symm a) (π.symm b)).trans π := by
  have h := Equiv.trans_swap_trans_symm a b π
  have h' := congrArg (fun σ : Equiv.Perm (Fin W) => σ.trans π) h
  simpa [permutationCodomainSwap, Equiv.trans_assoc] using h'

/-- The completion coupling inherits the `8/W` Fourier sensitivity estimate. -/
theorem norm_permutationFourierSum_codomainSwap_le (W : ℕ) (hW : 2 ≤ W)
    (x χ : Fin W → ℂ) (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1)
    (π : Equiv.Perm (Fin W)) (a b : Fin W) :
    ‖permutationFourierSum W x χ (permutationCodomainSwap W a b π) -
      permutationFourierSum W x χ π‖ ≤ 8 / (W : ℝ) := by
  rw [permutationCodomainSwap_eq_domainSwap]
  exact norm_permutationFourierSum_swap_le W hW x χ hx hχ π (π.symm a) (π.symm b)

#print axioms permutationPrefixFiber
#print axioms permutationCodomainSwap
#print axioms permutationCodomainSwap_apply
#print axioms permutationCodomainSwap_involutive
#print axioms permutationCodomainSwap_prefix
#print axioms permutationPrefixFiberSwap
#print axioms permutationPrefixFiberSwap_two_nonempty
#print axioms permutationCodomainSwap_eq_domainSwap
#print axioms norm_permutationFourierSum_codomainSwap_le

end RBM.Gauss
