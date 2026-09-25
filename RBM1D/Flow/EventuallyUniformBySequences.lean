/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib

/-!
# Eventual pointwise uniformity from every admissible sequence

This is a logical diagonal argument.  The predicates `A0`, `A1`, and `P` have no
probabilistic interpretation here.  In particular, the conclusion gives a common
eventual index for the pointwise assertions `P n z`; it does not construct a
simultaneous event in a probability space.
-/

namespace RBM

open Filter

/-- If every sequence satisfying `A0` everywhere and `A1` eventually satisfies
`P` eventually, then `P` holds eventually at every point satisfying both
conditions.  The base sequence fills indices at which no counterexample is
selected; its `A1` condition need only hold eventually. -/
theorem eventually_forall_of_forall_sequences {α : Type*}
    (A0 A1 P : ℕ → α → Prop) (b : ℕ → α)
    (hb0 : ∀ n, A0 n (b n))
    (hb1 : ∀ᶠ n : ℕ in atTop, A1 n (b n))
    (hseq : ∀ f : ℕ → α, (∀ n, A0 n (f n)) →
      (∀ᶠ n : ℕ in atTop, A1 n (f n)) →
      ∀ᶠ n : ℕ in atTop, P n (f n)) :
    ∀ᶠ n : ℕ in atTop, ∀ z, A0 n z → A1 n z → P n z := by
  classical
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  let bad (n : ℕ) : Prop := ∃ z, A0 n z ∧ A1 n z ∧ ¬ P n z
  have hbad : ∃ᶠ n : ℕ in atTop, bad n :=
    hnot.mono fun n hn => by
      simp only [not_forall] at hn
      obtain ⟨z, ha0, ha1, hp⟩ := hn
      exact ⟨z, ha0, ha1, hp⟩
  let f (n : ℕ) : α := if hn : bad n then hn.choose else b n
  have hf0 : ∀ n, A0 n (f n) := by
    intro n
    by_cases hn : bad n
    · simpa [f, hn] using (hn.choose_spec : A0 n hn.choose ∧ A1 n hn.choose ∧ ¬ P n hn.choose).1
    · simpa [f, hn] using hb0 n
  have hf1 : ∀ᶠ n : ℕ in atTop, A1 n (f n) := by
    filter_upwards [hb1] with n hbn
    by_cases hn : bad n
    · simpa [f, hn] using (hn.choose_spec : A0 n hn.choose ∧ A1 n hn.choose ∧ ¬ P n hn.choose).2.1
    · simpa [f, hn] using hbn
  have hfP := hseq f hf0 hf1
  obtain ⟨n, hn, hp⟩ := (hbad.and_eventually hfP).exists
  have hfn : f n = hn.choose := by simp [f, hn]
  exact (hn.choose_spec : A0 n hn.choose ∧ A1 n hn.choose ∧ ¬ P n hn.choose).2.2
    (hfn ▸ hp)

private def boolA0 (_ : ℕ) (_ : Bool) : Prop := True
private def boolA1 (_ : ℕ) (_ : Bool) : Prop := True
private def boolP (n : ℕ) (z : Bool) : Prop := n ≠ 0 ∨ z = false

/-- Nondegenerate satisfiability: both Boolean values are admissible even at
`n = 0`, where `true` is a counterexample.  All points satisfy `P` from `n = 1`
onward, so the sequence hypothesis and the eventual conclusion both hold. -/
theorem eventually_uniform_bool_satisfiable :
    (∀ n, boolA0 n false) ∧
    (∀ᶠ n : ℕ in atTop, boolA1 n false) ∧
    boolA0 0 false ∧ boolA1 0 false ∧
    boolA0 0 true ∧ boolA1 0 true ∧ ¬ boolP 0 true ∧
    (∀ f : ℕ → Bool, (∀ n, boolA0 n (f n)) →
      (∀ᶠ n : ℕ in atTop, boolA1 n (f n)) →
      ∀ᶠ n : ℕ in atTop, boolP n (f n)) ∧
    (∀ᶠ n : ℕ in atTop, ∀ z, boolA0 n z → boolA1 n z → boolP n z) := by
  have hb0 : ∀ n, boolA0 n false := by simp [boolA0]
  have hb1 : ∀ᶠ n : ℕ in atTop, boolA1 n false :=
    Eventually.of_forall (by simp [boolA1])
  have hseq : ∀ f : ℕ → Bool, (∀ n, boolA0 n (f n)) →
      (∀ᶠ n : ℕ in atTop, boolA1 n (f n)) →
      ∀ᶠ n : ℕ in atTop, boolP n (f n) := by
    intro f _ _
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Or.inl (Nat.ne_of_gt hn)
  refine ⟨hb0, hb1, trivial, trivial, trivial, trivial, ?_, hseq, ?_⟩
  · simp [boolP]
  · exact eventually_forall_of_forall_sequences boolA0 boolA1 boolP
      (fun _ => false) hb0 hb1 hseq

#print axioms RBM.eventually_forall_of_forall_sequences
#print axioms RBM.eventually_uniform_bool_satisfiable

end RBM
