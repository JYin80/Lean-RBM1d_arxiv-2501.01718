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

end RBM
