/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Alt
import RBM1D.Hierarchy.SumZeroDyn

/-!
# Exhaustiveness of the charge patterns

Pure finite combinatorics on cyclic Boolean sequences: for every `n ≥ 3` and every
`σ : Fin n → Bool`, either `σ` has a cyclic repeat (`SumZeroDyn.NonAlt`'s condition after the
`n = m + 2` re-indexing), or `n` is even and `σ` is one of the two alternating charges
`sigmaAltGen n` / `sigmaAltGen' n` (`RBM1D/Gauss/Lemma514Alt.lean`).

## Main results

* `sigma_exhaustive` — the `Fin n` form of the dichotomy, `n ≥ 3`.
* `sigma_exhaustive_nonAlt` — the `SumZeroDyn.NonAlt` form on `Fin (m + 2)`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM.SumZeroDyn

/-! ### Helper: the cyclic successor of a `Fin n` index, in terms of its `Nat` value -/

section FinSucc

/-- The value of `(1 : Fin n)`, for `2 ≤ n`. -/
private theorem val_one_of_two_le {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) : (1 : Fin n).val = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

/-- The value of the cyclic successor in `Fin n` (`n ≥ 2`): the naive successor, wrapped to `0`
at the last index. Reproved locally (the analogous fact in `Lemma514Alt.lean` is `private` to
that file). -/
private theorem val_succ_eq {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) (i : Fin n) :
    (i + 1).val = if i.val + 1 = n then 0 else i.val + 1 := by
  have h1 : (1 : Fin n).val = 1 := val_one_of_two_le hn2
  have hlt := i.isLt
  rw [Fin.val_add_eq_ite, h1]
  split_ifs <;> omega

/-- Parity flips under `+ 1` (as `decide`d Booleans): a small, fixed-shape numeric fact, no
`decide` on a free/universally-quantified variable (the two branches are on the *value* of
`j % 2 ∈ {0, 1}`, a concrete case split, not on `n`). -/
private theorem decide_succ_mod_two (j : ℕ) :
    decide ((j + 1) % 2 = 1) = !decide (j % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have h1 : (j + 1) % 2 = 1 := by omega
    rw [h1, h]; rfl
  · have h1 : (j + 1) % 2 = 0 := by omega
    rw [h1, h]; rfl

/-- `j % 2 = 1` is the Boolean complement of `j % 2 = 0`. -/
private theorem decide_mod_two_compl (j : ℕ) :
    decide (j % 2 = 1) = !decide (j % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> rw [h] <;> rfl

end FinSucc

/-! ### The exhaustiveness dichotomy -/

section Exhaustive

/-- **Exhaustiveness of the charge patterns**: for every `n ≥ 3` and every
`σ : Fin n → Bool`, either `σ` has a cyclic repeat, or `n` is even and `σ` is one of the two
alternating charges. -/
theorem sigma_exhaustive {n : ℕ} [NeZero n] (hn : 3 ≤ n) (σ : Fin n → Bool) :
    (∃ k : Fin n, σ k = σ (k + 1)) ∨ (Even n ∧ (σ = sigmaAltGen n ∨ σ = sigmaAltGen' n)) := by
  by_cases hrep : ∃ k : Fin n, σ k = σ (k + 1)
  · exact Or.inl hrep
  · right
    have hn2 : 2 ≤ n := by omega
    simp only [not_exists] at hrep
    -- `σ (k + 1) = !σ k` for every `k`.
    have hstep : ∀ k : Fin n, σ (k + 1) = !σ k := by
      intro k
      have hne := hrep k
      cases hk : σ k <;> cases hk1 : σ (k + 1) <;> simp_all
    have h0 : (0 : Fin n).val = 0 := by simp
    -- the pointwise formula `σ ⟨j,_⟩ = xor (σ 0) (decide (j % 2 = 1))`, by induction on `j`.
    have hform : ∀ j : ℕ, ∀ hj : j < n, σ ⟨j, hj⟩ = xor (σ (0 : Fin n)) (decide (j % 2 = 1)) := by
      intro j
      induction j with
      | zero =>
        intro hj
        have : (⟨0, hj⟩ : Fin n) = (0 : Fin n) := by
          apply Fin.ext; simp
        rw [this]; simp
      | succ j ih =>
        intro hj
        have hjlt : j < n := by omega
        have hsucc := hstep ⟨j, hjlt⟩
        have hval := val_succ_eq hn2 (⟨j, hjlt⟩ : Fin n)
        have hne : j + 1 ≠ n := by omega
        simp only [hne, ite_false] at hval
        have heq : (⟨j, hjlt⟩ + 1 : Fin n) = (⟨j + 1, hj⟩ : Fin n) := by
          apply Fin.ext; rw [hval]
        rw [heq] at hsucc
        rw [hsucc, ih hjlt, decide_succ_mod_two]
        cases σ (0 : Fin n) <;> cases decide (j % 2 = 1) <;> rfl
    -- closing the cycle at `k = n - 1` forces `n` even.
    have hlast : n - 1 < n := by omega
    have hcyc := hstep (⟨n - 1, hlast⟩ : Fin n)
    have hval := val_succ_eq hn2 (⟨n - 1, hlast⟩ : Fin n)
    have heqn : n - 1 + 1 = n := by omega
    simp only [heqn, ite_true] at hval
    have hzero : (⟨n - 1, hlast⟩ + 1 : Fin n) = (0 : Fin n) := by
      apply Fin.ext; rw [hval]; simp
    rw [hzero] at hcyc
    have hform_last := hform (n - 1) hlast
    rw [hform_last] at hcyc
    have heven : (n - 1) % 2 = 1 := by
      by_contra hcon
      have hp : decide ((n - 1) % 2 = 1) = false := by
        simp only [decide_eq_false_iff_not]; exact hcon
      rw [hp, Bool.xor_false] at hcyc
      cases hb : σ (0 : Fin n) <;> simp [hb] at hcyc
    have hn_even : Even n := by
      rw [Nat.even_iff]; omega
    refine ⟨hn_even, ?_⟩
    -- with `n` even, `σ 0` determines the whole pattern.
    cases hb0 : σ (0 : Fin n) with
    | true =>
      left
      funext i
      have hi := hform i.val i.isLt
      rw [hb0] at hi
      have hiv : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.eta i i.isLt
      rw [hiv] at hi
      rw [hi, Bool.true_xor]
      simp only [sigmaAltGen]
      rw [decide_mod_two_compl i.val, Bool.not_not]
    | false =>
      right
      funext i
      have hi := hform i.val i.isLt
      rw [hb0] at hi
      have hiv : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.eta i i.isLt
      rw [hiv] at hi
      rw [hi, Bool.false_xor]
      simp only [sigmaAltGen']
      exact decide_mod_two_compl i.val

/-- The `SumZeroDyn.NonAlt` restatement on `Fin (m + 2)`: for `m ≥ 1`
(so `n := m + 2 ≥ 3`), either `σ` is `NonAlt` or `n` is even and `σ` is one of the two
alternating charges. -/
theorem sigma_exhaustive_nonAlt {m : ℕ} (hm : 1 ≤ m) (σ : Fin (m + 2) → Bool) :
    NonAlt σ ∨ (Even (m + 2) ∧ (σ = sigmaAltGen (m + 2) ∨ σ = sigmaAltGen' (m + 2))) := by
  have : NeZero (m + 2) := ⟨by omega⟩
  have h := sigma_exhaustive (n := m + 2) (by omega) σ
  simpa only [NonAlt] using h

end Exhaustive

/-! ### Nondegeneracy: compiled witnesses at `n = 3` and `n = 4` -/

section Nondegeneracy

end Nondegeneracy

end RBM.Gauss.Grid

end

