/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Index

/-!
# Index bookkeeping for Ward's identity at general `n`

Toward Lemma 3.6, (3.13), for loops of length `n ≥ 3`.  A loop with `σ₁ = +`, `σₙ = -` is
written `fullLoop μ a' x = (+, μ, -; a', x)` with `|μ| = n - 2`, `|a'| = n - 1`; the two
loops on the right-hand side of (3.13) are `pmLoop ± μ a' = (±, μ; a')`.

The identities below say how the cut-and-glue operators act on these shapes.

* For `1 ≤ k < l ≤ n - 1` the left chain of `fullLoop` is again a `fullLoop` (with the same
  last label `x`), and the left chain of `pmLoop ±` is the matching `pmLoop ±`
  (`cutGlueL_fullLoop`, `cutGlueL_pmLoop`).  So summing the left chain over `x` produces
  the two sides of (3.13) one level down.
* For `2 ≤ k` the right chain does not see the first charge (`cutGlueR_fullLoop`); for
  `k = 1` it sees `+` (`cutGlueR_fullLoop_one`).
* For the cuts `(k, n)`: the left chain is a `fullLoop` of length `k + 1`
  (`cutGlueL_fullLoop_last`), and the right chain is the whole loop (`k = 1`) or the rotation
  of a left chain of `pmLoop -` (`cutGlueR_fullLoop_last`, `cutGlueR_fullLoop_last_one`).
* The right chain of `pmLoop ±` at `(1, m)` is the `pmLoop ±` of the left chain of
  `fullLoop` at `(m, n)` (`cutGlueR_pmLoop_one`).
-/

namespace RBM

namespace LoopIdx

variable {α : Type*}

/-- `(+, μ, -; a', x)`: a loop with first charge `+` and last charge `-`. -/
def fullLoop (μ : List Bool) (a' : List α) (x : α) : LoopIdx α :=
  ⟨true :: μ ++ [false], a' ++ [x]⟩

/-- `(s, μ; a')`: the loops `σ^±` on the right-hand side of (3.13). -/
def pmLoop (s : Bool) (μ : List Bool) (a' : List α) : LoopIdx α := ⟨s :: μ, a'⟩

/-- The middle charges after cutting at `(k, l)`. -/
def cutMu (k l : ℕ) (μ : List Bool) : List Bool := μ.take (k - 1) ++ μ.drop (l - 2)

/-- The labels (without the last) after cutting at `(k, l)` and gluing with `b`. -/
def cutA (k l : ℕ) (b : α) (a' : List α) : List α := a'.take (k - 1) ++ b :: a'.drop (l - 1)

variable (μ : List Bool) (a' : List α) (x b : α) {k l : ℕ}

theorem cutGlueL_fullLoop (hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ a'.length) :
    (fullLoop μ a' x).cutGlueL k l b = fullLoop (cutMu k l μ) (cutA k l b a') x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
  simp only [fullLoop, cutGlueL, cutMu, cutA, Nat.add_sub_cancel, List.take_succ_cons,
    show l + 2 - 1 = l + 1 by omega, show l + 2 - 2 = l by omega, List.drop_succ_cons,
    List.cons_append, List.append_assoc]
  congr 1
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]

theorem cutGlueL_pmLoop (s : Bool) (_hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) :
    (pmLoop s μ a').cutGlueL k l b = pmLoop s (cutMu k l μ) (cutA k l b a') := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
  simp only [pmLoop, cutGlueL, cutMu, cutA, Nat.add_sub_cancel, List.take_succ_cons,
    show l + 2 - 1 = l + 1 by omega, show l + 2 - 2 = l by omega, List.drop_succ_cons,
    List.cons_append]

theorem cutGlueR_fullLoop (s : Bool) (hμ : μ.length + 1 = a'.length) (hk : 2 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) :
    (fullLoop μ a' x).cutGlueR k l b = (pmLoop s μ a').cutGlueR k l b := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [fullLoop, pmLoop, cutGlueR, show k + 2 - 1 = k + 1 by omega, List.drop_succ_cons,
    List.cons_append]
  congr 1
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem cutGlueR_fullLoop_one (hμ : μ.length + 1 = a'.length) (hl1 : 1 < l)
    (hl : l ≤ a'.length) :
    (fullLoop μ a' x).cutGlueR 1 l b = (pmLoop true μ a').cutGlueR 1 l b := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [fullLoop, pmLoop, cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel,
    List.take_succ_cons, List.cons_append]
  congr 1
  · rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (by omega)]

theorem cutGlueL_fullLoop_last (hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkn : k ≤ a'.length) :
    (fullLoop μ a' x).cutGlueL k (a'.length + 1) b
      = fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [b]) x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [fullLoop, cutGlueL, Nat.add_sub_cancel, List.take_succ_cons, List.cons_append]
  congr 1
  · rw [List.take_append_of_le_length (by omega), ← hμ, List.drop_succ_cons, List.drop_left]
  · rw [List.take_append_of_le_length (by omega), List.drop_left]
    simp

theorem cutGlueR_fullLoop_last_one (hμ : μ.length + 1 = a'.length) :
    (fullLoop μ a' x).cutGlueR 1 (a'.length + 1) b = fullLoop μ a' b := by
  simp only [fullLoop, cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel]
  congr 1
  · rw [List.take_of_length_le (by simp; omega)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length]

/-- The right chain of the cut `(k, n)`, `k ≥ 2`, is the rotation of the left chain of
`pmLoop -` at `(1, k)`: both are `(σ_k, …, σ_{n-1}, -; a_k, …, a_{n-1}, b)` up to rotation. -/
theorem cutGlueR_fullLoop_last (hμ : μ.length + 1 = a'.length) (hk : 2 ≤ k)
    (hkn : k ≤ a'.length) :
    (fullLoop μ a' x).cutGlueR k (a'.length + 1) b
      = rot ((pmLoop false μ a').cutGlueL 1 k b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [fullLoop, pmLoop, cutGlueR, cutGlueL, show k + 2 - 1 = k + 1 by omega,
    List.drop_succ_cons, List.cons_append, Nat.sub_self, List.take_zero, List.nil_append,
    List.take_succ_cons, List.take_zero]
  rw [rot_mk_cons]
  congr 1
  · rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]

/-- The right chain never contains the last label `x`. -/
theorem cutGlueR_fullLoop_indep (y : α) (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ a'.length + 1) :
    (fullLoop μ a' x).cutGlueR k l b = (fullLoop μ a' y).cutGlueR k l b := by
  simp only [fullLoop, cutGlueR]
  congr 1
  rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)]

/-- The right chain of `pmLoop s` at `(1, m)` is `pmLoop s` of the base of the left chain of
`fullLoop` at `(m, n)` (`cutGlueL_fullLoop_last`). -/
theorem cutGlueR_pmLoop_one (s : Bool) (hm : 1 < l) :
    (pmLoop s μ a').cutGlueR 1 l b = pmLoop s (μ.take (l - 1)) (a'.take (l - 1) ++ [b]) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [pmLoop, cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel,
    List.take_succ_cons]

end LoopIdx

end RBM
