/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic

/-!
# Non-crossing diagonal sets: the combinatorial content of Lemma 3.2

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 3.1 and Lemma 3.2.

The paper's `T SP (P_a)` is the set of trees attached to equivalence classes of canonical
partitions of the polygon `P_a`.  Lemma 3.2 says that such a tree `Γ_a` is determined by
its set `F(Γ_a)` of non-adjacent pairs, that `F(Γ_a)` has no crossing pairs, and that
every crossing-free set of non-adjacent pairs is realized.  So
`T SP (P_a) ≃ {F ⊆ diagonals : F crossing-free}`, and we take the right-hand side as the
*definition* of `TSP` (see `docs/paper-deltas.md`).  The planar geometry of Definition 3.1
is not formalized.

Vertices are `0`-based: the paper's vertex `i ∈ {1, …, n}` is our `i - 1 : Fin n`.
A diagonal is stored as an ordered pair `(i, j)` with `i < j`.

## Main definitions

* `RBM.IsDiag n i j` : `{i, j}` is a diagonal of the `n`-gon (`i < j`, not adjacent in `ℤ_n`)
* `RBM.diagonals n` : the finset of diagonals
* `RBM.Crossing e f` : the paper's condition `i < k < j < l` or `k < i < l < j`
* `RBM.CrossingFree F` : no two pairs of `F` cross
* `RBM.TSP n` : crossing-free subsets of `diagonals n`

## Main results

* `RBM.crossing_comm`, `RBM.not_crossing_self` : `Crossing` is symmetric and irreflexive
* `RBM.TSP_three`, `RBM.TSP_four` : `TSP 3 = {∅}`, `TSP 4 = {∅, {(0,2)}, {(1,3)}}` (Figure 6)
* `RBM.card_TSP_five`, `RBM.card_TSP_six` : `11` and `45` (small Schröder numbers)
-/

namespace RBM

/-- `{i, j}` (with `i < j`) is a diagonal of the `n`-gon: the vertices are not adjacent
modulo `n`.  Note `{0, n - 1}` is a side, not a diagonal. -/
def IsDiag (n : ℕ) (i j : Fin n) : Prop :=
  i < j ∧ j.val ≠ i.val + 1 ∧ ¬(i.val = 0 ∧ j.val = n - 1)

instance (n : ℕ) (i j : Fin n) : Decidable (IsDiag n i j) := by
  unfold IsDiag; infer_instance

/-- The diagonals of the `n`-gon, as ordered pairs `(i, j)` with `i < j`. -/
def diagonals (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => IsDiag n p.1 p.2

/-- The crossing condition of Lemma 3.2: `(i, j)` and `(k, l)` cross if
`i < k < j < l` or `k < i < l < j`, with the order of `ℕ` (not of `ℤ_n`).
Pairs sharing an endpoint do not cross. -/
def Crossing {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨ (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

instance {n : ℕ} (e f : Fin n × Fin n) : Decidable (Crossing e f) := by
  unfold Crossing; infer_instance

/-- No two pairs of `F` cross. -/
def CrossingFree {n : ℕ} (F : Finset (Fin n × Fin n)) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, ¬Crossing e f

instance {n : ℕ} (F : Finset (Fin n × Fin n)) : Decidable (CrossingFree F) := by
  unfold CrossingFree; infer_instance

/-- `T SP (P_a)` for the `n`-gon, via Lemma 3.2: the crossing-free sets of diagonals. -/
def TSP (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  (diagonals n).powerset.filter CrossingFree

theorem crossing_comm {n : ℕ} (e f : Fin n × Fin n) : Crossing e f ↔ Crossing f e := by
  unfold Crossing; tauto

theorem not_crossing_self {n : ℕ} (e : Fin n × Fin n) : ¬Crossing e e := by
  unfold Crossing; omega

theorem mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} :
    F ∈ TSP n ↔ F ⊆ diagonals n ∧ CrossingFree F := by
  simp [TSP]

theorem empty_mem_TSP (n : ℕ) : (∅ : Finset (Fin n × Fin n)) ∈ TSP n := by
  simp [mem_TSP, CrossingFree]

/-- Pairs sharing an endpoint do not cross: the inequalities in Lemma 3.2 are strict. -/
example : ¬Crossing ((0, 2) : Fin 5 × Fin 5) (2, 4) := by decide
example : ¬Crossing ((0, 2) : Fin 5 × Fin 5) (0, 3) := by decide
example : Crossing ((0, 2) : Fin 4 × Fin 4) (1, 3) := by decide

/-- `{0, n - 1}` is a side, not a diagonal. -/
example : ¬IsDiag 5 0 4 := by decide

/-- A triangle has no diagonals. -/
theorem TSP_three : TSP 3 = {∅} := by decide

/-- The three trees of Figure 6: the star, and the two single diagonals `{1,3}`, `{2,4}`
(paper's `1`-based labels).  The two diagonals cross, so they cannot coexist. -/
theorem TSP_four : TSP 4 = {∅, {(0, 2)}, {(1, 3)}} := by decide

/-- Small Schröder numbers `1, 3, 11, 45, …` count dissections of the polygon. -/
theorem card_TSP_five : (TSP 5).card = 11 := by decide

set_option maxRecDepth 10000 in
theorem card_TSP_six : (TSP 6).card = 45 := by decide

end RBM
