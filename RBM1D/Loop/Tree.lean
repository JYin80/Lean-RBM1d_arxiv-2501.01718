/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Crossing
import RBM1D.Loop.Primitive

/-!
# Tree values: the star graph and the case `n = 4`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 3.3 and the
`n = 4` formula after Lemma 3.4, for the trees that are needed to pin down the conventions.

Indices are `0`-based: the polygon vertex `a i` (the paper's `a_{i+1}`) lies between the
regions `i` and `i + 1` (mod `n`), so the boundary edge at `a i` carries
`f_t = Θ_{t m(σ_i) m(σ_{i+1})}` (Definition 3.3, item 1).

## Two conventions, both checked against the primitive equation

* **Boundary indices in the `n = 4` display.** The boundary factor at `a_i` is
  `Θ_{t m_i m_{i+1}}`, as in Definition 3.3 (item 1) and in the display after Figure 6; with
  these factors the tree values solve (2.48).
* **`n = 2`.** For the `2`-gon the tree is the single edge `a₁ — a₂` with no internal vertex
  (Definition 3.3), and then Lemma 3.4 holds: the solution of (2.55) is `Θ_{a₁a₂}`
  (Example 2.15, `RBM.hasDerivAt_kTwo`).  The star formula would give `(Θ²)_{a₁a₂}`, which does
  *not* solve (2.55).

## Main definitions

* `RBM.thetaEdge` : `Θ_{t m(s) m(s')}`
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

/-- `Θ_{t m(s) m(s')}`, the value of an edge between regions with charges `s`, `s'`. -/
noncomputable def thetaEdge (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : Matrix (ZMod L) (ZMod L) ℂ :=
  Theta L (t * (m s * m s'))

theorem thetaEdge_comm (m : Bool → ℂ) (t : ℝ) (s s' : Bool) :
    thetaEdge L m t s s' = thetaEdge L m t s' s := by
  rw [thetaEdge, thetaEdge, mul_comm (m s)]

section Two

end Two

section Four

variable (m : Bool → ℂ) (t : ℝ) (σ : Fin 4 → Bool) (a : Fin 4 → ZMod L)

end Four

section General

/-!
### The general tree value (Definition 3.3)

Following the proof of Lemma 3.2, the value of the tree with pairing set `F` is defined by
recursion on `F` rather than by building the tree.  A polygon is stored as its region charges
`rs` (region `k` holds the `k`-th polygon edge) and its vertices `vs`, each with a label and a
boundary matrix; vertex `k` lies between regions `k` and `k + 1` (mod `n`).

* `F = []`: the star, `∑_b ∏_k (M_k)_{a_k b}`.
* `(i, j) :: F` with `(i, j)` a diagonal: the internal edge between regions `i` and `j`
  splits the polygon into the left piece (regions `i, …, j`, vertices `i, …, j - 1`) and the
  right piece (regions `j, …, n - 1, 0, …, i`, vertices `j, …, n - 1, 0, …, i - 1`), each
  closed up by a new vertex with the summed label `y`.  On the left the new vertex carries
  `(Θ_{t m_i m_j} - 1)ᵀ` and on the right the identity, which pins the right centre to `y`;
  together they produce the single internal edge `(Θ_{t m_i m_j} - 1)` between the centres.
  The remaining pairs go to the piece containing them.
* A head `(i, j)` that is not a diagonal is skipped.

**Termination.**  A diagonal has `j - i ≥ 2` and is not `(0, n - 1)` (`RBM.IsDiag` excludes
adjacent regions, including the wrap-around pair).  Hence the pieces have `j - i + 1 ≤ n - 1`
and `n - (j - i) + 1 ≤ n - 1` regions, and `n + |F|` decreases.  This is the entire
termination argument, and the reason adjacent pairs are not diagonals.

**Choice of pivot.**  The pivot is the head of the list; the diagonals of a `Finset` are listed
in lexicographic order, so the value of a `Finset` is well defined without proving
independence of the pivot.  Independence (needed later, e.g. to expand along another
diagonal) is not proved here.
-/

end General

section Acceptance

variable (m : Bool → ℂ) (t : ℝ) (σ : Fin 4 → Bool) (a : Fin 4 → ZMod L)

end Acceptance

end RBM
