/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Layer

/-!
# Regression tests for Definition 3.8 (layers by long edges)

`decide` checks of `RBM.Flong` / `RBM.TSPlong` on small polygons with alternating charges,
against counts computed independently (a brute-force enumeration of non-crossing diagonal
sets, `σ_i ≠ σ_j` for a long edge):

* `n = 4`, `σ = (+,-,+,-)`: both diagonals join equal charges, so all three trees form the
  single-molecule layer `π = ∅` (the paper's example after (3.42)).
* `n = 5`, `σ = (+,-,+,-,+)`: layers of sizes `5, 3, 3` (`π = ∅, {(0,3)}, {(1,4)}`).
* `n = 6`, `σ = (+,-,+,-,+,-)`: the `45` trees split as `18` single-molecule trees and `9` for
  each long diagonal `(0,3)`, `(1,4)`, `(2,5)` (these pairwise cross).
-/

namespace RBM.Numeric

/-- Alternating charges: `+` at even (0-based) positions. -/
def alt (n : ℕ) : Fin n → Bool := fun i => decide (i.val % 2 = 0)

example : TSPlong 4 (alt 4) ∅ = TSP 4 := by decide

example : (TSPlong 5 (alt 5) ∅).card = 5 := by decide
example : (TSPlong 5 (alt 5) {((0 : Fin 5), (3 : Fin 5))}).card = 3 := by decide
example : (TSPlong 5 (alt 5) {((1 : Fin 5), (4 : Fin 5))}).card = 3 := by decide

example : (TSPlong 6 (alt 6) ∅).card = 18 := by decide
example : (TSPlong 6 (alt 6) {((0 : Fin 6), (3 : Fin 6))}).card = 9 := by decide
example : (TSPlong 6 (alt 6) {((1 : Fin 6), (4 : Fin 6))}).card = 9 := by decide
example : (TSPlong 6 (alt 6) {((2 : Fin 6), (5 : Fin 6))}).card = 9 := by decide

/-- Two crossing long diagonals never occur together. -/
example : TSPlong 6 (alt 6) {((0 : Fin 6), (3 : Fin 6)), ((1 : Fin 6), (4 : Fin 6))} = ∅ := by
  decide

end RBM.Numeric
