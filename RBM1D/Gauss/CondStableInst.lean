/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondDom
import RBM1D.Gauss.Lemma41Glue

/-!
# The cardinality bound for off-diagonal index pairs

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4 (the integration-by-parts input of (4.5)).

`RBM.Gauss.card_OffPair_le`: the number of off-diagonal index pairs `RBM.OffPair` is at most
`N²` eventually, which is the cardinality bound of Definition 2.1 (i) for a union over these
pairs.
-/

namespace RBM.Gauss

open MeasureTheory Filter

section Stab

variable {E t : ℝ} {δ : ℕ → ℝ} {d : Dims} {N : ℕ}

end Stab

section Assembly

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- The Definition 2.1 (i) cardinality bound for `RBM.OffPair`. -/
theorem card_OffPair_le (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (OffPair d.L d.W N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  filter_upwards [card_Idx_prod_le d] with N hN
  refine le_trans ?_ hN
  exact_mod_cast Fintype.card_subtype_le (fun p : d.Idx N × d.Idx N => p.1 ≠ p.2)

end Assembly

end RBM.Gauss
