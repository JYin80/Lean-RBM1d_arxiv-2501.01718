/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBound
import RBM1D.Flow.Hypotheses

/-!
# The minor replacement error `|G_{ll} - G^{(k)}_{ll}| ≺ Ψ²`: the entry bridge

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*: the cost of replacing `G` by the minor `G^{(k)}` in an entry with indices different
from `k`.  This is the error term of the vanishing lemma of §4 (the self-contained proof of the
fluctuation averaging (4.12)).

Everything rests on **(4.9)**, which is already proved in `RBM1D/Green/Minor.lean`
(`RBM.inv_minorMat`) and restated on the full index set in `RBM1D/Green/EntryBound.lean`
(`RBM.greenMinor`, `RBM.greenMinor_sub`):

  `G^{(k)}_{jl} - G_{jl} = - G_{jk} G_{kl} / G_{kk}`.

So the replacement error is *exactly* a product of two entries divided by a diagonal entry.  With
`|G_{jk}|, |G_{kl}| ≤ Ψ` (the off-diagonal part of the local law (2.75)) and the lower bound
`|G_{kk}| ≥ 1/2`, which is contained in the event `Ω(t,c) = {‖G - m‖_max ≤ δ}` of (4.1)
(`RBM.goodSet`, through `RBM.GoodEvent.half_le_norm_diag`), it is at most `2 Ψ²`.

## Main results

* `RBM.Gauss.sub_smul_one_apply` — entries of `G - m` are `G_{ij} - m δ_{ij}`: the bridge
  between the `‖G - m • 1‖_max` shape of the local law (2.75) and the `if`-shape of
  `RBM.GoodEvent`.
-/

namespace RBM.Gauss

open Filter MeasureTheory Matrix

/-! ### The deterministic layer -/

section Det

variable {n : Type*} [DecidableEq n]

/-- Entries of `G - m` are `G_{ij} - m δ_{ij}`: the bridge between the `‖G - m • 1‖_max` shape
of the local law (2.75) (`RBM.Sample.llErr`) and the `if`-shape of `RBM.GoodEvent`. -/
theorem sub_smul_one_apply (A : Matrix n n ℂ) (m : ℂ) (i j : n) :
    (A - m • (1 : Matrix n n ℂ)) i j = A i j - (if i = j then m else 0) := by
  by_cases h : i = j
  · subst h
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, h]

end Det

/-! ### The stochastic layer -/

section Stoch

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {L W : ℕ → ℕ} [∀ N, NeZero (L N)]

end Stoch

end RBM.Gauss
