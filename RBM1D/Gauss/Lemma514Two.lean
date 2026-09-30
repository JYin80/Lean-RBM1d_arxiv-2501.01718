/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Alt

/-!
# Lemma 5.14 at n = 2 from the endpoint, and the n = 2 charge split

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, Lemma 5.14: the charge split at loop length `n = 2`.

## Main results

* `RBM.Gauss.Grid.sigma_split_two` — every `σ : Fin 2 → Bool` is non-alternating
  (`σ 0 = σ 1`) or one of the two alternating charges `sigmaAltGen 2` / `sigmaAltGen' 2`.
-/

open MeasureTheory Filter

namespace RBM.Gauss

end RBM.Gauss

namespace RBM.Gauss.Grid

/-- Every charge `σ : Fin 2 → Bool` is either non-alternating (`σ 0 = σ 1`) or one of
the two alternating charges `sigmaAltGen 2`, `sigmaAltGen' 2`. `Fin 2 → Bool` has exactly four
elements: `(F,F)` and `(T,T)` are non-alternating, `(T,F) = sigmaAltGen 2` and
`(F,T) = sigmaAltGen' 2`. -/
theorem sigma_split_two (sigma : Fin 2 → Bool) :
    sigma 0 = sigma 1 ∨ sigma = sigmaAltGen 2 ∨ sigma = sigmaAltGen' 2 := by
  cases h0 : sigma 0 <;> cases h1 : sigma 1
  · exact Or.inl rfl
  · refine Or.inr (Or.inr ?_)
    funext i
    fin_cases i <;> simp [sigmaAltGen', h0, h1]
  · refine Or.inr (Or.inl ?_)
    funext i
    fin_cases i <;> simp [sigmaAltGen, h0, h1]
  · exact Or.inl rfl

end RBM.Gauss.Grid

namespace RBM.Gauss

end RBM.Gauss

