/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

module

public import RBM1D.MainDefs
public import RBM1D.Flow.DBMInput
public import RBM1D.Flow.Step1Regularity
public import RBM1D.Flow.Step1Conditioning
public import RBM1D.Flow.Step1Rescale

@[expose] public section

/-!
# [51, Theorem 2.2] at unit density

The literal [51, (2.9)] lacks the factors `ρ_fc^{-k}`, `ρ_sc^{-k}`: with [51]'s
probability-marginal `p^{(k)}`, the two sides of the literal (2.9) tend to `ρ_fc^k I(O)` and
`ρ_sc^k I(O)` respectively, so a literal transcription is false whenever `ρ_fc ≠ ρ_sc`
(`docs/PAPER-VS-LEAN.md` §4.1–§4.3). This file states the corrected hypothesis `LSY22'`, dilating
each side's test function by its own density instead of multiplying by an extra `ρ^k` (which is
what `scaledPairing` does).
-/

open MeasureTheory Filter Matrix Topology

namespace RBM.Gauss

variable (d : Dims)

/-- The reference for Step 1: the GUE at `0`, with the test function dilated by
`ρ_sc(0)/ρ_sc(E₀)`. -/
noncomputable def gue0Ref' (N k : ℕ) (O : (Fin k → ℝ) → ℝ) (E₀ : ℝ) : ℝ :=
  RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
    (fun β => O (fun j => (rhoSc 0 / rhoSc E₀) * β j)) 0

/-- `scaledPairing` is `ρ^k` times the dilated `corrPairing` (unfolding). -/
theorem scaledPairing_eq_pow_mul {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*} [Fintype n]
    [DecidableEq n] (Pm : Measure Ω') (Hm : Ω' → Matrix n n ℂ) (hH : ∀ ω, (Hm ω).IsHermitian)
    (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E ρ : ℝ) :
    scaledPairing Pm Hm hH k O E ρ =
      ρ ^ k * RBM.corrPairing Pm Hm hH k (fun β => O (fun j => ρ * β j)) E :=
  rfl

end RBM.Gauss
