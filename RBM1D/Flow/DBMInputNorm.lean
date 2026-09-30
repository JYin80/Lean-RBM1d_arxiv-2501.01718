/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.DBMInput
import RBM1D.Flow.Step1Regularity
import RBM1D.Flow.Step1Conditioning
import RBM1D.Flow.Step1Rescale

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

/-- **[51, Theorem 2.2] at unit density.** The premises are those of [51, Theorem 2.2]. The
conclusion is (2.9) with the factors `ρ_fc^{-k}`, `ρ_sc^{-k}` (`docs/PAPER-VS-LEAN.md` §4.2):
equivalently, the test function is dilated by each side's own density. -/
def LSY22' : Prop :=
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ N, d.Idx N → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ N in atTop,
      msize d N ^ δ / msize d N ≤ g N ∧ g N ≤ msize d N ^ (-δ) ∧ G N ≤ msize d N ^ (-δ) ∧
      g N * msize d N ^ σ ≤ t N ∧ t N ≤ msize d N ^ (-σ) * G N ^ 2 ∧ |E N| ≤ q * G N ∧
      IsRegular51 (v N) (g N) (G N) c C CV ∧ IsFreeConv51 (v N) (t N) (m N) ∧
      Tendsto (fun η : ℝ => (m N ⟨E N, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ N))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, RBM.IsTestFun O →
      Tendsto (fun N =>
        RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (t N))
            (dbmMatrix_isHermitian d N (v N) (t N)) k (fun β => O (fun j => ρ N * β j)) (E N) -
          RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
            (fun β => O (fun j => rhoSc (E N) * β j)) (E N))
        atTop (𝓝 0)

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
