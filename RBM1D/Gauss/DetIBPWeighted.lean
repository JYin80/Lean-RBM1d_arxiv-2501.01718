/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondStableFlow
import RBM1D.Gauss.MinorDiffCond
import RBM1D.Flow.Thm221Bare
import RBM1D.Flow.EnergyUniform
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.CutoffBounds
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Flow.Eq548Producer
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.LDENetClose

/-!
# Deterministic-scale weighted Gaussian IBP remainder

The diagonal IBP remainder is weighted by `Sblk i i`.  Its stochastic size one is
therefore sufficient when `W⁻¹ ≤ Ψ²`; no fluctuation averaging is used here.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {d : Dims} {N : ℕ} {E u : ℝ}

/-- The actual conditional IBP residual, with the diagonal coefficient kept. -/
theorem norm_condExpDiag_sub_le_two_phi (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (i : d.Idx N) (ω : Ω d) {A Φ : ℝ}
    (hA0 : 0 ≤ A) (hΦ0 : 0 ≤ Φ)
    (hWΦ : ((d.W N : ℝ))⁻¹ ≤ Φ)
    (hoff : ∀ k : d.Idx N, k ≠ i → ‖ibpRem d N E u (i, k) ω‖ ≤ A * Φ)
    (hdiag : ‖ibpRem d N E u (i, i) ω‖ ≤ A) :
    ‖condExpDiag d N u (zt E u) (mE E) i ω
        - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖ ≤ 2 * A * Φ := by
  have hS : Sblk (d.L N) (d.W N) i i ≤ ((d.W N : ℝ))⁻¹ := by
    have h := Sblk_le (L := d.L N) (W := d.W N) i i
    simpa [sbSupport] using h
  calc
    _ ≤ A * Φ + Sblk (d.L N) (d.W N) i i * A :=
      norm_condExpDiag_sub_le_offdiag (gaussIBP d) hE hu0 hu1 i ω
        (mul_nonneg hA0 hΦ0) hoff hdiag
    _ ≤ A * Φ + Φ * A :=
      add_le_add_right (mul_le_mul_of_nonneg_right (hS.trans hWΦ) hA0) _
    _ = 2 * A * Φ := by ring

variable {s t Ψ : ℕ → ℝ}

variable {δ : ℕ → ℝ} {Kenv B : ℝ}

end RBM.Gauss
