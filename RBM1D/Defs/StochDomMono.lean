/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.StochDom

/-!
# A monotonicity helper for stochastic domination

This file contains the generic monotonicity lemma used by the Step 3 flow estimates, without
introducing any dependency on the flow hierarchy.
-/

namespace RBM

open MeasureTheory Filter

namespace Step3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- `ξ ≺ ζ` and `ζ ≤ C ζ'` (eventually, pointwise) give `ξ ≺ ζ'`. -/
theorem stochDom_mono {ξ ζ ζ' : ∀ N, U N → Ω → ℝ} (hζ' : ∀ N u ω, 0 ≤ ζ' N u ω) (C : ℝ)
    (hle : ∀ᶠ N : ℕ in atTop, ∀ u ω, ζ N u ω ≤ C * ζ' N u ω) (h : StochDom P ξ ζ) :
    StochDom P ξ ζ' := by
  refine StochDom.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, eventually_le_rpow C (half_pos hτ)] with N hN hC
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc (N : ℝ) ^ (τ / 2) * ζ N u ω ≤ (N : ℝ) ^ (τ / 2) * (C * ζ' N u ω) :=
        mul_le_mul_of_nonneg_left (hN u ω) hpos
    _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ζ' N u ω) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (hζ' N u ω)) hpos
    _ = (N : ℝ) ^ τ * ζ' N u ω := by rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]
    _ < ξ N u ω := hu

end Step3

end RBM
