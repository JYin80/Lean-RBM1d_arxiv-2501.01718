/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.StochDom

/-!
# High-probability events imply stochastic domination

This file contains the generic bridge from a simultaneous high-probability bound to
stochastic domination.  It is kept below the hierarchy layer so downstream users do not
acquire unrelated hierarchy imports.
-/

namespace RBM

open MeasureTheory Filter

namespace Step1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- **High probability gives `≺`**: if `ξ ≤ ζ` for all `u` w.h.p. (`ζ ≥ 0`), then `ξ ≺ ζ`. -/
theorem stochDom_of_highProb {ξ ζ : ∀ N, U N → Ω → ℝ} (hζ : ∀ N u ω, 0 ≤ ζ N u ω)
    (h : HighProb P (fun N => {ω | ∀ u, ξ N u ω ≤ ζ N u ω})) : StochDom P ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h D hD, eventually_ge_atTop 1] with N hN hN1
  refine (measure_mono ?_).trans hN
  rintro ω ⟨u, hu⟩ hω
  simp only [Set.mem_ofPred_eq] at hω
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hN1) hτ.le
  have := hω u
  nlinarith [hζ N u ω]

end Step1

end RBM
