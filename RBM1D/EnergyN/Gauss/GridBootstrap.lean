/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridBootstrap
import RBM1D.EnergyN.Gauss.Step2Eq557

/-!
# The pointwise grid bound gives (2.76), at an `N`-dependent energy

The predicate `RBM.Gauss.Grid.GridPointwise'N` and `RBM.Gauss.Grid.hpt_of_gridPointwise'N`, which
derives from it the bound of (2.76) at each time, at an `N`-dependent energy `E : ℕ → ℝ`. No
energy-dependent constant is fixed here. The only external dependency of
`hpt_of_gridPointwise'N` is `RBM.Gauss.Grid.pg_bad_eq_flow` (`Gauss/GridBootstrap.lean`), a
deterministic per-fixed-`N` fact (`{E δ : ℝ}` explicit, applied inside
`filter_upwards ... with N ...`), hence energy-free, used at `E N`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-- **The pointwise grid bound**: for every `D > 0` and time sequence `u`, there is `δ₀ > 0` such
that for all `0 < δ ≤ δ₀` and `D₁ > 0` a polynomially bounded grid size `K` makes the probability
that `lkErrMat` of the grid process exceeds `N^δ` times the bound of (2.76) at most `N^{-D₁}`,
eventually. No energy-dependent constant is fixed here: every `E`-use is pointwise, inside the
innermost `∀ᶠ N`. -/
def GridPointwise'N (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N,
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ D₁ : ℝ, 0 < D₁ →
      ∃ K : ℕ → ℕ, (∀ N, K N ≠ 0) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) ∧
        ∀ᶠ N : ℕ in atTop, Pg d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
          (N : ℝ) ^ δ * ((etaT (E N) (s N) / etaT (E N) (u N : ℝ)) ^ 4 *
            ((band d).scale (E N) N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2)
          < lkErrMat d (E N) N (u N : ℝ) (H d s (fun N => (u N : ℝ)) K N (K N) ω)
            (pmLoop p.1 p.2)}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁))

/-- **(2.76) at each time `u N ∈ [s, t]`**, from `GridPointwise'N`. The only external dependency,
`pg_bad_eq_flow`, is deterministic per fixed `N` and is applied at `E N`. -/
theorem hpt_of_gridPointwise'N {E : ℕ → ℝ} {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hG : GridPointwise'N d E s t) :
    ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (RBM.Gauss.P d)
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (sample d).lkErr (E N) N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) (u N)) ^ 4 *
        ((band d).scale (E N) N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2) := by
  intro D hD u
  obtain ⟨δ₀, hδ₀, hG'⟩ := hG D hD u
  intro τ hτ D₁ hD₁
  obtain ⟨K, hK0, -, hbad⟩ := hG' (min τ δ₀) (lt_min hτ hδ₀) (min_le_right _ _) D₁ hD₁
  filter_upwards [hbad, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [pg_bad_eq_flow d (E := E N) (δ := min τ δ₀) (uR := fun N => (u N : ℝ)) (hs0 N) (u N).2.1
    (hK0 N) (fun p => (etaT (E N) (s N) / etaT (E N) (u N : ℝ)) ^ 4 *
      ((band d).scale (E N) N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2)] at hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  refine ⟨p, lt_of_le_of_lt ?_ hp⟩
  have hr0 : (0 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) (u N : ℝ)) ^ 4 := by positivity
  have hsc0 : (0 : ℝ) ≤ ((band d).scale (E N) N (u N : ℝ))⁻¹ ^ 2 := by positivity
  have hdp0 : 0 ≤ (band d).decayProf N (u N : ℝ) D p.1 p.2 := by
    unfold Band.decayProf; positivity
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1' (min_le_left _ _))
    (mul_nonneg (mul_nonneg hr0 hsc0) hdp0)

section Compat

end Compat

end RBM.Gauss.Grid

end
