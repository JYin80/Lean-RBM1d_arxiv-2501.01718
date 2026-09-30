/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Deterministic stochastic domination `≺`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.1 (ii).

For two deterministic `N`-dependent quantities the paper writes `ξ ≺ ζ` if
`ξ ≤ N^τ ζ` for every `τ > 0` and all sufficiently large `N`.

Part (i) of Definition 2.1 is uniform in a possibly `N`-dependent parameter
`u ∈ U(N)`, and the deterministic estimates of the paper (e.g. (2.53), (2.54),
which hold uniformly in the lattice points) are used in that uniform form.  We
therefore take the uniform version `RBM.UnifDetDom` as the basic notion, with
`N₀` independent of `u`, and obtain the scalar version `RBM.DetDom` as the case
of a one-point parameter set.

The definition does not require the quantities to be non-negative; the lemmas
that need non-negativity (as the paper assumes throughout) take it as an
explicit hypothesis.

## Main definitions

* `RBM.UnifDetDom f g` : `f ≺ g` uniformly in `u ∈ U(N)`
* `RBM.DetDom f g`     : `f ≺ g` for scalar sequences, Definition 2.1 (ii);
  scoped notation `f ≺ g`

## Main results

* `refl`, `trans`, `add`, `mul`, `const_mul_left`, `const_mul_right`:
  the closure properties used throughout the paper
* `of_eventually_le_const_mul` : `f ≤ C g` implies `f ≺ g`
-/

namespace RBM

open Filter

/-- Definition 2.1 (ii), uniformly in a possibly `N`-dependent parameter `u ∈ U(N)`:
`f ≺ g` if for every `τ > 0` there is `N₀` with `f(N, u) ≤ N^τ g(N, u)` for all
`N ≥ N₀` and all `u ∈ U(N)`. -/
def UnifDetDom {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ (N : ℝ) ^ τ * g N u

/-- For `τ > 0` the factor `N^τ` eventually exceeds any fixed constant. -/
theorem eventually_le_rpow (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ τ :=
  ((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

namespace UnifDetDom

variable {U : ℕ → Type*} {f f' f₁ f₂ g g' g₁ g₂ h : ∀ N, U N → ℝ}

/-- A bound up to a constant factor implies `≺`. -/
theorem of_eventually_le_const_mul (hg : ∀ N u, 0 ≤ g N u) (C : ℝ)
    (hfg : ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ C * g N u) : UnifDetDom f g := by
  intro τ hτ
  filter_upwards [hfg, eventually_le_rpow C hτ] with N hN hC u
  exact (hN u).trans (mul_le_mul_of_nonneg_right hC (hg N u))

theorem mono_left (hf : ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ f' N u) (h : UnifDetDom f' g) :
    UnifDetDom f g := by
  intro τ hτ
  filter_upwards [hf, h τ hτ] with N hN h'N u
  exact (hN u).trans (h'N u)

/-- Splitting `N^τ = N^{τ/2} N^{τ/2}`. -/
theorem rpow_half_mul_rpow_half (N : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
  rw [← Real.rpow_add' (Nat.cast_nonneg N) (by linarith), add_halves]

/-- `≺` is transitive. -/
theorem trans (h₁ : UnifDetDom f g) (h₂ : UnifDetDom g h) : UnifDetDom f h := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [h₁ _ hτ2, h₂ _ hτ2] with N hN h'N u
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc f N u ≤ (N : ℝ) ^ (τ / 2) * g N u := hN u
    _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * h N u) :=
        mul_le_mul_of_nonneg_left (h'N u) hpos
    _ = (N : ℝ) ^ τ * h N u := by rw [← mul_assoc, rpow_half_mul_rpow_half N hτ]

end UnifDetDom

namespace DetDom

variable {f f₁ f₂ g g₁ g₂ h : ℕ → ℝ}

end DetDom

end RBM
