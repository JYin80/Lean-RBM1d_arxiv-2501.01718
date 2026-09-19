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
explicit hypothesis.  See `docs/paper-deltas.md`.

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

/-- Definition 2.1 (ii): for two deterministic `N`-dependent quantities, `f ≺ g`
if `f N ≤ N^τ g N` for every `τ > 0` and all sufficiently large `N`. -/
def DetDom (f g : ℕ → ℝ) : Prop :=
  UnifDetDom (U := fun _ => Unit) (fun N _ => f N) (fun N _ => g N)

@[inherit_doc] scoped infix:50 " ≺ " => DetDom

/-- `DetDom` unfolds to the literal statement of Definition 2.1 (ii). -/
theorem detDom_iff {f g : ℕ → ℝ} :
    f ≺ g ↔ ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, f N ≤ (N : ℝ) ^ τ * g N := by
  simp only [DetDom, UnifDetDom, forall_const]

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

theorem of_le (hg : ∀ N u, 0 ≤ g N u) (hfg : ∀ N u, f N u ≤ g N u) : UnifDetDom f g :=
  of_eventually_le_const_mul hg 1 (Eventually.of_forall fun N u => by simpa using hfg N u)

/-- `≺` is reflexive on non-negative quantities. -/
theorem refl (hg : ∀ N u, 0 ≤ g N u) : UnifDetDom g g :=
  of_le hg fun _ _ => le_rfl

theorem mono_left (hf : ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ f' N u) (h : UnifDetDom f' g) :
    UnifDetDom f g := by
  intro τ hτ
  filter_upwards [hf, h τ hτ] with N hN h'N u
  exact (hN u).trans (h'N u)

theorem mono_right (hg : ∀ᶠ N : ℕ in atTop, ∀ u, g N u ≤ g' N u) (h : UnifDetDom f g) :
    UnifDetDom f g' := by
  intro τ hτ
  filter_upwards [hg, h τ hτ] with N hN h'N u
  exact (h'N u).trans
    (mul_le_mul_of_nonneg_left (hN u) (Real.rpow_nonneg (Nat.cast_nonneg N) τ))

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

/-- `≺` is closed under addition. -/
theorem add (h₁ : UnifDetDom f₁ g₁) (h₂ : UnifDetDom f₂ g₂) :
    UnifDetDom (f₁ + f₂) (g₁ + g₂) := by
  intro τ hτ
  filter_upwards [h₁ τ hτ, h₂ τ hτ] with N hN h'N u
  simp only [Pi.add_apply, mul_add]
  exact add_le_add (hN u) (h'N u)

/-- `≺` is closed under multiplication of non-negative quantities. -/
theorem mul (hf₂ : ∀ N u, 0 ≤ f₂ N u) (hg₁ : ∀ N u, 0 ≤ g₁ N u)
    (h₁ : UnifDetDom f₁ g₁) (h₂ : UnifDetDom f₂ g₂) :
    UnifDetDom (f₁ * f₂) (g₁ * g₂) := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [h₁ _ hτ2, h₂ _ hτ2] with N hN h'N u
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  simp only [Pi.mul_apply]
  calc f₁ N u * f₂ N u ≤ ((N : ℝ) ^ (τ / 2) * g₁ N u) * f₂ N u :=
        mul_le_mul_of_nonneg_right (hN u) (hf₂ N u)
    _ ≤ ((N : ℝ) ^ (τ / 2) * g₁ N u) * ((N : ℝ) ^ (τ / 2) * g₂ N u) :=
        mul_le_mul_of_nonneg_left (h'N u) (mul_nonneg hpos (hg₁ N u))
    _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) * (g₁ N u * g₂ N u) := by ring
    _ = (N : ℝ) ^ τ * (g₁ N u * g₂ N u) := by rw [rpow_half_mul_rpow_half N hτ]

/-- Multiplying both sides by the same non-negative constant preserves `≺`. -/
theorem const_mul {c : ℝ} (hc : 0 ≤ c) (h : UnifDetDom f g) :
    UnifDetDom (fun N u => c * f N u) (fun N u => c * g N u) := by
  intro τ hτ
  filter_upwards [h τ hτ] with N hN u
  calc c * f N u ≤ c * ((N : ℝ) ^ τ * g N u) := mul_le_mul_of_nonneg_left (hN u) hc
    _ = (N : ℝ) ^ τ * (c * g N u) := by ring

/-- Constant factors on the left are absorbed: `f ≺ g` implies `c f ≺ g`. -/
theorem const_mul_left {c : ℝ} (hc : 0 ≤ c) (hg : ∀ N u, 0 ≤ g N u) (h : UnifDetDom f g) :
    UnifDetDom (fun N u => c * f N u) g :=
  (const_mul hc h).trans (of_eventually_le_const_mul hg c (Eventually.of_forall fun _ _ => le_rfl))

/-- Constant factors on the right are absorbed: `f ≺ g` implies `f ≺ c g` for `c > 0`. -/
theorem const_mul_right {c : ℝ} (hc : 0 < c) (hg : ∀ N u, 0 ≤ g N u) (h : UnifDetDom f g) :
    UnifDetDom f (fun N u => c * g N u) := by
  refine h.trans (of_eventually_le_const_mul (fun N u => mul_nonneg hc.le (hg N u)) c⁻¹
    (Eventually.of_forall fun N u => ?_))
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Two quantities dominated by the same `g` have a sum dominated by `g`. -/
theorem add_left (hg : ∀ N u, 0 ≤ g N u) (h₁ : UnifDetDom f₁ g) (h₂ : UnifDetDom f₂ g) :
    UnifDetDom (f₁ + f₂) g :=
  (h₁.add h₂).trans <| of_eventually_le_const_mul hg 2 <|
    Eventually.of_forall fun N u => by simp only [Pi.add_apply]; linarith

end UnifDetDom

namespace DetDom

variable {f f₁ f₂ g g₁ g₂ h : ℕ → ℝ}

theorem of_eventually_le_const_mul (hg : ∀ N, 0 ≤ g N) (C : ℝ)
    (hfg : ∀ᶠ N : ℕ in atTop, f N ≤ C * g N) : f ≺ g :=
  UnifDetDom.of_eventually_le_const_mul (fun N _ => hg N) C (hfg.mono fun _ hN _ => hN)

theorem refl (hg : ∀ N, 0 ≤ g N) : g ≺ g :=
  UnifDetDom.refl fun N _ => hg N

theorem trans (h₁ : f ≺ g) (h₂ : g ≺ h) : f ≺ h :=
  UnifDetDom.trans h₁ h₂

theorem add (h₁ : f₁ ≺ g₁) (h₂ : f₂ ≺ g₂) : f₁ + f₂ ≺ g₁ + g₂ :=
  UnifDetDom.add h₁ h₂

theorem mul (hf₂ : ∀ N, 0 ≤ f₂ N) (hg₁ : ∀ N, 0 ≤ g₁ N) (h₁ : f₁ ≺ g₁) (h₂ : f₂ ≺ g₂) :
    f₁ * f₂ ≺ g₁ * g₂ :=
  UnifDetDom.mul (fun N _ => hf₂ N) (fun N _ => hg₁ N) h₁ h₂

theorem const_mul_left {c : ℝ} (hc : 0 ≤ c) (hg : ∀ N, 0 ≤ g N) (h : f ≺ g) :
    (fun N => c * f N) ≺ g :=
  UnifDetDom.const_mul_left hc (fun N _ => hg N) h

theorem const_mul_right {c : ℝ} (hc : 0 < c) (hg : ∀ N, 0 ≤ g N) (h : f ≺ g) :
    f ≺ fun N => c * g N :=
  UnifDetDom.const_mul_right hc (fun N _ => hg N) h

/-- The form requested in the task list: `f ≺ g` implies `c • f ≺ g` for `c > 0`. -/
theorem smul_left {c : ℝ} (hc : 0 < c) (hg : ∀ N, 0 ≤ g N) (h : f ≺ g) : c • f ≺ g :=
  const_mul_left hc.le hg h

theorem add_left (hg : ∀ N, 0 ≤ g N) (h₁ : f₁ ≺ g) (h₂ : f₂ ≺ g) : f₁ + f₂ ≺ g :=
  UnifDetDom.add_left (fun N _ => hg N) h₁ h₂

end DetDom

end RBM
