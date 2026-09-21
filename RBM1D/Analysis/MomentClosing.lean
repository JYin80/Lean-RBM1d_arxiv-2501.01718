/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Analysis.StretchedExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The closing step of the moment Duhamel: integrate, then take the supremum (T132a)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, the passage from the differential inequality for `u ↦ E|Φ_u|^{2p}` to the bound
**(5.20) + (5.24)** in the combined form

  `‖Φ_t‖_{2p} ≤ ‖Φ_s‖_{2p} + 2 ∫_s^t f + (c ∫_s^t g)^{1/2}`.

Nothing here is specific to the model — this file is pure real analysis and uses nothing
outside Mathlib and `RBM1D/Analysis/StretchedExp.lean`.

## Why not Grönwall

The obvious route — Young's inequality `x^{2p-1} y ≤ x^{2p} + y^{2p}` followed by Mathlib's
`gronwallBound` — **loses a power of `η`** and must not be used here.  With
`f_u ≍ Φ / η_u` (which is the size of every `E`-term of (5.77) and of the quadratic variation
of (5.86)), Young produces the inhomogeneous term `∫_s^t f_u^{2p} du ≍ Φ^{2p} η_t^{1-2p}`,
whereas the paper's `(∫_s^t f_u du)^{2p} ≍ (Φ log)^{2p}`; after the `2p`-th root the two
differ by `η_t^{-1+1/(2p)}`.  Weighting Young by `1/η_u` does not help either: the Grönwall
factor then grows like `(η_s/η_t)^{C p²}`, quadratically in `p`, while `≺` needs arbitrarily
large `p` with the time step fixed before `ε` and `D`.

The correct closing needs **no ODE comparison theorem at all**: one integrates the
differential inequality, bounds `∫ √ψ · f` by `(sup √ψ) ∫ f`, takes the supremum of the
resulting inequality over the interval, and solves the resulting *quadratic* inequality for
that supremum.  That is what this file provides, in three independent pieces.

## Main statements

* `RBM.le_two_mul_add_sqrt_of_sq_le` — the quadratic step, pure algebra:
  `m² ≤ A + 2 F m` implies `m ≤ 2F + √A`.
* `RBM.integral_sqrt_mul_le` — the "integrate" step: `∫_s^u √(ψ) f ≤ √M ∫_s^t f` when `M`
  bounds `ψ` on `[s, t]` and `f ≥ 0`.
* `RBM.sqrt_le_of_isLUB` — the "take the supremum" step and the conclusion.
* `RBM.sqrt_le_of_integral_le` — the two combined: the form a caller actually has.

## The shape of the hypothesis

The caller arrives with `ψ = (φ + ε)^{1/p}` where `φ_u = E|Φ_u|^{2p}` (the `ε > 0` avoids the
division by `φ` at a zero of `φ` and is sent to `0` at the very end), for which the generator
identity gives `ψ' ≤ 2 √ψ f + c g` with `c = C_p / p`.  The integrated form of *that* is the
hypothesis `hmain` below; no differentiability of `ψ` is assumed anywhere in this file.
-/

namespace RBM

open Real MeasureTheory

/-! ### The quadratic step -/

/-- **`m² ≤ A + 2 F m` implies `m ≤ 2F + √A`.**  This is the step that turns the
supremum-of-the-interval inequality into the final bound; `2F` is where the factor `2` of
`2 ∫ ‖U ∘ F‖_{2p}` comes from.  Pure algebra: complete the square and use
`RBM.sqrt_add_le_add_sqrt`. -/
theorem le_two_mul_add_sqrt_of_sq_le {m F A : ℝ} (hF : 0 ≤ F)
    (h : m ^ 2 ≤ A + 2 * F * m) : m ≤ 2 * F + √A := by
  have hsq : (m - F) ^ 2 ≤ A + F ^ 2 := by nlinarith
  have h1 : m - F ≤ √(A + F ^ 2) := by
    calc m - F ≤ |m - F| := le_abs_self _
      _ = √((m - F) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √(A + F ^ 2) := Real.sqrt_le_sqrt hsq
  have h2 : √(A + F ^ 2) ≤ √A + F := by
    have := sqrt_add_le_add_sqrt A (sq_nonneg F)
    rwa [Real.sqrt_sq hF] at this
  linarith

/-! ### The "integrate" step -/

/-- `IntervalIntegrable f volume s u` for `s ≤ u ≤ t`, from integrability on `[s, t]`. -/
theorem intervalIntegrable_prefix {s t u : ℝ} {f : ℝ → ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    (hintf : IntervalIntegrable f volume s t) : IntervalIntegrable f volume s u :=
  hintf.mono_set (by
    rw [Set.uIcc_of_le hsu, Set.uIcc_of_le (hsu.trans hut)]
    exact Set.Icc_subset_Icc le_rfl hut)

/-- **The integral over a prefix is at most the integral over the whole interval**, for a
nonnegative integrand.  Used twice below, for `f` and for `g`. -/
theorem integral_le_integral_right {s t u : ℝ} {f : ℝ → ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    (hf0 : ∀ r ∈ Set.Icc s t, 0 ≤ f r) (hintf : IntervalIntegrable f volume s t) :
    (∫ r in s..u, f r) ≤ ∫ r in s..t, f r := by
  have hintfu : IntervalIntegrable f volume s u := intervalIntegrable_prefix hsu hut hintf
  have hintfut : IntervalIntegrable f volume u t :=
    hintf.mono_set (by
      rw [Set.uIcc_of_le hut, Set.uIcc_of_le (hsu.trans hut)]
      exact Set.Icc_subset_Icc hsu le_rfl)
  have h3 : (0 : ℝ) ≤ ∫ r in u..t, f r :=
    intervalIntegral.integral_nonneg hut fun r hr => hf0 r ⟨hsu.trans hr.1, hr.2⟩
  have h4 : (∫ r in s..u, f r) + ∫ r in u..t, f r = ∫ r in s..t, f r :=
    intervalIntegral.integral_add_adjacent_intervals hintfu hintfut
  linarith

/-- **`∫_s^u √(ψ) f ≤ √M ∫_s^t f`** for `s ≤ u ≤ t`, `f ≥ 0` and `ψ ≤ M` on `[s, t]`.
This is the only place the supremum `M` enters the integral, and it is what makes the
right-hand side of `hmain` independent of `u`. -/
theorem integral_sqrt_mul_le {s t u M : ℝ} {ψ f : ℝ → ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    (hM : ∀ r ∈ Set.Icc s t, ψ r ≤ M) (hf0 : ∀ r ∈ Set.Icc s t, 0 ≤ f r)
    (hint : IntervalIntegrable (fun r => √(ψ r) * f r) volume s u)
    (hintf : IntervalIntegrable f volume s t) :
    (∫ r in s..u, √(ψ r) * f r) ≤ √M * ∫ r in s..t, f r := by
  have hsub : Set.Icc s u ⊆ Set.Icc s t := Set.Icc_subset_Icc le_rfl hut
  have hintfu : IntervalIntegrable f volume s u := intervalIntegrable_prefix hsu hut hintf
  have hpt : ∀ r ∈ Set.Icc s u, √(ψ r) * f r ≤ √M * f r := fun r hr =>
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hM r (hsub hr))) (hf0 r (hsub hr))
  have h1 : (∫ r in s..u, √(ψ r) * f r) ≤ ∫ r in s..u, √M * f r :=
    intervalIntegral.integral_mono_on hsu hint (hintfu.const_mul _) hpt
  have h2 : (∫ r in s..u, √M * f r) = √M * ∫ r in s..u, f r :=
    intervalIntegral.integral_const_mul _ _
  calc (∫ r in s..u, √(ψ r) * f r) ≤ √M * ∫ r in s..u, f r := by rw [← h2]; exact h1
    _ ≤ √M * ∫ r in s..t, f r :=
        mul_le_mul_of_nonneg_left (integral_le_integral_right hsu hut hf0 hintf)
          (Real.sqrt_nonneg _)

/-! ### The "take the supremum" step -/

/-- **The closing lemma.**  If `ψ ≥ 0` on `[s, t]`, `M` is the least upper bound of `ψ` there,
and every value `ψ u` is bounded by `ψ s + 2 √M F + c G`, then

  `√(ψ t) ≤ √(ψ s) + 2 F + √(c G)`.

With `ψ = (φ + ε)^{1/p}`, `φ_u = E|Φ_u|^{2p}`, `F = ∫_s^t ‖(U_{u,t} ∘ F_u)_a‖_{2p}` and
`G = ∫_s^t ‖((U ⊗ U) ∘ (E ⊗ E))_{u,a,a}‖_p`, this *is* (5.20) + (5.24). -/
theorem sqrt_le_of_isLUB {s t : ℝ} (hst : s ≤ t) {ψ : ℝ → ℝ} {F G c M : ℝ}
    (hψ0 : ∀ u ∈ Set.Icc s t, 0 ≤ ψ u) (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) (hc0 : 0 ≤ c)
    (hM : IsLUB (ψ '' Set.Icc s t) M)
    (hmain : ∀ u ∈ Set.Icc s t, ψ u ≤ ψ s + 2 * √M * F + c * G) :
    √(ψ t) ≤ √(ψ s) + 2 * F + √(c * G) := by
  have hsmem : s ∈ Set.Icc s t := ⟨le_rfl, hst⟩
  have htmem : t ∈ Set.Icc s t := ⟨hst, le_rfl⟩
  have hM0 : 0 ≤ M := (hψ0 s hsmem).trans (hM.1 ⟨s, hsmem, rfl⟩)
  -- `M` is the least upper bound, and the right-hand side of `hmain` is one upper bound
  have hMle : M ≤ ψ s + 2 * √M * F + c * G := by
    refine hM.2 ?_
    rintro y ⟨u, hu, rfl⟩
    exact hmain u hu
  -- the quadratic inequality for `m = √M`
  have hsq : √M ^ 2 = M := Real.sq_sqrt hM0
  have hquad : √M ^ 2 ≤ (ψ s + c * G) + 2 * F * √M := by
    rw [hsq]; linarith
  have hkey : √M ≤ 2 * F + √(ψ s + c * G) :=
    le_two_mul_add_sqrt_of_sq_le hF0 hquad
  have hsplit : √(ψ s + c * G) ≤ √(ψ s) + √(c * G) :=
    sqrt_add_le_add_sqrt _ (mul_nonneg hc0 hG0)
  have hψt : √(ψ t) ≤ √M := Real.sqrt_le_sqrt (hM.1 ⟨t, htmem, rfl⟩)
  linarith

/-- **The closing lemma in the form a caller has it**: the integrated differential inequality
`ψ u ≤ ψ s + 2 ∫_s^u √ψ · f + c ∫_s^u g` on `[s, t]` gives

  `√(ψ t) ≤ √(ψ s) + 2 ∫_s^t f + √(c ∫_s^t g)`.

This is `RBM.integral_sqrt_mul_le` (integrate) followed by `RBM.sqrt_le_of_isLUB`
(take the supremum, then solve the quadratic).  **No ODE comparison theorem is used.** -/
theorem sqrt_le_of_integral_le {s t : ℝ} (hst : s ≤ t) {ψ f g : ℝ → ℝ} {c M : ℝ}
    (hψ0 : ∀ u ∈ Set.Icc s t, 0 ≤ ψ u)
    (hf0 : ∀ r ∈ Set.Icc s t, 0 ≤ f r) (hg0 : ∀ r ∈ Set.Icc s t, 0 ≤ g r) (hc0 : 0 ≤ c)
    (hM : IsLUB (ψ '' Set.Icc s t) M)
    (hintψf : ∀ u ∈ Set.Icc s t, IntervalIntegrable (fun r => √(ψ r) * f r) volume s u)
    (hintf : IntervalIntegrable f volume s t) (hintg : IntervalIntegrable g volume s t)
    (hdu : ∀ u ∈ Set.Icc s t,
      ψ u ≤ ψ s + 2 * (∫ r in s..u, √(ψ r) * f r) + c * ∫ r in s..u, g r) :
    √(ψ t) ≤ √(ψ s) + 2 * (∫ r in s..t, f r) + √(c * ∫ r in s..t, g r) := by
  have hMub : ∀ r ∈ Set.Icc s t, ψ r ≤ M := fun r hr => hM.1 ⟨r, hr, rfl⟩
  have hF0 : (0 : ℝ) ≤ ∫ r in s..t, f r := intervalIntegral.integral_nonneg hst hf0
  have hG0 : (0 : ℝ) ≤ ∫ r in s..t, g r := intervalIntegral.integral_nonneg hst hg0
  refine sqrt_le_of_isLUB hst hψ0 hF0 hG0 hc0 hM fun u hu => ?_
  have h1 : (∫ r in s..u, √(ψ r) * f r) ≤ √M * ∫ r in s..t, f r :=
    integral_sqrt_mul_le hu.1 hu.2 hMub hf0 (hintψf u hu) hintf
  have h2 : (∫ r in s..u, g r) ≤ ∫ r in s..t, g r :=
    integral_le_integral_right hu.1 hu.2 hg0 hintg
  have h3 := hdu u hu
  nlinarith [mul_le_mul_of_nonneg_left h2 hc0]

end RBM
