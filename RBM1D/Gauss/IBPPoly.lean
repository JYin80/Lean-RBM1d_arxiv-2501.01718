/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuad
import RBM1D.Gauss.LDEDiag
import RBM1D.Gauss.SteinMatrix

/-!
# Discharging `GaussIBP` — T104

`RBM1D/Gauss/LDEQuad.lean` carries the structure `RBM.Gauss.GaussIBP` with two fields:

* `stein` — Gaussian integration by parts against a `Tame` (continuous, finitely dependent,
  **polynomially** bounded) integrand;
* `polyInt` — all polynomial moments of `P d` are finite.

Its header suggests deriving `stein` from `RBM.Gauss.matrixStein` (T70, which assumes the
integrand *globally bounded*) by a smooth cutoff.  That detour is unnecessary: the
one-dimensional identity `RBM.integral_mul_gaussianReal` of `RBM1D/Gauss/Stein.lean` already
takes **integrability** hypotheses rather than boundedness — `RBM.Gauss.matrixStein` merely uses
its bounded corollary.  So the same fibrewise argument, with "bounded" replaced by "polynomially
bounded, hence integrable", proves `stein` directly.

## Main statements

* `RBM.Gauss.integrable_polyW_pow` : `polyInt`
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Finset

open scoped NNReal

variable {d : Dims}

/-! ### An elementary inequality -/

/-- `(a+b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h0 : 0 ≤ max a b := le_max_of_le_left ha
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by linarith) hmax n
    _ = 2 ^ n * max a b ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]
          have : (0 : ℝ) ≤ a ^ n := pow_nonneg ha n
          linarith
        · rw [max_eq_left h]
          have : (0 : ℝ) ≤ b ^ n := pow_nonneg hb n
          linarith

/-! ### All polynomial moments are finite -/

/-- `|ω_c|^n` is integrable. -/
theorem integrable_abs_pow_coord (d : Dims) (c : Coord d) (n : ℕ) :
    Integrable (fun ω : Ω d => |ω c| ^ n) (P d) := by
  have h := (integrable_pow_coord d c n).abs
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  show |ω c ^ n| = |ω c| ^ n
  rw [abs_pow]

theorem continuous_polyW (I : Finset (Coord d)) : Continuous fun ω : Ω d => polyW I ω := by
  refine continuous_const.add ?_
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).abs

/-- **`polyInt`**: every polynomial moment of `P d` is finite.  Induction on the finite set of
coordinates, using `(a+b)^n ≤ 2^n(a^n+b^n)` and the one-coordinate moments. -/
theorem integrable_polyW_pow (d : Dims) (I : Finset (Coord d)) (n : ℕ) :
    Integrable (fun ω : Ω d => polyW I ω ^ n) (P d) := by
  classical
  induction I using Finset.induction generalizing n with
  | empty =>
      have h : ∀ ω : Ω d, polyW (∅ : Finset (Coord d)) ω ^ n = 1 := by
        intro ω; simp [polyW]
      simp only [h]
      exact integrable_const 1
  | insert c I hc ih =>
      have hsplit : ∀ ω : Ω d, polyW (insert c I) ω = polyW I ω + |ω c| := by
        intro ω
        show 1 + ∑ x ∈ insert c I, |ω x| = (1 + ∑ x ∈ I, |ω x|) + |ω c|
        rw [Finset.sum_insert hc]
        ring
      have hmaj : Integrable
          (fun ω : Ω d => 2 ^ n * (polyW I ω ^ n + |ω c| ^ n)) (P d) :=
        ((ih n).add (integrable_abs_pow_coord d c n)).const_mul _
      refine Integrable.mono' hmaj
        (((continuous_polyW (insert c I)).pow n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      have hp : (0 : ℝ) ≤ polyW I ω := (polyW_nonneg I ω)
      have hq : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      have hb := add_pow_le_two_pow_mul hp hq n
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (polyW_nonneg (insert c I) ω) n), hsplit ω]
      exact hb

end RBM.Gauss
