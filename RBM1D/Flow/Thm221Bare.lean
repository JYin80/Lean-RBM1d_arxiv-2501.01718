/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Universality

/-!
# An arithmetic bridge for the step condition (2.72)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

(2.72) as printed in Theorem 2.21 reads `R^30 ≤ A`, with `A = W ℓ_t η_t` and
`R = (1 - s)/(1 - t)`; a regime bound reads `N^c ≤ A`.
`RBM.rpow_mul_rpow_le_of_pow_thirty` combines the two: `N^e R^b ≤ A^a` whenever
`e/c + b/30 ≤ a`.
-/

namespace RBM

open MeasureTheory Filter

/-! ### 1. The arithmetic bridge

`R^30 ≤ A` and `N^c ≤ A` give `N^e R^b ≤ A^a` whenever `e/c + b/30 ≤ a`.  For `b < 30 a` this
leaves a genuine gain `N^e` with `e = c (a - b/30) > 0`. -/

section Arith

/-- **The bridge**: from `R^30 ≤ A` (the bare (2.72)) and `N^c ≤ A` (the regime bound),
`N^e R^b ≤ A^a` as soon as `e/c + b/30 ≤ a`.

`R^b ≤ (R^30)^{b/30} ≤ A^{b/30}`, `N^e = (N^c)^{e/c} ≤ A^{e/c}`, and `A ≥ 1` lets the two
exponents be added. -/
theorem rpow_mul_rpow_le_of_pow_thirty {A R Nr c e b a : ℝ} (hN : 1 ≤ Nr) (hR : 1 ≤ R)
    (hc : 0 < c) (he : 0 ≤ e) (hb : 0 ≤ b) (h30 : R ^ (30 : ℕ) ≤ A) (hreg : Nr ^ c ≤ A)
    (hsum : e / c + b / 30 ≤ a) :
    Nr ^ e * R ^ b ≤ A ^ a := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hA1 : (1 : ℝ) ≤ A := (Real.one_le_rpow hN hc.le).trans hreg
  have hA0 : (0 : ℝ) < A := by linarith
  -- `R ^ b ≤ A ^ (b / 30)`
  have hRb : R ^ b ≤ A ^ (b / 30) := by
    have hpow : R ^ b = (R ^ (30 : ℕ)) ^ (b / 30) := by
      rw [← Real.rpow_natCast R 30, ← Real.rpow_mul hR0.le]
      congr 1
      push_cast
      ring
    rw [hpow]
    exact Real.rpow_le_rpow (by positivity) h30 (by positivity)
  -- `Nr ^ e ≤ A ^ (e / c)`
  have hNe : Nr ^ e ≤ A ^ (e / c) := by
    have hN0 : (0 : ℝ) < Nr := by linarith
    have hpow : Nr ^ e = (Nr ^ c) ^ (e / c) := by
      rw [← Real.rpow_mul hN0.le]
      congr 1
      field_simp
    rw [hpow]
    exact Real.rpow_le_rpow (by positivity) hreg (by positivity)
  calc Nr ^ e * R ^ b ≤ A ^ (e / c) * A ^ (b / 30) :=
        mul_le_mul hNe hRb (by positivity) (by positivity)
    _ = A ^ (e / c + b / 30) := (Real.rpow_add hA0 _ _).symm
    _ ≤ A ^ a := Real.rpow_le_rpow_of_exponent_le hA1 hsum

end Arith

section Cond

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end Cond

section Margin

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end Margin

section Thm

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

end Thm

section Counterexample

variable {Ω : Type*} [MeasurableSpace Ω] {E : ℝ}

end Counterexample

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω] {E : ℝ}

end Satisfiable

end RBM
