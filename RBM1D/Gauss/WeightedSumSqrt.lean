/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.FDeriv.Norm
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp

/-!
# Minkowski in a weighted `ℓ²` over a `Finset`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2–§5.3: the same-time quadratic-variation rates of the cross term of the Stein
route.

A bound on the quadratic-variation rate of a soft maximum `J̃ = (∑_{i ∈ S} ρ_i^{2r})^{1/(2r)}`
whose constant is the *random* rate of the numerators needs Minkowski in
`ℓ²(usedCoord, gvar)` *before* Hölder in `i`: `∑_α σ_α · max_i |∂_α ρ_i|²` and
`max_i ∑_α σ_α |∂_α ρ_i|²` differ by as much as `card S`, so the scalar, one-coordinate-at-a-time
bound is not enough.

## Main results

* `RBM.Gauss.sqrt_wsum_add_le` — two-term Minkowski for a weighted `ℓ²` sum over a `Finset`.
-/

namespace RBM

namespace Gauss

open scoped Matrix.Norms.L2Operator

open MeasureTheory Step2Bootstrap Cutoff

section Leibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A B : E → ℂ}

variable {d : Dims} {N : ℕ}

end Leibniz

section WeightGrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {S : Finset ι} {F : ι → E → ℂ} {T : ι → ℝ} {b₀ b₁ b₂ T₀ Θ : ℝ} {r : ℕ}

end WeightGrad

section Band

variable {d : Dims} {N : ℕ} {E D u ΘN Θ : ℝ} {r : ℕ}

open Step2

end Band

section QuadVar

variable {d : Dims} {N : ℕ}

end QuadVar

section Duhamel

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

end Duhamel

section GradChi

variable {d : Dims} {N : ℕ} {ι : Type*} {S : Finset ι}
variable {F : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {T : ι → ℝ}
variable {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
variable {b₀ b₁ b₂ c₀ c₁ c₂ T₀ Θ : ℝ} {r : ℕ}

end GradChi

section PZero

variable {Ω : Type*} [MeasurableSpace Ω]

end PZero

section VectorQV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ ι : Type*}

/-! #### 8.1 Minkowski in a weighted `ℓ²` over a `Finset` -/

/-- Two-term Minkowski for a weighted `ℓ²` sum over a `Finset`. -/
theorem sqrt_wsum_add_le (T : Finset κ) (σ : κ → ℝ) (hσ : ∀ q ∈ T, 0 ≤ σ q) (x y : κ → ℝ) :
    √(∑ q ∈ T, σ q * (x q + y q) ^ 2)
      ≤ √(∑ q ∈ T, σ q * x q ^ 2) + √(∑ q ∈ T, σ q * y q ^ 2) := by
  set A : ℝ := ∑ q ∈ T, σ q * x q ^ 2 with hA
  set Bq : ℝ := ∑ q ∈ T, σ q * y q ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun q hq => mul_nonneg (hσ q hq) (sq_nonneg _)
  have hB0 : 0 ≤ Bq := Finset.sum_nonneg fun q hq => mul_nonneg (hσ q hq) (sq_nonneg _)
  set a : κ → ℝ := fun q => √(σ q) * x q with ha
  set b : κ → ℝ := fun q => √(σ q) * y q with hb
  have hsq : ∀ q ∈ T, √(σ q) ^ 2 = σ q := fun q hq => Real.sq_sqrt (hσ q hq)
  have hA' : ∑ q ∈ T, a q ^ 2 = A := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [ha, mul_pow, hsq q hq]
  have hB' : ∑ q ∈ T, b q ^ 2 = Bq := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hb, mul_pow, hsq q hq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T a b
  rw [hA', hB'] at hcs
  have hcross : ∑ q ∈ T, σ q * (x q * y q) ≤ √A * √Bq := by
    have h1 : ∑ q ∈ T, a q * b q = ∑ q ∈ T, σ q * (x q * y q) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hmm : √(σ q) * √(σ q) = σ q := Real.mul_self_sqrt (hσ q hq)
      simp only [ha, hb]
      calc (√(σ q) * x q) * (√(σ q) * y q)
          = (√(σ q) * √(σ q)) * (x q * y q) := by ring
        _ = σ q * (x q * y q) := by rw [hmm]
    have h2 : (∑ q ∈ T, σ q * (x q * y q)) ^ 2 ≤ A * Bq := by rw [← h1]; exact hcs
    have h3 : ∑ q ∈ T, σ q * (x q * y q) ≤ √(A * Bq) := by
      calc ∑ q ∈ T, σ q * (x q * y q) ≤ |∑ q ∈ T, σ q * (x q * y q)| := le_abs_self _
        _ = √((∑ q ∈ T, σ q * (x q * y q)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(A * Bq) := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_mul hA0] at h3
  have hexp : ∑ q ∈ T, σ q * (x q + y q) ^ 2
      = A + 2 * (∑ q ∈ T, σ q * (x q * y q)) + Bq := by
    rw [hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [hexp]
  have hkey : A + 2 * (∑ q ∈ T, σ q * (x q * y q)) + Bq ≤ (√A + √Bq) ^ 2 := by
    have h1 : (√A + √Bq) ^ 2 = A + 2 * (√A * √Bq) + Bq := by
      have e1 : √A ^ 2 = A := Real.sq_sqrt hA0
      have e2 : √Bq ^ 2 = Bq := Real.sq_sqrt hB0
      nlinarith [e1, e2]
    rw [h1]; linarith
  calc √(A + 2 * (∑ q ∈ T, σ q * (x q * y q)) + Bq) ≤ √((√A + √Bq) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = √A + √Bq := Real.sqrt_sq (by positivity)

/-! #### 8.2 The directional derivatives, against the numerator's own gradient -/

end VectorQV

/-! #### 8.3 The vector bound on the model's coordinates -/

section S2

variable {d : Dims} {N : ℕ} {ι : Type*}

end S2

section S5

variable {d : Dims} {N : ℕ} {ι : Type*}

section Weight

variable {f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c : ι → ℝ} {r p : ℕ} {Θ K : ℝ}

end Weight

/-! #### 8.4 The cross term -/

section Cross

variable {f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c : ι → ℝ} {r p : ℕ} {Θ K : ℝ}

end Cross

end S5

/-! ### 9. Compiled satisfiability witnesses -/

section Sat

open Step2 MeasureTheory

end Sat

end Gauss

end RBM
