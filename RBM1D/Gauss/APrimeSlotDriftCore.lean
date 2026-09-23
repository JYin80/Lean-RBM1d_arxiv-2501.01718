/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeOneStepTerms
import RBM1D.Gauss.StepSideAPrimeCore

/-!
# Dependency-light drift-slot arithmetic for the A-prime step

This core contains exactly the scalar slot values needed to define the drift budget and the
two elementary lower bounds consumed upstream of the full slot-arithmetic facade.
-/

namespace RBM

namespace APrimeSlotArith

open Real
open StepSideAPrime APrimeOneStep

/-- The `Ξ` slot of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotXi (x : ℝ) : ℝ := x / 2

/-- The far-field threshold `A` slot of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotA (x R : ℝ) : ℝ := 2 * (cWt ^ 2 * x ^ 33 * R ^ 10)

/-- The far-field remainder `ε` slot of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotEps (x R : ℝ) : ℝ := (2 * (cWt ^ 2 * x ^ 33 * R ^ 10))⁻¹

/-- The near-field coefficient `q` slot of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotQ (R : ℝ) : ℝ := R ^ 2 / 2

/-- The linear far-field coefficient `β` slot of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotBeta (x R : ℝ) : ℝ := (2 * (cWt * x ^ 16 * R ^ 2))⁻¹

/-- The `3/2`-power far-field coefficient `γ` slot of
`RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotGamma (x R : ℝ) : ℝ := (2 * (cWt * √cWt * x ^ 24 * R ^ 4))⁻¹

/-- The a priori level slot `Jv` of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotJv (x R : ℝ) : ℝ := cWt * x ^ 16 * R ^ 4 / 2

/-- The `drift` slot of `RBM.APrimeOneStep.stepRhs''_div_of_slots`, at the eight values:
this is the `Dbd` that `RBM.APrimeModel.drift_bound_first_cell` must beat. -/
noncomputable def slotDrift (m x R : ℝ) : ℝ :=
  driftTerm m x R (slotXi x) (slotA x R) (slotEps x R) (slotQ R) (slotBeta x R)
    (slotGamma x R) (slotJv x R) / R ^ 4

/-- **The drift slot is at least its near-field term.**  The far-field group and the two
`Jv`-terms are non-negative, so they only help. -/
theorem driftTerm_ge_near {m x R Ξ A ε q β γ Jv : ℝ} (hm : 0 < m) (hx0 : 0 ≤ x)
    (hR0 : 0 ≤ R) (hΞ0 : 0 ≤ Ξ) (hA0 : 0 < A) (hε0 : 0 ≤ ε) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ)
    (hJ0 : 0 ≤ Jv) :
    Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ driftTerm m x R Ξ A ε q β γ Jv := by
  have hmi : (0 : ℝ) ≤ m⁻¹ := (inv_pos.2 hm).le
  have hAi : (0 : ℝ) ≤ A⁻¹ := (inv_pos.2 hA0).le
  have hsJ : (0 : ℝ) ≤ √Jv := Real.sqrt_nonneg _
  have hR2 : (0 : ℝ) ≤ R ^ 2 := pow_nonneg hR0 2
  have hb1 : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε :=
    add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmi) hR2) hAi)
      (mul_nonneg hR2 hε0)
  have h1 : (0 : ℝ) ≤ exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2
      * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) :=
    mul_nonneg (mul_nonneg (exp_pos 1).le (sq_nonneg _)) hb1
  have h2 : (0 : ℝ) ≤ x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hx0 hmi) hR2)
      (add_nonneg (mul_nonneg hβ0 hJ0) (mul_nonneg hγ0 (mul_nonneg hJ0 hsJ)))
  have hsplit : driftTerm m x R Ξ A ε q β γ Jv
      = Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε))
        + Ξ * (x * m⁻¹ * R ^ 2 * q)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) := by
    unfold driftTerm; ring
  rw [hsplit]
  have p1 := mul_nonneg hΞ0 h1
  have p2 := mul_nonneg hΞ0 h2
  linarith

/-- **⭐ The drift slot, at T263's witness values**: `Ξ = x/2` and `q = R²/2` alone already
give `x²/(4m)` after the `R⁻⁴` normalization. -/
theorem driftTerm_slot_ge {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    x ^ 2 * m⁻¹ / 4 ≤ slotDrift m x R := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : 0 < cWt := cWt_pos
  have hsc0 : 0 < √cWt := Real.sqrt_pos.2 hc0
  have hA0 : (0 : ℝ) < slotA x R := by unfold slotA; positivity
  have hε0 : (0 : ℝ) ≤ slotEps x R := by unfold slotEps; positivity
  have hβ0 : (0 : ℝ) ≤ slotBeta x R := by unfold slotBeta; positivity
  have hγ0 : (0 : ℝ) ≤ slotGamma x R := by unfold slotGamma; positivity
  have hJ0 : (0 : ℝ) ≤ slotJv x R := by unfold slotJv; positivity
  have hΞ0 : (0 : ℝ) ≤ slotXi x := by unfold slotXi; positivity
  have key := driftTerm_ge_near (m := m) (x := x) (R := R) (Ξ := slotXi x) (A := slotA x R)
    (ε := slotEps x R) (q := slotQ R) (β := slotBeta x R) (γ := slotGamma x R)
    (Jv := slotJv x R) hm hx0.le hR0.le hΞ0 hA0 hε0 hβ0 hγ0 hJ0
  have heq : slotXi x * (x * m⁻¹ * R ^ 2 * slotQ R) = x ^ 2 * m⁻¹ / 4 * R ^ 4 := by
    unfold slotXi slotQ; ring
  rw [heq] at key
  unfold slotDrift
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 4)]
  exact key

end APrimeSlotArith

end RBM
