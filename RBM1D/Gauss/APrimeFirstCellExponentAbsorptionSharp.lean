/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellExponentAbsorption

/-!
# T526: sharper first-cell deterministic exponent absorption

The six terms of T503's literal ledger are absorbed at the sharper target
exponent `delta / 5`, with the moment order fixed before the eventual cutoff.
-/

namespace RBM.APrimeFirstCellExponentAbsorptionSharp

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ :=
  APrimeFirstCellExponentAbsorption.delta

noncomputable abbrev alpha : ℝ :=
  APrimeFirstCellExponentAbsorption.alpha

private theorem ratio_neg_two_floor {R : ℝ} (hR1 : 1 ≤ R) (hR2 : R ≤ 2) :
    (1 / 4 : ℝ) ≤ R ^ (-(2 : ℝ)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hi : (2 : ℝ)⁻¹ ≤ R⁻¹ := inv_anti₀ hR0 hR2
  have hs := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) hi
  calc
    (1 / 4 : ℝ) = (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by norm_num
    _ ≤ R⁻¹ * R⁻¹ := by simpa only [pow_two] using hs
    _ = R ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hR0.le, Real.rpow_two, ← inv_pow]
      simp only [pow_two]

private theorem additive_le_ratio_mul_four {R x : ℝ} (hx : 0 ≤ x)
    (hR : (1 / 4 : ℝ) ≤ R ^ (-(2 : ℝ))) :
    x ≤ R ^ (-(2 : ℝ)) * (4 * x) := by
  have hnonneg : 0 ≤ x * (R ^ (-(2 : ℝ)) - 1 / 4) :=
    mul_nonneg hx (sub_nonneg.mpr hR)
  nlinarith

private noncomputable def absorbedSum (p N : ℕ) : ℝ :=
  (N : ℝ) ^ (5 * delta / 32) +
  APrimeFirstCellExponentAbsorption.driftConstant *
      (N : ℝ) ^ (delta / 8) +
  2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
      (N : ℝ) ^ (-31 * delta / 16) +
  (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
      (N : ℝ) ^ (delta / 32) +
  (4 * Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ)) *
      (N : ℝ) ^ (-(1 : ℝ) / 2) +
  4 * (N : ℝ) ^ (-(1 : ℝ))

private theorem momentRhs_le_ratio_mul_absorbedSum {p N : ℕ}
    (_hp : 1 ≤ p) {R : ℝ} (hR1 : 1 ≤ R) (hR2 : R ≤ 2) :
    APrimeFirstCellExponentAbsorption.momentRhs p N R ≤
      R ^ (-(2 : ℝ)) * absorbedSum p N := by
  have hfloor := ratio_neg_two_floor hR1 hR2
  have hsqrt : 0 ≤ Real.sqrt (2 * (p : ℝ) - 1) := Real.sqrt_nonneg _
  have hNhalf : 0 ≤
      Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ) *
        (N : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hNone : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hhalf := additive_le_ratio_mul_four hNhalf hfloor
  have hone := additive_le_ratio_mul_four hNone hfloor
  unfold APrimeFirstCellExponentAbsorption.momentRhs absorbedSum
  calc
    _ =
        R ^ (-(2 : ℝ)) *
          ((N : ℝ) ^ (5 * delta / 32) +
            APrimeFirstCellExponentAbsorption.driftConstant *
              (N : ℝ) ^ (delta / 8) +
            2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
              (N : ℝ) ^ (-31 * delta / 16) +
            (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
              (N : ℝ) ^ (delta / 32)) +
          Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ) *
            (N : ℝ) ^ (-(1 : ℝ) / 2) +
          (N : ℝ)⁻¹ := by ring
    _ ≤
        R ^ (-(2 : ℝ)) *
          ((N : ℝ) ^ (5 * delta / 32) +
            APrimeFirstCellExponentAbsorption.driftConstant *
              (N : ℝ) ^ (delta / 8) +
            2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
              (N : ℝ) ^ (-31 * delta / 16) +
            (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
              (N : ℝ) ^ (delta / 32)) +
          R ^ (-(2 : ℝ)) *
            (4 * (Real.sqrt (2 * (p : ℝ) - 1) *
              Real.sqrt (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2))) +
          R ^ (-(2 : ℝ)) * (4 * (N : ℝ)⁻¹) := by
      gcongr
    _ = R ^ (-(2 : ℝ)) * absorbedSum p N := by
      unfold absorbedSum
      rw [show (N : ℝ)⁻¹ = (N : ℝ) ^ (-(1 : ℝ)) by
        simp only [Real.rpow_neg_one]]
      ring

/-- T503's exact ledger is eventually absorbed at exponent `delta / 5`.
The fixed moment order precedes the eventual threshold, and the conclusion
is uniform over every ratio `1 ≤ R ≤ 2`. -/
theorem eventually_momentRhs_le (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, 1 ≤ R → R ≤ 2 →
      APrimeFirstCellExponentAbsorption.momentRhs p N R ≤
        (N : ℝ) ^ (delta / 5) * R ^ (-(2 : ℝ)) := by
  have h1 : 5 * delta / 32 < delta / 5 := by
    norm_num [delta, APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have h2 : delta / 8 < delta / 5 := by
    norm_num [delta, APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have h3 : -31 * delta / 16 < delta / 5 := by
    norm_num [delta, APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have h4 : delta / 32 < delta / 5 := by
    norm_num [delta, APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have h5 : -(1 : ℝ) / 2 < delta / 5 := by
    norm_num [delta, APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have h6 : -(1 : ℝ) < delta / 5 := by
    norm_num [delta, APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  filter_upwards [
    SumZeroDyn.eventually_const_mul_rpow_le 6 h1,
    SumZeroDyn.eventually_const_mul_rpow_le
      (6 * APrimeFirstCellExponentAbsorption.driftConstant) h2,
    SumZeroDyn.eventually_const_mul_rpow_le
      (6 * (2 * APrimeFirstCellFullCrossBudget.budgetConstant p)) h3,
    SumZeroDyn.eventually_const_mul_rpow_le
      (6 * (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3))) h4,
    SumZeroDyn.eventually_const_mul_rpow_le
      (6 * (4 * Real.sqrt (2 * (p : ℝ) - 1) *
        Real.sqrt (1 / 2 : ℝ))) h5,
    SumZeroDyn.eventually_const_mul_rpow_le (6 * 4) h6]
      with N hN1 hN2 hN3 hN4 hN5 hN6
  intro R hR1 hR2
  have htarget : 0 ≤ (N : ℝ) ^ (delta / 5) := by positivity
  have hs : absorbedSum p N ≤ (N : ℝ) ^ (delta / 5) := by
    unfold absorbedSum
    have hN1' :
        (N : ℝ) ^ (5 * delta / 32) ≤
          (N : ℝ) ^ (delta / 5) / 6 := by nlinarith
    have hN2' :
        APrimeFirstCellExponentAbsorption.driftConstant *
            (N : ℝ) ^ (delta / 8) ≤
          (N : ℝ) ^ (delta / 5) / 6 := by nlinarith
    have hN3' :
        2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
            (N : ℝ) ^ (-31 * delta / 16) ≤
          (N : ℝ) ^ (delta / 5) / 6 := by nlinarith
    have hN4' :
        (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
            (N : ℝ) ^ (delta / 32) ≤
          (N : ℝ) ^ (delta / 5) / 6 := by nlinarith
    have hN5' :
        (4 * Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ)) *
            (N : ℝ) ^ (-(1 : ℝ) / 2) ≤
          (N : ℝ) ^ (delta / 5) / 6 := by nlinarith
    have hN6' :
        4 * (N : ℝ) ^ (-(1 : ℝ)) ≤
          (N : ℝ) ^ (delta / 5) / 6 := by nlinarith
    linarith
  exact (momentRhs_le_ratio_mul_absorbedSum hp hR1 hR2).trans
    (by
      rw [mul_comm (R ^ (-(2 : ℝ)))]
      exact mul_le_mul_of_nonneg_right hs
        (Real.rpow_nonneg (by positivity) _))

/-- The same measurable high-probability sharp event and its positive `k=2`
resident witness the nonvacuity of the sharper deterministic statement. -/
theorem positive_two_same_sharpCommonEvent_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          τ' delta alpha N)) ∧
      HighProb (P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 2
        0 < v ∧
        1 ≤ APrimeFirstCellLoopCap.xRate v ∧
        APrimeFirstCellLoopCap.xRate v ≤ 2 ∧
        ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          τ' delta alpha N, True) := by
  simpa only [delta, alpha] using
    APrimeFirstCellExponentAbsorption.positive_two_same_sharpCommonEvent_witness

#print axioms eventually_momentRhs_le
#print axioms positive_two_same_sharpCommonEvent_witness

end
end RBM.APrimeFirstCellExponentAbsorptionSharp
