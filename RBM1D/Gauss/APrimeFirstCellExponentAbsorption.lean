/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFullCrossBudget
import RBM1D.Gauss.APrimeFirstCellDriftCoefficientAbsorbed
import RBM1D.Gauss.APrimeFirstCellSharpCommonEvent

/-!
# T503: first-cell deterministic exponent absorption

For the fixed first-cell exponents, all quantitative moment-budget terms
are eventually absorbed by the literal target with coefficient one,
uniformly for the endpoint ratio in `[1,2]`.
-/

namespace RBM.APrimeFirstCellExponentAbsorption

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ :=
  APrimeFirstCellDriftBadPayment.fixedDelta

noncomputable def alpha : ℝ := delta / 16

noncomputable def beta : ℝ := 1

noncomputable def driftConstant : ℝ :=
  APrimeFirstCellDriftCoefficient.coefficientConstant * (Real.sqrt 2 + 1)

/-- The literal deterministic ledger from T482 after setting
`delta=1/2000`, `alpha=delta/16`, and `beta=1`. -/
noncomputable def momentRhs (p N : ℕ) (R : ℝ) : ℝ :=
  (N : ℝ) ^ (5 * delta / 32) * R ^ (-(2 : ℝ)) +
  driftConstant * (N : ℝ) ^ (delta / 8) * R ^ (-(2 : ℝ)) +
  2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
      (N : ℝ) ^ (-31 * delta / 16) * R ^ (-(2 : ℝ)) +
  Real.sqrt (2 * (p : ℝ) - 1) *
    (384 * Real.sqrt 3 * (N : ℝ) ^ (delta / 32) *
        R ^ (-(2 : ℝ)) +
      Real.sqrt (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2)) +
  (N : ℝ)⁻¹

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
  driftConstant * (N : ℝ) ^ (delta / 8) +
  2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
      (N : ℝ) ^ (-31 * delta / 16) +
  (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
      (N : ℝ) ^ (delta / 32) +
  (4 * Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ)) *
      (N : ℝ) ^ (-(1 : ℝ) / 2) +
  4 * (N : ℝ) ^ (-(1 : ℝ))

private theorem momentRhs_le_ratio_mul_absorbedSum {p N : ℕ} (hp : 1 ≤ p)
    {R : ℝ} (hR1 : 1 ≤ R) (hR2 : R ≤ 2) :
    momentRhs p N R ≤ R ^ (-(2 : ℝ)) * absorbedSum p N := by
  have hfloor := ratio_neg_two_floor hR1 hR2
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hsqrt : 0 ≤ Real.sqrt (2 * (p : ℝ) - 1) := Real.sqrt_nonneg _
  have hNhalf : 0 ≤
      Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ) *
        (N : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hNone : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hhalf := additive_le_ratio_mul_four hNhalf hfloor
  have hone := additive_le_ratio_mul_four hNone hfloor
  unfold momentRhs absorbedSum
  calc
    _ =
        R ^ (-(2 : ℝ)) *
          ((N : ℝ) ^ (5 * delta / 32) +
            driftConstant * (N : ℝ) ^ (delta / 8) +
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
            driftConstant * (N : ℝ) ^ (delta / 8) +
            2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
              (N : ℝ) ^ (-31 * delta / 16) +
            (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
              (N : ℝ) ^ (delta / 32)) +
          R ^ (-(2 : ℝ)) *
            (4 * (Real.sqrt (2 * (p : ℝ) - 1) *
              Real.sqrt (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2))) +
          R ^ (-(2 : ℝ)) * (4 * (N : ℝ)⁻¹) := by
      gcongr
    _ = R ^ (-(2 : ℝ)) *
        ((N : ℝ) ^ (5 * delta / 32) +
          driftConstant * (N : ℝ) ^ (delta / 8) +
          2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
            (N : ℝ) ^ (-31 * delta / 16) +
          (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
            (N : ℝ) ^ (delta / 32) +
          (4 * Real.sqrt (2 * (p : ℝ) - 1) *
            Real.sqrt (1 / 2 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ) / 2) +
          4 * (N : ℝ) ^ (-(1 : ℝ))) := by
      rw [show (N : ℝ)⁻¹ = (N : ℝ) ^ (-(1 : ℝ)) by
        simp only [Real.rpow_neg_one]]
      ring

/-- The exact T482 ledger is eventually absorbed with coefficient one.
The moment order is fixed before the eventual threshold, and the estimate
is uniform for every `1 ≤ R ≤ 2`. -/
theorem eventually_momentRhs_le (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, 1 ≤ R → R ≤ 2 →
      momentRhs p N R ≤
        (N : ℝ) ^ (delta / 4) * R ^ (-(2 : ℝ)) := by
  have h1 : 5 * delta / 32 < delta / 4 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have h2 : delta / 8 < delta / 4 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have h3 : -31 * delta / 16 < delta / 4 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have h4 : delta / 32 < delta / 4 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have h5 : -(1 : ℝ) / 2 < delta / 4 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have h6 : -(1 : ℝ) < delta / 4 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  filter_upwards [
    SumZeroDyn.eventually_const_mul_rpow_le 6 h1,
    SumZeroDyn.eventually_const_mul_rpow_le (6 * driftConstant) h2,
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
  have htarget : 0 ≤ (N : ℝ) ^ (delta / 4) := by positivity
  have hs : absorbedSum p N ≤ (N : ℝ) ^ (delta / 4) := by
    unfold absorbedSum
    have hN1' :
        (N : ℝ) ^ (5 * delta / 32) ≤
          (N : ℝ) ^ (delta / 4) / 6 := by nlinarith
    have hN2' :
        driftConstant * (N : ℝ) ^ (delta / 8) ≤
          (N : ℝ) ^ (delta / 4) / 6 := by nlinarith
    have hN3' :
        2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
            (N : ℝ) ^ (-31 * delta / 16) ≤
          (N : ℝ) ^ (delta / 4) / 6 := by nlinarith
    have hN4' :
        (Real.sqrt (2 * (p : ℝ) - 1) * (384 * Real.sqrt 3)) *
            (N : ℝ) ^ (delta / 32) ≤
          (N : ℝ) ^ (delta / 4) / 6 := by nlinarith
    have hN5' :
        (4 * Real.sqrt (2 * (p : ℝ) - 1) * Real.sqrt (1 / 2 : ℝ)) *
            (N : ℝ) ^ (-(1 : ℝ) / 2) ≤
          (N : ℝ) ^ (delta / 4) / 6 := by nlinarith
    have hN6' :
        4 * (N : ℝ) ^ (-(1 : ℝ)) ≤
          (N : ℝ) ^ (delta / 4) / 6 := by nlinarith
    linarith
  exact (momentRhs_le_ratio_mul_absorbedSum hp hR1 hR2).trans
    (by
      rw [mul_comm (R ^ (-(2 : ℝ)))]
      exact mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (by positivity) _))

/-- The accepted first-cell event has an actual positive `k=2` resident
whose endpoint ratio lies in `[1,2]`, on that same literal event. -/
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
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  have hδ : 0 < delta := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have hδ100 : delta ≤ 1 / 100 := by
    norm_num [delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  have hα : 0 < alpha := by
    norm_num [alpha, delta, APrimeFirstCellDriftBadPayment.fixedDelta]
  obtain ⟨hmeas, hprob, hplateau⟩ := hall delta hδ hδ100 alpha hα
  refine ⟨τ', hτ', hmeas, hprob, ?_⟩
  filter_upwards [
    APrimeFirstCellScaleFloors.eventually_positive_two_scalePackage hτ',
    hplateau] with N hscale hresident
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hresident
  obtain ⟨ω, hω, _hk, _hw, _hv0, _hvT, _hT, _hsource,
    _hJall, _hJ0, _hJv⟩ := hresident
  exact ⟨hscale.1, hscale.2.one_le_ratio, hscale.2.ratio_le_two,
    ω, hω, trivial⟩

#print axioms eventually_momentRhs_le
#print axioms positive_two_same_sharpCommonEvent_witness

end
end RBM.APrimeFirstCellExponentAbsorption
