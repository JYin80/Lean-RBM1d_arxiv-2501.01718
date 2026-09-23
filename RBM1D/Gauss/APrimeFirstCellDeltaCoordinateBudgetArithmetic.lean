/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFullCrossBudget
import RBM1D.Gauss.APrimeFirstCellDeltaQVNormBudget
import RBM1D.Gauss.APrimeFirstCellDeltaDriftIntegralBudget
import RBM1D.Gauss.APrimeFirstCellDeltaInitialMomentBudget

/-!
# T554: variable-delta coordinate-budget exponent absorption

This file performs only the deterministic real-power arithmetic for the four
public numerical right-hand sides produced in T544--T547.  In particular, the
cross contribution is twice the integral budget for the literal `Bfull`; it is
not the separately defined `BcrossActual` budget.
-/

namespace RBM.APrimeFirstCellDeltaCoordinateBudgetArithmetic

open Filter

noncomputable section

/-- The exponent choice used in the first-cell coordinate estimate. -/
noncomputable def alpha (delta : Real) : Real := delta / 16

/-- The error exponent used in the first-cell coordinate estimate. -/
noncomputable def beta (delta : Real) : Real := delta

/-- T547's numerical initial-coordinate right-hand side, with the scale named `R`. -/
noncomputable def initialBudget (delta : Real) (N : Nat) (R : Real) : Real :=
  (N : Real) ^ (5 * delta / 32) * R ^ (-(2 : Real))

/-- T541's absorbed drift rate, with the scale named `R`. -/
noncomputable def absorbedRateAt (a : Real) (N : Nat) (R : Real) : Real :=
  APrimeFirstCellDriftCoefficient.coefficientConstant * (Real.sqrt 2 + 1) *
    (N : Real) ^ (2 * a) * R ^ (-(2 : Real))

/-- T546's complete numerical drift contribution. -/
noncomputable def driftBudget (delta : Real) (N : Nat) (R : Real) : Real :=
  absorbedRateAt (alpha delta) N R + (N : Real) ^ (-beta delta)

/-- The outer Minkowski factor `2` applied to T544's literal-`Bfull` integral. -/
noncomputable def literalCrossIntegralBudget
    (delta : Real) (P N : Nat) (R : Real) : Real :=
  2 * APrimeFirstCellDeltaFullCrossBudget.budgetConstant P *
    (N : Real) ^ (alpha delta - 2 * delta) * R ^ (-(2 : Real))

/-- T545's explicit square-root QV right-hand side, with the scale named `R`. -/
noncomputable def qvSqrtBudget
    (delta : Real) (P N : Nat) (R v : Real) : Real :=
  Real.sqrt ((2 : Real) * P - 1) *
    (384 * Real.sqrt 3 * (N : Real) ^ (alpha delta / 2) *
        R ^ (-(2 : Real)) +
      Real.sqrt v * (N : Real) ^ (-beta delta / 2))

/-- The exact four-term Minkowski budget to be absorbed. -/
noncomputable def totalBudget
    (delta : Real) (P N : Nat) (R v : Real) : Real :=
  initialBudget delta N R + driftBudget delta N R +
    literalCrossIntegralBudget delta P N R +
      qvSqrtBudget delta P N R v

/-- The fixed-order constant used by the common-exponent envelope. -/
noncomputable def envelopeConstant (P : Nat) : Real :=
  1 +
    (APrimeFirstCellDriftCoefficient.coefficientConstant *
      (Real.sqrt 2 + 1) + 4) +
    2 * APrimeFirstCellDeltaFullCrossBudget.budgetConstant P +
    Real.sqrt ((2 : Real) * P - 1) * (384 * Real.sqrt 3 + 4)

theorem absorbedRateAt_eq_public (a : Real) (N : Nat) (v : Real) :
    absorbedRateAt a N (APrimeFirstCellLoopCap.xRate v) =
      APrimeFirstCellDeltaDriftCoefficientAbsorbed.absorbedRate a N v := rfl

/-- This identity records that there is one outer factor `2`, applied to the
literal T544 budget; no `BcrossActual` factor is inserted. -/
theorem literalCrossIntegralBudget_eq_two_literal
    (delta : Real) (P N : Nat) (v : Real) :
    literalCrossIntegralBudget delta P N
        (APrimeFirstCellLoopCap.xRate v) =
      2 * APrimeFirstCellDeltaFullCrossBudget.budgetConstant P *
        APrimeFirstCellDeltaFullCrossBudget.crossScale
          delta (alpha delta) N v := by
  unfold literalCrossIntegralBudget APrimeFirstCellDeltaFullCrossBudget.crossScale
  ring

theorem alpha_eq (delta : Real) : alpha delta = delta / 16 := rfl

theorem beta_eq (delta : Real) : beta delta = delta := rfl

/-- The smallest gap, coming from the initial contribution. -/
theorem initial_exponent_gap (delta : Real) :
    delta / 5 - 5 * delta / 32 = 7 * delta / 160 := by ring

theorem initial_exponent_gap_pos {delta : Real} (hdelta : 0 < delta) :
    0 < delta / 5 - 5 * delta / 32 := by
  rw [initial_exponent_gap]
  positivity

theorem drift_exponent_gap (delta : Real) :
    delta / 5 - 2 * alpha delta = 3 * delta / 40 := by
  unfold alpha
  ring

theorem cross_exponent_gap (delta : Real) :
    delta / 5 - (alpha delta - 2 * delta) = 171 * delta / 80 := by
  unfold alpha
  ring

theorem qv_current_exponent_gap (delta : Real) :
    delta / 5 - alpha delta / 2 = 27 * delta / 160 := by
  unfold alpha
  ring

theorem drift_error_exponent_gap (delta : Real) :
    delta / 5 - (-beta delta) = 6 * delta / 5 := by
  unfold beta
  ring

theorem qv_error_exponent_gap (delta : Real) :
    delta / 5 - (-beta delta / 2) = 7 * delta / 10 := by
  unfold beta
  ring

/-- All six exponents lie strictly below the target exponent. -/
theorem all_exponent_gaps_pos {delta : Real} (hdelta : 0 < delta) :
    0 < delta / 5 - 5 * delta / 32 ∧
    0 < delta / 5 - 2 * alpha delta ∧
    0 < delta / 5 - (alpha delta - 2 * delta) ∧
    0 < delta / 5 - alpha delta / 2 ∧
    0 < delta / 5 - (-beta delta) ∧
    0 < delta / 5 - (-beta delta / 2) := by
  rw [initial_exponent_gap, drift_exponent_gap, cross_exponent_gap,
    qv_current_exponent_gap, drift_error_exponent_gap,
    qv_error_exponent_gap]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem envelopeConstant_nonneg (P : Nat) (hP : 1 <= P) :
    0 <= envelopeConstant P := by
  have hcoef : 0 <= (2 : Real) * P - 1 := by
    have hPR : (1 : Real) <= P := by exact_mod_cast hP
    linarith
  unfold envelopeConstant
  have hcross := APrimeFirstCellDeltaFullCrossBudget.budgetConstant_nonneg P
  have hdrift := APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
  positivity

private theorem one_le_four_mul_scale {R : Real}
    (hR1 : 1 <= R) (hR2 : R <= 2) :
    1 <= 4 * R ^ (-(2 : Real)) := by
  have h := Real.rpow_le_rpow_of_nonpos
    (zero_lt_one.trans_le hR1) hR2 (by norm_num : (-(2 : Real)) <= 0)
  have htwo : (2 : Real) ^ (-(2 : Real)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
    norm_num [Real.rpow_natCast]
  rw [htwo] at h
  nlinarith

private theorem rpow_le_initial_exponent {delta exponent : Real} {N : Nat}
    (hN : 1 <= N) (hexponent : exponent <= 5 * delta / 32) :
    (N : Real) ^ exponent <= (N : Real) ^ (5 * delta / 32) := by
  have hNR : (1 : Real) <= N := by exact_mod_cast hN
  exact Real.rpow_le_rpow_of_exponent_le hNR hexponent

/-- Before the last strict-gap absorption, all four public contributions fit
under one fixed-order multiple of the largest source exponent. -/
theorem totalBudget_le_envelope {delta : Real} (hdelta : 0 < delta)
    {P N : Nat} (_hP : 1 <= P) {R v : Real}
    (hN : 1 <= N) (hR1 : 1 <= R) (hR2 : R <= 2)
    (hv0 : 0 <= v) (hvhalf : v <= 1 / 2) :
    totalBudget delta P N R v <=
      envelopeConstant P * (N : Real) ^ (5 * delta / 32) *
        R ^ (-(2 : Real)) := by
  let M : Real := (N : Real) ^ (5 * delta / 32)
  let S : Real := R ^ (-(2 : Real))
  let Cd : Real := APrimeFirstCellDriftCoefficient.coefficientConstant *
    (Real.sqrt 2 + 1)
  let Cx : Real := APrimeFirstCellDeltaFullCrossBudget.budgetConstant P
  let Q : Real := Real.sqrt ((2 : Real) * P - 1)
  have hM0 : 0 <= M := by dsimp [M]; positivity
  have hS0 : 0 <= S := by dsimp [S]; positivity
  have hCd0 : 0 <= Cd := by
    dsimp [Cd]
    exact mul_nonneg APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
      (add_nonneg (Real.sqrt_nonneg 2) zero_le_one)
  have hCx0 : 0 <= Cx := by
    exact APrimeFirstCellDeltaFullCrossBudget.budgetConstant_nonneg P
  have hQ0 : 0 <= Q := Real.sqrt_nonneg _
  have hscale : 1 <= 4 * S := by
    dsimp [S]
    exact one_le_four_mul_scale hR1 hR2
  have hmainPos : 0 <= M * S := mul_nonneg hM0 hS0
  have hinit : initialBudget delta N R = M * S := by rfl
  have hdriftPow :
      (N : Real) ^ (2 * alpha delta) <= M := by
    apply rpow_le_initial_exponent hN
    unfold alpha
    linarith
  have hcrossPow :
      (N : Real) ^ (alpha delta - 2 * delta) <= M := by
    apply rpow_le_initial_exponent hN
    unfold alpha
    linarith
  have hqvPow :
      (N : Real) ^ (alpha delta / 2) <= M := by
    apply rpow_le_initial_exponent hN
    unfold alpha
    linarith
  have hdriftErrPow : (N : Real) ^ (-beta delta) <= M := by
    apply rpow_le_initial_exponent hN
    unfold beta
    linarith
  have hqvErrPow : (N : Real) ^ (-beta delta / 2) <= M := by
    apply rpow_le_initial_exponent hN
    unfold beta
    linarith
  have hsqrtv : Real.sqrt v <= 1 := by
    have hs0 := Real.sqrt_nonneg v
    have hsq := Real.sq_sqrt hv0
    nlinarith
  have hdrift : driftBudget delta N R <= (Cd + 4) * M * S := by
    have hfirst : Cd * (N : Real) ^ (2 * alpha delta) * S <= Cd * M * S := by
      gcongr
    have herr : (N : Real) ^ (-beta delta) <= 4 * M * S := by
      calc
        (N : Real) ^ (-beta delta) <= M := hdriftErrPow
        _ <= 4 * S * M := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hM0
        _ = 4 * M * S := by ring
    unfold driftBudget absorbedRateAt
    change Cd * (N : Real) ^ (2 * alpha delta) * S +
        (N : Real) ^ (-beta delta) <= (Cd + 4) * M * S
    nlinarith
  have hcross : literalCrossIntegralBudget delta P N R <=
      (2 * Cx) * M * S := by
    unfold literalCrossIntegralBudget
    change 2 * Cx * (N : Real) ^ (alpha delta - 2 * delta) * S <=
      (2 * Cx) * M * S
    gcongr
  have hqv : qvSqrtBudget delta P N R v <=
      Q * (384 * Real.sqrt 3 + 4) * M * S := by
    have hcurrent :
        384 * Real.sqrt 3 * (N : Real) ^ (alpha delta / 2) * S <=
          384 * Real.sqrt 3 * M * S := by
      gcongr
    have herr0 : Real.sqrt v * (N : Real) ^ (-beta delta / 2) <= M := by
      calc
        Real.sqrt v * (N : Real) ^ (-beta delta / 2) <=
            1 * (N : Real) ^ (-beta delta / 2) := by gcongr
        _ <= M := by simpa using hqvErrPow
    have herr : Real.sqrt v * (N : Real) ^ (-beta delta / 2) <=
        4 * M * S := by
      calc
        Real.sqrt v * (N : Real) ^ (-beta delta / 2) <= M := herr0
        _ <= 4 * S * M := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hM0
        _ = 4 * M * S := by ring
    unfold qvSqrtBudget
    change Q *
      (384 * Real.sqrt 3 * (N : Real) ^ (alpha delta / 2) * S +
        Real.sqrt v * (N : Real) ^ (-beta delta / 2)) <=
      Q * (384 * Real.sqrt 3 + 4) * M * S
    have hinside :
        384 * Real.sqrt 3 * (N : Real) ^ (alpha delta / 2) * S +
            Real.sqrt v * (N : Real) ^ (-beta delta / 2) <=
          (384 * Real.sqrt 3 + 4) * M * S := by
      nlinarith
    calc
      Q * (384 * Real.sqrt 3 * (N : Real) ^ (alpha delta / 2) * S +
          Real.sqrt v * (N : Real) ^ (-beta delta / 2)) <=
          Q * ((384 * Real.sqrt 3 + 4) * M * S) :=
        mul_le_mul_of_nonneg_left hinside hQ0
      _ = Q * (384 * Real.sqrt 3 + 4) * M * S := by ring
  unfold totalBudget envelopeConstant
  change M * S + driftBudget delta N R +
      literalCrossIntegralBudget delta P N R +
        qvSqrtBudget delta P N R v <=
    (1 + (Cd + 4) + 2 * Cx + Q * (384 * Real.sqrt 3 + 4)) * M * S
  nlinarith

/-- For fixed positive `delta` and fixed moment order, the exact coordinate
budget is eventually absorbed by `N^(delta/5) R^-2`, uniformly over the full
first-cell geometric ranges for `R` and `v`. -/
theorem eventually_totalBudget_le {delta : Real} (hdelta : 0 < delta)
    (P : Nat) (hP : 1 <= P) :
    ∀ᶠ N : Nat in atTop, ∀ R v : Real,
      1 <= R -> R <= 2 -> 0 <= v -> v <= 1 / 2 ->
      totalBudget delta P N R v <=
        (N : Real) ^ (delta / 5) * R ^ (-(2 : Real)) := by
  have hgap : 0 < delta / 5 - 5 * delta / 32 :=
    initial_exponent_gap_pos hdelta
  filter_upwards [eventually_le_rpow (envelopeConstant P) hgap,
    eventually_ge_atTop 1] with N hconstant hN
  intro R v hR1 hR2 hv0 hvhalf
  have henv := totalBudget_le_envelope hdelta hP hN hR1 hR2 hv0 hvhalf
  have hNR : (0 : Real) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hpow0 : 0 <= (N : Real) ^ (5 * delta / 32) := by positivity
  have hscale0 : 0 <= R ^ (-(2 : Real)) := by positivity
  calc
    totalBudget delta P N R v <=
        envelopeConstant P * (N : Real) ^ (5 * delta / 32) *
          R ^ (-(2 : Real)) := henv
    _ <= (N : Real) ^ (delta / 5 - 5 * delta / 32) *
          (N : Real) ^ (5 * delta / 32) * R ^ (-(2 : Real)) := by
      gcongr
    _ = (N : Real) ^ (delta / 5) * R ^ (-(2 : Real)) := by
      rw [← Real.rpow_add hNR]
      congr 2
      ring

#print axioms absorbedRateAt_eq_public
#print axioms literalCrossIntegralBudget_eq_two_literal
#print axioms alpha_eq
#print axioms beta_eq
#print axioms initial_exponent_gap
#print axioms initial_exponent_gap_pos
#print axioms drift_exponent_gap
#print axioms cross_exponent_gap
#print axioms qv_current_exponent_gap
#print axioms drift_error_exponent_gap
#print axioms qv_error_exponent_gap
#print axioms all_exponent_gaps_pos
#print axioms envelopeConstant_nonneg
#print axioms totalBudget_le_envelope
#print axioms eventually_totalBudget_le

end

end RBM.APrimeFirstCellDeltaCoordinateBudgetArithmetic
