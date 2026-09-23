/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeOneStep

/-!
# T553: variable-delta cutoff-integral conversion

This module isolates the final analytic conversion used after a first-cell
weighted moment-norm estimate.  It assumes the weighted moment estimate; it
does not produce a family or endpoint bound.
-/

namespace RBM.APrimeFirstCellDeltaCutTruncIntegral

open MeasureTheory Gauss
open RBM.MomentDuhamel MomentDuhamelCut

noncomputable section

/-- Raising the variable-delta moment-norm bound to the power `2 * p`
produces exactly the required constant and exponent. -/
theorem normBound_pow_eq {delta : Real} {p N : Nat} (hN : 1 <= N) :
    (2 * (N : Real) ^ (delta / 4)) ^ (2 * p) =
      2 ^ (2 * p) * (N : Real) ^ ((delta / 2) * (p : Real)) := by
  have hNpos : (0 : Real) < N := by
    exact_mod_cast (show 0 < N by omega)
  rw [mul_pow, ← Real.rpow_natCast ((N : Real) ^ (delta / 4)) (2 * p),
    ← Real.rpow_mul hNpos.le]
  congr 1
  push_cast
  ring_nf

/-- The positive-order cutoff integral follows from an honest weighted-power
integrability premise and a moment-norm bound for the same weight, observable,
and probability measure.  Nonnegativity of `J` is the exact hypothesis used
to contract `cutTrunc` pointwise. -/
theorem integral_cutTrunc_le_of_momNormW
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W J : Ω -> Real} {delta : Real} {p N : Nat}
    (hp : 1 <= p) (hN : 1 <= N)
    (hW0 : forall omega, 0 <= W omega)
    (_hW1 : forall omega, W omega <= 1)
    (_hWm : AEStronglyMeasurable W P)
    (hJ0 : forall omega, 0 <= J omega)
    (hJint : Integrable (fun omega => W omega * |J omega| ^ (2 * p)) P)
    (hnorm : momNormW P W p J <= 2 * (N : Real) ^ (delta / 4)) :
    (∫ omega, W omega *
      |cutTrunc ((N : Real) ^ (2 * delta)) (J omega)| ^ (2 * p) ∂P) <=
        2 ^ (2 * p) * (N : Real) ^ ((delta / 2) * (p : Real)) := by
  have hraw := APrimeOneStep.integral_cutTrunc_le_of_momNormW_le
    (P := P) (W := W) (Y := J) (Jf := J)
    (θ := (N : Real) ^ (2 * delta)) hW0 hp hJint (fun omega => by
      rw [abs_of_nonneg (cutTrunc_nonneg (hJ0 omega)),
        abs_of_nonneg (hJ0 omega)]
      exact cutTrunc_le_self (hJ0 omega)) hnorm
  exact hraw.trans_eq (normBound_pow_eq (delta := delta) hN)

/-- At `p = 0`, the integrand is the weight and is bounded directly by one;
the moment norm is deliberately not used. -/
theorem integral_cutTrunc_zero_le
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W J : Ω -> Real} {delta : Real} {N : Nat}
    (hW0 : forall omega, 0 <= W omega)
    (hW1 : forall omega, W omega <= 1)
    (hWm : AEStronglyMeasurable W P) :
    (∫ omega, W omega *
      |cutTrunc ((N : Real) ^ (2 * delta)) (J omega)| ^ (2 * 0) ∂P) <=
        2 ^ (2 * 0) * (N : Real) ^ ((delta / 2) * (0 : Real)) := by
  have hzero := Gauss.integral_weight_pow_zero_le
    (P := P) (W := W) (J := J)
    (θ := (N : Real) ^ (2 * delta)) hW0 hW1 hWm
  simpa using hzero

/-- The conditional interface is genuinely satisfiable on the nonzero
one-point Dirac probability space: take weight one and the zero observable.
The measure of the whole space is recorded as one, so this is not a
zero-measure witness. -/
theorem conditional_interface_satisfiable :
    let P0 : Measure Unit := Measure.dirac ()
    let W : Unit -> Real := fun _ => 1
    let J : Unit -> Real := fun _ => 0
    P0 Set.univ = 1 ∧
      (forall omega, 0 <= W omega) ∧
      (forall omega, W omega <= 1) ∧
      AEStronglyMeasurable W P0 ∧
      (forall omega, 0 <= J omega) ∧
      Integrable (fun omega => W omega * |J omega| ^ (2 * 1)) P0 ∧
      momNormW P0 W 1 J <=
        2 * (1 : Real) ^ ((1 / 100 : Real) / 4) ∧
      (∫ omega, W omega *
        |cutTrunc ((1 : Real) ^ (2 * (1 / 100 : Real))) (J omega)| ^ (2 * 1)
          ∂P0) <=
        2 ^ (2 * 1) * (1 : Real) ^ (((1 / 100 : Real) / 2) * (1 : Real)) := by
  dsimp only
  simp [momNormW]

#print axioms normBound_pow_eq
#print axioms integral_cutTrunc_le_of_momNormW
#print axioms integral_cutTrunc_zero_le
#print axioms conditional_interface_satisfiable

end

end RBM.APrimeFirstCellDeltaCutTruncIntegral
