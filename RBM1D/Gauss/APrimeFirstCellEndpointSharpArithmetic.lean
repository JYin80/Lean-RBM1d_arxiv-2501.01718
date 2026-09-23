/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilySharpArithmetic
import RBM1D.Gauss.APrimeFirstCellExponentAbsorptionSharp

/-!
# T530: strict-margin first-cell endpoint arithmetic

The two-coordinate family cost is sharpened to `delta / 40`.  Its product
with T526's `delta / 5` rate has exponent `9 * delta / 40`, leaving the
strict gap `delta / 40` needed to absorb the endpoint baseline uniformly
for `1 ≤ R ≤ 2`.
-/

namespace RBM.APrimeFirstCellEndpointSharpArithmetic

open Filter Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ :=
  APrimeFirstCellFamilySharpArithmetic.delta

/-- At fixed order `P ≥ 80000`, the exact family-root cost is at most
`N^(delta/40)`. -/
theorem family_card_root_le {N P : ℕ} (hN : 81 ≤ N) (hP : 80000 ≤ P) :
    (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
        ((1 : ℝ) / (2 * (P : ℝ))) ≤
      (N : ℝ) ^ (delta / 40) := by
  have hNr : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hPr : (80000 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hcard :
      (Fintype.card (LoopArg (d.L N) 2) : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast APrimeFirstCellFamilyHighMoment.family_card_le hN
  have hpexp : (1 : ℝ) / (P : ℝ) ≤ delta / 40 := by
    rw [div_le_iff₀ hP0]
    norm_num [delta, APrimeFirstCellFamilySharpArithmetic.delta,
      APrimeFirstCellExponentAbsorptionSharp.delta,
      APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
    linarith
  calc
    _ ≤ ((N : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / (2 * (P : ℝ))) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)
    _ = (N : ℝ) ^ ((1 : ℝ) / (P : ℝ)) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      congr 1
      push_cast
      field_simp
    _ ≤ (N : ℝ) ^ (delta / 40) :=
      Real.rpow_le_rpow_of_exponent_le hNr hpexp

/-- Exact exponent bookkeeping and the strict remaining margin. -/
theorem sharp_exponent_bookkeeping :
    delta / 40 + delta / 5 = 9 * delta / 40 ∧
      9 * delta / 40 < delta / 4 := by
  constructor
  · ring
  · norm_num [delta, APrimeFirstCellFamilySharpArithmetic.delta,
      APrimeFirstCellExponentAbsorptionSharp.delta,
      APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]

/-- The family cost times T526's rate has exactly exponent
`9 * delta / 40`. -/
theorem sharp_exponent_product_eq {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (delta / 40) * (N : ℝ) ^ (delta / 5) =
      (N : ℝ) ^ (9 * delta / 40) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [← Real.rpow_add hN0, sharp_exponent_bookkeeping.1]

/-- Eventually the strict exponent margin absorbs both the endpoint
baseline and the coefficient-one main term, uniformly on `1 ≤ R ≤ 2`. -/
theorem eventually_endpoint_le :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, 1 ≤ R → R ≤ 2 →
      R ^ (-(4 : ℝ)) + (N : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) ≤
        (N : ℝ) ^ (delta / 4) * R ^ (-(2 : ℝ)) := by
  have hzero : (0 : ℝ) < delta / 4 := by
    norm_num [delta, APrimeFirstCellFamilySharpArithmetic.delta,
      APrimeFirstCellExponentAbsorptionSharp.delta,
      APrimeFirstCellExponentAbsorption.delta,
      APrimeFirstCellDriftBadPayment.fixedDelta]
  have hgap : 9 * delta / 40 < delta / 4 :=
    sharp_exponent_bookkeeping.2
  filter_upwards [
    SumZeroDyn.eventually_const_mul_rpow_le 2 hzero,
    SumZeroDyn.eventually_const_mul_rpow_le 2 hgap]
      with N hbase hmain
  intro R hR1 _hR2
  have hRpow : R ^ (-(4 : ℝ)) ≤ R ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hRnonneg : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hpowZero : (N : ℝ) ^ (0 : ℝ) = 1 := by simp
  rw [hpowZero, mul_one] at hbase
  have hbase' : (1 : ℝ) ≤ (N : ℝ) ^ (delta / 4) / 2 := by
    linarith
  have hmain' : (N : ℝ) ^ (9 * delta / 40) ≤
      (N : ℝ) ^ (delta / 4) / 2 := by
    linarith
  have hcoeff : 1 + (N : ℝ) ^ (9 * delta / 40) ≤
      (N : ℝ) ^ (delta / 4) := by
    linarith
  calc
    _ ≤ R ^ (-(2 : ℝ)) +
        (N : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) :=
      add_le_add hRpow (le_refl _)
    _ = (1 + (N : ℝ) ^ (9 * delta / 40)) * R ^ (-(2 : ℝ)) := by ring
    _ ≤ (N : ℝ) ^ (delta / 4) * R ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hRnonneg

/-- The uniform theorem contains both closed interval endpoints literally. -/
theorem eventually_endpoint_boundaries :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ^ (-(4 : ℝ)) +
          (N : ℝ) ^ (9 * delta / 40) * (1 : ℝ) ^ (-(2 : ℝ)) ≤
        (N : ℝ) ^ (delta / 4) * (1 : ℝ) ^ (-(2 : ℝ)) ∧
      (2 : ℝ) ^ (-(4 : ℝ)) +
          (N : ℝ) ^ (9 * delta / 40) * (2 : ℝ) ^ (-(2 : ℝ)) ≤
        (N : ℝ) ^ (delta / 4) * (2 : ℝ) ^ (-(2 : ℝ)) := by
  filter_upwards [eventually_endpoint_le] with N hN
  exact ⟨hN 1 (by norm_num) (by norm_num), hN 2 (by norm_num) (by norm_num)⟩

/-- Explicit numerical values inhabit the fixed-size premises, while the
same witness retains the eventual uniform estimate and both boundaries. -/
theorem admissible_numeric_eventual_witness :
    ∃ N P : ℕ, 81 ≤ N ∧ 80000 ≤ P ∧
      (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (P : ℝ))) ≤
        (N : ℝ) ^ (delta / 40) ∧
      (∀ᶠ M : ℕ in atTop,
        (∀ R : ℝ, 1 ≤ R → R ≤ 2 →
          R ^ (-(4 : ℝ)) +
              (M : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) ≤
            (M : ℝ) ^ (delta / 4) * R ^ (-(2 : ℝ))) ∧
        ((1 : ℝ) ^ (-(4 : ℝ)) +
              (M : ℝ) ^ (9 * delta / 40) * (1 : ℝ) ^ (-(2 : ℝ)) ≤
            (M : ℝ) ^ (delta / 4) * (1 : ℝ) ^ (-(2 : ℝ))) ∧
        ((2 : ℝ) ^ (-(4 : ℝ)) +
              (M : ℝ) ^ (9 * delta / 40) * (2 : ℝ) ^ (-(2 : ℝ)) ≤
            (M : ℝ) ^ (delta / 4) * (2 : ℝ) ^ (-(2 : ℝ)))) := by
  refine ⟨81, 80000, by norm_num, by norm_num,
    family_card_root_le (by norm_num) (by norm_num), ?_⟩
  filter_upwards [eventually_endpoint_le, eventually_endpoint_boundaries]
      with M hM hMb
  exact ⟨hM, hMb.1, hMb.2⟩

#print axioms family_card_root_le
#print axioms sharp_exponent_bookkeeping
#print axioms sharp_exponent_product_eq
#print axioms eventually_endpoint_le
#print axioms eventually_endpoint_boundaries
#print axioms admissible_numeric_eventual_witness

end
end RBM.APrimeFirstCellEndpointSharpArithmetic
