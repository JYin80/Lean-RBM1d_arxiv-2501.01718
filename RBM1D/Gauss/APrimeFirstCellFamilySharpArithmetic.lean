/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyHighMoment
import RBM1D.Gauss.APrimeFirstCellExponentAbsorptionSharp

/-!
# T529: sharp finite-family arithmetic for the first cell

The exact two-coordinate family cost is paid at exponent `delta / 20`
when the fixed moment order is at least `40000`.  Combining this cost with
T526's `delta / 5` deterministic bound gives exactly `delta / 4`.
-/

namespace RBM.APrimeFirstCellFamilySharpArithmetic

open Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ :=
  APrimeFirstCellExponentAbsorptionSharp.delta

/-- For `P ≥ 40000`, the exact finite-family root cost is at most
`N^(delta/20)`. -/
theorem family_card_root_le {N P : ℕ} (hN : 81 ≤ N) (hP : 40000 ≤ P) :
    (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
        ((1 : ℝ) / (2 * (P : ℝ))) ≤
      (N : ℝ) ^ (delta / 20) := by
  have hNr : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hPr : (40000 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hcard :
      (Fintype.card (LoopArg (d.L N) 2) : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast APrimeFirstCellFamilyHighMoment.family_card_le hN
  have hpexp : (1 : ℝ) / (P : ℝ) ≤ delta / 20 := by
    rw [div_le_iff₀ hP0]
    norm_num [delta, APrimeFirstCellExponentAbsorptionSharp.delta,
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
    _ ≤ (N : ℝ) ^ (delta / 20) :=
      Real.rpow_le_rpow_of_exponent_le hNr hpexp

/-- The sharp family exponent and T526's deterministic exponent add exactly
to the first-cell target exponent. -/
theorem sharp_exponent_product_eq {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (delta / 20) * (N : ℝ) ^ (delta / 5) =
      (N : ℝ) ^ (delta / 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [← Real.rpow_add hN0]
  congr 1
  ring

/-- Inequality form of the exact exponent payment. -/
theorem sharp_exponent_product_le {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (delta / 20) * (N : ℝ) ^ (delta / 5) ≤
      (N : ℝ) ^ (delta / 4) := by
  exact (sharp_exponent_product_eq hN).le

/-- The numerical hypotheses are simultaneously inhabited, including both
requested deterministic conclusions. -/
theorem admissible_numeric_witness :
    ∃ N P : ℕ, 81 ≤ N ∧ 40000 ≤ P ∧
      (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (P : ℝ))) ≤
        (N : ℝ) ^ (delta / 20) ∧
      (N : ℝ) ^ (delta / 20) * (N : ℝ) ^ (delta / 5) ≤
        (N : ℝ) ^ (delta / 4) := by
  refine ⟨81, 40000, by norm_num, by norm_num, ?_, ?_⟩
  · exact family_card_root_le (by norm_num) (by norm_num)
  · exact sharp_exponent_product_le (by norm_num)

#print axioms family_card_root_le
#print axioms sharp_exponent_product_eq
#print axioms sharp_exponent_product_le
#print axioms admissible_numeric_witness

end
end RBM.APrimeFirstCellFamilySharpArithmetic
