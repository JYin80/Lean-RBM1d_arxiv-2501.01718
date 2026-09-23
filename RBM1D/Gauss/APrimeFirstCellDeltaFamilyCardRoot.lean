/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaTargetWeight
import RBM1D.Gauss.APrimeFirstCellFamilyHighMoment

/-!
# T548: variable-delta finite-family root arithmetic

The high order `max p ceil(20 / delta)` pays the exact two-coordinate family
cardinality by `N^(delta / 20)`.  This file contains only deterministic
arithmetic and no moment, event, or assembly statement.
-/

namespace RBM.APrimeFirstCellDeltaFamilyCardRoot

open Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

open APrimeFirstCellDeltaTargetWeight

/-- The ceiling in `highOrder` gives the exact reciprocal exponent bound.
The proof keeps the natural-to-real cast and positivity of the denominator
explicit. -/
theorem one_div_highOrder_le {delta : Real} (hdelta : 0 < delta)
    {p : Nat} (hp : 1 <= p) :
    (1 : Real) / (highOrder delta p : Real) <= delta / 20 := by
  have hPnat : 1 <= highOrder delta p :=
    (highOrder_bounds delta hp).2.2
  have hPpos : (0 : Real) < (highOrder delta p : Real) := by
    exact_mod_cast (show 0 < highOrder delta p by omega)
  have hceilNat : ⌈20 / delta⌉₊ <= highOrder delta p :=
    ceil_le_highOrder delta p
  have hceilReal : (20 : Real) / delta <= (highOrder delta p : Real) := by
    exact (Nat.le_ceil ((20 : Real) / delta)).trans (by exact_mod_cast hceilNat)
  have htwenty : (20 : Real) <= (highOrder delta p : Real) * delta :=
    (div_le_iff₀ hdelta).1 hceilReal
  apply (div_le_iff₀ hPpos).2
  calc
    (1 : Real) = 20 / 20 := by norm_num
    _ <= ((highOrder delta p : Real) * delta) / 20 :=
      div_le_div_of_nonneg_right htwenty (by norm_num)
    _ = delta / 20 * (highOrder delta p : Real) := by ring

/-- T512's exact cardinality bound and the explicit high order give the
coefficient-one family-root cost `N^(delta/20)`. -/
theorem family_card_root_le {delta : Real} (hdelta : 0 < delta)
    {p N : Nat} (hp : 1 <= p) (hN : 81 <= N) :
    (Fintype.card (LoopArg (d.L N) 2) : Real) ^
        ((1 : Real) / (2 * (highOrder delta p : Real))) <=
      (N : Real) ^ (delta / 20) := by
  have hNr : (1 : Real) <= N := by
    exact_mod_cast (show 1 <= N by omega)
  have hPnat : 1 <= highOrder delta p :=
    (highOrder_bounds delta hp).2.2
  have hPpos : (0 : Real) < (highOrder delta p : Real) := by
    exact_mod_cast (show 0 < highOrder delta p by omega)
  have hcard :
      (Fintype.card (LoopArg (d.L N) 2) : Real) <= (N : Real) ^ 2 := by
    exact_mod_cast APrimeFirstCellFamilyHighMoment.family_card_le hN
  have hpexp : (1 : Real) / (highOrder delta p : Real) <= delta / 20 :=
    one_div_highOrder_le hdelta hp
  calc
    _ <= ((N : Real) ^ (2 : Nat)) ^
        ((1 : Real) / (2 * (highOrder delta p : Real))) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)
    _ = (N : Real) ^ ((1 : Real) / (highOrder delta p : Real)) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      congr 1
      push_cast
      field_simp
    _ <= (N : Real) ^ (delta / 20) :=
      Real.rpow_le_rpow_of_exponent_le hNr hpexp

/-- The family cost and the delta-dependent coordinate exponent add exactly
to `delta/4`. -/
theorem exponent_product_eq {delta : Real} {N : Nat} (hN : 1 <= N) :
    (N : Real) ^ (delta / 20) * (N : Real) ^ (delta / 5) =
      (N : Real) ^ (delta / 4) := by
  have hNpos : (0 : Real) < N := by
    exact_mod_cast (show 0 < N by omega)
  rw [← Real.rpow_add hNpos]
  congr 1
  ring

/-- Inequality form of the exact exponent identity. -/
theorem exponent_product_le {delta : Real} {N : Nat} (hN : 1 <= N) :
    (N : Real) ^ (delta / 20) * (N : Real) ^ (delta / 5) <=
      (N : Real) ^ (delta / 4) :=
  (exponent_product_eq (delta := delta) hN).le

/-- One explicit positive bootstrap exponent, low order, and matrix size
simultaneously satisfy every numerical hypothesis and all three conclusions. -/
theorem admissible_parameters_witness :
    exists delta : Real, exists p N : Nat,
      0 < delta ∧ delta <= 1 / 100 ∧ 1 <= p ∧ 81 <= N ∧
      (1 : Real) / (highOrder delta p : Real) <= delta / 20 ∧
      (Fintype.card (LoopArg (d.L N) 2) : Real) ^
          ((1 : Real) / (2 * (highOrder delta p : Real))) <=
        (N : Real) ^ (delta / 20) ∧
      (N : Real) ^ (delta / 20) * (N : Real) ^ (delta / 5) =
        (N : Real) ^ (delta / 4) := by
  refine ⟨1 / 100, 1, 81, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_, ?_⟩
  · exact one_div_highOrder_le (by norm_num) (by norm_num)
  · exact family_card_root_le (by norm_num) (by norm_num) (by norm_num)
  · exact exponent_product_eq (by norm_num)

#print axioms one_div_highOrder_le
#print axioms family_card_root_le
#print axioms exponent_product_eq
#print axioms exponent_product_le
#print axioms admissible_parameters_witness

end

end RBM.APrimeFirstCellDeltaFamilyCardRoot
