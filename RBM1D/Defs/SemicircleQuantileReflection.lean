/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleCDFReflection
import RBM1D.Defs.SemicircleQuantileCells

/-!
# Reflection of semicircle midpoint quantiles

The even semicircle density gives an exact reflection law for the CDF. The
unique quantile inverse then pairs the midpoint representatives of the equal
mass cells.
-/

namespace RBM

open Set

noncomputable section

/-- Midpoint quantiles in complementary equal-mass cells are negatives. -/
theorem semicircleLambda_reflection (W : ℕ) (hW : 1 ≤ W) (j : ℕ)
    (hj : j < W) :
    semicircleLambda W hW (W - 1 - j) (by omega) =
      -semicircleLambda W hW j hj := by
  let k : ℕ := W - 1 - j
  have hk : k < W := by dsimp [k]; omega
  let x : ℝ := semicircleLambda W hW j hj
  have hx : ProbabilityTheory.cdf semicircleMeasure x =
      ((j : ℝ) + 1 / 2) / (W : ℝ) := by
    simpa [x] using semicircleLambda_cdf W hW j hj
  have hreflect := semicircleMeasure_cdf_reflection x
  have hNat : k + j + 1 = W := by dsimp [k]; omega
  have hsum : (k : ℝ) + 1 = (W : ℝ) - (j : ℝ) := by
    have hNat' : (k : ℝ) + (j : ℝ) + 1 = (W : ℝ) := by exact_mod_cast hNat
    linarith
  have hnegcdf : ProbabilityTheory.cdf semicircleMeasure (-x) =
      ((k : ℝ) + 1 / 2) / (W : ℝ) := by
    rw [hreflect, hx]
    have hWpos : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
    rw [show (k : ℝ) + 1 / 2 = (W : ℝ) - ((j : ℝ) + 1 / 2) by linarith [hsum]]
    field_simp
  have huniq := existsUnique_semicircleCDF_eq (((k : ℝ) + 1 / 2) / (W : ℝ))
    (by positivity) (by
      have hWpos : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
      rw [div_le_one hWpos]
      have hkcast : (k : ℝ) + 1 ≤ (W : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hk)
      linarith)
  have hxmem : x ∈ Icc (-2 : ℝ) 2 := by
    dsimp [x, semicircleLambda]
    exact (semicircleMidpointQuantile W hW j hj).property
  have hnegmem : -x ∈ Icc (-2 : ℝ) 2 := by
    rcases hxmem with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hqmem : semicircleLambda W hW k hk ∈ Icc (-2 : ℝ) 2 :=
    (semicircleMidpointQuantile W hW k hk).property
  have hqlevel : ProbabilityTheory.cdf semicircleMeasure
      (semicircleLambda W hW k hk) = ((k : ℝ) + 1 / 2) / (W : ℝ) :=
    semicircleLambda_cdf W hW k hk
  have heq := huniq.unique
    (show ProbabilityTheory.cdf semicircleMeasure
      (⟨-x, hnegmem⟩ : Icc (-2 : ℝ) 2) = ((k : ℝ) + 1 / 2) / (W : ℝ) by
        exact hnegcdf)
    (show ProbabilityTheory.cdf semicircleMeasure
      (⟨semicircleLambda W hW k hk, hqmem⟩ : Icc (-2 : ℝ) 2) =
        ((k : ℝ) + 1 / 2) / (W : ℝ) by exact hqlevel)
  have hval : -x = semicircleLambda W hW k hk := congrArg Subtype.val heq
  dsimp [x] at hval
  linarith

/-- The central midpoint quantile of an odd number of cells is zero. -/
theorem semicircleLambda_odd_center (m : ℕ) :
    semicircleLambda (2 * m + 1) (by omega) m (by omega) = 0 := by
  have hsym := semicircleLambda_reflection (2 * m + 1) (by omega) m (by omega)
  have hidx : (2 * m + 1) - 1 - m = m := by omega
  have hsym' : semicircleLambda (2 * m + 1) (by omega) m (by omega) =
      -semicircleLambda (2 * m + 1) (by omega) m (by omega) := by
    simpa only [hidx] using hsym
  linarith

/-- At width two, the midpoint representatives are distinct and both cells
have strictly positive semicircle measure. -/
theorem semicircleQuantileReflection_witness_two :
    semicircleLambda 2 (by norm_num) 0 (by norm_num) <
      semicircleLambda 2 (by norm_num) 1 (by norm_num) ∧
    0 < semicircleMeasure (Ioc (semicircleGamma 2 (by norm_num) 0 (by norm_num))
      (semicircleGamma 2 (by norm_num) 1 (by norm_num))) ∧
    0 < semicircleMeasure (Ioc (semicircleGamma 2 (by norm_num) 1 (by norm_num))
      (semicircleGamma 2 (by norm_num) 2 (by norm_num))) := by
  have h := semicircleQuantileCell_witness_two
  refine ⟨lt_trans h.2.1 h.2.2.1, ?_, ?_⟩
  · rw [semicircleQuantileCell_mass 2 (by norm_num) 0 (by norm_num)]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  · rw [semicircleQuantileCell_mass 2 (by norm_num) 1 (by norm_num)]
    exact ENNReal.ofReal_pos.mpr (by norm_num)

#print axioms semicircleLambda_reflection
#print axioms semicircleLambda_odd_center
#print axioms semicircleQuantileReflection_witness_two

end

end RBM
