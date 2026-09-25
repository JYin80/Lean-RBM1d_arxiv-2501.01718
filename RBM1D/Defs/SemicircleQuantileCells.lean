/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleQuantileBase
import RBM1D.Defs.SemicircleCDFStrict

/-!
# Equal-mass cells from semicircle quantiles

For every positive integer width, the semicircle CDF quantile divides its
support into consecutive half-open cells of equal mass. This is a deterministic
measure-theoretic construction.
-/

namespace RBM

open Set

noncomputable section

/-- The boundary level `j/W`, packaged in the domain of the semicircle quantile. -/
def semicircleBoundaryLevel (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j ≤ W) :
    Icc (0 : ℝ) 1 := by
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjle : (j : ℝ) ≤ (W : ℝ) := by exact_mod_cast hj
  refine ⟨(j : ℝ) / (W : ℝ), ?_⟩
  constructor
  · exact div_nonneg hjnonneg hWpos.le
  · rw [div_le_one hWpos]
    exact hjle

/-- The midpoint level `(j+1/2)/W`, packaged in the quantile domain. -/
def semicircleMidpointLevel (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    Icc (0 : ℝ) 1 := by
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjsucc : (j + 1 : ℕ) ≤ W := Nat.succ_le_of_lt hj
  have hjsucc' : ((j + 1 : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast hjsucc
  have hnum_nonneg : 0 ≤ (j : ℝ) + 1 / 2 := by positivity
  have hnum_le : (j : ℝ) + 1 / 2 ≤ (W : ℝ) := by
    push_cast at hjsucc'
    nlinarith
  refine ⟨((j : ℝ) + 1 / 2) / (W : ℝ), ?_⟩
  constructor
  · exact div_nonneg hnum_nonneg hWpos.le
  · rw [div_le_one hWpos]
    exact hnum_le

/-- The quantile at the boundary level `j/W`. -/
def semicircleBoundaryQuantile (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j ≤ W) :
    Icc (-2 : ℝ) 2 :=
  semicircleQuantile (semicircleBoundaryLevel W hW j hj)

/-- The quantile at the midpoint level `(j+1/2)/W`. -/
def semicircleMidpointQuantile (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    Icc (-2 : ℝ) 2 :=
  semicircleQuantile (semicircleMidpointLevel W hW j hj)

/-- The real-valued `j`th boundary of the `W` equal-mass cells. -/
def semicircleGamma (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j ≤ W) : ℝ :=
  (semicircleBoundaryQuantile W hW j hj).val

/-- The real-valued midpoint quantile in the `j`th cell. -/
def semicircleLambda (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) : ℝ :=
  (semicircleMidpointQuantile W hW j hj).val

/-- The CDF at a boundary quantile is its prescribed level. -/
theorem semicircleGamma_cdf (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j ≤ W) :
    ProbabilityTheory.cdf semicircleMeasure (semicircleGamma W hW j hj) =
      (j : ℝ) / (W : ℝ) := by
  simpa [semicircleGamma, semicircleBoundaryQuantile, semicircleBoundaryLevel,
    semicircleCDF_semicircleQuantile]

/-- The CDF at a midpoint quantile is its prescribed midpoint level. -/
theorem semicircleLambda_cdf (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    ProbabilityTheory.cdf semicircleMeasure (semicircleLambda W hW j hj) =
      ((j : ℝ) + 1 / 2) / (W : ℝ) := by
  simpa [semicircleLambda, semicircleMidpointQuantile, semicircleMidpointLevel,
    semicircleCDF_semicircleQuantile]

/-- The first boundary level is zero. -/
theorem semicircleBoundaryLevel_zero (W : ℕ) (hW : 1 ≤ W) :
    semicircleBoundaryLevel W hW 0 (Nat.zero_le W) = ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  simp [semicircleBoundaryLevel]

/-- The last boundary level is one. -/
theorem semicircleBoundaryLevel_last (W : ℕ) (hW : 1 ≤ W) :
    semicircleBoundaryLevel W hW W le_rfl = ⟨1, by norm_num⟩ := by
  apply Subtype.ext
  have hWne : (W : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (Nat.zero_lt_of_lt hW))
  simp [semicircleBoundaryLevel, hWne]

/-- The first boundary is the left endpoint of the semicircle support. -/
theorem semicircleGamma_zero (W : ℕ) (hW : 1 ≤ W) :
    semicircleGamma W hW 0 (Nat.zero_le W) = -2 := by
  change (semicircleQuantile (semicircleBoundaryLevel W hW 0 _)).val = -2
  rw [semicircleBoundaryLevel_zero, semicircleQuantile_zero]

/-- The last boundary is the right endpoint of the semicircle support. -/
theorem semicircleGamma_last (W : ℕ) (hW : 1 ≤ W) :
    semicircleGamma W hW W le_rfl = 2 := by
  change (semicircleQuantile (semicircleBoundaryLevel W hW W le_rfl)).val = 2
  rw [semicircleBoundaryLevel_last, semicircleQuantile_one]

/-- Consecutive boundary quantiles are strictly increasing. -/
theorem semicircleGamma_strictMono (W : ℕ) (hW : 1 ≤ W) {j : ℕ}
    (hj : j < W) :
    semicircleGamma W hW j (Nat.le_of_lt hj) <
      semicircleGamma W hW (j + 1) (Nat.succ_le_of_lt hj) := by
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hlevels : semicircleBoundaryLevel W hW j (Nat.le_of_lt hj) <
      semicircleBoundaryLevel W hW (j + 1) (Nat.succ_le_of_lt hj) := by
    change (j : ℝ) / (W : ℝ) < ((j + 1 : ℕ) : ℝ) / (W : ℝ)
    rw [div_lt_div_iff_of_pos_right hWpos]
    push_cast
    exact_mod_cast (Nat.lt_succ_self j)
  have hq := strictMono_semicircleQuantile hlevels
  simpa [semicircleGamma, semicircleBoundaryQuantile] using hq

/-- Each midpoint quantile lies strictly between its two boundary quantiles. -/
theorem semicircleGamma_lt_Lambda_lt_Gamma_succ (W : ℕ) (hW : 1 ≤ W)
    {j : ℕ} (hj : j < W) :
    semicircleGamma W hW j (Nat.le_of_lt hj) < semicircleLambda W hW j hj ∧
      semicircleLambda W hW j hj <
        semicircleGamma W hW (j + 1) (Nat.succ_le_of_lt hj) := by
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hleft : semicircleBoundaryLevel W hW j (Nat.le_of_lt hj) <
      semicircleMidpointLevel W hW j hj := by
    change (j : ℝ) / (W : ℝ) < ((j : ℝ) + 1 / 2) / (W : ℝ)
    rw [div_lt_div_iff_of_pos_right hWpos]
    linarith
  have hright : semicircleMidpointLevel W hW j hj <
      semicircleBoundaryLevel W hW (j + 1) (Nat.succ_le_of_lt hj) := by
    change ((j : ℝ) + 1 / 2) / (W : ℝ) <
      ((j + 1 : ℕ) : ℝ) / (W : ℝ)
    rw [div_lt_div_iff_of_pos_right hWpos]
    push_cast
    linarith
  have hqleft := strictMono_semicircleQuantile hleft
  have hqright := strictMono_semicircleQuantile hright
  constructor
  · simpa [semicircleGamma, semicircleLambda, semicircleBoundaryQuantile,
      semicircleMidpointQuantile] using hqleft
  · simpa [semicircleGamma, semicircleLambda, semicircleBoundaryQuantile,
      semicircleMidpointQuantile] using hqright

/-- Every half-open quantile cell has exactly mass `1/W`. -/
theorem semicircleQuantileCell_mass (W : ℕ) (hW : 1 ≤ W) (j : ℕ)
    (hj : j < W) :
    semicircleMeasure (Ioc (semicircleGamma W hW j (Nat.le_of_lt hj))
      (semicircleGamma W hW (j + 1) (Nat.succ_le_of_lt hj))) =
        ENNReal.ofReal (1 / (W : ℝ)) := by
  rw [semicircleMeasure_Ioc_cdf
    (semicircleGamma W hW j (Nat.le_of_lt hj))
    (semicircleGamma W hW (j + 1) (Nat.succ_le_of_lt hj))]
  rw [semicircleGamma_cdf W hW (j + 1) (Nat.succ_le_of_lt hj),
    semicircleGamma_cdf W hW j (Nat.le_of_lt hj)]
  congr 1
  have hWne : (W : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (Nat.zero_lt_of_lt hW))
  field_simp
  push_cast
  ring

/-- At width one, the single nondegenerate cell has mass one. -/
theorem semicircleQuantileCell_witness_one :
    semicircleGamma 1 (by norm_num) 0 (by norm_num) = -2 ∧
    semicircleGamma 1 (by norm_num) 1 (by norm_num) = 2 ∧
    semicircleGamma 1 (by norm_num) 0 (by norm_num) <
      semicircleLambda 1 (by norm_num) 0 (by norm_num) ∧
    semicircleLambda 1 (by norm_num) 0 (by norm_num) <
      semicircleGamma 1 (by norm_num) 1 (by norm_num) ∧
    semicircleMeasure (Ioc (semicircleGamma 1 (by norm_num) 0 (by norm_num))
      (semicircleGamma 1 (by norm_num) 1 (by norm_num))) = 1 := by
  refine ⟨semicircleGamma_zero 1 (by norm_num), semicircleGamma_last 1 (by norm_num),
    (semicircleGamma_lt_Lambda_lt_Gamma_succ 1 (by norm_num) (by norm_num)).1,
    (semicircleGamma_lt_Lambda_lt_Gamma_succ 1 (by norm_num) (by norm_num)).2, ?_⟩
  simpa using semicircleQuantileCell_mass 1 (by norm_num) 0 (by norm_num)

/-- At width two, both nondegenerate cells have mass one half. -/
theorem semicircleQuantileCell_witness_two :
    semicircleGamma 2 (by norm_num) 0 (by norm_num) <
      semicircleLambda 2 (by norm_num) 0 (by norm_num) ∧
    semicircleLambda 2 (by norm_num) 0 (by norm_num) <
      semicircleGamma 2 (by norm_num) 1 (by norm_num) ∧
    semicircleGamma 2 (by norm_num) 1 (by norm_num) <
      semicircleLambda 2 (by norm_num) 1 (by norm_num) ∧
    semicircleLambda 2 (by norm_num) 1 (by norm_num) <
      semicircleGamma 2 (by norm_num) 2 (by norm_num) ∧
    semicircleMeasure (Ioc (semicircleGamma 2 (by norm_num) 0 (by norm_num))
      (semicircleGamma 2 (by norm_num) 1 (by norm_num))) = ENNReal.ofReal (1 / 2) ∧
    semicircleMeasure (Ioc (semicircleGamma 2 (by norm_num) 1 (by norm_num))
      (semicircleGamma 2 (by norm_num) 2 (by norm_num))) = ENNReal.ofReal (1 / 2) := by
  have h0 := semicircleGamma_lt_Lambda_lt_Gamma_succ 2 (by norm_num) (j := 0) (by norm_num)
  have h1 := semicircleGamma_lt_Lambda_lt_Gamma_succ 2 (by norm_num) (j := 1) (by norm_num)
  refine ⟨h0.1, h0.2, h1.1, h1.2, ?_, ?_⟩
  · simpa using semicircleQuantileCell_mass 2 (by norm_num) 0 (by norm_num)
  · simpa using semicircleQuantileCell_mass 2 (by norm_num) 1 (by norm_num)

#print axioms semicircleBoundaryLevel
#print axioms semicircleMidpointLevel
#print axioms semicircleBoundaryQuantile
#print axioms semicircleMidpointQuantile
#print axioms semicircleGamma
#print axioms semicircleLambda
#print axioms semicircleGamma_cdf
#print axioms semicircleLambda_cdf
#print axioms semicircleBoundaryLevel_zero
#print axioms semicircleBoundaryLevel_last
#print axioms semicircleGamma_zero
#print axioms semicircleGamma_last
#print axioms semicircleGamma_strictMono
#print axioms semicircleGamma_lt_Lambda_lt_Gamma_succ
#print axioms semicircleQuantileCell_mass
#print axioms semicircleQuantileCell_witness_one
#print axioms semicircleQuantileCell_witness_two

end

end RBM
