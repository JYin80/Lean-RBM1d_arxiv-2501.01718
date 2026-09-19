/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Temporary API probe

Confirms the exact names and signatures of the Mathlib declarations the
propagator development needs.  This file is deleted once Phase 1 lands.
-/

open scoped Matrix.Norms.Operator

section Probe

noncomputable example : NormedRing (Matrix (Fin 3) (Fin 3) ℂ) := by infer_instance
noncomputable example : NormedAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ) := by infer_instance
example : HasSummableGeomSeries (Matrix (Fin 3) (Fin 3) ℂ) := by infer_instance
example : NormOneClass (Matrix (Fin 3) (Fin 3) ℂ) := by infer_instance
example (c : ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) : ‖c • A‖ = ‖c‖ * ‖A‖ := norm_smul c A

/-- Is the unit inverse of `1 - t` definitionally the geometric series? -/
example (t : Matrix (Fin 3) (Fin 3) ℂ) (h : ‖t‖ < 1) :
    (↑((Units.oneSub t h)⁻¹) : Matrix (Fin 3) (Fin 3) ℂ) = ∑' i : ℕ, t ^ i := rfl

example : ‖(3 : ℂ)‖₊ = 3 := by simp
example : ‖(3 : ℂ)⁻¹‖₊ = (3 : NNReal)⁻¹ := by simp

#check @Units.val_oneSub
#check @Matrix.mulVec_mulVec
#check @Matrix.mulVec_smul
#check @Matrix.smul_mulVec
#check @Finset.sup_const
#check @Finset.univ_nonempty

#check @Ring.inverse_unit
#check @Ring.inverse_mul_cancel
#check @Ring.mul_inverse_cancel
#check @Matrix.linfty_opNNNorm_def
#check @Finset.sup_le
#check @Finset.sup_le_iff
#check @NNReal.coe_le_coe
#check @Matrix.mulVec_smul
#check @Matrix.circulant_apply

#check @Summable.tsum_le_tsum
#check @norm_pow_le
#check @norm_tsum_le_tsum_norm
#check @tsum_geometric_of_lt_one
#check @summable_geometric_of_lt_one
#check @eventually_nhdsWithin_of_eventually_nhds
#check @Matrix.submatrix_mul_equiv
#check @Matrix.submatrix_one_equiv

#check @ZMod.val_add
#check @ZMod.val_lt
#check @ZMod.val_cast_of_lt
#check @ZMod.neg_val
#check @Matrix.sum_apply
#check @smul_pow
#check @geom_sum_mul

end Probe
