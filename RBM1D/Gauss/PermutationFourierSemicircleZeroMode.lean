/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierSwap
import RBM1D.Gauss.PermutationFourierCharacter
import RBM1D.Defs.SemicircleQuadrature
import RBM1D.Defs.SemicircleFlowKernelTimeModulus

/-! # The permutation-invariant semicircle zero Fourier mode

The constant Fourier character removes the permutation by reindexing. The
remaining literal midpoint-quantile sum is the accepted closed-flow
equal-mass quadrature from the semicircle density.
-/

namespace RBM.Gauss

open RBM

/-- The literal midpoint-quantile semicircle table has the uniform closed-flow
`8√2/W` zero-mode error, for every permutation and every `W ≥ 1`. -/
theorem permutationFourierSemicircleZeroMode_bound
    (W : ℕ) (hW : 1 ≤ W) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (π : Equiv.Perm (Fin W)) :
    ‖permutationFourierSum W
      (fun j : Fin W => semicircleFlowKernel u
        (semicircleLambda W hW j.val j.isLt))
      (fun _ => 1) π - Complex.I‖ ≤ 8 * Real.sqrt 2 / (W : ℝ) := by
  have hsum :
      permutationFourierSum W
        (fun j : Fin W => semicircleFlowKernel u
          (semicircleLambda W hW j.val j.isLt))
        (fun _ => 1) π =
      (↑(1 / (W : ℝ)) : ℂ) *
        (∑ j ∈ Finset.range W,
          (((Real.sqrt u * semicircleQuadratureLambda W hW j : ℝ) : ℂ) -
            Complex.I * ((1-u : ℝ) : ℂ))⁻¹) := by
    unfold permutationFourierSum
    simp only [one_mul]
    have hperm :
        (∑ x : Fin W, semicircleFlowKernel u
          (semicircleLambda W hW (π x).val (π x).isLt)) =
        (∑ x : Fin W, semicircleFlowKernel u
          (semicircleLambda W hW x.val x.isLt)) := by
      exact Equiv.sum_comp π
        (fun x : Fin W => semicircleFlowKernel u
          (semicircleLambda W hW x.val x.isLt))
    rw [hperm]
    have hrange :
        (∑ x : Fin W, semicircleFlowKernel u
          (semicircleLambda W hW x.val x.isLt)) =
        (∑ j ∈ Finset.range W,
          (((Real.sqrt u * semicircleQuadratureLambda W hW j : ℝ) : ℂ) -
            Complex.I * ((1-u : ℝ) : ℂ))⁻¹) := by
      calc
        _ = ∑ x : Fin W, semicircleFlowKernel u
              (semicircleQuadratureLambda W hW x.val) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [semicircleQuadratureLambda_eq W hW x.val x.isLt]
        _ = _ := by
          simpa [semicircleFlowKernel] using
            (Fin.sum_univ_eq_sum_range
              (fun j : ℕ =>
                (((Real.sqrt u * semicircleQuadratureLambda W hW j : ℝ) : ℂ) -
                  Complex.I * ((1-u : ℝ) : ℂ))⁻¹) W)
    rw [hrange]
    push_cast
    field_simp [show (W : ℂ) ≠ 0 by exact_mod_cast (by omega : W ≠ 0)]
  rw [hsum]
  exact semicircleQuadrature_closed_flow_explicit W hW u hu0 hu1

/-- For the canonical zero character, the literal weight is the constant-one
table used by the zero-mode bound. -/
theorem permutationFourierCharacter_zero_eq_one (W : ℕ) (hW : 1 ≤ W) :
    permutationFourierCharacter W ⟨0, by omega⟩ = (fun _ : Fin W => (1 : ℂ)) := by
  funext j
  simp [permutationFourierCharacter]

/-- At `W=1,u=1/2`, every permutation gives the exact error one. This witnesses
that the general zero-mode estimate is nontrivial at its smallest width. -/
theorem permutationFourierSemicircleZeroMode_one_half_error (π : Equiv.Perm (Fin 1)) :
    ‖permutationFourierSum 1
      (fun j : Fin 1 => semicircleFlowKernel (1 / 2)
        (semicircleLambda 1 (by norm_num) j.val j.isLt))
      (fun _ => 1) π - Complex.I‖ = 1 := by
  have hπ : π = Equiv.refl (Fin 1) := Subsingleton.elim _ _
  subst π
  have hlam : semicircleLambda 1 (by norm_num) 0 (by norm_num) = 0 := by
    rw [← semicircleQuadratureLambda_eq 1 (by norm_num) 0 (by norm_num)]
    exact semicircleQuadratureLambda_one_zero
  norm_num [permutationFourierSum, Fin.sum_univ_one,
    semicircleFlowKernel, hlam]
  have h : (2 : ℂ) * Complex.I - Complex.I = Complex.I := by ring
  rw [h]
  simp

theorem permutationFourierSemicircleZeroMode_W2_positive_cells :
    semicircleGamma 2 (by norm_num) 0 (by norm_num) <
        semicircleLambda 2 (by norm_num) 0 (by norm_num) ∧
      semicircleLambda 2 (by norm_num) 0 (by norm_num) <
        semicircleGamma 2 (by norm_num) 1 (by norm_num) ∧
      semicircleGamma 2 (by norm_num) 1 (by norm_num) <
        semicircleLambda 2 (by norm_num) 1 (by norm_num) ∧
      semicircleLambda 2 (by norm_num) 1 (by norm_num) <
        semicircleGamma 2 (by norm_num) 2 (by norm_num) ∧
      semicircleMeasure (Set.Ioc
        (semicircleGamma 2 (by norm_num) 0 (by norm_num))
        (semicircleGamma 2 (by norm_num) 1 (by norm_num))) = ENNReal.ofReal (1 / 2) ∧
      semicircleMeasure (Set.Ioc
        (semicircleGamma 2 (by norm_num) 1 (by norm_num))
        (semicircleGamma 2 (by norm_num) 2 (by norm_num))) = ENNReal.ofReal (1 / 2) :=
  semicircleQuantileCell_witness_two

#print axioms permutationFourierSemicircleZeroMode_bound
#print axioms permutationFourierCharacter_zero_eq_one
#print axioms permutationFourierSemicircleZeroMode_one_half_error
#print axioms permutationFourierSemicircleZeroMode_W2_positive_cells

end RBM.Gauss
