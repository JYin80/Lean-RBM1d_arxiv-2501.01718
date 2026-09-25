/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationBlockDiagonalCarrier
import RBM1D.Gauss.PermutationFourierCirculantResolvent
import RBM1D.Gauss.PermutationFourierExampleGrowFlowCarrier
import RBM1D.Gauss.PermutationFourierExampleGrowEntryMargin
import RBM1D.Gauss.APrimeGeneralMovingGoodMesh

/-!
# Operator norm of the actual Fourier-quantile physical carrier

The midpoint semicircle quantiles lie strictly inside `(-2,2)`.  Fourier
unitarity and block-diagonalization therefore give operator norm at most two
for every permutation and every dimension.  This is only a deterministic
membership result for the fixed norm event `APrimeGeneralMovingGoodMesh.good`.
-/

open Matrix RBM.Gauss Filter
open scoped Matrix.Norms.L2Operator

namespace RBM.Gauss

private theorem l2_opNorm_one_nonempty {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : ‖(1 : Matrix ι ι ℂ)‖ = 1 := by
  rw [show (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun _ : ι => (1 : ℂ)) by
    ext i j
    simp]
  rw [Matrix.l2_opNorm_diagonal]
  simp

private theorem l2_opNorm_conj_diagonal_le_two {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) (v : ι → ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hv : ∀ i, ‖v i‖ ≤ 2) : ‖Uᴴ * Matrix.diagonal v * U‖ ≤ 2 := by
  have hUnorm : ‖U‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [hU, l2_opNorm_one_nonempty] at h
    nlinarith [norm_nonneg U]
  have hUstar : ‖Uᴴ‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Uᴴ
    rw [show (Uᴴ)ᴴ * Uᴴ = 1 by simpa using hU', l2_opNorm_one_nonempty] at h
    nlinarith [norm_nonneg Uᴴ]
  have hdiag : ‖(Matrix.diagonal v : Matrix ι ι ℂ)‖ ≤ 2 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2 hv
  calc
    ‖Uᴴ * Matrix.diagonal v * U‖ ≤ ‖Uᴴ‖ * ‖Matrix.diagonal v‖ * ‖U‖ := by
      calc
        _ ≤ ‖Uᴴ * Matrix.diagonal v‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (‖Uᴴ‖ * ‖Matrix.diagonal v‖) * ‖U‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖Matrix.diagonal v‖ := by rw [hUstar, hUnorm]; ring
    _ ≤ 2 := hdiag

theorem semicircleLambda_mem_open_support (W : ℕ) (hW : 1 ≤ W)
    (j : ℕ) (hj : j < W) :
    semicircleLambda W hW j hj ∈ Set.Ioo (-2 : ℝ) 2 := by
  have h := semicircleGamma_lt_Lambda_lt_Gamma_succ W hW hj
  have hleft : -2 ≤ semicircleGamma W hW j (Nat.le_of_lt hj) :=
    (semicircleBoundaryQuantile W hW j (Nat.le_of_lt hj)).property.1
  have hright : semicircleGamma W hW (j + 1) (Nat.succ_le_of_lt hj) ≤ 2 :=
    (semicircleBoundaryQuantile W hW (j + 1) (Nat.succ_le_of_lt hj)).property.2
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem physicalFourierBlock_opNorm_le_two (d : Dims) (N : ℕ)
    (π : Equiv.Perm (Fin (d.W N))) :
    ‖blockDiagonal d N (fun _ =>
      permutationFourierBlock (d.W N) (d.W_pos N) π)‖ ≤ 2 := by
  let W := d.W N
  let L := d.L N
  let F := permutationFourierMatrix W
  let U : Matrix (d.Idx N) (d.Idx N) ℂ := blockDiagonal d N (fun _ => F)
  let V : d.Idx N → ℂ := fun i =>
    (semicircleLambda W (d.W_pos N) (π i.2).val (π i.2).isLt : ℂ)
  let D : Matrix (d.Idx N) (d.Idx N) ℂ := Matrix.diagonal V
  have hF : Fᴴ * F = 1 := permutationFourierMatrix_conjTranspose_mul W (d.W_pos N)
  have hF' : F * Fᴴ = 1 := permutationFourierMatrix_mul_conjTranspose W (d.W_pos N)
  have hstar : Uᴴ = blockDiagonal d N (fun _ => Fᴴ) := by
    ext ⟨a, x⟩ ⟨b, y⟩
    change star (blockDiagonal d N (fun _ => F) (b, y) (a, x)) = _
    simp only [blockDiagonal]
    by_cases hab : a = b
    · subst b
      simp [Matrix.conjTranspose_apply]
    · have hba : b ≠ a := fun h => hab h.symm
      simp [hab, hba]
  have hU : Uᴴ * U = 1 := by
    rw [hstar]
    dsimp [U]
    change blockDiagonal d N (fun _ => Fᴴ) * blockDiagonal d N (fun _ => F) = 1
    rw [blockDiagonal_mul, hF, blockDiagonal_one]
  have hU' : U * Uᴴ = 1 := by
    rw [hstar]
    dsimp [U]
    change blockDiagonal d N (fun _ => F) * blockDiagonal d N (fun _ => Fᴴ) = 1
    rw [blockDiagonal_mul, hF', blockDiagonal_one]
  have hV : ∀ i, ‖V i‖ ≤ 2 := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hi := semicircleLambda_mem_open_support W (d.W_pos N)
      (π i.2).val (π i.2).isLt
    exact ⟨le_of_lt hi.1, le_of_lt hi.2⟩
  have hfactor : Uᴴ * D * U =
      blockDiagonal d N (fun _ => permutationFourierBlock W (d.W_pos N) π) := by
    have hD : D = blockDiagonal d N (fun _ =>
        Matrix.diagonal (fun j : Fin W =>
          (semicircleLambda W (d.W_pos N) (π j).val (π j).isLt : ℂ))) := by
      ext ⟨a, x⟩ ⟨b, y⟩
      by_cases hab : a = b
      · subst b
        simp [D, V, blockDiagonal, Matrix.diagonal_apply]
      · simp [D, blockDiagonal, hab]
    rw [hstar, hD]
    dsimp only [U]
    change blockDiagonal d N (fun _ => Fᴴ) *
      blockDiagonal d N (fun _ => Matrix.diagonal (fun j : Fin W =>
        (semicircleLambda W (d.W_pos N) (π j).val (π j).isLt : ℂ))) *
      blockDiagonal d N (fun _ => F) = _
    rw [blockDiagonal_mul, blockDiagonal_mul]
    rfl
  rw [← hfactor]
  exact l2_opNorm_conj_diagonal_le_two U V hU hU' hV

theorem quantileCarrier_mem_generalMovingGoodMesh (N : ℕ)
    (π : Equiv.Perm (Fin (Dims.exampleGrow.W N)))
    (hN : 2 ≤ N) :
    omegaOfHermitian Dims.exampleGrow N
      (blockDiagonal Dims.exampleGrow N (fun _ =>
        permutationFourierBlock (Dims.exampleGrow.W N)
          (Dims.exampleGrow.W_pos N) π)) ∈
      APrimeGeneralMovingGoodMesh.good N := by
  change ‖Xmat Dims.exampleGrow N _‖ ≤ (N : ℝ)
  rw [blockDiagonal_readback _ _ _ (fun _ =>
    permutationFourierBlock_hermitian _ _ π)]
  have h := physicalFourierBlock_opNorm_le_two Dims.exampleGrow N π
  exact h.trans (by exact_mod_cast hN)

theorem eventually_quantileCarrier_mem_generalMovingGoodMesh_nonzero :
    ∀ᶠ N : ℕ in atTop,
      ∃ π : Equiv.Perm (Fin (Dims.exampleGrow.W N)),
        ∃ ω : Ω Dims.exampleGrow,
          ω ∈ APrimeGeneralMovingGoodMesh.good N ∧
          Xmat Dims.exampleGrow N ω = blockDiagonal Dims.exampleGrow N
            (fun _ => permutationFourierBlock (Dims.exampleGrow.W N)
              (Dims.exampleGrow.W_pos N) π) ∧
          Xmat Dims.exampleGrow N ω ≠ 0 ∧
          (∀ c : Coord Dims.exampleGrow,
            (gvar Dims.exampleGrow c : ℝ) = 0 → ω c = 0) := by
  filter_upwards [permutationFourierExampleGrow_eventually_entry_margin_nonempty,
    eventually_ge_atTop 2] with N hN hN2
  obtain ⟨hW2, π, _⟩ := hN
  let π' : Equiv.Perm (Fin (Dims.exampleGrow.W N)) := π
  let C := permutationFourierBlock (Dims.exampleGrow.W N)
    (Dims.exampleGrow.W_pos N) π'
  let M := blockDiagonal Dims.exampleGrow N (fun _ => C)
  let ω := omegaOfHermitian Dims.exampleGrow N M
  refine ⟨π', ω, quantileCarrier_mem_generalMovingGoodMesh N π' hN2, ?_, ?_, ?_⟩
  · exact blockDiagonal_readback _ _ _
      (fun _ => permutationFourierBlock_hermitian _ _ π')
  · rw [blockDiagonal_readback _ _ _ (fun _ => permutationFourierBlock_hermitian _ _ π')]
    intro hzero
    have hCzero : C = 0 := by
      ext x y
      have h := congrArg (fun A : Matrix (Dims.exampleGrow.Idx N)
        (Dims.exampleGrow.Idx N) ℂ => A (0, x) (0, y)) hzero
      have h' : permutationFourierBlock (Dims.exampleGrow.W N)
          (Dims.exampleGrow.W_pos N) π' x y = 0 := by
        simpa only [blockDiagonal, ↓reduceIte, Matrix.zero_apply] using h
      exact h'
    exact quantileBlock_nonzero (Dims.exampleGrow.W N)
      (Dims.exampleGrow.W_pos N) hW2 π' hCzero
  · intro c hg
    exact blockDiagonal_zeroVar Dims.exampleGrow N (fun _ => C) c hg

#print axioms semicircleLambda_mem_open_support
#print axioms quantileCarrier_mem_generalMovingGoodMesh
#print axioms eventually_quantileCarrier_mem_generalMovingGoodMesh_nonzero

end RBM.Gauss
