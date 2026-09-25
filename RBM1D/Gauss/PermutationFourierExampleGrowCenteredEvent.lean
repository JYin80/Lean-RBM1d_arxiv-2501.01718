/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowFlowCarrier
import RBM1D.Gauss.APrimeGeneralMovingTwoChargeModulus
import RBM1D.Gauss.PermutationFourierExampleGrowCenteredZeroMargin

/-!
# Deterministic two-charge centered-event sample for the growing model

The same nonzero Fourier-quantile block sample belongs to both the literal
flow-resolvent event and the literal two-charge centered block-trace event.
The result is deterministic sample existence, without a Gaussian measure claim.
-/

set_option autoImplicit false

namespace RBM.Gauss

open RBM RBM.Gauss Matrix

theorem trace_Eblk_exact (d : Gauss.Dims) (N : ℕ)
    (A : Matrix (d.Idx N) (d.Idx N) ℂ) (b : ZMod (d.L N)) :
    Matrix.trace (A * Eblk (d.L N) (d.W N) b) =
      (d.W N : ℂ)⁻¹ * ∑ α : Fin (d.W N), A (b, α) (b, α) :=
  RBM.Gauss.sumSblk_trace_mul_Eblk A b

theorem centered_true_diagonal (d : Gauss.Dims) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (b : ZMod (d.L N)) :
    Matrix.trace ((Gsig M (zt 0 u) true - mSigma 0 true •
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b) =
      (d.W N : ℂ)⁻¹ * ∑ α : Fin (d.W N),
        (Gsig M (zt 0 u) true (b, α) (b, α) - Complex.I) := by
  rw [trace_Eblk_exact]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  norm_num [mSigma, mE]

theorem centered_false_conj_true (d : Gauss.Dims) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian)
    (b : ZMod (d.L N)) :
    Matrix.trace ((Gsig M (zt 0 u) false - mSigma 0 false •
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b) =
      (starRingEnd ℂ) (Matrix.trace ((Gsig M (zt 0 u) true - mSigma 0 true •
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b)) := by
  rw [mSigma_false, mSigma_true]
  exact RBM.APrimeTwoChargeOneLoop.centered_block_trace_false_eq_conj_true
    (d.L N) (d.W N) M hM (zt 0 u) (mE 0) b

theorem centered_true_of_constant_diagonal (d : Gauss.Dims) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (b : ZMod (d.L N)) (q : ℂ)
    (hdiag : ∀ α : Fin (d.W N), Gsig M (zt 0 u) true (b, α) (b, α) = q) :
    Matrix.trace ((Gsig M (zt 0 u) true - mSigma 0 true •
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b) =
      q - Complex.I := by
  rw [centered_true_diagonal]
  have hs : (∑ α : Fin (d.W N), (Gsig M (zt 0 u) true (b, α) (b, α) - Complex.I)) =
      (d.W N : ℂ) * (q - Complex.I) := by
    simp_rw [hdiag]
    simp [nsmul_eq_mul, mul_sub]
  rw [hs]
  have hW : (d.W N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (d.W_pos N))
  field_simp

theorem actual_twoCharge_of_diagonal (N : ℕ) (u : ℝ)
    (ω : Gauss.Ω Gauss.Dims.exampleGrow)
    (b : ZMod (Gauss.Dims.exampleGrow.L N)) (q : ℂ)
    (hdiag : ∀ α : Fin (Gauss.Dims.exampleGrow.W N),
      Gsig (Gauss.Hflow Gauss.Dims.exampleGrow N u ω) (zt 0 u) true
        (b, α) (b, α) = q) :
    ∀ σ : Bool,
      RBM.APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω σ b =
        if σ then q - Complex.I else (starRingEnd ℂ) (q - Complex.I) := by
  intro σ
  have htrue : RBM.APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω true b =
      q - Complex.I := by
    exact centered_true_of_constant_diagonal Gauss.Dims.exampleGrow N u
      (Gauss.Hflow Gauss.Dims.exampleGrow N u ω) b q hdiag
  cases σ with
  | false =>
      rw [RBM.APrimeGeneralMovingTwoChargeModulus.centeredTrace_false_eq_conj_true,
        htrue]
      rfl
  | true => simpa using htrue

theorem actual_twoCharge_of_oneBlock_diagonal (N : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (ω : Gauss.Ω Gauss.Dims.exampleGrow)
    (b : ZMod (Gauss.Dims.exampleGrow.L N))
    (π : Equiv.Perm (Fin (Gauss.Dims.exampleGrow.W N)))
    (hfull : ∀ α : Fin (Gauss.Dims.exampleGrow.W N),
      Gsig (Gauss.Hflow Gauss.Dims.exampleGrow N u ω) (zt 0 u) true
        (b, α) (b, α) =
      (((Real.sqrt u : ℂ) •
          permutationFourierBlock (Gauss.Dims.exampleGrow.W N)
            (Gauss.Dims.exampleGrow.W_pos N) π -
        (Complex.I * ((1-u : ℝ) : ℂ)) •
          (1 : Matrix (Fin (Gauss.Dims.exampleGrow.W N))
            (Fin (Gauss.Dims.exampleGrow.W N)) ℂ))⁻¹) α α) :
    ∀ σ : Bool,
      RBM.APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω σ b =
        if σ then
          permutationFourierSum (Gauss.Dims.exampleGrow.W N)
            (fun j => semicircleFlowKernel u
              (semicircleLambda (Gauss.Dims.exampleGrow.W N)
                (Gauss.Dims.exampleGrow.W_pos N) j.val j.isLt))
            (fun _ => 1) π - Complex.I
        else (starRingEnd ℂ) (permutationFourierSum (Gauss.Dims.exampleGrow.W N)
            (fun j => semicircleFlowKernel u
              (semicircleLambda (Gauss.Dims.exampleGrow.W N)
                (Gauss.Dims.exampleGrow.W_pos N) j.val j.isLt))
            (fun _ => 1) π - Complex.I) := by
  apply actual_twoCharge_of_diagonal
  intro α
  rw [hfull α]
  exact permutationFourierBlock_resolvent_diagonal_zero_mode
    (Gauss.Dims.exampleGrow.W N) (Gauss.Dims.exampleGrow.W_pos N)
    π u hu0 hu1 α

def fullDiagonalBridge (N : ℕ) (ω : Gauss.Ω Gauss.Dims.exampleGrow) : Prop :=
  ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
    ∀ b : ZMod (Gauss.Dims.exampleGrow.L N),
      ∃ π : Equiv.Perm (Fin (Gauss.Dims.exampleGrow.W N)),
        ∀ α : Fin (Gauss.Dims.exampleGrow.W N),
          Gsig (Gauss.Hflow Gauss.Dims.exampleGrow N u ω) (zt 0 u) true
            (b, α) (b, α) =
          (((Real.sqrt u : ℂ) •
              permutationFourierBlock (Gauss.Dims.exampleGrow.W N)
                (Gauss.Dims.exampleGrow.W_pos N) π -
            (Complex.I * ((1-u : ℝ) : ℂ)) •
              (1 : Matrix (Fin (Gauss.Dims.exampleGrow.W N))
                (Fin (Gauss.Dims.exampleGrow.W N)) ℂ))⁻¹) α α

theorem eventual_centeredEvent_of_fullDiagonalBridge {zeta : ℝ} (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ ω : Gauss.Ω Gauss.Dims.exampleGrow,
        fullDiagonalBridge N ω →
          ω ∈ RBM.APrimeGeneralMovingCommonSources.centeredEvent 0
            (fun _ => 0) (fun _ => 1 / 2) zeta N := by
  filter_upwards
    [RBM.Gauss.eventually_permutationFourierExampleGrow_zeroMode_below_centered_threshold
      hzeta] with N hmargin
  intro ω hbridge σ p
  obtain ⟨⟨u, hu⟩, b⟩ := p
  obtain ⟨π, hfull⟩ := hbridge u hu b
  have htwo := actual_twoCharge_of_oneBlock_diagonal N u hu.1 hu.2 ω b π hfull σ
  have hbound := hmargin u hu π
  cases σ with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at htwo
      rw [htwo, Complex.norm_conj]
      exact le_of_lt hbound
  | true =>
      simp only [↓reduceIte] at htwo
      rw [htwo]
      exact le_of_lt hbound

theorem width_two_half_time_check :
    Gauss.Dims.exampleGrow.W 6 = 2 ∧
    (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) ∧
    (((Real.sqrt (1 / 2 : ℝ) : ℂ) •
      permutationFourierBlock 2 (by norm_num) (Equiv.refl (Fin 2)) -
      (Complex.I * ((1 - (1 / 2 : ℝ) : ℝ) : ℂ)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹) 0 1 ≠ 0 ∧
    0 < RBM.APrimeGeneralMovingControlExtension.qExt 0
      (fun _ => 0) (fun _ => 1 / 2) 6 (1 / 2) := by
  refine ⟨Gauss.exampleGrow_width_six, by norm_num,
    permutationFourierBlock_resolvent_two_offdiag_nonzero, ?_⟩
  rw [RBM.Gauss.permutationFourierExampleGrow_qExt_eq_fraction 6 (by norm_num)]
  rw [Gauss.exampleGrow_width_six]
  norm_num

#print axioms trace_Eblk_exact
#print axioms centered_true_diagonal
#print axioms centered_false_conj_true
#print axioms centered_true_of_constant_diagonal
#print axioms actual_twoCharge_of_diagonal
#print axioms actual_twoCharge_of_oneBlock_diagonal
#print axioms eventual_centeredEvent_of_fullDiagonalBridge
#print axioms width_two_half_time_check

end RBM.Gauss

namespace RBM.Gauss

open RBM RBM.Gauss Matrix Filter

private theorem quantile_sample_fullDiagonalBridge (N : ℕ)
    (π : Equiv.Perm (Fin (Gauss.Dims.exampleGrow.W N))) :
    fullDiagonalBridge N
      (omegaOfHermitian Gauss.Dims.exampleGrow N
        (blockDiagonal Gauss.Dims.exampleGrow N
          (fun _ => permutationFourierBlock (Gauss.Dims.exampleGrow.W N)
            (Gauss.Dims.exampleGrow.W_pos N) π))) := by
  let d := Gauss.Dims.exampleGrow
  let C := permutationFourierBlock (d.W N) (d.W_pos N) π
  let ω := omegaOfHermitian d N (blockDiagonal d N (fun _ => C))
  intro u hu b
  refine ⟨π, ?_⟩
  intro α
  have hread : Xmat d N ω = blockDiagonal d N (fun _ => C) :=
    blockDiagonal_readback d N _ (fun _ => permutationFourierBlock_hermitian _ _ π)
  change green (Hflow d N u ω) (zt 0 u) (b, α) (b, α) = _
  rw [Hflow, hread, zt_zero_energy]
  rw [blockDiagonal_const_resolvent d N C
    (permutationFourierBlock_hermitian _ _ π) u hu.2 (b, α) (b, α)]
  simp only [ite_true]
  change ((Real.sqrt u : ℂ) • C -
    (((1-u : ℝ) : ℂ) * Complex.I) •
      (1 : Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ))⁻¹ α α = _
  rw [mul_comm (((1-u : ℝ) : ℂ)) Complex.I]

#print axioms quantile_sample_fullDiagonalBridge

theorem eventually_nondegenerate_centeredEvent_sample {zeta : ℝ} (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop,
      ∃ ω : Ω Dims.exampleGrow,
        ω ∈ goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1/2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1/2)) N ∧
        ω ∈ RBM.APrimeGeneralMovingCommonSources.centeredEvent 0
          (fun _ => 0) (fun _ => 1/2) zeta N ∧
        Xmat Dims.exampleGrow N ω ≠ 0 ∧
        (∀ c : Coord Dims.exampleGrow,
          (gvar Dims.exampleGrow c : ℝ) = 0 → ω c = 0) := by
  filter_upwards [permutationFourierExampleGrow_eventually_entry_margin_nonempty,
    eventual_centeredEvent_of_fullDiagonalBridge hzeta] with N hN hcenter
  obtain ⟨hW2, π, hπ⟩ := hN
  let d := Dims.exampleGrow
  let δ := flowDelta d 0 (fun _ => 1/2) N
  let C := permutationFourierBlock (d.W N) (d.W_pos N) π
  let ω := omegaOfHermitian d N (blockDiagonal d N (fun _ => C))
  refine ⟨ω, ?_, ?_, ?_, ?_⟩
  · have hδ : 0 ≤ δ := by
      dsimp [δ, flowDelta]
      have hscale := PermutationFourierExampleGrowFlowMargin.scale_half_pos N
      change 0 ≤ ((band d).scale 0 N (1/2))⁻¹ ^ ((1 : ℝ) / 6)
      positivity
    exact quantile_block_event d N π δ hδ (by
      intro u hu0 hu1 a b
      exact hπ u hu0 hu1 a b)
  · exact hcenter ω (quantile_sample_fullDiagonalBridge N π)
  · rw [show Xmat d N ω = blockDiagonal d N (fun _ => C) from
      blockDiagonal_readback d N _ (fun _ => permutationFourierBlock_hermitian _ _ π)]
    intro hzero
    apply quantileBlock_nonzero (d.W N) (d.W_pos N) hW2 π
    ext x y
    have h := congrArg (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      M (0, x) (0, y)) hzero
    simpa [RBM.Gauss.blockDiagonal, C] using h
  · intro c hg
    exact blockDiagonal_zeroVar d N (fun _ => C) c hg

#print axioms eventually_nondegenerate_centeredEvent_sample

end RBM.Gauss
