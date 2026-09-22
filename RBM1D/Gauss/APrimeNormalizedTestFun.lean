/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftTimeFamily

/-! # T297: the normalized A′ moment is an admissible Gaussian test function -/

#check @RBM.Gauss.TestFunT₁
#check @RBM.Gauss.testFunT₁_momentObsT_of_coef
#check @RBM.Gauss.exists_bdd_Kval_Kprim
#check @RBM.Gauss.hasDerivAt_Kval_Kprim
#check @RBM.Gauss.window_le_abs_im
#check @RBM.APrimeDriftTimeFamily.momentAt

namespace RBM.APrimeNormalizedTestFun

open Set
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Gauss.Dims} {N : ℕ} {T : Set ℝ}
  {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

private theorem timeD1_const_smul (c : ℝ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Gauss.timeD1 (fun r M => c • Ψ r M) u M = c • Gauss.timeD1 Ψ u M := by
  unfold Gauss.timeD1
  exact deriv_const_smul_field c _

private theorem testFunT₁_const_smul (h : Gauss.TestFunT₁ d N T Ψ) (c : ℝ) :
    Gauss.TestFunT₁ d N T (fun u M => c • Ψ u M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact (h.contDiffM u hu).const_smul c
  · intro u hu M
    exact (h.diffJoint u hu M).const_smul c
  · intro u hu
    have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        Gauss.timeD1 (fun r M => c • Ψ r M) u M) =
        fun M => c • Gauss.timeD1 Ψ u M := by
      funext M
      exact timeD1_const_smul c u M
    rw [heq]
    exact (h.contT u hu).const_smul c
  · obtain ⟨C, hC⟩ := h.bdd₀
    refine ⟨|c| * C, ?_⟩
    intro u hu M
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC u hu M) (abs_nonneg c)
  · obtain ⟨C, hC⟩ := h.bdd₁
    refine ⟨|c| * C, ?_⟩
    intro u hu M
    change ‖fderiv ℝ (c • Ψ u) M‖ ≤ |c| * C
    simp only [fderiv_const_smul_field, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC u hu M) (abs_nonneg c)
  · obtain ⟨C, hC⟩ := h.bdd₂
    refine ⟨|c| * C, ?_⟩
    intro u hu M
    change ‖fderiv ℝ (fderiv ℝ (c • Ψ u)) M‖ ≤ |c| * C
    simp only [fderiv_const_smul_field, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC u hu M) (abs_nonneg c)
  · obtain ⟨C, hC⟩ := h.bddT
    refine ⟨|c| * C, ?_⟩
    intro u hu M
    rw [timeD1_const_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC u hu M) (abs_nonneg c)

private theorem momentAt_eq_smul_raw (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hscale : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v)
    (r : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    APrimeDriftTimeFamily.momentAt d E D N p σ a s v r M =
      (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ ^ (2 * p) •
        Gauss.momentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
          (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a p r M := by
  rw [APrimeDriftTimeFamily.momentAt, APrimeDriftTimeFamily.coordAt,
    Gauss.momentObsT, Gauss.momentFun_eq]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
  rw [div_pow]
  simp only [Complex.real_smul, Complex.ofReal_mul,
    div_eq_mul_inv, inv_pow]
  ring

/-- T292's normalized Gaussian moment test function has all seven
`TestFunT₁` fields on a fixed closed window. -/
theorem normalizedTestFunBridge (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    APrimeDriftTimeFamily.NormalizedTestFunBridge d E D N p σ a s v := by
  classical
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d (D := D) hE hsv hv1 N a
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) E N hE.le hs0 hv1 (v := v) σ
  have hraw : Gauss.TestFunT₁ d N (Icc s v)
      (Gauss.momentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (fun r b => (Gauss.band d).Kval E N r (LoopData.idx (σ, b))) a p) :=
    Gauss.testFunT₁_momentObsT_of_coef E (m := 2) (List.length_ofFn) (by omega)
      (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (Gauss.band d).Kval E N r (LoopData.idx (σ, b)))
      (Gauss.Kprim (Gauss.band d) E N σ) a p (Gauss.window_eta_pos hE hv1) hcK
      (Gauss.window_le_abs_im hE hv1)
      (fun r hr b => Gauss.hasDerivAt_Kval_Kprim (Gauss.band d) E N
        (Gauss.window_norm_mul_lt hE.le hs0 hv1 r hr) σ b) hKb hK'b
  let c : ℝ := (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ ^ (2 * p)
  have hscaled := testFunT₁_const_smul hraw c
  have heq :
      (fun r M => c • Gauss.momentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
        ((v : ℝ) : ℂ)
        (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a p r M) =
      APrimeDriftTimeFamily.momentAt d E D N p σ a s v := by
    funext r M
    exact (momentAt_eq_smul_raw d E D N p σ a hscale r M).symm
  change Gauss.TestFunT₁ d N (Icc s v)
    (APrimeDriftTimeFamily.momentAt d E D N p σ a s v)
  rw [← heq]
  exact hscaled

theorem first_cell_witness (d : Gauss.Dims) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.NormalizedTestFunBridge d 0 0 N 1 σ a 0 (1 / 2) ∧
      (0 : ℝ) < 1 / 2 := by
  exact ⟨normalizedTestFunBridge d 0 0 N 1 σ a
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), by norm_num⟩

#print axioms RBM.APrimeNormalizedTestFun.normalizedTestFunBridge
#print axioms RBM.APrimeNormalizedTestFun.first_cell_witness

end RBM.APrimeNormalizedTestFun
