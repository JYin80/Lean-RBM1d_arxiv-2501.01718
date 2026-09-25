/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingControlExtension
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.PermutationFourierSemicircleZeroMode
import RBM1D.Gauss.DimsExample

/-! # The zero-mode error is eventually below the centered-event scalar margin

For the actual `Dims.exampleGrow` sequence, the producer `qExt` at `E=0` on
`[0,1/2]` is exactly `1/(W_N(1-u))`. Thus its doubled value dominates `2/W_N`
uniformly, and every-permutation T933 zero-mode error is eventually strictly
below `N^ζ (2 qExt)`, for each fixed `ζ>0`. This is a scalar comparison only:
it does not establish membership in the centered event or a matrix/probability
claim.
-/

namespace RBM.Gauss

open Filter Set

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev s : ℕ → ℝ := fun _ => 0
private noncomputable abbrev t : ℕ → ℝ := fun _ => 1 / 2

/-- Exact `E=0`, `s=0`, `t=1/2` specialization of the actual `qExt` producer. -/
theorem permutationFourierExampleGrow_qExt_eq_fraction
    (N : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 / 2)) :
    APrimeGeneralMovingControlExtension.qExt 0 s t N u =
      1 / ((d.W N : ℝ) * (1 - u)) := by
  rw [APrimeGeneralMovingControlExtension.qExt_eq_q hu]
  rw [APrimeGeneralMovingControlExtension.q_eq_inv (E := 0) (s := s) (N := N) (u := u)
    (by norm_num) (by norm_num) (by norm_num) hu.1
    (hu.2.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))]
  have hell : (Gauss.band d).ell N (s N) = 1 := by
    change ellHat (d.L N) ((s N : ℝ) : ℂ) = 1
    rw [show (s N : ℝ) = 0 by rfl]
    exact ellHat_zero _ (d.three_le_L N)
  have heta : etaT 0 u = 1 - u := by
    rw [etaT, mE_im]
    norm_num
  rw [hell, heta]
  simp [d]

/-- The actual producer is uniformly bounded below by `1/W_N` on the window. -/
theorem permutationFourierExampleGrow_qExt_ge_invW
    (N : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 / 2)) :
    1 / (d.W N : ℝ) ≤
      APrimeGeneralMovingControlExtension.qExt 0 s t N u := by
  rw [permutationFourierExampleGrow_qExt_eq_fraction N hu]
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hu' : 0 < 1 - u := by linarith [hu.2]
  have hden : 0 < (d.W N : ℝ) * (1 - u) := mul_pos hW hu'
  rw [one_div, one_div]
  apply (inv_le_inv₀ hW hden).2
  have hfac : 1 - u ≤ 1 := by linarith [hu.1]
  nlinarith [mul_le_mul_of_nonneg_right hfac hW.le]

/-- At the actual width-one endpoint, the producer takes distinct positive
values at the two ends of the nontrivial half-time interval. -/
theorem permutationFourierExampleGrow_W1_nondegenerate_check :
    d.W 0 = 1 ∧
    APrimeGeneralMovingControlExtension.qExt 0 s t 0 0 = 1 ∧
    APrimeGeneralMovingControlExtension.qExt 0 s t 0 (1 / 2) = 2 ∧
    0 < APrimeGeneralMovingControlExtension.qExt 0 s t 0 0 ∧
    0 < APrimeGeneralMovingControlExtension.qExt 0 s t 0 (1 / 2) := by
  have hW : d.W 0 = 1 := by simp [d, Dims.exampleGrow_W, Gauss.Dims.growW, Gauss.Dims.growL]
  have h0 := permutationFourierExampleGrow_qExt_eq_fraction 0
    (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2))
  have hhalf := permutationFourierExampleGrow_qExt_eq_fraction 0
    (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 (1 / 2))
  rw [hW] at h0 hhalf
  refine ⟨hW, ?_, ?_, ?_, ?_⟩ <;> norm_num at h0 hhalf ⊢ <;> linarith

/-- For each fixed positive `ζ`, the actual T933 permutation-invariant
zero-mode error is eventually strictly below the centered-event scalar
threshold, simultaneously for every `u∈[0,1/2]` and every permutation. -/
theorem eventually_permutationFourierExampleGrow_zeroMode_below_centered_threshold
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Icc (0 : ℝ) (1 / 2), ∀ π : Equiv.Perm (Fin (d.W N)),
        ‖permutationFourierSum (d.W N)
          (fun j : Fin (d.W N) => semicircleFlowKernel u
            (semicircleLambda (d.W N) (d.W_pos N) j.val j.isLt))
          (fun _ => 1) π - Complex.I‖ <
          (N : ℝ) ^ zeta *
            (2 * APrimeGeneralMovingControlExtension.qExt 0 s t N u) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) ^ zeta) atTop atTop :=
    (tendsto_rpow_atTop hzeta).comp tendsto_natCast_atTop_atTop
  have hNlarge : ∀ᶠ N : ℕ in atTop, 4 * Real.sqrt 2 < (N : ℝ) ^ zeta :=
    htop.eventually_gt_atTop (4 * Real.sqrt 2)
  filter_upwards [hNlarge, eventually_gt_atTop 0] with N hlarge hNpos u hu π
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hq := permutationFourierExampleGrow_qExt_ge_invW N hu
  have hq2 : 2 / (d.W N : ℝ) ≤
      2 * APrimeGeneralMovingControlExtension.qExt 0 s t N u := by
    calc
      2 / (d.W N : ℝ) = 2 * (1 / (d.W N : ℝ)) := by ring
      _ ≤ 2 * APrimeGeneralMovingControlExtension.qExt 0 s t N u :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
  have hbase : 8 * Real.sqrt 2 / (d.W N : ℝ) <
      (N : ℝ) ^ zeta * (2 / (d.W N : ℝ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hr : 0 < (N : ℝ) ^ zeta := Real.rpow_pos_of_pos hN zeta
    have hi : 0 < ((d.W N : ℝ)⁻¹) := inv_pos.mpr hW
    nlinarith [mul_lt_mul_of_pos_right hlarge hi]
  have hscale : 0 ≤ (N : ℝ) ^ zeta := Real.rpow_nonneg (Nat.cast_nonneg N) zeta
  have hstrict := hbase.trans_le (mul_le_mul_of_nonneg_left hq2 hscale)
  have herr := permutationFourierSemicircleZeroMode_bound (d.W N) (d.W_pos N)
    u hu.1 hu.2 π
  exact lt_of_le_of_lt herr hstrict

#print axioms permutationFourierExampleGrow_qExt_eq_fraction
#print axioms permutationFourierExampleGrow_qExt_ge_invW
#print axioms permutationFourierExampleGrow_W1_nondegenerate_check
#print axioms eventually_permutationFourierExampleGrow_zeroMode_below_centered_threshold

end RBM.Gauss
