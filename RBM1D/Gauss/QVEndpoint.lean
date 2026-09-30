/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.WeightedSumSqrt
import RBM1D.Gauss.MomentDuhamelHypGauss
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Gauss.Lemma514Moment

/-!
# The doubled evolution kernel in the endpoint quadratic variation

The first bridge below applies Lemma 7.1 to the actual `E ⊗ E` tensor, with the
correct conjugated second copy of the charge.  Its input is an explicit finite
sum of the tensor entries, rather than an assumed bound on the evolved tensor.
The sharp spatial estimate (5.42) requires a separate weighted convolution
bound for that sum.
-/

namespace RBM
namespace QVEndpoint

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

private noncomputable def kernelPhase (z : ℂ) : ℂ :=
  if z = 0 then 0 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

private theorem norm_kernelPhase_le_one (z : ℂ) : ‖kernelPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [kernelPhase, hz]
  · simp only [kernelPhase, if_neg hz, norm_div, RCLike.norm_conj,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

private theorem mul_kernelPhase (z : ℂ) : z * kernelPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [kernelPhase, hz]
  · simp only [kernelPhase, if_neg hz]
    rw [← mul_div_assoc, Gauss.mul_conj_eq, Complex.ofReal_pow]
    have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    field_simp

/-- Choosing the phase of every input separately realizes the absolute kernel
convolution as the norm of one `Uker` output. -/
private theorem weightedKernelSum_eq_norm_Uker (L n : ℕ) [NeZero L]
    (ξ : Fin n → ℂ) (u v : ℝ) (a : LoopArg L n)
    (w : LoopArg L n → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : LoopArg L n,
        ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)‖ * w b)
      = ‖Uker L ξ (u : ℂ) (v : ℂ)
          (fun b => kernelPhase
            (∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)) * (w b : ℂ)) a‖ := by
  classical
  set K : LoopArg L n → ℂ :=
    fun b => ∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)
  have hsum : (0 : ℝ) ≤ ∑ b : LoopArg L n, ‖K b‖ * w b :=
    Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hw b)
  have hval : Uker L ξ (u : ℂ) (v : ℂ)
      (fun b => kernelPhase (K b) * (w b : ℂ)) a
        = ((∑ b : LoopArg L n, ‖K b‖ * w b) : ℂ) := by
    rw [Uker_apply]
    exact Finset.sum_congr rfl fun b _ => by
      change K b * (kernelPhase (K b) * (w b : ℂ)) = (‖K b‖ : ℂ) * (w b : ℂ)
      rw [← mul_assoc, mul_kernelPhase]
  change (∑ b : LoopArg L n, ‖K b‖ * w b) = _
  rw [hval]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg hsum]

/-- The absolute two-loop kernel convolved with the tail, obtained from the
existing (5.39) propagation estimate by a phase choice at each input loop. -/
theorem weightedKernel_tail_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u v : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) {W D : ℝ}
    (hW : Real.exp 1 ≤ W)
    (hAuv : W * ellHat L (v : ℂ) * ((1 - v) * m)
      ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    (a : LoopArg L 2) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ *
          tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (b 0 - b 1)))
      ≤ ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
        tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (a 0 - a 1)) := by
  classical
  let w : LoopArg L 2 → ℝ := fun b =>
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (b 0 - b 1))
  let K : LoopArg L 2 → ℂ :=
    fun b => ∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)
  let A : LoopArg L 2 → ℂ := fun b => kernelPhase (K b) * (w b : ℂ)
  have hW0 : 0 ≤ W := le_trans (Real.exp_nonneg 1) hW
  have hw (b : LoopArg L 2) : 0 ≤ w b := tailT_nonneg hW0 _
  have hA (b : LoopArg L 2) : ‖A b‖ ≤ w b := by
    rw [show A b = kernelPhase (K b) * (w b : ℂ) from rfl,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw b)]
    calc ‖kernelPhase (K b)‖ * w b ≤ 1 * w b :=
          mul_le_mul_of_nonneg_right (norm_kernelPhase_le_one _) (hw b)
      _ = w b := one_mul _
  have hprop := Step2.norm_Uker_le_of_tail hL hm0 hm1 hu0 huv
    (hu0.trans huv) hv1 hW (by norm_num : (0 : ℝ) ≤ 1) hAuv
    (A := A) (fun b => by simpa only [one_mul] using hA b) a
  have hsum := weightedKernelSum_eq_norm_Uker L 2 (fun _ => 1) u v a w hw
  change (∑ b : LoopArg L 2, ‖K b‖ * w b) ≤ _
  rw [hsum]
  simpa only [one_mul, mul_one] using hprop

/-- Absolute kernel mass carried from a diagonal band into a separated pair. -/
theorem weightedKernel_supp_far_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {ρ Δ : ℝ} (hΔ : 0 < Δ) (a : LoopArg L 2)
    (hd : ρ + 2 * Δ ≤ (zdist L (a 0 - a 1) : ℝ)) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ *
          (if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then 1 else 0))
      ≤ 128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
        Real.exp (-(Δ / ellHat L (v : ℂ) / 2)) := by
  classical
  let w : LoopArg L 2 → ℝ := fun b =>
    if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then 1 else 0
  let K : LoopArg L 2 → ℂ :=
    fun b => ∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)
  let A : LoopArg L 2 → ℂ := fun b => kernelPhase (K b) * (w b : ℂ)
  have hw (b : LoopArg L 2) : 0 ≤ w b := by simp only [w]; split_ifs <;> norm_num
  have hA (b : LoopArg L 2) : ‖A b‖ ≤ w b := by
    rw [show A b = kernelPhase (K b) * (w b : ℂ) from rfl,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw b)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (norm_kernelPhase_le_one (K b)) (hw b)
  have hprop := Step2MomentStep.norm_Uker_supp_far_le L hL hu0 huv hv1
    (by norm_num : (0 : ℝ) ≤ 1) hΔ (A := A)
    (fun b => by simpa only [one_mul] using hA b) a hd
  have hsum := weightedKernelSum_eq_norm_Uker L 2 (fun _ => 1) u v a w hw
  change (∑ b : LoopArg L 2, ‖K b‖ * w b) ≤ _
  rw [hsum]
  simpa only [one_mul, mul_one] using hprop

/-- A near-diagonal input band of radius `4ℓ*_u` reaches beyond `6ℓ*_v`
only through the exponentially decaying part of the two-loop kernel. -/
theorem weightedKernel_near_tail_far_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {m : ℝ} (_hm0 : 0 < m) (_hm1 : m ≤ 1)
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {W D : ℝ} (hW : Real.exp 1 ≤ W)
    (a : LoopArg L 2)
    (hd : 6 * ellStar W (ellHat L (v : ℂ))
      ≤ (zdist L (a 0 - a 1) : ℝ)) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ *
          (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
              (zdist L (b 0 - b 1)) *
            (if (zdist L (b 0 - b 1) : ℝ)
                ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0)))
      ≤ tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
          (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
            Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
              ellHat L (v : ℂ) / 2))) := by
  classical
  have hu1 : u < 1 := huv.trans_lt hv1
  have hv0 : 0 ≤ v := hu0.trans huv
  have hℓu : 0 < ellHat L (u : ℂ) := by
    have := one_le_ellHat_of_nonneg (L := L) (by omega : 1 ≤ L) hu0 hu1
    linarith
  have hℓv : 0 < ellHat L (v : ℂ) := by
    have := one_le_ellHat_of_nonneg (L := L) (by omega : 1 ≤ L) hv0 hv1
    linarith
  have hlog : 0 ≤ Real.log W :=
    Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hW)
  have hp : 0 ≤ Real.log W ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hlog _
  have hstar : ellStar W (ellHat L (u : ℂ))
      ≤ ellStar W (ellHat L (v : ℂ)) := by
    unfold ellStar
    exact mul_le_mul_of_nonneg_left (Step3.ellHat_mono (L := L) huv hv1) hp
  have hΔ : 0 < ellStar W (ellHat L (v : ℂ)) := by
    unfold ellStar
    have hlog1 : 1 ≤ Real.log W := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hW
    have : 0 < Real.log W ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hd' : 4 * ellStar W (ellHat L (u : ℂ)) +
      2 * ellStar W (ellHat L (v : ℂ))
        ≤ (zdist L (a 0 - a 1) : ℝ) := by linarith
  have hsup := weightedKernel_supp_far_le L hL hu0 huv hv1 hΔ a hd'
  have hW0 : 0 ≤ W := le_trans (Real.exp_nonneg 1) hW
  have hT0 : 0 ≤ tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 :=
    tailT_nonneg hW0 _
  let T : ℝ := tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0
  let K : LoopArg L 2 → ℝ := fun b =>
    ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖
  let χ : LoopArg L 2 → ℝ := fun b =>
    if (zdist L (b 0 - b 1) : ℝ)
      ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0
  have hpt (b : LoopArg L 2) :
      K b * (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
          (zdist L (b 0 - b 1)) * χ b) ≤ T * (K b * χ b) := by
    have htail : tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
        (zdist L (b 0 - b 1)) ≤ T :=
      tailT_antitone hℓu (Nat.cast_nonneg _)
    have hχ : 0 ≤ χ b := by simp only [χ]; split_ifs <;> norm_num
    nlinarith [mul_nonneg (norm_nonneg
      (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i))) hχ]
  calc
    (∑ b : LoopArg L 2, K b *
        (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
          (zdist L (b 0 - b 1)) * χ b))
      ≤ ∑ b : LoopArg L 2, T * (K b * χ b) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = T * ∑ b : LoopArg L 2, K b * χ b := by rw [Finset.mul_sum]
    _ ≤ T * (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
        Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
          ellHat L (v : ℂ) / 2))) :=
        mul_le_mul_of_nonneg_left hsup hT0

/-- Lemma 7.1's row expansion for the absolute two-loop kernel. -/
theorem weightedKernel_row_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {u v : ℝ} (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (a : LoopArg L 2) :
    (∑ b : LoopArg L 2,
      ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖)
        ≤ ((1 - u) / (1 - v)) ^ 2 := by
  let f : Fin 2 → ZMod L → ℝ :=
    fun i c => ‖edgeKer L 1 (u : ℂ) (v : ℂ) (a i) c‖
  have h0 : ∀ i : Fin 2, 0 ≤ ∑ c : ZMod L, f i c :=
    fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hle : ∀ i : Fin 2,
      ∑ c : ZMod L, f i c ≤ (1 - u) / (1 - v) :=
    fun i => Step2MomentStep.sum_norm_edgeKer_one_row_le L hL huv hv0 hv1 (a i)
  calc
    (∑ b : LoopArg L 2,
      ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖)
      = ∑ b : LoopArg L 2, ∏ i : Fin 2, f i (b i) := by
        exact Finset.sum_congr rfl fun b _ => by simp [f]
    _ = ∏ i : Fin 2, ∑ c : ZMod L, f i c := sum_prod_pi L f
    _ ≤ ∏ _i : Fin 2, (1 - u) / (1 - v) :=
      Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => hle i)
    _ = ((1 - u) / (1 - v)) ^ 2 := by simp [div_pow]

noncomputable def diagNearRate (B : Band Ω) (N : ℕ) (ℓu ℓs ηu : ℝ) : ℝ :=
  2 * ηu⁻¹ * Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5

noncomputable def diagFarRate (B : Band Ω) (N : ℕ)
    (ℓu ηu D J Smax : ℝ) : ℝ :=
  2 * ηu⁻¹ *
      (Lemma57.cFar2 (B.W N : ℝ) ℓu *
          ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    + 4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3

end QVEndpoint
end RBM
