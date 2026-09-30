/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.QVEndpoint
import RBM1D.Gauss.GridQVConv

/-!
# (2.79): far-split QV through `Uker`

Formalization of the far-split analogue of `RBM.Gauss.Grid.qv_conv_le`
(`GridQVConv.lean`): the same weighted quadratic-variation bound through `Uker`,
but with the rate `R` of the Cauchy–Schwarz hypothesis split into a near-supported part (weight
`Qn`), a tail part
(weight `Qf`), and a distance-independent residual (weight `Qr`), and the fixed input
loop `b` assumed far (`6 * ellStar W (ellHat L v) ≤ zdist L (b0 - b1)`).

This is a purely deterministic kernel estimate: no (2.72)/regularity hypothesis
appears anywhere.

## Main declarations

* `RBM.Gauss.Grid.qv_conv_le_far` — the far-split weighted QV bound.
-/

namespace RBM
namespace Gauss
namespace Grid

open Matrix

variable {L : ℕ} [NeZero L]

/-! ### Local real-analysis helpers -/

private theorem far_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  have hxy : 0 ≤ √x * √y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt (add_nonneg hx hy), Real.sqrt_nonneg x,
    Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y)]

private theorem far_sqrt_three_le {A B C T χ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hχ : χ = 0 ∨ χ = 1) :
    √((A * χ + B) * T ^ 2 + C)
      ≤ √A * (T * χ) + √B * T + √C := by
  rcases hχ with rfl | rfl
  · simp only [mul_zero, zero_add]
    calc
      √(B * T ^ 2 + C) ≤ √(B * T ^ 2) + √C :=
        far_sqrt_add_le _ _ (mul_nonneg hB (sq_nonneg _)) hC
      _ = √B * T + √C := by rw [Real.sqrt_mul hB, Real.sqrt_sq hT]
  · simp only [mul_one]
    have hAB : 0 ≤ A * T ^ 2 + B * T ^ 2 :=
      add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _))
    have heq : (A + B) * T ^ 2 + C = (A * T ^ 2 + B * T ^ 2) + C := by ring
    rw [heq]
    calc
      √(A * T ^ 2 + B * T ^ 2 + C)
        ≤ √(A * T ^ 2 + B * T ^ 2) + √C := far_sqrt_add_le _ _ hAB hC
      _ ≤ (√(A * T ^ 2) + √(B * T ^ 2)) + √C := by
        gcongr
        exact far_sqrt_add_le _ _ (mul_nonneg hA (sq_nonneg _))
          (mul_nonneg hB (sq_nonneg _))
      _ = √A * T + √B * T + √C := by
        rw [Real.sqrt_mul hA, Real.sqrt_mul hB, Real.sqrt_sq hT]

/-! ### (T1) -/

/-- **(T1)**: the far-split weighted quadratic-variation bound through `Uker`.
Reuses steps 1–2 of `qv_conv_le` (triangle inequality, then the Cauchy–Schwarz hypothesis) and,
directly (not through a near/far case split of the kernel estimate, which would
mis-file the boundary `zdist = 6 * ellStar` into its near branch), the three kernel
estimates `weightedKernel_near_tail_far_le`, `weightedKernel_tail_le`,
`weightedKernel_row_le`. -/
theorem qv_conv_le_far (hL : 3 ≤ L) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u v : ℝ} (hu0 : 0 ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) {W D Qn Qf Qr : ℝ} (hW : Real.exp 1 ≤ W)
    (hQn : 0 ≤ Qn) (hQf : 0 ≤ Qf) (hQr : 0 ≤ Qr)
    (hAuv : W * ellHat L (v : ℂ) * ((1 - v) * m) ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    {R : LoopArg L 2 → ℝ} (hR0 : ∀ a, 0 ≤ R a)
    (hR : ∀ a, R a ≤ (Qn * (if (zdist L (a 0 - a 1) : ℝ) ≤ 4 * ellStar W (ellHat L (u : ℂ))
                              then 1 else 0) + Qf) *
                 tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (a 0 - a 1)) ^ 2 + Qr)
    {EE : LoopArg L 2 → LoopArg L 2 → ℂ}
    (hEE : ∀ a a', ‖EE a a'‖ ≤ Real.sqrt (R a) * Real.sqrt (R a'))
    (b : LoopArg L 2) (hb : 6 * ellStar W (ellHat L (v : ℂ)) ≤ (zdist L (b 0 - b 1) : ℝ)) :
    ‖∑ a, ∑ a', (∏ i, edgeKer L 1 u v (b i) (a i)) *
        (starRingEnd ℂ) (∏ i, edgeKer L 1 u v (b i) (a' i)) * EE a a'‖
      ≤ (√Qn * tailT W (ellHat L u) ((1 - u) * m) D 0 *
            (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
              Real.exp (-(ellStar W (ellHat L v) / ellHat L v / 2)))
          + √Qf * ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
              tailT W (ellHat L v) ((1 - v) * m) D (zdist L (b 0 - b 1))
          + √Qr * ((1 - u) / (1 - v)) ^ 2) ^ 2 := by
  classical
  have hv0 : 0 ≤ v := hu0.trans huv
  set c : LoopArg L 2 → ℝ := fun x => Real.sqrt (R x) with hc_def
  have hc_nonneg : ∀ x, 0 ≤ c x := fun x => Real.sqrt_nonneg _
  let K : LoopArg L 2 → ℝ := fun x =>
    ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (x i)‖
  let Tu : LoopArg L 2 → ℝ := fun x =>
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (x 0 - x 1))
  let χu : LoopArg L 2 → ℝ := fun x =>
    if (zdist L (x 0 - x 1) : ℝ) ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0
  -- Pointwise bound on `c` from `hR`, via `far_sqrt_three_le`.
  have hc_le : ∀ x : LoopArg L 2,
      c x ≤ Real.sqrt Qn * (Tu x * χu x) + Real.sqrt Qf * Tu x + Real.sqrt Qr := by
    intro x
    have hT0 : 0 ≤ Tu x := tailT_nonneg (le_trans (Real.exp_nonneg 1) hW) _
    have hχ01 : χu x = 0 ∨ χu x = 1 := by
      by_cases hcond : (zdist L (x 0 - x 1) : ℝ) ≤ 4 * ellStar W (ellHat L (u : ℂ))
      · exact Or.inr (if_pos hcond)
      · exact Or.inl (if_neg hcond)
    calc c x = Real.sqrt (R x) := rfl
      _ ≤ Real.sqrt ((Qn * χu x + Qf) * Tu x ^ 2 + Qr) := Real.sqrt_le_sqrt (hR x)
      _ ≤ Real.sqrt Qn * (Tu x * χu x) + Real.sqrt Qf * Tu x + Real.sqrt Qr :=
          far_sqrt_three_le hQn hQf hQr hT0 hχ01
  -- Steps 1–2 of `qv_conv_le`: triangle inequality, then the Cauchy–Schwarz hypothesis.
  have hstep1 :
      ‖∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) *
            (starRingEnd ℂ) (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)) * EE a a'‖
        ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2, K a * K a' * ‖EE a a'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    exact le_of_eq (by rw [norm_mul, norm_mul, Complex.norm_conj])
  have hstep2 :
      (∑ a : LoopArg L 2, ∑ a' : LoopArg L 2, K a * K a' * ‖EE a a'‖)
        ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2, (K a * c a) * (K a' * c a') := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ => ?_
    have hnn1 : (0 : ℝ) ≤ K a * K a' := by positivity
    calc K a * K a' * ‖EE a a'‖ ≤ K a * K a' * (c a * c a') :=
          mul_le_mul_of_nonneg_left (hEE a a') hnn1
      _ = (K a * c a) * (K a' * c a') := by ring
  have hstep3 :
      (∑ a : LoopArg L 2, ∑ a' : LoopArg L 2, (K a * c a) * (K a' * c a'))
        = (∑ a : LoopArg L 2, K a * c a) ^ 2 := by
    rw [sq, Fintype.sum_mul_sum]
  -- Bound `∑ₐ K a * c a` directly via the three far-split kernel lemmas.
  have hK_sum_le :
      (∑ a : LoopArg L 2, K a * c a) ≤
        Real.sqrt Qn * tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
            (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
              Real.exp (-(ellStar W (ellHat L (v : ℂ)) / ellHat L (v : ℂ) / 2)))
          + Real.sqrt Qf * ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
              tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (b 0 - b 1))
          + Real.sqrt Qr * ((1 - u) / (1 - v)) ^ 2 := by
    have hsum_le :
        (∑ a : LoopArg L 2, K a * c a)
          ≤ Real.sqrt Qn * (∑ a : LoopArg L 2, K a * (Tu a * χu a))
            + Real.sqrt Qf * (∑ a : LoopArg L 2, K a * Tu a)
            + Real.sqrt Qr * (∑ a : LoopArg L 2, K a) := by
      calc (∑ a : LoopArg L 2, K a * c a)
          ≤ ∑ a : LoopArg L 2,
              K a * (Real.sqrt Qn * (Tu a * χu a) + Real.sqrt Qf * Tu a + Real.sqrt Qr) :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hc_le a) (norm_nonneg _)
        _ = Real.sqrt Qn * (∑ a : LoopArg L 2, K a * (Tu a * χu a))
              + Real.sqrt Qf * (∑ a : LoopArg L 2, K a * Tu a)
              + Real.sqrt Qr * (∑ a : LoopArg L 2, K a) := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun a _ => by ring
    have h1 := QVEndpoint.weightedKernel_near_tail_far_le
      (D := D) L hL hm0 hm1 hu0 huv hv1 hW b hb
    have h2 := QVEndpoint.weightedKernel_tail_le
      (D := D) L hL hm0 hm1 hu0 huv hv1 hW hAuv b
    have h3 := QVEndpoint.weightedKernel_row_le L hL huv hv0 hv1 b
    have e1 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg Qn)
    have e2 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg Qf)
    have e3 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg Qr)
    calc (∑ a : LoopArg L 2, K a * c a)
        ≤ Real.sqrt Qn * (∑ a : LoopArg L 2, K a * (Tu a * χu a))
          + Real.sqrt Qf * (∑ a : LoopArg L 2, K a * Tu a)
          + Real.sqrt Qr * (∑ a : LoopArg L 2, K a) := hsum_le
      _ ≤ _ := by nlinarith [e1, e2, e3]
  have hKc_nonneg : 0 ≤ ∑ a : LoopArg L 2, K a * c a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (norm_nonneg _) (hc_nonneg a)
  calc ‖∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
        (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) *
          (starRingEnd ℂ) (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)) * EE a a'‖
      ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2, K a * K a' * ‖EE a a'‖ := hstep1
    _ ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2, (K a * c a) * (K a' * c a') := hstep2
    _ = (∑ a : LoopArg L 2, K a * c a) ^ 2 := hstep3
    _ ≤ (Real.sqrt Qn * tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
            (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
              Real.exp (-(ellStar W (ellHat L (v : ℂ)) / ellHat L (v : ℂ) / 2)))
          + Real.sqrt Qf * ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
              tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (b 0 - b 1))
          + Real.sqrt Qr * ((1 - u) / (1 - v)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ hKc_nonneg hK_sum_le 2

/-! ### Non-vacuity witness -/

end Grid
end Gauss
end RBM
