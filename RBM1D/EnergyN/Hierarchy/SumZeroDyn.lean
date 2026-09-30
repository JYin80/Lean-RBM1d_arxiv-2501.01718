/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.EnergyN.Hierarchy.Step3

/-!
# Crude scale bounds of the flow at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

`RBM.SumZeroDyn.flow_crudeN`: eventually in `N`, uniformly in `u ∈ [s,t]`, `1 ≤ W ℓ_u η_u ≤ N`,
`L, W ≤ N` and `(1-u)^{-1} ≤ N`. It uses only `hE : ∀ N, |E N| < 2` (no `κ`),
`RBM.Step3.scales_flowN` (`RBM1D/EnergyN/Hierarchy/Step3.lean`) and `RBM.Cond272N`
(`Flow/EnergyUniform.lean`), none of which fixes an `E`-dependent constant before `∀ᶠ N`.
-/

namespace RBM

namespace SumZeroDyn

section FlowScalesN

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **Crude bounds on the scales of the flow**, at an `N`-dependent energy: eventually in `N`,
uniformly in `u ∈ [s,t]`, `1 ≤ W ℓ_u η_u ≤ N`, `L, W ≤ N` and `(1-u)^{-1} ≤ N`. -/
theorem flow_crudeN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) :
    ∀ᶠ N : ℕ in atTop, (B.L N : ℝ) ≤ N ∧ (B.W N : ℝ) ≤ N ∧ 1 ≤ N ∧
      ∀ u : TimeIcc s t N,
        1 ≤ B.scale (E N) N u ∧ B.scale (E N) N u ≤ N ∧ (1 - (u : ℝ))⁻¹ ≤ N := by
  have sc := Step3.scales_flowN (B := B) hE hs0 hst ht1 hc
  filter_upwards [B.dim, sc.one_le_As, sc.one_le_R, sc.le_A, eventually_ge_atTop 1] with
    N hdim hAs hR hle hN1
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hL1 : (1 : ℝ) ≤ B.L N := by have := B.three_le_L N; exact_mod_cast (by omega : 1 ≤ B.L N)
  have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
  have hLN : (B.L N : ℝ) ≤ N := by nlinarith
  have hWN : (B.W N : ℝ) ≤ N := by nlinarith
  refine ⟨hLN, hWN, by exact_mod_cast hN1, fun u => ?_⟩
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hA1 : 1 ≤ B.scale (E N) N u := by
    have h4 := hle u
    have h5 : 1 ≤ Step3.flowR B s t N ^ 2 := one_le_pow₀ hR
    have h6 : 1 ≤ Step3.flowAs B (E N) s N ^ ((3 : ℝ) / 4) := Real.one_le_rpow hAs (by norm_num)
    have h7 : 1 ≤ Step3.flowR B s t N ^ 2 * Step3.flowAs B (E N) s N ^ ((3 : ℝ) / 4) := by
      nlinarith
    exact h7.trans h4
  have him := mE_im_le_one (hE N)
  have him0 := mE_im_pos (hE N)
  have hℓ := ellHat_real_le_L (L := B.L N) hu1
  have hℓ0 := Step3.ellHat_pos_of_lt_one (L := B.L N) (by have := B.three_le_L N; omega) hu1
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have hscale := Band.scale_eq B (E N) N u
  refine ⟨hA1, ?_, ?_⟩
  · rw [hscale]
    have h1 : (1 - (u : ℝ)) * ellHat (B.L N) (u : ℂ) ≤ B.L N := by nlinarith
    have h2 : (B.W N : ℝ) * (mE (E N)).im ≤ B.W N := by nlinarith
    calc (B.W N : ℝ) * (mE (E N)).im * ((1 - (u : ℝ)) * ellHat (B.L N) (u : ℂ))
        ≤ B.W N * B.L N := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ ≤ N := hWL
  · rw [inv_le_iff_one_le_mul₀ h1u]
    rw [hscale] at hA1
    have h1 : (B.W N : ℝ) * (mE (E N)).im * ellHat (B.L N) (u : ℂ) ≤ N := by
      calc (B.W N : ℝ) * (mE (E N)).im * ellHat (B.L N) (u : ℂ) ≤ B.W N * 1 * B.L N := by gcongr
        _ ≤ N := by linarith
    nlinarith

end FlowScalesN

end SumZeroDyn

end RBM
