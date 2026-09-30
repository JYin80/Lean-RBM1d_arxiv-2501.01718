/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57
import Mathlib.Analysis.MeanInequalities

/-!
# The `W^{-D}` floor of the tail function (5.27)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Section 5.3 (step 2 of Theorem 2.21).

`RBM.Cutoff.one_le_rpow_mul_tailT_sq`: for `W ≥ 1`, `1 ≤ W^{2D} T_{u,D}(ℓ)²`.  The floor `W^{-D}`
of the tail function `T_{u,D}` of (5.27) is what lets an additive remainder be absorbed into the
`T_{u,D}²` normalization, at the cost of `W^{2D}`.  Nothing here is random.
-/

namespace RBM
namespace Cutoff

open Real Finset

/-! ### The smooth maximum (`r`-norm) -/

variable {ι : Type*} [Fintype ι]

variable {r : ℝ} {a : ι → ℝ}

/-! ### The chain rule for the smooth maximum -/

/-! ### The weighted quadratic form: `∑ S |∂J|²` from `∑ S |∂(L-K)_a|²` -/

/-! ### `∂_u T_{u,D}` along the flow -/

section Flow

variable {W D ℓ : ℝ} {ℓf ηf : ℝ → ℝ} {ℓ' η' u : ℝ}

end Flow

/-! ### The `W^{-D}` floor: absorbing an additive remainder into `T_{u,D}²` -/

section Floor

variable {W ℓu ηu D ℓ : ℝ}

/-- `1 ≤ W^{2D} T_{u,D}(ℓ)²`: the floor `W^{-D}` of (5.27) is exactly what lets an additive
remainder be absorbed into the `T_{u,D}²` normalization, at the cost of `W^{2D}`. -/
theorem one_le_rpow_mul_tailT_sq (hW : 1 ≤ W) :
    1 ≤ W ^ (2 * D) * tailT W ℓu ηu D ℓ ^ 2 := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hfl : (0 : ℝ) < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hle : W ^ (-D) ≤ tailT W ℓu ηu D ℓ := rpow_neg_le_tailT ℓ
  have hsq : (W ^ (-D)) ^ 2 ≤ tailT W ℓu ηu D ℓ ^ 2 := by nlinarith
  have hid : (W ^ (-D)) ^ 2 = W ^ (-(2 * D)) := by
    rw [sq, ← Real.rpow_add hW0]; ring_nf
  have hcancel : W ^ (2 * D) * W ^ (-(2 * D)) = 1 := by
    rw [← Real.rpow_add hW0]; simp
  have hpos : (0 : ℝ) < W ^ (2 * D) := Real.rpow_pos_of_pos hW0 _
  calc (1 : ℝ) = W ^ (2 * D) * W ^ (-(2 * D)) := hcancel.symm
    _ = W ^ (2 * D) * (W ^ (-D)) ^ 2 := by rw [hid]
    _ ≤ W ^ (2 * D) * tailT W ℓu ηu D ℓ ^ 2 := by nlinarith

end Floor

/-! ### `∑ S |∂J|²` from (5.36) -/

/-! ### The time dependence of the threshold: `Θ̇_u / Θ_u = 4 m / η_u` -/

section Threshold

variable {ηf : ℝ → ℝ} {m u c : ℝ}

end Threshold

/-! ### The second derivative -/

section SecondDeriv
variable {ι : Type*} [Fintype ι] {r : ℝ}

end SecondDeriv

end Cutoff
end RBM

