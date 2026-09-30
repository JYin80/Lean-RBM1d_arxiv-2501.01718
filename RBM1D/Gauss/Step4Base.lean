/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step3Charges
import RBM1D.Gauss.Step2Plain
import RBM1D.Gauss.PPUniform

/-!
# Step 4 base inputs: the scale check at loop length `2`

Formalization support for Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional
Random Band Matrices*, §5.7: at loop length `2` the bound `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}`
is weaker than the Step 4 target `Ψ(2,l)` for every `l`.

## Main results

* `RBM.Gauss.quarter_le_psi_two` — the scale check made precise: `Ψ(2,l) ≥ A_s^{1/2}`
  (`Step3.psi`'s definition, both `l = 0` and `l ≥ 1`) and `A_u^{1/4} ≤ A_s^{1/4} ≤ A_s^{1/2}`
  (`A_u ≤ A_s`, `A_s ≥ 1`), so `A_u^{1/4} ≤ Ψ(2,l)` for every `l`.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace Gauss

variable (d : Dims)

/-! ### The `m = 2` case -/

/-- **The scale check, made precise**: `A_u^{1/4} ≤ Ψ(2,l,s,u,t)` for every `l`, given
`A_s ≥ 1`, `R ≥ 0`, `0 ≤ A_u ≤ A_s`. From `Step3.psi`'s definition, `Ψ(2,l) ≥ A_s^{1/2}` for
both `l = 0` (`psi_zero`, the extra term `R * A_u ≥ 0`) and `l ≥ 1` (`psi_of_ne_zero`, `Psi`, the
extra term `R * A_s^{1-l/4} ≥ 0` since `A_s > 0`); and `A_u^{1/4} ≤ A_s^{1/4} ≤ A_s^{1/2}`
(`A_u ≤ A_s`, `A_s ≥ 1`). -/
theorem quarter_le_psi_two {As R Au : ℝ} (hAs1 : 1 ≤ As) (hR0 : 0 ≤ R) (hAu0 : 0 ≤ Au)
    (hAuAs : Au ≤ As) (l : ℕ) : Au ^ ((1 : ℝ) / 4) ≤ Step3.psi As R Au 2 l := by
  have hAs0 : (0 : ℝ) < As := by linarith
  have hhalf : Au ^ ((1 : ℝ) / 4) ≤ As ^ ((1 : ℝ) / 2) := by
    calc Au ^ ((1 : ℝ) / 4) ≤ As ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hAu0 hAuAs (by norm_num)
      _ ≤ As ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hAs1 (by norm_num)
  rcases Nat.eq_zero_or_pos l with hl0 | hl0
  · subst hl0
    rw [Step3.psi_zero]
    exact hhalf.trans (le_add_of_nonneg_right (by positivity))
  · rw [Step3.psi_of_ne_zero hl0.ne']
    unfold Step3.Psi
    exact hhalf.trans (le_add_of_nonneg_right (by positivity))

end Gauss

end RBM

end

