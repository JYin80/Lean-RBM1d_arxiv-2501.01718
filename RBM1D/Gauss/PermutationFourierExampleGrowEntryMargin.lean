/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowUniform
import RBM1D.Gauss.PermutationFourierExampleGrowFlowMargin
import RBM1D.Gauss.PermutationFourierExampleGrowZeroFlowMargin

/-! The actual growing-model midpoint-quantile table has one permutation whose
Fourier entries stay strictly within the literal closed-flow margin, uniformly
over the closed half-time interval. This is a deterministic scalar auxiliary;
it makes no matrix, sample, or local-law claim. -/

set_option autoImplicit false

open RBM RBM.Gauss Filter

namespace RBM.Gauss

/-- For all sufficiently large actual growing widths, one permutation is chosen
before every time and pair of matrix indices, and every normalized Fourier
entry of the actual midpoint-quantile flow table is strictly within the
literal `flowDelta` margin. -/
theorem permutationFourierExampleGrow_eventually_entry_margin :
    ∀ᶠ N : ℕ in atTop,
      ∃ π : PermΩ (Dims.exampleGrow.W N),
        ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
          ∀ a b : Fin (Dims.exampleGrow.W N),
            ‖permutationFourierSum (Dims.exampleGrow.W N)
              (fun j => semicircleFlowKernel u
                (semicircleLambda (Dims.exampleGrow.W N)
                  (by have h := Dims.exampleGrow.W_pos N; omega)
                  j.val j.isLt))
              (permutationFourierCharacter (Dims.exampleGrow.W N) (b - a)) π -
              (if a = b then Complex.I else 0)‖ <
                flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
  filter_upwards [permutationFourierExampleGrow_eventually_uniform,
    PermutationFourierExampleGrowFlowMargin.eventual_margin,
    PermutationFourierExampleGrowZeroFlowMargin.eventual_zero_mode_lt_flowDelta]
    with N huniform hoffMargin hdiagMargin
  obtain ⟨π, hπ⟩ := huniform
  refine ⟨π, ?_⟩
  intro u hu0 hu1 a b
  let W := Dims.exampleGrow.W N
  have hW : 1 ≤ W := Dims.exampleGrow.W_pos N
  letI : NeZero W := ⟨by omega⟩
  by_cases hab : a = b
  · subst b
    have hzero : (a - a : Fin W) = (⟨0, by omega⟩ : Fin W) := by
      change a - a = (0 : Fin W)
      exact sub_self a
    rw [if_pos rfl, hzero, permutationFourierCharacter_zero_eq_one W hW]
    exact (permutationFourierSemicircleZeroMode_bound W hW u hu0 hu1 π).trans_lt
      hdiagMargin
  · have hnonzero : (b - a : Fin W) ≠ (⟨0, by omega⟩ : Fin W) := by
      change b - a ≠ (0 : Fin W)
      exact (sub_ne_zero).2 (Ne.symm hab)
    rw [if_neg hab, sub_zero]
    exact (hπ u hu0 hu1 (b - a) hnonzero).trans hoffMargin

/-- The same eventual set can be taken with actual width at least two, so the
all-index assertion has nonempty distinct indices and a nonzero Fourier mode. -/
theorem permutationFourierExampleGrow_eventually_entry_margin_nonempty :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ Dims.exampleGrow.W N ∧
        ∃ π : PermΩ (Dims.exampleGrow.W N),
          ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
            ∀ a b : Fin (Dims.exampleGrow.W N),
              ‖permutationFourierSum (Dims.exampleGrow.W N)
                (fun j => semicircleFlowKernel u
                  (semicircleLambda (Dims.exampleGrow.W N)
                    (by have h := Dims.exampleGrow.W_pos N; omega)
                    j.val j.isLt))
                (permutationFourierCharacter (Dims.exampleGrow.W N) (b - a)) π -
                (if a = b then Complex.I else 0)‖ <
                  flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
  filter_upwards [permutationFourierExampleGrow_eventually_entry_margin,
    permutationFourierExampleGrow_eventually_exponent_and_premise]
    with N hmargin hnd
  exact ⟨hnd.2.1, hmargin⟩

#print axioms permutationFourierExampleGrow_eventually_entry_margin
#print axioms permutationFourierExampleGrow_eventually_entry_margin_nonempty

end RBM.Gauss
