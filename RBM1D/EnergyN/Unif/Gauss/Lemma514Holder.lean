/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.EnergyN.Unif.Flow.Iteration

/-!
# The `∃ C after E` reorder for the constant producer of `Gauss/Lemma514Holder.lean`

`exists_norm_Kval_le_upto` derives its own spectral gap `k := min 1 (2 - |E|)` via
`exists_gap_of_abs_lt_two hE` and feeds it into `Band.norm_Kval_le`, so its witness depends on
`E` through that gap. The gap cannot be chosen before `E`: `∃ k, ∀ E, |E| < 2 → |E| ≤ 2 - k` is
false (as `E → 2⁻` no single `k > 0` works).

With `k` as a hypothesis (the shape `∃ C, ∀ E, |E| ≤ 2 - k → …`), no gap has to be produced:
`exists_norm_Kval_le_upto_unif` takes `k` and calls `Band.norm_Kval_le_unif` at that `k`, with
the same induction on the loop length `m` as `exists_norm_Kval_le_upto`.
-/

namespace RBM.Gauss

variable {Ωb : Type*} [MeasurableSpace Ωb]

/-- **`exists_norm_Kval_le_upto`, reordered, with `k` taken externally** (bypassing the internal
`exists_gap_of_abs_lt_two` derivation; see the module docstring). -/
theorem exists_norm_Kval_le_upto_unif (B : Band Ωb) {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (N : ℕ) (w : ℝ), 0 ≤ w → w < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ m →
        ‖B.Kval E N w J‖ ≤ C * (B.scale E N w)⁻¹ ^ (J.length - 1) := by
  induction m with
  | zero => exact ⟨0, le_rfl, fun E _ N w _ _ J hJ h2 hle => absurd hle (by omega)⟩
  | succ m ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      obtain ⟨C', hC'0, hC'⟩ := B.norm_Kval_le_unif hk0 hk1 (n := m + 1) (by omega)
      refine ⟨max C C', le_max_of_le_left hC0, fun E hEk N w hw0 hw1 J hJ h2 hle => ?_⟩
      have hE : |E| < 2 := by linarith
      have hs0 : (0 : ℝ) ≤ (B.scale E N w)⁻¹ :=
        inv_nonneg.2 (B.scale_pos' hE N hw0 hw1).le
      rcases le_or_gt J.length m with h | h
      · exact (hC E hEk N w hw0 hw1 J hJ h2 h).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hs0 _))
      · have hlen : J.length = m + 1 := by omega
        have h' := hC' E hEk N w hw0 hw1 J hJ hlen
        rw [hlen]
        exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hs0 _))

end RBM.Gauss

section Compat

open RBM RBM.Gauss

end Compat
