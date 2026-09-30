/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step3
import RBM1D.EnergyN.Unif.Flow.Iteration

/-!
# The `∃ C after E` reorder for the constant producer of `Hierarchy/Step3.lean`

`RBM.Step3.exists_norm_Kval_le_unif`: for `|E| ≤ 2 - κ`, the kernel bound
`‖K_u‖ ≤ C · scale_u⁻¹ ^ (n - 1)` for loops of length `n` at every time `u ∈ [s, t]`, with `C`
chosen before `E`. The witness `C` is the `C` returned by `Band.norm_Kval_le_unif`
(`RBM1D/EnergyN/Unif/Flow/Iteration.lean`).
-/

namespace RBM

namespace Step3

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

section FlowFamilies

variable {s t : ℕ → ℝ}

/-- **The loop-kernel bound on `[s, t]`, with the constant chosen before `E`.** Pass-through via
`Band.norm_Kval_le_unif`. -/
theorem exists_norm_Kval_le_unif {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) n),
      ‖B.Kval E N u v.idx‖ ≤ C * (B.scale E N u)⁻¹ ^ (n - 1) := by
  obtain ⟨C, hC0, hC⟩ := B.norm_Kval_le_unif hκ0 hκ1 hn
  refine ⟨C, hC0, fun E hEκ N u v => ?_⟩
  exact hC E hEκ N u ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N)) v.idx v.idx_wf (by simp)

end FlowFamilies

end Step3

section Compat

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {s t : ℕ → ℝ}

end Compat

end RBM
