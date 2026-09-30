/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514NonAlt
import RBM1D.EnergyN.Unif.Gauss.Lemma510Fixed

/-!
# The `∃ C after E` reorder for the constant producer of `Gauss/Lemma514NonAlt.lean`
-/

namespace RBM.Gauss.Grid

variable (d : Dims)

/-- **The kernel envelope with the constant chosen before `E`**: for `|E| ≤ 2 - κ` and
`1 ≤ scale`, the bound of `exists_uniform_Kval_bound_unif` for loop lengths `2 ≤ |J| ≤ n`, and
`‖K_J‖ ≤ CK + 1` for `|J| ≤ n`. Pass-through via `exists_uniform_Kval_bound_unif`. -/
theorem exists_Kval_env_unif {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ (N : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 1 ≤ (band d).scale E N v →
      (∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖(band d).Kval E N v J‖ ≤ CK * ((band d).scale E N v)⁻¹ ^ (J.length - 1))
      ∧ ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ n → ‖(band d).Kval E N v J‖ ≤ CK + 1 := by
  obtain ⟨CK, hCK0, hCK⟩ := exists_uniform_Kval_bound_unif d hκ0 hκ1 n hn
  refine ⟨CK, hCK0, fun E hEκ N v hv0 hv1 hA1 =>
    ⟨fun J hJ h2 hln => hCK E hEκ N v hv0 hv1 J hJ h2 hln, ?_⟩⟩
  have hE : |E| < 2 := by linarith
  intro J hJ hln
  by_cases h2 : 2 ≤ J.length
  · have h := hCK E hEκ N v hv0 hv1 J hJ h2 hln
    have hAi : ((band d).scale E N v)⁻¹ ^ (J.length - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hA1)
    have : CK * ((band d).scale E N v)⁻¹ ^ (J.length - 1) ≤ CK * 1 :=
      mul_le_mul_of_nonneg_left hAi hCK0
    linarith
  · have hK : (band d).Kval E N v J = Kgen (d.L N) (d.W N) (mSigma E) v J := rfl
    rw [hK]
    by_cases h1 : J.length = 1
    · have : ‖Kgen (d.L N) (d.W N) (mSigma E) v J‖ = 1 := by
        simp [Kgen, h1, norm_mSigma hE.le]
      linarith
    · have h0 : J.length = 0 := by omega
      have : Kgen (d.L N) (d.W N) (mSigma E) v J = 0 := by
        simp [Kgen, h0]
      rw [this, norm_zero]
      linarith

end RBM.Gauss.Grid

section Compat

open RBM RBM.Gauss RBM.Gauss.Grid

end Compat
