/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma510Fixed
import RBM1D.EnergyN.Unif.Flow.Iteration

/-!
# The `∃ C after E` reorder for the constant producer of `Gauss/Lemma510Fixed.lean`

`exists_uniform_Kval_bound_unif`: one constant `CK`, depending only on `k` and `n`, bounds
`‖K_J‖` by `CK` times `scale⁻¹ ^ (|J| - 1)` for every loop of length `2 ≤ |J| ≤ n` and every energy
with `|E| ≤ 2 - k`. The witness `CK` is `(Finset.Icc 2 n).sup' _ C`, where `C m` is chosen
(`choose!`) from `Band.norm_Kval_le_unif` (`RBM1D/EnergyN/Unif/Flow/Iteration.lean`) for each
length `m`. The `sup'` ranges over `m ∈ Finset.Icc 2 n`, not over `E`, so it depends on `k` only.
-/

namespace RBM.Gauss.Grid

variable (d : Dims)

/-- **The kernel bound for loop lengths `2 ≤ |J| ≤ n`, with the constant chosen before `E`.**
Pass-through via `Band.norm_Kval_le_unif`. -/
theorem exists_uniform_Kval_bound_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (N : ℕ) (v : ℝ), 0 ≤ v → v < 1 →
      ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖(band d).Kval E N v J‖ ≤ CK * ((band d).scale E N v)⁻¹ ^ (J.length - 1) := by
  classical
  have hex : ∀ m ∈ Finset.Icc 2 n, ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (N : ℕ) (v : ℝ), 0 ≤ v → v < 1 →
      ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length = m →
        ‖(band d).Kval E N v J‖ ≤ C * ((band d).scale E N v)⁻¹ ^ (m - 1) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact (band d).norm_Kval_le_unif hk0 hk1 (n := m) (by omega)
  choose! C hC0 hC using hex
  refine ⟨(Finset.Icc 2 n).sup' (Finset.nonempty_Icc.2 hn) C, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Finset.nonempty_Icc.2 hn
    exact le_trans (hC0 m hm) (Finset.le_sup' C hm)
  · intro E hEk N v hv0 hv1 J hJ hJ2 hJn
    have hmem : J.length ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨hJ2, hJn⟩
    have hb := hC J.length hmem E hEk N v hv0 hv1 J hJ rfl
    have hAnn : (0 : ℝ) ≤ ((band d).scale E N v)⁻¹ ^ (J.length - 1) := by
      have := (band d).scale_nonneg E N hv1.le
      positivity
    exact hb.trans (mul_le_mul_of_nonneg_right (Finset.le_sup' C hmem) hAnn)

end RBM.Gauss.Grid

section Compat

open RBM RBM.Gauss RBM.Gauss.Grid

end Compat
