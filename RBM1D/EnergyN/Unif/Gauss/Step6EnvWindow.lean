/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6EnvWindow
import RBM1D.EnergyN.Unif.Flow.Iteration

/-!
# The `∃ C after E` reorder of `exists_norm_Kval_le_envFloor`

This file adds `exists_norm_Kval_le_envFloor_unif`, the reordered form
`∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - κ → …` of `RBM.exists_norm_Kval_le_envFloor`.

The three witnesses `C1, C2, C3` (loop lengths `1, 2, 3`) are already explicit in `κ` alone,
via the reorder `RBM.Band.norm_Kval_le_unif` (`EnergyN/Unif/Flow/Iteration.lean`): the same
`max C1 (max C2 C3)` construction as in `RBM.exists_norm_Kval_le_envFloor`, now obtained once
before `E`.
-/

namespace RBM

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`K` at loop lengths `1, 2, 3` is bounded by `C R_N^3` on the window, with one constant,
uniformly in the energy.** The reorder `∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - κ → …` of
`RBM.exists_norm_Kval_le_envFloor`, via `RBM.Band.norm_Kval_le_unif`. -/
theorem exists_norm_Kval_le_envFloor_unif (B : Band Ω) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ (N : ℕ) (v : TimeIcc s t N) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
        ‖B.Kval E N (v : ℝ) J‖ ≤ C * envFloor E t N ^ 3 := by
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le_unif hκ0 hκ1 (n := 1) le_rfl
  obtain ⟨C2, hC20, hC2⟩ := B.norm_Kval_le_unif hκ0 hκ1 (n := 2) (by norm_num)
  obtain ⟨C3, hC30, hC3⟩ := B.norm_Kval_le_unif hκ0 hκ1 (n := 3) (by norm_num)
  refine ⟨max C1 (max C2 C3), le_max_of_le_left hC10, fun E hEκ N v J hJ hn h3 => ?_⟩
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  have hv0 : 0 ≤ (v : ℝ) := (hs0 N).trans v.2.1
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
  have hmono : etaT E (t N) ≤ etaT E (v : ℝ) := etaT_le_of_le_window hE v.2.2
  -- `η_v ≤ W ℓ_v η_v` because `W ≥ 1` and `ℓ_v ≥ 1`
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hell : (1 : ℝ) ≤ B.ell N (v : ℝ) := one_le_ellHat (B.L N) (B.three_le_L N) hv0 hv1
  have hηv : 0 < etaT E (v : ℝ) := etaT_pos hE hv1
  have hWl : (1 : ℝ) ≤ (B.W N : ℝ) * B.ell N (v : ℝ) := by nlinarith
  have hscale : etaT E (v : ℝ) ≤ B.scale E N (v : ℝ) := by
    show etaT E (v : ℝ) ≤ (B.W N : ℝ) * B.ell N (v : ℝ) * etaT E (v : ℝ)
    calc etaT E (v : ℝ) = 1 * etaT E (v : ℝ) := (one_mul _).symm
      _ ≤ ((B.W N : ℝ) * B.ell N (v : ℝ)) * etaT E (v : ℝ) :=
          mul_le_mul_of_nonneg_right hWl hηv.le
  have hscale0 : 0 < B.scale E N (v : ℝ) := lt_of_lt_of_le hηv hscale
  have hinv : (B.scale E N (v : ℝ))⁻¹ ≤ envFloor E t N :=
    le_trans (le_trans (inv_anti₀ hηv hscale) (inv_anti₀ hηt hmono))
      (le_max_right _ _)
  have hinv0 : (0 : ℝ) ≤ (B.scale E N (v : ℝ))⁻¹ := inv_nonneg.2 hscale0.le
  have hpow : ∀ n : ℕ, n ≤ 3 → (B.scale E N (v : ℝ))⁻¹ ^ n ≤ envFloor E t N ^ 3 := by
    intro n hn3
    exact (pow_le_pow_left₀ hinv0 hinv n).trans
      (pow_le_pow_right₀ (one_le_envFloor E t N) hn3)
  have hCmax : ∀ (c : ℝ) (n : ℕ), 0 ≤ c → c ≤ max C1 (max C2 C3) → n ≤ 4 →
      ‖B.Kval E N (v : ℝ) J‖ ≤ c * (B.scale E N (v : ℝ))⁻¹ ^ (n - 1) →
      ‖B.Kval E N (v : ℝ) J‖ ≤ max C1 (max C2 C3) * envFloor E t N ^ 3 := by
    intro c n hc0 hcle hn4 hb
    refine hb.trans ?_
    have h1 : c * (B.scale E N (v : ℝ))⁻¹ ^ (n - 1) ≤ c * envFloor E t N ^ 3 :=
      mul_le_mul_of_nonneg_left (hpow _ (by omega)) hc0
    exact h1.trans (mul_le_mul_of_nonneg_right hcle (pow_nonneg (envFloor_nonneg E t N) 3))
  have hcases : J.length = 1 ∨ J.length = 2 ∨ J.length = 3 := by omega
  rcases hcases with h | h | h
  · exact hCmax C1 1 hC10 (le_max_left _ _) (by norm_num) (hC1 E hEκ N (v : ℝ) hv0 hv1 J hJ h)
  · exact hCmax C2 2 hC20 (le_max_of_le_right (le_max_left _ _)) (by norm_num)
      (hC2 E hEκ N (v : ℝ) hv0 hv1 J hJ h)
  · exact hCmax C3 3 hC30 (le_max_of_le_right (le_max_right _ _)) (by norm_num)
      (hC3 E hEκ N (v : ℝ) hv0 hv1 J hJ h)

end RBM
