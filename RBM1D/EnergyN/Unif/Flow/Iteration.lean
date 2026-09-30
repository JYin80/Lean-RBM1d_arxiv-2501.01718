/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Iteration
import RBM1D.EnergyN.Unif.Loop.KBound

/-!
# The `∃ C after E` reorder for the constant producers of `Flow/Iteration.lean`

All three witnesses are already explicit in `k` (and `n`) alone, once the dependency
`norm_Kgen_le` is replaced by its reorder `norm_Kgen_le_unif`
(`RBM1D/EnergyN/Unif/Loop/KBound.lean`): `norm_Kval_le_of_ne_two`'s witness is `1` or
`max C 1` with `C` from `norm_Kgen_le`; `norm_Kval_two_le`'s witness is
`2 * cTwo52 / √k + 1 + 8 * exp 1`, already `k`-only; `norm_Kval_le` only case-splits on the fixed
`n`. No new mathematics.
-/

namespace RBM

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- **`norm_Kval_le_of_ne_two`, reordered.** Pass-through via `norm_Kgen_le_unif`; no
extra κ-bound needed. -/
theorem norm_Kval_le_of_ne_two_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {n : ℕ}
    (hn : n = 1 ∨ 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ N (t : ℝ), 0 ≤ t → t < 1 → ∀ I : LoopIdx (ZMod (B.L N)), I.WF →
      I.length = n → ‖B.Kval E N t I‖ ≤ C * (B.scale E N t)⁻¹ ^ (n - 1) := by
  rcases hn with rfl | hn
  · refine ⟨1, zero_le_one, fun E hEk N t _ _ I hI hlen => ?_⟩
    have hE2 : |E| ≤ 2 := by linarith
    obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := hlen
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    rw [Kval, Kgen_one, norm_mSigma hE2, pow_zero, mul_one]
  · obtain ⟨C, hC0, hC⟩ := norm_Kgen_le_unif hk0 hk1 n
    refine ⟨max C 1, le_max_of_le_right zero_le_one, fun E hEk N t ht0 ht1 I hI hlen => ?_⟩
    have hE2 : |E| ≤ 2 := by linarith
    have hE : |E| < 2 := by linarith
    have hY0 : 0 ≤ (B.scale E N t)⁻¹ := inv_nonneg.2 (B.scale_nonneg E N ht1.le)
    have hYp : 0 ≤ (B.scale E N t)⁻¹ ^ (n - 1) := pow_nonneg hY0 _
    rcases ht0.lt_or_eq with ht0' | rfl
    · have h := hC E hEk (B.L N) (B.three_le_L N) (B.W N) t ht0' ht1 I hI (by omega) (by omega)
      have hs : (B.W N : ℝ) * (etaT E t * ellHat (B.L N) (t : ℂ)) = B.scale E N t := by
        rw [scale, ell]; ring
      rw [hs, hlen] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hYp)
    · have h0 : B.Kval E N 0 I = primInit (B.L N) (B.W N) (mSigma E) I := by
        rw [Kval, ← gloop_zero_zt_zero_eq_Kgen hE2 I hI (by omega)]
        exact gloop_zero_zt_zero hE2 I hI (by omega)
      have hpos : 0 < B.scale E N 0 :=
        flowScale_pos (by linarith [B.one_le_W N]) (B.one_le_L N) hE zero_lt_one
      have hWinv : (B.W N : ℝ)⁻¹ ≤ (B.scale E N 0)⁻¹ := inv_anti₀ hpos (B.scale_zero_le E hE2 N)
      rw [h0]
      refine (norm_primInit_le hE2 I).trans ?_
      rw [hlen]
      calc ((B.W N : ℝ)⁻¹) ^ (n - 1) ≤ (B.scale E N 0)⁻¹ ^ (n - 1) :=
            pow_le_pow_left₀ (inv_nonneg.2 (Nat.cast_nonneg _)) hWinv _
        _ = 1 * (B.scale E N 0)⁻¹ ^ (n - 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hYp

/-- **`norm_Kval_two_le`, reordered.** The witness `Bk + 8 exp 1` is already `k`-only. -/
theorem norm_Kval_two_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ N (t : ℝ), 0 ≤ t → t < 1 → ∀ I : LoopIdx (ZMod (B.L N)), I.WF →
      I.length = 2 → ‖B.Kval E N t I‖ ≤ C * (B.scale E N t)⁻¹ ^ (2 - 1) := by
  set Bk := 2 * cTwo52 / Real.sqrt k + 1
  have hBk : 1 ≤ Bk := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / Real.sqrt k := by
      have := Real.sqrt_nonneg k; positivity
    simp only [Bk]; linarith
  have he : 0 ≤ 8 * Real.exp 1 := by positivity
  refine ⟨Bk + 8 * Real.exp 1, by linarith, fun E hEk N t ht0 ht1 I hI hlen => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 2 := hlen
  have hσ : σ.length = 2 := hI.trans ha
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  have hL := B.three_le_L N
  have hW1 := B.one_le_W N
  have hs : (B.W N : ℝ) * (etaT E t * ellHat (B.L N) (t : ℂ)) = B.scale E N t := by
    rw [scale, ell]; ring
  have hη : 0 < etaT E t := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ellHat (B.L N) (t : ℂ) := by
    rw [ellHat_ofReal _ ht1]
    refine le_min ?_ (by exact_mod_cast (show 1 ≤ B.L N by omega))
    rw [le_div_iff₀ (Real.sqrt_pos.2 (by linarith)), one_mul]
    exact Real.sqrt_le_one.2 (by linarith)
  have hηℓ : etaT E t * ellHat (B.L N) (t : ℂ) ≤ 1 := by
    rcases ht0.lt_or_eq with ht0' | rfl
    · exact etaT_mul_ellHat_le hL hE2 ht0'.le ht1
    · have h1 : ellHat (B.L N) ((0 : ℝ) : ℂ) = 1 := by
        rw [ellHat_ofReal _ zero_lt_one, sub_zero, Real.sqrt_one, div_one]
        exact min_eq_left (by exact_mod_cast (show 1 ≤ B.L N by omega))
      rw [h1, mul_one, etaT, sub_zero, one_mul]
      exact mE_im_le_one hE
  have hpos : 0 < B.scale E N t := by rw [← hs]; positivity
  have hWinv : (B.W N : ℝ)⁻¹ ≤ (B.scale E N t)⁻¹ := by
    refine inv_anti₀ hpos ?_
    rw [← hs]; nlinarith
  have hS0 : 0 ≤ (B.scale E N t)⁻¹ := inv_nonneg.2 hpos.le
  rw [Kval, Kgen_two, kTwo, pow_one]
  have hm : ‖mSigma E s₁ * mSigma E s₂‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, one_mul]
  rw [norm_mul, norm_mul, hm, mul_one, norm_inv, Complex.norm_natCast]
  by_cases hss : s₁ = s₂
  · subst hss
    have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0 ht1 s₁ x y
    have h' : ‖Theta (B.L N) ((t : ℂ) * (mSigma E s₁ * mSigma E s₁)) x y‖ ≤ Bk :=
      h.trans (mul_le_of_le_one_right (by linarith) (by
        rw [Real.exp_le_one_iff, neg_nonpos]; have := cZero_pos; positivity))
    calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) ((t : ℂ) * (mSigma E s₁ * mSigma E s₁)) x y‖
        ≤ (B.scale E N t)⁻¹ * Bk := mul_le_mul hWinv h' (norm_nonneg _) hS0
      _ ≤ (Bk + 8 * Real.exp 1) * (B.scale E N t)⁻¹ := by nlinarith
  · rw [mSigma_mul_of_ne hE2 hss, mul_one]
    rcases ht0.lt_or_eq with ht0' | rfl
    · have h := norm_Theta_long_edge_le (B.L N) hL hk0 (by linarith) hEk ht0' ht1 x y
      rw [← etaT_eq_zt_im] at h
      calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) (t : ℂ) x y‖
          ≤ (B.W N : ℝ)⁻¹ * (8 * Real.exp 1 / (etaT E t * ellHat (B.L N) (t : ℂ))) := by
            gcongr
        _ = 8 * Real.exp 1 * (B.scale E N t)⁻¹ := by
            rw [← hs]; field_simp
        _ ≤ (Bk + 8 * Real.exp 1) * (B.scale E N t)⁻¹ := by nlinarith
    · have h1 : ‖Theta (B.L N) ((0 : ℝ) : ℂ) x y‖ ≤ 1 := by
        rw [Complex.ofReal_zero, Theta_zero, Matrix.one_apply]
        split_ifs <;> simp
      calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) ((0 : ℝ) : ℂ) x y‖ ≤ (B.scale E N 0)⁻¹ * 1 :=
            mul_le_mul hWinv h1 (norm_nonneg _) hS0
        _ ≤ (Bk + 8 * Real.exp 1) * (B.scale E N 0)⁻¹ := by nlinarith

/-- **`norm_Kval_le`, reordered.** `n` stays fixed before `∃ C` (only `E` moves); the case split
on `n = 2` calls the two reordered lemmas above. -/
theorem norm_Kval_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ N (t : ℝ), 0 ≤ t → t < 1 → ∀ I : LoopIdx (ZMod (B.L N)), I.WF →
      I.length = n → ‖B.Kval E N t I‖ ≤ C * (B.scale E N t)⁻¹ ^ (n - 1) := by
  by_cases h2 : n = 2
  · subst h2; exact B.norm_Kval_two_le_unif hk0 hk1
  · exact B.norm_Kval_le_of_ne_two_unif hk0 hk1 (by omega)

end Band

section Compat

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

end Compat

end RBM
