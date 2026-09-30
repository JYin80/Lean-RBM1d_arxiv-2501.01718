/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridGoodEvent
import RBM1D.Flow.EnergyUniformReg

/-!
# The Azuma constant of the grid good event at an `N`-dependent energy

`RBM.Gauss.Grid.azumaMm_leN`: `azumaMm ≤ N^{δ/8}` eventually, for `τ₁ ≤ δ/32`, at an
`N`-dependent energy `E : ℕ → ℝ`.

## The external `κ`

`azumaMm` involves `(mE (E N)).im`, inside `Step2FarInputs.eventually_xiK_le` and
`qvSumConst (E N) = 1200/(mE (E N)).im`, which must be bounded before the `∀ᶠ N`. The theorem
uses the uniform `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N` (`κ' := min κ 1`, `mE_im_ge`).
`Step2.xiK L W m` is antitone in `m > 0` (its only `m`-dependent term is `(m²)⁻¹`,
`Hierarchy/Step2.lean`), so `xiK … (mE (E N)).im ≤ xiK … mκ`; there is no named `xiK`-antitone
lemma, so the two-line argument is proved inline. `eventually_xiK_le (band d) mκ`
(`Step2FarInputs.lean`, `E`-free) is then applied, and `qvSumConst (E N) ≤ Cq := 1200/mκ` follows
the same way. Constant: `8·1200/mκ + 13`.
-/

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

/-- **`Mm ≤ N^{δ/8}` eventually**, for `0 ≤ τ₁ ≤ δ/32`, uniformly in `N` via the κ-bound
`mκ ≤ (mE (E N)).im`. -/
theorem azumaMm_leN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {δ τ₁ : ℝ} (hδ0 : 0 < δ) (hτ₁δ : τ₁ ≤ δ / 32) :
    ∀ᶠ N : ℕ in atTop, azumaMm d (E N) δ τ₁ N ≤ (N : ℝ) ^ (δ / 8) := by
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκpos : 0 < mκ := by positivity
  have hmge : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  set Cq : ℝ := 1200 / mκ with hCqdef
  have hCq0 : 0 < Cq := by positivity
  have hxiAnti : ∀ N, Step2.xiK (d.L N) (d.W N) (mE (E N)).im ≤
      Step2.xiK (d.L N) (d.W N) mκ := by
    intro N
    have hle : mκ ^ 2 ≤ (mE (E N)).im ^ 2 := by nlinarith [hmge N, hmκpos.le]
    have hinv : ((mE (E N)).im ^ 2)⁻¹ ≤ (mκ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hle
    unfold Step2.xiK
    linarith
  have hqvConst_le : ∀ N, qvSumConst (E N) ≤ Cq := by
    intro N
    unfold qvSumConst
    exact div_le_div_of_nonneg_left (by norm_num) hmκpos (hmge N)
  filter_upwards [Step2FarInputs.eventually_xiK_le (band d) mκ
      (by positivity : (0 : ℝ) < δ / 128),
    eventually_le_rpow (8 * Cq + 13) (by positivity : (0 : ℝ) < δ / 16),
    eventually_ge_atTop 1] with N hxiκ hCκ hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hq0 : 0 < qvSumConst (E N) := by
    have hm0 := mE_im_pos (show |E N| < 2 by linarith [hE N])
    unfold qvSumConst; positivity
  set ξ := Step2.xiK (d.L N) (d.W N) (mE (E N)).im with hξ
  have hξ0 : 0 ≤ ξ := Step2.xiK_nonneg _ _ _
  have hξ' : ξ ≤ (N : ℝ) ^ (δ / 128) := (hxiAnti N).trans hxiκ
  have hC : (8 * qvSumConst (E N) + 13) ≤ (N : ℝ) ^ (δ / 16) := by
    have := hqvConst_le N
    linarith [hCκ]
  have hξ2 : ξ ^ 2 ≤ (N : ℝ) ^ (δ / 64) := by
    calc ξ ^ 2 ≤ ((N : ℝ) ^ (δ / 128)) ^ 2 := pow_le_pow_left₀ hξ0 hξ' 2
      _ = (N : ℝ) ^ (δ / 64) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hP : (N : ℝ) ^ (τ₁ + δ / 64) ≤ (N : ℝ) ^ (3 * δ / 64) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hA1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 64) := Real.one_le_rpow hN1' (by positivity)
  have hA3 : (1 : ℝ) ≤ (N : ℝ) ^ (3 * δ / 64) := Real.one_le_rpow hN1' (by positivity)
  have hmul : (N : ℝ) ^ (δ / 64) * (N : ℝ) ^ (3 * δ / 64) = (N : ℝ) ^ (δ / 16) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hB1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 16) := Real.one_le_rpow hN1' (by positivity)
  have hQ : 4 * ξ ^ 2 * (2 * qvSumConst (E N) * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5
      ≤ (N : ℝ) ^ (δ / 8) := by
    have h1 : 4 * ξ ^ 2 * (2 * qvSumConst (E N) * (N : ℝ) ^ (τ₁ + δ / 64) + 2)
        ≤ 4 * (N : ℝ) ^ (δ / 64) * (2 * qvSumConst (E N) * (N : ℝ) ^ (3 * δ / 64)
          + 2 * (N : ℝ) ^ (3 * δ / 64)) := by
      have hPp : 0 ≤ (N : ℝ) ^ (τ₁ + δ / 64) := Real.rpow_nonneg hN0.le _
      gcongr
      · nlinarith [hq0]
    have h2 : 4 * (N : ℝ) ^ (δ / 64) * (2 * qvSumConst (E N) * (N : ℝ) ^ (3 * δ / 64)
          + 2 * (N : ℝ) ^ (3 * δ / 64)) = (8 * qvSumConst (E N) + 8) * (N : ℝ) ^ (δ / 16) := by
      rw [← hmul]; ring
    have h3 : (8 * qvSumConst (E N) + 13) * (N : ℝ) ^ (δ / 16) ≤ (N : ℝ) ^ (δ / 16) *
        (N : ℝ) ^ (δ / 16) := mul_le_mul_of_nonneg_right hC (by positivity)
    have h4 : (N : ℝ) ^ (δ / 16) * (N : ℝ) ^ (δ / 16) = (N : ℝ) ^ (δ / 8) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    nlinarith
  unfold azumaMm
  rw [← hξ]
  have hsq : Real.sqrt (4 * ξ ^ 2 * (2 * qvSumConst (E N) * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5)
      ≤ (N : ℝ) ^ (δ / 16) := by
    rw [Real.sqrt_le_left (by positivity)]
    calc _ ≤ (N : ℝ) ^ (δ / 8) := hQ
      _ = ((N : ℝ) ^ (δ / 16)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  calc (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ξ ^ 2 *
        (2 * qvSumConst (E N) * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5)
      ≤ (N : ℝ) ^ (δ / 16) * (N : ℝ) ^ (δ / 16) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (N : ℝ) ^ (δ / 8) := by rw [← Real.rpow_add hN0]; congr 1; ring

section Compat

end Compat

end RBM.Gauss.Grid
