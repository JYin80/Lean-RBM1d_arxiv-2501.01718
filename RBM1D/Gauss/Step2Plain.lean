/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Close

/-!
# Step 2 under the plain (2.72) with the `−3/7` exponent in (5.35)

## Main results

* `drift_point_le_heG'`: the drift bound at a point, with conclusion exponent `−3/7`.
* `driftCoef'`, `phiG'`, `drift_sum_le'`, `grid_step_bound_core'`, `grid_step_bound'`: the
  grid step bound chain at the `−3/7` exponent.
* `QVSum.J_pow_le_plain`, `QVSum.Qd_mul_le_plain`: the quadratic-variation time sum under the
  **plain** (2.72) `(η_s/η_t)^{30} ≤ scale(t)` and `N^c ≤ scale(t)`, with `90 δ ≤ c` (no `N^c`
  gain in any hypothesis).
* `heG_coef_eq_driftCoef'`, `drift_of_goodSet'`: the good-set drift bound in `driftCoef'`
  shape.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Real Finset RBM RBM.Step2FarInputs

/-! ### Scalar facts for the `−3/7` exponent -/

/-- `A^{-1/2} ≤ A^{-3/7}` for `A ≥ 1`. -/
theorem inv_sqrt_le_rpow_three_sevenths {A : ℝ} (hA : 1 ≤ A) :
    (√A)⁻¹ ≤ A⁻¹ ^ ((3 : ℝ) / 7) := by
  have hA0 : 0 < A := by linarith
  have h1 : (0 : ℝ) < A⁻¹ := by positivity
  have h2 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have := Real.rpow_le_rpow_of_exponent_ge h1 h2 (by norm_num : (3 : ℝ) / 7 ≤ 1 / 2)
  rwa [show A⁻¹ ^ ((1 : ℝ) / 2) = (√A)⁻¹ by rw [← Real.sqrt_eq_rpow, Real.sqrt_inv]] at this

/-- `A^{-1} ≤ A^{-3/7}` for `A ≥ 1`. -/
theorem inv_le_rpow_three_sevenths {A : ℝ} (hA : 1 ≤ A) : A⁻¹ ≤ A⁻¹ ^ ((3 : ℝ) / 7) := by
  have hA0 : 0 < A := by linarith
  have h1 : (0 : ℝ) < A⁻¹ := by positivity
  have h2 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have := Real.rpow_le_rpow_of_exponent_ge h1 h2 (by norm_num : (3 : ℝ) / 7 ≤ 1)
  rwa [Real.rpow_one] at this

section T1

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

namespace DriftPt

/-- **(T1), scalar core**: the (5.35) coefficient bound at the exponent `A^{-3/7}`
(`(√A)⁻¹ ≤ A^{-3/7}`, `A⁻¹ ≤ A^{-3/7}` for `A ≥ 1`). -/
theorem heG_coef_le' {η A cNw cFw cN cF g r r0 R x y Λ res : ℝ}
    (hη : 0 < η) (hA : 1 ≤ A) (hcNw0 : 0 ≤ cNw) (hcNw : cNw ≤ cN) (hcFw0 : 0 ≤ cFw)
    (hcFw : cFw ≤ cF) (hg1 : 1 ≤ g) (hr : r = g * r0) (hr01 : 1 ≤ r0) (hr0R : r0 ^ 2 ≤ R)
    (hx1 : 1 ≤ x) (hΛ : Λ = x * R ^ 4) (hy1 : 1 ≤ y) (hyx : y ≤ x) (hres : res ≤ η⁻¹) :
    η⁻¹ * (cNw * r ^ 3 + cFw * (r * √r * (√A)⁻¹ * (y * Λ))
        + 169 * (r * A⁻¹ * ((y * Λ) * √(y * Λ)))) + res
      ≤ g ^ 2 * (cN + cF + 170) * η⁻¹ * (((g * r0) ^ 3 + 1) + A⁻¹ ^ ((3 : ℝ) / 7) * Λ ^ 3) := by
  subst hr hΛ
  have hηi : 0 < η⁻¹ := inv_pos.2 hη
  have hA0 : 0 < A := by linarith
  have hR1 : 1 ≤ R := by nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hr00 : 0 ≤ r0 := by linarith
  have hcN0 : 0 ≤ cN := hcNw0.trans hcNw
  have hcF0 : 0 ≤ cF := hcFw0.trans hcFw
  set Λ := x * R ^ 4 with hΛdef
  have hΛ1 : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le hx1 (one_le_pow₀ hR1)
  have hΛ0 : 0 ≤ Λ := by linarith
  set A' := A⁻¹ ^ ((3 : ℝ) / 7) with hA'
  have hA'0 : 0 ≤ A' := Real.rpow_nonneg (by positivity) _
  have hsA : (√A)⁻¹ ≤ A' := inv_sqrt_le_rpow_three_sevenths hA
  have hiA : A⁻¹ ≤ A' := inv_le_rpow_three_sevenths hA
  have hgr1 : 1 ≤ g * r0 := one_le_mul_of_one_le_of_one_le hg1 hr01
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  -- (2) the `c_far` piece
  have hsg : √g ≤ g := Lemma57.sqrt_le_self hg1
  have hrr : g * r0 * √(g * r0) ≤ g ^ 2 * (r0 * √r0) := by
    rw [Real.sqrt_mul hg0]
    calc g * r0 * (√g * √r0) = √g * (g * (r0 * √r0)) := by ring
      _ ≤ g * (g * (r0 * √r0)) := by
          apply mul_le_mul_of_nonneg_right hsg; positivity
      _ = g ^ 2 * (r0 * √r0) := by ring
  have hk2 : r0 * √r0 * (y * Λ) ≤ Λ ^ 3 := by
    have hl0 : 0 ≤ r0 * √r0 * (y * Λ) := by positivity
    have hr0 : 0 ≤ Λ ^ 3 := by positivity
    refine (pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero).1 ?_
    have hr3 : r0 ^ 3 ≤ R ^ 2 := by
      calc r0 ^ 3 ≤ r0 ^ 4 := pow_le_pow_right₀ hr01 (by norm_num)
        _ = (r0 ^ 2) ^ 2 := by ring
        _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hr0R 2
    have hy2 : y ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy0 hyx 2
    have hRx : R ^ 2 * x ^ 2 ≤ Λ ^ 4 := by
      rw [hΛdef]
      calc R ^ 2 * x ^ 2 ≤ R ^ 16 * x ^ 4 :=
            mul_le_mul (pow_le_pow_right₀ hR1 (by norm_num)) (pow_le_pow_right₀ hx1 (by norm_num))
              (by positivity) (by positivity)
        _ = (x * R ^ 4) ^ 4 := by ring
    calc (r0 * √r0 * (y * Λ)) ^ 2 = r0 ^ 2 * (√r0) ^ 2 * y ^ 2 * Λ ^ 2 := by ring
      _ = r0 ^ 3 * y ^ 2 * Λ ^ 2 := by rw [Real.sq_sqrt hr00]; ring
      _ ≤ R ^ 2 * x ^ 2 * Λ ^ 2 := by gcongr
      _ ≤ Λ ^ 4 * Λ ^ 2 := by gcongr
      _ = (Λ ^ 3) ^ 2 := by ring
  have hT2 : cFw * (g * r0 * √(g * r0) * (√A)⁻¹ * (y * Λ)) ≤ g ^ 2 * cF * (A' * Λ ^ 3) := by
    calc cFw * (g * r0 * √(g * r0) * (√A)⁻¹ * (y * Λ))
        = cFw * ((g * r0 * √(g * r0)) * (y * Λ) * (√A)⁻¹) := by ring
      _ ≤ cF * ((g ^ 2 * (r0 * √r0)) * (y * Λ) * A') := by gcongr
      _ = g ^ 2 * cF * ((r0 * √r0 * (y * Λ)) * A') := by ring
      _ ≤ g ^ 2 * cF * (Λ ^ 3 * A') := by gcongr
      _ = g ^ 2 * cF * (A' * Λ ^ 3) := by ring
  -- (3) the `169` piece
  have hk3 : r0 * ((y * Λ) * √(y * Λ)) ≤ Λ ^ 3 := by
    have hl0 : 0 ≤ r0 * ((y * Λ) * √(y * Λ)) := by positivity
    have hr0 : 0 ≤ Λ ^ 3 := by positivity
    refine (pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero).1 ?_
    have hy3 : y ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hy0 hyx 3
    have hRx : R * x ^ 3 ≤ Λ ^ 3 := by
      rw [hΛdef]
      calc R * x ^ 3 ≤ R ^ 12 * x ^ 3 :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ hR1 (by norm_num)) (by positivity)
        _ = (x * R ^ 4) ^ 3 := by ring
    have hyΛ : 0 ≤ y * Λ := by positivity
    calc (r0 * ((y * Λ) * √(y * Λ))) ^ 2 = r0 ^ 2 * (y * Λ) ^ 2 * (√(y * Λ)) ^ 2 := by ring
      _ = r0 ^ 2 * y ^ 3 * Λ ^ 3 := by rw [Real.sq_sqrt hyΛ]; ring
      _ ≤ R * x ^ 3 * Λ ^ 3 := by gcongr
      _ ≤ Λ ^ 3 * Λ ^ 3 := by gcongr
      _ = (Λ ^ 3) ^ 2 := by ring
  have hT3 : 169 * (g * r0 * A⁻¹ * ((y * Λ) * √(y * Λ))) ≤ g ^ 2 * 169 * (A' * Λ ^ 3) := by
    have hgg : g ≤ g ^ 2 := le_self_pow₀ hg1 two_ne_zero
    calc 169 * (g * r0 * A⁻¹ * ((y * Λ) * √(y * Λ)))
        = 169 * (g * (r0 * ((y * Λ) * √(y * Λ))) * A⁻¹) := by ring
      _ ≤ 169 * (g ^ 2 * Λ ^ 3 * A') := by gcongr
      _ = g ^ 2 * 169 * (A' * Λ ^ 3) := by ring
  -- (1) the near piece and the residue
  have hT1 : cNw * (g * r0) ^ 3 ≤ cN * ((g * r0) ^ 3 + 1) := by
    have : cNw * (g * r0) ^ 3 ≤ cN * (g * r0) ^ 3 := by gcongr
    nlinarith
  -- assemble
  have hM1 : cN + 1 ≤ g ^ 2 * (cN + cF + 170) := by nlinarith
  have hM2 : g ^ 2 * (cF + 169) ≤ g ^ 2 * (cN + cF + 170) := by nlinarith
  have hq0 : 0 ≤ (g * r0) ^ 3 + 1 := by positivity
  have hAL0 : 0 ≤ A' * Λ ^ 3 := by positivity
  have hsum : cNw * (g * r0) ^ 3 + cFw * (g * r0 * √(g * r0) * (√A)⁻¹ * (y * Λ))
        + 169 * (g * r0 * A⁻¹ * ((y * Λ) * √(y * Λ))) + 1
      ≤ g ^ 2 * (cN + cF + 170) * (((g * r0) ^ 3 + 1) + A' * Λ ^ 3) := by
    have hq1 : 1 ≤ (g * r0) ^ 3 + 1 := by
      have := pow_nonneg (by linarith : (0 : ℝ) ≤ g * r0) 3; linarith
    have e1 : cN * ((g * r0) ^ 3 + 1) + 1 ≤ (cN + 1) * ((g * r0) ^ 3 + 1) := by
      have h : (cN + 1) * ((g * r0) ^ 3 + 1) = cN * ((g * r0) ^ 3 + 1) + ((g * r0) ^ 3 + 1) := by
        ring
      linarith
    have e2 := mul_le_mul_of_nonneg_right hM1 hq0
    have e3 := mul_le_mul_of_nonneg_right hM2 hAL0
    linarith [hT1, hT2, hT3, e1, e2, e3]
  have := mul_le_mul_of_nonneg_left hsum hηi.le
  linarith [this, hres]

end DriftPt

open DriftPt in
/-- **`drift_point_le_heG'`**: the drift bound at a point, with the (5.35) coefficient
`A_u^{-3/7}`.  The exponent is derived (`heG_coef_le'`, from the unmerged
`A^{-1/2} r^{3/2} J + A^{-1} r J^{3/2}` of `drift_point_le_blk'` and `A_u ≥ 1`), not assumed. -/
theorem drift_point_le_heG' {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {δ ε ζ D : ℝ} {N : ℕ} {u : ℝ}
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsu : s N ≤ u) (hu1 : u < 1)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ) (hD : 8 + 2 * ζ ≤ D)
    (hW8 : 8 ≤ (B.W N : ℝ)) (hLW : (B.L N : ℝ) ≤ B.W N) (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hlog : 2 * D ^ 2 ≤ Real.log (B.W N : ℝ))
    (hJA : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ≤ B.scale E N u)
    (hDreg : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D)) ≤ B.ell N u * (B.scale E N u)⁻¹)
    {κ : ℝ}
    (h273 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ (B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))) ^ 2 * ((B.scale E N u) ^ 2)⁻¹)
    (h557C : ∀ (x y : ZMod (B.L N)) (p : B.Idx N), p.1 = y →
      ∑ r : B.Idx N, Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))) * (√(B.scale E N u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : B.Idx N), r.1 = x →
      ∑ p : B.Idx N, Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))) * (√(B.scale E N u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * (B.scale E N u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)))
    (hjS : jSMat B.toDims E D N u M ≤ Step2.thr E s δ N u)
    (hjG : jGMat B.toDims E N u (B.ell N u) (etaT E u) D M
      ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) :
    ∀ b : LoopArg (B.L N) 2,
      ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
            (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))‖
        ≤ (exp 1 * Step2.thr E s δ N u ^ 2 *
              (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹)
                + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D))
            + mgDrift B ζ N * (etaT E u)⁻¹ *
              (((4 * (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N))) ^ 3 + 1)
                + (B.scale E N u)⁻¹ ^ ((3 : ℝ) / 7) * Step2.thr E s δ N u ^ 3))
          * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)) := by
  intro b
  have hofn : List.ofFn b = [b 0, b 1] := by simp [List.ofFn_succ]
  rw [hofn]
  -- scalar facts
  have hW1 : (1 : ℝ) ≤ B.W N := by linarith
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hs1 : s N < 1 := lt_of_le_of_lt hsu hu1
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hη0 : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hη1 : etaT E u ≤ 1 := by
    rw [Step2.etaT_eq]
    calc (1 - u) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
      _ = 1 := one_mul 1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hℓu0 : 0 < B.ell N u := by linarith
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1
  have hℓs0 : 0 < B.ell N (s N) := by linarith
  have hℓsu : B.ell N (s N) ≤ B.ell N u := Step3.ellHat_mono hsu hu1
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN1 hζ0
  have hg1 : 1 ≤ 4 * (N : ℝ) ^ ζ := by linarith
  have hg0 : 0 < 4 * (N : ℝ) ^ ζ := by linarith
  have hℓs'0 : 0 < B.ell N (s N) / (4 * (N : ℝ) ^ ζ) := div_pos hℓs0 hg0
  have hrr : B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))
      = 4 * (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N)) := by
    field_simp
  have hr01 : 1 ≤ B.ell N u / B.ell N (s N) := by rw [le_div_iff₀ hℓs0]; linarith
  have hr : 1 ≤ B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) := by
    rw [hrr]; exact one_le_mul_of_one_le_of_one_le hg1 hr01
  -- `J := N^{2ε} Λ(u)`
  have hR1 : 1 ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith)]; linarith
  have hy1 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have hΛ1 : 1 ≤ Step2.thr E s δ N u := by
    unfold Step2.thr
    exact one_le_mul_of_one_le_of_one_le hx1 (one_le_pow₀ hR1)
  have hJ1 : 1 ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u :=
    one_le_mul_of_one_le_of_one_le hy1 hΛ1
  have hJ0 : 0 ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u := by linarith
  have hA : 1 ≤ B.scale E N u := hJ1.trans hJA
  -- the `jGMat` corollary with `J := N^{2ε} Λ(u)`
  have h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) *
            tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) := by
    intro x y hxy
    exact (two_loop_re_le_jGMat (ηu := etaT E u) (D := D) hM x y hxy).trans
      (mul_le_mul_of_nonneg_right hjG (tailT_nonneg hW0.le _))
  have h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        gmBlkM B N M (zt E u) x y ≤ √((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) *
          √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y))) := by
    intro x y hxy
    refine (gmBlkM_le_sqrt_jGMat (ηu := etaT E u) (D := D) hM x y hxy).trans ?_
    rw [← Real.sqrt_mul hJ0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hjG (tailT_nonneg hW0.le _))
  -- `h554`, deterministically, with `ρ`
  have hlogW1 : 1 ≤ Real.log (B.W N : ℝ) := by
    rw [Real.le_log_iff_exp_le hW0]
    have := Real.exp_one_lt_d9
    linarith
  have h554set := mem_h554Set_of_isHermitian (d := B.toDims) (D := D) hE N hu1 hℓu0 hlogW1
    (M := M) hM
  have h554 : ∀ x y c : ZMod (B.L N),
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (y - c) : ℝ) →
        ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤
          rho554 B.toDims E N u D (jGMat B.toDims E N u (B.ell N u) (etaT E u) D M) :=
    fun x y c h => h554set hM x y c h
  have hjG1 : 1 ≤ jGMat B.toDims E N u (B.ell N u) (etaT E u) D M := one_le_jGMat' E N u M
  have hρ0 : 0 ≤ rho554 B.toDims E N u D (jGMat B.toDims E N u (B.ell N u) (etaT E u) D M) := by
    unfold rho554
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hη0.le) (by linarith)) (Real.sqrt_nonneg _)
  have hρ : rho554 B.toDims E N u D (jGMat B.toDims E N u (B.ell N u) (etaT E u) D M) ≤
      2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) * (B.W N : ℝ) ^ (-D) :=
    (rho554_mono B.toDims E N u D hη0 hjG).trans
      (rho554_le_two_mul_rpow B.toDims E N hη0 hℓu0 hA hlog hJ0)
  -- (T3') at `ℓ_s'`
  have hmain := drift_point_le_blk' (s := s) (δ := δ) (D := D)
    (ℓs := B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) hM hL3 hW1 hℓu1 hℓs'0 hη0 hA hr hDreg hJ1 hρ0
    h273 h554 h531 h42 h557C h557R hone hκ hjS b
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (tailT_nonneg hW0.le _))
  -- the coefficient
  have hJW : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ≤ B.W N :=
    hJA.trans (scale_le_W B hE N hu0 hu1)
  have hℓL : B.ell N u ≤ (B.L N : ℝ) := min_le_right _ _
  have hrg : B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) ≤ 4 * (N : ℝ) ^ ζ * B.ell N u := by
    rw [hrr]
    exact mul_le_mul_of_nonneg_left (div_le_self hℓu0.le hℓs1) hg0.le
  have hgW : 4 * (N : ℝ) ^ ζ ≤ 4 * (B.W N : ℝ) ^ (2 * ζ) := by
    have := natCast_rpow_le_W_rpow (Nat.cast_nonneg N) hNW hζ0 hW0.le
    linarith
  have hres := resCoef_le (Lr := (B.L N : ℝ)) hW8 hℓu0 hℓs'0 hη0 hη1 hρ hJ0 hJW hℓL hLW hrg
    hgW hD
  have hr0R : (B.ell N u / B.ell N (s N)) ^ 2 ≤ etaT E (s N) / etaT E u := by
    have hK := ell_mul_sqrt_le B N hu1 hsu
    have ha : 0 < 1 - u := by linarith
    have hc : 0 < 1 - s N := by linarith
    have hsq := pow_le_pow_left₀ (by positivity) hK 2
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hc.le] at hsq
    rw [Step2.etaT_ratio hE, div_pow, div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hyx : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
  have key := heG_coef_le' (η := etaT E u) (A := (B.W N : ℝ) * B.ell N u * etaT E u)
    (cNw := Lemma57.cNear (B.W N : ℝ) (B.ell N u)) (cFw := Lemma57.cFar (B.W N : ℝ) (B.ell N u))
    (cN := Lemma57.cNear (B.W N : ℝ) 1) (cF := Lemma57.cFar (B.W N : ℝ) 1)
    (R := etaT E (s N) / etaT E u) (x := (N : ℝ) ^ δ) (y := (N : ℝ) ^ (2 * ε))
    (Λ := Step2.thr E s δ N u) hη0 hA (Lemma57.cNear_nonneg hW1 hℓu0) (cNear_le_one hℓu1)
    (Lemma57.cFar_nonneg hW1 hℓu0) (cFar_le_one hℓu1) hg1 hrr hr01 hr0R hx1 rfl hy1 hyx hres
  have hsc : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  rw [hsc]
  unfold mdr' mgDrift
  linarith [key]

end T1

/-! ### (T2) The grid step bound at the `−3/7` exponent -/

section StepBoundPrime

open RBM Finset MeasureTheory Filter Real
open scoped Matrix.Norms.L2Operator

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}
  {N : ℕ}


/-- **`driftCoef'`**: the drift coefficient with the `(5.35)` coefficient `A_u^{-3/7}`;
exactly the coefficient of `drift_point_le_heG'` (T1). -/
noncomputable def driftCoef' (B : Band Ω') (E : ℝ) (s : ℕ → ℝ) (δ D ζ Mg : ℝ) (N : ℕ)
    (u : ℝ) : ℝ :=
  exp 1 * Step2.thr E s δ N u ^ 2 *
      (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹) + (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D))
    + Mg * ((etaT E u)⁻¹ * (qGrid B s ζ N u +
        (B.scale E N u)⁻¹ ^ ((3 : ℝ) / 7) * Step2.thr E s δ N u ^ 3))

/-- **`phiG'`**: the grid right-hand side at the exponent `A_v^{-3/7}`. -/
noncomputable def phiG' (B : Band Ω') (E : ℝ) (s : ℕ → ℝ) (δ D ζ Mi Mg Mm : ℝ) (N : ℕ)
    (v : ℝ) : ℝ :=
  Mi * (etaT E (s N) / etaT E v) ^ 2 * Step2.xiK (B.L N) (B.W N) (mE E).im
  + Step2.xiK (B.L N) (B.W N) (mE E).im *
    (exp 1 * Step2.thr E s δ N v ^ 2 *
        (36 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (B.scale E N v)⁻¹
          + (etaT E (s N) / etaT E v) ^ 2 * ((B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D)))
      + Mg * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 *
        (qGrid B s ζ N v + (B.scale E N v)⁻¹ ^ ((3 : ℝ) / 7) * Step2.thr E s δ N v ^ 3))
  + Mm * ((etaT E (s N) / etaT E v) ^ 2 + 1) + 1 + 1


theorem driftCoef'_nonneg (hE : |E| < 2) {δ D ζ Mg : ℝ} (hMg : 0 ≤ Mg) {u : ℝ} (hs1 : s N < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 ≤ driftCoef' B E s δ D ζ Mg N u := by
  have hη := Step2.etaT_pos' hE hu1
  have hA := B.scale_pos' hE N hu0 hu1
  have hq := qGrid_nonneg B ζ u hs1 hu1
  have hΛ := thr_nonneg (E := E) (s := s) (N := N) δ u
  have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have hε : (0 : ℝ) ≤ (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) := by
    have := Real.rpow_nonneg hW (-D); positivity
  unfold driftCoef'
  have : 0 ≤ (B.scale E N u)⁻¹ ^ ((3 : ℝ) / 7) := Real.rpow_nonneg (inv_nonneg.2 hA.le) _
  positivity

/-- **The drift term of the grid step bound**, with `η_{u_j}⁻¹` paired with the propagator
factor: the time sum has weight `m⁻¹ R_k²` (not `R_k³`). -/
theorem drift_sum_le' (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) (hW : exp 1 ≤ (B.W N : ℝ)) {D δ ζ Mg : ℝ}
    (hMg : 0 ≤ Mg) (Dv : ℕ → LoopArg (B.L N) 2 → ℂ)
    (hdrift : ∀ j < k, ∀ b, ‖Dv j b‖ ≤ driftCoef' B E s δ D ζ Mg N (time s t K N j) *
      Step2.tT B E N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)))
    (a : LoopArg (B.L N) 2) :
    ‖(∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dv j)) a‖ ≤
      Step2.xiK (B.L N) (B.W N) (mE E).im *
        (exp 1 * Step2.thr E s δ N (time s t K N k) ^ 2 *
          (36 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (time s t K N k)) ^ 2 *
              (B.scale E N (time s t K N k))⁻¹
            + (etaT E (s N) / etaT E (time s t K N k)) ^ 2 *
              ((B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D)))
        + Mg * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (time s t K N k)) ^ 2 *
          (qGrid B s ζ N (time s t K N k) + (B.scale E N (time s t K N k))⁻¹ ^ ((3 : ℝ) / 7) *
            Step2.thr E s δ N (time s t K N k) ^ 3)) *
        Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) := by
  classical
  set u : ℕ → ℝ := fun j => time s t K N j with hudef
  set Δ := step s t K N with hΔ
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t K N hst
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  set m := (mE E).im with hm
  have hW0 : (0 : ℝ) < B.W N := lt_of_lt_of_le (exp_pos 1) hW
  have hs1 : s N < 1 := hst.trans_lt ht1
  have huk : u k ≤ t N := time_le_t s t K N hst hK1 hk
  have huk1 : u k < 1 := huk.trans_lt ht1
  have hsu : ∀ j, s N ≤ u j := fun j => s_le_time s t K N hst j
  have hu_succ : ∀ j, u j ≤ u (j + 1) := fun j => time_mono' s t K N hst (Nat.le_succ j)
  have hu0 : 0 ≤ u 0 := hs0.trans (hsu 0)
  have hkΔ : (k : ℝ) * Δ = u k - s N := by simp only [hudef, time_eq]; ring
  -- `M j`
  set M : ℕ → ℝ := fun j => max (driftCoef' B E s δ D ζ Mg N (u j)) 0 with hMdef
  have hM0 : ∀ j, 0 ≤ M j := fun j => le_max_right _ _
  have hMj : ∀ j < k, M j = driftCoef' B E s δ D ζ Mg N (u j) := by
    intro j hj
    have hj1 : u j < 1 := (time_mono' s t K N hst hj.le).trans_lt huk1
    exact max_eq_left (driftCoef'_nonneg B hE hMg hs1 (hs0.trans (hsu j)) hj1)
  have hA : ∀ j < k, ∀ b, ‖Dv j b‖ ≤
      M j * tailT (B.W N) (ellHat (B.L N) (u j : ℂ)) ((1 - u j) * m) D
        (zdist (B.L N) (b 0 - b 1)) := by
    intro j hj b
    rw [hMj j hj]; exact hdrift j hj b
  have hAuv : ∀ j < k, (B.W N : ℝ) * ellHat (B.L N) (u k : ℂ) * ((1 - u k) * m)
      ≤ (B.W N : ℝ) * ellHat (B.L N) (u (j + 1) : ℂ) * ((1 - u (j + 1)) * m) := by
    intro j hj
    exact flowScale_antitoneOn hW0.le (B.L N) E
      (Set.mem_Iic.2 ((time_mono' s t K N hst (by omega : j + 1 ≤ k)).trans huk1.le))
      (Set.mem_Iic.2 huk1.le) (time_mono' s t K N hst (by omega : j + 1 ≤ k))
  have hwd := weighted_duhamel_sum_le (B.L N) (B.three_le_L N) hm0 hm1 u hu0 hu_succ huk1 hW
    hΔ0 Dv M hM0 hA hAuv a
  refine hwd.trans ?_
  have hT0 : 0 ≤ Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) :=
    tailT_nonneg hW0.le _
  refine mul_le_mul_of_nonneg_right ?_ hT0
  -- the paired time sum
  set Ξ := Step2.xiK (B.L N) (B.W N) m with hΞ
  have hΞ0 : 0 ≤ Ξ := Step2.xiK_nonneg _ _ _
  set R := etaT E (s N) / etaT E (u k) with hR
  have hRe : R = (1 - s N) / (1 - u k) := Step2.etaT_ratio hE _ _
  set Λ := Step2.thr E s δ N (u k) with hΛ
  have hΛ0 : 0 ≤ Λ := thr_nonneg δ _
  set Ainv := (B.scale E N (u k))⁻¹ with hAinv
  have hAk := B.scale_pos' hE N (hs0.trans (hsu k)) huk1
  have hAinv0 : 0 ≤ Ainv := inv_nonneg.2 hAk.le
  set α := Ainv ^ ((3 : ℝ) / 7) with hα
  have hα0 : 0 ≤ α := Real.rpow_nonneg hAinv0 _
  set ε := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hε
  have hε0 : 0 ≤ ε := by have := Real.rpow_nonneg hW0.le (-D); positivity
  set q := qGrid B s ζ N (u k) with hq
  have hq0 : 0 ≤ q := qGrid_nonneg B ζ _ hs1 huk1
  set Q := q + α * Λ ^ 3 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set P := Ξ * (exp 1 * Λ ^ 2 * 36 * Ainv + Mg * Q) with hP
  set Qc := Ξ * (exp 1 * Λ ^ 2 * ε) with hQc
  have hP0 : 0 ≤ P := by positivity
  have hQc0 : 0 ≤ Qc := by positivity
  set w : ℕ → ℝ := fun j => (1 - u (j + 1)) / (1 - u k) with hw
  have h1k : 0 < 1 - u k := by linarith
  -- termwise
  have hterm : ∀ j ∈ Finset.range k, Δ * M j * w j ^ 2 * Ξ ≤
      P * (Δ * ((etaT E (u j))⁻¹ * w j ^ 2)) + Qc * (Δ * w j ^ 2) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hj1k : u (j + 1) ≤ u k := time_mono' s t K N hst (by omega)
    have hjk' : u j ≤ u k := time_mono' s t K N hst hjk.le
    have huj1 : u j < 1 := hjk'.trans_lt huk1
    have huj0 : 0 ≤ u j := hs0.trans (hsu j)
    have hηj := Step2.etaT_pos' hE huj1
    rw [hMj j hjk]
    have hΛj : Step2.thr E s δ N (u j) ≤ Λ := thr_mono hE δ hs1 hjk' huk1
    have hΛj0 : 0 ≤ Step2.thr E s δ N (u j) := thr_nonneg δ _
    have hAj : (B.scale E N (u j))⁻¹ ≤ Ainv := scale_inv_mono B hE huj0 hjk' huk1
    have hAj0 : 0 ≤ (B.scale E N (u j))⁻¹ := inv_nonneg.2 (B.scale_pos' hE N huj0 huj1).le
    have hαj : (B.scale E N (u j))⁻¹ ^ ((3 : ℝ) / 7) ≤ α :=
      Real.rpow_le_rpow hAj0 hAj (by norm_num)
    have hqj : qGrid B s ζ N (u j) ≤ q := qGrid_mono B ζ hs1 hjk' huk1
    have hqj0 := qGrid_nonneg B ζ (u j) hs1 huj1
    have hcoef : driftCoef' B E s δ D ζ Mg N (u j) ≤
        exp 1 * Λ ^ 2 * (36 * ((etaT E (u j))⁻¹ * Ainv) + ε) + Mg * ((etaT E (u j))⁻¹ * Q) := by
      unfold driftCoef'
      have hαj0 : 0 ≤ (B.scale E N (u j))⁻¹ ^ ((3 : ℝ) / 7) := Real.rpow_nonneg hAj0 _
      rw [hQ]
      gcongr
    have hw0 : 0 ≤ Δ * w j ^ 2 * Ξ := by positivity
    calc Δ * driftCoef' B E s δ D ζ Mg N (u j) * w j ^ 2 * Ξ
        = driftCoef' B E s δ D ζ Mg N (u j) * (Δ * w j ^ 2 * Ξ) := by ring
      _ ≤ (exp 1 * Λ ^ 2 * (36 * ((etaT E (u j))⁻¹ * Ainv) + ε)
            + Mg * ((etaT E (u j))⁻¹ * Q)) * (Δ * w j ^ 2 * Ξ) :=
          mul_le_mul_of_nonneg_right hcoef hw0
      _ = P * (Δ * ((etaT E (u j))⁻¹ * w j ^ 2)) + Qc * (Δ * w j ^ 2) := by
          rw [hP, hQc]; ring
  -- the two time sums
  have hS1 : ∑ j ∈ Finset.range k, Δ * ((etaT E (u j))⁻¹ * w j ^ 2) ≤ m⁻¹ * R ^ 2 := by
    have hb : ∀ j ∈ Finset.range k, Δ * ((etaT E (u j))⁻¹ * w j ^ 2) ≤
        Δ * (m⁻¹ * ((1 - s N) / (1 - u k) ^ 2)) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hj1k : u (j + 1) ≤ u k := time_mono' s t K N hst (by omega)
      have hpair := eta_inv_mul_weight_le hE (hu_succ j) hj1k huk1
      refine mul_le_mul_of_nonneg_left (hpair.trans ?_) hΔ0
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm0.le)
      exact div_le_div_of_nonneg_right (by linarith [hsu j]) (by positivity)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hkΔ, hRe]
    rw [show (u k - s N) * (m⁻¹ * ((1 - s N) / (1 - u k) ^ 2))
        = m⁻¹ * ((u k - s N) * (1 - s N) / (1 - u k) ^ 2) by ring, div_pow]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm0.le)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hS2 : ∑ j ∈ Finset.range k, Δ * w j ^ 2 ≤ R ^ 2 := by
    have hb : ∀ j ∈ Finset.range k, Δ * w j ^ 2 ≤ Δ * R ^ 2 := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hj1k : u (j + 1) ≤ u k := time_mono' s t K N hst (by omega)
      refine mul_le_mul_of_nonneg_left ?_ hΔ0
      rw [hRe]
      refine pow_le_pow_left₀ (div_nonneg (by linarith) h1k.le) ?_ 2
      exact div_le_div_of_nonneg_right (by linarith [hsu (j + 1)]) h1k.le
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hkΔ]
    have : u k - s N ≤ 1 := by linarith [hsu k]
    have : 0 ≤ u k - s N := by linarith [hsu k]
    nlinarith [sq_nonneg R]
  calc ∑ j ∈ Finset.range k, Δ * M j * ((1 - u (j + 1)) / (1 - u k)) ^ 2 * Ξ
      ≤ ∑ j ∈ Finset.range k,
          (P * (Δ * ((etaT E (u j))⁻¹ * w j ^ 2)) + Qc * (Δ * w j ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = P * ∑ j ∈ Finset.range k, Δ * ((etaT E (u j))⁻¹ * w j ^ 2)
          + Qc * ∑ j ∈ Finset.range k, Δ * w j ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ P * (m⁻¹ * R ^ 2) + Qc * R ^ 2 := by gcongr
    _ = _ := by rw [hP, hQc, hQ]; ring

/-- **The deterministic core of (T1)**: the five-term bound for abstract vectors satisfying the
expansion identity of `grid_expansion_all'` (the `Z`- and `Y`-sums entered as the vectors
`Zs`, `Ys`). -/
theorem grid_step_bound_core' (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) (hW : exp 1 ≤ (B.W N : ℝ)) (hN2 : 2 ≤ N)
    (hWL : (B.W N : ℝ) * B.L N ≤ N) (hηt : (etaT E (t N))⁻¹ ≤ N)
    {D δ ζ Mi Mg Mm : ℝ} (hD0 : 0 ≤ D) (hMi : 0 ≤ Mi) (hMg : 0 ≤ Mg)
    (hΔR : step s t K N ≤ (N : ℝ) ^ (-(2 * D + 76)))
    (A0 Ak Zs Ys : LoopArg (B.L N) 2 → ℂ) (Dv Rv : ℕ → LoopArg (B.L N) 2 → ℂ)
    (hexp : ∀ b, Ak b
      = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ) A0 b
        + Zs b + Ys b
        + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dv j)) b
        + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rv j)) b)
    (hinit : ∀ b, ‖A0 b‖ ≤ Mi * Step2.tT B E N D (time s t K N 0) (zdist (B.L N) (b 0 - b 1)))
    (hdrift : ∀ j < k, ∀ b, ‖Dv j b‖ ≤ driftCoef' B E s δ D ζ Mg N (time s t K N j) *
      Step2.tT B E N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)))
    (hZ : ∀ b, ‖Zs b‖ ≤ Mm * ((etaT E (s N) / etaT E (time s t K N k)) ^ 2 + 1) *
      Step2.tT B E N D (time s t K N k) (zdist (B.L N) (b 0 - b 1)))
    (hY : ∀ b, ‖Ys b‖ ≤ Step2.tT B E N D (time s t K N k) (zdist (B.L N) (b 0 - b 1)))
    (hRstep : ∀ j < k, ∀ b, ‖Rv j b‖ ≤
      stepErr B E N (time s t K N j) (time s t K N (j + 1)) (step s t K N))
    (a : LoopArg (B.L N) 2) :
    ‖Ak a‖ ≤ phiG' B E s δ D ζ Mi Mg Mm N (time s t K N k) *
      Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) := by
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hW0 : (0 : ℝ) < B.W N := lt_of_lt_of_le (exp_pos 1) hW
  have huk : time s t K N k ≤ t N := time_le_t s t K N hst hK1 hk
  have huk1 : time s t K N k < 1 := huk.trans_lt ht1
  have hsk : s N ≤ time s t K N k := s_le_time s t K N hst k
  set T := Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) with hT
  -- (i) the initial term
  have hAuv0 : (B.W N : ℝ) * ellHat (B.L N) (time s t K N k : ℂ) *
        ((1 - time s t K N k) * (mE E).im) ≤ (B.W N : ℝ) * ellHat (B.L N) (time s t K N 0 : ℂ) *
        ((1 - time s t K N 0) * (mE E).im) :=
    flowScale_antitoneOn hW0.le (B.L N) E
      (Set.mem_Iic.2 ((time_mono' s t K N hst (Nat.zero_le k)).trans huk1.le))
      (Set.mem_Iic.2 huk1.le) (time_mono' s t K N hst (Nat.zero_le k))
  have hI := Step2.norm_Uker_le_of_tail (B.three_le_L N) hm0 hm1
    (by rw [time_zero]; exact hs0) (time_mono' s t K N hst (Nat.zero_le k))
    (hs0.trans hsk) huk1 hW hMi hAuv0 hinit a
  have hR : (1 - time s t K N 0) / (1 - time s t K N k)
      = etaT E (s N) / etaT E (time s t K N k) := by
    rw [Step2.etaT_ratio hE, time_zero]
  rw [hR] at hI
  -- (ii) drift, (iii) remainder
  have hDr := drift_sum_le' B hE hs0 hst ht1 hK1 hk hW hMg Dv hdrift a
  have hRs := rsum_le B hE hs0 hst ht1 hK1 hk hN2 hWL hηt hD0 hΔR Rv hRstep a
  -- assemble
  rw [hexp a]
  have htri : ∀ x₁ x₂ x₃ x₄ x₅ : ℂ, ‖x₁ + x₂ + x₃ + x₄ + x₅‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ :=
    fun x₁ x₂ x₃ x₄ x₅ => by
      have h1 := norm_add_le (x₁ + x₂ + x₃ + x₄) x₅
      have h2 := norm_add_le (x₁ + x₂ + x₃) x₄
      have h3 := norm_add_le (x₁ + x₂) x₃
      have h4 := norm_add_le x₁ x₂
      linarith
  refine (htri _ _ _ _ _).trans ?_
  have hZa := hZ a
  have hYa := hY a
  have hI' : ‖Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ) A0 a‖ ≤
      Mi * (etaT E (s N) / etaT E (time s t K N k)) ^ 2 *
        Step2.xiK (B.L N) (B.W N) (mE E).im * T := hI
  unfold phiG'
  nlinarith [hI', hDr, hRs, hZa, hYa]

/-- **`grid_step_bound'`**: the grid form of Step 2's step bound, pathwise at a fixed
`ω` and a fixed target `k ≤ K N`. -/
theorem grid_step_bound' (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) (hW : exp 1 ≤ (B.W N : ℝ)) (hN2 : 2 ≤ N)
    (hWL : (B.W N : ℝ) * B.L N ≤ N) (hηt : (etaT E (t N))⁻¹ ≤ N)
    {D δ ζ Mi Mg Mm : ℝ} (hD0 : 0 ≤ D) (hMi : 0 ≤ Mi) (hMg : 0 ≤ Mg)
    (hΔR : step s t K N ≤ (N : ℝ) ^ (-(2 * D + 76))) (ω : Ωg B.toDims)
    (hexp : ∀ b : LoopArg (B.L N) 2,
      Agrid B E s t K N k ω b
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
              (Agrid B E s t K N 0 ω) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B E s t K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B E s t K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω)) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω)) b)
    (hinit : ∀ b, ‖Agrid B E s t K N 0 ω b‖ ≤
      Mi * Step2.tT B E N D (time s t K N 0) (zdist (B.L N) (b 0 - b 1)))
    (hdrift : ∀ j < k, ∀ b, ‖Dgrid B E s t K N j ω b‖ ≤
      driftCoef' B E s δ D ζ Mg N (time s t K N j) *
        Step2.tT B E N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)))
    (hZ : ∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B E s t K N (j + 1) ω)) b‖ ≤
      Mm * ((etaT E (s N) / etaT E (time s t K N k)) ^ 2 + 1) *
        Step2.tT B E N D (time s t K N k) (zdist (B.L N) (b 0 - b 1)))
    (hY : ∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B E s t K N (j + 1) ω)) b‖ ≤
      Step2.tT B E N D (time s t K N k) (zdist (B.L N) (b 0 - b 1)))
    (hRstep : ∀ j < k, ∀ b, ‖Rgrid B E s t K N j ω b‖ ≤
      stepErr B E N (time s t K N j) (time s t K N (j + 1)) (step s t K N))
    (a : LoopArg (B.L N) 2) :
    ‖Agrid B E s t K N k ω a‖ ≤ phiG' B E s δ D ζ Mi Mg Mm N (time s t K N k) *
      Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) :=
  grid_step_bound_core' B hE hs0 hst ht1 hK1 hk hW hN2 hWL hηt hD0 hMi hMg hΔR
    (Agrid B E s t K N 0 ω) (Agrid B E s t K N k ω)
    (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
      (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B E s t K N (j + 1) ω))
    (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
      (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B E s t K N (j + 1) ω))
    (fun j => Dgrid B E s t K N j ω) (fun j => Rgrid B E s t K N j ω)
    hexp hinit hdrift hZ hY hRstep a

end StepBoundPrime

end RBM.Gauss.Grid

/-! ### (T2) Scale facts from the plain (2.72) and `N^c ≤ scale(t)` -/

namespace RBM.Step2

open Finset Real MeasureTheory Filter

section PlainFacts

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- `(N^δ)^n ≤ a^m` from `N^c ≤ a` when `δ n ≤ c m` (`N ≥ 1`, `c ≥ 0`). -/
theorem natCast_rpow_pow_le_of_le {N : ℕ} (hN : (1 : ℝ) ≤ N) {δ c a : ℝ} {n m : ℕ}
    (hnm : δ * n ≤ c * m) (ha : (N : ℝ) ^ c ≤ a) : ((N : ℝ) ^ δ) ^ n ≤ a ^ m := by
  rw [natCast_rpow_pow]
  calc (N : ℝ) ^ (δ * n) ≤ (N : ℝ) ^ (c * m) := Real.rpow_le_rpow_of_exponent_le hN hnm
    _ = ((N : ℝ) ^ c) ^ m := (natCast_rpow_pow N c m).symm
    _ ≤ a ^ m := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha m

end PlainFacts

end RBM.Step2

/-! ### (T2) The threshold improvement under the plain (2.72) -/

namespace RBM.Gauss.Grid

open RBM Finset MeasureTheory Filter Real

section ImprovePlain

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}

end ImprovePlain

end RBM.Gauss.Grid
/-! ### (T3) The grid good event under the plain (2.72) -/

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section GoodEventPlain

variable {d : Dims}

end GoodEventPlain

end RBM.Gauss.Grid

/-! ### (T3) the quadratic-variation time sum under the plain (2.72) -/

namespace RBM.Gauss.Grid

open Filter Real RBM

namespace QVSum

/-- **The `J`-power absorption from the plain (2.72)**: with
`x = N^δ`, `x^{90} ≤ A` (from `N^c ≤ A`, `90δ ≤ c`), `R^{30} ≤ A`, `A ≥ 1`, `J ≤ x² R⁴`, `r² ≤ R`:
`J ≤ A`, `J³ ≤ A`, `J⁴ r³ ≤ A`, all from
`(x⁸ R^{19})^{90} = (x^{90})⁸ (R^{30})^{57} ≤ A^{65} ≤ A^{90}`. -/
theorem J_pow_le_plain {x R r A J : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R)
    (hxA : x ^ 90 ≤ A) (hRA : R ^ 30 ≤ A) (hA1 : 1 ≤ A) (hJ0 : 0 ≤ J) (hJ : J ≤ x ^ 2 * R ^ 4) :
    J ≤ A ∧ J ^ 3 ≤ A ∧ J ^ 4 * r ^ 3 ≤ A := by
  have hR0 : 0 ≤ R := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hrR : r ≤ R := by
    have : r ^ 2 ≤ R ^ 2 := hr.trans (by nlinarith)
    exact (pow_le_pow_iff_left₀ hr0 hR0 (by norm_num)).1 this
  have hbig : x ^ 8 * R ^ 19 ≤ A := by
    have h90 : (x ^ 8 * R ^ 19) ^ 90 ≤ A ^ 90 := by
      calc (x ^ 8 * R ^ 19) ^ 90 = (x ^ 90) ^ 8 * (R ^ 30) ^ 57 := by ring
        _ ≤ A ^ 8 * A ^ 57 := mul_le_mul (pow_le_pow_left₀ (by positivity) hxA 8)
            (pow_le_pow_left₀ (by positivity) hRA 57) (by positivity) (by positivity)
        _ = A ^ 65 := by ring
        _ ≤ A ^ 90 := pow_le_pow_right₀ hA1 (by norm_num)
    exact (pow_le_pow_iff_left₀ (by positivity) hA0 (by norm_num)).1 h90
  have hxm : ∀ a b : ℕ, a ≤ 8 → b ≤ 19 → x ^ a * R ^ b ≤ x ^ 8 * R ^ 19 := by
    intro a b ha hb
    exact mul_le_mul (pow_le_pow_right₀ hx ha) (pow_le_pow_right₀ hR hb) (by positivity)
      (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · calc J ≤ x ^ 2 * R ^ 4 := hJ
      _ ≤ x ^ 8 * R ^ 19 := hxm 2 4 (by norm_num) (by norm_num)
      _ ≤ A := hbig
  · calc J ^ 3 ≤ (x ^ 2 * R ^ 4) ^ 3 := pow_le_pow_left₀ hJ0 hJ 3
      _ = x ^ 6 * R ^ 12 := by ring
      _ ≤ x ^ 8 * R ^ 19 := hxm 6 12 (by norm_num) (by norm_num)
      _ ≤ A := hbig
  · calc J ^ 4 * r ^ 3 ≤ (x ^ 2 * R ^ 4) ^ 4 * R ^ 3 :=
          mul_le_mul (pow_le_pow_left₀ hJ0 hJ 4) (pow_le_pow_left₀ hr0 hrR 3) (by positivity)
            (by positivity)
      _ = x ^ 8 * R ^ 19 := by ring
      _ ≤ A := hbig

/-- The `Q_d` product bound of the quadratic-variation time sum under the plain (2.72) and
`N^c ≤ A_t` (via `J_pow_le_plain`). -/
theorem Qd_mul_le_plain {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℝ} (hE : |E| < 2)
    {s : ℕ → ℝ} {δ ε D c κ : ℝ} {N : ℕ} {t w v : ℝ}
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsw : s N ≤ w) (hwv : w ≤ v) (hvt : v ≤ t)
    (ht1 : t < 1)
    (hc0 : 0 < c) (hreg0 : (etaT E (s N) / etaT E t) ^ 30 ≤ B.scale E N t)
    (hAc : (N : ℝ) ^ c ≤ B.scale E N t)
    (hδ0 : 0 ≤ δ) (hδc : 90 * δ ≤ c) (hεδ : 2 * ε ≤ δ) (hD : 60 ≤ D)
    (hWbig : Real.exp ((4 * D) ^ 2 + 4) ≤ (B.W N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N) (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hcN : ∀ ℓ : ℝ, 1 ≤ ℓ → Lemma57.cNear2 (B.W N : ℝ) ℓ ≤ (N : ℝ) ^ κ) :
    Qd B E s δ ε D N w * ((1 - w) / (1 - v)) ^ 4 ≤
      (34 * (N : ℝ) ^ κ + 1152) * (etaT E (s N) ^ 3 / etaT E v ^ 4)
        + 3 * (etaT E (s N) / etaT E v) ^ 4 := by
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hwt : w ≤ t := hwv.trans hvt
  have hw1 : w < 1 := hwt.trans_lt ht1
  have hv1 : v < 1 := hvt.trans_lt ht1
  have hs1 : s N < 1 := hsw.trans_lt hw1
  have hw0 : 0 ≤ w := hs0.trans hsw
  have hηw : 0 < etaT E w := Step2.etaT_pos' hE hw1
  have hηv : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hηt : 0 < etaT E t := Step2.etaT_pos' hE ht1
  have hηs : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hηws : etaT E w ≤ etaT E (s N) := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηtw : etaT E t ≤ etaT E w := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηw1 : etaT E w ≤ 1 := by
    simp only [Step2.etaT_eq]
    calc (1 - w) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
      _ = 1 := one_mul 1
  have hratio : (1 - w) / (1 - v) = etaT E w / etaT E v := (Step2.etaT_ratio hE w v).symm
  -- scales
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hL0 : (0 : ℝ) < (B.L N : ℝ) := by exact_mod_cast (show 0 < B.L N by omega)
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := B.one_le_W N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hℓw1 : 1 ≤ B.ell N w := one_le_ellHat_of_nonneg hL1 hw0 hw1
  have hℓw0 : 0 < B.ell N w := by linarith
  have hℓtL : B.ell N t ≤ (B.L N : ℝ) := by
    simp only [Band.ell, ellHat]; exact min_le_right _ _
  have hℓwL : B.ell N w ≤ (B.L N : ℝ) := by
    simp only [Band.ell, ellHat]; exact min_le_right _ _
  have hℓt0 : 0 < B.ell N t := Step3.ellHat_pos_of_lt_one hL1 ht1
  -- (K1): `r_w² η_w ≤ η_s`
  have hK1 : (B.ell N w / B.ell N (s N)) ^ 2 * etaT E w ≤ etaT E (s N) := by
    have hK := ellHat_sq_mul_one_sub_le (B.L N) hw1 hsw
    change B.ell N w ^ 2 * (1 - w) ≤ B.ell N (s N) ^ 2 * (1 - s N) at hK
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simp only [Step2.etaT_eq]
    calc B.ell N w ^ 2 * ((1 - w) * (mE E).im) = (B.ell N w ^ 2 * (1 - w)) * (mE E).im := by
          ring
      _ ≤ (B.ell N (s N) ^ 2 * (1 - s N)) * (mE E).im := mul_le_mul_of_nonneg_right hK hm0.le
      _ = (1 - s N) * (mE E).im * B.ell N (s N) ^ 2 := by ring
  -- the scale `A_w` and its lower bound from the plain (2.72)
  have hAdef : B.scale E N w = (B.W N : ℝ) * B.ell N w * etaT E w := rfl
  have hA0 : 0 < B.scale E N w := by rw [hAdef]; positivity
  have hAtw : B.scale E N t ≤ B.scale E N w :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hw1.le) (Set.mem_Iic.2 ht1.le) hwt
  set Rw : ℝ := etaT E (s N) / etaT E w with hRw
  set Rt : ℝ := etaT E (s N) / etaT E t with hRt
  have hRw1 : 1 ≤ Rw := (one_le_div hηw).2 hηws
  have hRwt : Rw ≤ Rt := div_le_div_of_nonneg_left hηs.le hηt hηtw
  have hRt1 : 1 ≤ Rt := hRw1.trans hRwt
  have hg1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1 hc0.le
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have hAt1 : 1 ≤ B.scale E N t := hg1.trans hAc
  have hxA : ((N : ℝ) ^ δ) ^ 90 ≤ B.scale E N w := by
    have h : ((N : ℝ) ^ δ) ^ 90 ≤ B.scale E N w ^ 1 :=
      Step2.natCast_rpow_pow_le_of_le hN1 (by push_cast; linarith) (hAc.trans hAtw)
    rwa [pow_one] at h
  have hRA : Rw ^ 30 ≤ B.scale E N w :=
    (pow_le_pow_left₀ (by linarith) hRwt 30).trans (hreg0.trans hAtw)
  -- `J`
  set J : ℝ := qvJ E s δ ε N w with hJdef
  have hJeq : J = (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * Rw ^ 4) := rfl
  have hJ0 : 0 ≤ J := by rw [hJeq]; positivity
  have hJx : J ≤ ((N : ℝ) ^ δ) ^ 2 * Rw ^ 4 := by
    have h2e : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
    rw [hJeq]
    calc (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * Rw ^ 4) ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * Rw ^ 4) :=
          mul_le_mul_of_nonneg_right h2e (by positivity)
      _ = ((N : ℝ) ^ δ) ^ 2 * Rw ^ 4 := by ring
  have hr0 : 0 ≤ B.ell N w / B.ell N (s N) := by positivity
  have hr : (B.ell N w / B.ell N (s N)) ^ 2 ≤ Rw := by
    rw [hRw, le_div_iff₀ hηw]; exact hK1
  obtain ⟨hJA, hJ3, hJ4⟩ := J_pow_le_plain hx1 hRw1 hr0 hr hxA hRA (hAt1.trans hAtw) hJ0 hJx
  have hS0 : 0 ≤ EarlyQVRateEv.sDet B E N w (B.ell N (s N)) :=
    EarlyQVRateEv.sDet_nonneg B E N hw0 hw1 hℓs
  have hS : J ^ 4 * B.scale E N w ^ 2 * EarlyQVRateEv.sDet B E N w (B.ell N (s N)) ≤ 1 := by
    have e : J ^ 4 * B.scale E N w ^ 2 * EarlyQVRateEv.sDet B E N w (B.ell N (s N)) =
        J ^ 4 * (B.ell N w / B.ell N (s N)) ^ 3 / B.scale E N w := by
      unfold EarlyQVRateEv.sDet
      field_simp
    rw [e]
    exact div_le_one_of_le₀ hJ4 hA0.le
  -- `W` is large
  have hlog : (4 * D) ^ 2 + 4 ≤ Real.log (B.W N : ℝ) := (Real.le_log_iff_exp_le hW0).2 hWbig
  have hD2 : 0 ≤ (4 * D) ^ 2 := sq_nonneg _
  have hWe : Real.exp 1 ≤ (B.W N : ℝ) :=
    (Real.exp_le_exp.2 (by linarith)).trans hWbig
  have hW6 : (6 : ℝ) ≤ (B.W N : ℝ) := by
    have := Real.add_one_le_exp ((4 * D) ^ 2 + 4)
    have h1 : (1 : ℝ) ≤ (4 * D) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  -- near term
  have hnear := near_mul_le hℓs hℓw0.le hηw hηv hηws hK1
    (Lemma57.cNear2_nonneg hW1 hℓw0) (hcN _ hℓw1)
  -- far terms
  have hcF : Lemma57.cFar2 (B.W N : ℝ) (B.ell N w) ≤ 2 * (N : ℝ) ^ κ :=
    (cFar2_le_two_cNear2 hWe hℓw0).trans (by linarith [hcN _ hℓw1])
  have hfar := far_mul_le (W := (B.W N : ℝ)) (L := (B.L N : ℝ)) (D := D) hW0 hL0.le hηw hηv hηws
    hJ0 hA0 hS0 hJ3 hS (Lemma57.cFar2_nonneg hW1 hℓw0) hcF
  have hfar3 : 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) ≤ 1 := by
    have hAN : B.scale E N w ≤ N := by
      rw [hAdef]
      calc (B.W N : ℝ) * B.ell N w * etaT E w ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 := by gcongr
        _ ≤ N := by linarith
    have hJ3N : J ^ 3 ≤ N := hJ3.trans hAN
    have hWLJ : (B.W N : ℝ) * (B.L N : ℝ) * J ^ 3 ≤ (B.W N : ℝ) ^ 4 := by
      calc (B.W N : ℝ) * (B.L N : ℝ) * J ^ 3 ≤ (N : ℝ) * N :=
            mul_le_mul hWL hJ3N (by positivity) (by linarith)
        _ ≤ (B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2 :=
            mul_le_mul hNW hNW (by linarith) (by positivity)
        _ = (B.W N : ℝ) ^ 4 := by ring
    have hWD : (B.W N : ℝ) ^ (-D) ≤ ((B.W N : ℝ) ^ 6)⁻¹ := by
      calc (B.W N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-(6 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = ((B.W N : ℝ) ^ 6)⁻¹ := by
            rw [Real.rpow_neg hW0.le]; norm_cast
    have hWD0 : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    have e : 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) =
        32 * ((B.W N : ℝ) * (B.L N : ℝ) * J ^ 3) * (B.W N : ℝ) ^ (-D) := by ring
    rw [e]
    calc 32 * ((B.W N : ℝ) * (B.L N : ℝ) * J ^ 3) * (B.W N : ℝ) ^ (-D)
        ≤ 32 * (B.W N : ℝ) ^ 4 * ((B.W N : ℝ) ^ 6)⁻¹ :=
          mul_le_mul (by linarith) hWD hWD0 (by positivity)
      _ = 32 / (B.W N : ℝ) ^ 2 := by field_simp
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          have h36 : (6 : ℝ) ^ 2 ≤ (B.W N : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hW6 2
          norm_num at h36
          linarith
  -- nearEpsilon
  have hnE : EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J ≤
      (B.W N : ℝ)⁻¹ := by
    have hηt' : (N : ℝ)⁻¹ ≤ etaT E w := by
      have hNt : 1 ≤ (N : ℝ) * etaT E t := by
        calc (1 : ℝ) ≤ B.scale E N t := hAt1
          _ = (B.W N : ℝ) * B.ell N t * etaT E t := rfl
          _ ≤ (B.W N : ℝ) * (B.L N : ℝ) * etaT E t := by gcongr
          _ ≤ N * etaT E t := by gcongr
      have : (N : ℝ)⁻¹ ≤ etaT E t := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]; linarith
      exact this.trans hηtw
    have hA1 : 1 ≤ (B.W N : ℝ) * B.ell N w * etaT E w := hAt1.trans hAtw
    have hAN : (B.W N : ℝ) * B.ell N w * etaT E w ≤ N := by
      calc (B.W N : ℝ) * B.ell N w * etaT E w ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 := by gcongr
        _ ≤ N := by linarith
    have hJN : J ≤ (N : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]; exact hJA.trans (by rw [hAdef]; exact hAN)
    exact EEDef.nearEpsilon_le_inv hWe hL0 hℓw0 hηw hN1 zero_le_one hJ0 (by linarith) hηt' hA1
      hAN hWL hNW hJN (by linarith) (by linarith)
  -- assembly
  have hP0 : 0 ≤ (etaT E w / etaT E v) ^ 4 := by positivity
  have hPY : (etaT E w / etaT E v) ^ 4 ≤ (etaT E (s N) / etaT E v) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hηws hηv.le) 4
  have hWinv : (B.W N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hnEP : EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J *
      (etaT E w / etaT E v) ^ 4 ≤ (etaT E (s N) / etaT E v) ^ 4 :=
    calc EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J *
          (etaT E w / etaT E v) ^ 4 ≤ (B.W N : ℝ)⁻¹ * (etaT E w / etaT E v) ^ 4 :=
          mul_le_mul_of_nonneg_right hnE hP0
      _ ≤ 1 * (etaT E (s N) / etaT E v) ^ 4 := mul_le_mul hWinv hPY hP0 zero_le_one
      _ = (etaT E (s N) / etaT E v) ^ 4 := one_mul _
  have hY0 : 0 ≤ (etaT E (s N) / etaT E v) ^ 4 := by positivity
  have hfar3Y : 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) *
      (etaT E (s N) / etaT E v) ^ 4 ≤ (etaT E (s N) / etaT E v) ^ 4 :=
    calc 32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) *
          (etaT E (s N) / etaT E v) ^ 4 ≤ 1 * (etaT E (s N) / etaT E v) ^ 4 :=
          mul_le_mul_of_nonneg_right hfar3 hY0
      _ = (etaT E (s N) / etaT E v) ^ 4 := one_mul _
  have hX0 : 0 ≤ etaT E (s N) ^ 3 / etaT E v ^ 4 := by positivity
  have hnear' : QVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w) *
      (etaT E w / etaT E v) ^ 4 ≤ 2 * (N : ℝ) ^ κ * (etaT E (s N) ^ 3 / etaT E v ^ 4) := by
    unfold QVEndpoint.diagNearRate; exact hnear
  have hfar' : QVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D J
        (EarlyQVRateEv.sDet B E N w (B.ell N (s N))) * (etaT E w / etaT E v) ^ 4 ≤
      (16 * (2 * (N : ℝ) ^ κ) + 1152) * (etaT E (s N) ^ 3 / etaT E v ^ 4) +
        32 * ((B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3) *
          (etaT E (s N) / etaT E v) ^ 4 := by
    unfold QVEndpoint.diagFarRate; exact hfar
  have e1 : Qd B E s δ ε D N w * (etaT E w / etaT E v) ^ 4 =
      QVEndpoint.diagNearRate B N (B.ell N w) (B.ell N (s N)) (etaT E w) *
          (etaT E w / etaT E v) ^ 4
        + 2 * (EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N w) (etaT E w) D J *
          (etaT E w / etaT E v) ^ 4)
        + QVEndpoint.diagFarRate B N (B.ell N w) (etaT E w) D J
          (EarlyQVRateEv.sDet B E N w (B.ell N (s N))) * (etaT E w / etaT E v) ^ 4 := by
    unfold Qd; rw [← hJdef]; ring
  rw [hratio, e1]
  linarith

end QVSum

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section GoodEventPlain2

variable {d : Dims}

end GoodEventPlain2

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open Real Finset RBM RBM.Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω]

end RBM.Gauss.Grid

/-! ### (T3) Step 2 closes under the plain (2.72) -/

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-- `drift_point_le_heG'`'s coefficient is `driftCoef'` at `Mg = mgDrift`. -/
theorem heG_coef_eq_driftCoef' (E : ℝ) (s : ℕ → ℝ) (δ D ζ : ℝ) (N : ℕ) (v : ℝ) :
    Real.exp 1 * Step2.thr E s δ N v ^ 2 *
        (36 * ((etaT E v)⁻¹ * ((band d).scale E N v)⁻¹)
          + ((band d).W N : ℝ) * ((band d).L N : ℝ) * ((band d).W N : ℝ) ^ (-D))
      + mgDrift (band d) ζ N * (etaT E v)⁻¹ *
        (((4 * (N : ℝ) ^ ζ * ((band d).ell N v / (band d).ell N (s N))) ^ 3 + 1)
          + ((band d).scale E N v)⁻¹ ^ ((3 : ℝ) / 7) * Step2.thr E s δ N v ^ 3)
    = driftCoef' (band d) E s δ D ζ (mgDrift (band d) ζ N) N v := by
  unfold driftCoef' qGrid
  ring

/-- The good-set drift bound with the `(5.35)` exponent `3/7` (`drift_point_le_heG'`,
`driftCoef'`). -/
theorem drift_of_goodSet' {E : ℝ} (hE : |E| < 2) {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} {δ ε ζ D τ₁ : ℝ}
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsv : s N ≤ time s u K N j)
    (hv1 : time s u K N j < 1)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ) (hD : 8 + 2 * ζ ≤ D)
    (hW8 : 8 ≤ ((band d).W N : ℝ)) (hLW : ((band d).L N : ℝ) ≤ (band d).W N)
    (hNW : (N : ℝ) ≤ ((band d).W N : ℝ) ^ 2) (hlog : 2 * D ^ 2 ≤ Real.log ((band d).W N : ℝ))
    (hJA : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s u K N j) ≤
      (band d).scale E N (time s u K N j))
    (hDreg : ((band d).L N : ℝ) * √(((band d).W N : ℝ) ^ (-D)) ≤
      (band d).ell N (time s u K N j) * ((band d).scale E N (time s u K N j))⁻¹)
    (hG : H d s u K N j ω ∈
      goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζ ζ (ζ / 2) D)
    (hR : H d s u K N j ω ∈ rowSet d E N (time s u K N j) ((band d).ell N (s N)) (ζ / 2))
    (hjS : jSMat d E D N (time s u K N j) (H d s u K N j ω) ≤
      Step2.thr E s δ N (time s u K N j)) :
    ∀ b : LoopArg ((band d).L N) 2, ‖Dgrid (band d) E s u K N j ω b‖ ≤
      driftCoef' (band d) E s δ D ζ (mgDrift (band d) ζ N) N (time s u K N j) *
        Step2.tT (band d) E N D (time s u K N j) (zdist ((band d).L N) (b 0 - b 1)) := by
  intro b
  set v := time s u K N j with hv
  set M := H d s u K N j ω with hMdef
  have hM : M.IsHermitian := H_isHermitian d s u K N j ω
  obtain ⟨⟨⟨⟨⟨_hqv, hjg⟩, _h554⟩, hone⟩, h273⟩, h557⟩ := hG
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hℓs1 : 1 ≤ (band d).ell N (s N) := one_le_ellHat_of_nonneg ((band d).one_le_L N) hs0 hs1
  have hℓs0 : 0 < (band d).ell N (s N) := by linarith
  have hℓv1 : 1 ≤ (band d).ell N v := one_le_ellHat_of_nonneg ((band d).one_le_L N) hv0 hv1
  have hA0 : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN1 hζ0
  set g := 4 * (N : ℝ) ^ ζ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have e : (band d).ell N v / ((band d).ell N (s N) / g)
      = g * ((band d).ell N v / (band d).ell N (s N)) := by
    field_simp
  have hrat0 : 0 ≤ (band d).ell N v / (band d).ell N (s N) := by positivity
  -- `h273`
  have h273' : ∀ x y c : ZMod ((band d).L N),
      ‖gloop ((band d).L N) ((band d).W N) M (zt E v) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ ((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹ := by
    intro x y c
    have h := h273 ((![false, true, true], ![y, c, x]) : LoopData (d.L N) 3)
    have hidx : LoopData.idx ((![false, true, true], ![y, c, x]) : LoopData (d.L N) 3)
        = ⟨[false, true, true], [y, c, x]⟩ := by
      simp [LoopData.idx, List.ofFn_succ]
    rw [hidx] at h
    refine h.trans ?_
    rw [← hg, e, mul_pow, inv_pow]
    have hNg : (N : ℝ) ^ ζ ≤ g ^ 2 := by rw [hg]; nlinarith
    have h0 : 0 ≤ ((band d).ell N v / (band d).ell N (s N)) ^ 2 * (((band d).scale E N v) ^ 2)⁻¹ :=
      by positivity
    calc (N : ℝ) ^ ζ * ((band d).ell N v / (band d).ell N (s N)) ^ (3 - 1) *
          (((band d).scale E N v) ^ (3 - 1))⁻¹
        = (N : ℝ) ^ ζ * (((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹) := by norm_num; ring
      _ ≤ g ^ 2 * (((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹) := mul_le_mul_of_nonneg_right hNg h0
      _ = g ^ 2 * ((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹ := by ring
  -- `N^{ζ/2} √(ℓ_v/ℓ_s) ≤ √(ℓ_v/ℓ_s')`
  have hsq : (N : ℝ) ^ (ζ / 2) ≤ Real.sqrt g := by
    have e2 : (N : ℝ) ^ (ζ / 2) = Real.sqrt ((N : ℝ) ^ ζ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
    rw [e2]
    exact Real.sqrt_le_sqrt (by rw [hg]; linarith)
  have hkey : (N : ℝ) ^ (ζ / 2) * Real.sqrt ((band d).ell N v / (band d).ell N (s N)) ≤
      Real.sqrt ((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) := by
    rw [← hg, e, Real.sqrt_mul hg0.le]
    exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
  have hisq0 : 0 ≤ (Real.sqrt ((band d).scale E N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have h557C : ∀ (x y : ZMod ((band d).L N)) (p : (band d).Idx N), p.1 = y →
      ∑ r : (band d).Idx N, Lemma57.blkW ((band d).L N) ((band d).W N) r x *
          ‖green M (zt E v) r p‖ ≤
        √((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) *
          (√((band d).scale E N v))⁻¹ := by
    intro x y p hp
    exact (h557 x y p hp).trans (mul_le_mul_of_nonneg_right hkey hisq0)
  have h557R : ∀ (x y : ZMod ((band d).L N)) (r : (band d).Idx N), r.1 = x →
      ∑ p : (band d).Idx N, Lemma57.blkW ((band d).L N) ((band d).W N) p y *
          ‖green M (zt E v) r p‖ ≤
        √((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) *
          (√((band d).scale E N v))⁻¹ := by
    intro x y r hr
    exact (hR x y r hr).trans (mul_le_mul_of_nonneg_right hkey hisq0)
  -- `hone`, `hκ`
  have hone' : ∀ (σ : Bool) (b' : ZMod (d.L N)), ‖Matrix.trace ((Gsig M (zt E v) σ
        - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b')‖
      ≤ ((N : ℝ) ^ ζ * (2 * ((band d).ell N v / (band d).ell N (s N)))) *
        ((band d).scale E N v)⁻¹ := by
    intro σ b'
    exact (hone σ b').trans (le_of_eq (by ring))
  have hκ : 2 * ((N : ℝ) ^ ζ * (2 * ((band d).ell N v / (band d).ell N (s N)))) ≤
      (band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ)) := by
    rw [← hg, e, hg]; apply le_of_eq; ring
  -- `hjG`
  have hjG : jGMat (band d).toDims E N v ((band d).ell N v) (etaT E v) D M
      ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N v :=
    hjg.trans (mul_le_mul_of_nonneg_left hjS (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  have hmain := drift_point_le_heG' (B := band d) hE hM hN1 hs0 hsv hv1 hδ0 hε0 hεδ hζ0 hD hW8
    hLW hNW hlog hJA hDreg h273' h557C h557R hone' hκ hjS hjG b
  rw [heG_coef_eq_driftCoef'] at hmain
  exact hmain

end RBM.Gauss.Grid

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

end RBM.Gauss

end

