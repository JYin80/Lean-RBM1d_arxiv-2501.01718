/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarClosure
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.Step2Gauss
import RBM1D.EnergyN.Gauss.GridSharp47
import RBM1D.EnergyN.Gauss.GridFarMart
import RBM1D.EnergyN.Gauss.GridFarLift
import RBM1D.Flow.EnergyUniform
import RBM1D.Flow.Scales

/-!
# The far-field closure on the grid at an `N`-dependent energy

## Main results

* `grid_far_closeN` — the deterministic far-field closure on the grid: given the grid Duhamel
  expansion of `Agrid` and bounds on its initial value, drift, martingale and remainder terms,
  `|Agrid_k(a)| ≤ 6 N^{δ/4} T_{u_k, D-5}(|a₁ - a₂|)` at every far pair `|a₁ - a₂| > 6 ℓ*_{u_k}`.
  The constant `(2 + 36e)/(mE (E N)).im + e + 4` must be fixed before `∀ᶠ N`, so the theorem
  takes the κ-pair `(hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)` and replaces `(mE (E N)).im` there
  by the uniform lower bound `mκ := √(2κ')/2 ≤ (mE (E N)).im` (`κ' := min κ 1`, `mE_im_ge`), as
  in `GridGoodEvent.lean` and `GridFarMart.lean`. The other calls (`grid_phi_premises'N`,
  `eventually_constsN`, and the deterministic per-`N` helpers of `FarClosure`/`Sharp47`) are
  evaluated at `E N`.
* `farGridPointwise_gauss_plainN` — the per-endpoint far statement `FarGridPointwiseN d E s t`
  under the plain pair, with `{κ} (hκ0) (hκ1) (hEκ : ∀ N, |E N| ≤ 2 - κ)` and
  `hB : BoundsCoreN … E s`. It calls `sharp47_grid_plainN`, `highProb_farMart_grid_plainN`,
  `grid_far_closeN` (above), `plain_endpointN`, `scale_endpointN`,
  `drift_point_le_heG_scalars_plainN`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM Finset
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in
-- a long chain of `set`-bound real quantities
open Sharp47 FarClosure in
/-- **The deterministic far-field closure on the grid** (see the module docstring). The crossing
constant `(2 + 36e)/(mE (E N)).im + e + 4` is bounded through the uniform κ-bound
`mκ ≤ (mE (E N)).im`. -/
theorem grid_far_closeN {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {κ : ℝ} (hκ0 : 0 < κ)
    {E : ℕ → ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 90 * δ ≤ c) (hD : 64 ≤ D) :
    ∀ᶠ N : ℕ in atTop, ∀ Mi : ℝ, 0 ≤ Mi → Mi ≤ (N : ℝ) ^ (δ / 8) →
      1 ≤ K N → step s t K N ≤ (N : ℝ) ^ (-(2 * D + 76)) → ∀ k ≤ K N, ∀ ω,
      (∀ b : LoopArg (B.L N) 2,
        Agrid B (E N) s t K N k ω b
          = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
                (Agrid B (E N) s t K N 0 ω) b
            + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B (E N) s t K N (j + 1) ω)) b
            + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B (E N) s t K N (j + 1) ω)) b
            + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B (E N) s t K N j ω)) b
            + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B (E N) s t K N j ω)) b) →
      (∀ b, ‖Agrid B (E N) s t K N 0 ω b‖ ≤
        Mi * Step2.tT B (E N) N D (time s t K N 0) (zdist (B.L N) (b 0 - b 1))) →
      (∀ j < k, ∀ b, ‖Dgrid B (E N) s t K N j ω b‖ ≤
        ((drNear B (E N) s (δ / 96) N (time s t K N j)
            + drRes B (E N) s (δ / 96) N (time s t K N j)
                (2 * (etaT (E N) (time s t K N j))⁻¹ *
                  ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N (time s t K N j)) *
                  (B.W N : ℝ) ^ (-D)))
            * (if (zdist (B.L N) (b 0 - b 1) : ℝ)
                  ≤ ellStar (B.W N : ℝ) (B.ell N (time s t K N j)) then 1 else 0)
          + drFar B (E N) s δ (δ / 4) (δ / 96) D (thrFar (E N) s δ N (time s t K N j)) N
              (time s t K N j)) *
          Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1))) →
      (∀ a : LoopArg (B.L N) 2,
        6 * ellStar ((B.W N : ℝ)) (B.ell N (time s t K N k)) < (zdist (B.L N) (a 0 - a 1) : ℝ) →
        ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B (E N) s t K N (j + 1) ω)) a‖ ≤
          (N : ℝ) ^ (δ / 8) * Step2.tT B (E N) N D (time s t K N k) (zdist (B.L N) (a 0 - a 1))) →
      (∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B (E N) s t K N (j + 1) ω)) b‖ ≤
        Step2.tT B (E N) N D (time s t K N k) (zdist (B.L N) (b 0 - b 1))) →
      (∀ j < k, ∀ b, ‖Rgrid B (E N) s t K N j ω b‖ ≤
        stepErr B (E N) N (time s t K N j) (time s t K N (j + 1)) (step s t K N)) →
      ∀ a : LoopArg (B.L N) 2,
        6 * ellStar ((B.W N : ℝ)) (B.ell N (time s t K N k)) < (zdist (B.L N) (a 0 - a 1) : ℝ) →
        ‖Agrid B (E N) s t K N k ω a‖ ≤
          6 * (N : ℝ) ^ (δ / 4) *
            Step2.tT B (E N) N (D - 5) (time s t K N k) (zdist (B.L N) (a 0 - a 1)) := by
  classical
  have hE2 : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE N) (by linarith)
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'2 : κ' ≤ 2 := (min_le_right κ 1).trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκ0 : 0 < mκ := by positivity
  have hmge : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hδ4 : (0 : ℝ) < δ / 4 := by positivity
  filter_upwards [grid_phi_premises'N B hκ0 hE hs0 hst ht1 hc0 hreg0 hAc hδ0 hδ1 hδc hD,
    eventually_constsN B hκ0 hE hδ0,
    eventually_le_rpow ((2 + 36 * Real.exp 1) / mκ + Real.exp 1 + 4) hδ4,
    (Step2.tendsto_W B).eventually_ge_atTop ((10 : ℝ) ^ 6),
    (Real.tendsto_log_atTop.comp (Step2.tendsto_W B)).eventually_ge_atTop ((D + 16) ^ 2)]
    with N hF hC hC4 hW6 hlogW Mi hMi0 hMix hK1 hΔR k hk ω hexp hinit hdrift hZ hY hRstep a ha
  obtain ⟨hWe, hx1, -, -, hN2, hWL, hηt, hvF⟩ := hF
  obtain ⟨hΞy, hcNy, hcFy, hCy, hNW, hexW⟩ := hC
  have hlogW' : (D + 16) ^ 2 ≤ Real.log (B.W N : ℝ) := hlogW
  set x := (N : ℝ) ^ (δ / 8) with hx
  set y := (N : ℝ) ^ (δ / 64) with hy
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hxy : x = y ^ 8 := by
    rw [hx, hy, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hy1 : 1 ≤ y := Real.one_le_rpow hN1' (by positivity)
  have hyN : y ≤ N := by
    calc y ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      _ = N := Real.rpow_one _
  have hm0 := mE_im_pos (hE2 N)
  have hm1 : (mE (E N)).im ≤ 1 := mE_im_le_one (hE2 N)
  set m := (mE (E N)).im with hm
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set v := time s t K N k with hv
  have hvt : v ≤ t N := time_le_t s t K N (hst N) hK1 hk
  have hsv : s N ≤ v := s_le_time s t K N (hst N) k
  have hv1 : v < 1 := hvt.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hsv
  set R := etaT (E N) (s N) / etaT (E N) v with hR
  have hRe : R = (1 - s N) / (1 - v) := Step2.etaT_ratio (hE2 N) _ _
  have h1v : 0 < 1 - v := by linarith
  have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1v]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := le_trans (Real.one_le_exp (by norm_num)) hWe
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL1 : (1 : ℝ) ≤ B.L N := by exact_mod_cast B.one_le_L N
  have hLN : (B.L N : ℝ) ≤ N := by nlinarith only [hWL, hW1, hL1]
  have hWN : (B.W N : ℝ) ≤ N := by nlinarith only [hWL, hW1, hL1]
  have hηv0 : 0 < etaT (E N) v := Step2.etaT_pos' (hE2 N) hv1
  have hηt0 : 0 < etaT (E N) (t N) := Step2.etaT_pos' (hE2 N) (ht1 N)
  have hηvN : (etaT (E N) v)⁻¹ ≤ N := by
    refine (inv_anti₀ hηt0 ?_).trans hηt
    simp only [Step2.etaT_eq]
    exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hWD : (B.W N : ℝ) ^ (-D) ≤ ((N : ℝ) ^ 32)⁻¹ := by
    rw [Real.rpow_neg hW0.le]
    refine inv_anti₀ (by positivity) ?_
    calc (N : ℝ) ^ 32 ≤ ((B.W N : ℝ) ^ 2) ^ 32 := pow_le_pow_left₀ hN0.le hNW 32
      _ = (B.W N : ℝ) ^ ((64 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
      _ ≤ (B.W N : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
  have hexN : Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) ≤ N := hexW.trans hWN
  have hscaleN : ∀ w : ℝ, 0 ≤ w → w < 1 → B.scale (E N) N w ≤ N := by
    intro w hw0 hw1
    have hℓ : B.ell N w ≤ (B.L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hη1 : etaT (E N) w ≤ 1 := by
      simp only [Step2.etaT_eq]
      calc (1 - w) * (mE (E N)).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hηw : 0 < etaT (E N) w := Step2.etaT_pos' (hE2 N) hw1
    calc B.scale (E N) N w = (B.W N : ℝ) * B.ell N w * etaT (E N) w := rfl
      _ ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hℓ hW0.le) hη1 hηw.le
          positivity
      _ ≤ N := by linarith
  have hRN : R ≤ N := by
    have hηs1 : etaT (E N) (s N) ≤ 1 := by
      simp only [Step2.etaT_eq]
      calc (1 - s N) * (mE (E N)).im ≤ 1 * 1 :=
            mul_le_mul (by linarith [hs0 N]) hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hηs0 : 0 < etaT (E N) (s N) := Step2.etaT_pos' (hE2 N) hs1
    calc R = etaT (E N) (s N) * (etaT (E N) v)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 1 * N := mul_le_mul hηs1 hηvN (inv_nonneg.2 hηv0.le) zero_le_one
      _ = N := one_mul _
  have hN8 : (N : ℝ) ^ δ = x ^ 8 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hN4 : (N : ℝ) ^ (2 * (δ / 4)) = x ^ 4 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hN4' : (N : ℝ) ^ (δ / 4) = x ^ 2 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hthr : Step2.thr (E N) s δ N v = x ^ 8 * R ^ 4 := by rw [Step2.thr, hN8]
  have hJv : (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v = x ^ 12 * R ^ 4 := by
    rw [hN4, hthr]; ring
  have hx0 : 0 ≤ x := by linarith
  have hJv6 : (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v ≤ (N : ℝ) ^ 6 := by
    rw [hJv]
    have hx12 : x ^ 12 ≤ (N : ℝ) ^ 2 := by
      rw [hx, Step2.natCast_rpow_pow]
      calc (N : ℝ) ^ (δ / 8 * ((12 : ℕ) : ℝ)) ≤ (N : ℝ) ^ ((2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
        _ = (N : ℝ) ^ 2 := Real.rpow_natCast _ 2
    calc x ^ 12 * R ^ 4 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 4 :=
          mul_le_mul hx12 (pow_le_pow_left₀ hR0 hRN 4) (by positivity) (by positivity)
      _ = (N : ℝ) ^ 6 := by ring
  have hx4N : x ^ 4 ≤ N := by
    rw [hx, Step2.natCast_rpow_pow]
    calc (N : ℝ) ^ (δ / 8 * ((4 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
      _ = N := Real.rpow_one _
  -- Ξ
  set Ξ := Step2.xiK (B.L N) (B.W N) m with hΞdef
  have hΞ0 : 0 ≤ Ξ := Step2.xiK_nonneg _ _ _
  have hy8 : y ≤ y ^ 8 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 8)
  have hΞx : Ξ ≤ x := hΞy.trans (hxy ▸ hy8)
  have hmΞ : (m ^ 2)⁻¹ ≤ Ξ := by
    rw [hΞdef]; unfold Step2.xiK
    have := Real.exp_pos (Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))
    have : 0 ≤ cTail * (1 + 2 * (B.L N : ℝ) *
      Real.exp (-(Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) / 8))) := by
      have := cTail_nonneg; positivity
    linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hm21 : 1 ≤ (m ^ 2)⁻¹ := one_le_inv₀ hm2 |>.2 (pow_le_one₀ hm0.le hm1)
  have hΞ1 : 1 ≤ Ξ := hm21.trans hmΞ
  have hΞR : 1 ≤ Ξ * R ^ 2 := one_le_mul_of_one_le_of_one_le hΞ1 (one_le_pow₀ hR1)
  -- premises at `v`
  obtain ⟨hvA, hvα, hvε⟩ := hvF v ⟨hsv, hvt⟩
  have hA0 : 0 < B.scale (E N) N v := B.scale_pos' (hE2 N) N hv0 hv1
  have hA1 : 1 ≤ B.scale (E N) N v := by
    have : 1 ≤ x ^ 17 * R ^ 10 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) (one_le_pow₀ hR1)
    linarith
  have hxA37 : x ^ 24 * R ^ 10 ≤ B.scale (E N) N v ^ ((3 : ℝ) / 7) := by
    rw [Real.inv_rpow hA0.le] at hvα
    have hp : 0 < B.scale (E N) N v ^ ((3 : ℝ) / 7) := Real.rpow_pos_of_pos hA0 _
    rw [inv_mul_le_iff₀ hp, mul_one] at hvα
    exact hvα
  have hxA48 : x ^ 48 * R ^ 20 ≤ B.scale (E N) N v := by
    have h0 : 0 ≤ x ^ 24 * R ^ 10 := by positivity
    calc x ^ 48 * R ^ 20 = (x ^ 24 * R ^ 10) ^ 2 := by ring
      _ ≤ (B.scale (E N) N v ^ ((3 : ℝ) / 7)) ^ 2 := pow_le_pow_left₀ h0 hxA37 2
      _ = B.scale (E N) N v ^ ((3 : ℝ) / 7 * ((2 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]
      _ ≤ B.scale (E N) N v ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
      _ = B.scale (E N) N v := Real.rpow_one _
  -- the ratio `q = ℓ_v/ℓ_s`
  have hL1n : 1 ≤ B.L N := B.one_le_L N
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1n (hs0 N) hs1
  have hℓv : B.ell N (s N) ≤ B.ell N v := Step3.ellHat_mono hsv hv1
  set q := B.ell N v / B.ell N (s N) with hqdef
  have hq1 : 1 ≤ q := by rw [hqdef, le_div_iff₀ (by linarith)]; linarith
  have hq2 : q ^ 2 ≤ R := by
    have h := Step3.ellHat_le_sqrt_mul (L := B.L N) hsv hv1
    have h' : q ≤ √R := by
      rw [hqdef, div_le_iff₀ (by linarith), hRe]
      exact h
    calc q ^ 2 ≤ √R ^ 2 := pow_le_pow_left₀ (by linarith) h' 2
      _ = R := Real.sq_sqrt hR0
  set z := (N : ℝ) ^ (δ / 96) with hz
  have hz0 : 0 ≤ z := Real.rpow_nonneg hN0.le _
  have hzy : z ≤ y := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hrv : 4 * z * B.ell N v / B.ell N (s N) = 4 * z * q := by rw [hqdef, mul_div_assoc]
  have hr0 : 0 ≤ 4 * z * q := by positivity
  have hr3 : (4 * z * q) ^ 3 ≤ 64 * z ^ 3 * R ^ 2 := by
    have hq3 : q ^ 3 ≤ R ^ 2 := by
      calc q ^ 3 ≤ q ^ 4 := pow_le_pow_right₀ hq1 (by norm_num)
        _ = (q ^ 2) ^ 2 := by ring
        _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hq2 2
    calc (4 * z * q) ^ 3 = 64 * z ^ 3 * q ^ 3 := by ring
      _ ≤ 64 * z ^ 3 * R ^ 2 := by gcongr
  have hr2 : (4 * z * q) ^ 2 ≤ 16 * z ^ 2 * R := by
    calc (4 * z * q) ^ 2 = 16 * z ^ 2 * q ^ 2 := by ring
      _ ≤ 16 * z ^ 2 * R := by gcongr
  -- constants
  set cF1 := Lemma57.cFar (B.W N : ℝ) 1 with hcF1
  have hcF0 : 0 ≤ cF1 := Lemma57.cFar_nonneg hW1 one_pos
  have hy16 : 456976 ≤ y := by
    have : 0 < cSharp47 (E N) := by unfold cSharp47; positivity
    linarith
  have hCF : 64 * Ξ ^ 2 * cF1 ^ 2 * z ^ 3 ≤ x ^ 8 := by
    rw [hxy]
    calc 64 * Ξ ^ 2 * cF1 ^ 2 * z ^ 3 ≤ 64 * y ^ 2 * y ^ 2 * y ^ 3 := by gcongr
      _ = 64 * y ^ 7 := by ring
      _ ≤ y ^ 57 * y ^ 7 := by
          gcongr
          calc (64 : ℝ) ≤ y := by linarith
            _ ≤ y ^ 57 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 57)
      _ = (y ^ 8) ^ 8 := by ring
  have hC2 : Ξ ^ 2 * 169 ^ 2 * 16 * z ^ 2 ≤ x ^ 20 := by
    rw [hxy]
    calc Ξ ^ 2 * 169 ^ 2 * 16 * z ^ 2 ≤ y ^ 2 * 169 ^ 2 * 16 * y ^ 2 := by gcongr
      _ = 456976 * y ^ 4 := by ring
      _ ≤ y ^ 156 * y ^ 4 := by
          gcongr
          calc (456976 : ℝ) ≤ y := hy16
            _ ≤ y ^ 156 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 156)
      _ = (y ^ 8) ^ 20 := by ring
  -- the far drift coefficients at `v` and their pass-2 closures
  set P1 := cF1 * (4 * z * B.ell N v / B.ell N (s N)) ^ ((3 : ℝ) / 2) *
      (√(B.scale (E N) N v))⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v) with hP1def
  set P2 := 169 * (4 * z * B.ell N v / B.ell N (s N)) * (B.scale (E N) N v)⁻¹ *
      ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v) ^ ((3 : ℝ) / 2) with hP2def
  set P3 := Real.exp 1 * Step2.thr (E N) s δ N v ^ 2 * 36 * (B.scale (E N) N v)⁻¹ with hP3def
  set εW := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hεW
  have hεW0 : 0 ≤ εW := by have := Real.rpow_nonneg hW0.le (-D); positivity
  set Q := Real.exp 1 * Step2.thr (E N) s δ N v ^ 2 * εW with hQdef
  set P := P1 + P2 + P3 with hPdef
  have hP1c : Ξ * P1 * R ^ 2 ≤ 1 := by
    have h := far1R_le hΞ0 hcF0 hr0 hr3 hA0 hx1 hR1 hJv hxA48 hCF
    rw [← hrv] at h
    rw [hP1def]; linarith
  have hP2c : Ξ * P2 * R ^ 2 ≤ 1 := by
    have h := far2R_le hΞ0 hr0 hr2 hA0 hx1 hR1 hJv hxA48 hC2
    rw [← hrv] at h
    rw [hP2def]; linarith
  have hxA' : Ξ * (x ^ 16 * R ^ 10) ≤ B.scale (E N) N v := by
    calc Ξ * (x ^ 16 * R ^ 10) ≤ x * (x ^ 16 * R ^ 10) := by gcongr
      _ = x ^ 17 * R ^ 10 := by ring
      _ ≤ B.scale (E N) N v := hvA
  have hP3c : Ξ * P3 * R ^ 2 ≤ 36 * Real.exp 1 := by
    have e : Ξ * P3 * R ^ 2
        = 36 * Real.exp 1 * ((Ξ * (x ^ 16 * R ^ 10)) * (B.scale (E N) N v)⁻¹) := by
      rw [hP3def, hthr]; ring
    rw [e]
    have : (Ξ * (x ^ 16 * R ^ 10)) * (B.scale (E N) N v)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hA0, one_mul]; exact hxA'
    have he0 : 0 < Real.exp 1 := Real.exp_pos 1
    calc 36 * Real.exp 1 * ((Ξ * (x ^ 16 * R ^ 10)) * (B.scale (E N) N v)⁻¹)
        ≤ 36 * Real.exp 1 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 36 * Real.exp 1 := mul_one _
  have hQc : Ξ * Q * R ^ 2 ≤ Real.exp 1 := by
    have e : Ξ * Q * R ^ 2 = Real.exp 1 * (εW * (Ξ * (x ^ 16 * R ^ 10))) := by
      rw [hQdef, hthr]; ring
    rw [e]
    have : εW * (Ξ * (x ^ 16 * R ^ 10)) ≤ 1 := by
      calc εW * (Ξ * (x ^ 16 * R ^ 10)) ≤ εW * (x * (x ^ 16 * R ^ 10)) := by gcongr
        _ = εW * x ^ 17 * R ^ 10 := by ring
        _ ≤ 1 := hvε
    have he0 : 0 < Real.exp 1 := Real.exp_pos 1
    calc Real.exp 1 * (εW * (Ξ * (x ^ 16 * R ^ 10))) ≤ Real.exp 1 * 1 :=
          mul_le_mul_of_nonneg_left this he0.le
      _ = Real.exp 1 := mul_one _
  have hP0 : 0 ≤ P := by
    have h1 : 0 ≤ (4 * z * B.ell N v / B.ell N (s N)) := by rw [hrv]; exact hr0
    have h2 : 0 ≤ (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v := by rw [hJv]; positivity
    have h3 : 0 ≤ (√(B.scale (E N) N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have h4 : 0 ≤ (B.scale (E N) N v)⁻¹ := inv_nonneg.2 hA0.le
    have h5 := Real.rpow_nonneg h1 ((3 : ℝ) / 2)
    have h6 := Real.rpow_nonneg h2 ((3 : ℝ) / 2)
    rw [hPdef, hP1def, hP2def, hP3def]
    positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hPc : Ξ * P * R ^ 2 ≤ 2 + 36 * Real.exp 1 := by
    have e : Ξ * P * R ^ 2 = Ξ * P1 * R ^ 2 + Ξ * P2 * R ^ 2 + Ξ * P3 * R ^ 2 := by
      rw [hPdef]; ring
    rw [e]; linarith
  have he3 := exp_one_le_three
  have hPle : P ≤ 110 := by
    have : P ≤ Ξ * P * R ^ 2 := by
      calc P = P * 1 := (mul_one P).symm
        _ ≤ P * (Ξ * R ^ 2) := mul_le_mul_of_nonneg_left hΞR hP0
        _ = Ξ * P * R ^ 2 := by ring
    linarith
  have hQle : Q ≤ 3 := by
    have : Q ≤ Ξ * Q * R ^ 2 := by
      calc Q = Q * 1 := (mul_one Q).symm
        _ ≤ Q * (Ξ * R ^ 2) := mul_le_mul_of_nonneg_left hΞR hQ0
        _ = Ξ * Q * R ^ 2 := by ring
    linarith
  -- time facts
  have htj : ∀ j < k, s N ≤ time s t K N j ∧ time s t K N j ≤ v ∧ time s t K N j < 1 := by
    intro j hj
    have hjk : time s t K N j ≤ v := time_mono' s t K N (hst N) hj.le
    exact ⟨s_le_time s t K N (hst N) j, hjk, hjk.trans_lt hv1⟩
  have hcoefF : ∀ j < k,
      drFar B (E N) s δ (δ / 4) (δ / 96) D (thrFar (E N) s δ N (time s t K N j)) N
        (time s t K N j) ≤ P * (etaT (E N) (time s t K N j))⁻¹ + Q := by
    intro j hj
    obtain ⟨hsj, hjk, hj1⟩ := htj j hj
    have hΛ0 : 0 ≤ thrFar (E N) s δ N (time s t K N j) := by
      unfold thrFar
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (div_nonneg (Step2.etaT_pos' (hE2 N) hs1).le
          (Step2.etaT_pos' (hE2 N) hj1).le) _)
    have hΛ : thrFar (E N) s δ N (time s t K N j) ≤ Step2.thr (E N) s δ N v :=
      (thrFar_le_thr' (hE2 N) hsj hj1).trans (thr_mono (hE2 N) δ hs1 hjk hv1)
    exact coefFar_le B (hE2 N) (hs0 N) hsj hjk hv1 hW1 hΛ0 hΛ
  -- the pointwise split of `D_j` at the near band
  set Dn : ℕ → LoopArg (B.L N) 2 → ℂ := fun j b =>
    if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N (time s t K N j))
      then Dgrid B (E N) s t K N j ω b else 0 with hDndef
  set Df : ℕ → LoopArg (B.L N) 2 → ℂ := fun j b =>
    if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N (time s t K N j))
      then 0 else Dgrid B (E N) s t K N j ω b with hDfdef
  have hsplit : ∀ j, Dgrid B (E N) s t K N j ω = Dn j + Df j := by
    intro j; funext b
    simp only [hDndef, hDfdef, Pi.add_apply]
    split_ifs <;> simp
  have hDsum : (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B (E N) s t K N j ω)) a
      = (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dn j)) a
        + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Df j)) a := by
    have hfun : (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B (E N) s t K N j ω))
        = ∑ j ∈ Finset.range k, (step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dn j)
          + step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Df j)) :=
      Finset.sum_congr rfl fun j _ => by rw [hsplit j, Uker_add, smul_add]
    rw [hfun, Finset.sum_add_distrib, Pi.add_apply]
  -- far part of the drift
  have hDf : ∀ j < k, ∀ b, ‖Df j b‖ ≤
      ((0 : ℝ) * ((etaT (E N) (time s t K N j))⁻¹ *
          (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3)
        + P * (etaT (E N) (time s t K N j))⁻¹ + Q) *
      Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)) := by
    intro j hj b
    obtain ⟨hsj, hjk, hj1⟩ := htj j hj
    have hT0 : 0 ≤ Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)) :=
      tailT_nonneg hW0.le _
    have hη0 : 0 ≤ (etaT (E N) (time s t K N j))⁻¹ := inv_nonneg.2 (Step2.etaT_pos' (hE2 N) hj1).le
    by_cases hnear : (zdist (B.L N) (b 0 - b 1) : ℝ) ≤
        ellStar (B.W N : ℝ) (B.ell N (time s t K N j))
    · have e : Df j b = 0 := by simp only [hDfdef, hnear, ↓reduceIte]
      rw [e, norm_zero]
      exact mul_nonneg (by rw [zero_mul, zero_add]; positivity) hT0
    · have e : Df j b = Dgrid B (E N) s t K N j ω b := by simp only [hDfdef, hnear, ↓reduceIte]
      rw [e]
      have h := hdrift j hj b
      simp only [hnear, ↓reduceIte, mul_zero, zero_add] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hT0)
      rw [zero_mul, zero_add]
      exact hcoefF j hj
  have hDr := drift_sum_split B (hE2 N) (hs0 N) (hst N) (ht1 N) hK1 hk hWe (le_refl (0 : ℝ)) hP0 hQ0
    Df hDf a
  have hDrc : Ξ * ((0 : ℝ) * (2 * m⁻¹ * R ^ 2) + P * (m⁻¹ * R ^ 2) + Q * R ^ 2) ≤
      (2 + 36 * Real.exp 1) / m + Real.exp 1 := by
    have hmi0 : 0 ≤ m⁻¹ := inv_nonneg.2 hm0.le
    calc Ξ * ((0 : ℝ) * (2 * m⁻¹ * R ^ 2) + P * (m⁻¹ * R ^ 2) + Q * R ^ 2)
        = m⁻¹ * (Ξ * P * R ^ 2) + Ξ * Q * R ^ 2 := by ring
      _ ≤ m⁻¹ * (2 + 36 * Real.exp 1) + Real.exp 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hPc hmi0) hQc
      _ = (2 + 36 * Real.exp 1) / m + Real.exp 1 := by rw [div_eq_mul_inv]; ring
  set T := Step2.tT B (E N) N D v (zdist (B.L N) (a 0 - a 1)) with hT
  set T' := Step2.tT B (E N) N (D - 5) v (zdist (B.L N) (a 0 - a 1)) with hT'
  have hT0 : 0 ≤ T := tailT_nonneg hW0.le _
  have hTT' : T ≤ T' := Step2FarMart.tT_mono (B := B) (E := E N) hW1 (by linarith)
  have hWT' : (B.W N : ℝ) ^ (-(D - 5)) ≤ T' := rpow_neg_le_tailT _
  have hDfa : ‖(∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
      (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Df j)) a‖ ≤
      ((2 + 36 * Real.exp 1) / m + Real.exp 1) * T :=
    hDr.trans (mul_le_mul_of_nonneg_right hDrc hT0)
  -- near part of the drift
  have hCn0 : (0 : ℝ) ≤ 370 * (N : ℝ) ^ 8 := by positivity
  have hDn : ∀ j < k, ∀ b, ‖Dn j b‖ ≤ 370 * (N : ℝ) ^ 8 *
      (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N (time s t K N j))
        then 1 else 0) := by
    intro j hj b
    obtain ⟨hsj, hjk, hj1⟩ := htj j hj
    by_cases hnear : (zdist (B.L N) (b 0 - b 1) : ℝ) ≤
        ellStar (B.W N : ℝ) (B.ell N (time s t K N j))
    · have e : Dn j b = Dgrid B (E N) s t K N j ω b := by simp only [hDndef, hnear, ↓reduceIte]
      simp only [e, hnear, ↓reduceIte, mul_one]
      have h := hdrift j hj b
      simp only [hnear, ↓reduceIte, mul_one] at h
      have hηj : (etaT (E N) (time s t K N j))⁻¹ ≤ N := by
        refine (inv_anti₀ hηv0 ?_).trans hηvN
        simp only [Step2.etaT_eq]
        exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
      have hηj0 : 0 ≤ (etaT (E N) (time s t K N j))⁻¹ :=
        inv_nonneg.2 (Step2.etaT_pos' (hE2 N) hj1).le
      have hnr := drNear_le B (hE2 N) hδ1 (hs0 N) hsj hj1 hN1' hW1 hLN hηj (hcNy.trans hyN)
      have hΛ0 : 0 ≤ thrFar (E N) s δ N (time s t K N j) := by
        unfold thrFar
        exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg (div_nonneg (Step2.etaT_pos' (hE2 N) hs1).le
            (Step2.etaT_pos' (hE2 N) hj1).le) _)
      have hJj : (N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N (time s t K N j) ≤ (N : ℝ) ^ 6 := by
        refine le_trans ?_ hJv6
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
        exact (thrFar_le_thr' (hE2 N) hsj hj1).trans (thr_mono (hE2 N) δ hs1 hjk hv1)
      have hrs := drRes_le B (hE2 N) (D := D) hδ1 (hs0 N) hsj hj1 hN1' hW1 hLN hηj hWD hexN
        (hscaleN _ ((hs0 N).trans hsj) hj1) hΛ0 hJj
      have hrs' : drRes B (E N) s (δ / 96) N (time s t K N j)
          (2 * (etaT (E N) (time s t K N j))⁻¹ *
            ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N (time s t K N j)) * (B.W N : ℝ) ^ (-D))
          ≤ 8 := by
        refine hrs.trans ?_
        have hN20 : (N : ℝ) ≤ (N : ℝ) ^ 20 := by
          calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (N : ℝ) ^ 20 := pow_le_pow_right₀ hN1' (by norm_num)
        have hp : 0 < (N : ℝ) ^ 20 := by positivity
        calc 8 * ((N : ℝ) ^ 20)⁻¹ * (etaT (E N) (time s t K N j))⁻¹
            ≤ 8 * ((N : ℝ) ^ 20)⁻¹ * N := by gcongr
          _ = 8 * ((N : ℝ) / (N : ℝ) ^ 20) := by ring
          _ ≤ 8 * 1 := by gcongr; rw [div_le_one hp]; exact hN20
          _ = 8 := mul_one 8
      have hfr : drFar B (E N) s δ (δ / 4) (δ / 96) D (thrFar (E N) s δ N (time s t K N j)) N
          (time s t K N j) ≤ 110 * N + 3 := by
        refine (hcoefF j hj).trans ?_
        have := mul_le_mul hPle hηj hηj0 (by norm_num : (0 : ℝ) ≤ 110)
        linarith
      have hAj : 1 ≤ B.scale (E N) N (time s t K N j) := by
        refine hA1.trans ?_
        exact flowScale_antitoneOn hW0.le (B.L N) (E N) (Set.mem_Iic.2 hj1.le)
          (Set.mem_Iic.2 hv1.le) hjk
      have hT2 := tT_le_two B (d := (zdist (B.L N) (b 0 - b 1) : ℝ)) (by linarith : (0 : ℝ) ≤ D)
        hW1 hAj
      have hT0j : 0 ≤ Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)) :=
        tailT_nonneg hW0.le _
      have hsum : drNear B (E N) s (δ / 96) N (time s t K N j)
          + drRes B (E N) s (δ / 96) N (time s t K N j)
              (2 * (etaT (E N) (time s t K N j))⁻¹ *
                ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N (time s t K N j)) *
                (B.W N : ℝ) ^ (-D))
          + drFar B (E N) s δ (δ / 4) (δ / 96) D (thrFar (E N) s δ N (time s t K N j)) N
              (time s t K N j) ≤ 185 * (N : ℝ) ^ 8 := by
        have hN8 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hN1'
        have hNN8 : (N : ℝ) ≤ (N : ℝ) ^ 8 := by
          calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hN1' (by norm_num)
        linarith
      refine h.trans ?_
      calc _ ≤ (185 * (N : ℝ) ^ 8) * Step2.tT B (E N) N D (time s t K N j)
            (zdist (B.L N) (b 0 - b 1)) := mul_le_mul_of_nonneg_right hsum hT0j
        _ ≤ (185 * (N : ℝ) ^ 8) * 2 := mul_le_mul_of_nonneg_left hT2 (by positivity)
        _ = 370 * (N : ℝ) ^ 8 := by ring
    · have e : Dn j b = 0 := by simp only [hDndef, hnear, ↓reduceIte]
      simp only [e, hnear, ↓reduceIte, norm_zero, mul_zero, le_refl]
  have hNL := near_leak_le B (hE2 N) (hs0 N) (hst N) (ht1 N) hK1 hk hWe hCn0 Dn hDn a ha
  have hNLc : 370 * (N : ℝ) ^ 8 * (128 * Real.exp 3 * R ^ 2 *
      Real.exp (-(5 / 4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ)))) ≤ (B.W N : ℝ) ^ (-(D - 5)) := by
    have hex := exp_log_le_rpow hW1 (by linarith : (0 : ℝ) ≤ D + 16) hlogW'
    have he3 := exp_three_le
    have hR2 : R ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hR0 hRN 2
    have hN10 : (N : ℝ) ^ 10 ≤ (B.W N : ℝ) ^ 20 := by
      calc (N : ℝ) ^ 10 ≤ ((B.W N : ℝ) ^ 2) ^ 10 := pow_le_pow_left₀ hN0.le hNW 10
        _ = (B.W N : ℝ) ^ 20 := by ring
    have hC : 370 * (N : ℝ) ^ 8 * (128 * Real.exp 3 * R ^ 2) ≤ (B.W N : ℝ) ^ 21 := by
      have he30 : 0 ≤ Real.exp 3 := (Real.exp_pos 3).le
      calc 370 * (N : ℝ) ^ 8 * (128 * Real.exp 3 * R ^ 2)
          ≤ 370 * (N : ℝ) ^ 8 * (128 * 21 * (N : ℝ) ^ 2) := by gcongr
        _ = 994560 * (N : ℝ) ^ 10 := by ring
        _ ≤ (B.W N : ℝ) * (B.W N : ℝ) ^ 20 := by
            have : (994560 : ℝ) ≤ B.W N := by
              have : (994560 : ℝ) ≤ 10 ^ 6 := by norm_num
              linarith
            exact mul_le_mul this hN10 (by positivity) hW0.le
        _ = (B.W N : ℝ) ^ 21 := by ring
    have hEx0 : 0 ≤ Real.exp (-(5 / 4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ))) :=
      (Real.exp_pos _).le
    calc 370 * (N : ℝ) ^ 8 * (128 * Real.exp 3 * R ^ 2 *
          Real.exp (-(5 / 4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ))))
        = (370 * (N : ℝ) ^ 8 * (128 * Real.exp 3 * R ^ 2)) *
            Real.exp (-(5 / 4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ))) := by ring
      _ ≤ (B.W N : ℝ) ^ 21 * (B.W N : ℝ) ^ (-(D + 16)) :=
          mul_le_mul hC hex hEx0 (by positivity)
      _ = (B.W N : ℝ) ^ (-(D - 5)) := rpow_nat_mul_rpow hW0 21 (by push_cast; ring)
  -- the initial term
  have hinit' : ∀ b, ‖Agrid B (E N) s t K N 0 ω b‖ ≤ Mi * tailT (B.W N : ℝ)
      (ellHat (B.L N) (time s t K N 0 : ℂ)) ((1 - time s t K N 0) * m) D
      (zdist (B.L N) (b 0 - b 1)) := fun b => hinit b
  have hlp : 0 ≤ Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg hW1) _
  have hℓstar0 : 0 ≤ ellStar (B.W N : ℝ) (B.ell N v) := by
    unfold ellStar
    have hℓv1 : 1 ≤ B.ell N v := one_le_ellHat_of_nonneg hL1n hv0 hv1
    exact mul_nonneg hlp (by linarith)
  have hd : ellStar (B.W N : ℝ) (ellHat (B.L N) (v : ℂ)) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by
    have : ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by linarith
    exact this
  have hI := init_far_le (B.three_le_L N) (hE2 N) (by rw [time_zero]; exact hs0 N)
    (time_mono' s t K N (hst N) (Nat.zero_le k)) hv1 hWe hMi0 hinit' a hd
  have hR' : (1 - time s t K N 0) / (1 - v) = R := by rw [hRe, time_zero]
  rw [hR'] at hI
  have hIrem : Mi * (m ^ 2)⁻¹ * R ^ 2 * (B.W N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-(D - 5)) := by
    have hMm : Mi * (m ^ 2)⁻¹ ≤ x * x :=
      mul_le_mul hMix (hmΞ.trans hΞx) (by positivity) hx0
    have hxxW : x * x ≤ (B.W N : ℝ) := by
      have h2 : (x * x) ^ 2 ≤ ((B.W N : ℝ)) ^ 2 := by
        calc (x * x) ^ 2 = x ^ 4 := by ring
          _ ≤ (N : ℝ) := hx4N
          _ ≤ (B.W N : ℝ) ^ 2 := hNW
      exact (pow_le_pow_iff_left₀ (by positivity) hW0.le two_ne_zero).1 h2
    have hR4 : R ^ 2 ≤ (B.W N : ℝ) ^ 4 := by
      calc R ^ 2 ≤ ((B.W N : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hR0 (hRN.trans hNW) 2
        _ = (B.W N : ℝ) ^ 4 := by ring
    have hWD0 : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    calc Mi * (m ^ 2)⁻¹ * R ^ 2 * (B.W N : ℝ) ^ (-D)
        ≤ (B.W N : ℝ) * (B.W N : ℝ) ^ 4 * (B.W N : ℝ) ^ (-D) := by
          gcongr
          exact hMm.trans hxxW
      _ = (B.W N : ℝ) ^ 5 * (B.W N : ℝ) ^ (-D) := by ring
      _ = (B.W N : ℝ) ^ (-(D - 5)) := rpow_nat_mul_rpow hW0 5 (by push_cast; ring)
  -- the remaining terms
  have hZa := hZ a ha
  have hYa := hY a
  have hRs := rsum_le B (hE2 N) (hs0 N) (hst N) (ht1 N) hK1 hk hN2 hWL hηt
    (by linarith : (0 : ℝ) ≤ D) hΔR (fun j => Rgrid B (E N) s t K N j ω) hRstep a
  rw [hexp a, hDsum]
  have hMiΞ : Mi * Ξ ≤ x ^ 2 := by
    calc Mi * Ξ ≤ x * x := mul_le_mul hMix hΞx hΞ0 hx0
      _ = x ^ 2 := by ring
  have hxx2 : x ≤ x ^ 2 := by
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := mul_le_mul_of_nonneg_left hx1 hx0
      _ = x ^ 2 := by ring
  have hminv : m⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκ0 (hmge N)
  have hC4' : (2 + 36 * Real.exp 1) / m + Real.exp 1 + 4 ≤ x ^ 2 := by
    have hstep : (2 + 36 * Real.exp 1) / m ≤ (2 + 36 * Real.exp 1) / mκ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hminv (by positivity)
    rw [← hN4']
    linarith [hC4]
  have hcm0 : 0 ≤ (2 + 36 * Real.exp 1) / m + Real.exp 1 := by positivity
  have hI' : ‖Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (v : ℂ)
      (Agrid B (E N) s t K N 0 ω) a‖ ≤ Mi * Ξ * T + (B.W N : ℝ) ^ (-(D - 5)) :=
    hI.trans (add_le_add (le_of_eq rfl) hIrem)
  rw [hN4']
  exact final_far_arith hI' hZa hYa (hNL.trans hNLc) hDfa hRs hMiΞ hxx2 hC4' hcm0 hT0 hTT' hWT'

variable (d : Dims)

set_option maxHeartbeats 1000000 in
-- the event carries many components and grid facts at once
set_option linter.unusedVariables false in
open FarClosure in
/-- The per-endpoint far statement `FarGridPointwiseN` under the plain pair.
Internal choices: `δ₀ = min(c/90,1)`, `D′ = max(D+5,64)`, `K = gridK D′ (D₁+3)`. The event is
`goodEventSharp47` (at `D₁+1`) ∩ the complement of the far-martingale bad event (at
`D₁+1`); on it `gridTauFar = K` and `J*_{u_j} < thrFar(u_j)` for all `j ≤ K` are conclusions of
`sharp47_grid_plainN`, the drift is `drift_of_goodSet_split` at `Λ = thrFar(u_j)`
(`hΛ = thrFar_le_thr'`), and `grid_far_closeN` at `D′` followed by `tT_mono`
(`D ≤ D′ - 5`) gives `lkErrMat ≤ 6 N^{δ/4} T_{u,D} ≤ N^δ T_{u,D}` at every far `p`. -/
theorem farGridPointwise_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    FarGridPointwiseN d E s t := by
  intro D hD u
  have hE : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hEκ N) (by linarith)
  refine ⟨min (c / 90) 1, lt_min (by positivity) one_pos, ?_⟩
  intro δ hδ0 hδ₀ D₁ hD₁
  have hδc : δ ≤ c / 90 := hδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ₀.trans (min_le_right _ _)
  have hεδ : 2 * (δ / 4) ≤ δ := by linarith
  have hD'64 : 64 ≤ max (D + 5) 64 := le_max_right _ _
  have hD'5 : D + 5 ≤ max (D + 5) 64 := le_max_left _ _
  have hsu : ∀ N, s N ≤ (u N : ℝ) := fun N => (u N).2.1
  have hut : ∀ N, (u N : ℝ) ≤ t N := fun N => (u N).2.2
  have hu1 : ∀ N, (u N : ℝ) < 1 := fun N => (hut N).trans_lt (ht1 N)
  have hK0 : ∀ N, gridK (max (D + 5) 64) (D₁ + 3) N ≠ 0 := gridK_ne_zero _ (D₁ + 3)
  have hCK : 0 ≤ CK (max (D + 5) 64) (D₁ + 3) := by unfold CK; linarith
  refine ⟨gridK (max (D + 5) 64) (D₁ + 3), hK0,
    ⟨CK (max (D + 5) 64) (D₁ + 3) + 2, by linarith, gridK_card_le hCK⟩, ?_⟩
  have hG4 := sharp47_grid_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hD'64 hδ0 hδ₀ u
    (D₁ + 1) (by linarith)
  rw [show D₁ + 1 + 2 = D₁ + 3 by ring] at hG4
  have hG5 := highProb_farMart_grid_plainN (d := d) hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hδ0 hδc
    hD'64 hsu hut (D₁ + 1) (by linarith)
  rw [show D₁ + 1 + 2 = D₁ + 3 by ring] at hG5
  have hcore := grid_far_closeN (band d) (K := gridK (max (D + 5) 64) (D₁ + 3)) hκ0 hEκ hs0 hsu hu1
    hc0 (plain_endpointN (band d) hE ht1 hreg0 u) (scale_endpointN (band d) ht1 hAc u) hδ0 hδ1
    (by linarith : 90 * δ ≤ c) hD'64
  have hScal := drift_point_le_heG_scalars_plainN (band d) hE hs0 ht1 hc0 hreg0 hAc hδ0.le hδc
    hεδ (by linarith : (4 : ℝ) ≤ max (D + 5) 64)
  have hstepR : ∀ᶠ N : ℕ in atTop, step s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N
      ≤ (N : ℝ) ^ (-(2 * max (D + 5) 64 + 76)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact (step_gridK_le hN1 (by linarith [hs0 N, hut N, ht1 N])).trans
      (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith))
  filter_upwards [hG4, hG5, hcore, hScal, hstepR,
    eventually_le_rpow 7 (by positivity : (0 : ℝ) < 3 * δ / 4), eventually_ge_atTop 2]
    with N h4 h5 hcN hScalN hΔR h7 hN2
  obtain ⟨hprob4, hgood⟩ := h4
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨_, hW8, hLW, hNW, hlog, hv⟩ := hScalN
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by linarith
  refine (measure_le_of_subset_union ?_ hprob4 h5).trans ?_
  · intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or, Set.notMem_compl_iff] at hcon
    obtain ⟨hG, h5ω⟩ := hcon
    obtain ⟨p, hpfar, hpbad⟩ := hω
    refine absurd hpbad (not_lt.2 ?_)
    obtain ⟨hτeq, hall, -⟩ := hgood ω hG
    obtain ⟨⟨⟨hGω, hRω⟩, hAω⟩, hYω⟩ := hG
    obtain ⟨⟨⟨_hZall, _hYold⟩, _hGall⟩, hinit, _hJ0⟩ := hGω
    have hN1n : 1 ≤ gridK (max (D + 5) 64) (D₁ + 3) N := Nat.one_le_iff_ne_zero.2 (hK0 N)
    have htime : ∀ j ≤ gridK (max (D + 5) 64) (D₁ + 3) N,
        s N ≤ time s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N j ∧
        time s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N j < 1 := by
      intro j hj
      have hm := time_mono_of_le (s := s) (u := fun N => (u N : ℝ))
        (K := gridK (max (D + 5) 64) (D₁ + 3)) (N := N) (hsu N) (Nat.zero_le j)
      rw [time_zero] at hm
      have h1 : time s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N j
          ≤ (u N : ℝ) := by
        rw [← time_last s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N (hK0 N)]
        exact time_mono_of_le (s := s) (u := fun N => (u N : ℝ)) (hsu N) hj
      exact ⟨hm, h1.trans_lt (hu1 N)⟩
    have htl : time s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N
        (gridK (max (D + 5) 64) (D₁ + 3) N) = (u N : ℝ) :=
      time_last s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N (hK0 N)
    have hmono5 : Step2.tT (band d) (E N) N (max (D + 5) 64 - 5) (u N : ℝ)
          (zdist (d.L N) (p.1 - p.2))
        ≤ Step2.tT (band d) (E N) N D (u N : ℝ) (zdist (d.L N) (p.1 - p.2)) :=
      Step2FarMart.tT_mono (B := band d) (E := E N) hW1 (by linarith)
    have hmono' : Step2.tT (band d) (E N) N (max (D + 5) 64) (u N : ℝ) (zdist (d.L N) (p.1 - p.2))
        ≤ Step2.tT (band d) (E N) N D (u N : ℝ) (zdist (d.L N) (p.1 - p.2)) :=
      Step2FarMart.tT_mono (B := band d) (E := E N) hW1 (by linarith)
    have hT0 : 0 ≤ Step2.tT (band d) (E N) N D (u N : ℝ) (zdist (d.L N) (p.1 - p.2)) :=
      tailT_nonneg (by linarith) _
    have h6 : 6 * (N : ℝ) ^ (δ / 4) ≤ (N : ℝ) ^ δ := by
      have e : (N : ℝ) ^ δ = (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (3 * δ / 4) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      rw [e]
      have h0 : 0 ≤ (N : ℝ) ^ (δ / 4) := Real.rpow_nonneg hN0.le _
      nlinarith
    rcases lt_or_eq_of_le (hsu N) with hlt | heq
    · obtain ⟨hexp, hRst⟩ := hAω hlt
      have hlk := lkErrMat_eq_norm_Agrid d (E := E N) (s := s) (u := fun N => (u N : ℝ))
        (K := gridK (max (D + 5) 64) (D₁ + 3)) (gridK (max (D + 5) 64) (D₁ + 3) N) ω p.1 p.2
      rw [htl] at hlk
      rw [hlk]
      have hafar : 6 * ellStar ((band d).W N : ℝ) ((band d).ell N
          (time s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N
            (gridK (max (D + 5) 64) (D₁ + 3) N)))
          < (zdist ((band d).L N) ((![p.1, p.2] : LoopArg ((band d).L N) 2) 0
              - (![p.1, p.2] : LoopArg ((band d).L N) 2) 1) : ℝ) := by
        rw [htl]; exact hpfar
      have hA := hcN ((N : ℝ) ^ (δ / 16)) (Real.rpow_nonneg hN0.le _)
        (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)) hN1n hΔR
        (gridK (max (D + 5) 64) (D₁ + 3) N) le_rfl ω (hexp _ le_rfl) hinit
        (fun j hj b => by
          have hjK : j ≤ gridK (max (D + 5) 64) (D₁ + 3) N := hj.le
          obtain ⟨h1, h2⟩ := hall j hjK
          obtain ⟨ht0, ht1'⟩ := htime j hjK
          have hjR := hRω ⟨j, Nat.lt_succ_of_le hjK⟩
          have hmem := mem_Icc_time s (fun N => (u N : ℝ)) (gridK (max (D + 5) 64) (D₁ + 3)) N j
            (hs0 N) (hsu N) hjK
          obtain ⟨hJA, hDreg⟩ := hv _ hmem.1 (hmem.2.trans (hut N))
          rw [show δ / 192 = δ / 96 / 2 by ring] at h2 hjR
          exact drift_of_goodSet_split d (hE N) hN1' (hs0 N) ht0 ht1' hδ0.le
            (by positivity : (0 : ℝ) ≤ δ / 4) hεδ (by positivity : (0 : ℝ) ≤ δ / 96)
            (by linarith : 8 + 2 * (δ / 96) ≤ max (D + 5) 64) hW8 hLW hNW hlog hJA hDreg h2 hjR
            h1.le (thrFar_le_thr' (hE N) ht0 ht1') b)
        (fun b hb => by
          by_contra hc
          push Not at hc
          refine h5ω ⟨gridK (max (D + 5) 64) (D₁ + 3) N, le_rfl, b, hb, ?_⟩
          rw [hτeq, min_self]
          exact hc.le)
        (fun b => by
          have hb := hYω b
          rw [hτeq] at hb
          exact hb.le)
        (fun j hj b => hRst j hj b) ![p.1, p.2] hafar
      rw [htl] at hA
      calc _ ≤ 6 * (N : ℝ) ^ (δ / 4) * Step2.tT (band d) (E N) N (max (D + 5) 64 - 5) (u N : ℝ)
            (zdist (d.L N) (p.1 - p.2)) := hA
        _ ≤ 6 * (N : ℝ) ^ (δ / 4) * Step2.tT (band d) (E N) N D (u N : ℝ)
            (zdist (d.L N) (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_left hmono5 (by positivity)
        _ ≤ (N : ℝ) ^ δ * Step2.tT (band d) (E N) N D (u N : ℝ) (zdist (d.L N) (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_right h6 hT0
    · -- degenerate grid `s N = u N`: `H_K = H_0`
      have hlk := lkErrMat_eq_norm_Agrid d (E := E N) (s := s) (u := fun N => (u N : ℝ))
        (K := gridK (max (D + 5) 64) (D₁ + 3)) 0 ω p.1 p.2
      rw [time_zero] at hlk
      have heq' : s N = (u N : ℝ) := heq
      rw [H_eq_H_zero_of_eq d heq, ← heq', hlk]
      have hb := hinit ![p.1, p.2]
      rw [time_zero] at hb
      have h16 : (N : ℝ) ^ (δ / 16) ≤ (N : ℝ) ^ δ :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      have hmono'' : Step2.tT (band d) (E N) N (max (D + 5) 64) (s N) (zdist (d.L N) (p.1 - p.2))
          ≤ Step2.tT (band d) (E N) N D (s N) (zdist (d.L N) (p.1 - p.2)) :=
        Step2FarMart.tT_mono (B := band d) (E := E N) hW1 (by linarith)
      have hT0' : 0 ≤ Step2.tT (band d) (E N) N D (s N) (zdist (d.L N) (p.1 - p.2)) :=
        tailT_nonneg (by linarith) _
      calc _ ≤ (N : ℝ) ^ (δ / 16) * Step2.tT (band d) (E N) N (max (D + 5) 64) (s N)
            (zdist (d.L N) (p.1 - p.2)) := hb
        _ ≤ (N : ℝ) ^ (δ / 16) * Step2.tT (band d) (E N) N D (s N) (zdist (d.L N) (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_left hmono'' (Real.rpow_nonneg hN0.le _)
        _ ≤ (N : ℝ) ^ δ * Step2.tT (band d) (E N) N D (s N) (zdist (d.L N) (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_right h16 hT0'
  · have p1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D₁ + 1)) := Real.rpow_nonneg hN0.le _
    rw [← ENNReal.ofReal_add p1 p1]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (N : ℝ) ^ (-(D₁ + 1)) = (N : ℝ) ^ (-D₁) * (N : ℝ)⁻¹ := by
      rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    rw [e1]
    have h0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have hi : (N : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN2'
    nlinarith

section CompatN

end CompatN

end RBM.Gauss.Grid

end
