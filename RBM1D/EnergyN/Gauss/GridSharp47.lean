/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridSharp47
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.Step2Gauss
import RBM1D.EnergyN.Gauss.Step2Close
import RBM1D.EnergyN.Gauss.GridGoodEvent
import RBM1D.EnergyN.Gauss.GridFarStop

/-!
# The sharp bound on `J*` along the grid, at an `N`-dependent energy

Five statements at an `N`-dependent energy `E : ℕ → ℝ`: the eventual numerical bounds on the
constants (`RBM.Gauss.Grid.Sharp47.eventually_constsN`), the deterministic improvement
`J* ≤ cSharp47 N^{δ/2} ((η_s/η_u)^2 + 1) < thrFar` at each grid time
(`RBM.Gauss.Grid.grid_sharp47_improveN`), the comparison with the threshold
(`RBM.Gauss.Grid.Sharp47.eventually_lev_ltN`), the probability of the good event
(`RBM.Gauss.Grid.Sharp47.goodEventSharp47_probN`), and the resulting statement on the good event
(`RBM.Gauss.Grid.sharp47_grid_plainN`).

## The external `κ`

The constants `cSharp47 (E N) = 16 + e + (36e+16)/(mE (E N)).im` and
`Step2.xiK (B.L N) (B.W N) (mE (E N)).im` must be bounded before `∀ᶠ N`. The theorems take
`{κ:ℝ}(hκ0:0<κ)(hE:∀N,|E N|≤2-κ)`, the uniform `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N`
(`κ' := min κ 1`, `mE_im_ge`, as elsewhere in `RBM1D/EnergyN`), and the antitone bound
`cSharp47 (E N) ≤ 16 + e + (36e+16)·mκ⁻¹` (the only `m`-dependent term of `cSharp47` is
`(36e+16)/m`, decreasing in `m>0`) together with the `xiK`-antitone argument
(`xiK L W m`'s only `m`-term is `(m²)⁻¹`, decreasing in `m>0`).

Energy-dependent dependencies: `grid_phi_premises'N`, `plain_endpointN`, `scale_endpointN`,
`Step2.cond272_of_plainN` (`Step2Plain.lean`); `xZ_le_azumaMm_plainN`, `goodEvent_grid_plainN`,
`drift_point_le_heG_scalars_plainN` (`Step2Gauss.lean`); `highProb_grid_rowSetN`
(`Step2Close.lean`); `azumaMm_leN` (`GridGoodEvent.lean`); `cheb_grid_at_tauFar_plainN`
(`GridFarStop.lean`). Every other callee (`drift_sum_split`, `coef_le`, `far1_le`, `far2_le`,
`final_arith`, `second_conj`, `gridTauFar_le`, `gridTauFar_le_gridTau`, `lt_gridTauFar_imp`,
`min_firstHit_eq_of_at`, `jSMat_le_of_Agrid`, `H_eq_H_zero_of_eq`, `time_eq_time_zero_of_eq`,
`thrFar_le_thr'`, `mem_Icc_time`, `drift_of_goodSet_unmerged`, `step_gridK_le`, `gridK_ne_zero`,
`gridK_card_le`, `ae_gridAE`, …) is energy-free or a generic helper, applied at the concrete real
`E N` for whichever `N` is fixed at that point of the proof.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM Finset
open scoped NNReal ENNReal Matrix.Norms.L2Operator

namespace Sharp47

/-- **Eventual bounds on the constants**: `Step2.xiK … (mE (E N)).im`, `cNear`, `cFar` and
`456976 + 2·cSharp47 (E N) + 1` are at most `N^{δ/64}`, `N ≤ W²` and `exp((log W)^{3/4}) ≤ W`.
`Step2.xiK … (mE (E N)).im` and `cSharp47 (E N)` are bounded by the uniform κ-bounds
`Step2.xiK … mκ` and `cSharp47_κ := 16 + e + (36e+16)·mκ⁻¹`, with `mκ ≤ (mE (E N)).im` for every
`N`. -/
theorem eventually_constsN {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℕ → ℝ} {κ : ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Step2.xiK (B.L N) (B.W N) (mE (E N)).im ≤ (N : ℝ) ^ (δ / 64) ∧
      Lemma57.cNear (B.W N : ℝ) 1 ≤ (N : ℝ) ^ (δ / 64) ∧
      Lemma57.cFar (B.W N : ℝ) 1 ≤ (N : ℝ) ^ (δ / 64) ∧
      456976 + 2 * cSharp47 (E N) + 1 ≤ (N : ℝ) ^ (δ / 64) ∧
      (N : ℝ) ≤ (B.W N : ℝ) ^ 2 ∧
      Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) ≤ (B.W N : ℝ) := by
  have h64 : 0 < δ / 64 := by positivity
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'2 : κ' ≤ 2 := (min_le_right κ 1).trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκ0 : 0 < mκ := by positivity
  have hm : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hxiAnti : ∀ N, Step2.xiK (B.L N) (B.W N) (mE (E N)).im ≤
      Step2.xiK (B.L N) (B.W N) mκ := by
    intro N
    have hle : mκ ^ 2 ≤ (mE (E N)).im ^ 2 := by nlinarith [hm N, hmκ0.le]
    have hinv : ((mE (E N)).im ^ 2)⁻¹ ≤ (mκ ^ 2)⁻¹ := inv_anti₀ (by positivity) hle
    unfold Step2.xiK
    linarith
  have hcSle : ∀ N, cSharp47 (E N) ≤ 16 + Real.exp 1 + (36 * Real.exp 1 + 16) * mκ⁻¹ := by
    intro N
    unfold cSharp47
    have hinv : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκ0 (hm N)
    have h0 : (0 : ℝ) ≤ 36 * Real.exp 1 + 16 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv h0
    rw [div_eq_mul_inv]
    linarith
  filter_upwards [Step2FarInputs.eventually_xiK_le B mκ h64,
    DriftPt.eventually_cNear_cFar_le B h64,
    eventually_le_rpow (456976 + 2 * (16 + Real.exp 1 + (36 * Real.exp 1 + 16) * mκ⁻¹) + 1) h64,
    Step2.eventually_le_W_sq B,
    (Step2.tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 1 one_pos)]
    with N h1 h2 h3 h4 h5
  refine ⟨(hxiAnti N).trans h1, h2.1, h2.2, ?_, h4, ?_⟩
  · linarith [hcSle N]
  · simpa only [one_mul, Real.rpow_one] using h5

end Sharp47

set_option maxHeartbeats 2000000 in
-- a long chain of `set`-bound real quantities (as in `xZ_le_azumaMm_plainN`)
open Sharp47 in
/-- **The deterministic improvement on the grid**: given the grid Duhamel expansion of `Agrid` and
bounds on its initial value, drift, martingale and remainder terms, at each grid time `k`,
`jSMat ≤ cSharp47 N^{δ/2} ((η_s/η_{u_k})^2 + 1) < thrFar`. It uses `eventually_constsN` and
`grid_phi_premises'N`; the deterministic core (`drift_sum_split`, `coef_le`, `far1_le`,
`far2_le`, `final_arith`, `second_conj`) is applied at the concrete real `E N`. -/
theorem grid_sharp47_improveN {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℕ → ℝ}
    {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} {K : ℕ → ℕ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 90 * δ ≤ c) (hD : 64 ≤ D) :
    ∀ᶠ N : ℕ in atTop, ∀ Mi Mm : ℝ, 0 ≤ Mi → Mi ≤ (N : ℝ) ^ (δ / 8) → Mm ≤ (N : ℝ) ^ (δ / 8) →
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
        (drNear B (E N) s (δ / 96) N (time s t K N j)
          + drRes B (E N) s (δ / 96) N (time s t K N j)
              (2 * (etaT (E N) (time s t K N j))⁻¹ *
                ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N (time s t K N j)) *
                (B.W N : ℝ) ^ (-D))
          + drFar B (E N) s δ (δ / 4) (δ / 96) D (Step2.thr (E N) s δ N (time s t K N j)) N
              (time s t K N j)) *
          Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1))) →
      (∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B (E N) s t K N (j + 1) ω)) b‖ ≤
        Mm * ((etaT (E N) (s N) / etaT (E N) (time s t K N k)) ^ 2 + 1) *
          Step2.tT B (E N) N D (time s t K N k) (zdist (B.L N) (b 0 - b 1))) →
      (∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B (E N) s t K N (j + 1) ω)) b‖ ≤
        Step2.tT B (E N) N D (time s t K N k) (zdist (B.L N) (b 0 - b 1))) →
      (∀ j < k, ∀ b, ‖Rgrid B (E N) s t K N j ω b‖ ≤
        stepErr B (E N) N (time s t K N j) (time s t K N (j + 1)) (step s t K N)) →
      jSMat B.toDims (E N) D N (time s t K N k) (H B.toDims s t K N k ω)
        ≤ cSharp47 (E N) * (N : ℝ) ^ (δ / 2) *
            ((etaT (E N) (s N) / etaT (E N) (time s t K N k)) ^ 2 + 1)
      ∧ cSharp47 (E N) * (N : ℝ) ^ (δ / 2) *
            ((etaT (E N) (s N) / etaT (E N) (time s t K N k)) ^ 2 + 1)
          < thrFar (E N) s δ N (time s t K N k) := by
  filter_upwards [grid_phi_premises'N B hκ0 hE hs0 hst ht1 hc0 hreg0 hAc hδ0 hδ1 hδc hD,
    eventually_constsN B hκ0 hE hδ0]
    with N hF hC Mi Mm hMi0 hMix hMmx hK1 hΔR k hk ω hexp hinit hdrift hZ hY hRstep
  have hE2 : |E N| < 2 := by linarith [hE N]
  obtain ⟨hWe, hx1, -, -, hN2, hWL, hηt, hvF⟩ := hF
  obtain ⟨hΞy, hcNy, hcFy, hCy, hNW, hexW⟩ := hC
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
  have hm0 := mE_im_pos hE2
  have hm1 : (mE (E N)).im ≤ 1 := mE_im_le_one hE2
  set m := (mE (E N)).im with hm
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set v := time s t K N k with hv
  have hvt : v ≤ t N := time_le_t s t K N (hst N) hK1 hk
  have hsv : s N ≤ v := s_le_time s t K N (hst N) k
  have hv1 : v < 1 := hvt.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hsv
  set R := etaT (E N) (s N) / etaT (E N) v with hR
  have hRe : R = (1 - s N) / (1 - v) := Step2.etaT_ratio hE2 _ _
  have h1v : 0 < 1 - v := by linarith
  have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1v]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := le_trans (Real.one_le_exp (by norm_num)) hWe
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL1 : (1 : ℝ) ≤ B.L N := by exact_mod_cast B.one_le_L N
  have hLN : (B.L N : ℝ) ≤ N := by nlinarith
  have hWN : (B.W N : ℝ) ≤ N := by nlinarith
  have hηv0 : 0 < etaT (E N) v := Step2.etaT_pos' hE2 hv1
  have hηt0 : 0 < etaT (E N) (t N) := Step2.etaT_pos' hE2 (ht1 N)
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
    have hηw : 0 < etaT (E N) w := Step2.etaT_pos' hE2 hw1
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
    have hηs0 : 0 < etaT (E N) (s N) := Step2.etaT_pos' hE2 hs1
    calc R = etaT (E N) (s N) * (etaT (E N) v)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 1 * N := mul_le_mul hηs1 hηvN (inv_nonneg.2 hηv0.le) zero_le_one
      _ = N := one_mul _
  have hN8 : (N : ℝ) ^ δ = x ^ 8 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hN4 : (N : ℝ) ^ (2 * (δ / 4)) = x ^ 4 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hN2d : (N : ℝ) ^ (δ / 2) = x ^ 4 := by
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
  -- Ξ
  set Ξ := Step2.xiK (B.L N) (B.W N) m with hΞdef
  have hΞ0 : 0 ≤ Ξ := Step2.xiK_nonneg _ _ _
  have hy8 : y ≤ y ^ 8 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 8)
  have hΞx : Ξ ≤ x := hΞy.trans (hxy ▸ hy8)
  -- premises at `v`
  obtain ⟨hvA, hvα, hvε⟩ := hvF v ⟨hsv, hvt⟩
  have hA0 : 0 < B.scale (E N) N v := B.scale_pos' hE2 N hv0 hv1
  have hA1 : 1 ≤ B.scale (E N) N v := by
    have : 1 ≤ x ^ 17 * R ^ 10 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) (one_le_pow₀ hR1)
    linarith
  have hxA24 : x ^ 24 * R ^ 10 ≤ B.scale (E N) N v := by
    have h1 : x ^ 24 * R ^ 10 ≤ B.scale (E N) N v ^ ((3 : ℝ) / 7) := by
      rw [Real.inv_rpow hA0.le] at hvα
      have hp : 0 < B.scale (E N) N v ^ ((3 : ℝ) / 7) := Real.rpow_pos_of_pos hA0 _
      rw [inv_mul_le_iff₀ hp, mul_one] at hvα
      exact hvα
    refine h1.trans ?_
    calc B.scale (E N) N v ^ ((3 : ℝ) / 7) ≤ B.scale (E N) N v ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
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
  set cN1 := Lemma57.cNear (B.W N : ℝ) 1 with hcN1
  set cF1 := Lemma57.cFar (B.W N : ℝ) 1 with hcF1
  have hcN0 : 0 ≤ cN1 := Lemma57.cNear_nonneg hW1 one_pos
  have hcF0 : 0 ≤ cF1 := Lemma57.cFar_nonneg hW1 one_pos
  have hy16 : 456976 ≤ y := by
    have : 0 < cSharp47 (E N) := by unfold cSharp47; positivity
    linarith
  have hCN : Ξ * (64 * z ^ 3 * cN1) ≤ 4 * x ^ 4 := by
    rw [hxy]
    calc Ξ * (64 * z ^ 3 * cN1) ≤ y * (64 * y ^ 3 * y) := by gcongr
      _ = 4 * (16 * y ^ 5) := by ring
      _ ≤ 4 * (y ^ 27 * y ^ 5) := by
          gcongr
          calc (16 : ℝ) ≤ y := by linarith
            _ ≤ y ^ 27 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 27)
      _ = 4 * (y ^ 8) ^ 4 := by ring
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
  have h2cS : 2 * cSharp47 (E N) < x ^ 4 := by
    rw [hxy]
    calc 2 * cSharp47 (E N) < y := by linarith
      _ ≤ (y ^ 8) ^ 4 := by
          rw [← pow_mul]; simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 8 * 4)
  have hP1 := far1_le hΞ0 hcF0 hr0 hr3 hA0 hJv hxA24 hCF
  have hP2 := far2_le hΞ0 hr0 hr2 hA0 hx1 hR1 hJv hxA24 hC2
  rw [← hrv] at hP1 hP2
  have hP3 : Ξ * (8 * ((N : ℝ) ^ 20)⁻¹) ≤ x ^ 4 := by
    have hΞN : Ξ ≤ N := hΞy.trans hyN
    have h8 : 8 * (N : ℝ) ≤ (N : ℝ) ^ 20 := by
      have : (2 : ℝ) ^ 19 ≤ (N : ℝ) ^ 19 := pow_le_pow_left₀ (by norm_num) hN2' 19
      calc 8 * (N : ℝ) ≤ (N : ℝ) ^ 19 * N :=
            mul_le_mul_of_nonneg_right (by linarith) hN0.le
        _ = (N : ℝ) ^ 20 := by ring
    have hpos : 0 < (N : ℝ) ^ 20 := by positivity
    calc Ξ * (8 * ((N : ℝ) ^ 20)⁻¹) ≤ N * (8 * ((N : ℝ) ^ 20)⁻¹) :=
          mul_le_mul_of_nonneg_right hΞN (by positivity)
      _ = 8 * (N : ℝ) / (N : ℝ) ^ 20 := by ring
      _ ≤ 1 := by rw [div_le_one hpos]; exact h8
      _ ≤ x ^ 4 := one_le_pow₀ hx1
  -- the split drift hypothesis
  set P := Lemma57.cFar (B.W N : ℝ) 1 *
        (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) ^ ((3 : ℝ) / 2) *
        (√(B.scale (E N) N v))⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v)
      + 169 * (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) * (B.scale (E N) N v)⁻¹ *
        ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v) ^ ((3 : ℝ) / 2)
      + 8 * ((N : ℝ) ^ 20)⁻¹
      + Real.exp 1 * Step2.thr (E N) s δ N v ^ 2 * 36 * (B.scale (E N) N v)⁻¹ with hPdef
  set εW := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hεW
  have hεW0 : 0 ≤ εW := by have := Real.rpow_nonneg hW0.le (-D); positivity
  set Q := Real.exp 1 * Step2.thr (E N) s δ N v ^ 2 * εW with hQdef
  have hCN0 : 0 ≤ 64 * z ^ 3 * cN1 := by positivity
  have hP0 : 0 ≤ P := by
    have h1 : 0 ≤ (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) := by
      rw [hrv]; exact hr0
    have h2 : 0 ≤ (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v := by rw [hJv]; positivity
    have h3 : 0 ≤ (√(B.scale (E N) N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have h4 : 0 ≤ (B.scale (E N) N v)⁻¹ := inv_nonneg.2 hA0.le
    have h5 := Real.rpow_nonneg h1 ((3 : ℝ) / 2)
    have h6 := Real.rpow_nonneg h2 ((3 : ℝ) / 2)
    positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hdrift' : ∀ j < k, ∀ b, ‖Dgrid B (E N) s t K N j ω b‖ ≤
      ((64 * z ^ 3 * cN1) * ((etaT (E N) (time s t K N j))⁻¹ *
          (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3)
        + P * (etaT (E N) (time s t K N j))⁻¹ + Q) *
      Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)) := by
    intro j hj b
    have hjk : time s t K N j ≤ v := time_mono' s t K N (hst N) hj.le
    have hsj : s N ≤ time s t K N j := s_le_time s t K N (hst N) j
    have hj1 : time s t K N j < 1 := hjk.trans_lt hv1
    have hAj : B.scale (E N) N (time s t K N j) ≤ N := hscaleN _ ((hs0 N).trans hsj) hj1
    refine (hdrift j hj b).trans (mul_le_mul_of_nonneg_right ?_ (tailT_nonneg hW0.le _))
    exact coef_le B hE2 hδ1 (hs0 N) hsj hjk hv1 hN1' hW1 hLN hηvN hWD hexN hAj hJv6
  have hDr := drift_sum_split B hE2 (hs0 N) (hst N) (ht1 N) hK1 hk hWe hCN0 hP0 hQ0
    (fun j => Dgrid B (E N) s t K N j ω) hdrift'
  have hRs := rsum_le B hE2 (hs0 N) (hst N) (ht1 N) hK1 hk hN2 hWL hηt (by linarith : (0 : ℝ) ≤ D)
    hΔR (fun j => Rgrid B (E N) s t K N j ω) hRstep
  -- the initial term
  have hAuv0 : (B.W N : ℝ) * ellHat (B.L N) (v : ℂ) * ((1 - v) * m) ≤
      (B.W N : ℝ) * ellHat (B.L N) (time s t K N 0 : ℂ) * ((1 - time s t K N 0) * m) :=
    flowScale_antitoneOn hW0.le (B.L N) (E N)
      (Set.mem_Iic.2 ((time_mono' s t K N (hst N) (Nat.zero_le k)).trans hv1.le))
      (Set.mem_Iic.2 hv1.le) (time_mono' s t K N (hst N) (Nat.zero_le k))
  have hR' : (1 - time s t K N 0) / (1 - v) = R := by rw [hRe, time_zero]
  -- the pointwise bound on `A_k`
  set φ := Mi * R ^ 2 * Ξ
      + Ξ * ((64 * z ^ 3 * cN1) * (2 * m⁻¹ * R ^ 2) + P * (m⁻¹ * R ^ 2) + Q * R ^ 2)
      + Mm * (R ^ 2 + 1) + 1 + 1 with hφ
  have hAk : ∀ a, ‖Agrid B (E N) s t K N k ω a‖ ≤
      φ * Step2.tT B (E N) N D v (zdist (B.L N) (a 0 - a 1)) := by
    intro a
    have hI := Step2.norm_Uker_le_of_tail (B.three_le_L N) hm0 hm1
      (by rw [time_zero]; exact hs0 N) (time_mono' s t K N (hst N) (Nat.zero_le k))
      hv0 hv1 hWe hMi0 hAuv0 hinit a
    rw [hR'] at hI
    have hZa := hZ a
    have hYa := hY a
    have hDa := hDr a
    have hRa := hRs a
    rw [hexp a]
    have htri : ∀ x₁ x₂ x₃ x₄ x₅ : ℂ,
        ‖x₁ + x₂ + x₃ + x₄ + x₅‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ :=
      fun x₁ x₂ x₃ x₄ x₅ => by
        have h1 := norm_add_le (x₁ + x₂ + x₃ + x₄) x₅
        have h2 := norm_add_le (x₁ + x₂ + x₃) x₄
        have h3 := norm_add_le (x₁ + x₂) x₃
        have h4 := norm_add_le x₁ x₂
        linarith
    refine (htri _ _ _ _ _).trans ?_
    set T := Step2.tT B (E N) N D v (zdist (B.L N) (a 0 - a 1)) with hT
    have hI' : ‖Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (v : ℂ)
        (Agrid B (E N) s t K N 0 ω) a‖ ≤ Mi * R ^ 2 * Ξ * T := hI
    have e : φ * T = Mi * R ^ 2 * Ξ * T + Mm * (R ^ 2 + 1) * T + T
        + Ξ * ((64 * z ^ 3 * cN1) * (2 * m⁻¹ * R ^ 2) + P * (m⁻¹ * R ^ 2) + Q * R ^ 2) * T
        + T := by rw [hφ]; ring
    rw [e]
    linarith [hI', hZa, hYa, hDa, hRa]
  have hJ := jSMat_le_of_Agrid B hAk
  have hfin := final_arith (P1 := Lemma57.cFar (B.W N : ℝ) 1 *
        (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) ^ ((3 : ℝ) / 2) *
        (√(B.scale (E N) N v))⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v))
      (P2 := 169 * (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) * (B.scale (E N) N v)⁻¹ *
        ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N v) ^ ((3 : ℝ) / 2))
      (P3 := 8 * ((N : ℝ) ^ 20)⁻¹) (εW := εW)
      hx1 hR1 hΞ0 hΞx hm0 hMix hMmx hCN hP1 hP2 hP3 hthr hA0 hvA hεW0 hvε
  refine ⟨?_, ?_⟩
  · rw [hN2d]
    unfold cSharp47
    exact hJ.trans (by rw [hφ]; linarith [hfin])
  · -- second conjunct, uniform in `k`
    rw [hN2d]
    have hcS0 : 0 < cSharp47 (E N) := by unfold cSharp47; positivity
    have hthrF : thrFar (E N) s δ N v = x ^ 8 * R ^ ((13 : ℝ) / 4) := by rw [thrFar, hN8]
    rw [hthrF]
    exact second_conj hR1 (by positivity) h2cS hcS0


namespace Sharp47

/-- **`cSharp47 N^{δ/2} ((η_s/η_v)^2 + 1) < thrFar(v)` for all `v ∈ [s, 1)`, eventually.** Same
κ-bound as `eventually_constsN`. -/
theorem eventually_lev_ltN {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {s : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, s N ≤ v → v < 1 →
      cSharp47 (E N) * (N : ℝ) ^ (δ / 2) * ((etaT (E N) (s N) / etaT (E N) v) ^ 2 + 1)
        < thrFar (E N) s δ N v := by
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'2 : κ' ≤ 2 := (min_le_right κ 1).trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκ0 : 0 < mκ := by positivity
  have hm : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hcSle : ∀ N, cSharp47 (E N) ≤ 16 + Real.exp 1 + (36 * Real.exp 1 + 16) * mκ⁻¹ := by
    intro N
    unfold cSharp47
    have hinv : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκ0 (hm N)
    have h0 : (0 : ℝ) ≤ 36 * Real.exp 1 + 16 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv h0
    rw [div_eq_mul_inv]
    linarith
  filter_upwards [eventually_le_rpow (2 * (16 + Real.exp 1 + (36 * Real.exp 1 + 16) * mκ⁻¹) + 1)
      (by positivity : (0 : ℝ) < δ / 2), eventually_ge_atTop 1] with N hC hN1 v hsv hv1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set x := (N : ℝ) ^ (δ / 8) with hx
  have hN2d : (N : ℝ) ^ (δ / 2) = x ^ 4 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hN8 : (N : ℝ) ^ δ = x ^ 8 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hEN : |E N| < 2 := by linarith [hE N]
  have hR1 : 1 ≤ etaT (E N) (s N) / etaT (E N) v := by
    rw [Step2.etaT_ratio hEN, le_div_iff₀ (by linarith)]; linarith
  have hcS0 : 0 < cSharp47 (E N) := by
    unfold cSharp47; have := mE_im_pos hEN; positivity
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  rw [hN2d] at hC ⊢
  rw [thrFar, hN8]
  have h2cS : 2 * cSharp47 (E N) < x ^ 4 := by linarith [hcSle N]
  exact second_conj hR1 hx0 h2cS hcS0

/-- **The good event `goodEventSharp47` fails with probability at most `N^{-D₁}`**, eventually.
No new energy-dependent constant (its callees are `goodEvent_grid_plainN`,
`highProb_grid_rowSetN`, `cheb_grid_at_tauFar_plainN`, `Step2.cond272_of_plainN`). -/
theorem goodEventSharp47_probN (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {D δ : ℝ} (hD : 64 ≤ D) (hδ0 : 0 < δ) (hδ₀ : δ ≤ min (c / 90) 1) (u : ∀ N, TimeIcc s t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) (goodEventSharp47 d (E N) D δ s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N)ᶜ
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  intro D₁ hD₁
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hδc : δ ≤ c / 90 := hδ₀.trans (min_le_left _ _)
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE2 hst ht1 hreg0
  set uR : ℕ → ℝ := fun N => (u N : ℝ) with huR
  have hsu : ∀ N, s N ≤ uR N := fun N => (u N).2.1
  have hut : ∀ N, uR N ≤ t N := fun N => (u N).2.2
  have hu1 : ∀ N, uR N < 1 := fun N => (hut N).trans_lt (ht1 N)
  set K : ℕ → ℕ := gridK D (D₁ + 2) with hK
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D (D₁ + 2)
  have hCK : 0 ≤ CK D (D₁ + 2) := by unfold CK; linarith
  have HG := goodEvent_grid_plainN (d := d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc
    (by linarith : (60 : ℝ) ≤ D) (by positivity : (0 : ℝ) < δ / 32)
    (by positivity : (0 : ℝ) < δ / 4)
    (by positivity : (0 : ℝ) < δ / 96) (by positivity : (0 : ℝ) < δ / 96)
    (by positivity : (0 : ℝ) < δ / 192) hsu hut (D₁ + 1) (by linarith)
  rw [show D₁ + 1 + 1 = D₁ + 2 by ring] at HG
  have HR := highProb_grid_rowSetN d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc (δ / 192)
    (by positivity) hsu hut K hK0 (by linarith : (0 : ℝ) ≤ CK D (D₁ + 2) + 2)
    (gridK_card_le hCK)
  have HY := cheb_grid_at_tauFar_plainN (d := d) hE2 hs0 hst ht1 hc0 hAc
    (by linarith : (0 : ℝ) ≤ D)
    δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) hsu hut (D₁ + 2) (by linarith)
  filter_upwards [HG, HR (D₁ + 1) (by linarith), HY, eventually_ge_atTop 3] with N hG hR hY hN3
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  set Ae : Set (Ωg d) := {ω | ¬ (s N < uR N → GridAE d (E N) s uR K N ω)} with hAe
  have hAe0 : Pg d Ae = 0 := by
    refine ae_iff.1 ?_
    by_cases hlt : s N < uR N
    · filter_upwards [ae_gridAE d (hE2 N) (hs0 N) hlt (hu1 N) (hK0 N)] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hlt
  set G := goodEventGrid d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s uR K
        (2 * D + 2) (2 * D + 2) N with hGdef
  set R := {ω | ∀ k : Fin (K N + 1), H d s uR K N k ω ∈
        rowSet d (E N) N (time s uR K N k) ((band d).ell N (s N)) (δ / 192)} with hRdef
  set Y := {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D
            (time s uR K N
              (gridTauFar d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s uR K N ω))
            (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range
                (gridTauFar d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s uR K N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s uR K N (j + 1) : ℂ)
                (time s uR K N
                  (gridTauFar d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s uR K N ω) :
                  ℂ)
                (Yvec (band d) (E N) s uR K N (j + 1) ω)) a‖} with hYdef
  have hsub : (goodEventSharp47 d (E N) D δ s uR K N)ᶜ ⊆ ((Gᶜ ∪ Rᶜ) ∪ Ae) ∪ Y := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨⟨⟨hGω, hRω⟩, hAω⟩, hYω⟩ := hcon
    apply hω
    refine ⟨⟨⟨hGω, hRω⟩, fun h => ?_⟩, fun a => ?_⟩
    · by_contra hn; exact hAω (fun himp => hn (himp h))
    · by_contra hn; exact hYω ⟨a, not_lt.1 hn⟩
  have p1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D₁ + 1)) := Real.rpow_nonneg hN0.le _
  have p2 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D₁ + 2)) := Real.rpow_nonneg hN0.le _
  have hfin : (N : ℝ) ^ (-(D₁ + 1)) + (N : ℝ) ^ (-(D₁ + 1)) + (N : ℝ) ^ (-(D₁ + 2))
      ≤ (N : ℝ) ^ (-D₁) := by
    have e1 : (N : ℝ) ^ (-(D₁ + 1)) = (N : ℝ) ^ (-D₁) * (N : ℝ)⁻¹ := by
      rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have e2 : (N : ℝ) ^ (-(D₁ + 2)) = (N : ℝ) ^ (-D₁) * (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      rw [show -(D₁ + 2) = -D₁ + (-1) + (-1) by ring, Real.rpow_add hN0, Real.rpow_add hN0,
        Real.rpow_neg_one]
    rw [e1, e2]
    have h0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have hi : (N : ℝ)⁻¹ ≤ 1 / 3 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN3'
    have hi0 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN0.le
    have h1 := mul_le_mul_of_nonneg_left hi h0
    have h2 : (N : ℝ) ^ (-D₁) * (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-D₁) * (N : ℝ)⁻¹ := by
      have : (N : ℝ)⁻¹ ≤ 1 := hi.trans (by norm_num)
      exact mul_le_of_le_one_right (mul_nonneg h0 hi0) this
    linarith
  calc (Pg d) (goodEventSharp47 d (E N) D δ s uR K N)ᶜ ≤ Pg d (((Gᶜ ∪ Rᶜ) ∪ Ae) ∪ Y) :=
        measure_mono hsub
    _ ≤ Pg d ((Gᶜ ∪ Rᶜ) ∪ Ae) + Pg d Y := measure_union_le _ _
    _ ≤ (Pg d (Gᶜ ∪ Rᶜ) + Pg d Ae) + Pg d Y := by gcongr; exact measure_union_le _ _
    _ ≤ ((Pg d Gᶜ + Pg d Rᶜ) + Pg d Ae) + Pg d Y := by gcongr; exact measure_union_le _ _
    _ ≤ ((ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))) + 0)
          + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 2))) := by
        rw [hAe0]; exact add_le_add (add_le_add (add_le_add hG hR) le_rfl) hY
    _ = ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)) + (N : ℝ) ^ (-(D₁ + 1)) + (N : ℝ) ^ (-(D₁ + 2))) := by
        rw [add_zero, ENNReal.ofReal_add (by positivity) p2, ENNReal.ofReal_add p1 p1]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := ENNReal.ofReal_le_ofReal hfin

end Sharp47

set_option maxHeartbeats 2000000 in
-- the bootstrap carries many event components and grid facts at once
set_option linter.unusedVariables false in
open Sharp47 in
/-- **The sharp bound on the good event**: `goodEventSharp47` fails with probability at most
`N^{-D₁}`, and on it `gridTauFar = gridK`, at every grid time `jSMat < thrFar` and the grid
process lies in `goodSet`, and at the endpoint `jSMat ≤ cSharp47 N^{δ/2} ((η_s/η_u)^2 + 1)`. It
uses `grid_sharp47_improveN`, `eventually_lev_ltN` and `azumaMm_leN`. -/
theorem sharp47_grid_plainN (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {D δ : ℝ} (hD : 64 ≤ D) (hδ0 : 0 < δ) (hδ₀ : δ ≤ min (c / 90) 1) (u : ∀ N, TimeIcc s t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) (goodEventSharp47 d (E N) D δ s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N)ᶜ
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) ∧
      ∀ ω ∈ goodEventSharp47 d (E N) D δ s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N,
        gridTauFar d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s
            (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N ω = gridK D (D₁ + 2) N ∧
        (∀ k ≤ gridK D (D₁ + 2) N,
          jSMat d (E N) D N (time s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N k)
              (H d s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N k ω)
            < thrFar (E N) s δ N (time s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N k) ∧
          H d s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N k ω ∈
            goodSet d (E N) N (time s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N k)
              ((band d).ell N (s N)) (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) D) ∧
        jSMat d (E N) D N (u N : ℝ)
            (H d s (fun N => (u N : ℝ)) (gridK D (D₁ + 2)) N (gridK D (D₁ + 2) N) ω)
          ≤ cSharp47 (E N) * (N : ℝ) ^ (δ / 2) *
              ((etaT (E N) (s N) / etaT (E N) (u N : ℝ)) ^ 2 + 1) := by
  intro D₁ hD₁
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hδc : δ ≤ c / 90 := hδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ₀.trans (min_le_right _ _)
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE2 hst ht1 hreg0
  set uR : ℕ → ℝ := fun N => (u N : ℝ) with huR
  have hsu : ∀ N, s N ≤ uR N := fun N => (u N).2.1
  have hut : ∀ N, uR N ≤ t N := fun N => (u N).2.2
  have hu1 : ∀ N, uR N < 1 := fun N => (hut N).trans_lt (ht1 N)
  set K : ℕ → ℕ := gridK D (D₁ + 2) with hK
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D (D₁ + 2)
  have hεδ : 2 * (δ / 4) ≤ δ := by linarith
  have hΔ10 : ∀ᶠ N : ℕ in atTop, step s uR K N ≤ (N : ℝ) ^ (-(D + 10)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact (step_gridK_le hN1 (by linarith [hs0 N, hut N, ht1 N])).trans
      (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith))
  have hstepR : ∀ᶠ N : ℕ in atTop, step s uR K N ≤ (N : ℝ) ^ (-(2 * D + 76)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact (step_gridK_le hN1 (by linarith [hs0 N, hut N, ht1 N])).trans
      (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith))
  have hcore := grid_sharp47_improveN (band d) (K := K) hκ0 hEκ hs0 hsu hu1 hc0
    (plain_endpointN (band d) hE2 ht1 hreg0 u) (scale_endpointN (band d) ht1 hAc u) hδ0 hδ1
    (by linarith : 90 * δ ≤ c) hD
  have hScal := drift_point_le_heG_scalars_plainN (band d) hE2 hs0 ht1 hc0 hreg0 hAc hδ0.le hδc hεδ
    (by linarith : (4 : ℝ) ≤ D)
  filter_upwards [goodEventSharp47_probN d hκ0 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hD hδ0 hδ₀ u D₁ hD₁,
    hcore, hScal, hstepR,
    xZ_le_azumaMm_plainN (d := d) hE2 hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc
      (by positivity : (0 : ℝ) ≤ δ / 4) hεδ (by linarith : (60 : ℝ) ≤ D)
      hsu hut K hK0 hΔ10 (by linarith : 2 * D ≤ 2 * D + 2) (by linarith : 2 * D ≤ 2 * D + 2)
      (τ₁ := δ / 32),
    azumaMm_leN (d := d) hκ0 hEκ hδ0 (le_refl (δ / 32)),
    eventually_lev_ltN (s := s) hκ0 hEκ hδ0, eventually_ge_atTop 1]
    with N hprob hcN hScalN hΔR hxZ hMm hlev hN1
  refine ⟨hprob, ?_⟩
  intro ω hω
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨_, hW8, hLW, hNW, hlog, hv⟩ := hScalN
  obtain ⟨⟨⟨hGω, hRω⟩, hAω⟩, hYω⟩ := hω
  obtain ⟨⟨⟨hZall, _hYold⟩, hGall⟩, hinit, _hJ0⟩ := hGω
  set τ' := gridTauFar d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s uR K N ω with hτ'
  have hτK : τ' ≤ K N := gridTauFar_le _ _ _ _ _ _ _ _ _ _ _ _ ω
  have hτle : τ' ≤ gridTau d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s uR K N ω :=
    gridTauFar_le_gridTau (hE2 N) (hsu N) (hu1 N) ω
  have htime : ∀ j ≤ K N, s N ≤ time s uR K N j ∧ time s uR K N j < 1 := by
    intro j hj
    have hm := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j)
    rw [time_zero] at hm
    have h1 : time s uR K N j ≤ uR N := by
      rw [← time_last s uR K N (hK0 N)]; exact time_mono_of_le (hsu N) hj
    exact ⟨hm, h1.trans_lt (hu1 N)⟩
  -- `Z` at `τ′` only: the all-`k` Azuma component at `k = τ′ ≤ gridTau`
  have hZ : ∀ b : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range τ', Uker (d.L N) (fun _ => (1 : ℂ)) (time s uR K N (j + 1) : ℂ)
          (time s uR K N τ' : ℂ) (Zvec (band d) (E N) s uR K N (j + 1) ω)) b‖ ≤
        azumaMm d (E N) δ (δ / 32) N *
            ((etaT (E N) (s N) / etaT (E N) (time s uR K N τ')) ^ 2 + 1) *
          Step2.tT (band d) (E N) N D (time s uR K N τ') (zdist (d.L N) (b 0 - b 1)) := by
    intro b
    have h1 := hZall τ' hτK b
    rw [min_eq_left hτle] at h1
    exact h1.le.trans (hxZ τ' hτK b)
  -- `Y` at `τ′` only: the fourth component of `goodEventSharp47`
  have hY : ∀ b : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range τ', Uker (d.L N) (fun _ => (1 : ℂ)) (time s uR K N (j + 1) : ℂ)
          (time s uR K N τ' : ℂ) (Yvec (band d) (E N) s uR K N (j + 1) ω)) b‖ ≤
        Step2.tT (band d) (E N) N D (time s uR K N τ') (zdist (d.L N) (b 0 - b 1)) :=
    fun b => (hYω b).le
  -- the output bound at `τ′`
  have hat : jSMat d (E N) D N (time s uR K N τ') (H d s uR K N τ' ω) ≤
        cSharp47 (E N) * (N : ℝ) ^ (δ / 2) *
            ((etaT (E N) (s N) / etaT (E N) (time s uR K N τ')) ^ 2 + 1) ∧
      cSharp47 (E N) * (N : ℝ) ^ (δ / 2) *
          ((etaT (E N) (s N) / etaT (E N) (time s uR K N τ')) ^ 2 + 1)
        < thrFar (E N) s δ N (time s uR K N τ') := by
    rcases lt_or_eq_of_le (hsu N) with hlt | heq
    · obtain ⟨hexp, hRst⟩ := hAω hlt
      -- drift for `j < τ′`: `drift_of_goodSet_unmerged` at `Λ = thr`, `jS < thrFar ≤ thr`
      have hdrift : ∀ j < τ', ∀ b : LoopArg ((band d).L N) 2,
          ‖Dgrid (band d) (E N) s uR K N j ω b‖ ≤
            (drNear (band d) (E N) s (δ / 96) N (time s uR K N j)
              + drRes (band d) (E N) s (δ / 96) N (time s uR K N j)
                  (2 * (etaT (E N) (time s uR K N j))⁻¹ *
                    ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr (E N) s δ N (time s uR K N j)) *
                    ((band d).W N : ℝ) ^ (-D))
              + drFar (band d) (E N) s δ (δ / 4) (δ / 96) D
                  (Step2.thr (E N) s δ N (time s uR K N j)) N (time s uR K N j)) *
            Step2.tT (band d) (E N) N D (time s uR K N j) (zdist ((band d).L N) (b 0 - b 1)) := by
        intro j hj b
        have hjK : j ≤ K N := hj.le.trans hτK
        obtain ⟨h1, h2⟩ := lt_gridTauFar_imp hj
        obtain ⟨ht0, ht1'⟩ := htime j hjK
        have hjS : jSMat d (E N) D N (time s uR K N j) (H d s uR K N j ω) ≤
            Step2.thr (E N) s δ N (time s uR K N j) :=
          (h1.trans_le (thrFar_le_thr' (hE2 N) ht0 ht1')).le
        have hjR := hRω ⟨j, Nat.lt_succ_of_le hjK⟩
        have hmem := mem_Icc_time s uR K N j (hs0 N) (hsu N) hjK
        obtain ⟨hJA, hDreg⟩ := hv (time s uR K N j) hmem.1 (hmem.2.trans (hut N))
        rw [show δ / 192 = δ / 96 / 2 by ring] at h2 hjR
        have h := drift_of_goodSet_unmerged d (hE2 N) hN1' (hs0 N) ht0 ht1' hδ0.le
          (by positivity : (0 : ℝ) ≤ δ / 4) hεδ (by positivity : (0 : ℝ) ≤ δ / 96)
          (by linarith : 8 + 2 * (δ / 96) ≤ D) hW8 hLW hNW hlog hJA hDreg h2 hjR hjS le_rfl b
        rw [mul_one] at h
        exact h
      exact hcN ((N : ℝ) ^ (δ / 16)) (azumaMm d (E N) δ (δ / 32) N) (Real.rpow_nonneg hN0.le _)
        (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)) hMm
        (Nat.one_le_iff_ne_zero.2 (hK0 N)) hΔR τ' hτK ω (hexp τ' hτK) hinit hdrift hZ hY
        (fun j hj b => hRst j (lt_of_lt_of_le hj hτK) b)
    · -- degenerate grid `s N = u N`: every grid point is the initial one
      refine ⟨?_, hlev _ (htime τ' hτK).1 (htime τ' hτK).2⟩
      have hJ0 := jSMat_le_of_Agrid (band d) hinit
      rw [H_eq_H_zero_of_eq d heq, time_eq_time_zero_of_eq heq τ']
      refine hJ0.trans ?_
      have hcS : 16 ≤ cSharp47 (E N) := by
        unfold cSharp47; have := mE_im_pos (hE2 N); have := Real.exp_pos 1
        have : 0 ≤ (36 * Real.exp 1 + 16) / (mE (E N)).im := by positivity
        linarith
      have hR2 : 1 ≤ (etaT (E N) (s N) / etaT (E N) (time s uR K N 0)) ^ 2 + 1 := by
        have := sq_nonneg (etaT (E N) (s N) / etaT (E N) (time s uR K N 0)); linarith
      have h16 : (N : ℝ) ^ (δ / 16) ≤ (N : ℝ) ^ (δ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow hN1' (by positivity)
      calc (N : ℝ) ^ (δ / 16) + 1 ≤ 16 * (N : ℝ) ^ (δ / 2) := by linarith
        _ ≤ cSharp47 (E N) * (N : ℝ) ^ (δ / 2) * 1 := by rw [mul_one]; gcongr
        _ ≤ cSharp47 (E N) * (N : ℝ) ^ (δ / 2) *
              ((etaT (E N) (s N) / etaT (E N) (time s uR K N 0)) ^ 2 + 1) := by
            gcongr
  -- `min_firstHit_eq_of_at` with the level `j ↦ thrFar(u_j)` gives `τ′ = K`
  have hτeq : τ' = K N :=
    min_firstHit_eq_of_at
      (fun j (ω : Ωg d) => jSMat d (E N) D N (time s uR K N j) (H d s uR K N j ω))
      (fun j (ω : Ωg d) => (goodSet d (E N) N (time s uR K N j) ((band d).ell N (s N)) (δ / 32)
        (δ / 4) (δ / 96) (δ / 96) (δ / 192) D)ᶜ.indicator (fun _ => (1 : ℝ)) (H d s uR K N j ω))
      (fun j => thrFar (E N) s δ N (time s uR K N j)) (1 / 2) (K N)
      (fun j hj => by
        rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hGall ⟨j, Nat.lt_succ_of_le hj⟩))]
        norm_num)
      (hat.1.trans_lt hat.2)
  refine ⟨hτeq, fun k hk => ⟨?_, hGall ⟨k, Nat.lt_succ_of_le hk⟩⟩, ?_⟩
  · rcases lt_or_eq_of_le hk with hlt | heq
    · exact (lt_gridTauFar_imp (hτeq ▸ hlt : k < τ')).1
    · subst heq; rw [← hτeq]; exact hat.1.trans_lt hat.2
  · have := hat.1
    rw [hτeq, time_last s uR K N (hK0 N)] at this
    exact this

namespace Sharp47

section CompatN

end CompatN

end Sharp47

end RBM.Gauss.Grid

end
