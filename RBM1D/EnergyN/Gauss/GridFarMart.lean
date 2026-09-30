/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarMart
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.Flow.EnergyUniform
import RBM1D.Flow.Scales

/-!
# The far-field martingale on the grid at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: conditional sub-Gaussian bounds for
the stopped far-field martingale increments
(`RBM.Gauss.Grid.FarMart.hsubG_gridTauFar_plainN`), the bound on the sum of their variance
proxies (`RBM.Gauss.Grid.farQV_sum_leN`), and the resulting high-probability bound on the
far-field martingale (`RBM.Gauss.Grid.highProb_farMart_grid_plainN`).

## The external `κ`

The constants of `farQV_sum_leN` involve `(mE (E N)).im`, inside
`Step2FarInputs.eventually_xiK_le` and in `65536/(mE (E N)).im`, and must be fixed before the
`∀ᶠ N`. The theorem uses the uniform `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N`
(`κ' := min κ 1`, `mE_im_ge`, `Flow/Scales.lean`). `Step2.xiK L W m` is antitone in `m > 0` (its
only `m`-dependent term is `(m²)⁻¹`, `Hierarchy/Step2.lean`), so
`xiK … (mE (E N)).im ≤ xiK … mκ` (proved inline, as in `GridGoodEvent.lean`);
`eventually_xiK_le (band d) mκ` (`Step2FarInputs.lean`, `E`-free) is then applied, and
`65536/(mE (E N)).im ≤ 65536/mκ` follows the same way. Constant: `65536/mκ`. Neither
`hsubG_gridTauFar_plainN` nor `highProb_farMart_grid_plainN` fixes an energy-dependent constant:
the former only calls `thr_le_sqrtN_plainN`, and the latter only calls the other two.

## Private helpers

The proofs of `hsubG_gridTauFar_plainN` and `farQV_sum_leN` use nine `private` helpers of this
file: `v_Ab_le_far`, `diagFarRate_mono`, `diagNearRate_nonneg'`, `diagFarRate_nonneg'`,
`nearEpsilon_nonneg'`, `quadVar_step_le_split`, `farRate_point_le`, `farQV_assembly`,
`leak_absorb`. Five are energy-free real/`Band`-level facts, `quadVar_step_le_split` takes a
plain `E : ℝ` and is applied at `E N`, and `farRate_point_le`/`farQV_assembly`/`leak_absorb` are
pure real-arithmetic lemmas with no `E` or `N`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {d : Dims}

namespace FarMart

/-! ## The far `v_Ab` bound (`v_Ab_le` with `qv_conv_le_far`) -/

variable {N : ℕ}

private theorem v_Ab_le_far
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (hL : 3 ≤ d.L N) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u vt : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ vt)
    (hv1 : vt < 1) {W D Qn Qf : ℝ} (hW : Real.exp 1 ≤ W) (hQn : 0 ≤ Qn) (hQf : 0 ≤ Qf)
    (hAuv : W * ellHat (d.L N) (vt : ℂ) * ((1 - vt) * m)
        ≤ W * ellHat (d.L N) (u : ℂ) * ((1 - u) * m))
    (b : LoopArg (d.L N) 2)
    (hb : 6 * ellStar W (ellHat (d.L N) (vt : ℂ)) ≤ (zdist (d.L N) (b 0 - b 1) : ℝ))
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hqv : ∀ a : LoopArg (d.L N) 2, quadVar d N (Φ a) M
        ≤ (Qn * (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤ 4 * ellStar W (ellHat (d.L N) (u : ℂ))
                  then 1 else 0) + Qf) *
          tailT W (ellHat (d.L N) (u : ℂ)) ((1 - u) * m) D (zdist (d.L N) (a 0 - a 1)) ^ 2) :
    v N (∑ a : LoopArg (d.L N) 2,
        ((∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)).re : ℂ) • gradMat (Φ a) M)
      ≤ (√Qn * tailT W (ellHat (d.L N) u) ((1 - u) * m) D 0 *
            (128 * Real.exp 3 * ((1 - u) / (1 - vt)) ^ 2 *
              Real.exp (-(ellStar W (ellHat (d.L N) vt) / ellHat (d.L N) vt / 2)))
          + √Qf * ((1 - u) / (1 - vt)) ^ 2 * Step2.xiK (d.L N) W m *
              tailT W (ellHat (d.L N) vt) ((1 - vt) * m) D (zdist (d.L N) (b 0 - b 1))) ^ 2 := by
  classical
  set r : LoopArg (d.L N) 2 → ℝ :=
    fun a => (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)).re with hr_def
  set A : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ := fun a => gradMat (Φ a) M with hA_def
  have hsum_eq : (∑ a : LoopArg (d.L N) 2,
      ((∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)).re : ℂ) • gradMat (Φ a) M)
      = ∑ a : LoopArg (d.L N) 2, (r a : ℂ) • A a := rfl
  rw [hsum_eq, v_sum_eq]
  have hker : ∀ a : LoopArg (d.L N) 2,
      (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)) = (r a : ℂ) := by
    intro a
    obtain ⟨ra, _hra0, hraeq⟩ := Uker_one_nonneg hL hu0 huv hv1 b a
    have hre : r a = ra := by rw [hr_def]; simp only [hraeq, Complex.ofReal_re]
    rw [hre, hraeq]
  set EE : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℂ :=
    fun a a' => (vB N (A a) (A a') : ℂ) with hEE_def
  set R : LoopArg (d.L N) 2 → ℝ := fun a => quadVar d N (Φ a) M with hR_def
  have hR0 : ∀ a, 0 ≤ R a := fun a => quadVar_nonneg (Φ a) M
  have hREq : ∀ a, R a = v N (A a) := by
    intro a
    rw [hR_def, hA_def]
    exact (v_gradMat_eq_quadVar (hΦ a) (hReal a) hM).symm
  have hEE : ∀ a a' : LoopArg (d.L N) 2, ‖EE a a'‖ ≤ Real.sqrt (R a) * Real.sqrt (R a') := by
    intro a a'
    rw [hEE_def]
    have h1 : ‖(vB N (A a) (A a') : ℂ)‖ = |vB N (A a) (A a')| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hREq a, hREq a']
    exact abs_vB_le N (A a) (A a')
  have hqR : ∀ a, R a ≤ (Qn * (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
      4 * ellStar W (ellHat (d.L N) (u : ℂ)) then 1 else 0) + Qf) *
        tailT W (ellHat (d.L N) (u : ℂ)) ((1 - u) * m) D (zdist (d.L N) (a 0 - a 1)) ^ 2 + 0 :=
    fun a => by rw [add_zero]; exact hqv a
  have hconv := qv_conv_le_far hL hm0 hm1 hu0 huv hv1 hW hQn hQf le_rfl hAuv hR0 hqR hEE b hb
  rw [Real.sqrt_zero, zero_mul, add_zero] at hconv
  have hnonneg : 0 ≤ (∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
      r a * r a' * vB N (A a) (A a') : ℝ) := by
    have h := v_nonneg N (∑ a : LoopArg (d.L N) 2, (r a : ℂ) • A a)
    rwa [v_sum_eq] at h
  have hcast : ((∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
      r a * r a' * vB N (A a) (A a') : ℝ) : ℂ)
      = ∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
          (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)) *
          (starRingEnd ℂ) (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a' i))
          * EE a a' := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [hker a, hker a', Complex.conj_ofReal]
  have heq2 : (∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
      r a * r a' * vB N (A a) (A a') : ℝ)
      = ‖∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
          (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)) *
          (starRingEnd ℂ) (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a' i))
          * EE a a'‖ := by
    rw [← hcast, Complex.norm_of_nonneg hnonneg]
  rw [heq2]
  exact hconv

/-! ## The split one-step QV bound (`quadVar_step_le` with the near indicator kept) -/

private theorem diagFarRate_mono {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ)
    {ℓu ηu D J J' Smax : ℝ} (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hW1 : 1 ≤ (B.W N : ℝ)) (hJ : 0 ≤ J)
    (hJJ' : J ≤ J') :
    QVEndpoint.diagFarRate B N ℓu ηu D J Smax
      ≤ QVEndpoint.diagFarRate B N ℓu ηu D J' Smax := by
  have hcfar := Lemma57.cFar2_nonneg hW1 hℓu
  have hsq : (2 * J) ^ 2 ≤ (2 * J') ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hcube : (2 * J) ^ 3 ≤ (2 * J') ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hc1 : (0 : ℝ) ≤ 2 * ηu⁻¹ *
      (Lemma57.cFar2 (B.W N : ℝ) ℓu * ((B.W N : ℝ) * ℓu * ηu * (2 * Real.sqrt Smax))) := by
    positivity
  have hc23 : (0 : ℝ) ≤ 2 * ηu⁻¹ * 72 * ((B.W N : ℝ) * ℓu * ηu)⁻¹
      + 4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) := by
    have : (0 : ℝ) ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
    positivity
  have hexpand : ∀ x : ℝ, QVEndpoint.diagFarRate B N ℓu ηu D x Smax
      = (2 * ηu⁻¹ * (Lemma57.cFar2 (B.W N : ℝ) ℓu *
            ((B.W N : ℝ) * ℓu * ηu * (2 * Real.sqrt Smax)))) * (2 * x) ^ 2
        + (2 * ηu⁻¹ * 72 * ((B.W N : ℝ) * ℓu * ηu)⁻¹
            + 4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)) * (2 * x) ^ 3 := by
    intro x; unfold QVEndpoint.diagFarRate; ring
  rw [hexpand, hexpand]
  nlinarith [mul_le_mul_of_nonneg_left hsq hc1, mul_le_mul_of_nonneg_left hcube hc23]

private theorem diagNearRate_nonneg' {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ)
    {ℓu ℓs ηu : ℝ} (hW1 : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) :
    0 ≤ QVEndpoint.diagNearRate B N ℓu ℓs ηu := by
  unfold QVEndpoint.diagNearRate
  have := Lemma57.cNear2_nonneg hW1 hℓu
  positivity

private theorem diagFarRate_nonneg' {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ)
    {ℓu ηu D J Smax : ℝ} (hW1 : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hJ : 0 ≤ J) :
    0 ≤ QVEndpoint.diagFarRate B N ℓu ηu D J Smax := by
  unfold QVEndpoint.diagFarRate
  have hcfar := Lemma57.cFar2_nonneg hW1 hℓu
  have : (0 : ℝ) ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
  positivity

private theorem nearEpsilon_nonneg' {W L ℓu ηu D J : ℝ} (hW : 0 ≤ W) (hL : 0 ≤ L) :
    0 ≤ EEDef.nearEpsilon W L ℓu ηu D J := by
  unfold EEDef.nearEpsilon; positivity

/-- **Split one-step QV bound**: `quadVar_step_le` (GridQVStep:775) keeping the near indicator,
moved from `4ℓ*_{u_j}` to `4ℓ*_{u_{j+1}}`. The output is `qv_conv_le_far`'s `hR` shape with
`Qn = 2N^τ(near + 2nε(J))`, `Qf = 2N^τ far(J) + 2Csh²Δ²W^{2D}`, `Qr = 0`. -/
private theorem quadVar_step_le_split (N : ℕ) {E : ℝ} (hE : |E| < 2)
    {uj Δ : ℝ} (huj0 : 0 ≤ uj) (hΔ : 0 ≤ Δ) (hu'1 : uj + Δ < 1)
    {D J' J τ ℓs : ℝ} (hℓs : 0 < ℓs) (hJ'0 : 0 ≤ J') (hJ'J : J' ≤ J)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hqv : ∀ a : LoopArg (d.L N) 2,
      Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun (band d) E N uj M' Step2.sigPM a) M
        ≤ (N : ℝ) ^ τ * QVEndpoint.diagShape' (band d) N
            ((band d).ell N uj) ℓs (etaT E uj) D J'
            (EarlyQVRateEv.sDet (band d) E N uj ℓs)
            (EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
              ((band d).ell N uj) (etaT E uj) D J') a) :
    ∀ a : LoopArg (d.L N) 2,
      Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun (band d) E N (uj + Δ) M' Step2.sigPM a) M
        ≤ (2 * (N : ℝ) ^ τ *
              (QVEndpoint.diagNearRate (band d) N ((band d).ell N uj) ℓs (etaT E uj)
                + 2 * EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
                    ((band d).ell N uj) (etaT E uj) D J) *
            (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
                4 * ellStar ((band d).W N : ℝ) ((band d).ell N (uj + Δ)) then 1 else 0)
          + (2 * (N : ℝ) ^ τ *
              QVEndpoint.diagFarRate (band d) N ((band d).ell N uj) (etaT E uj) D J
                (EarlyQVRateEv.sDet (band d) E N uj ℓs)
            + 2 * qvTimeShiftConst d N E (uj + Δ) ^ 2 * Δ ^ 2 *
                ((band d).W N : ℝ) ^ (2 * D))) *
          tailT ((band d).W N : ℝ) ((band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
            (zdist (d.L N) (a 0 - a 1)) ^ 2 := by
  intro a
  have huj1 : uj < 1 := by linarith
  have huu' : uj ≤ uj + Δ := by linarith
  have hJ0 : 0 ≤ J := hJ'0.trans hJ'J
  have hL1 : 1 ≤ d.L N := by have := d.three_le_L N; omega
  have hℓu : 0 < (band d).ell N uj :=
    lt_of_lt_of_le zero_lt_one (one_le_ellHat_of_nonneg hL1 huj0 huj1)
  have hηu : 0 < etaT E uj := etaT_pos_of_lt_one' hE huj1
  have hW1 : 1 ≤ ((band d).W N : ℝ) := by
    have := d.W_pos N; exact_mod_cast this
  have hW0 : (0 : ℝ) < ((band d).W N : ℝ) := by linarith
  set Smax : ℝ := EarlyQVRateEv.sDet (band d) E N uj ℓs with hSmaxdef
  set nJ' : ℝ := EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
      ((band d).ell N uj) (etaT E uj) D J' with hnJ'def
  set nJ : ℝ := EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
      ((band d).ell N uj) (etaT E uj) D J with hnJdef
  have hnJ'0 : 0 ≤ nJ' := nearEpsilon_nonneg' hW0.le (Nat.cast_nonneg _)
  have hεmono : nJ' ≤ nJ :=
    nearEpsilon_mono_J (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ'0 hJ'J
  set near : ℝ := QVEndpoint.diagNearRate (band d) N ((band d).ell N uj) ℓs (etaT E uj)
    with hneardef
  set farJ' : ℝ := QVEndpoint.diagFarRate (band d) N ((band d).ell N uj) (etaT E uj) D J'
      Smax with hfarJ'def
  set farJ : ℝ := QVEndpoint.diagFarRate (band d) N ((band d).ell N uj) (etaT E uj) D J
      Smax with hfarJdef
  have hnear0 : 0 ≤ near := diagNearRate_nonneg' (band d) N hW1 hℓu hℓs hηu
  have hfarJ'0 : 0 ≤ farJ' := diagFarRate_nonneg' (band d) N hW1 hℓu hηu hJ'0
  have hfarmono : farJ' ≤ farJ := diagFarRate_mono (band d) N hℓu hηu hW1 hJ'0 hJ'J
  -- time shift
  have hT1 := sqrt_quadVar_time_shift d N hE huj0 huu' hu'1 hM a
  rw [show uj + Δ - uj = Δ from by ring] at hT1
  set Csh : ℝ := qvTimeShiftConst d N E (uj + Δ) with hCshdef
  set QVu : ℝ := Gauss.quadVar d N
      (fun M' => MomentDuhamel.lkFun (band d) E N uj M' Step2.sigPM a) M with hQVudef
  set QVu' : ℝ := Gauss.quadVar d N
      (fun M' => MomentDuhamel.lkFun (band d) E N (uj + Δ) M' Step2.sigPM a) M
      with hQVu'def
  have hQVu0 : 0 ≤ QVu := Gauss.quadVar_nonneg _ _
  have hQVu'0 : 0 ≤ QVu' := Gauss.quadVar_nonneg _ _
  have hCsh0 : 0 ≤ Csh := qvTimeShiftConst_nonneg d N E (uj + Δ)
  have hsq : QVu' ≤ 2 * QVu + 2 * (Csh * Δ) ^ 2 := by
    have hsq1 : Real.sqrt QVu' ^ 2 ≤ (Real.sqrt QVu + Csh * Δ) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hT1 2
    have e1 : Real.sqrt QVu' ^ 2 = QVu' := Real.sq_sqrt hQVu'0
    have e2 : Real.sqrt QVu ^ 2 = QVu := Real.sq_sqrt hQVu0
    nlinarith [hsq1, e1, e2, sq_nonneg (Real.sqrt QVu - Csh * Δ)]
  -- the indicator and the tail move forward in time
  set χ : ℝ := if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
      4 * ellStar ((band d).W N : ℝ) ((band d).ell N uj) then 1 else 0 with hχdef
  set χ' : ℝ := if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
      4 * ellStar ((band d).W N : ℝ) ((band d).ell N (uj + Δ)) then 1 else 0 with hχ'def
  have hχ0 : 0 ≤ χ := by rw [hχdef]; split_ifs <;> norm_num
  have hχχ' : χ ≤ χ' := by
    have hℓmono : (band d).ell N uj ≤ (band d).ell N (uj + Δ) := Step3.ellHat_mono huu' hu'1
    have hlog : 0 ≤ Real.log ((band d).W N : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg hW1) _
    have hstar : ellStar ((band d).W N : ℝ) ((band d).ell N uj) ≤
        ellStar ((band d).W N : ℝ) ((band d).ell N (uj + Δ)) := by
      unfold ellStar; exact mul_le_mul_of_nonneg_left hℓmono hlog
    rw [hχdef, hχ'def]
    by_cases h1 : (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
        4 * ellStar ((band d).W N : ℝ) ((band d).ell N uj)
    · have h2 : (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
          4 * ellStar ((band d).W N : ℝ) ((band d).ell N (uj + Δ)) := h1.trans (by linarith)
      simp only [h1, h2, ↓reduceIte, le_refl]
    · simp only [h1, ↓reduceIte]; split_ifs <;> norm_num
  set T : ℝ := tailT ((band d).W N : ℝ) ((band d).ell N uj) (etaT E uj) D
      (zdist (d.L N) (a 0 - a 1)) with hTdef
  set T' : ℝ := tailT ((band d).W N : ℝ) ((band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
      (zdist (d.L N) (a 0 - a 1)) with hT'def
  have hT0 : 0 ≤ T := tailT_nonneg hW0.le _
  have hTT' : T ≤ T' :=
    tailT_mono_time (d.L N) (d.three_le_L N) (m := (mE E).im) (mE_im_pos hE) huj0 huu' hu'1
      (by positivity) (by positivity)
  have hT2 : T ^ 2 ≤ T' ^ 2 := pow_le_pow_left₀ hT0 hTT' 2
  have hone : 1 ≤ ((band d).W N : ℝ) ^ (2 * D) * T' ^ 2 :=
    Cutoff.one_le_rpow_mul_tailT_sq hW1
  -- the pointwise bound at `u_j`
  have hqva : QVu ≤ (N : ℝ) ^ τ * ((near + 2 * nJ') * χ * T ^ 2 + farJ' * T ^ 2) := by
    have h := hqv a
    unfold QVEndpoint.diagShape' at h
    exact h
  have hNτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := by positivity
  have hstepA : (near + 2 * nJ') * χ * T ^ 2 + farJ' * T ^ 2
      ≤ (near + 2 * nJ) * χ' * T' ^ 2 + farJ * T' ^ 2 := by
    have h1 : near + 2 * nJ' ≤ near + 2 * nJ := by linarith
    have h10 : 0 ≤ near + 2 * nJ' := by linarith
    have hT'0 : 0 ≤ T' ^ 2 := sq_nonneg _
    have hχ'0 : 0 ≤ χ' := hχ0.trans hχχ'
    have ha : (near + 2 * nJ') * χ * T ^ 2 ≤ (near + 2 * nJ) * χ' * T' ^ 2 := by
      apply mul_le_mul (mul_le_mul h1 hχχ' hχ0 (by linarith)) hT2 (sq_nonneg _)
      exact mul_nonneg (by linarith) hχ'0
    have hb : farJ' * T ^ 2 ≤ farJ * T' ^ 2 :=
      mul_le_mul hfarmono hT2 (sq_nonneg _) (hfarJ'0.trans hfarmono)
    linarith
  have hQVu : QVu ≤ (N : ℝ) ^ τ * ((near + 2 * nJ) * χ' * T' ^ 2 + farJ * T' ^ 2) :=
    hqva.trans (mul_le_mul_of_nonneg_left hstepA hNτ0)
  have hCshΔsq0 : (0 : ℝ) ≤ 2 * Csh ^ 2 * Δ ^ 2 := by positivity
  have hshift :
      2 * (Csh * Δ) ^ 2 ≤ 2 * Csh ^ 2 * Δ ^ 2 * ((band d).W N : ℝ) ^ (2 * D) * T' ^ 2 := by
    have := mul_le_mul_of_nonneg_left hone hCshΔsq0
    nlinarith
  calc QVu' ≤ 2 * QVu + 2 * (Csh * Δ) ^ 2 := hsq
    _ ≤ 2 * ((N : ℝ) ^ τ * ((near + 2 * nJ) * χ' * T' ^ 2 + farJ * T' ^ 2))
          + 2 * Csh ^ 2 * Δ ^ 2 * ((band d).W N : ℝ) ^ (2 * D) * T' ^ 2 := by linarith
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- a long chain of `set`-bound real quantities (as in `hsubG_gridTau_plainN`)
/-- **Conditional sub-Gaussian bounds for the stopped far-field martingale increments**:
eventually, for `k ≤ K N`, `j < k` and every `a`, the real and imaginary parts of
`1(j < gridTauFar) · (U_{u_{j+1}, u_k} Z_{j+1})_a` are conditionally sub-Gaussian with variance
proxy `cZFar`. It fixes no energy-dependent constant (it uses only `thr_le_sqrtN_plainN`). -/
theorem hsubG_gridTauFar_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 90) {D : ℝ} (hD0 : 0 ≤ D)
    (τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) (Cc : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2, ∀ j < k,
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTauFar d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'}.indicator
          (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N k : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).re)
        (cZFar d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTauFar d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'}.indicator
          (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N k : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).im)
        (cZFar d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) := by
  filter_upwards [thr_le_sqrtN_plainN hE hs0 hst ht1 hc0 hreg0 hAc hδ0 hδc, eventually_le_W d 3]
    with N hthr hW3 k hk a j hjk
  set S : Set (Ωg d) := {ω' | j < gridTauFar d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'} with hSdef
  have hS : MeasurableSet[filt d j] S :=
    lt_gridTauFar_measurableSet (hE N) D δ τ₁ ε ζCtr τ3 τ57 s u K N j
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have htK : time s u K N (K N) = u N := time_last s u K N (hK0 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set uv := time s u K N (j + 1) with hvdef
  set uw := time s u K N k with hwdef
  set uj := time s u K N j with hujdef
  have hsuj : s N ≤ uj := by
    have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j); rwa [time_zero] at this
  have huj0 : 0 ≤ uj := (hs0 N).trans hsuj
  have hujv : uj ≤ uv := time_mono_of_le (hsu N) (Nat.le_succ j)
  have hvw : uv ≤ uw := time_mono_of_le (hsu N) hjk
  have hwu : uw ≤ u N := by rw [← htK]; exact time_mono_of_le (hsu N) hk
  have hw1 : uw < 1 := (hwu.trans (hut N)).trans_lt (ht1 N)
  have hv1 : uv < 1 := hvw.trans_lt hw1
  have hv0 : 0 ≤ uv := huj0.trans hujv
  have huj1 : uj < 1 := hujv.trans_lt hv1
  have hujt : uj ≤ t N := (hujv.trans hvw).trans (hwu.trans (hut N))
  have hΦ : ∀ a', TestFun d N (Φgrid (band d) (E N) N uv a') := fun a' =>
    Φgrid_testFun (band d) (hE N) N hv1 a'
  have hc0 : 0 ≤ cZFar d (E N) s u K δ ε D τ₁ Cc N k a j := cZFar_nonneg (hsu N) k a j
  have hcnn : (cZFar d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal
      = ⟨cZFar d (E N) s u K δ ε D τ₁ Cc N k a j, hc0⟩ := Real.toNNReal_of_nonneg hc0
  have hkey : ∀ ω', Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ) (uw : ℂ)
      (Zvec (band d) (E N) s u K N (j + 1) ω') a
        = (stepZ d s u K N j (Φgrid (band d) (E N) N uv) (ukerMat (d.L N) uv uw) a ω' : ℂ) :=
    fun ω' => (stepZ_ukerMat_eq_Uker d s u K N j (Φgrid (band d) (E N) N uv) hv0 hvw hw1 a ω').symm
  -- common scalar facts
  have hM : ∀ ω, (H d s u K N j ω).IsHermitian := fun ω => H_isHermitian d s u K N j ω
  have hℓs : 0 < (band d).ell N (s N) := Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) hs1
  have hℓuj : 0 < (band d).ell N uj := Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) huj1
  have hu'1 : uj + step s u K N < 1 := by rw [hujdef, ← time_succ_eq]; exact hv1
  have hm0 := mE_im_pos (hE N)
  have hm1 := mE_im_le_one (E := (E N)) (hE N)
  have hWe : Real.exp 1 ≤ (d.W N : ℝ) := by
    have h1 : (3 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast hW3
    have h2 : Real.exp 1 ≤ (3 : ℝ) := by
      have := Real.exp_one_lt_d9
      nlinarith
    linarith
  have hAuv : (d.W N : ℝ) * ellHat (d.L N) (uw : ℂ) * ((1 - uw) * (mE (E N)).im)
      ≤ (d.W N : ℝ) * ellHat (d.L N) (uv : ℂ) * ((1 - uv) * (mE (E N)).im) :=
    flowScale_antitoneOn (Nat.cast_nonneg _) (d.L N) (E N) (Set.mem_Iic.2 hv1.le)
      (Set.mem_Iic.2 hw1.le) hvw
  have hfl : 0 ≤ step s u K N * (N : ℝ) ^ (-Cc) :=
    mul_nonneg hΔ0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hU : ukerMat (d.L N) uv uw
      = fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i) (a' i)).re :=
    funext fun b' => funext fun a' => ukerMat_eq_prod_re (d.L N) uv uw b' a'
  -- the per-`ω` variance bound on `S`
  have hbound : ∀ ω ∈ S, step s u K N * v N (Ab d s u K N j (Φgrid (band d) (E N) N uv)
      (ukerMat (d.L N) uv uw) a ω) ≤ cZFar d (E N) s u K δ ε D τ₁ Cc N k a j := by
    intro ω hω
    rw [hU]
    obtain ⟨hjS, hG⟩ := lt_gridTauFar_imp hω
    obtain ⟨⟨⟨⟨⟨hqvS, hjg⟩, -⟩, -⟩, -⟩, -⟩ := hG
    have hthrF : thrFar (E N) s δ N uj ≤ Step2.thr (E N) s δ N uj := thrFar_le_thr' (hE N) hsuj huj1
    have hjS' : jSMat d (E N) D N uj (H d s u K N j ω) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      hjS.le.trans (hthrF.trans (hthr uj hsuj hujt))
    have hqv0 := hqvS huj1 hjS'
    have hJ'0 : 0 ≤ jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω) :=
      jGMat_nonneg (E N) N uj hℓuj hW3 _
    have hqv' : ∀ a' : LoopArg (d.L N) 2,
        Gauss.quadVar d N
            (fun M' => MomentDuhamel.lkFun (Gauss.band d) (E N) N uj M' Step2.sigPM a')
            (H d s u K N j ω)
          ≤ (N : ℝ) ^ τ₁ * QVEndpoint.diagShape' (Gauss.band d) N
              ((Gauss.band d).ell N uj) ((band d).ell N (s N)) (etaT (E N) uj) D
              (jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω))
              (EarlyQVRateEv.sDet (Gauss.band d) (E N) N uj ((band d).ell N (s N)))
              (EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
                ((Gauss.band d).ell N uj) (etaT (E N) uj) D
                (jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω)))
              a' := by
      intro a'
      have h1 := hqv0 a'
      unfold qvVal at h1
      rw [dite_eq_left_of_eq_true (eq_true (hM ω))] at h1
      exact h1
    have hNε : (0 : ℝ) ≤ (N : ℝ) ^ (2 * ε) := by positivity
    by_cases hfar : 6 * ellStar ((band d).W N : ℝ) ((band d).ell N uw) <
        (zdist (d.L N) (a 0 - a 1) : ℝ)
    · -- far label: split QV bound and `qv_conv_le_far`
      have hJ'J : jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω)
          ≤ (N : ℝ) ^ (2 * ε) * thrFar (E N) s δ N uj :=
        hjg.trans (mul_le_mul_of_nonneg_left hjS.le hNε)
      have hstep := quadVar_step_le_split N (hE N) huj0 hΔ0 hu'1 hℓs hJ'0 hJ'J (hM ω) hqv'
      have hQn : 0 ≤ QnF d (E N) s u K δ ε D τ₁ N j := by
        unfold QnF
        have hW1 : 1 ≤ ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
        have := diagNearRate_nonneg' (band d) N hW1 hℓuj hℓs (etaT_pos_of_lt_one' (hE N) huj1)
        have := nearEpsilon_nonneg' (W := ((band d).W N : ℝ)) (L := ((band d).L N : ℝ))
          (ℓu := (band d).ell N uj) (ηu := etaT (E N) uj) (D := D)
          (J := (N : ℝ) ^ (2 * ε) * thrFar (E N) s δ N uj) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        positivity
      have hQf : 0 ≤ QfF d (E N) s u K δ ε D τ₁ N j := by
        unfold QfF
        have hW1 : 1 ≤ ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
        have hthr0 : 0 ≤ thrFar (E N) s δ N uj :=
          mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg
            (div_nonneg (Step2.etaT_pos' (hE N) hs1).le (Step2.etaT_pos' (hE N) huj1).le) _)
        have := diagFarRate_nonneg' (band d) N (D := D)
          (Smax := EarlyQVRateEv.sDet (band d) (E N) N uj ((band d).ell N (s N))) hW1 hℓuj
          (etaT_pos_of_lt_one' (hE N) huj1) (mul_nonneg hNε hthr0)
        have := qvTimeShiftConst_nonneg d N (E N) uv
        have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        positivity
      have hqvΦ : ∀ a' : LoopArg (d.L N) 2,
          Gauss.quadVar d N (Φgrid (band d) (E N) N uv a') (H d s u K N j ω)
            ≤ (QnF d (E N) s u K δ ε D τ₁ N j *
                (if (zdist (d.L N) (a' 0 - a' 1) : ℝ) ≤
                  4 * ellStar (d.W N : ℝ) (ellHat (d.L N) (uv : ℂ)) then 1 else 0)
                + QfF d (E N) s u K δ ε D τ₁ N j) *
              tailT (d.W N : ℝ) (ellHat (d.L N) (uv : ℂ)) ((1 - uv) * (mE (E N)).im) D
                (zdist (d.L N) (a' 0 - a' 1)) ^ 2 := by
        intro a'
        rw [quadVar_Φgrid_eq (hE N) N hv1 a' (hM ω)]
        have h1 := hstep a'
        rw [hujdef, ← time_succ_eq] at h1
        exact h1
      have hb : 6 * ellStar (d.W N : ℝ) (ellHat (d.L N) (uw : ℂ)) ≤
          (zdist (d.L N) (a 0 - a 1) : ℝ) := hfar.le
      have hvAb := v_Ab_le_far (Φ := Φgrid (band d) (E N) N uv) hΦ
        (fun a' A hA => Φgrid_im_eq_zero (band d) (hE N).le N hv0 hv1 a' hA) (d.three_le_L N)
        hm0 hm1 hv0 hvw hw1 hWe hQn hQf hAuv a hb (hM ω) hqvΦ
      have hcZ : cZFar d (E N) s u K δ ε D τ₁ Cc N k a j =
          step s u K N * (Real.sqrt (QnF d (E N) s u K δ ε D τ₁ N j) * leak d (E N) s u K D N k j
            + Real.sqrt (QfF d (E N) s u K δ ε D τ₁ N j) * ((1 - uv) / (1 - uw)) ^ 2 *
              Step2.xiK (d.L N) (d.W N) (mE (E N)).im *
              Step2.tT (band d) (E N) N D uw (zdist (d.L N) (a 0 - a 1))) ^ 2
          + step s u K N * (N : ℝ) ^ (-Cc) := by
        unfold cZFar
        split_ifs with h
        · rfl
        · exact absurd hfar h
      rw [hcZ]
      have hsq_eq : (√(QnF d (E N) s u K δ ε D τ₁ N j) *
            tailT (d.W N : ℝ) (ellHat (d.L N) uv) ((1 - uv) * (mE (E N)).im) D 0 *
            (128 * Real.exp 3 * ((1 - uv) / (1 - uw)) ^ 2 *
              Real.exp (-(ellStar (d.W N : ℝ) (ellHat (d.L N) uw) / ellHat (d.L N) uw / 2)))
          + √(QfF d (E N) s u K δ ε D τ₁ N j) * ((1 - uv) / (1 - uw)) ^ 2 *
              Step2.xiK (d.L N) (d.W N : ℝ) (mE (E N)).im *
              tailT (d.W N : ℝ) (ellHat (d.L N) uw) ((1 - uw) * (mE (E N)).im) D
                (zdist (d.L N) (a 0 - a 1))) ^ 2
          = (Real.sqrt (QnF d (E N) s u K δ ε D τ₁ N j) * leak d (E N) s u K D N k j
            + Real.sqrt (QfF d (E N) s u K δ ε D τ₁ N j) * ((1 - uv) / (1 - uw)) ^ 2 *
              Step2.xiK (d.L N) (d.W N) (mE (E N)).im *
              Step2.tT (band d) (E N) N D uw (zdist (d.L N) (a 0 - a 1))) ^ 2 := by
        unfold leak
        rw [← hvdef, ← hwdef, mul_assoc (Real.sqrt (QnF d (E N) s u K δ ε D τ₁ N j))]
        rfl
      calc step s u K N * v N (Ab d s u K N j (Φgrid (band d) (E N) N uv)
            (fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i)
              (a' i)).re) a ω)
          ≤ step s u K N * (Real.sqrt (QnF d (E N) s u K δ ε D τ₁ N j) * leak d (E N) s u K D N k j
            + Real.sqrt (QfF d (E N) s u K δ ε D τ₁ N j) * ((1 - uv) / (1 - uw)) ^ 2 *
              Step2.xiK (d.L N) (d.W N) (mE (E N)).im *
              Step2.tT (band d) (E N) N D uw (zdist (d.L N) (a 0 - a 1))) ^ 2 := by
            rw [← hsq_eq]
            exact mul_le_mul_of_nonneg_left hvAb hΔ0
        _ ≤ _ := le_add_of_nonneg_right hfl
    · -- near label: Step 2's combined bound at `qvJ ≥ N^{2ε} thrFar`
      have hJ'J : jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω)
          ≤ qvJ (E N) s δ ε N uj := by
        refine hjg.trans ?_
        unfold qvJ
        exact mul_le_mul_of_nonneg_left (hjS.le.trans hthrF) hNε
      have hstep := quadVar_step_le d N (hE N) huj0 hΔ0 hu'1 hD0 hℓs hJ'0 hJ'J (hM ω) hqv'
      have hQ : 0 ≤ Qprime d (E N) s u K δ ε D τ₁ N j := by
        unfold Qprime
        have := QVSum.Qd_nonneg (band d) (hE N) (s := s) (δ := δ) (ε := ε) (D := D) (N := N)
          hs1 huj0 huj1
        have : 0 ≤ qvTimeShiftConst d N (E N) (time s u K N (j + 1)) :=
          qvTimeShiftConst_nonneg _ _ _ _
        have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        positivity
      have hqvΦ : ∀ a' : LoopArg (d.L N) 2,
          Gauss.quadVar d N (Φgrid (band d) (E N) N uv a') (H d s u K N j ω)
            ≤ Qprime d (E N) s u K δ ε D τ₁ N j *
              (tailT (d.W N : ℝ) (ellHat (d.L N) (uv : ℂ)) ((1 - uv) * (mE (E N)).im) D
                (zdist (d.L N) (a' 0 - a' 1))) ^ 2 := by
        intro a'
        rw [quadVar_Φgrid_eq (hE N) N hv1 a' (hM ω)]
        have h1 := hstep a'
        rw [hujdef, ← time_succ_eq] at h1
        exact h1
      have hvAb := v_Ab_le_H (Φ := Φgrid (band d) (E N) N uv) hΦ
        (fun a' A hA => Φgrid_im_eq_zero (band d) (hE N).le N hv0 hv1 a' hA) (d.three_le_L N) hm0
        hm1 hv0 hvw (hv0.trans hvw) hw1 hWe hQ hAuv a ω hqvΦ
      have hcZ : cZFar d (E N) s u K δ ε D τ₁ Cc N k a j
          = cZ d (E N) s u K δ ε D τ₁ Cc N k a j := by
        unfold cZFar
        split_ifs with h
        · exact absurd h hfar
        · rfl
      rw [hcZ]
      calc step s u K N * v N (Ab d s u K N j (Φgrid (band d) (E N) N uv)
            (fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i)
              (a' i)).re) a ω)
          ≤ step s u K N * (Real.sqrt (Qprime d (E N) s u K δ ε D τ₁ N j)
              * ((1 - uv) / (1 - uw)) ^ 2 * Step2.xiK (d.L N) (d.W N) (mE (E N)).im
              * Step2.tT (band d) (E N) N D uw (zdist (d.L N) (a 0 - a 1))) ^ 2 :=
            mul_le_mul_of_nonneg_left hvAb hΔ0
        _ ≤ cZ d (E N) s u K δ ε D τ₁ Cc N k a j := by
            unfold cZ
            linarith
  constructor
  · -- the real part
    have hfun : (fun ω => (S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ)
        (uw : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).re)
        = fun ω => S.indicator
            (fun ω => stepZ d s u K N j (Φgrid (band d) (E N) N uv) (ukerMat (d.L N) uv uw) a ω)
              ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        have h := congrArg Complex.re (hkey ω)
        rw [Complex.ofReal_re] at h
        exact h
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_re]
    rw [hfun, hcnn]
    exact stepDecomp_Z_subG d s u K N j hΦ _ a S hS _ hc0 hbound
  · -- the imaginary part: identically zero
    have hz0 : ∀ ω, stepZ d s u K N j (Φgrid (band d) (E N) N uv) (fun _ _ => (0 : ℝ)) a ω = 0 := by
      intro ω; simp [stepZ, Ab, lin]
    have hfun : (fun ω => (S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ)
        (uw : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).im)
        = fun ω => S.indicator
            (fun ω => stepZ d s u K N j (Φgrid (band d) (E N) N uv) (fun _ _ => (0 : ℝ)) a ω)
              ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hz0]
        have h := congrArg Complex.im (hkey ω)
        rw [Complex.ofReal_im] at h
        exact h
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_im]
    rw [hfun, hcnn]
    refine stepDecomp_Z_subG d s u K N j hΦ _ a S hS _ hc0 ?_
    intro ω _
    have hAb : Ab d s u K N j (Φgrid (band d) (E N) N uv) (fun _ _ => (0 : ℝ)) a ω = 0 := by
      simp [Ab]
    have hv0' : RBM.Gauss.Grid.v N (0 : Matrix (d.Idx N) (d.Idx N) ℂ) = 0 := by
      simp [Gauss.Grid.v, linVar, lin]
    rw [hAb, hv0', mul_zero]
    exact hc0

/-! ## Exponent control for `farQV_sum_leN` (pure real arithmetic) -/

/-- Pointwise far rate with the propagator factor: the `J²` part carries
`J_v² r^{3/2} A^{-1/2}` (`Z² ≤ A`, `r² ≤ q⁴ = R`), the `J³` part `J_v³ A^{-1}`, both with
`η_w^{-1}ρ⁴ ≤ η_s³/η_v⁴`; the `W^{-D}` part is kept with `ρ ≤ R_b`. -/
private theorem farRate_point_le {W L D J A S ηw ηs ηv c2 cF r Jv q Z ρ Rb : ℝ}
    (hW0 : 0 < W) (hL0 : 0 ≤ L) (hηw : 0 < ηw) (hηv : 0 < ηv) (hws : ηw ≤ ηs)
    (hJ0 : 0 ≤ J) (hJ : J ≤ Jv) (hA0 : 0 < A) (hZ0 : 0 < Z) (hZA : Z ^ 2 ≤ A)
    (hS : S = r ^ 3 * A⁻¹ ^ 3) (hr0 : 0 ≤ r) (hq0 : 0 ≤ q) (hrq : r ^ 2 ≤ q ^ 4)
    (hc0 : 0 ≤ c2) (hc : c2 ≤ cF) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ηw / ηv) (hρR : ρ ≤ Rb) :
    (2 * ηw⁻¹ * (c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹)
        + 4 * W * L * W ^ (-D) * (2 * J) ^ 3) * ρ ^ 4
      ≤ (ηs ^ 3 / ηv ^ 4) * (16 * cF * (Jv ^ 2 * q ^ 3 / Z) + 1152 * (Jv ^ 3 / Z ^ 2))
        + 32 * (W * L * W ^ (-D)) * Jv ^ 3 * Rb ^ 4 := by
  have hJv0 : 0 ≤ Jv := hJ0.trans hJ
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  -- `J² A √S ≤ J_v² q³ / Z`
  have hr3 : r ^ 3 ≤ q ^ 6 := by
    have h6 : (r ^ 3) ^ 2 ≤ (q ^ 6) ^ 2 := by
      calc (r ^ 3) ^ 2 = (r ^ 2) ^ 3 := by ring
        _ ≤ (q ^ 4) ^ 3 := pow_le_pow_left₀ (by positivity) hrq 3
        _ = (q ^ 6) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h6
  have hJ4 : J ^ 4 ≤ Jv ^ 4 := pow_le_pow_left₀ hJ0 hJ 4
  have hJ3 : J ^ 3 ≤ Jv ^ 3 := pow_le_pow_left₀ hJ0 hJ 3
  have hAinv : A⁻¹ ≤ (Z ^ 2)⁻¹ := inv_anti₀ (by positivity) hZA
  have hsqS : J ^ 2 * (A * Real.sqrt S) ≤ Jv ^ 2 * q ^ 3 / Z := by
    have hl0 : 0 ≤ J ^ 2 * (A * Real.sqrt S) := by positivity
    have hr0' : 0 ≤ Jv ^ 2 * q ^ 3 / Z := by positivity
    have hsq : (J ^ 2 * (A * Real.sqrt S)) ^ 2 = J ^ 4 * r ^ 3 * A⁻¹ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hS0, hS]
      field_simp
    have hsq' : (Jv ^ 2 * q ^ 3 / Z) ^ 2 = Jv ^ 4 * q ^ 6 * (Z ^ 2)⁻¹ := by
      field_simp
    have hle : (J ^ 2 * (A * Real.sqrt S)) ^ 2 ≤ (Jv ^ 2 * q ^ 3 / Z) ^ 2 := by
      rw [hsq, hsq']
      apply mul_le_mul (mul_le_mul hJ4 hr3 (by positivity) (by positivity)) hAinv
        (by positivity) (by positivity)
    exact (pow_le_pow_iff_left₀ hl0 hr0' (by norm_num)).1 hle
  have hJA : J ^ 3 * A⁻¹ ≤ Jv ^ 3 / Z ^ 2 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hJ3 hAinv (by positivity) (by positivity)
  have hηρ : ηw⁻¹ * ρ ^ 4 ≤ ηs ^ 3 / ηv ^ 4 := by
    have h1 : ρ ^ 4 ≤ (ηw / ηv) ^ 4 := pow_le_pow_left₀ hρ0 hρ 4
    calc ηw⁻¹ * ρ ^ 4 ≤ ηw⁻¹ * (ηw / ηv) ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ηw ^ 3 / ηv ^ 4 := by field_simp
      _ ≤ ηs ^ 3 / ηv ^ 4 := by gcongr
  have hρ4 : ρ ^ 4 ≤ Rb ^ 4 := pow_le_pow_left₀ hρ0 hρR 4
  have hP0 : 0 ≤ ηs ^ 3 / ηv ^ 4 := by
    have : 0 ≤ ηs := hηw.le.trans hws
    positivity
  have e : (2 * ηw⁻¹ * (c2 * ((2 * J) ^ 2 * (A * (2 * Real.sqrt S))) + 72 * (2 * J) ^ 3 * A⁻¹)
        + 4 * W * L * W ^ (-D) * (2 * J) ^ 3) * ρ ^ 4
      = (ηw⁻¹ * ρ ^ 4) * (16 * c2 * (J ^ 2 * (A * Real.sqrt S)) + 1152 * (J ^ 3 * A⁻¹))
        + 32 * (W * L * W ^ (-D)) * J ^ 3 * ρ ^ 4 := by ring
  rw [e]
  have hin0 : 0 ≤ 16 * c2 * (J ^ 2 * (A * Real.sqrt S)) + 1152 * (J ^ 3 * A⁻¹) := by positivity
  have hin : 16 * c2 * (J ^ 2 * (A * Real.sqrt S)) + 1152 * (J ^ 3 * A⁻¹)
      ≤ 16 * cF * (Jv ^ 2 * q ^ 3 / Z) + 1152 * (Jv ^ 3 / Z ^ 2) := by
    have h1 : c2 * (J ^ 2 * (A * Real.sqrt S)) ≤ cF * (Jv ^ 2 * q ^ 3 / Z) :=
      mul_le_mul hc hsqS (by positivity) (hc0.trans hc)
    linarith
  have hWL0 : 0 ≤ W * L * W ^ (-D) := by positivity
  have t1 : (ηw⁻¹ * ρ ^ 4) * (16 * c2 * (J ^ 2 * (A * Real.sqrt S)) + 1152 * (J ^ 3 * A⁻¹))
      ≤ (ηs ^ 3 / ηv ^ 4) * (16 * cF * (Jv ^ 2 * q ^ 3 / Z) + 1152 * (Jv ^ 3 / Z ^ 2)) :=
    mul_le_mul hηρ hin hin0 hP0
  have t2 : 32 * (W * L * W ^ (-D)) * J ^ 3 * ρ ^ 4 ≤ 32 * (W * L * W ^ (-D)) * Jv ^ 3 * Rb ^ 4 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hJ3 (by positivity)) hρ4 (by positivity)
      (by positivity)
  linarith

set_option maxHeartbeats 1000000 in
-- five explicit rows of high-degree monomial comparisons
/-- The final normalisation of `farQV_sum_leN`, with `z = A_v^{1/360}`, `q = R_v^{1/4}`,
`n = N^{δ/32}`, `J_v = n^{48} q^{13}`: every row closes against `z^{-25} = A_v^{-5/72}`. -/
private theorem farQV_assembly {n q z m ξ cF Xb TSb WLD T : ℝ}
    (hn : 1 ≤ n) (hq : 1 ≤ q) (hz : 1 ≤ z) (hnz : n ^ 8 ≤ z) (hqz : q ≤ z ^ 3) (hm0 : 0 < m)
    (hconst : 65536 / m ≤ n) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ n ^ 2) (hcF0 : 0 ≤ cF)
    (hcF : cF ≤ 2 * n ^ 4) (hWLD0 : 0 ≤ WLD) (hWLD : 1024 * z ^ 360 * WLD ≤ 1)
    (hTS0 : 0 ≤ TSb) (hTS : 16 * z ^ 360 * TSb ≤ 1) (hX0 : 0 ≤ Xb)
    (hX : 16 * z ^ 360 * Xb ≤ T ^ 2) :
    2 * Xb + 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (16 * cF * ((n ^ 48 * q ^ 13) ^ 2 * q ^ 3
        / z ^ 180) + 1152 * ((n ^ 48 * q ^ 13) ^ 3 / (z ^ 180) ^ 2))
        + 32 * WLD * (n ^ 48 * q ^ 13) ^ 3 * q ^ 16) + TSb * q ^ 16)
      ≤ (z ^ 25)⁻¹ * T ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hn0 : 0 < n := by linarith
  have hq0 : 0 < q := by linarith
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  have hξ2 : ξ ^ 2 ≤ n ^ 4 := by
    calc ξ ^ 2 ≤ (n ^ 2) ^ 2 := pow_le_pow_left₀ hξ0 hξ 2
      _ = n ^ 4 := by ring
  have hmn : 65536 ≤ m * n := by
    have := (div_le_iff₀ hm0).1 hconst; linarith
  -- basic comparisons
  have hn160 : n ^ 160 ≤ z ^ 20 := by
    calc n ^ 160 = (n ^ 8) ^ 20 := by ring
      _ ≤ z ^ 20 := pow_le_pow_left₀ (by positivity) hnz 20
  have hq45 : q ^ 45 ≤ z ^ 135 := by
    calc q ^ 45 ≤ (z ^ 3) ^ 45 := pow_le_pow_left₀ hq0.le hqz 45
      _ = z ^ 135 := by ring
  have hq55 : q ^ 55 ≤ z ^ 165 := by
    calc q ^ 55 ≤ (z ^ 3) ^ 55 := pow_le_pow_left₀ hq0.le hqz 55
      _ = z ^ 165 := by ring
  have hq16 : q ^ 16 ≤ z ^ 48 := by
    calc q ^ 16 ≤ (z ^ 3) ^ 16 := pow_le_pow_left₀ hq0.le hqz 16
      _ = z ^ 48 := by ring
  have hnpow : ∀ a b : ℕ, a ≤ b → n ^ a ≤ n ^ b := fun a b h => pow_le_pow_right₀ hn h
  have hzpow : ∀ a b : ℕ, a ≤ b → z ^ a ≤ z ^ b := fun a b h => pow_le_pow_right₀ hz h
  have hz25 : 0 < z ^ 25 := by positivity
  -- row 1 (`J²`): `≤ (1/2) z^{-25} T²`
  have r1 : 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (16 * cF * ((n ^ 48 * q ^ 13) ^ 2 * q ^ 3
        / z ^ 180)))) ≤ (1 / 2) * ((z ^ 25)⁻¹ * T ^ 2) := by
    have e : 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (16 * cF * ((n ^ 48 * q ^ 13) ^ 2 * q ^ 3
        / z ^ 180)))) = (64 * ξ ^ 2 * cF * n ^ 97 * q ^ 45) * T ^ 2 / (m * z ^ 180) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hk : 64 * ξ ^ 2 * cF * n ^ 97 * q ^ 45 * (2 * z ^ 25) ≤ m * z ^ 180 := by
      calc 64 * ξ ^ 2 * cF * n ^ 97 * q ^ 45 * (2 * z ^ 25)
          ≤ 64 * n ^ 4 * (2 * n ^ 4) * n ^ 97 * z ^ 135 * (2 * z ^ 25) := by gcongr
        _ = 256 * n ^ 105 * z ^ 160 := by ring
        _ ≤ (m * n) * n ^ 105 * z ^ 160 := by gcongr; linarith
        _ = m * n ^ 106 * z ^ 160 := by ring
        _ ≤ m * n ^ 160 * z ^ 160 := by gcongr; norm_num
        _ ≤ m * z ^ 20 * z ^ 160 := by gcongr
        _ = m * z ^ 180 := by ring
    have : (1 / 2) * ((z ^ 25)⁻¹ * T ^ 2) * (m * z ^ 180)
        = T ^ 2 * (m * z ^ 180) / (2 * z ^ 25) := by field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hk hT2]
  -- row 2 (`J³`): `≤ (1/8) z^{-25} T²`
  have r2 : 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (1152 * ((n ^ 48 * q ^ 13) ^ 3
        / (z ^ 180) ^ 2)))) ≤ (1 / 8) * ((z ^ 25)⁻¹ * T ^ 2) := by
    have e : 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (1152 * ((n ^ 48 * q ^ 13) ^ 3
        / (z ^ 180) ^ 2)))) = (4608 * ξ ^ 2 * n ^ 145 * q ^ 55) * T ^ 2 / (m * z ^ 360) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hk : 4608 * ξ ^ 2 * n ^ 145 * q ^ 55 * (8 * z ^ 25) ≤ m * z ^ 360 := by
      calc 4608 * ξ ^ 2 * n ^ 145 * q ^ 55 * (8 * z ^ 25)
          ≤ 4608 * n ^ 4 * n ^ 145 * z ^ 165 * (8 * z ^ 25) := by gcongr
        _ = 36864 * n ^ 149 * z ^ 190 := by ring
        _ ≤ (m * n) * n ^ 149 * z ^ 190 := by gcongr; linarith
        _ = m * n ^ 150 * z ^ 190 := by ring
        _ ≤ m * n ^ 160 * z ^ 190 := by gcongr; norm_num
        _ ≤ m * z ^ 20 * z ^ 190 := by gcongr
        _ = m * z ^ 210 := by ring
        _ ≤ m * z ^ 360 := by gcongr; norm_num
    have : (1 / 8) * ((z ^ 25)⁻¹ * T ^ 2) * (m * z ^ 360)
        = T ^ 2 * (m * z ^ 360) / (8 * z ^ 25) := by field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hk hT2]
  -- row 3 (`W^{-D} J³`)
  have r3 : 2 * ξ ^ 2 * T ^ 2 * (2 * n * (32 * WLD * (n ^ 48 * q ^ 13) ^ 3 * q ^ 16))
      ≤ (1 / 8) * ((z ^ 25)⁻¹ * T ^ 2) := by
    have hk : 128 * ξ ^ 2 * n ^ 145 * q ^ 55 * z ^ 25 ≤ 128 * z ^ 360 := by
      calc 128 * ξ ^ 2 * n ^ 145 * q ^ 55 * z ^ 25
          ≤ 128 * n ^ 4 * n ^ 145 * z ^ 165 * z ^ 25 := by gcongr
        _ = 128 * n ^ 149 * z ^ 190 := by ring
        _ ≤ 128 * n ^ 160 * z ^ 190 := by gcongr; norm_num
        _ ≤ 128 * z ^ 20 * z ^ 190 := by gcongr
        _ = 128 * z ^ 210 := by ring
        _ ≤ 128 * z ^ 360 := by gcongr; norm_num
    have e : 2 * ξ ^ 2 * T ^ 2 * (2 * n * (32 * WLD * (n ^ 48 * q ^ 13) ^ 3 * q ^ 16))
        = (128 * ξ ^ 2 * n ^ 145 * q ^ 55 * z ^ 25) * WLD * ((z ^ 25)⁻¹ * T ^ 2) := by
      field_simp; ring
    rw [e]
    have hw : (128 * ξ ^ 2 * n ^ 145 * q ^ 55 * z ^ 25) * WLD ≤ 1 / 8 := by
      calc (128 * ξ ^ 2 * n ^ 145 * q ^ 55 * z ^ 25) * WLD ≤ 128 * z ^ 360 * WLD :=
            mul_le_mul_of_nonneg_right hk hWLD0
        _ ≤ 1 / 8 := by linarith
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  -- row 4 (time shift)
  have r4 : 2 * ξ ^ 2 * T ^ 2 * (TSb * q ^ 16) ≤ (1 / 8) * ((z ^ 25)⁻¹ * T ^ 2) := by
    have hk : 2 * ξ ^ 2 * q ^ 16 * z ^ 25 ≤ 2 * z ^ 360 := by
      calc 2 * ξ ^ 2 * q ^ 16 * z ^ 25 ≤ 2 * n ^ 4 * z ^ 48 * z ^ 25 := by gcongr
        _ ≤ 2 * n ^ 160 * z ^ 48 * z ^ 25 := by gcongr; norm_num
        _ ≤ 2 * z ^ 20 * z ^ 48 * z ^ 25 := by gcongr
        _ = 2 * z ^ 93 := by ring
        _ ≤ 2 * z ^ 360 := by gcongr; norm_num
    have e : 2 * ξ ^ 2 * T ^ 2 * (TSb * q ^ 16)
        = (2 * ξ ^ 2 * q ^ 16 * z ^ 25) * TSb * ((z ^ 25)⁻¹ * T ^ 2) := by
      field_simp
    rw [e]
    have hw : (2 * ξ ^ 2 * q ^ 16 * z ^ 25) * TSb ≤ 1 / 8 := by
      calc (2 * ξ ^ 2 * q ^ 16 * z ^ 25) * TSb ≤ 2 * z ^ 360 * TSb :=
            mul_le_mul_of_nonneg_right hk hTS0
        _ ≤ 1 / 8 := by linarith
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  -- row 5 (near → far leakage)
  have r5 : 2 * Xb ≤ (1 / 8) * ((z ^ 25)⁻¹ * T ^ 2) := by
    have h1 : z ^ 25 ≤ z ^ 360 := hzpow 25 360 (by norm_num)
    have h2 : 16 * z ^ 25 * Xb ≤ T ^ 2 := by
      have : 16 * z ^ 25 * Xb ≤ 16 * z ^ 360 * Xb := by gcongr
      linarith
    have : (1 / 8) * ((z ^ 25)⁻¹ * T ^ 2) = T ^ 2 / (8 * z ^ 25) := by field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith
  have e : 2 * Xb + 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (16 * cF * ((n ^ 48 * q ^ 13) ^ 2
        * q ^ 3 / z ^ 180) + 1152 * ((n ^ 48 * q ^ 13) ^ 3 / (z ^ 180) ^ 2))
        + 32 * WLD * (n ^ 48 * q ^ 13) ^ 3 * q ^ 16) + TSb * q ^ 16)
      = 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (16 * cF * ((n ^ 48 * q ^ 13) ^ 2 * q ^ 3
          / z ^ 180))))
        + 2 * ξ ^ 2 * T ^ 2 * (2 * n * (q ^ 16 / m * (1152 * ((n ^ 48 * q ^ 13) ^ 3
          / (z ^ 180) ^ 2))))
        + 2 * ξ ^ 2 * T ^ 2 * (2 * n * (32 * WLD * (n ^ 48 * q ^ 13) ^ 3 * q ^ 16))
        + 2 * ξ ^ 2 * T ^ 2 * (TSb * q ^ 16) + 2 * Xb := by ring
  rw [e]
  linarith

/-- Near → far leakage absorption: `e^{-(log W)^{3/2}}` beats every fixed power of `W` once
`log W ≥ (2D+40)²`. -/
private theorem leak_absorb {W D : ℝ} (hD : 0 ≤ D) (hW : Real.exp ((2 * D + 40) ^ 2) ≤ W) :
    2 ^ 23 * Real.exp 6 * W ^ 26 * Real.exp (-(Real.log W ^ (3 / 2 : ℝ))) ≤ W ^ (-(2 * D)) := by
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos _) hW
  set x := Real.log W with hx
  have hxW : (2 * D + 40) ^ 2 ≤ x := (Real.le_log_iff_exp_le hW0).2 hW
  have hx0 : 0 ≤ x := le_trans (sq_nonneg _) hxW
  have hWx : W = Real.exp x := (Real.exp_log hW0).symm
  have hsq : 2 * D + 40 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxW
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx0 (by norm_num), Real.rpow_one]
  have h2 : (2 : ℝ) ^ 23 ≤ Real.exp 23 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have : (2 : ℝ) ≤ Real.exp 1 := by linarith
    calc (2 : ℝ) ^ 23 ≤ Real.exp 1 ^ 23 := pow_le_pow_left₀ (by norm_num) this 23
      _ = Real.exp 23 := by rw [← Real.exp_nat_mul]; norm_num
  have hW26 : W ^ 26 = Real.exp (26 * x) := by
    rw [hWx, ← Real.exp_nat_mul]; norm_num
  have hWD : W ^ (-(2 * D)) = Real.exp (-(2 * D) * x) := by
    rw [Real.rpow_def_of_pos hW0, mul_comm]
  have hx1600 : 1600 ≤ x := by nlinarith
  have hkey : 23 + 6 + 26 * x - x * Real.sqrt x ≤ -(2 * D) * x := by
    have : (2 * D + 40) * x ≤ x * Real.sqrt x := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hsq hx0
    nlinarith
  calc 2 ^ 23 * Real.exp 6 * W ^ 26 * Real.exp (-(Real.log W ^ (3 / 2 : ℝ)))
      ≤ Real.exp 23 * Real.exp 6 * Real.exp (26 * x) * Real.exp (-(x * Real.sqrt x)) := by
        rw [hW26, ← hx, hx32]; gcongr
    _ = Real.exp (23 + 6 + 26 * x - x * Real.sqrt x) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(2 * D) * x) := Real.exp_le_exp.2 hkey
    _ = W ^ (-(2 * D)) := hWD.symm
end FarMart

section Main

open FarMart

set_option maxHeartbeats 8000000 in
-- a long chain of `set`-bound real quantities (as in `xZ_le_azumaMm_plainN`)
/-- **The sum over `j < k` of the variance proxies `cZFar`** is at most
`N^{-Cc} · step · k + (W ℓ η)_{u_k}^{-5/72} T_{u_k,D}²` at every far pair, eventually. The
constants `(mE (E N)).im` and `65536/(mE (E N)).im` are bounded through the uniform κ-bound
`mκ ≤ (mE (E N)).im` (see the module docstring). -/
theorem farQV_sum_leN {κ : ℝ} (hκ0 : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) (hD : 64 ≤ D)
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    (hΔ : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-(D + 20))) (Cc : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      6 * ellStar ((band d).W N : ℝ) ((band d).ell N (time s u K N k)) <
          (zdist (d.L N) (a 0 - a 1) : ℝ) →
      ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ (δ / 4) D (δ / 32) Cc N k a j ≤
        (N : ℝ) ^ (-Cc) * step s u K N * k +
          (band d).scale (E N) N (time s u K N k) ^ (-(5 : ℝ) / 72) *
            Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) ^ 2 := by
  have hE2 : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE N) (by linarith)
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκpos : 0 < mκ := by positivity
  have hmge : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hxiAnti : ∀ N, Step2.xiK (d.L N) (d.W N) (mE (E N)).im ≤
      Step2.xiK (d.L N) (d.W N) mκ := by
    intro N
    have hle : mκ ^ 2 ≤ (mE (E N)).im ^ 2 := by nlinarith [hmge N, hmκpos.le]
    have hinv : ((mE (E N)).im ^ 2)⁻¹ ≤ (mκ ^ 2)⁻¹ := inv_anti₀ (by positivity) hle
    unfold Step2.xiK
    linarith
  filter_upwards [hreg0, hAc, d.dim, Step2.eventually_le_W_sq (band d),
    QVSum.eventually_cNear2_le_rpow (band d) (τ := δ / 8) (by positivity),
    Step2FarInputs.eventually_xiK_le (band d) mκ (τ := δ / 16) (by positivity),
    eventually_le_rpow (65536 / mκ) (τ := δ / 32) (by positivity),
    etaT_inv_le_of_plainN (band d) hE2 ht1 hc0 hAc, hΔ,
    (Step2.tendsto_W (band d)).eventually_ge_atTop (Real.exp ((4 * D + 40) ^ 2)),
    eventually_ge_atTop 64]
    with N hregN hAcN hdim hNW hcN hxi hcst hηt hΔN hWbig hN64 k hk a hfar
  have hm0 := mE_im_pos (hE2 N)
  have hm1 := mE_im_le_one (E := E N) (hE2 N)
  have hN64' : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  -- scales of `W`, `L`
  have hL1 : 1 ≤ d.L N := by have := d.three_le_L N; omega
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
  have hW0 : (0 : ℝ) < ((band d).W N : ℝ) := by linarith
  have hWL : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hLN : ((band d).L N : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ ((band d).L N : ℝ) := Nat.cast_nonneg _
    nlinarith only [this, hWL, hW1]
  have hWN : ((band d).W N : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ ((band d).L N : ℝ) := by exact_mod_cast hL1
    nlinarith only [this, hWL, hW0.le]
  have hlogW : (4 * D + 40) ^ 2 ≤ Real.log ((band d).W N : ℝ) :=
    (Real.le_log_iff_exp_le hW0).2 hWbig
  have hlog1 : (2 * D + 40) ^ 2 ≤ Real.log ((band d).W N : ℝ) :=
    le_trans (by nlinarith only [hD0]) hlogW
  have hWbig2 : Real.exp ((2 * D + 40) ^ 2) ≤ ((band d).W N : ℝ) :=
    le_trans (Real.exp_le_exp.2 (by nlinarith only [hD0])) hWbig
  have hW2 : (2 : ℝ) ≤ ((band d).W N : ℝ) := by
    have h := Real.add_one_le_exp ((4 * D + 40) ^ 2)
    nlinarith only [h, hWbig, hD0]
  have hWe : Real.exp 1 ≤ ((band d).W N : ℝ) :=
    le_trans (Real.exp_le_exp.2 (by nlinarith only [hD0])) hWbig
  -- the target time `v = u_k`
  set v := time s u K N k with hvdef
  have hv1 : v < 1 := time_lt_one_of_le hsu hut ht1 hK0 hk
  have hvt : v ≤ t N := by
    have := time_mono_of_le (K := K) (hsu N) hk
    rw [time_last s u K N (hK0 N)] at this; linarith [hut N]
  have hsv : s N ≤ v := by
    have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le k); rwa [time_zero] at this
  have hkΔ : (k : ℝ) * step s u K N = v - s N := by rw [hvdef]; unfold time; ring
  -- `η`'s
  have hηs := Step2.etaT_pos' (hE2 N) hs1
  have hηv := Step2.etaT_pos' (hE2 N) hv1
  have hηt0 := Step2.etaT_pos' (hE2 N) (ht1 N)
  have hηtv : etaT (E N) (t N) ≤ etaT (E N) v := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηvs : etaT (E N) v ≤ etaT (E N) (s N) := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηs1 : etaT (E N) (s N) ≤ 1 := by
    simp only [Step2.etaT_eq]
    calc (1 - s N) * (mE (E N)).im
        ≤ 1 * 1 := mul_le_mul (by linarith [hs0 N]) hm1 hm0.le zero_le_one
      _ = 1 := one_mul 1
  -- `R = η_s/η_v`, `A = A_v`
  set R := etaT (E N) (s N) / etaT (E N) v with hRdef
  have hR1 : 1 ≤ R := (one_le_div hηv).2 hηvs
  have hR0 : 0 ≤ R := by linarith
  have hRt : R ≤ etaT (E N) (s N) / etaT (E N) (t N) := div_le_div_of_nonneg_left hηs.le hηt0 hηtv
  have hRN : R ≤ N := by
    calc R ≤ etaT (E N) (s N) / etaT (E N) (t N) := hRt
      _ ≤ 1 / etaT (E N) (t N) := div_le_div_of_nonneg_right hηs1 hηt0.le
      _ = (etaT (E N) (t N))⁻¹ := one_div _
      _ ≤ N := hηt
  set A := (band d).scale (E N) N v with hAdef
  have hAtv : (band d).scale (E N) N (t N) ≤ A :=
    flowScale_antitoneOn hW0.le ((band d).L N) (E N) (Set.mem_Iic.2 hv1.le)
      (Set.mem_Iic.2 (ht1 N).le) hvt
  have hNc1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have hA1 : 1 ≤ A := hNc1.trans (hAcN.trans hAtv)
  have hA0 : 0 < A := by linarith
  have hAN : A ≤ N := by
    have hℓ : (band d).ell N v ≤ ((band d).L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hη1 : etaT (E N) v ≤ 1 := hηvs.trans hηs1
    calc A = ((band d).W N : ℝ) * (band d).ell N v * etaT (E N) v := rfl
      _ ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) * 1 := by gcongr
      _ ≤ N := by linarith
  have hR30 : R ^ 30 ≤ A :=
    (pow_le_pow_left₀ hR0 hRt 30).trans (hregN.trans hAtv)
  -- `n = N^{δ/32}`, `z = A^{1/360}`, `q = R^{1/4}`
  set n := (N : ℝ) ^ (δ / 32) with hndef
  have hn1 : 1 ≤ n := Real.one_le_rpow hN1' (by positivity)
  have hnpow : ∀ k : ℕ, n ^ k = (N : ℝ) ^ (δ / 32 * k) := fun k =>
    (Real.rpow_mul_natCast hN0.le (δ / 32) k).symm
  set z := A ^ ((1 : ℝ) / 360) with hzdef
  have hz360 : z ^ 360 = A := by
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hz1 : 1 ≤ z := Real.one_le_rpow hA1 (by norm_num)
  have hz0 : 0 < z := by linarith
  have hnz : n ^ 8 ≤ z := by
    have h1 : (n ^ 8) ^ 360 ≤ z ^ 360 := by
      rw [hz360, ← pow_mul, hnpow 2880]
      calc (N : ℝ) ^ (δ / 32 * ((8 * 360 : ℕ) : ℝ)) ≤ (N : ℝ) ^ c :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
        _ ≤ A := hAcN.trans hAtv
    exact (pow_le_pow_iff_left₀ (by positivity) hz0.le (by norm_num)).1 h1
  set q := R ^ ((1 : ℝ) / 4) with hqdef
  have hq4 : q ^ 4 = R := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hR0]; norm_num
  have hq1 : 1 ≤ q := Real.one_le_rpow hR1 (by norm_num)
  have hq0 : 0 < q := by linarith
  have hqz : q ≤ z ^ 3 := by
    have h1 : q ^ 120 ≤ (z ^ 3) ^ 120 := by
      calc q ^ 120 = (q ^ 4) ^ 30 := by ring
        _ = R ^ 30 := by rw [hq4]
        _ ≤ A := hR30
        _ = (z ^ 3) ^ 120 := by rw [← hz360]; ring
    exact (pow_le_pow_iff_left₀ hq0.le (by positivity) (by norm_num)).1 h1
  have hq16 : q ^ 16 = R ^ 4 := by rw [← hq4]; ring
  -- `T = T_{u_k}(a)`
  set T := Step2.tT (band d) (E N) N D v (zdist (d.L N) (a 0 - a 1)) with hTdef
  have hTW : ((band d).W N : ℝ) ^ (-D) ≤ T := rpow_neg_le_tailT _
  have hTpos : 0 < T := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hTW
  have hT2W : ((band d).W N : ℝ) ^ (-(2 * D)) ≤ T ^ 2 := by
    have e : ((band d).W N : ℝ) ^ (-(2 * D)) = (((band d).W N : ℝ) ^ (-D)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    rw [e]; exact pow_le_pow_left₀ (Real.rpow_nonneg hW0.le _) hTW 2
  -- the constants of the assembly
  set ξ := Step2.xiK (d.L N) (d.W N) (mE (E N)).im with hξdef
  have hξ0 : 0 ≤ ξ := Step2.xiK_nonneg _ _ _
  have hξn : ξ ≤ n ^ 2 := by
    rw [hnpow 2]
    have hxi' := (hxiAnti N).trans hxi
    convert hxi' using 2 <;> first | rfl | (push_cast; ring)
  set Jv := n ^ 48 * q ^ 13 with hJvdef
  set P := etaT (E N) (s N) ^ 3 / etaT (E N) v ^ 4 with hPdef
  set Zc := z ^ 180 with hZcdef
  set G := 16 * (2 * n ^ 4) * (Jv ^ 2 * q ^ 3 / Zc) + 1152 * (Jv ^ 3 / Zc ^ 2) with hGdef
  set WLD := ((band d).W N : ℝ) * ((band d).L N : ℝ) * ((band d).W N : ℝ) ^ (-D) with hWLDdef
  set TSb := ((band d).W N : ℝ) ^ (-(20 : ℝ)) with hTSbdef
  set Xb := 8 * (N : ℝ) ^ 8 * (4 * (128 * Real.exp 3) ^ 2 * q ^ 16 *
    Real.exp (-(Real.log ((band d).W N : ℝ) ^ (3 / 2 : ℝ)))) with hXbdef
  set M := 2 * Xb + 2 * ξ ^ 2 * T ^ 2 * (2 * n * (P * G + 32 * WLD * Jv ^ 3 * q ^ 16)
    + TSb * q ^ 16) with hMdef
  -- nonnegativity
  have hn0 : 0 < n := by linarith
  have hJv0 : 0 ≤ Jv := by positivity
  have hZc0 : 0 < Zc := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hWLD0 : 0 ≤ WLD := by
    have : 0 ≤ ((band d).W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    positivity
  have hTSb0 : 0 ≤ TSb := Real.rpow_nonneg hW0.le _
  have hXb0 : 0 ≤ Xb := by positivity
  -- comparisons used repeatedly
  have hnN : n ≤ N := by
    calc n ≤ n ^ 8 := by
          calc n = n ^ 1 := (pow_one n).symm
            _ ≤ n ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
      _ ≤ z := hnz
      _ ≤ z ^ 360 := by
          calc z = z ^ 1 := (pow_one z).symm
            _ ≤ z ^ 360 := pow_le_pow_right₀ hz1 (by norm_num)
      _ = A := hz360
      _ ≤ N := hAN
  have hn4N : n ^ 4 ≤ N := by
    calc n ^ 4 ≤ n ^ 8 := pow_le_pow_right₀ hn1 (by norm_num)
      _ ≤ z := hnz
      _ ≤ z ^ 360 := by
          calc z = z ^ 1 := (pow_one z).symm
            _ ≤ z ^ 360 := pow_le_pow_right₀ hz1 (by norm_num)
      _ = A := hz360
      _ ≤ N := hAN
  have hJvN : Jv ≤ N := by
    have h1 : n ^ 48 ≤ z ^ 6 := by
      calc n ^ 48 = (n ^ 8) ^ 6 := by ring
        _ ≤ z ^ 6 := pow_le_pow_left₀ (by positivity) hnz 6
    have h2 : q ^ 13 ≤ z ^ 39 := by
      calc q ^ 13 ≤ (z ^ 3) ^ 13 := pow_le_pow_left₀ hq0.le hqz 13
        _ = z ^ 39 := by ring
    calc Jv = n ^ 48 * q ^ 13 := rfl
      _ ≤ z ^ 6 * z ^ 39 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = z ^ 45 := by ring
      _ ≤ z ^ 360 := pow_le_pow_right₀ hz1 (by norm_num)
      _ = A := hz360
      _ ≤ N := hAN
  have hcN4 : ∀ ℓ : ℝ, 1 ≤ ℓ → Lemma57.cNear2 ((band d).W N : ℝ) ℓ ≤ n ^ 4 := by
    intro ℓ hℓ
    rw [hnpow 4]
    refine (hcN ℓ hℓ).trans_eq ?_
    congr 1; push_cast; ring
  have hℓs1 : 1 ≤ (band d).ell N (s N) := one_le_ellHat_of_nonneg hL1 (hs0 N) hs1
  have hℓs0 : 0 < (band d).ell N (s N) := by linarith
  -- the per-`j` bound
  have hterm : ∀ j ∈ Finset.range k, cZFar d (E N) s u K δ (δ / 4) D (δ / 32) Cc N k a j ≤
      step s u K N * M + step s u K N * (N : ℝ) ^ (-Cc) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set w := time s u K N j with hwdef
    set u' := time s u K N (j + 1) with hu'def
    have hsw : s N ≤ w := by
      have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j); rwa [time_zero] at this
    have hww' : w ≤ u' := time_mono_of_le (hsu N) (Nat.le_succ j)
    have hu'v : u' ≤ v := time_mono_of_le (hsu N) hjk
    have hu'1 : u' < 1 := hu'v.trans_lt hv1
    have hw1 : w < 1 := hww'.trans_lt hu'1
    have hw0 : 0 ≤ w := (hs0 N).trans hsw
    have hu'0 : 0 ≤ u' := hw0.trans hww'
    have hηw := Step2.etaT_pos' (hE2 N) hw1
    have hηu' := Step2.etaT_pos' (hE2 N) hu'1
    have hηws : etaT (E N) w ≤ etaT (E N) (s N) := by
      simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    have hηvw : etaT (E N) v ≤ etaT (E N) w := by
      simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    have hηtw : etaT (E N) (t N) ≤ etaT (E N) w := hηtv.trans hηvw
    have hηtu' : etaT (E N) (t N) ≤ etaT (E N) u' := by
      simp only [Step2.etaT_eq]
      exact mul_le_mul_of_nonneg_right (by linarith [hu'v, hvt]) hm0.le
    -- `ρ = (1-u_{j+1})/(1-u_k)`
    set ρ := (1 - u') / (1 - v) with hρdef
    have h1v : 0 < 1 - v := by linarith
    have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) h1v.le
    have hρw : ρ ≤ etaT (E N) w / etaT (E N) v := by
      rw [Step2.etaT_ratio (hE2 N)]; exact div_le_div_of_nonneg_right (by linarith) h1v.le
    have hρR : ρ ≤ R := by
      rw [hRdef, Step2.etaT_ratio (hE2 N)]; exact div_le_div_of_nonneg_right (by linarith) h1v.le
    have hρ4 : ρ ^ 4 ≤ q ^ 16 := by
      rw [hq16]; exact pow_le_pow_left₀ hρ0 hρR 4
    -- `ℓ`'s and `A_w`
    have hℓw1 : 1 ≤ (band d).ell N w := one_le_ellHat_of_nonneg hL1 hw0 hw1
    have hℓw0 : 0 < (band d).ell N w := by linarith
    have hℓwL : (band d).ell N w ≤ ((band d).L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hAw : A ≤ (band d).scale (E N) N w :=
      flowScale_antitoneOn hW0.le ((band d).L N) (E N) (Set.mem_Iic.2 hw1.le)
        (Set.mem_Iic.2 hv1.le) (hww'.trans hu'v)
    have hAw0 : 0 < (band d).scale (E N) N w := lt_of_lt_of_le hA0 hAw
    have hK1 : ((band d).ell N w / (band d).ell N (s N)) ^ 2 * etaT (E N) w ≤ etaT (E N) (s N) := by
      have hK := QVSum.ellHat_sq_mul_one_sub_le ((band d).L N) hw1 hsw
      change (band d).ell N w ^ 2 * (1 - w) ≤ (band d).ell N (s N) ^ 2 * (1 - s N) at hK
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      simp only [Step2.etaT_eq]
      calc (band d).ell N w ^ 2 * ((1 - w) * (mE (E N)).im)
          = ((band d).ell N w ^ 2 * (1 - w)) * (mE (E N)).im := by ring
        _ ≤ ((band d).ell N (s N) ^ 2 * (1 - s N)) * (mE (E N)).im :=
            mul_le_mul_of_nonneg_right hK hm0.le
        _ = (1 - s N) * (mE (E N)).im * (band d).ell N (s N) ^ 2 := by ring
    have hrq : ((band d).ell N w / (band d).ell N (s N)) ^ 2 ≤ q ^ 4 := by
      rw [hq4]
      calc ((band d).ell N w / (band d).ell N (s N)) ^ 2
          ≤ etaT (E N) (s N) / etaT (E N) w := by rw [le_div_iff₀ hηw]; exact hK1
        _ ≤ R := div_le_div_of_nonneg_left hηs.le hηv hηvw
    -- `J_w ≤ J_v`
    have hJw0 : 0 ≤ (N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w :=
      mul_nonneg (Real.rpow_nonneg hN0.le _) (mul_nonneg (Real.rpow_nonneg hN0.le _)
        (Real.rpow_nonneg (div_nonneg hηs.le hηw.le) _))
    have hJw : (N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w ≤ Jv := by
      have hRw : etaT (E N) (s N) / etaT (E N) w ≤ R := div_le_div_of_nonneg_left hηs.le hηv hηvw
      have h13 : (etaT (E N) (s N) / etaT (E N) w) ^ ((13 : ℝ) / 4) ≤ q ^ 13 := by
        have e : q ^ 13 = R ^ ((13 : ℝ) / 4) := by
          rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hR0]; norm_num
        rw [e]
        exact Real.rpow_le_rpow (div_nonneg hηs.le hηw.le) hRw (by norm_num)
      have hN48 : (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ δ = n ^ 48 := by
        rw [hnpow 48, ← Real.rpow_add hN0]; congr 1; push_cast; ring
      unfold thrFar
      calc (N : ℝ) ^ (2 * (δ / 4)) *
            ((N : ℝ) ^ δ * (etaT (E N) (s N) / etaT (E N) w) ^ ((13 : ℝ) / 4))
          = ((N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ δ) *
              (etaT (E N) (s N) / etaT (E N) w) ^ ((13 : ℝ) / 4) := by ring
        _ ≤ n ^ 48 * q ^ 13 := by rw [hN48]; gcongr
    -- far part: `QfF_j ρ⁴`
    have hcF : Lemma57.cFar2 ((band d).W N : ℝ) ((band d).ell N w) ≤ 2 * n ^ 4 :=
      (QVSum.cFar2_le_two_cNear2 hWe hℓw0).trans (by linarith [hcN4 _ hℓw1])
    have hfarR := farRate_point_le (W := ((band d).W N : ℝ)) (L := ((band d).L N : ℝ)) (D := D)
      (J := (N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w) (A := (band d).scale (E N) N w)
      (S := EarlyQVRateEv.sDet (band d) (E N) N w ((band d).ell N (s N)))
      (c2 := Lemma57.cFar2 ((band d).W N : ℝ) ((band d).ell N w)) (cF := 2 * n ^ 4)
      (r := (band d).ell N w / (band d).ell N (s N)) (Jv := Jv) (q := q) (Z := Zc) (ρ := ρ)
      (Rb := R) hW0 (Nat.cast_nonneg _) hηw hηv hηws hJw0 hJw hAw0 hZc0
      (by rw [hZcdef, ← pow_mul]; exact hz360.le.trans hAw) rfl (by positivity) hq0.le hrq
      (Lemma57.cFar2_nonneg hW1 hℓw0) hcF hρ0 hρw hρR
    have hTS : 2 * qvTimeShiftConst d N (E N) u' ^ 2 * step s u K N ^ 2 *
        ((band d).W N : ℝ) ^ (2 * D) ≤ TSb := by
      have hinv : (etaT (E N) u')⁻¹ ≤ N := (inv_anti₀ hηt0 hηtu').trans hηt
      have hCs := qvTimeShiftConst_le hN1' (card_idx_le hdim.1) hinv (inv_nonneg.2 hηu'.le)
      have hΔ' : step s u K N ≤ (N : ℝ) ^ (-((D + 10) + 10)) := by
        convert hΔN using 3; ring
      have h2 := two_Csh_sq_step_sq_le hN64' (D := D + 10) (by linarith)
        (qvTimeShiftConst_nonneg d N (E N) u') hCs hΔ0 hΔ' hW1 hWN
      have e : ((band d).W N : ℝ) ^ (2 * D) =
          ((band d).W N : ℝ) ^ (2 * (D + 10)) * ((band d).W N : ℝ) ^ (-(20 : ℝ)) := by
        rw [← Real.rpow_add hW0]; congr 1; ring
      rw [e]
      have h0 : 0 ≤ ((band d).W N : ℝ) ^ (-(20 : ℝ)) := hTSb0
      calc 2 * qvTimeShiftConst d N (E N) u' ^ 2 * step s u K N ^ 2 *
            (((band d).W N : ℝ) ^ (2 * (D + 10)) * ((band d).W N : ℝ) ^ (-(20 : ℝ)))
          = (2 * qvTimeShiftConst d N (E N) u' ^ 2 * step s u K N ^ 2 *
              ((band d).W N : ℝ) ^ (2 * (D + 10))) * ((band d).W N : ℝ) ^ (-(20 : ℝ)) := by ring
        _ ≤ 1 * ((band d).W N : ℝ) ^ (-(20 : ℝ)) := mul_le_mul_of_nonneg_right h2 h0
        _ = TSb := one_mul _
    have hQf : QfF d (E N) s u K δ (δ / 4) D (δ / 32) N j * ρ ^ 4 ≤
        2 * n * (P * G + 32 * WLD * Jv ^ 3 * q ^ 16) + TSb * q ^ 16 := by
      unfold QfF
      rw [← hwdef, ← hu'def]
      have hfar' : QVEndpoint.diagFarRate (band d) N ((band d).ell N w) (etaT (E N) w) D
          ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w)
          (EarlyQVRateEv.sDet (band d) (E N) N w ((band d).ell N (s N))) * ρ ^ 4 ≤
          P * G + 32 * WLD * Jv ^ 3 * q ^ 16 := by
        unfold QVEndpoint.diagFarRate
        refine hfarR.trans_eq ?_
        rw [hq16]
      have hTSρ : 2 * qvTimeShiftConst d N (E N) u' ^ 2 * step s u K N ^ 2 *
          ((band d).W N : ℝ) ^ (2 * D) * ρ ^ 4 ≤ TSb * q ^ 16 :=
        mul_le_mul hTS hρ4 (by positivity) hTSb0
      have e : (2 * (N : ℝ) ^ (δ / 32) *
            QVEndpoint.diagFarRate (band d) N ((band d).ell N w) (etaT (E N) w) D
              ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w)
              (EarlyQVRateEv.sDet (band d) (E N) N w ((band d).ell N (s N)))
          + 2 * qvTimeShiftConst d N (E N) u' ^ 2 * step s u K N ^ 2 *
            ((band d).W N : ℝ) ^ (2 * D)) * ρ ^ 4
          = 2 * n * (QVEndpoint.diagFarRate (band d) N ((band d).ell N w) (etaT (E N) w) D
              ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w)
              (EarlyQVRateEv.sDet (band d) (E N) N w ((band d).ell N (s N))) * ρ ^ 4)
            + 2 * qvTimeShiftConst d N (E N) u' ^ 2 * step s u K N ^ 2 *
              ((band d).W N : ℝ) ^ (2 * D) * ρ ^ 4 := by rw [hndef]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hfar' (by positivity : (0 : ℝ) ≤ 2 * n)
      linarith only [this, hTSρ]
    -- near part: `QnF_j · leak²`
    have hQn : QnF d (E N) s u K δ (δ / 4) D (δ / 32) N j ≤ 8 * (N : ℝ) ^ 8 := by
      unfold QnF
      rw [← hwdef]
      have hnear : QVEndpoint.diagNearRate (band d) N ((band d).ell N w)
          ((band d).ell N (s N)) (etaT (E N) w) ≤ 2 * (N : ℝ) ^ 7 := by
        unfold QVEndpoint.diagNearRate
        have hηinv : (etaT (E N) w)⁻¹ ≤ N := (inv_anti₀ hηt0 hηtw).trans hηt
        have hc : Lemma57.cNear2 ((band d).W N : ℝ) ((band d).ell N w) ≤ N :=
          (hcN4 _ hℓw1).trans hn4N
        have hc0 := Lemma57.cNear2_nonneg hW1 hℓw0
        have hr : (band d).ell N w / (band d).ell N (s N) ≤ N := by
          calc (band d).ell N w / (band d).ell N (s N) ≤ (band d).ell N w / 1 :=
                div_le_div_of_nonneg_left hℓw0.le zero_lt_one hℓs1
            _ = (band d).ell N w := div_one _
            _ ≤ N := hℓwL.trans hLN
        have hr5 : ((band d).ell N w / (band d).ell N (s N)) ^ 5 ≤ (N : ℝ) ^ 5 :=
          pow_le_pow_left₀ (by positivity) hr 5
        calc 2 * (etaT (E N) w)⁻¹ * Lemma57.cNear2 ((band d).W N : ℝ) ((band d).ell N w) *
              ((band d).ell N w / (band d).ell N (s N)) ^ 5
            ≤ 2 * (N : ℝ) * N * (N : ℝ) ^ 5 := by gcongr
          _ = 2 * (N : ℝ) ^ 7 := by ring
      have hnE : EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ) ((band d).ell N w)
          (etaT (E N) w) D ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w) ≤ 1 := by
        have hNinv : (N : ℝ)⁻¹ ≤ etaT (E N) w := by
          have : (N : ℝ)⁻¹ ≤ etaT (E N) (t N) := by
            rw [inv_le_comm₀ hN0 hηt0]; exact hηt
          exact this.trans hηtw
        have hAw1 : 1 ≤ ((band d).W N : ℝ) * (band d).ell N w * etaT (E N) w := hA1.trans hAw
        have hAwN : ((band d).W N : ℝ) * (band d).ell N w * etaT (E N) w ≤ N := by
          have hη1 : etaT (E N) w ≤ 1 := hηws.trans hηs1
          calc ((band d).W N : ℝ) * (band d).ell N w * etaT (E N) w
              ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) * 1 := by gcongr
            _ ≤ N := by linarith
        have hJN : (N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w ≤ (N : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact hJw.trans hJvN
        have h := EEDef.nearEpsilon_le_inv (D := D) hWe (by positivity) hℓw0 hηw hN1'
          zero_le_one hJw0 (by linarith only [hD]) hNinv hAw1 hAwN hWL hNW hJN
          (by nlinarith only [hlogW, hD0]) (by nlinarith only [hlogW, hD0])
        exact h.trans (inv_le_one_of_one_le₀ hW1)
      have hn' : (N : ℝ) ^ (δ / 32) ≤ N := hnN
      have hnear0 : 0 ≤ QVEndpoint.diagNearRate (band d) N ((band d).ell N w)
          ((band d).ell N (s N)) (etaT (E N) w) := diagNearRate_nonneg' (band d) N hW1 hℓw0 hℓs0 hηw
      have hnE0 : 0 ≤ EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ) ((band d).ell N w)
          (etaT (E N) w) D ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w) :=
        nearEpsilon_nonneg' hW0.le (Nat.cast_nonneg _)
      have hN8 : (N : ℝ) ≤ (N : ℝ) ^ 8 := by
        calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hN1' (by norm_num)
      calc 2 * (N : ℝ) ^ (δ / 32) * (QVEndpoint.diagNearRate (band d) N ((band d).ell N w)
            ((band d).ell N (s N)) (etaT (E N) w) + 2 * EEDef.nearEpsilon ((band d).W N : ℝ)
              ((band d).L N : ℝ) ((band d).ell N w) (etaT (E N) w) D
              ((N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w))
          ≤ 2 * (N : ℝ) * (2 * (N : ℝ) ^ 7 + 2 * 1) := by gcongr
        _ = 4 * (N : ℝ) ^ 8 + 4 * N := by ring
        _ ≤ 8 * (N : ℝ) ^ 8 := by linarith only [hN8]
    have hleak : leak d (E N) s u K D N k j ^ 2 ≤
        4 * (128 * Real.exp 3) ^ 2 * q ^ 16 *
          Real.exp (-(Real.log ((band d).W N : ℝ) ^ (3 / 2 : ℝ))) := by
      unfold leak
      rw [← hu'def, ← hvdef]
      have hT0 : tailT (d.W N : ℝ) (ellHat (d.L N) (u' : ℂ)) ((1 - u') * (mE (E N)).im) D 0
          ≤ 2 := by
        have hA' : 1 ≤ (d.W N : ℝ) * ellHat (d.L N) (u' : ℂ) * ((1 - u') * (mE (E N)).im) := by
          have hAu' : A ≤ (band d).scale (E N) N u' :=
            flowScale_antitoneOn hW0.le ((band d).L N) (E N) (Set.mem_Iic.2 hu'1.le)
              (Set.mem_Iic.2 hv1.le) hu'v
          exact hA1.trans hAu'
        unfold tailT
        have h1 : ((((d.W N : ℝ) * ellHat (d.L N) (u' : ℂ) * ((1 - u') * (mE (E N)).im)) ^ 2))⁻¹
            ≤ 1 :=
          inv_le_one_of_one_le₀ (one_le_pow₀ hA')
        have h2 : Real.exp (-Real.sqrt (0 / ellHat (d.L N) (u' : ℂ))) = 1 := by simp
        have h3 : (d.W N : ℝ) ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
        rw [h2, mul_one]; linarith only [h1, h3]
      have hT00 : 0 ≤ tailT (d.W N : ℝ) (ellHat (d.L N) (u' : ℂ)) ((1 - u') * (mE (E N)).im) D 0 :=
        tailT_nonneg hW0.le _
      have hℓv0 : 0 < ellHat (d.L N) (v : ℂ) := Step3.ellHat_pos_of_lt_one hL1 hv1
      have hstar : ellStar (d.W N : ℝ) (ellHat (d.L N) (v : ℂ)) / ellHat (d.L N) (v : ℂ) =
          Real.log ((band d).W N : ℝ) ^ (3 / 2 : ℝ) := by
        unfold ellStar; field_simp; rfl
      rw [hstar]
      set y := Real.log ((band d).W N : ℝ) ^ (3 / 2 : ℝ) with hy
      have hexp : Real.exp (-(y / 2)) ^ 2 = Real.exp (-y) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hρ2 : ((1 - u') / (1 - v)) ^ 2 ≥ 0 := by positivity
      calc (tailT (d.W N : ℝ) (ellHat (d.L N) (u' : ℂ)) ((1 - u') * (mE (E N)).im) D 0 *
            (128 * Real.exp 3 * ((1 - u') / (1 - v)) ^ 2 * Real.exp (-(y / 2)))) ^ 2
          = tailT (d.W N : ℝ) (ellHat (d.L N) (u' : ℂ)) ((1 - u') * (mE (E N)).im) D 0 ^ 2 *
              (128 * Real.exp 3) ^ 2 * ρ ^ 4 * Real.exp (-(y / 2)) ^ 2 := by rw [hρdef]; ring
        _ ≤ 2 ^ 2 * (128 * Real.exp 3) ^ 2 * q ^ 16 * Real.exp (-(y / 2)) ^ 2 := by
            gcongr
        _ = 4 * (128 * Real.exp 3) ^ 2 * q ^ 16 * Real.exp (-y) := by rw [hexp]; ring
    have hQn0 : 0 ≤ QnF d (E N) s u K δ (δ / 4) D (δ / 32) N j := by
      unfold QnF
      have := diagNearRate_nonneg' (band d) N hW1 hℓw0 hℓs0 hηw
      have := nearEpsilon_nonneg' (W := ((band d).W N : ℝ)) (L := ((band d).L N : ℝ))
        (ℓu := (band d).ell N w) (ηu := etaT (E N) w) (D := D)
        (J := (N : ℝ) ^ (2 * (δ / 4)) * thrFar (E N) s δ N w) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _)
      positivity
    have hQf0 : 0 ≤ QfF d (E N) s u K δ (δ / 4) D (δ / 32) N j := by
      unfold QfF
      have := diagFarRate_nonneg' (band d) N (D := D)
        (Smax := EarlyQVRateEv.sDet (band d) (E N) N w ((band d).ell N (s N))) hW1 hℓw0 hηw hJw0
      have := qvTimeShiftConst_nonneg d N (E N) u'
      have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    -- combine
    have hcZ : cZFar d (E N) s u K δ (δ / 4) D (δ / 32) Cc N k a j =
        step s u K N * (Real.sqrt (QnF d (E N) s u K δ (δ / 4) D (δ / 32) N j) *
            leak d (E N) s u K D N k j
          + Real.sqrt (QfF d (E N) s u K δ (δ / 4) D (δ / 32) N j) * ρ ^ 2 * ξ * T) ^ 2
        + step s u K N * (N : ℝ) ^ (-Cc) := by
      unfold cZFar
      split_ifs with h
      · rfl
      · exact absurd hfar h
    rw [hcZ]
    set X := Real.sqrt (QnF d (E N) s u K δ (δ / 4) D (δ / 32) N j) * leak d (E N) s u K D N k j
      with hX
    set Y := Real.sqrt (QfF d (E N) s u K δ (δ / 4) D (δ / 32) N j) * ρ ^ 2 * ξ * T with hY
    have hX2 : X ^ 2 ≤ Xb := by
      rw [hX, mul_pow, Real.sq_sqrt hQn0, hXbdef]
      exact mul_le_mul hQn hleak (sq_nonneg _) (by positivity)
    have hY2 : Y ^ 2 ≤ ξ ^ 2 * T ^ 2 * (2 * n * (P * G + 32 * WLD * Jv ^ 3 * q ^ 16)
        + TSb * q ^ 16) := by
      have e : Y ^ 2 = ξ ^ 2 * T ^ 2 * (QfF d (E N) s u K δ (δ / 4) D (δ / 32) N j * ρ ^ 4) := by
        rw [hY, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hQf0]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hQf (by positivity)
    have hXY : (X + Y) ^ 2 ≤ M := by
      have : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith only [sq_nonneg (X - Y)]
      rw [hMdef]; linarith only [this, hX2, hY2]
    have := mul_le_mul_of_nonneg_left hXY hΔ0
    linarith only [this]
  -- summing
  have hsum : ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ (δ / 4) D (δ / 32) Cc N k a j ≤
      (k : ℝ) * step s u K N * M + (N : ℝ) ^ (-Cc) * step s u K N * k := by
    calc ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ (δ / 4) D (δ / 32) Cc N k a j
        ≤ ∑ _j ∈ Finset.range k, (step s u K N * M + step s u K N * (N : ℝ) ^ (-Cc)) :=
          Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- the final normalisation
  have hkΔ0 : 0 ≤ (k : ℝ) * step s u K N := by positivity
  have hkΔ1 : (k : ℝ) * step s u K N ≤ 1 - s N := by rw [hkΔ]; linarith
  have hkΔle : (k : ℝ) * step s u K N ≤ 1 := by linarith [hs0 N]
  have hPid : (1 - s N) * P = q ^ 16 / (mE (E N)).im := by
    rw [hq16, hPdef, hRdef]
    have e : etaT (E N) (s N) = (1 - s N) * (mE (E N)).im := rfl
    rw [e]; field_simp
  have hkM : (k : ℝ) * step s u K N * M ≤ 2 * Xb + 2 * ξ ^ 2 * T ^ 2 *
      (2 * n * (q ^ 16 / (mE (E N)).im * G + 32 * WLD * Jv ^ 3 * q ^ 16) + TSb * q ^ 16) := by
    set κ := (k : ℝ) * step s u K N with hκ
    have hκP : κ * P ≤ q ^ 16 / (mE (E N)).im := by
      rw [← hPid]; exact mul_le_mul_of_nonneg_right hkΔ1 hP0
    have e : κ * M = κ * (2 * Xb) + 2 * ξ ^ 2 * T ^ 2 *
        (2 * n * ((κ * P) * G + κ * (32 * WLD * Jv ^ 3 * q ^ 16)) + κ * (TSb * q ^ 16)) := by
      rw [hMdef]; ring
    rw [e]
    have h1 : κ * (2 * Xb) ≤ 2 * Xb := by nlinarith only [hkΔle, hkΔ0, hXb0]
    have h2 : κ * (32 * WLD * Jv ^ 3 * q ^ 16) ≤ 32 * WLD * Jv ^ 3 * q ^ 16 := by
      have : 0 ≤ 32 * WLD * Jv ^ 3 * q ^ 16 := by positivity
      nlinarith only [hkΔle, hkΔ0, this]
    have h3 : κ * (TSb * q ^ 16) ≤ TSb * q ^ 16 := by
      have : 0 ≤ TSb * q ^ 16 := by positivity
      nlinarith only [hkΔle, hkΔ0, this]
    have h4 : (κ * P) * G ≤ q ^ 16 / (mE (E N)).im * G := mul_le_mul_of_nonneg_right hκP hG0
    have hc : 0 ≤ 2 * ξ ^ 2 * T ^ 2 := by positivity
    have hin : 2 * n * ((κ * P) * G + κ * (32 * WLD * Jv ^ 3 * q ^ 16)) + κ * (TSb * q ^ 16)
        ≤ 2 * n * (q ^ 16 / (mE (E N)).im * G + 32 * WLD * Jv ^ 3 * q ^ 16) + TSb * q ^ 16 := by
      have : 0 ≤ 2 * n := by positivity
      have h5 := mul_le_mul_of_nonneg_left (add_le_add h4 h2) this
      linarith only [h5, h3]
    linarith only [h1, mul_le_mul_of_nonneg_left hin hc]
  -- the three absorption hypotheses of the assembly
  have hz360N : z ^ 360 ≤ N := hz360.le.trans hAN
  have hconst : 65536 / (mE (E N)).im ≤ n := by
    have h1 : 65536 / (mE (E N)).im ≤ 65536 / mκ :=
      div_le_div_of_nonneg_left (by norm_num) hmκpos (hmge N)
    exact h1.trans hcst
  have hWLD : 1024 * z ^ 360 * WLD ≤ 1 := by
    have hWD : ((band d).W N : ℝ) ^ (-D) ≤ (((band d).W N : ℝ) ^ 64)⁻¹ := by
      calc ((band d).W N : ℝ) ^ (-D) ≤ ((band d).W N : ℝ) ^ (-(64 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = (((band d).W N : ℝ) ^ 64)⁻¹ := by
            rw [Real.rpow_neg hW0.le]; norm_cast
    have hWD0 : 0 ≤ ((band d).W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    have h60 : (1024 : ℝ) ≤ ((band d).W N : ℝ) ^ 60 := by
      calc (1024 : ℝ) ≤ 2 ^ 60 := by norm_num
        _ ≤ ((band d).W N : ℝ) ^ 60 := pow_le_pow_left₀ (by norm_num) hW2 60
    calc 1024 * z ^ 360 * WLD
        ≤ 1024 * N * (N * ((band d).W N : ℝ) ^ (-D)) := by
          rw [hWLDdef]; gcongr
      _ ≤ 1024 * ((band d).W N : ℝ) ^ 2 * (((band d).W N : ℝ) ^ 2 *
            (((band d).W N : ℝ) ^ 64)⁻¹) := by gcongr
      _ = 1024 / ((band d).W N : ℝ) ^ 60 := by field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact h60
  have hTSabs : 16 * z ^ 360 * TSb ≤ 1 := by
    have e : TSb = (((band d).W N : ℝ) ^ 20)⁻¹ := by
      rw [hTSbdef, Real.rpow_neg hW0.le]; norm_cast
    have h18 : (16 : ℝ) ≤ ((band d).W N : ℝ) ^ 18 := by
      calc (16 : ℝ) ≤ 2 ^ 18 := by norm_num
        _ ≤ ((band d).W N : ℝ) ^ 18 := pow_le_pow_left₀ (by norm_num) hW2 18
    rw [e]
    calc 16 * z ^ 360 * (((band d).W N : ℝ) ^ 20)⁻¹
        ≤ 16 * ((band d).W N : ℝ) ^ 2 * (((band d).W N : ℝ) ^ 20)⁻¹ := by
          gcongr; exact hz360N.trans hNW
      _ = 16 / ((band d).W N : ℝ) ^ 18 := by field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact h18
  have hXabs : 16 * z ^ 360 * Xb ≤ T ^ 2 := by
    have hq16N : q ^ 16 ≤ (N : ℝ) ^ 4 := by
      rw [hq16]; exact pow_le_pow_left₀ hR0 hRN 4
    have hN13 : (N : ℝ) ^ 13 ≤ ((band d).W N : ℝ) ^ 26 := by
      calc (N : ℝ) ^ 13 ≤ (((band d).W N : ℝ) ^ 2) ^ 13 := pow_le_pow_left₀ hN0.le hNW 13
        _ = ((band d).W N : ℝ) ^ 26 := by ring
    have he : (128 * Real.exp 3) ^ 2 = 16384 * Real.exp 6 := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    set ey := Real.exp (-(Real.log ((band d).W N : ℝ) ^ (3 / 2 : ℝ))) with hey
    have hey0 : 0 ≤ ey := (Real.exp_pos _).le
    have habs := leak_absorb hD0 hWbig2
    calc 16 * z ^ 360 * Xb
        = 16 * z ^ 360 * (8 * (N : ℝ) ^ 8 * (4 * (128 * Real.exp 3) ^ 2 * q ^ 16 * ey)) := by
          rw [hXbdef]
      _ ≤ 16 * N * (8 * (N : ℝ) ^ 8 * (4 * (128 * Real.exp 3) ^ 2 * (N : ℝ) ^ 4 * ey)) := by
          gcongr
      _ = 2 ^ 23 * Real.exp 6 * (N : ℝ) ^ 13 * ey := by rw [he]; ring
      _ ≤ 2 ^ 23 * Real.exp 6 * ((band d).W N : ℝ) ^ 26 * ey := by gcongr
      _ ≤ ((band d).W N : ℝ) ^ (-(2 * D)) := habs
      _ ≤ T ^ 2 := hT2W
  have hass := farQV_assembly hn1 hq1 hz1 hnz hqz hm0 hconst hξ0 hξn (cF := 2 * n ^ 4)
    (by positivity) le_rfl hWLD0 hWLD hTSb0 hTSabs hXb0 hXabs
  have hA572 : A ^ (-(5 : ℝ) / 72) = (z ^ 25)⁻¹ := by
    rw [← hz360, ← Real.rpow_natCast z 360, ← Real.rpow_mul hz0.le, ← Real.rpow_natCast z 25,
      ← Real.rpow_neg hz0.le]
    norm_num
  rw [hA572]
  have hfin : (k : ℝ) * step s u K N * M ≤ (z ^ 25)⁻¹ * T ^ 2 := hkM.trans hass
  linarith only [hsum, hfin]

set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
-- the `highProb_azuma_grid_plainN` route with a label-dependent threshold; `hκ1`, `hB` are regime
-- binders (unused here)
/-- **The far-field martingale is small with high probability**: for every `D₁ > 0`, eventually,
the probability that at some grid time `k` and far pair `a` the stopped martingale sum is at
least `N^{δ/8} T_{u_k,D}` is at most `N^{-D₁}`. `κ, hκ0, hκ1` are used by `farQV_sum_leN`; `hB` is
(2.68)–(2.70) at `s`. -/
theorem highProb_farMart_grid_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t u : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {δ D : ℝ} (hδ0 : 0 < δ)
    (hδc : δ ≤ c / 90) (hD : 64 ≤ D) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) {ω | ∃ k ≤ gridK D (D₁ + 2) N, ∃ a : LoopArg (d.L N) 2,
          6 * ellStar ((band d).W N : ℝ) ((band d).ell N (time s u (gridK D (D₁ + 2)) N k))
              < (zdist (d.L N) (a 0 - a 1) : ℝ) ∧
          (N : ℝ) ^ (δ / 8) * Step2.tT (band d) (E N) N D (time s u (gridK D (D₁ + 2)) N k)
              (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (min k (gridTauFar d (E N) D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96)
                (δ / 192) s u (gridK D (D₁ + 2)) N ω)),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D (D₁ + 2)) N (j + 1) : ℂ)
                (time s u (gridK D (D₁ + 2)) N k : ℂ)
                (Zvec (band d) (E N) s u (gridK D (D₁ + 2)) N (j + 1) ω)) a‖}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  intro D₁ hD₁
  set K := gridK D (D₁ + 2) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := fun N => gridK_ne_zero D (D₁ + 2) N
  have hD0 : 0 ≤ D := by linarith
  have hCK : 0 ≤ CK D (D₁ + 2) := by unfold CK; linarith
  have hδ8 : 0 < δ / 8 := by positivity
  have hΔ : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-(D + 20)) :=
    eventually_step_gridK_le hs0 hut ht1 hD0 hD₁.le
  set τ₁ : ℝ := δ / 32 with hτ₁
  set ε : ℝ := δ / 4 with hε
  filter_upwards [hsubG_gridTauFar_plainN hE2 hs0 hst ht1 hc0 hreg0 hAc hδ0.le hδc hD0 τ₁ ε
      (δ / 96) (δ / 96) (δ / 192) hsu hut K hK0 (2 * D),
    farQV_sum_leN hκ0 hEκ hs0 hst ht1 hc0 hreg0 hAc hδ0 hδc hD hsu hut K hK0 hΔ (2 * D),
    gridK_card_le hCK, eventually_mul_exp_neg_rpow_le 4 (CK D (D₁ + 2) + 2 + 2) hδ8 D₁,
    eventually_le_rpow 8 hδ8, hAc, d.dim, eventually_ge_atTop 1]
    with N hsub hfarQV hKN hsmall h8 hAcN hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set τN : Ωg d → ℕ := fun ω => gridTauFar d (E N) D δ τ₁ ε (δ / 96) (δ / 96) (δ / 192) s u K N ω
    with hτN
  -- `T ≥ N^{-D} > 0`
  have hWN : ((band d).W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ d.L N := by exact_mod_cast (by have := d.three_le_L N; omega : 1 ≤ d.L N)
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
    change (d.W N : ℝ) ≤ N
    nlinarith only [hL, h', hW0]
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
  have hTlow : ∀ k : ℕ, ∀ a : LoopArg (d.L N) 2, (N : ℝ) ^ (-D) ≤
      Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) := by
    intro k a
    exact (Real.rpow_le_rpow_of_nonpos (by linarith) hWN (by linarith)).trans
      (rpow_neg_le_tailT _)
  have hTpos : ∀ k : ℕ, ∀ a : LoopArg (d.L N) 2,
      0 < Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) :=
    fun k a => lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (hTlow k a)
  -- the thresholds
  set x : ℕ → LoopArg (d.L N) 2 → ℝ := fun k a =>
    if 6 * ellStar ((band d).W N : ℝ) ((band d).ell N (time s u K N k)) <
        (zdist (d.L N) (a 0 - a 1) : ℝ) then
      (N : ℝ) ^ (δ / 8) * Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))
    else (N : ℝ) ^ (δ / 8) *
      Real.sqrt (4 * ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j + 1)
    with hxdef
  have hxpos : ∀ k a, 0 < x k a := by
    intro k a
    rw [hxdef]
    dsimp only
    split_ifs
    · exact mul_pos (Real.rpow_pos_of_pos hN0 _) (hTpos k a)
    · have hS : 0 ≤ ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j :=
        Finset.sum_nonneg fun j _ => cZFar_nonneg (hsu N) k a j
      exact mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_pos.2 (by linarith))
  set Ev : Set (Ωg d) := {ω | ∃ k ≤ K N, ∃ a : LoopArg (d.L N) 2,
      6 * ellStar ((band d).W N : ℝ) ((band d).ell N (time s u K N k))
          < (zdist (d.L N) (a 0 - a 1) : ℝ) ∧
      (N : ℝ) ^ (δ / 8) * Step2.tT (band d) (E N) N D (time s u K N k)
          (zdist (d.L N) (a 0 - a 1)) ≤
      ‖(∑ j ∈ Finset.range (min k (τN ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) (E N) s u K N (j + 1) ω)) a‖} with hEv
  change (Pg d) Ev ≤ _
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  rcases hΔ0.eq_or_lt with hΔ | hΔ
  · -- `Δ = 0`: every sum vanishes, the event is empty
    have hall : Ev = ∅ := by
      ext ω
      simp only [hEv, Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq, not_exists, not_and]
      intro k _ a _
      have h0 : ∀ j, Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
          (time s u K N k : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω) a = 0 := fun j =>
        Uker_apply_eq_zero_of _ _ _
          (fun b => Zvec_succ_eq_zero_of_step (E := (E N)) hΔ.symm j ω b) a
      rw [Finset.sum_apply]
      simp only [h0, Finset.sum_const_zero, norm_zero, not_le]
      exact mul_pos (Real.rpow_pos_of_pos hN0 _) (hTpos k a)
    rw [hall, measure_empty]; exact zero_le
  · -- `Δ > 0`
    have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j =>
      lt_gridTauFar_measurableSet (hE2 N) D δ τ₁ ε (δ / 96) (δ / 96) (δ / 192) s u K N j
    have hZ : ∀ i, StronglyMeasurable[filt d i] (ZvecCut (d := d) (E N) s u K N i) := fun i =>
      stronglyMeasurable_ZvecCut (hE2 N) hsu hut ht1 hK0 N i
    have hsub' : ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2, ∀ j < k,
        HasCondSubgaussianMGF (filt d j) ((filt d).le j)
          (fun ω => ({ω' | j < τN ω'}.indicator
            (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
              (time s u K N k : ℂ) (ZvecCut (d := d) (E N) s u K N (j + 1) ω') a) ω).re)
          (cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j).toNNReal (Pg d) ∧
        HasCondSubgaussianMGF (filt d j) ((filt d).le j)
          (fun ω => ({ω' | j < τN ω'}.indicator
            (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
              (time s u K N k : ℂ) (ZvecCut (d := d) (E N) s u K N (j + 1) ω') a) ω).im)
          (cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j).toNNReal (Pg d) := by
      intro k hk a j hj
      rw [ZvecCut_succ (by omega)]
      exact hsub k hk a j hj
    have hx : ∀ k ≤ K N, ∀ a, 0 ≤ x k a := fun k _ a => (hxpos k a).le
    -- the union lemma's `hx0`, discharged
    have hx0 : ∀ a, 0 < x 0 a := fun a => hxpos 0 a
    have hU := stopped_duhamel_azuma_union (μ := Pg d) (d.L N) (ξ := fun _ => (1 : ℂ))
      (u := time s u K N) hτmeas hZ (K N) hsub' hx hx0
    set Sbad : Set (Ωg d) := {ω | ∃ k ≤ K N, ∃ a, x k a ≤
        ‖(∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (ZvecCut (d := d) (E N) s u K N (j + 1) ω)) a‖} with hSbad
    have hsubset : Ev ⊆ Sbad := by
      rintro ω ⟨k, hk, a, hfar, ha⟩
      refine ⟨k, hk, a, ?_⟩
      have hxk : x k a = (N : ℝ) ^ (δ / 8) *
          Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) := by
        rw [hxdef]; dsimp only; simp only [hfar, ↓reduceIte]
      have hsum : (∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (ZvecCut (d := d) (E N) s u K N (j + 1) ω))
          = ∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
            (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
              (Zvec (band d) (E N) s u K N (j + 1) ω) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j < min k (τN ω) := Finset.mem_range.1 hj
        rw [ZvecCut_succ (by omega)]
      rw [hsum, hxk]; exact ha
    -- the per-summand bound
    have hterm : ∀ k ∈ Finset.Icc 1 (K N), ∀ a : LoopArg (d.L N) 2,
        4 * Real.exp (-(x k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j).toNNReal : ℝ)))
          ≤ 4 * Real.exp (-(N : ℝ) ^ (δ / 8)) := by
      intro k hk a
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hkK : k ≤ K N := (Finset.mem_Icc.1 hk).2
      have hcoe : ∑ j ∈ Finset.range k,
          ((cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j).toNNReal : ℝ)
          = ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j :=
        Finset.sum_congr rfl fun j _ => Real.coe_toNNReal _ (cZFar_nonneg (hsu N) k a j)
      rw [hcoe]
      set Sk := ∑ j ∈ Finset.range k, cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j with hSk
      have hSk0 : 0 < Sk := by
        have h1 : step s u K N * (N : ℝ) ^ (-(2 * D)) ≤ Sk := by
          have := Finset.single_le_sum (f := fun j => cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j)
            (fun j _ => cZFar_nonneg (hsu N) k a j) (Finset.mem_range.2 hk1)
          exact (floor_le_cZFar (hsu N) k a 0).trans this
        exact lt_of_lt_of_le (mul_pos hΔ (Real.rpow_pos_of_pos hN0 _)) h1
      have hN8 : 0 < (N : ℝ) ^ (δ / 8) := Real.rpow_pos_of_pos hN0 _
      have hsq8 : ((N : ℝ) ^ (δ / 8)) ^ 2 = (N : ℝ) ^ (δ / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      have hle : (N : ℝ) ^ (δ / 8) * (4 * Sk) ≤ x k a ^ 2 := by
        by_cases hfar : 6 * ellStar ((band d).W N : ℝ) ((band d).ell N (time s u K N k)) <
            (zdist (d.L N) (a 0 - a 1) : ℝ)
        · have hxk : x k a = (N : ℝ) ^ (δ / 8) *
              Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) := by
            rw [hxdef]; dsimp only; simp only [hfar, ↓reduceIte]
          set T := Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) with hT
          have hq := hfarQV k hkK a hfar
          rw [← hSk, ← hT] at hq
          -- `Σ c ≤ 2 T²`
          have hkΔ : step s u K N * k ≤ 1 := by
            have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 N)
            have hKΔ : (K N : ℝ) * step s u K N = u N - s N := by unfold step; field_simp
            have : (k : ℝ) ≤ K N := by exact_mod_cast hkK
            have := mul_le_mul_of_nonneg_right this hΔ0
            nlinarith only [this, hKΔ, hs0 N, hut N, ht1 N]
          have hfl : (N : ℝ) ^ (-(2 * D)) * step s u K N * k ≤ T ^ 2 := by
            have h2D : (N : ℝ) ^ (-(2 * D)) = ((N : ℝ) ^ (-D)) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
            have hT2 : ((N : ℝ) ^ (-D)) ^ 2 ≤ T ^ 2 :=
              pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) (hTlow k a) 2
            calc (N : ℝ) ^ (-(2 * D)) * step s u K N * k
                = (N : ℝ) ^ (-(2 * D)) * (step s u K N * k) := by ring
              _ ≤ (N : ℝ) ^ (-(2 * D)) * 1 :=
                  mul_le_mul_of_nonneg_left hkΔ (Real.rpow_nonneg hN0.le _)
              _ = ((N : ℝ) ^ (-D)) ^ 2 := by rw [mul_one, h2D]
              _ ≤ T ^ 2 := hT2
          have hA1 : (band d).scale (E N) N (time s u K N k) ^ (-(5 : ℝ) / 72) ≤ 1 := by
            have hkt : time s u K N k ≤ t N := by
              have := time_mono_of_le (K := K) (hsu N) hkK
              rw [time_last s u K N (hK0 N)] at this; linarith [hut N]
            have hk1' : time s u K N k < 1 := time_lt_one_of_le hsu hut ht1 hK0 hkK
            have hAtv : (band d).scale (E N) N (t N) ≤ (band d).scale (E N) N (time s u K N k) :=
              flowScale_antitoneOn (by linarith) ((band d).L N) (E N) (Set.mem_Iic.2 hk1'.le)
                (Set.mem_Iic.2 (ht1 N).le) hkt
            have hA : 1 ≤ (band d).scale (E N) N (time s u K N k) :=
              ((Real.one_le_rpow hN1' hc0.le).trans hAcN).trans hAtv
            exact Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
          have hS2 : Sk ≤ 2 * T ^ 2 := by
            have hT20 : 0 ≤ T ^ 2 := sq_nonneg _
            have := mul_le_mul_of_nonneg_right hA1 hT20
            linarith only [hq, hfl, this]
          rw [hxk, mul_pow, hsq8]
          have h8' : 8 * (N : ℝ) ^ (δ / 8) ≤ (N : ℝ) ^ (δ / 4) := by
            have e : (N : ℝ) ^ (δ / 4) = (N : ℝ) ^ (δ / 8) * (N : ℝ) ^ (δ / 8) := by
              rw [← Real.rpow_add hN0]; congr 1; ring
            rw [e]; exact mul_le_mul_of_nonneg_right h8 hN8.le
          have hT20 : 0 ≤ T ^ 2 := sq_nonneg _
          calc (N : ℝ) ^ (δ / 8) * (4 * Sk) ≤ (N : ℝ) ^ (δ / 8) * (8 * T ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith only [hS2]) hN8.le
            _ = (8 * (N : ℝ) ^ (δ / 8)) * T ^ 2 := by ring
            _ ≤ (N : ℝ) ^ (δ / 4) * T ^ 2 := mul_le_mul_of_nonneg_right h8' hT20
        · have hxk : x k a = (N : ℝ) ^ (δ / 8) * Real.sqrt (4 * Sk + 1) := by
            rw [hxdef]; dsimp only; simp only [hfar, ↓reduceIte]; rfl
          rw [hxk, mul_pow, hsq8, Real.sq_sqrt (by linarith)]
          have hN14 : (N : ℝ) ^ (δ / 8) ≤ (N : ℝ) ^ (δ / 4) :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
          calc (N : ℝ) ^ (δ / 8) * (4 * Sk) ≤ (N : ℝ) ^ (δ / 4) * (4 * Sk) :=
                mul_le_mul_of_nonneg_right hN14 (by linarith)
            _ ≤ (N : ℝ) ^ (δ / 4) * (4 * Sk + 1) :=
                mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hN0.le _)
      have h4S : 0 < 4 * Sk := by linarith
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ h4S]
      exact hle
    have hLN : (d.L N : ℝ) ≤ N := by
      have hW : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
      have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
      nlinarith only [hW, h', (Nat.cast_nonneg (d.L N) : (0 : ℝ) ≤ d.L N)]
    have hsum_le : ∑ k ∈ Finset.Icc 1 (K N), ∑ a : LoopArg (d.L N) 2,
        4 * Real.exp (-(x k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZFar d (E N) s u K δ ε D τ₁ (2 * D) N k a j).toNNReal : ℝ)))
        ≤ (N : ℝ) ^ (-D₁) := by
      calc _ ≤ ∑ _k ∈ Finset.Icc 1 (K N), ∑ _a : LoopArg (d.L N) 2,
            4 * Real.exp (-(N : ℝ) ^ (δ / 8)) :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => hterm k hk a
        _ = (K N : ℝ) * ((d.L N : ℝ) ^ 2 * (4 * Real.exp (-(N : ℝ) ^ (δ / 8)))) := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, card_loopArg_two,
              Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
            push_cast; ring
        _ ≤ (N : ℝ) ^ (CK D (D₁ + 2) + 2) *
            ((N : ℝ) ^ (2 : ℝ) * (4 * Real.exp (-(N : ℝ) ^ (δ / 8)))) := by
            have hK : (K N : ℝ) ≤ (N : ℝ) ^ (CK D (D₁ + 2) + 2) := by
              have : (K N : ℝ) ≤ ((K N + 1 : ℕ) : ℝ) := by push_cast; linarith
              exact this.trans hKN
            have hL2 : (d.L N : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 : ℝ) := by
              rw [Real.rpow_two]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hLN 2
            have he : 0 ≤ 4 * Real.exp (-(N : ℝ) ^ (δ / 8)) := by positivity
            have hL0 : 0 ≤ (d.L N : ℝ) ^ 2 := by positivity
            gcongr
        _ = 4 * (N : ℝ) ^ (CK D (D₁ + 2) + 2 + 2) * Real.exp (-(N : ℝ) ^ (δ / 8)) := by
            rw [Real.rpow_add hN0 (CK D (D₁ + 2) + 2) 2]; ring
        _ ≤ (N : ℝ) ^ (-D₁) := hsmall
    calc (Pg d) Ev ≤ (Pg d) Sbad := measure_mono hsubset
      _ = ENNReal.ofReal ((Pg d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := ENNReal.ofReal_le_ofReal (hU.trans hsum_le)
end Main

end RBM.Gauss.Grid

end
