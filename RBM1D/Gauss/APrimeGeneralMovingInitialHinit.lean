/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeAssembly
import RBM1D.Gauss.APrimeGeneralMovingDetFields

/-!
# T488: initial A-prime moment on a general moving window

The fixed-terminal-time hypothesis in `APrimeAssembly.eventually_initial_hinit_gauss'`
is replaced by the polynomial endpoint floor furnished by `Cond272Reg`.  The result is
uniform in the moving endpoint and in every two-loop coordinate.
-/

namespace RBM.APrimeGeneralMovingInitialHinit

open Filter MeasureTheory Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The moving endpoint floor gives a uniform polynomial lower bound on the spectral scale. -/
theorem eventually_eta_window {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N),
      (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT E u := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  filter_upwards [
    APrimeGeneralMovingWindowFloor.eventually_endpoint_floor hE hs0 hst ht1 hc hreg,
    eventually_le_rpow ((mE E).im)⁻¹ (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with N hfloor hmN hN u hu
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hNinv_m : (N : ℝ)⁻¹ ≤ (mE E).im := by
    exact (inv_le_comm₀ hm hNr).mp (by simpa only [Real.rpow_one] using hmN)
  have hNinv_t : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloor.1
  have hNinv_u : (N : ℝ)⁻¹ ≤ 1 - u := by linarith [hu.2]
  have hmul : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ (1 - u) * (mE E).im := by
    nlinarith [mul_le_mul hNinv_u hNinv_m hNinv (by linarith [ht1 N, hu.2])]
  rw [etaT]
  calc
    (N : ℝ) ^ (-(2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      rw [Real.rpow_neg hNr.le, Real.rpow_two]
      simpa only [pow_two] using (inv_pow (N : ℝ) 2).symm
    _ ≤ (1 - u) * (mE E).im := hmul

/-- The residual endpoint scale `R_v⁻²` has the same uniform polynomial floor. -/
theorem eventually_initial_phi_lower {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      (N : ℝ) ^ (-(2 : ℝ)) ≤
        (etaT E (s N) / etaT E v) ^ (-(2 : ℝ)) := by
  filter_upwards [
    APrimeGeneralMovingWindowFloor.eventually_endpoint_floor hE hs0 hst ht1 hc hreg,
    eventually_ge_atTop 1] with N hfloor hN v
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hnum : 0 < 1 - s N := by linarith [v.2.1]
  have hratio : (N : ℝ)⁻¹ ≤ (1 - (v : ℝ)) / (1 - s N) := by
    apply (le_div_iff₀ hnum).2
    have hNinv_t : (N : ℝ)⁻¹ ≤ 1 - t N := by
      simpa only [Real.rpow_neg_one] using hfloor.1
    have hNinv_v : (N : ℝ)⁻¹ ≤ 1 - (v : ℝ) := by linarith [v.2.2]
    have hsle : 1 - s N ≤ 1 := by linarith [hs0 N]
    nlinarith [mul_le_mul_of_nonneg_left hsle hNinv]
  have hident : (etaT E (s N) / etaT E v) ^ (-(2 : ℝ)) =
      ((1 - (v : ℝ)) / (1 - s N)) ^ 2 := by
    rw [Step2.etaT_ratio hE, Real.rpow_neg (by positivity), Real.rpow_ofNat]
    rw [div_pow, inv_div, div_pow]
  rw [hident]
  have hpow : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ)⁻¹) ^ 2 := by
    rw [Real.rpow_neg hNr.le, Real.rpow_two]
    exact (inv_pow (N : ℝ) 2).symm
  rw [hpow]
  exact pow_le_pow_left₀ hNinv hratio 2

/-- A deterministic all-sample polynomial envelope, uniform over every moving endpoint. -/
theorem eventually_initialEvolvedNormAt_le_rpow {E D c : ℝ}
    (hE : |E| < 2) (hD : 0 ≤ D) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      ∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
        APrimeAssembly.initialEvolvedNormAt (sample d) E D s N v a ω ≤
          (N : ℝ) ^ (D + 6) := by
  let κ : ℝ := min 1 (2 - |E|)
  have hκ0 : 0 < κ := lt_min (by norm_num) (by linarith)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hEκ : |E| ≤ 2 - κ := by
    have := min_le_right (1 : ℝ) (2 - |E|)
    dsimp [κ]
    linarith
  obtain ⟨C, _hC0, hJ⟩ := Step2Bootstrap.exists_jS_envelope
    (sample d) hκ0 hκ1 hEκ hD (cη := 2) (by norm_num)
    hs0 ht1 (eventually_eta_window hE hs0 hst ht1 hc hreg)
  have hXi := Step2FarInputs.eventually_xiK_le B
    (mE E).im (τ := 1) (by norm_num)
  filter_upwards [hJ, hXi, (Step2.tendsto_W B).eventually_ge_atTop (Real.exp 1),
    SumZeroDyn.eventually_const_mul_rpow_le C (show D + 5 < D + 6 by linarith),
    eventually_ge_atTop 1] with N hJN hXiN hWN hAbs hN1 v a ω
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hXi0 := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
  have hY := APrimeAssembly.initial_evolved_normalized_le_at
    (sample d) hE (hs0 N) (ht1 N) hWN D ω v a
  have hJb : Step2.jS (sample d) E D N (s N) ω ≤
      C * (N : ℝ) ^ (D + 4) := by
    convert hJN (s N) ⟨le_rfl, hst N⟩ ω using 1 <;> ring
  calc
    APrimeAssembly.initialEvolvedNormAt (sample d) E D s N v a ω
        ≤ Step2.jS (sample d) E D N (s N) ω *
          Step2.xiK (d.L N) (d.W N) (mE E).im := hY
    _ ≤ (C * (N : ℝ) ^ (D + 4)) * (N : ℝ) ^ (1 : ℝ) := by
      exact mul_le_mul hJb hXiN hXi0 (by positivity)
    _ = C * (N : ℝ) ^ (D + 5) := by
      calc
        (C * (N : ℝ) ^ (D + 4)) * (N : ℝ) ^ (1 : ℝ) =
            C * ((N : ℝ) ^ (D + 4) * (N : ℝ) ^ (1 : ℝ)) := by ring
        _ = C * (N : ℝ) ^ ((D + 4) + 1) := by
          conv_rhs => rw [Real.rpow_add hN0]
        _ = C * (N : ℝ) ^ (D + 5) := by ring
    _ ≤ (N : ℝ) ^ (D + 6) := hAbs

/-- The moving initial coordinate has uniform polynomial moments with residual scale `R_v⁻²`. -/
theorem initialEvolvedNormAt_momentDom {E D c : ℝ}
    (hE : |E| < 2) (hD : 0 < D) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) :
    Gauss.MomentDom B.P
      (fun N (va : TimeIcc s t N × LoopArg (d.L N) 2) ω =>
        APrimeAssembly.initialEvolvedNormAt (sample d) E D s N va.1 va.2 ω)
      (fun N va => (etaT E (s N) / etaT E va.1) ^ (-(2 : ℝ))) := by
  letI := B.isProbabilityMeasure
  have hY0 : ∀ N (va : TimeIcc s t N × LoopArg (d.L N) 2) ω,
      0 ≤ APrimeAssembly.initialEvolvedNormAt (sample d) E D s N va.1 va.2 ω := by
    intro N ⟨v, a⟩ ω
    have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
    have hR := Step2Moment.ratR_pos hE (v.2.1.trans_lt hv1) hv1
    have hT : 0 < Step2.tT B E N D v (zdist (d.L N) (a 0 - a 1)) :=
      tailT_pos (by exact_mod_cast B.W_pos N) _
    unfold APrimeAssembly.initialEvolvedNormAt
    exact div_nonneg (norm_nonneg _) (mul_pos hT (by positivity)).le
  exact APrimeAssembly.momentDom_of_stochDom_of_eventual_envelope hY0
    (fun N va => APrimeAssembly.measurable_initialEvolvedNormAt_gauss
      d hE hs0 hst ht1 N va.1 D va.2)
    (fun p N va => APrimeAssembly.integrable_initialEvolvedNormAt_pow_gauss
      d hE hs0 hst ht1 p N va.1 D va.2)
    (fun N va => Real.rpow_pos_of_pos
      (Step2Moment.ratR_pos hE
        (va.1.2.1.trans_lt (va.1.2.2.trans_lt (ht1 N)))
        (va.1.2.2.trans_lt (ht1 N))) _)
    (Bexp := 2) (by norm_num)
    (by
      filter_upwards [eventually_initial_phi_lower hE hs0 hst ht1 hc hreg]
        with N hN va
      exact hN va.1)
    (K := D + 6) (by linarith)
    (by
      filter_upwards [eventually_initialEvolvedNormAt_le_rpow
        hE hD.le hs0 hst ht1 hc hreg] with N hN va ω
      exact hN va.1 va.2 ω)
    (APrimeAssembly.initialEvolvedNorm_stochDom_sharp'
      (sample d) hE hs0 hst ht1 hreg.toCond272 hB D hD)

/-- The exact numerical initial slot, uniformly over moving endpoints and coordinates,
without a fixed terminal time. -/
theorem eventually_initial_hinit {E D c δ : ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p)
    (W : ∀ N, (TimeIcc s t N × LoopArg (d.L N) 2) → Ω d → ℝ)
    (hWm : ∀ N va, AEStronglyMeasurable (W N va) B.P)
    (hW0 : ∀ N va ω, 0 ≤ W N va ω)
    (hW1 : ∀ N va ω, W N va ω ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ va : TimeIcc s t N × LoopArg (d.L N) 2,
      MomentDuhamel.momNormW B.P (W N va) p
        (APrimeAssembly.initialEvolvedNormAt (sample d) E D s N va.1 va.2) ≤
        APrimeOneStep.initTerm ((N : ℝ) ^ (δ / 8))
          (etaT E (s N) / etaT E va.1)
          (APrimeInit.slotXi' ((N : ℝ) ^ (δ / 8))) /
          (etaT E (s N) / etaT E va.1) ^ 4 := by
  letI := B.isProbabilityMeasure
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hint : ∀ q N (va : TimeIcc s t N × LoopArg (d.L N) 2), Integrable
      (fun ω => |APrimeAssembly.initialEvolvedNormAt
        (sample d) E D s N va.1 va.2 ω| ^ (2 * q)) B.P :=
    fun q N va => APrimeAssembly.integrable_initialEvolvedNormAt_pow_gauss
      d hE hs0 hst ht1 q N va.1 D va.2
  have hmom := APrimeAssembly.weighted_moments_of_momentDom hint W hWm hW0 hW1
    (initialEvolvedNormAt_momentDom hE hDpos hs0 hst ht1 hc hreg hB)
  have hΦ0 : ∀ N (va : TimeIcc s t N × LoopArg (d.L N) 2),
      0 ≤ (etaT E (s N) / etaT E va.1) ^ (-(2 : ℝ)) := by
    intro N va
    exact (Real.rpow_pos_of_pos
      (Step2Moment.ratR_pos hE
        (va.1.2.1.trans_lt (va.1.2.2.trans_lt (ht1 N)))
        (va.1.2.2.trans_lt (ht1 N))) _).le
  have hsmall := APrimeAssembly.eventually_momNormW_le_small_initial_scale
    hδ p hp hW0 hΦ0 hmom
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN hN1 va
  have hv1 : (va.1 : ℝ) < 1 := va.1.2.2.trans_lt (ht1 N)
  have hR : 0 < etaT E (s N) / etaT E va.1 :=
    Step2Moment.ratR_pos hE (va.1.2.1.trans_lt hv1) hv1
  have hscale := APrimeAssembly.initial_slot_scale_eq (δ := δ)
    (R := etaT E (s N) / etaT E va.1) hN1 hR
  rw [hscale]
  exact hN va

/-! A positive-length first cell supplies a simultaneous nondegenerate witness. -/

private theorem eventual_cap :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
  filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with N hNpow hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
      ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hN0]
  rw [hEq]
  have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
  norm_num at hInv ⊢
  exact hInv

/-- A genuine positive-length window with `s=0`, `BoundsCore_zero`, and the
moving initial estimate for the constant weight. -/
theorem positive_length_hinit_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      let s := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
      let t := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ (∀ᶠ N : ℕ in atTop, s N < t N) := by
  obtain ⟨τ', hτ', c, hc, _n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain B (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  obtain ⟨_, hsteps⟩ := hgrid 0 (by norm_num)
    (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) eventual_cap
  obtain ⟨hs0, hst, ht1, hreg⟩ := hsteps 0
  let s : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
  let t : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  have hsEq : ∀ N, s N = 0 := by
    intro N
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hB : BoundsCore (sample d) 0 s :=
    (BoundsCore_zero (sample d) (by norm_num : |(0 : ℝ)| ≤ 2)).congr
      (sample d) (Eventually.of_forall fun N => (hsEq N).symm)
  have hpos := eventually_gridT_zero_lt_gridT_one B hτ'
    (Eventually.of_forall fun _ => by norm_num : ∀ᶠ N : ℕ in atTop, 0 < (1 / 2 : ℝ))
  change ∀ᶠ N : ℕ in atTop, s N < t N at hpos
  exact ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1, hreg, hB, hpos⟩

#print axioms eventually_eta_window
#print axioms eventually_initial_phi_lower
#print axioms eventually_initialEvolvedNormAt_le_rpow
#print axioms initialEvolvedNormAt_momentDom
#print axioms eventually_initial_hinit
#print axioms positive_length_hinit_witness

end
end RBM.APrimeGeneralMovingInitialHinit
