/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeExponents
import RBM1D.Gauss.APrimeSlotFields
import RBM1D.Gauss.APrimeWeight
import RBM1D.Gauss.APrimeBadSplit
import RBM1D.Gauss.APrimeQVEndpoint
import RBM1D.Hierarchy.Step2FarInputs

/-!
# T280e: initial propagation and conditional first assembly

The original D20 arithmetic obstructions remain recorded below.  The corrected
small-slot and margin routes avoid them.  The positive constructor here is conditional
on a widened-weight family moment estimate; no existing model theorem supplies it.
-/

-- Check the target, its constructor, the one-step producer, the slot arithmetic,
-- and the two negative certificates before making any assembly claim.
#check @RBM.APrimeSlotFields.APrimeSlot'
#check @RBM.APrimeSlotFields.jsNormDom_of_aprimeSlot'
#check @RBM.APrimeSlotFields.aprimeHypOn_jSnorm_event
#check @RBM.APrimeModel.aprimeHypOn_of_stepBound''
#check @RBM.APrimeModel.oneStep_of_slots
#check @RBM.APrimeSlotArith.eventually_slot_arith_of_detDom
#check @RBM.APrimeInit.no_family_absorption_slot
#check @RBM.APrimeExponents.not_eventually_product_scale_of_separate
#check @RBM.Step2.le_jStar_mul
#check @RBM.Step2.norm_lk_eq
#check @RBM.APrimeQVEndpoint.weightedKernel_tail_le
#check @RBM.Step2FarInputs.eventually_xiK_le
#check @RBM.APrimeSlotFields.stochDom_jS_init_of_boundsCore
#check @RBM.APrimeInit.weightedMomentDom_of_stochDom_of_nonneg
#check @RBM.APrimeInit.numerical_hinit_of_weighted_integral
#check @RBM.APrimeWeight.jSnorm_piecewiseW_fields
#check @RBM.APrimeWeight.weightedMoment_of_stepBound_mono
#check @RBM.APrimeBadSplit.drift_norm_le_of_event
#check @RBM.APrimeBadSplit.evolved_qv_norm_le_of_event
#check @RBM.APrimeBadSplit.crossPart_le_of_S5_event
#check @RBM.APrimeQVEndpoint.sqrt_evolvedQV_le_endpoint
#check @RBM.Gauss.highProb_normX_le
#check @RBM.Gauss.measurableSet_normX_le
#check @RBM.Gauss.TraceMomentBound
#check @RBM.Gauss.traceMomentBound_gauss
#check @RBM.APrimeInit.integral_cutTrunc_le_family_high
#check @RBM.APrimeInit.momNormW_le_momNormW_of_exponent_le
#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.MomentDuhamel.weightedMinkowski_of_deriv_le
#check @RBM.APrimeInit.coordinate_integral_of_small_slots
#check @RBM.APrimeDuhamelModel.hasDerivAt_momFlow
#check @RBM.APrimeDuhamelModel.continuousOn_momFlow
#check @RBM.APrimeDuhamelModel.intervalIntegrable_momFlowDeriv
#check @intervalIntegrable_inv_iff
#check @intervalIntegral.integral_undef
#check @RBM.Gauss.etaT_le_of_le
#check @RBM.Step2Bootstrap.exists_jS_envelope
#check @RBM.Gauss.integrable_lkT_pow
#check @RBM.Gauss.continuous_uker_lkT_omega
#check @RBM.Gauss.rpow_neg_one_le_etaT_of_scale_ge
#check @RBM.Gauss.window_norm_mul_lt
#check @RBM.Gauss.zt_im_ne_zero_of_lt_one
#check @RBM.Gauss.integrable_of_continuous_of_bound
#check @div_pow
#check @inv_pow
#check @Real.rpow_natCast
#check @Real.rpow_ofNat

namespace RBM.APrimeAssembly

open Real Filter MeasureTheory Step2Bootstrap CutHypTheta MomentDuhamelCut
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The left-endpoint observable propagated to the right endpoint.  The absolute
kernel estimate gives precisely `R² * xiK`; no larger power of `R` enters. -/
theorem norm_initial_Uker_le (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} {N : ℕ} (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (D : ℝ) (ω : Ω)
    (a : LoopArg (B.L N) 2) :
    ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
        (s N : ℂ) (t N : ℂ) (Step2.lk X E N (s N) ω) a‖ ≤
      Step2.jS X E D N (s N) ω *
        (etaT E (s N) / etaT E (t N)) ^ 2 *
        Step2.xiK (B.L N) (B.W N) (mE E).im *
        Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1)) := by
  classical
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hAuv := flowScale_antitoneOn hW0 (B.L N) E
    (Set.mem_Iic.2 (hst.trans ht1.le)) (Set.mem_Iic.2 ht1.le) hst
  have hk := APrimeQVEndpoint.weightedKernel_tail_le (D := D) (B.L N) (B.three_le_L N)
    (mE_im_pos hE) (mE_im_le_one hE) hs0 hst ht1 hW hAuv a
  rw [← Step2.etaT_ratio hE] at hk
  have hWpos : (0 : ℝ) < B.W N := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hJ0 : 0 ≤ Step2.jS X E D N (s N) ω :=
    (Step2Moment.one_le_jS X N (s N) ω).trans' zero_le_one
  have hA : ∀ b : LoopArg (B.L N) 2,
      ‖Step2.lk X E N (s N) ω b‖ ≤ Step2.jS X E D N (s N) ω *
        Step2.tT B E N D (s N) (zdist (B.L N) (b 0 - b 1)) := by
    intro b
    exact Step2.le_jStar_mul (f := fun b => ‖Step2.lk X E N (s N) ω b‖)
      (ℓu := B.ell N (s N)) (ηu := etaT E (s N)) (D := D) hWpos b
  rw [Uker_apply]
  calc
    ‖∑ b : LoopArg (B.L N) 2,
        (∏ i : Fin 2, edgeKer (B.L N) (xiOf (mSigma E) Step2.sigPM i)
          (s N : ℂ) (t N : ℂ) (a i) (b i)) * Step2.lk X E N (s N) ω b‖
        ≤ ∑ b : LoopArg (B.L N) 2,
          ‖(∏ i : Fin 2, edgeKer (B.L N) (xiOf (mSigma E) Step2.sigPM i)
            (s N : ℂ) (t N : ℂ) (a i) (b i)) * Step2.lk X E N (s N) ω b‖ :=
          norm_sum_le _ _
    _ = ∑ b : LoopArg (B.L N) 2,
          ‖∏ i : Fin 2, edgeKer (B.L N) (xiOf (mSigma E) Step2.sigPM i)
            (s N : ℂ) (t N : ℂ) (a i) (b i)‖ * ‖Step2.lk X E N (s N) ω b‖ := by
          simp only [norm_mul]
    _ ≤ Step2.jS X E D N (s N) ω *
          (∑ b : LoopArg (B.L N) 2,
            ‖∏ i : Fin 2, edgeKer (B.L N) (xiOf (mSigma E) Step2.sigPM i)
              (s N : ℂ) (t N : ℂ) (a i) (b i)‖ *
              Step2.tT B E N D (s N) (zdist (B.L N) (b 0 - b 1))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro b _
          nlinarith [hA b, norm_nonneg (∏ i : Fin 2,
            edgeKer (B.L N) (xiOf (mSigma E) Step2.sigPM i)
              (s N : ℂ) (t N : ℂ) (a i) (b i))]
    _ ≤ Step2.jS X E D N (s N) ω *
          ((etaT E (s N) / etaT E (t N)) ^ 2 *
            Step2.xiK (B.L N) (B.W N) (mE E).im *
            Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1))) := by
          apply mul_le_mul_of_nonneg_left _ hJ0
          simpa [Step2.sigPM_xi hE.le, Step2.tT, Band.ell,
            Step2.etaT_eq, Fin.prod_univ_two] using hk
    _ = _ := by ring

/-- The `R²` kernel loss is absorbed by the `R⁴` normalization.  The remaining
factor is the deterministic `xiK`, which is `N^{o(1)}`. -/
theorem initial_evolved_normalized_le (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} {N : ℕ} (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (D : ℝ) (ω : Ω)
    (a : LoopArg (B.L N) 2) :
    ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
        (s N : ℂ) (t N : ℂ) (Step2.lk X E N (s N) ω) a‖ /
      (Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1)) *
        (etaT E (s N) / etaT E (t N)) ^ 4) ≤
      Step2.jS X E D N (s N) ω * Step2.xiK (B.L N) (B.W N) (mE E).im := by
  let R : ℝ := etaT E (s N) / etaT E (t N)
  let T : ℝ := Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1))
  let J : ℝ := Step2.jS X E D N (s N) ω
  let Ξ : ℝ := Step2.xiK (B.L N) (B.W N) (mE E).im
  have hR1 : 1 ≤ R := Step2Moment.one_le_ratR (s := s) hE hst ht1
  have hT0 : 0 < T := tailT_pos
    (lt_of_lt_of_le (Real.exp_pos 1) hW) _
  have hJ0 : 0 ≤ J := zero_le_one.trans (Step2Moment.one_le_jS X N (s N) ω)
  have hΞ0 : 0 ≤ Ξ := Step2.xiK_nonneg _ _ _
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hR24 : R ^ 2 ≤ R ^ 4 := by
    calc R ^ 2 = R ^ 2 * 1 := by ring
      _ ≤ R ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hR2 (sq_nonneg R)
      _ = R ^ 4 := by ring
  have hnum := norm_initial_Uker_le X hE hs0 hst ht1 hW D ω a
  apply (div_le_iff₀ (mul_pos hT0 (by positivity : 0 < R ^ 4))).2
  calc
    ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
        (s N : ℂ) (t N : ℂ) (Step2.lk X E N (s N) ω) a‖
        ≤ J * R ^ 2 * Ξ * T := hnum
    _ ≤ J * Ξ * (T * R ^ 4) := by
      calc J * R ^ 2 * Ξ * T ≤ J * R ^ 4 * Ξ * T := by
              gcongr
        _ = J * Ξ * (T * R ^ 4) := by ring

/-- The sharper initial estimate keeps the useful `R⁻²` after normalization. -/
theorem initial_evolved_normalized_le_sharp (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} {N : ℕ} (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (D : ℝ) (ω : Ω)
    (a : LoopArg (B.L N) 2) :
    ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
        (s N : ℂ) (t N : ℂ) (Step2.lk X E N (s N) ω) a‖ /
      (Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1)) *
        (etaT E (s N) / etaT E (t N)) ^ 4) ≤
      Step2.jS X E D N (s N) ω * Step2.xiK (B.L N) (B.W N) (mE E).im /
        (etaT E (s N) / etaT E (t N)) ^ 2 := by
  let R : ℝ := etaT E (s N) / etaT E (t N)
  let T : ℝ := Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1))
  let J : ℝ := Step2.jS X E D N (s N) ω
  let Ξ : ℝ := Step2.xiK (B.L N) (B.W N) (mE E).im
  have hR : 0 < R := Step2Moment.ratR_pos hE (hst.trans_lt ht1) ht1
  have hT : 0 < T := tailT_pos (lt_of_lt_of_le (Real.exp_pos 1) hW) _
  have hnum := norm_initial_Uker_le X hE hs0 hst ht1 hW D ω a
  apply (div_le_iff₀ (mul_pos hT (by positivity : 0 < R ^ 4))).2
  calc
    ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
        (s N : ℂ) (t N : ℂ) (Step2.lk X E N (s N) ω) a‖
        ≤ J * R ^ 2 * Ξ * T := hnum
    _ = J * Ξ / R ^ 2 * (T * R ^ 4) := by field_simp

/-- The absolute value of the evolved left-endpoint coordinate, divided by the
right-endpoint spatial tail and the fourth power of the time ratio. -/
noncomputable def initialEvolvedNorm (X : Sample B) (E D : ℝ)
    (s t : ℕ → ℝ) (N : ℕ) (a : LoopArg (B.L N) 2) (ω : Ω) : ℝ :=
  ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
      (s N : ℂ) (t N : ℂ) (Step2.lk X E N (s N) ω) a‖ /
    (Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1)) *
      (etaT E (s N) / etaT E (t N)) ^ 4)

/-- The evolved initial coordinate with its right endpoint explicit. -/
noncomputable def initialEvolvedNormAt (X : Sample B) (E D : ℝ)
    (s : ℕ → ℝ) (N : ℕ) (v : ℝ) (a : LoopArg (B.L N) 2) (ω : Ω) : ℝ :=
  ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
      (s N : ℂ) (v : ℂ) (Step2.lk X E N (s N) ω) a‖ /
    (Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) *
      (etaT E (s N) / etaT E v) ^ 4)

theorem initial_evolved_normalized_le_sharp_at (X : Sample B)
    {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {N : ℕ}
    (hs0 : 0 ≤ s N) (ht1 : t N < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (D : ℝ) (ω : Ω)
    (v : TimeIcc s t N) (a : LoopArg (B.L N) 2) :
    initialEvolvedNormAt X E D s N v a ω ≤
      Step2.jS X E D N (s N) ω *
        Step2.xiK (B.L N) (B.W N) (mE E).im /
          (etaT E (s N) / etaT E v) ^ 2 := by
  let t' : ℕ → ℝ := fun M => if M = N then v else t M
  have ht'N : t' N = v := by simp [t']
  have h := initial_evolved_normalized_le_sharp (t := t') X hE hs0
    (by simpa [ht'N] using v.2.1)
    (by simpa [ht'N] using (v.2.2.trans_lt ht1)) hW D ω a
  simpa [initialEvolvedNormAt, ht'N] using h

theorem initial_evolved_normalized_le_at (X : Sample B)
    {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {N : ℕ}
    (hs0 : 0 ≤ s N) (ht1 : t N < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (D : ℝ) (ω : Ω)
    (v : TimeIcc s t N) (a : LoopArg (B.L N) 2) :
    initialEvolvedNormAt X E D s N v a ω ≤
      Step2.jS X E D N (s N) ω *
        Step2.xiK (B.L N) (B.W N) (mE E).im := by
  let t' : ℕ → ℝ := fun M => if M = N then v else t M
  have ht'N : t' N = v := by simp [t']
  have h := initial_evolved_normalized_le (t := t') X hE hs0
    (by simpa [ht'N] using v.2.1)
    (by simpa [ht'N] using (v.2.2.trans_lt ht1)) hW D ω a
  simpa [initialEvolvedNormAt, ht'N] using h

/-- The actual Gaussian evolved initial coordinate is measurable at every N. -/
theorem measurable_initialEvolvedNorm_gauss (d : Gauss.Dims) {E : ℝ}
    (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (D : ℝ) (N : ℕ) (a : LoopArg (d.L N) 2) :
    Measurable (initialEvolvedNorm (Gauss.sample d) E D s t N a) := by
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hz : (zt E (s N)).im ≠ 0 :=
    Gauss.zt_im_ne_zero_of_lt_one hE hs1
  have hm : ∀ x y : Bool, ‖((s N : ℝ) : ℂ) *
      (mSigma E x * mSigma E y)‖ < 1 := by
    intro x y
    exact Gauss.window_norm_mul_lt hE.le (hs0 N) (ht1 N) (s N)
      ⟨le_rfl, hst N⟩ x y
  have hcont := Gauss.continuous_uker_lkT_omega d E N hz hm
    Step2.sigPM (xiOf (mSigma E) Step2.sigPM) a (t N : ℂ)
  unfold initialEvolvedNorm
  exact hcont.measurable.norm.div_const _

/-- Every even power of the Gaussian initial observable is integrable.  At each
fixed size the two-loop index is finite, so the deterministic kernel is bounded
at the single initial time. -/
theorem integrable_initialEvolvedNorm_pow_gauss (d : Gauss.Dims) {E : ℝ}
    (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (D : ℝ) (p N : ℕ) (a : LoopArg (d.L N) 2) :
    Integrable (fun ω =>
      |initialEvolvedNorm (Gauss.sample d) E D s t N a ω| ^ (2 * p))
      (Gauss.band d).P := by
  classical
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hz : (zt E (s N)).im ≠ 0 :=
    Gauss.zt_im_ne_zero_of_lt_one hE hs1
  have hm : ∀ x y : Bool, ‖((s N : ℝ) : ℂ) *
      (mSigma E x * mSigma E y)‖ < 1 := by
    intro x y
    exact Gauss.window_norm_mul_lt hE.le (hs0 N) (ht1 N) (s N)
      ⟨le_rfl, hst N⟩ x y
  have hcont := Gauss.continuous_uker_lkT_omega d E N hz hm
    Step2.sigPM (xiOf (mSigma E) Step2.sigPM) a (t N : ℂ)
  let cK : ℝ := ∑ b : LoopArg (d.L N) 2,
    ‖(Gauss.band d).Kval E N (s N) (LoopData.idx (Step2.sigPM, b))‖
  have hcK : 0 ≤ cK := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKb : ∀ u ∈ Set.Icc (s N) (s N),
      ∀ b : LoopArg (d.L N) 2,
      ‖(Gauss.band d).Kval E N u (LoopData.idx (Step2.sigPM, b))‖ ≤ cK := by
    intro u hu b
    have hueq : u = s N := le_antisymm hu.2 hu.1
    subst u
    exact Finset.single_le_sum (f := fun b' : LoopArg (d.L N) 2 =>
      ‖(Gauss.band d).Kval E N (s N) (LoopData.idx (Step2.sigPM, b'))‖)
      (fun b' _ => norm_nonneg _) (Finset.mem_univ b)
  obtain ⟨C, hC0, hC⟩ := Gauss.exists_bdd_uker_lkT
    (d := d) E N hE hs1 Step2.sigPM a (t N : ℂ) hcK hKb
  have hT : 0 < Step2.tT (Gauss.band d) E N D (t N)
      (zdist (d.L N) (a 0 - a 1)) :=
    tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
  have hR : 0 < etaT E (s N) / etaT E (t N) :=
    Step2Moment.ratR_pos hE hs1 (ht1 N)
  let den : ℝ := Step2.tT (Gauss.band d) E N D (t N)
      (zdist (d.L N) (a 0 - a 1)) *
      (etaT E (s N) / etaT E (t N)) ^ 4
  have hden : 0 < den := mul_pos hT (by positivity)
  have hYcont : Continuous
      (initialEvolvedNorm (Gauss.sample d) E D s t N a) := by
    unfold initialEvolvedNorm
    exact hcont.norm.div_const _
  refine Gauss.integrable_of_continuous_of_bound (hYcont.abs.pow (2 * p))
    (C := (C / den) ^ (2 * p)) fun ω => ?_
  have hb : initialEvolvedNorm (Gauss.sample d) E D s t N a ω ≤ C / den := by
    unfold initialEvolvedNorm
    exact div_le_div_of_nonneg_right (hC (s N) ⟨le_rfl, le_rfl⟩ ω) hden.le
  have hY0 : 0 ≤ initialEvolvedNorm (Gauss.sample d) E D s t N a ω := by
    unfold initialEvolvedNorm
    exact div_nonneg (norm_nonneg _) hden.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg hY0]; exact hb) _

private theorem patched_endpoint_order {s t : ℕ → ℝ}
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {N : ℕ} (v : TimeIcc s t N) :
    (∀ M, s M ≤ (if M = N then (v : ℝ) else t M)) ∧
    (∀ M, (if M = N then (v : ℝ) else t M) < 1) := by
  constructor
  · intro M; by_cases h : M = N
    · subst M; simpa using v.2.1
    · simpa [h] using hst M
  · intro M; by_cases h : M = N
    · subst M; simpa using v.2.2.trans_lt (ht1 N)
    · simpa [h] using ht1 M

theorem measurable_initialEvolvedNormAt_gauss (d : Gauss.Dims)
    {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (v : TimeIcc s t N)
    (D : ℝ) (a : LoopArg (d.L N) 2) :
    Measurable (initialEvolvedNormAt (Gauss.sample d) E D s N v a) := by
  let t' : ℕ → ℝ := fun M => if M = N then v else t M
  obtain ⟨hst', ht1'⟩ := patched_endpoint_order hst ht1 v
  have h := measurable_initialEvolvedNorm_gauss d hE hs0 hst' ht1' D N a
  have heq : initialEvolvedNorm (Gauss.sample d) E D s t' N a =
      initialEvolvedNormAt (Gauss.sample d) E D s N v a := by
    funext ω
    simp [initialEvolvedNormAt, initialEvolvedNorm, t']
  rwa [heq] at h

theorem integrable_initialEvolvedNormAt_pow_gauss (d : Gauss.Dims)
    {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (p N : ℕ) (v : TimeIcc s t N)
    (D : ℝ) (a : LoopArg (d.L N) 2) :
    Integrable (fun ω =>
      |initialEvolvedNormAt (Gauss.sample d) E D s N v a ω| ^ (2 * p))
      (Gauss.band d).P := by
  let t' : ℕ → ℝ := fun M => if M = N then v else t M
  obtain ⟨hst', ht1'⟩ := patched_endpoint_order hst ht1 v
  have h := integrable_initialEvolvedNorm_pow_gauss d hE hs0 hst' ht1' D p N a
  have heq : initialEvolvedNorm (Gauss.sample d) E D s t' N a =
      initialEvolvedNormAt (Gauss.sample d) E D s N v a := by
    funext ω
    simp [initialEvolvedNormAt, initialEvolvedNorm, t']
  convert h using 1
  funext ω
  exact congrArg (fun y : ℝ => |y| ^ (2 * p)) (congrFun heq ω).symm

private theorem eventually_rpow_neg_one_le_fixed {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ η := by
  obtain ⟨k, hk⟩ := exists_nat_gt η⁻¹
  filter_upwards [eventually_ge_atTop (max k 1)] with N hN
  have hNk : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left k 1) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right k 1) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Real.rpow_neg hN0.le, Real.rpow_one]
  have h1 : η⁻¹ ≤ (N : ℝ) := le_trans hk.le hNk
  have := inv_anti₀ (inv_pos.2 hη) h1
  rwa [inv_inv] at this

/-- The fixed upper time supplies the lower spectral scale needed by the
existing deterministic `J*` envelope, at the same `(s,t)` window. -/
theorem eventually_eta_window_of_fixed_t0 {E t₀ : ℝ} (hE : |E| < 2)
    (ht₀ : t₀ < 1) {s t : ℕ → ℝ} (htt : ∀ N, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E u := by
  filter_upwards [eventually_rpow_neg_one_le_fixed (etaT_pos hE ht₀)] with N hN u hu
  exact hN.trans (Gauss.etaT_le_of_le hE (hu.2.trans (htt N)))

/-- On a fixed upper time window, the residual `R⁻²` is bounded below by a
positive constant. -/
theorem eventually_initial_phi_lower_of_fixed_t0 {E t₀ : ℝ} (hE : |E| < 2)
    (ht₀ : t₀ < 1) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (htt : ∀ N, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 : ℝ)) ≤
        (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ)) := by
  have hρ : 0 < 1 - t₀ := by linarith
  filter_upwards [eventually_rpow_neg_one_le_fixed (sq_pos_of_pos hρ)] with N hN
  have hs1 : s N < 1 := (hst N).trans_lt ((htt N).trans_lt ht₀)
  have ht1 : t N < 1 := (htt N).trans_lt ht₀
  have hnum : 0 < 1 - s N := by linarith
  have hden : 0 < 1 - t N := by linarith
  have hratio : 1 - t₀ ≤ (1 - t N) / (1 - s N) := by
    apply (le_div_iff₀ hnum).2
    have hρden : 1 - t₀ ≤ 1 - t N := by linarith [htt N]
    have hnumle : 1 - s N ≤ 1 := by linarith [hs0 N]
    nlinarith
  have hident : (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ)) =
      ((1 - t N) / (1 - s N)) ^ 2 := by
    rw [Step2.etaT_ratio hE, Real.rpow_neg (by positivity)]
    rw [Real.rpow_ofNat]
    rw [div_pow, inv_div, div_pow]
  rw [hident]
  exact hN.trans (pow_le_pow_left₀ hρ.le hratio 2)

theorem eventually_initial_phi_lower_of_fixed_t0' {E t₀ : ℝ} (hE : |E| < 2)
    (ht₀ : t₀ < 1) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (htt : ∀ N, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      (N : ℝ) ^ (-(1 : ℝ)) ≤
        (etaT E (s N) / etaT E v) ^ (-(2 : ℝ)) := by
  have hρ : 0 < 1 - t₀ := by linarith
  filter_upwards [eventually_rpow_neg_one_le_fixed (sq_pos_of_pos hρ)] with N hN v
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt ((htt N).trans_lt ht₀)
  have hnum : 0 < 1 - s N := by linarith [v.2.1, hv1]
  have hden : 0 < 1 - (v : ℝ) := by linarith
  have hratio : 1 - t₀ ≤ (1 - (v : ℝ)) / (1 - s N) := by
    apply (le_div_iff₀ hnum).2
    have hρden : 1 - t₀ ≤ 1 - (v : ℝ) := by linarith [v.2.2, htt N]
    have hnumle : 1 - s N ≤ 1 := by linarith [hs0 N]
    nlinarith
  have hident : (etaT E (s N) / etaT E v) ^ (-(2 : ℝ)) =
      ((1 - (v : ℝ)) / (1 - s N)) ^ 2 := by
    rw [Step2.etaT_ratio hE, Real.rpow_neg (by positivity), Real.rpow_ofNat]
    rw [div_pow, inv_div, div_pow]
  rw [hident]
  exact hN.trans (pow_le_pow_left₀ hρ.le hratio 2)

/-- The normalized initial Gaussian coordinate has a deterministic polynomial
envelope for all sufficiently large sizes, uniformly in the loop coordinate. -/
theorem eventually_initialEvolvedNorm_le_rpow (d : Gauss.Dims)
    {E D t₀ : ℝ} (hE : |E| < 2) (hD : 0 ≤ D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2, ∀ ω : Gauss.Ω d,
      initialEvolvedNorm (Gauss.sample d) E D s t N a ω ≤
        (N : ℝ) ^ (D + 4) := by
  let κ : ℝ := min 1 (2 - |E|)
  have hκ0 : 0 < κ := lt_min (by norm_num) (by linarith)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hEκ : |E| ≤ 2 - κ := by have := min_le_right (1 : ℝ) (2 - |E|); dsimp [κ]; linarith
  have ht1 : ∀ N, t N < 1 := fun N => (htt N).trans_lt ht₀
  obtain ⟨C, hC0, hJ⟩ := Step2Bootstrap.exists_jS_envelope
    (Gauss.sample d) hκ0 hκ1 hEκ hD (cη := 1) (by norm_num)
    hs0 ht1 (eventually_eta_window_of_fixed_t0 hE ht₀ htt)
  have hXi := Step2FarInputs.eventually_xiK_le (Gauss.band d)
    (mE E).im (τ := 1) (by norm_num)
  filter_upwards [hJ, hXi, (Step2.tendsto_W (Gauss.band d)).eventually_ge_atTop (Real.exp 1),
    SumZeroDyn.eventually_const_mul_rpow_le C (show D + 3 < D + 4 by linarith),
    eventually_ge_atTop 1] with N hJN hXiN hWN hAbs hN1 a ω
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNpow : 0 ≤ (N : ℝ) ^ (D + 2) := Real.rpow_nonneg hN0.le _
  have hXi0 := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
  have hJ0 : 0 ≤ Step2.jS (Gauss.sample d) E D N (s N) ω :=
    zero_le_one.trans (Step2Moment.one_le_jS (Gauss.sample d) N (s N) ω)
  have hY := initial_evolved_normalized_le (Gauss.sample d) hE
    (hs0 N) (hst N) (ht1 N) hWN D ω a
  have hJb : Step2.jS (Gauss.sample d) E D N (s N) ω ≤
      C * (N : ℝ) ^ (D + 2) := by
    simpa only [mul_one] using hJN (s N) ⟨le_rfl, hst N⟩ ω
  calc
    initialEvolvedNorm (Gauss.sample d) E D s t N a ω
        ≤ Step2.jS (Gauss.sample d) E D N (s N) ω *
          Step2.xiK (d.L N) (d.W N) (mE E).im := hY
    _ ≤ (C * (N : ℝ) ^ (D + 2)) * (N : ℝ) ^ (1 : ℝ) := by
        exact mul_le_mul hJb hXiN hXi0 (by positivity)
    _ = C * (N : ℝ) ^ (D + 3) := by
        calc
          (C * (N : ℝ) ^ (D + 2)) * (N : ℝ) ^ (1 : ℝ)
              = C * ((N : ℝ) ^ (D + 2) * (N : ℝ) ^ (1 : ℝ)) := by ring
          _ = C * (N : ℝ) ^ ((D + 2) + 1) := by
              conv_rhs => rw [Real.rpow_add hN0]
          _ = C * (N : ℝ) ^ (D + 3) := by ring
    _ ≤ (N : ℝ) ^ (D + 4) := hAbs

theorem eventually_initialEvolvedNormAt_le_rpow (d : Gauss.Dims)
    {E D t₀ : ℝ} (hE : |E| < 2) (hD : 0 ≤ D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      ∀ a : LoopArg (d.L N) 2, ∀ ω : Gauss.Ω d,
      initialEvolvedNormAt (Gauss.sample d) E D s N v a ω ≤
        (N : ℝ) ^ (D + 4) := by
  let κ : ℝ := min 1 (2 - |E|)
  have hκ0 : 0 < κ := lt_min (by norm_num) (by linarith)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hEκ : |E| ≤ 2 - κ := by have := min_le_right (1 : ℝ) (2 - |E|); dsimp [κ]; linarith
  have ht1 : ∀ N, t N < 1 := fun N => (htt N).trans_lt ht₀
  obtain ⟨C, hC0, hJ⟩ := Step2Bootstrap.exists_jS_envelope
    (Gauss.sample d) hκ0 hκ1 hEκ hD (cη := 1) (by norm_num)
    hs0 ht1 (eventually_eta_window_of_fixed_t0 hE ht₀ htt)
  have hXi := Step2FarInputs.eventually_xiK_le (Gauss.band d)
    (mE E).im (τ := 1) (by norm_num)
  filter_upwards [hJ, hXi, (Step2.tendsto_W (Gauss.band d)).eventually_ge_atTop (Real.exp 1),
    SumZeroDyn.eventually_const_mul_rpow_le C (show D + 3 < D + 4 by linarith),
    eventually_ge_atTop 1] with N hJN hXiN hWN hAbs hN1 v a ω
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hXi0 := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
  have hY := initial_evolved_normalized_le_at (Gauss.sample d) hE
    (hs0 N) (ht1 N) hWN D ω v a
  have hJb : Step2.jS (Gauss.sample d) E D N (s N) ω ≤
      C * (N : ℝ) ^ (D + 2) := by
    simpa only [mul_one] using hJN (s N) ⟨le_rfl, hst N⟩ ω
  calc
    initialEvolvedNormAt (Gauss.sample d) E D s N v a ω
        ≤ Step2.jS (Gauss.sample d) E D N (s N) ω *
          Step2.xiK (d.L N) (d.W N) (mE E).im := hY
    _ ≤ (C * (N : ℝ) ^ (D + 2)) * (N : ℝ) ^ (1 : ℝ) := by
        exact mul_le_mul hJb hXiN hXi0 (by positivity)
    _ = C * (N : ℝ) ^ (D + 3) := by
        calc
          (C * (N : ℝ) ^ (D + 2)) * (N : ℝ) ^ (1 : ℝ)
              = C * ((N : ℝ) ^ (D + 2) * (N : ℝ) ^ (1 : ℝ)) := by ring
          _ = C * (N : ℝ) ^ ((D + 2) + 1) := by
              conv_rhs => rw [Real.rpow_add hN0]
          _ = C * (N : ℝ) ^ (D + 3) := by ring
    _ ≤ (N : ℝ) ^ (D + 4) := hAbs

/-- The reverse domination-to-moment bridge only needs its deterministic
envelope eventually.  A zero prefix supplies the all-size interface of the
existing theorem without changing any eventual conclusion. -/
theorem momentDom_of_stochDom_of_eventual_envelope
    {P : Measure Ω} [IsFiniteMeasure P]
    {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ}
    {Φ : ∀ N, U N → ℝ} {K Bexp : ℝ}
    (hY0 : ∀ N (u : U N) ω, 0 ≤ Y N u ω)
    (hmeas : ∀ N (u : U N), Measurable (Y N u))
    (hint : ∀ p N (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hΦ : ∀ N (u : U N), 0 < Φ N u)
    (hB : 0 ≤ Bexp)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u : U N, (N : ℝ) ^ (-Bexp) ≤ Φ N u)
    (hK : 0 ≤ K)
    (henv : ∀ᶠ N : ℕ in atTop, ∀ u : U N, ∀ ω, Y N u ω ≤ (N : ℝ) ^ K)
    (hdom : StochDom P Y (fun N u _ => Φ N u)) :
    Gauss.MomentDom P Y Φ := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 henv
  let Y' : ∀ N, U N → Ω → ℝ := fun N u ω => if N₀ ≤ N then Y N u ω else 0
  let Env : ℕ → ℝ := fun N => if N₀ ≤ N then (N : ℝ) ^ K else 0
  have hY'0 : ∀ N (u : U N) ω, 0 ≤ Y' N u ω := by
    intro N u ω; by_cases h : N₀ ≤ N <;> simp [Y', h, hY0]
  have hmeas' : ∀ N (u : U N), Measurable (Y' N u) := by
    intro N u; by_cases h : N₀ ≤ N <;> simp [Y', h, hmeas]
  have hint' : ∀ p N (u : U N), Integrable
      (fun ω => |Y' N u ω| ^ (2 * p)) P := by
    intro p N u; by_cases h : N₀ ≤ N
    · simpa [Y', h] using hint p N u
    · simpa [Y', h] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
  have hEnv0 : ∀ N, 0 ≤ Env N := by
    intro N; by_cases h : N₀ ≤ N <;> simp [Env, h, Real.rpow_nonneg]
  have henv' : ∀ N (u : U N) ω, Y' N u ω ≤ Env N := by
    intro N u ω; by_cases h : N₀ ≤ N
    · simpa [Y', Env, h] using hN₀ N h u ω
    · simp [Y', Env, h]
  have hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ K := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    simp [Env, hN]
  have hdom' : StochDom P Y' (fun N u _ => Φ N u) := by
    intro ε hε D hD
    filter_upwards [hdom ε hε D hD, eventually_ge_atTop N₀] with N hN hN₀'
    have heq : badSet Y' (fun N u _ => Φ N u) ε N =
        badSet Y (fun N u _ => Φ N u) ε N := by
      ext ω
      simp [badSet, Y', hN₀']
    rw [heq]
    exact hN
  have hmom := Gauss.momentDom_of_stochDom_of_nonneg hY'0 hmeas' hint'
    hΦ hB hΦlow hEnv0 hK henv' hEnvpoly hdom'
  intro ε hε p
  obtain ⟨C, hC, hCev⟩ := hmom ε hε p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCev, eventually_ge_atTop N₀] with N hCN hN₀' u
  simpa [Y', hN₀'] using hCN u

/-- The `hinit` stochastic input from (2.69) and the absolute-kernel tail
estimate.  This is uniform over all two-loop coordinates `a`. -/
theorem initialEvolvedNorm_stochDom (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (hB : BoundsCore X E s)
    (D : ℝ) (hD : 0 < D) :
    StochDom B.P (fun N (a : LoopArg (B.L N) 2) ω =>
      initialEvolvedNorm X E D s t N a ω) (fun _ _ _ => (1 : ℝ)) := by
  have hJunit := APrimeSlotFields.stochDom_jS_init_of_boundsCore X hE hst ht1 hc hB D hD
  have hJ : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) ω =>
      Step2.jS X E D N (s N) ω) (fun _ _ _ => (1 : ℝ)) :=
    hJunit.precomp_param (fun _ _ => ())
  have hXiDet : UnifDetDom
      (fun N (_ : LoopArg (B.L N) 2) => Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ => (1 : ℝ)) := by
    intro τ hτ
    filter_upwards [Step2FarInputs.eventually_xiK_le B (mE E).im hτ] with N hN a
    simpa using hN
  have hXi : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) (_ : Ω) =>
      Step2.xiK (B.L N) (B.W N) (mE E).im) (fun _ _ _ => (1 : ℝ)) :=
    StochDom.of_unifDetDom hXiDet
  have hprod : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) ω =>
      Step2.jS X E D N (s N) ω * Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ _ => (1 : ℝ)) := by
    have hh := StochDom.mul (P := B.P)
      (ξ₁ := fun N (_ : LoopArg (B.L N) 2) ω => Step2.jS X E D N (s N) ω)
      (ξ₂ := fun N (_ : LoopArg (B.L N) 2) (_ : Ω) =>
        Step2.xiK (B.L N) (B.W N) (mE E).im)
      (ζ₁ := fun _ _ _ => (1 : ℝ)) (ζ₂ := fun _ _ _ => (1 : ℝ))
      (fun N _ _ => Step2.xiK_nonneg _ _ _)
      (fun _ _ _ => zero_le_one) hJ hXi
    simpa [StochDom, badSet, Pi.mul_apply] using hh
  refine StochDom.of_subset hprod (fun τ hτ => ⟨τ, hτ, ?_⟩)
  filter_upwards [(Step2.tendsto_W B).eventually_ge_atTop (Real.exp 1)] with N hWN
  intro ω hω
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, lt_of_lt_of_le ha ?_⟩
  exact initial_evolved_normalized_le X hE (hs0 N) (hst N) (ht1 N) hWN D ω a

/-- The form needed for the numerical initial slot: the remaining `R⁻²`
is retained in the deterministic control for the reverse moment bridge. -/
theorem initialEvolvedNorm_stochDom_sharp (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (hB : BoundsCore X E s)
    (D : ℝ) (hD : 0 < D) :
    StochDom B.P (fun N (a : LoopArg (B.L N) 2) ω =>
      initialEvolvedNorm X E D s t N a ω)
      (fun N _ _ => (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ))) := by
  have hJunit := APrimeSlotFields.stochDom_jS_init_of_boundsCore X hE hst ht1 hc hB D hD
  have hJ : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) ω =>
      Step2.jS X E D N (s N) ω) (fun _ _ _ => (1 : ℝ)) :=
    hJunit.precomp_param (fun _ _ => ())
  have hXiDet : UnifDetDom
      (fun N (_ : LoopArg (B.L N) 2) => Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ => (1 : ℝ)) := by
    intro τ hτ
    filter_upwards [Step2FarInputs.eventually_xiK_le B (mE E).im hτ] with N hN a
    simpa using hN
  have hXi : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) (_ : Ω) =>
      Step2.xiK (B.L N) (B.W N) (mE E).im) (fun _ _ _ => (1 : ℝ)) :=
    StochDom.of_unifDetDom hXiDet
  have hprod : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) ω =>
      Step2.jS X E D N (s N) ω * Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ _ => (1 : ℝ)) := by
    have hh := StochDom.mul (P := B.P)
      (ξ₁ := fun N (_ : LoopArg (B.L N) 2) ω => Step2.jS X E D N (s N) ω)
      (ξ₂ := fun N (_ : LoopArg (B.L N) 2) (_ : Ω) =>
        Step2.xiK (B.L N) (B.W N) (mE E).im)
      (ζ₁ := fun _ _ _ => (1 : ℝ)) (ζ₂ := fun _ _ _ => (1 : ℝ))
      (fun N _ _ => Step2.xiK_nonneg _ _ _)
      (fun _ _ _ => zero_le_one) hJ hXi
    simpa [StochDom, badSet, Pi.mul_apply] using hh
  let f : ℕ → ℝ := fun N => (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ))
  have hf : ∀ N, 0 ≤ f N := fun N => Real.rpow_nonneg
    (Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) (ht1 N)).le _
  have hscaled : StochDom B.P (fun N (_ : LoopArg (B.L N) 2) ω =>
      f N * (Step2.jS X E D N (s N) ω * Step2.xiK (B.L N) (B.W N) (mE E).im))
      (fun N _ _ => f N) := by
    have hh := StochDom.det_mul_of (P := B.P) hf
      (ξ := fun N (_ : LoopArg (B.L N) 2) ω =>
        Step2.jS X E D N (s N) ω * Step2.xiK (B.L N) (B.W N) (mE E).im)
      (ζ := fun _ _ _ => (1 : ℝ))
      (fun N _ ω => mul_nonneg
        (zero_le_one.trans (Step2Moment.one_le_jS X N (s N) ω))
        (Step2.xiK_nonneg _ _ _)) hprod
    simpa [StochDom, badSet, f] using hh
  refine StochDom.of_subset hscaled (fun τ hτ => ⟨τ, hτ, ?_⟩)
  filter_upwards [(Step2.tendsto_W B).eventually_ge_atTop (Real.exp 1)] with N hWN
  intro ω hω
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, lt_of_lt_of_le ha ?_⟩
  have hsharp := initial_evolved_normalized_le_sharp X hE
    (hs0 N) (hst N) (ht1 N) hWN D ω a
  simpa [initialEvolvedNorm, f, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hsharp

/-- The sharp initial domination with the right endpoint included in the
parameter set.  One exceptional event controls every endpoint in the window
and every two-loop coordinate at each size. -/
theorem initialEvolvedNorm_stochDom_sharp' (X : Sample B)
    {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (D : ℝ) (hD : 0 < D) :
    StochDom B.P
      (fun N (va : TimeIcc s t N × LoopArg (B.L N) 2) ω =>
        initialEvolvedNormAt X E D s N va.1 va.2 ω)
      (fun N va _ => (etaT E (s N) / etaT E va.1) ^ (-(2 : ℝ))) := by
  have hJunit := APrimeSlotFields.stochDom_jS_init_of_boundsCore
    X hE hst ht1 hc hB D hD
  have hJ : StochDom B.P
      (fun N (_ : TimeIcc s t N × LoopArg (B.L N) 2) ω =>
        Step2.jS X E D N (s N) ω) (fun _ _ _ => (1 : ℝ)) :=
    hJunit.precomp_param (fun _ _ => ())
  have hXiDet : UnifDetDom
      (fun N (_ : TimeIcc s t N × LoopArg (B.L N) 2) =>
        Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ => (1 : ℝ)) := by
    intro τ hτ
    filter_upwards [Step2FarInputs.eventually_xiK_le B (mE E).im hτ]
      with N hN va
    simpa using hN
  have hXi : StochDom B.P
      (fun N (_ : TimeIcc s t N × LoopArg (B.L N) 2) (_ : Ω) =>
        Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ _ => (1 : ℝ)) := StochDom.of_unifDetDom hXiDet
  have hprod : StochDom B.P
      (fun N (_ : TimeIcc s t N × LoopArg (B.L N) 2) ω =>
        Step2.jS X E D N (s N) ω *
          Step2.xiK (B.L N) (B.W N) (mE E).im)
      (fun _ _ _ => (1 : ℝ)) := by
    have hh := StochDom.mul (P := B.P)
      (ξ₁ := fun N (_ : TimeIcc s t N × LoopArg (B.L N) 2) ω =>
        Step2.jS X E D N (s N) ω)
      (ξ₂ := fun N (_ : TimeIcc s t N × LoopArg (B.L N) 2) (_ : Ω) =>
        Step2.xiK (B.L N) (B.W N) (mE E).im)
      (ζ₁ := fun _ _ _ => (1 : ℝ)) (ζ₂ := fun _ _ _ => (1 : ℝ))
      (fun N _ _ => Step2.xiK_nonneg _ _ _)
      (fun _ _ _ => zero_le_one) hJ hXi
    simpa [StochDom, badSet, Pi.mul_apply] using hh
  refine StochDom.of_subset hprod (fun τ hτ => ⟨τ, hτ, ?_⟩)
  filter_upwards [(Step2.tendsto_W B).eventually_ge_atTop (Real.exp 1)] with N hWN
  intro ω hω
  obtain ⟨⟨v, a⟩, ha⟩ := hω
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hR : 0 < etaT E (s N) / etaT E v :=
    Step2Moment.ratR_pos hE (v.2.1.trans_lt hv1) hv1
  have hΦ : 0 < (etaT E (s N) / etaT E v) ^ (-(2 : ℝ)) :=
    Real.rpow_pos_of_pos hR _
  have hY := initial_evolved_normalized_le_sharp_at X hE (hs0 N)
    (ht1 N) hWN D ω v a
  have hY' : initialEvolvedNormAt X E D s N v a ω ≤
      (Step2.jS X E D N (s N) ω *
        Step2.xiK (B.L N) (B.W N) (mE E).im) *
          (etaT E (s N) / etaT E v) ^ (-(2 : ℝ)) := by
    calc
      _ ≤ (Step2.jS X E D N (s N) ω *
          Step2.xiK (B.L N) (B.W N) (mE E).im) /
            (etaT E (s N) / etaT E v) ^ 2 := hY
      _ = _ := by rw [Real.rpow_neg hR.le, Real.rpow_ofNat, div_eq_mul_inv]
  have hlt := lt_of_lt_of_le ha hY'
  have hlt' := lt_of_mul_lt_mul_right hlt hΦ.le
  refine ⟨(v, a), ?_⟩
  simpa only [mul_one] using hlt'

/-- The model-level reverse bridge for the actual Gaussian initial coordinate.
The all-size regularity comes from the Gaussian resolvent; the polynomial
envelope is needed only eventually and is supplied on the fixed time window. -/
theorem initialEvolvedNorm_momentDom_gauss (d : Gauss.Dims)
    {E D t₀ : ℝ} (hE : |E| < 2) (hD : 0 < D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀)
    (hc : Cond272 (Gauss.band d) E s t)
    (hB : BoundsCore (Gauss.sample d) E s) :
    Gauss.MomentDom (Gauss.band d).P
      (fun N (a : LoopArg (d.L N) 2) ω =>
        initialEvolvedNorm (Gauss.sample d) E D s t N a ω)
      (fun N _ => (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ))) := by
  letI := (Gauss.band d).isProbabilityMeasure
  have ht1 : ∀ N, t N < 1 := fun N => (htt N).trans_lt ht₀
  have hY0 : ∀ N (a : LoopArg (d.L N) 2) ω,
      0 ≤ initialEvolvedNorm (Gauss.sample d) E D s t N a ω := by
    intro N a ω
    have hR := Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) (ht1 N)
    have hT : 0 < Step2.tT (Gauss.band d) E N D (t N)
        (zdist (d.L N) (a 0 - a 1)) :=
      tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
    unfold initialEvolvedNorm
    exact div_nonneg (norm_nonneg _) (mul_pos hT (by positivity)).le
  exact momentDom_of_stochDom_of_eventual_envelope hY0
    (measurable_initialEvolvedNorm_gauss d hE hs0 hst ht1 D)
    (integrable_initialEvolvedNorm_pow_gauss d hE hs0 hst ht1 D)
    (fun N a => Real.rpow_pos_of_pos
      (Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) (ht1 N)) _)
    (Bexp := 1) (by norm_num)
    (by filter_upwards [eventually_initial_phi_lower_of_fixed_t0 hE ht₀ hs0 hst htt]
      with N hN a; exact hN)
    (K := D + 4) (by linarith)
    (eventually_initialEvolvedNorm_le_rpow d hE hD.le ht₀ hs0 hst htt)
    (initialEvolvedNorm_stochDom_sharp (Gauss.sample d) hE hs0 hst ht1 hc hB D hD)

theorem initialEvolvedNorm_momentDom_gauss' (d : Gauss.Dims)
    {E D t₀ : ℝ} (hE : |E| < 2) (hD : 0 < D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀)
    (hc : Cond272 (Gauss.band d) E s t)
    (hB : BoundsCore (Gauss.sample d) E s) :
    Gauss.MomentDom (Gauss.band d).P
      (fun N (va : TimeIcc s t N × LoopArg (d.L N) 2) ω =>
        initialEvolvedNormAt (Gauss.sample d) E D s N va.1 va.2 ω)
      (fun N va => (etaT E (s N) / etaT E va.1) ^ (-(2 : ℝ))) := by
  letI := (Gauss.band d).isProbabilityMeasure
  have ht1 : ∀ N, t N < 1 := fun N => (htt N).trans_lt ht₀
  have hY0 : ∀ N (va : TimeIcc s t N × LoopArg (d.L N) 2) ω,
      0 ≤ initialEvolvedNormAt (Gauss.sample d) E D s N va.1 va.2 ω := by
    intro N ⟨v, a⟩ ω
    have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
    have hR := Step2Moment.ratR_pos hE (v.2.1.trans_lt hv1) hv1
    have hT : 0 < Step2.tT (Gauss.band d) E N D v
        (zdist (d.L N) (a 0 - a 1)) :=
      tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
    unfold initialEvolvedNormAt
    exact div_nonneg (norm_nonneg _) (mul_pos hT (by positivity)).le
  exact momentDom_of_stochDom_of_eventual_envelope hY0
    (fun N va => measurable_initialEvolvedNormAt_gauss d hE hs0 hst ht1 N va.1 D va.2)
    (fun p N va => integrable_initialEvolvedNormAt_pow_gauss d hE hs0 hst ht1 p N va.1 D va.2)
    (fun N va => Real.rpow_pos_of_pos
      (Step2Moment.ratR_pos hE
        (va.1.2.1.trans_lt (va.1.2.2.trans_lt (ht1 N)))
        (va.1.2.2.trans_lt (ht1 N))) _)
    (Bexp := 1) (by norm_num)
    (by filter_upwards [eventually_initial_phi_lower_of_fixed_t0' hE ht₀ hs0 hst htt]
      with N hN va; exact hN va.1)
    (K := D + 4) (by linarith)
    (by filter_upwards [eventually_initialEvolvedNormAt_le_rpow d hE hD.le ht₀ hs0 hst htt]
      with N hN va ω; exact hN va.1 va.2 ω)
    (initialEvolvedNorm_stochDom_sharp' (Gauss.sample d) hE hs0 hst ht1 hc hB D hD)

theorem weighted_moments_of_momentDom {P : Measure Ω} [IsFiniteMeasure P]
    {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    (hint : ∀ p N (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (W : ∀ N, U N → Ω → ℝ)
    (hWm : ∀ N (u : U N), AEStronglyMeasurable (W N u) P)
    (hW0 : ∀ N u ω, 0 ≤ W N u ω)
    (hW1 : ∀ N u ω, W N u ω ≤ 1)
    (hmom : Gauss.MomentDom P Y Φ) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u : U N,
        ∫ ω, W N u ω * |Y N u ω| ^ (2 * p) ∂P
          ≤ C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p)) := by
  have hWint : ∀ p N (u : U N), Integrable
      (fun ω => W N u ω * |Y N u ω| ^ (2 * p)) P := by
    intro p N u
    have hYm : AEStronglyMeasurable (fun ω => |Y N u ω| ^ (2 * p)) P :=
      (hint p N u).aestronglyMeasurable
    refine Integrable.mono' (hint p N u) ((hWm N u).mul hYm) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hW0 N u ω) (pow_nonneg (abs_nonneg _) _))]
    exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) (hW1 N u ω)
  intro ε hε p
  obtain ⟨C, hC, hCev⟩ := hmom ε hε p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCev] with N hN u
  exact (integral_mono (hWint p N u) (hint p N u)
    (fun ω => mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) (hW1 N u ω))).trans
      (hN u)

theorem eventually_momNormW_le_small_initial_scale {P : Measure Ω}
    {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ}
    {Φ : ∀ N, U N → ℝ} {W : ∀ N, U N → Ω → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p)
    (hW0 : ∀ N u ω, 0 ≤ W N u ω)
    (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hmom : ∀ ε > (0 : ℝ), ∀ q : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ u : U N,
        ∫ ω, W N u ω * |Y N u ω| ^ (2 * q) ∂P
          ≤ C * ((N : ℝ) ^ (ε * q) * Φ N u ^ (2 * q))) :
    ∀ᶠ N : ℕ in atTop, ∀ u : U N,
      MomentDuhamel.momNormW P (W N u) p (Y N u) ≤
        (N : ℝ) ^ (5 * δ / 32) * Φ N u := by
  obtain ⟨C, hC, hCev⟩ := hmom (δ / 8) (by linarith) p
  have hgap : (δ / 8) * (p : ℝ) < (5 * δ / 16) * (p : ℝ) := by
    have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    nlinarith
  filter_upwards [hCev, SumZeroDyn.eventually_const_mul_rpow_le C hgap,
    eventually_ge_atTop 1] with N hN hAbs hN1 u
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hΦpow : 0 ≤ Φ N u ^ (2 * p) := pow_nonneg (hΦ0 N u) _
  have hpow : (N : ℝ) ^ ((5 * δ / 16) * (p : ℝ)) =
      ((N : ℝ) ^ (5 * δ / 32)) ^ (2 * p) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (5 * δ / 32)) (2 * p),
      ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hcslot : 0 ≤ (N : ℝ) ^ (5 * δ / 32) * Φ N u :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (hΦ0 N u)
  have hint : ∫ ω, W N u ω * |Y N u ω| ^ (2 * p) ∂P ≤
      ((N : ℝ) ^ (5 * δ / 32) * Φ N u) ^ (2 * p) := by
    calc
      _ ≤ C * ((N : ℝ) ^ ((δ / 8) * (p : ℝ)) * Φ N u ^ (2 * p)) := hN u
      _ = (C * (N : ℝ) ^ ((δ / 8) * (p : ℝ))) * Φ N u ^ (2 * p) := by ring
      _ ≤ (N : ℝ) ^ ((5 * δ / 16) * (p : ℝ)) * Φ N u ^ (2 * p) :=
        mul_le_mul_of_nonneg_right hAbs hΦpow
      _ = ((N : ℝ) ^ (5 * δ / 32) * Φ N u) ^ (2 * p) := by
        rw [mul_pow, ← hpow]
  exact APrimeInit.numerical_hinit_of_weighted_integral hp hcslot (hW0 N u) hint

/-- The small initial slot is exactly the normalized `N^(5δ/32)` scale. -/
theorem initial_slot_scale_eq {δ R : ℝ} {N : ℕ} (hN : 1 ≤ N) (hR : 0 < R) :
    APrimeOneStep.initTerm ((N : ℝ) ^ (δ / 8)) R
      (APrimeInit.slotXi' ((N : ℝ) ^ (δ / 8))) / R ^ 4 =
      (N : ℝ) ^ (5 * δ / 32) * R ^ (-(2 : ℝ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx0 : 0 < (N : ℝ) ^ (δ / 8) := Real.rpow_pos_of_pos hN0 _
  have hR0 : R ≠ 0 := ne_of_gt hR
  rw [APrimeOneStep.initTerm, APrimeInit.slotXi']
  have hx : (N : ℝ) ^ (δ / 8) * ((N : ℝ) ^ (δ / 8)) ^ (1 / 4 : ℝ) =
      (N : ℝ) ^ (5 * δ / 32) := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    ring
  rw [show (N : ℝ) ^ (δ / 8) * R ^ 2 *
      ((N : ℝ) ^ (δ / 8)) ^ (1 / 4 : ℝ) =
      ((N : ℝ) ^ (δ / 8) * ((N : ℝ) ^ (δ / 8)) ^ (1 / 4 : ℝ)) * R ^ 2 by ring,
    hx, Real.rpow_neg hR.le, Real.rpow_ofNat]
  field_simp

/-- The first-pass numerical initial slot holds at one eventual size threshold
for every endpoint and every coordinate simultaneously. -/
theorem eventually_initial_hinit_gauss' (d : Gauss.Dims)
    {E D t₀ δ : ℝ} (hE : |E| < 2) (hD : 0 < D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀)
    (hc : Cond272 (Gauss.band d) E s t)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p)
    (W : ∀ N, (TimeIcc s t N × LoopArg (d.L N) 2) → Gauss.Ω d → ℝ)
    (hWm : ∀ N (va : TimeIcc s t N × LoopArg (d.L N) 2),
      AEStronglyMeasurable (W N va) (Gauss.band d).P)
    (hW0 : ∀ N va ω, 0 ≤ W N va ω)
    (hW1 : ∀ N va ω, W N va ω ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ va : TimeIcc s t N × LoopArg (d.L N) 2,
      MomentDuhamel.momNormW (Gauss.band d).P (W N va) p
        (initialEvolvedNormAt (Gauss.sample d) E D s N va.1 va.2) ≤
        APrimeOneStep.initTerm ((N : ℝ) ^ (δ / 8))
          (etaT E (s N) / etaT E va.1)
          (APrimeInit.slotXi' ((N : ℝ) ^ (δ / 8))) /
          (etaT E (s N) / etaT E va.1) ^ 4 := by
  letI := (Gauss.band d).isProbabilityMeasure
  have ht1 : ∀ N, t N < 1 := fun N => (htt N).trans_lt ht₀
  have hint : ∀ q N (va : TimeIcc s t N × LoopArg (d.L N) 2), Integrable
      (fun ω => |initialEvolvedNormAt (Gauss.sample d) E D s N va.1 va.2 ω| ^ (2 * q))
      (Gauss.band d).P := fun q N va =>
        integrable_initialEvolvedNormAt_pow_gauss d hE hs0 hst ht1 q N va.1 D va.2
  have hmom := weighted_moments_of_momentDom hint W hWm hW0 hW1
    (initialEvolvedNorm_momentDom_gauss' d hE hD ht₀ hs0 hst htt hc hB)
  have hΦ0 : ∀ N (va : TimeIcc s t N × LoopArg (d.L N) 2),
      0 ≤ (etaT E (s N) / etaT E va.1) ^ (-(2 : ℝ)) := by
    intro N va
    exact (Real.rpow_pos_of_pos
      (Step2Moment.ratR_pos hE
        (va.1.2.1.trans_lt (va.1.2.2.trans_lt (ht1 N)))
        (va.1.2.2.trans_lt (ht1 N))) _).le
  have hsmall := eventually_momNormW_le_small_initial_scale hδ p hp hW0 hΦ0 hmom
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN hN1 va
  have hv1 : (va.1 : ℝ) < 1 := va.1.2.2.trans_lt (ht1 N)
  have hR : 0 < etaT E (s N) / etaT E va.1 :=
    Step2Moment.ratR_pos hE (va.1.2.1.trans_lt hv1) hv1
  have hscale := initial_slot_scale_eq (δ := δ)
    (R := etaT E (s N) / etaT E va.1) hN1 hR
  rw [hscale]
  exact hN va

/-- The concrete initial moments remain valid after multiplication by any
measurable weight in `[0,1]`, including the T280a stopping weight. -/
theorem initialEvolvedNorm_weighted_moments_gauss (d : Gauss.Dims)
    {E D t₀ : ℝ} (hE : |E| < 2) (hD : 0 < D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀)
    (hc : Cond272 (Gauss.band d) E s t)
    (hB : BoundsCore (Gauss.sample d) E s)
    (W : ∀ N, LoopArg (d.L N) 2 → Gauss.Ω d → ℝ)
    (hWm : ∀ N (a : LoopArg (d.L N) 2),
      AEStronglyMeasurable (W N a) (Gauss.band d).P)
    (hW0 : ∀ N a ω, 0 ≤ W N a ω)
    (hW1 : ∀ N a ω, W N a ω ≤ 1) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ a : LoopArg (d.L N) 2,
        ∫ ω, W N a ω *
          |initialEvolvedNorm (Gauss.sample d) E D s t N a ω| ^ (2 * p)
          ∂(Gauss.band d).P
        ≤ C * ((N : ℝ) ^ (ε * p) *
          ((etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ))) ^ (2 * p)) := by
  letI := (Gauss.band d).isProbabilityMeasure
  have ht1 : ∀ N, t N < 1 := fun N => (htt N).trans_lt ht₀
  have hYint : ∀ p N (a : LoopArg (d.L N) 2), Integrable
      (fun ω => |initialEvolvedNorm (Gauss.sample d) E D s t N a ω| ^ (2 * p))
      (Gauss.band d).P :=
    integrable_initialEvolvedNorm_pow_gauss d hE hs0 hst ht1 D
  have hWint : ∀ p N (a : LoopArg (d.L N) 2), Integrable
      (fun ω => W N a ω *
        |initialEvolvedNorm (Gauss.sample d) E D s t N a ω| ^ (2 * p))
      (Gauss.band d).P := by
    intro p N a
    have hYmeas : Measurable
        (initialEvolvedNorm (Gauss.sample d) E D s t N a) :=
      measurable_initialEvolvedNorm_gauss d hE hs0 hst ht1 D N a
    have hYm : AEStronglyMeasurable
        (fun ω => |initialEvolvedNorm (Gauss.sample d) E D s t N a ω| ^ (2 * p))
        (Gauss.band d).P := by
      simpa only [Real.norm_eq_abs] using
        (hYmeas.norm.pow_const (2 * p)).aestronglyMeasurable
    refine Integrable.mono' (hYint p N a)
      ((hWm N a).mul hYm) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hW0 N a ω) (pow_nonneg (abs_nonneg _) _))]
    exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) (hW1 N a ω)
  have hmom := initialEvolvedNorm_momentDom_gauss d hE hD ht₀ hs0 hst htt hc hB
  intro ε hε p
  obtain ⟨C, hC, hCev⟩ := hmom ε hε p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCev] with N hN a
  have hle := integral_mono (hWint p N a) (hYint p N a)
    (fun ω => mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) (hW1 N a ω))
  exact hle.trans (hN a)

/-- The actual Gaussian initial coordinate fits the first-pass numerical
`hinit` slot for each fixed positive moment order.  All the analytic
regularity required by the reverse bridge is supplied above. -/
theorem eventually_initial_hinit_gauss (d : Gauss.Dims)
    {E D t₀ δ : ℝ} (hE : |E| < 2) (hD : 0 < D) (ht₀ : t₀ < 1)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (htt : ∀ N, t N ≤ t₀)
    (hc : Cond272 (Gauss.band d) E s t)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p)
    (W : ∀ N, LoopArg (d.L N) 2 → Gauss.Ω d → ℝ)
    (hWm : ∀ N (a : LoopArg (d.L N) 2),
      AEStronglyMeasurable (W N a) (Gauss.band d).P)
    (hW0 : ∀ N a ω, 0 ≤ W N a ω)
    (hW1 : ∀ N a ω, W N a ω ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
      MomentDuhamel.momNormW (Gauss.band d).P (W N a) p
        (initialEvolvedNorm (Gauss.sample d) E D s t N a) ≤
        APrimeOneStep.initTerm ((N : ℝ) ^ (δ / 8))
          (etaT E (s N) / etaT E (t N))
          (APrimeInit.slotXi' ((N : ℝ) ^ (δ / 8))) /
          (etaT E (s N) / etaT E (t N)) ^ 4 := by
  have hmom := initialEvolvedNorm_weighted_moments_gauss d
    hE hD ht₀ hs0 hst htt hc hB W hWm hW0 hW1
  obtain ⟨C, hC, hCev⟩ := hmom (δ / 8) (by linarith) p
  have hgap : (δ / 8) * (p : ℝ) < (5 * δ / 16) * (p : ℝ) := by
    have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    nlinarith
  filter_upwards [hCev, SumZeroDyn.eventually_const_mul_rpow_le C hgap,
    eventually_ge_atTop 1] with N hN hAbs hN1 a
  let R : ℝ := etaT E (s N) / etaT E (t N)
  let x : ℝ := (N : ℝ) ^ (δ / 8)
  have hR : 0 < R := Step2Moment.ratR_pos hE
    ((hst N).trans_lt ((htt N).trans_lt ht₀)) ((htt N).trans_lt ht₀)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hΦpow : 0 ≤ (R ^ (-(2 : ℝ))) ^ (2 * p) := by positivity
  have hpow : (N : ℝ) ^ ((5 * δ / 16) * (p : ℝ)) =
      ((N : ℝ) ^ (5 * δ / 32)) ^ (2 * p) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (5 * δ / 32)) (2 * p),
      ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hscale := initial_slot_scale_eq (δ := δ) (R := R) hN1 hR
  have hcslot : 0 ≤ APrimeOneStep.initTerm x R (APrimeInit.slotXi' x) / R ^ 4 := by
    rw [show x = (N : ℝ) ^ (δ / 8) from rfl, hscale]
    positivity
  have hint : ∫ ω, W N a ω *
      |initialEvolvedNorm (Gauss.sample d) E D s t N a ω| ^ (2 * p)
      ∂(Gauss.band d).P ≤
      (APrimeOneStep.initTerm x R (APrimeInit.slotXi' x) / R ^ 4) ^ (2 * p) := by
    calc
      _ ≤ C * ((N : ℝ) ^ ((δ / 8) * (p : ℝ)) *
          (R ^ (-(2 : ℝ))) ^ (2 * p)) := hN a
      _ = (C * (N : ℝ) ^ ((δ / 8) * (p : ℝ))) *
          (R ^ (-(2 : ℝ))) ^ (2 * p) := by ring
      _ ≤ (N : ℝ) ^ ((5 * δ / 16) * (p : ℝ)) *
          (R ^ (-(2 : ℝ))) ^ (2 * p) :=
            mul_le_mul_of_nonneg_right hAbs hΦpow
      _ = ((N : ℝ) ^ (5 * δ / 32) * R ^ (-(2 : ℝ))) ^ (2 * p) := by
          rw [mul_pow, ← hpow]
      _ = (APrimeOneStep.initTerm x R (APrimeInit.slotXi' x) / R ^ 4) ^ (2 * p) := by
          rw [show x = (N : ℝ) ^ (δ / 8) from rfl, hscale]
  exact APrimeInit.numerical_hinit_of_weighted_integral hp hcslot (hW0 N a) hint

/-- Conditional reverse bridge for the actual evolved initial observable.  The
stochastic input is proved above from `BoundsCore`; the remaining analytic
regularity and polynomial envelope are stated explicitly because no concrete
Gaussian supplier has yet been connected to this observable. -/
theorem initialEvolvedNorm_weighted_moments (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (hB : BoundsCore X E s)
    (D : ℝ) (hD : 0 < D) [MeasureTheory.IsFiniteMeasure B.P]
    {Bexp Kenv : ℝ} (hBexp : 0 ≤ Bexp) (hKenv : 0 ≤ Kenv)
    (hΦlow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-Bexp) ≤
        (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ)))
    (hmeas : ∀ N (a : LoopArg (B.L N) 2),
      Measurable (initialEvolvedNorm X E D s t N a))
    (hint : ∀ (p N : ℕ) (a : LoopArg (B.L N) 2),
      MeasureTheory.Integrable (fun ω =>
        |initialEvolvedNorm X E D s t N a ω| ^ (2 * p)) B.P)
    {Env : ℕ → ℝ} (hEnv0 : ∀ N, 0 ≤ Env N)
    (henv : ∀ N (a : LoopArg (B.L N) 2) ω,
      initialEvolvedNorm X E D s t N a ω ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (W : ∀ N, LoopArg (B.L N) 2 → Ω → ℝ)
    (hW1 : ∀ N a ω, W N a ω ≤ 1)
    (hintW : ∀ (p N : ℕ) (a : LoopArg (B.L N) 2),
      MeasureTheory.Integrable (fun ω => W N a ω *
        |initialEvolvedNorm X E D s t N a ω| ^ (2 * p)) B.P) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ a : LoopArg (B.L N) 2,
        ∫ ω, W N a ω * |initialEvolvedNorm X E D s t N a ω| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) *
            ((etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ))) ^ (2 * p)) := by
  have hY0 : ∀ N (a : LoopArg (B.L N) 2) ω,
      0 ≤ initialEvolvedNorm X E D s t N a ω := by
    intro N a ω
    have hR : 0 < etaT E (s N) / etaT E (t N) :=
      Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) (ht1 N)
    have hT : 0 < Step2.tT B E N D (t N) (zdist (B.L N) (a 0 - a 1)) :=
      tailT_pos (by exact_mod_cast B.W_pos N) _
    unfold initialEvolvedNorm
    exact div_nonneg (norm_nonneg _) (mul_pos hT (by positivity)).le
  have hΦ : ∀ N (a : LoopArg (B.L N) 2),
      0 < (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ)) := by
    intro N a
    exact Real.rpow_pos_of_pos
      (Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) (ht1 N)) _
  exact APrimeInit.weightedMomentDom_of_stochDom_of_nonneg hY0 hmeas hint hΦ
    hBexp (by filter_upwards [hΦlow] with N hN a; exact hN)
    hEnv0 hKenv henv hEnvpoly
    (initialEvolvedNorm_stochDom_sharp X hE hs0 hst ht1 hc hB D hD)
    hW1 hintW

/-- Transfer a completed family moment estimate at the order-dependent widened
weight to the order-independent prefix weight.  The family estimate has the
post-summation `N^(δp/2)` exponent, so it cannot be used as the one-step input
of `weightedMoment_of_stepBound_mono`, whose right side is smaller. -/
theorem weightedMoment_of_widened_family {P : Measure Ω} [IsProbabilityMeasure P]
    {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ}
    {W : ℝ → ℕ → ℕ → Ω → ℝ} {Wp : ℕ → ℝ → ℕ → ℕ → Ω → ℝ}
    {δ₀ : ℝ}
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω)
    (hJm : ∀ N u, AEStronglyMeasurable (J N u) P)
    (hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω)
    (hW1 : ∀ δ N k ω, W δ N k ω ≤ 1)
    (hWm : ∀ δ N k, AEStronglyMeasurable (W δ N k) P)
    (hWp0 : ∀ p δ N k ω, 0 ≤ Wp p δ N k ω)
    (hWp1 : ∀ p δ N k ω, Wp p δ N k ω ≤ 1)
    (hWpm : ∀ p δ N k, AEStronglyMeasurable (Wp p δ N k) P)
    (hle : ∀ p δ N k ω, W δ N k ω ≤ Wp p δ N k ω)
    (hfamily : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∫ ω, Wp p δ N k ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) :
    WeightedMoment P J s t mesh (fun _ _ => (1 : ℝ)) (fun _ => 1) δ₀ W := by
  intro δ hδ hδ₀ p
  obtain ⟨C, hC, hCev⟩ := hfamily δ hδ hδ₀ p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCev, eventually_ge_atTop 1] with N hN hN1 k hk
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN1)
  have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNr _
  have hLint : Integrable (fun ω => W δ N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ))
        (J N (cutNetPt s mesh N k) ω)| ^ (2 * p)) P :=
    integrable_weight_mul hθ (hW0 δ N k) (hW1 δ N k) (hWm δ N k)
      (hJ0 N _) (hJm N _) (2 * p)
  have hRint : Integrable (fun ω => Wp p δ N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ))
        (J N (cutNetPt s mesh N k) ω)| ^ (2 * p)) P :=
    integrable_weight_mul hθ (hWp0 p δ N k) (hWp1 p δ N k) (hWpm p δ N k)
      (hJ0 N _) (hJm N _) (2 * p)
  simpa only [mul_one, one_pow] using
    (calc
      ∫ ω, W δ N k ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
          ≤ ∫ ω, Wp p δ N k ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P :=
            integral_mono hLint hRint fun ω =>
              mul_le_mul_of_nonneg_right (hle p δ N k ω) (by positivity)
      _ ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := hN k hk)

/-- Conditional Gaussian slot assembly.  The remaining `hfamily` is the
post-summation widened-weight moment estimate, uniform in the net index after
`δ,p` are fixed.  T280b/T280c give ingredients for it but no concrete model
producer at this type yet. -/
noncomputable def aprimeSlot_of_widened_family (d : Gauss.Dims)
    {E D t₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀)
    (hwindow : ∀ N, s N ≤ t N)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ 1)
    (Ccard : ℝ)
    (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (hfamily : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∫ ω, APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
          (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
          s t mesh δ p N k ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (Gauss.sample d) E D s N
              (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂(Gauss.band d).P
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) :
    APrimeSlotFields.APrimeSlot' (Gauss.sample d) E s t D := by
  letI := (Gauss.band d).isProbabilityMeasure
  let J : ℕ → ℝ → Gauss.Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω
  let W : ℝ → ℕ → ℕ → Gauss.Ω d → ℝ :=
    APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1 J s t mesh
  let Wp : ℕ → ℝ → ℕ → ℕ → Gauss.Ω d → ℝ := fun p δ N k ω =>
    APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N k ω
  have hfields := APrimeWeight.jSnorm_piecewiseW_fields
    (P := (Gauss.band d).P) (Gauss.sample d) E D s t mesh
  have hWm : ∀ δ N k, AEStronglyMeasurable (W δ N k) (Gauss.band d).P := hfields.1
  have hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω := hfields.2.1
  have hW1 : ∀ δ N k ω, W δ N k ω ≤ 1 := hfields.2.2.1
  have hWdom : ∀ δ N k ω,
      ω ∈ prefNet J s mesh (fun N _ => (N : ℝ) ^ (2 * δ) * 1) N k →
        1 ≤ W δ N k ω := hfields.2.2.2
  have hJ0 : ∀ N u ω, 0 ≤ J N u ω := by
    intro N u ω
    exact div_nonneg
      (zero_le_one.trans (Step2Moment.one_le_jS (Gauss.sample d) N u ω))
      (by positivity)
  have hJmeas : ∀ N u, Measurable (J N u) := fun N u =>
    APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D s N u
  have hWp0 : ∀ p δ N k ω, 0 ≤ Wp p δ N k ω := by
    intro p δ N k ω
    exact APrimeWeight.widenedW_nonneg _ _ _ _ _ _ _ _ _ _ ω
  have hWp1 : ∀ p δ N k ω, Wp p δ N k ω ≤ 1 := by
    intro p δ N k ω
    exact APrimeWeight.widenedW_le_one _ _ _ _ _ _ _ _ _ _ ω
  have hWpm : ∀ p δ N k, AEStronglyMeasurable (Wp p δ N k) (Gauss.band d).P := by
    intro p δ N k
    exact APrimeWeight.widenedW_meas _ _ _ _ _ _ hJmeas p δ N k
  have hle : ∀ p δ N k ω, W δ N k ω ≤ Wp p δ N k ω := by
    intro p δ N k ω
    exact APrimeWeight.piecewiseW_le_widenedW (by norm_num) δ p N k ω
  have hmom : WeightedMoment (Gauss.band d).P J s t mesh
      (fun _ _ => (1 : ℝ)) (fun _ => 1) δ₀ W := by
    exact weightedMoment_of_widened_family hJ0
      (fun N u => (hJmeas N u).aestronglyMeasurable)
      hW0 hW1 hWm hWp0 hWp1 hWpm hle hfamily
  have hGood : HighProb (Gauss.band d).P
      (fun N => {ω : Gauss.Ω d | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)}) :=
    Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)
  refine ⟨fun N => {ω : Gauss.Ω d | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)}, ?_, hGood⟩
  exact APrimeSlotFields.aprimeHypOn_jSnorm_event d hE hD ht₀0 ht₀
    hs0 htt hwindow (fun N => Set.Subset.rfl)
    (Gauss.measurableSet_normX_le d) δ₀ hδ₀ mesh hmesh hfine Ccard hcard
    W hWm hW0 hW1 hWdom hmom

/-- Both arithmetic bridges requested by D20 are refuted at their actual quantified
strength.  The first negation holds at every fixed moment order and exponent; the
second refutes multiplication of the two separate eventual scale lower bounds. -/
theorem first_pass_D20_obstructions (δ : ℝ) (p : ℕ) :
    (¬ ∃ C : ℝ, 0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (δ / 2 * (p : ℝ))
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)))) ∧
    (¬ (∀ (R A : ℕ → ℝ),
      (∀ᶠ N : ℕ in Filter.atTop, R N ^ 30 ≤ A N) →
      (∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ 30 ≤ A N) →
      ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ 30 * R N ^ 30 ≤ A N)) := by
  exact ⟨APrimeInit.no_family_absorption_slot δ p,
    APrimeExponents.not_eventually_product_scale_of_separate⟩

/-- A numerical drift budget, even with a nonnegative rate, does not supply
the interval integrability demanded by weighted Minkowski.  The interval
integral is defined as zero when the integrand is not integrable. -/
theorem not_intervalIntegrable_of_drift_budget_alone :
    ¬ ∀ A : ℝ → ℝ,
      (∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ A u) →
      2 * (∫ r in (0 : ℝ)..1, A r) ≤ 0 →
      IntervalIntegrable A volume 0 1 := by
  intro h
  have hnot : ¬ IntervalIntegrable (fun r : ℝ => r⁻¹) volume 0 1 := by
    simp [intervalIntegrable_inv_iff]
  have hnonneg : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ u⁻¹ := by
    intro u hu
    exact inv_nonneg.mpr hu.1
  have hbudget : 2 * (∫ r in (0 : ℝ)..1, r⁻¹) ≤ (0 : ℝ) := by
    rw [intervalIntegral.integral_undef hnot]
    norm_num
  exact hnot (h (fun r => r⁻¹) hnonneg hbudget)

#print axioms RBM.APrimeAssembly.first_pass_D20_obstructions
#print axioms RBM.APrimeAssembly.not_intervalIntegrable_of_drift_budget_alone
#print axioms RBM.APrimeAssembly.norm_initial_Uker_le
#print axioms RBM.APrimeAssembly.initial_evolved_normalized_le_sharp
#print axioms RBM.APrimeAssembly.initialEvolvedNorm_stochDom_sharp
#print axioms RBM.APrimeAssembly.initialEvolvedNorm_stochDom_sharp'
#print axioms RBM.APrimeAssembly.initialEvolvedNorm_weighted_moments
#print axioms RBM.APrimeAssembly.measurable_initialEvolvedNorm_gauss
#print axioms RBM.APrimeAssembly.integrable_initialEvolvedNorm_pow_gauss
#print axioms RBM.APrimeAssembly.eventually_initialEvolvedNorm_le_rpow
#print axioms RBM.APrimeAssembly.momentDom_of_stochDom_of_eventual_envelope
#print axioms RBM.APrimeAssembly.initialEvolvedNorm_momentDom_gauss
#print axioms RBM.APrimeAssembly.initialEvolvedNorm_weighted_moments_gauss
#print axioms RBM.APrimeAssembly.eventually_initial_hinit_gauss
#print axioms RBM.APrimeAssembly.initialEvolvedNorm_momentDom_gauss'
#print axioms RBM.APrimeAssembly.weighted_moments_of_momentDom
#print axioms RBM.APrimeAssembly.eventually_momNormW_le_small_initial_scale
#print axioms RBM.APrimeAssembly.eventually_initial_hinit_gauss'
#print axioms RBM.APrimeAssembly.weightedMoment_of_widened_family
#print axioms RBM.APrimeAssembly.aprimeSlot_of_widened_family

end RBM.APrimeAssembly
