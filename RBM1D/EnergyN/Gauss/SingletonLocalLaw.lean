/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.SingletonLocalLaw
import RBM1D.EnergyN.Gauss.Step1Hyp
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.EnergyN.Flow.Thm221Bare
import RBM1D.Flow.EnergyUniformReg

/-!
# The local law at a single moving time, at an `N`-dependent energy

Six statements at an `N`-dependent energy `E : ℕ → ℝ`: the bound on `llMax²`
(`RBM.SingletonLocalLaw.llMax_sq_stochDomN`), the entrywise local law at a time `u N ∈ [s, t]`
with the control `selectorPsi` (`RBM.SingletonLocalLaw.selector_llErr_stochDomN`), the smallness
of `selectorQ` and `selectorPsi` (`RBM.SingletonLocalLaw.eventually_selectorQ_leN`,
`RBM.SingletonLocalLaw.eventually_selectorPsi_leN`), the floor `N^{-2} ≤ η_u`
(`RBM.SingletonLocalLaw.eventually_selector_eta_floorN`), and their combination
(`RBM.SingletonLocalLaw.general_moving_singleton_localLawN`).

## The external `κ`

`llMax_sq_stochDomN` takes an external `κ` (`hE : ∀ N, |E N| ≤ 2 - κ`), passed directly into
`Step1.aprioriN`/`.eq58N` (both take that exact shape). `eventually_selector_eta_floorN` needs
a bound on `(mE (E N)).im⁻¹` that does not depend on `N`; it uses the uniform `mκ⁻¹`,
`mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N` (`κ' := min κ 1`, `mE_im_ge`; same pattern as
in `CenteredTraceModulus.lean`). `selector_llErr_stochDomN` takes `κ` only through
`llMax_sq_stochDomN`; `general_moving_singleton_localLawN` takes `κ` through both
`llMax_sq_stochDomN` and `eventually_selector_eta_floorN`.
`eventually_selectorQ_leN`/`.eventually_selectorPsi_leN` need no `κ`: they only use
`Cond272NReg.margin` at plain `hE : ∀ N, |E N| < 2`.
-/

namespace RBM.SingletonLocalLaw

open Filter MeasureTheory Set Gauss

noncomputable section

/-- **`llMax_u² ≺ (ℓ_u/ℓ_s) (W ℓ_u η_u)^{-1} + W⁻¹`** uniformly in `u ∈ [s, t]`, from (2.68)–(2.70)
at `s`, the regime condition and the hypotheses of Step 1. The margin is the external `κ` of
`hE`. -/
theorem llMax_sq_stochDomN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s) (hStep : Step1.HypN (sample d) E s t) :
    StochDom (P d)
      (fun N (u : TimeIcc s t N) ω => Step1.llMax (sample d) (E N) N (u : ℝ) ω ^ 2)
      (fun N (u : TimeIcc s t N) _ =>
        (band d).ell N (u : ℝ) / (band d).ell N (s N) *
          ((band d).scale (E N) N (u : ℝ))⁻¹ + (d.W N : ℝ)⁻¹) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  let Φ : ∀ N, TimeIcc s t N → ℝ := fun N u =>
    (band d).ell N (u : ℝ) / (band d).ell N (s N) * ((band d).scale (E N) N (u : ℝ))⁻¹
  have hΦ0 : ∀ N (u : TimeIcc s t N), 0 ≤ Φ N u := by
    intro N u
    have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    have hr : 1 ≤ (band d).ell N (u : ℝ) / (band d).ell N (s N) :=
      Step1.one_le_ell_div (B := band d) u.2.1 hu1
    have hA : 0 < (band d).scale (E N) N (u : ℝ) := (band d).scale_pos' (hE2 N) N hu0 hu1
    exact mul_nonneg (zero_le_one.trans hr) (inv_nonneg.mpr hA.le)
  have h2 := Step1.aprioriN (sample d) hκ0 hE hB hs0 hst ht1 hreg.1 hc hreg.2 hStep 2
    (by norm_num)
  have h2pm := h2.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) =>
      (p.1, Step45.pmData p.2.1 p.2.2))
  have hin : StochDom (P d)
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (Step1.goodEv (sample d) (E N) N p.1).indicator
          (fun ω => ‖(sample d).Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
    refine StochDom.of_le_left
      (ξ' := fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        ‖(sample d).Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2)‖) ?_ ?_
    · intro N p ω
      by_cases hp : ω ∈ Step1.goodEv (sample d) (E N) N p.1
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        exact norm_nonneg _
    · simpa only [Φ, band, Step1.aprioriRhs, Step45.pmData_idx,
        Nat.reduceSub, pow_one] using h2pm
  have hind := hStep.lemma41 Φ hΦ0 hin
  have h58 := Step1.eq58N (sample d) hκ0 hE hB hs0 hst ht1 hreg.1
    hStep.scaling (by norm_num) (hStep.lift 2 (by norm_num))
  have hweak := Step1.weakLaw_highProbN (sample d) hE2 hB hs0 hst ht1
    hreg.1 hc hreg.2 h58 hStep.lemma41 hStep.cont
  have hgood : HighProb (P d) (fun N =>
      {ω | ∀ u : TimeIcc s t N,
        ω ∈ Step1.goodEv (sample d) (E N) N (u : ℝ)}) := by
    refine hweak.mono ?_
    filter_upwards [Step1.eventually_scale_factsN (B := band d)
      hE2 hst ht1 hreg.1 hreg.2, eventually_ge_atTop 1]
      with N hf hN ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA : 0 < (band d).scale (E N) N (u : ℝ) :=
      (band d).scale_pos' (hE2 N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hA1 : 1 ≤ (band d).scale (E N) N (u : ℝ) :=
      (Real.one_le_rpow hN1 hc.le).trans (hf u).1
    have hpow : ((band d).scale (E N) N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 4) ≤
        ((band d).scale (E N) N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr hA)
        (inv_le_one_of_one_le₀ hA1) (by norm_num)
    exact (hω u).le.trans hpow
  simpa only [Φ, band] using Step1.stochDom_of_indicator hgood hind

/-- **The entrywise local law `llErr ≺ selectorPsi` at the time `u N ∈ [s N, t N]`.** It takes the
external `κ` through `llMax_sq_stochDomN`. -/
theorem selector_llErr_stochDomN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t u : ℕ → ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    StochDom (P d)
      (fun N (ij : d.Idx N × d.Idx N) ω =>
        (sample d).llErr (E N) N (u N) ω ij)
      (fun N _ _ => selectorPsi d (E N) s u N) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hraw := llMax_sq_stochDomN d hκ0 hE hs0 hst ht1 hc hreg hB hStep
  have hsel := hraw.precomp_param
    (fun N (_ : d.Idx N × d.Idx N) =>
      (⟨u N, (hu N).1, (hu N).2⟩ : TimeIcc s t N))
  have hsqrt := StochDom.sqrt_of
    (fun N (_ : d.Idx N × d.Idx N) ω =>
      sq_nonneg (Step1.llMax (sample d) (E N) N (u N) ω))
    (fun N (_ : d.Idx N × d.Idx N) _ =>
      add_nonneg (selectorQ_nonneg d (hE2 N) hs0 ht1 hu N)
        (inv_nonneg.mpr (Nat.cast_nonneg _))) hsel
  refine StochDom.of_le_left
    (ξ' := fun N (_ : d.Idx N × d.Idx N) ω =>
      Real.sqrt (Step1.llMax (sample d) (E N) N (u N) ω ^ 2)) ?_ ?_
  · intro N ij ω
    calc
      (sample d).llErr (E N) N (u N) ω ij ≤
          Step1.llMax (sample d) (E N) N (u N) ω :=
        Step1.llErr_le_llMax (sample d) N (u N) ω ij
      _ = Real.sqrt (Step1.llMax (sample d) (E N) N (u N) ω ^ 2) :=
        (Real.sqrt_sq (Step1.llMax_nonneg (sample d) N (u N) ω)).symm
  · simpa only [selectorPsi, selectorQ] using hsqrt

/-- **`selectorQ ≤ N^{-59c/60}` eventually.** No energy-dependent constant is fixed here (it only
uses `Cond272NReg.margin` at plain `hE : ∀ N, |E N| < 2`). -/
theorem eventually_selectorQ_leN (d : Dims) {E : ℕ → ℝ} {c : ℝ} {s t u : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      selectorQ d (E N) s u N ≤ (N : ℝ) ^ (-(59 * c / 60)) := by
  let e : ℝ := 59 * c / 60
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hsum : e / c + (1 / 2 : ℝ) / 30 ≤ 1 := by
    dsimp [e]
    field_simp [ne_of_gt hc]
    norm_num
  have hm := hreg.margin hE hst ht1 hc (e := e) (b := (1 : ℝ) / 2)
    (a := 1) he0 (by norm_num) hsum
  filter_upwards [hm, eventually_ge_atTop 1] with N hmN hN
  let uu : TimeIcc s t N := ⟨u N, (hu N).1, (hu N).2⟩
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hu0 : 0 ≤ u N := (hs0 N).trans (hu N).1
  have hu1 : u N < 1 := (hu N).2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hu N).1.trans_lt hu1
  have hA : 0 < (band d).scale (E N) N (u N) := (band d).scale_pos' (hE N) N hu0 hu1
  have hNp : 0 < (N : ℝ) ^ e := Real.rpow_pos_of_pos hNr _
  have hℓs : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat ((band d).L N) (s N : ℂ) by linarith)
  have hell := Step3.ellHat_le_sqrt_mul
    (L := (band d).L N) (s := s N) (t := u N) (hu N).1 hu1
  have hr : (band d).ell N (u N) / (band d).ell N (s N) ≤
      Real.sqrt (etaT (E N) (s N) / etaT (E N) (u N)) := by
    rw [etaT_div_etaT (hE N)]
    apply (div_le_iff₀ hℓs).2
    simpa only [Band.ell] using hell
  have hmain : (N : ℝ) ^ e * ((band d).ell N (u N) / (band d).ell N (s N)) ≤
      (band d).scale (E N) N (u N) := by
    calc
      (N : ℝ) ^ e * ((band d).ell N (u N) / (band d).ell N (s N)) ≤
          (N : ℝ) ^ e * Real.sqrt (etaT (E N) (s N) / etaT (E N) (u N)) :=
        mul_le_mul_of_nonneg_left hr hNp.le
      _ = (N : ℝ) ^ e *
          (etaT (E N) (s N) / etaT (E N) (u N)) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
      _ ≤ (band d).scale (E N) N (u N) := by
        simpa only [uu, Real.rpow_one] using hmN uu
  have hrdiv : (band d).ell N (u N) / (band d).ell N (s N) ≤
      (band d).scale (E N) N (u N) / (N : ℝ) ^ e := by
    apply (le_div_iff₀ hNp).2
    simpa only [mul_comm] using hmain
  calc
    selectorQ d (E N) s u N =
        ((band d).ell N (u N) / (band d).ell N (s N)) / (band d).scale (E N) N (u N) := by
      simp only [selectorQ, div_eq_mul_inv]
    _ ≤ ((band d).scale (E N) N (u N) / (N : ℝ) ^ e) / (band d).scale (E N) N (u N) :=
      div_le_div_of_nonneg_right hrdiv hA.le
    _ = ((N : ℝ) ^ e)⁻¹ := by field_simp
    _ = (N : ℝ) ^ (-e) := by rw [Real.rpow_neg hNr.le]
    _ = (N : ℝ) ^ (-(59 * c / 60)) := by rfl

/-- **`selectorPsi ≤ N^{-a}` eventually**, for `a < 59c/120`. No energy-dependent constant is fixed
here. -/
theorem eventually_selectorPsi_leN (d : Dims) {E : ℕ → ℝ} {c a : ℝ} {s t u : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (_ha0 : 0 < a) (ha : a < 59 * c / 120) :
    ∀ᶠ N : ℕ in atTop,
      selectorPsi d (E N) s u N ≤ (N : ℝ) ^ (-a) := by
  let e : ℝ := 59 * c / 60
  have hgap : 0 < e - 2 * a := by dsimp [e]; linarith
  filter_upwards [eventually_selectorQ_leN d hE hs0 hst ht1 hu hc hreg,
    eventually_le_rpow 2 hgap, eventually_ge_atTop 1]
    with N hq hpow hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hq0 := selectorQ_nonneg d (hE N) hs0 ht1 hu N
  have hwq := W_inv_le_selectorQ d (hE N) hs0 ht1 hu N
  have hsum : selectorQ d (E N) s u N + (d.W N : ℝ)⁻¹ ≤
      2 * (N : ℝ) ^ (-e) := by
    have hq' : selectorQ d (E N) s u N ≤ (N : ℝ) ^ (-e) := by
      simpa only [e] using hq
    nlinarith
  have hsq : 2 * (N : ℝ) ^ (-e) ≤ ((N : ℝ) ^ (-a)) ^ 2 := by
    calc
      2 * (N : ℝ) ^ (-e) ≤
          (N : ℝ) ^ (e - 2 * a) * (N : ℝ) ^ (-e) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNr.le _)
      _ = ((N : ℝ) ^ (-a)) ^ 2 := by
        rw [pow_two, ← Real.rpow_add hNr, ← Real.rpow_add hNr]
        congr 1
        ring
  unfold selectorPsi
  calc
    Real.sqrt (selectorQ d (E N) s u N + (d.W N : ℝ)⁻¹) ≤
        Real.sqrt (2 * (N : ℝ) ^ (-e)) := Real.sqrt_le_sqrt hsum
    _ ≤ Real.sqrt (((N : ℝ) ^ (-a)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (N : ℝ) ^ (-a) := Real.sqrt_sq (Real.rpow_nonneg hNr.le _)

/-- **`N^{-2} ≤ η_u` eventually.** The constant `(mE (E N)).im⁻¹` is bounded by the uniform
`mκ⁻¹` (same pattern as in `CenteredTraceModulus.lean`). -/
theorem eventually_selector_eta_floorN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t u : ℕ → ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (_hs0 : ∀ N, 0 ≤ s N)
    (_hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT (E N) (u N) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_geN (band d) hE2 ht1 hc hreg.2
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have hmge : ∀ N, Real.sqrt (2 * κ') / 2 ≤ (mE (E N)).im :=
    fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hmpos : 0 < Real.sqrt (2 * κ') / 2 := by positivity
  have hmEN : ∀ N, (mE (E N)).im⁻¹ ≤ (Real.sqrt (2 * κ') / 2)⁻¹ :=
    fun N => inv_anti₀ hmpos (hmge N)
  have hmunif := eventually_le_rpow (Real.sqrt (2 * κ') / 2)⁻¹ (by norm_num : (0 : ℝ) < 1)
  have hm : ∀ᶠ N : ℕ in atTop, (mE (E N)).im⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [hmunif] with N hN
    exact (hmEN N).trans hN
  filter_upwards [hfloor, hm, eventually_ge_atTop 1] with N hfloorN hmN hN
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hm0 : 0 < (mE (E N)).im := mE_im_pos (hE2 N)
  have hNinv_m : (N : ℝ)⁻¹ ≤ (mE (E N)).im := by
    exact (inv_le_comm₀ hm0 hNr).mp (by simpa only [Real.rpow_one] using hmN)
  have hNinv_t : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloorN
  have hNinv_u : (N : ℝ)⁻¹ ≤ 1 - u N := by
    linarith [hu N |>.2]
  have hmul : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ (1 - u N) * (mE (E N)).im := by
    nlinarith [mul_le_mul hNinv_u hNinv_m hNinv (by linarith [ht1 N, hu N |>.2])]
  rw [etaT]
  calc
    (N : ℝ) ^ (-(2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      rw [Real.rpow_neg hNr.le, Real.rpow_two]
      simpa only [pow_two] using (inv_pow (N : ℝ) 2).symm
    _ ≤ (1 - u N) * (mE (E N)).im := hmul

/-- **The local law at a single moving time**: `llErr ≺ selectorPsi` at `u`,
`W^{-1/2} ≤ selectorPsi`, and eventually `selectorPsi ≤ N^{-a}` and `N^{-2} ≤ η_u`. It fixes no
energy-dependent constant itself (it takes the external `κ` through `selector_llErr_stochDomN`
and `eventually_selector_eta_floorN`). -/
theorem general_moving_singleton_localLawN (d : Dims) {E : ℕ → ℝ} {κ c a : ℝ}
    {s t u : ℕ → ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t)
    (ha0 : 0 < a) (ha : a < 59 * c / 120) :
    StochDom (P d)
        (fun N (ij : d.Idx N × d.Idx N) ω =>
          (sample d).llErr (E N) N (u N) ω ij)
        (fun N _ _ => selectorPsi d (E N) s u N) ∧
      (∀ N, (d.W N : ℝ) ^ (-(1 : ℝ) / 2) ≤ selectorPsi d (E N) s u N) ∧
      (∀ᶠ N : ℕ in atTop,
        selectorPsi d (E N) s u N ≤ (N : ℝ) ^ (-a)) ∧
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT (E N) (u N) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  exact ⟨selector_llErr_stochDomN d hκ0 hE hs0 hst ht1 hu hc hreg hB hStep,
    fun N => W_rpow_neg_half_le_selectorPsi d (hE2 N) hs0 ht1 hu N,
    eventually_selectorPsi_leN d hE2 hs0 hst ht1 hu hc hreg ha0 ha,
    eventually_selector_eta_floorN d hκ0 hE hs0 hst ht1 hu hc hreg⟩

section Compat

end Compat

end
end RBM.SingletonLocalLaw
