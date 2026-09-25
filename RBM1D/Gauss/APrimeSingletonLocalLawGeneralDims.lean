/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSingletonLocalLaw

/-!
# T1371: arbitrary-dimension deterministic-selector singleton local law

The generic length-two Step-1 estimate, Lemma 4.1, and simultaneous weak-law
event give the sharp entry scale at any deterministic selector chosen before
the eventual cutoff.
-/

namespace RBM.APrimeSingletonLocalLawGeneralDims

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable def selectorQ (d : Dims) (E : ℝ) (s u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (band d).ell N (u N) / (band d).ell N (s N) * ((band d).scale E N (u N))⁻¹

noncomputable def selectorPsi (d : Dims) (E : ℝ) (s u : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (selectorQ d E s u N + (d.W N : ℝ)⁻¹)

theorem selectorQ_nonneg (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    0 ≤ selectorQ d E s u N := by
  have hu0 : 0 ≤ u N := (hs0 N).trans (hu N).1
  have hu1 : u N < 1 := (hu N).2.trans_lt (ht1 N)
  have hr : 1 ≤ (band d).ell N (u N) / (band d).ell N (s N) :=
    Step1.one_le_ell_div (B := band d) (hu N).1 hu1
  have hA : 0 < (band d).scale E N (u N) := (band d).scale_pos' hE N hu0 hu1
  exact mul_nonneg (zero_le_one.trans hr) (inv_nonneg.mpr hA.le)

/-- The all-time squared entry maximum furnished by the actual Step-1 inputs. -/
theorem llMax_sq_stochDom (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    StochDom (P d)
      (fun N (u : TimeIcc s t N) ω =>
        Step1.llMax (sample d) E N (u : ℝ) ω ^ 2)
      (fun N (u : TimeIcc s t N) _ =>
        (band d).ell N (u : ℝ) / (band d).ell N (s N) *
          ((band d).scale E N (u : ℝ))⁻¹ + (d.W N : ℝ)⁻¹) := by
  let κ : ℝ := (2 - |E|) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hEκ : |E| ≤ 2 - κ := by dsimp [κ]; linarith
  let Φ : ∀ N, TimeIcc s t N → ℝ := fun N u =>
    (band d).ell N (u : ℝ) / (band d).ell N (s N) * ((band d).scale E N (u : ℝ))⁻¹
  have hΦ0 : ∀ N (u : TimeIcc s t N), 0 ≤ Φ N u := by
    intro N u
    have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    have hr : 1 ≤ (band d).ell N (u : ℝ) / (band d).ell N (s N) :=
      Step1.one_le_ell_div (B := band d) u.2.1 hu1
    have hA : 0 < (band d).scale E N (u : ℝ) := (band d).scale_pos' hE N hu0 hu1
    exact mul_nonneg (zero_le_one.trans hr) (inv_nonneg.mpr hA.le)
  have h2 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 2 (by norm_num)
  have h2pm := h2.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) =>
      (p.1, Step45.pmData p.2.1 p.2.2))
  have hin : StochDom (P d)
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (Step1.goodEv (sample d) E N p.1).indicator
          (fun ω => ‖(sample d).Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
    refine StochDom.of_le_left
      (ξ' := fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        ‖(sample d).Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖) ?_ ?_
    · intro N p ω
      by_cases hp : ω ∈ Step1.goodEv (sample d) E N p.1
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        exact norm_nonneg _
    · simpa only [Φ, band, Step1.aprioriRhs, Step45.pmData_idx,
        Nat.reduceSub, pow_one] using h2pm
  have hind := hStep.lemma41 Φ hΦ0 hin
  have h58 := Step1.eq58 (sample d) hκ hEκ hB hs0 hst ht1 hreg.1
    hStep.scaling (by norm_num) (hStep.lift 2 (by norm_num))
  have hweak := Step1.weakLaw_highProb (sample d) hE hB hs0 hst ht1
    hreg.1 hc hreg.2 h58 hStep.lemma41 hStep.cont
  have hgood : HighProb (P d) (fun N =>
      {ω | ∀ u : TimeIcc s t N,
        ω ∈ Step1.goodEv (sample d) E N (u : ℝ)}) := by
    refine hweak.mono ?_
    filter_upwards [Step1.eventually_scale_facts (B := band d)
      hE hst ht1 hreg.1 hreg.2, eventually_ge_atTop 1]
      with N hf hN ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA : 0 < (band d).scale E N (u : ℝ) :=
      (band d).scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hA1 : 1 ≤ (band d).scale E N (u : ℝ) :=
      (Real.one_le_rpow hN1 hc.le).trans (hf u).1
    have hpow : ((band d).scale E N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 4) ≤
        ((band d).scale E N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr hA)
        (inv_le_one_of_one_le₀ hA1) (by norm_num)
    exact (hω u).le.trans hpow
  simpa only [Φ, band] using Step1.stochDom_of_indicator hgood hind

/-- The sharp singleton entry law, with the deterministic selector fixed before `N → ∞`. -/
theorem selector_llErr_stochDom (d : Dims) {E c : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    StochDom (P d)
      (fun N (ij : d.Idx N × d.Idx N) ω =>
        (sample d).llErr E N (u N) ω ij)
      (fun N _ _ => selectorPsi d E s u N) := by
  have hraw := llMax_sq_stochDom d hE hs0 hst ht1 hc hreg hB hStep
  have hsel := hraw.precomp_param
    (fun N (_ : d.Idx N × d.Idx N) =>
      (⟨u N, (hu N).1, (hu N).2⟩ : TimeIcc s t N))
  have hsqrt := StochDom.sqrt_of
    (fun N (_ : d.Idx N × d.Idx N) ω =>
      sq_nonneg (Step1.llMax (sample d) E N (u N) ω))
    (fun N (_ : d.Idx N × d.Idx N) _ =>
      add_nonneg (selectorQ_nonneg d hE hs0 ht1 hu N)
        (inv_nonneg.mpr (Nat.cast_nonneg _))) hsel
  refine StochDom.of_le_left
    (ξ' := fun N (_ : d.Idx N × d.Idx N) ω =>
      Real.sqrt (Step1.llMax (sample d) E N (u N) ω ^ 2)) ?_ ?_
  · intro N ij ω
    calc
      (sample d).llErr E N (u N) ω ij ≤
          Step1.llMax (sample d) E N (u N) ω :=
        Step1.llErr_le_llMax (sample d) N (u N) ω ij
      _ = Real.sqrt (Step1.llMax (sample d) E N (u N) ω ^ 2) :=
        (Real.sqrt_sq (Step1.llMax_nonneg (sample d) N (u N) ω)).symm
  · simpa only [selectorPsi, selectorQ] using hsqrt

theorem W_inv_le_selectorQ (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    (d.W N : ℝ)⁻¹ ≤ selectorQ d E s u N := by
  have hu0 : 0 ≤ u N := (hs0 N).trans (hu N).1
  have hu1 : u N < 1 := (hu N).2.trans_lt (ht1 N)
  have hbase := Step1.inv_W_le_inv_scale (B := band d) hE N hu0 hu1
  have hr : 1 ≤ (band d).ell N (u N) / (band d).ell N (s N) :=
    Step1.one_le_ell_div (B := band d) (hu N).1 hu1
  have hAi : 0 ≤ ((band d).scale E N (u N))⁻¹ :=
    inv_nonneg.mpr ((band d).scale_nonneg E N hu1.le)
  unfold selectorQ
  exact hbase.trans (by nlinarith [mul_le_mul_of_nonneg_right hr hAi])

theorem W_inv_sqrt_le_selectorPsi (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    Real.sqrt ((d.W N : ℝ)⁻¹) ≤ selectorPsi d E s u N := by
  unfold selectorPsi
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (selectorQ_nonneg d hE hs0 ht1 hu N))

theorem W_rpow_neg_half_le_selectorPsi (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    (d.W N : ℝ) ^ (-(1 : ℝ) / 2) ≤ selectorPsi d E s u N := by
  have hW : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have heq : (d.W N : ℝ) ^ (-(1 : ℝ) / 2) =
      Real.sqrt ((d.W N : ℝ)⁻¹) := by
    calc
      (d.W N : ℝ) ^ (-(1 : ℝ) / 2) =
          (d.W N : ℝ) ^ (-((1 : ℝ) / 2)) := by congr 1; ring
      _ = ((d.W N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := Real.rpow_neg hW _
      _ = ((d.W N : ℝ)⁻¹) ^ ((1 : ℝ) / 2) :=
        (Real.inv_rpow hW _).symm
      _ = Real.sqrt ((d.W N : ℝ)⁻¹) := (Real.sqrt_eq_rpow _).symm
  rw [heq]
  exact W_inv_sqrt_le_selectorPsi d hE hs0 ht1 hu N

/-- The exact `59c/60` decay of the squared sharp scale. -/
theorem eventually_selectorQ_le (d : Dims) {E c : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      selectorQ d E s u N ≤ (N : ℝ) ^ (-(59 * c / 60)) := by
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
  have hA : 0 < (band d).scale E N (u N) := (band d).scale_pos' hE N hu0 hu1
  have hNp : 0 < (N : ℝ) ^ e := Real.rpow_pos_of_pos hNr _
  have hℓs : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat ((band d).L N) (s N : ℂ) by linarith)
  have hell := Step3.ellHat_le_sqrt_mul
    (L := (band d).L N) (s := s N) (t := u N) (hu N).1 hu1
  have hr : (band d).ell N (u N) / (band d).ell N (s N) ≤
      Real.sqrt (etaT E (s N) / etaT E (u N)) := by
    rw [etaT_div_etaT hE]
    apply (div_le_iff₀ hℓs).2
    simpa only [Band.ell] using hell
  have hmain : (N : ℝ) ^ e * ((band d).ell N (u N) / (band d).ell N (s N)) ≤
      (band d).scale E N (u N) := by
    calc
      (N : ℝ) ^ e * ((band d).ell N (u N) / (band d).ell N (s N)) ≤
          (N : ℝ) ^ e * Real.sqrt (etaT E (s N) / etaT E (u N)) :=
        mul_le_mul_of_nonneg_left hr hNp.le
      _ = (N : ℝ) ^ e *
          (etaT E (s N) / etaT E (u N)) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
      _ ≤ (band d).scale E N (u N) := by
        simpa only [uu, Real.rpow_one] using hmN uu
  have hrdiv : (band d).ell N (u N) / (band d).ell N (s N) ≤
      (band d).scale E N (u N) / (N : ℝ) ^ e := by
    apply (le_div_iff₀ hNp).2
    simpa only [mul_comm] using hmain
  calc
    selectorQ d E s u N =
        ((band d).ell N (u N) / (band d).ell N (s N)) / (band d).scale E N (u N) := by
      simp only [selectorQ, div_eq_mul_inv]
    _ ≤ ((band d).scale E N (u N) / (N : ℝ) ^ e) / (band d).scale E N (u N) :=
      div_le_div_of_nonneg_right hrdiv hA.le
    _ = ((N : ℝ) ^ e)⁻¹ := by field_simp
    _ = (N : ℝ) ^ (-e) := by rw [Real.rpow_neg hNr.le]
    _ = (N : ℝ) ^ (-(59 * c / 60)) := by rfl

/-- Every exponent strictly below `59c/120` is an eventual upper exponent for `Ψ`. -/
theorem eventually_selectorPsi_le (d : Dims) {E c a : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (_ha0 : 0 < a) (ha : a < 59 * c / 120) :
    ∀ᶠ N : ℕ in atTop,
      selectorPsi d E s u N ≤ (N : ℝ) ^ (-a) := by
  let e : ℝ := 59 * c / 60
  have hgap : 0 < e - 2 * a := by dsimp [e]; linarith
  filter_upwards [eventually_selectorQ_le d hE hs0 hst ht1 hu hc hreg,
    eventually_le_rpow 2 hgap, eventually_ge_atTop 1]
    with N hq hpow hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hq0 := selectorQ_nonneg d hE hs0 ht1 hu N
  have hwq := W_inv_le_selectorQ d hE hs0 ht1 hu N
  have hsum : selectorQ d E s u N + (d.W N : ℝ)⁻¹ ≤
      2 * (N : ℝ) ^ (-e) := by
    have hq' : selectorQ d E s u N ≤ (N : ℝ) ^ (-e) := by
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
    Real.sqrt (selectorQ d E s u N + (d.W N : ℝ)⁻¹) ≤
        Real.sqrt (2 * (N : ℝ) ^ (-e)) := Real.sqrt_le_sqrt hsum
    _ ≤ Real.sqrt (((N : ℝ) ^ (-a)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (N : ℝ) ^ (-a) := Real.sqrt_sq (Real.rpow_nonneg hNr.le _)

/-- T488's moving spectral floor, specialized to the deterministic selector. -/
theorem eventually_selector_eta_floor (d : Dims) {E c : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (_hs0 : ∀ N, 0 ≤ s N)
    (_hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT E (u N) := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_ge
    (band d) hE ht1 hc hreg.2
  filter_upwards [hfloor,
    eventually_le_rpow ((mE E).im)⁻¹ (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with N hfloorN hmN hN
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hNinv_m : (N : ℝ)⁻¹ ≤ (mE E).im := by
    exact (inv_le_comm₀ hm hNr).mp (by simpa only [Real.rpow_one] using hmN)
  have hNinv_t : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloorN
  have hNinv_u : (N : ℝ)⁻¹ ≤ 1 - u N := by
    linarith [hu N |>.2]
  have hmul : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ (1 - u N) * (mE E).im := by
    nlinarith [mul_le_mul hNinv_u hNinv_m hNinv (by linarith [ht1 N, hu N |>.2])]
  rw [etaT]
  calc
    (N : ℝ) ^ (-(2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      rw [Real.rpow_neg hNr.le, Real.rpow_two]
      simpa only [pow_two] using (inv_pow (N : ℝ) 2).symm
    _ ≤ (1 - u N) * (mE E).im := hmul

/-- Complete deterministic-selector package. -/
theorem general_moving_singleton_localLaw (d : Dims) {E c a : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t)
    (ha0 : 0 < a) (ha : a < 59 * c / 120) :
    StochDom (P d)
        (fun N (ij : d.Idx N × d.Idx N) ω =>
          (sample d).llErr E N (u N) ω ij)
        (fun N _ _ => selectorPsi d E s u N) ∧
      (∀ N, (d.W N : ℝ) ^ (-(1 : ℝ) / 2) ≤ selectorPsi d E s u N) ∧
      (∀ᶠ N : ℕ in atTop,
        selectorPsi d E s u N ≤ (N : ℝ) ^ (-a)) ∧
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT E (u N) := by
  exact ⟨selector_llErr_stochDom d hE hs0 hst ht1 hu hc hreg hB hStep,
    W_rpow_neg_half_le_selectorPsi d hE hs0 ht1 hu,
    eventually_selectorPsi_le d hE hs0 hst ht1 hu hc hreg ha0 ha,
    eventually_selector_eta_floor d hE hs0 hst ht1 hu hc hreg⟩

/-- The generic selectors specialize definitionally to the accepted fixed example. -/
@[simp] theorem selectorQ_exampleGrow {E : ℝ} {s u : ℕ → ℝ} (N : ℕ) :
    selectorQ Dims.exampleGrow E s u N =
      APrimeGeneralMovingSingletonLocalLaw.selectorQ E s u N := rfl

@[simp] theorem selectorPsi_exampleGrow {E : ℝ} {s u : ℕ → ℝ} (N : ℕ) :
    selectorPsi Dims.exampleGrow E s u N =
      APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N := rfl

/-- The arbitrary-dimension producer recovers the accepted `exampleGrow` package verbatim. -/
theorem general_moving_singleton_localLaw_exampleGrow {E c a : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c)
    (hreg : Cond272Reg (band Dims.exampleGrow) E s t c)
    (hB : BoundsCore (sample Dims.exampleGrow) E s)
    (hStep : Step1.Hyp (sample Dims.exampleGrow) E s t)
    (ha0 : 0 < a) (ha : a < 59 * c / 120) :
    StochDom (P Dims.exampleGrow)
        (fun N (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) ω =>
          (sample Dims.exampleGrow).llErr E N (u N) ω ij)
        (fun N _ _ => APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N) ∧
      (∀ N, (Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 2) ≤
        APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N) ∧
      (∀ᶠ N : ℕ in atTop,
        APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N ≤ (N : ℝ) ^ (-a)) ∧
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT E (u N) := by
  have h := general_moving_singleton_localLaw Dims.exampleGrow
    hE hs0 hst ht1 hu hc hreg hB hStep ha0 ha
  simpa only [selectorPsi_exampleGrow] using h

#print axioms selectorQ_nonneg
#print axioms llMax_sq_stochDom
#print axioms selector_llErr_stochDom
#print axioms W_inv_le_selectorQ
#print axioms W_inv_sqrt_le_selectorPsi
#print axioms W_rpow_neg_half_le_selectorPsi
#print axioms eventually_selectorQ_le
#print axioms eventually_selectorPsi_le
#print axioms eventually_selector_eta_floor
#print axioms general_moving_singleton_localLaw
#print axioms selectorQ_exampleGrow
#print axioms selectorPsi_exampleGrow
#print axioms general_moving_singleton_localLaw_exampleGrow

end
end RBM.APrimeSingletonLocalLawGeneralDims
