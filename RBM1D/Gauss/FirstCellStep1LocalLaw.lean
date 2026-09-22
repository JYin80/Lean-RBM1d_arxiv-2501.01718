/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FirstCellLocalLawBridge
import RBM1D.Flow.Step1Producer

/-!
# The sharp first-cell local law from Step 1

The length-two Step 1 loop estimate and Lemma 4.1 give the sharp first-cell
Green-entry scale. The time-uniform weak-law event removes the indicator.
-/

namespace RBM.Gauss

open Filter MeasureTheory

private theorem firstCell_phi_le_two_invW {τ' : ℝ} (N : ℕ)
    (u : TimeIcc (firstCellS τ') (firstCellT τ') N) :
    (band Dims.exampleGrow).ell N (u : ℝ) /
        (band Dims.exampleGrow).ell N (firstCellS τ' N) *
        ((band Dims.exampleGrow).scale 0 N (u : ℝ))⁻¹ ≤
      2 * ((Dims.exampleGrow.W N : ℝ))⁻¹ := by
  let d := Dims.exampleGrow
  let B := band d
  have hs : firstCellS τ' N = 0 := by
    unfold firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hu0 : 0 ≤ (u : ℝ) := by linarith [u.2.1]
  have hu2 : (u : ℝ) ≤ 1 / 2 := by
    apply u.2.2.trans
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
    exact gridT_le (1 / 2 : ℝ) 1
  have hu1 : (u : ℝ) < 1 := by linarith
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hℓ : 0 < B.ell N (u : ℝ) := by
    have h := one_le_ellHat (B.L N) hL hu0 hu1
    change 1 ≤ B.ell N (u : ℝ) at h
    linarith
  have hℓ0 : B.ell N (firstCellS τ' N) = 1 := by
    rw [hs]
    exact ellHat_zero (B.L N) hL
  have hη : etaT 0 (u : ℝ) = 1 - (u : ℝ) := by
    have htwo : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp [etaT, mE_im, htwo]
  have hηhalf : 1 / 2 ≤ etaT 0 (u : ℝ) := by rw [hη]; linarith
  have hηpos : 0 < etaT 0 (u : ℝ) := by linarith
  have hηinv : (etaT 0 (u : ℝ))⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hηpos]
    linarith
  have hW : 0 < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) ≤ (B.W N : ℝ)⁻¹ := inv_nonneg.mpr hW.le
  change B.ell N (u : ℝ) / B.ell N (firstCellS τ' N) *
      (B.scale 0 N (u : ℝ))⁻¹ ≤ 2 * (B.W N : ℝ)⁻¹
  rw [hℓ0, div_one]
  change B.ell N (u : ℝ) *
      ((B.W N : ℝ) * B.ell N (u : ℝ) * etaT 0 (u : ℝ))⁻¹ ≤
    2 * (B.W N : ℝ)⁻¹
  calc
    B.ell N (u : ℝ) *
        ((B.W N : ℝ) * B.ell N (u : ℝ) * etaT 0 (u : ℝ))⁻¹ =
        (B.W N : ℝ)⁻¹ * (etaT 0 (u : ℝ))⁻¹ := by
          field_simp
    _ ≤ (B.W N : ℝ)⁻¹ * 2 := mul_le_mul_of_nonneg_left hηinv hW0
    _ = 2 * (B.W N : ℝ)⁻¹ := by ring

private theorem firstCell_llMax_sq_stochDom {τ' c : ℝ} (hc0 : 0 < c)
    (hB : BoundsCore (sample Dims.exampleGrow) 0 (firstCellS τ'))
    (hs0 : ∀ N, 0 ≤ firstCellS τ' N)
    (hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N)
    (ht1 : ∀ N, firstCellT τ' N < 1)
    (hc : Cond272 (band Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ'))
    (hreg : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ c ≤ (band Dims.exampleGrow).scale 0 N (firstCellT τ' N))
    (h1 : Step1.Hyp (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ')) :
    StochDom (band Dims.exampleGrow).P
      (fun N (u : TimeIcc (firstCellS τ') (firstCellT τ') N) ω =>
        Step1.llMax (sample Dims.exampleGrow) 0 N (u : ℝ) ω ^ 2)
      (fun N (u : TimeIcc (firstCellS τ') (firstCellT τ') N) _ =>
        (band Dims.exampleGrow).ell N (u : ℝ) /
          (band Dims.exampleGrow).ell N (firstCellS τ' N) *
            ((band Dims.exampleGrow).scale 0 N (u : ℝ))⁻¹ +
          (Dims.exampleGrow.W N : ℝ)⁻¹) := by
  let d := Dims.exampleGrow
  let B := band d
  let X := sample d
  let s := firstCellS τ'
  let t := firstCellT τ'
  let Φ : ∀ N, TimeIcc s t N → ℝ := fun N u =>
    B.ell N (u : ℝ) / B.ell N (s N) * (B.scale 0 N (u : ℝ))⁻¹
  have hΦ0 : ∀ N (u : TimeIcc s t N), 0 ≤ Φ N u := by
    intro N u
    have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    have hℓ : 0 ≤ B.ell N (u : ℝ) :=
      (one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1).trans' (by norm_num)
    have hℓs : 0 ≤ B.ell N (s N) := by
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      exact (one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1).trans' (by norm_num)
    have hA : 0 ≤ B.scale 0 N (u : ℝ) := B.scale_nonneg 0 N hu1.le
    exact mul_nonneg (div_nonneg hℓ hℓs) (inv_nonneg.mpr hA)
  have h2 := Step1.apriori X (κ := 1) (by norm_num) (by norm_num)
    hB hs0 hst ht1 hc hc0 hreg h1 2 (by norm_num)
  have h2pm := h2.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      (p.1, Step45.pmData p.2.1 p.2.2))
  have hin : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (Step1.goodEv X 0 N p.1).indicator
          (fun ω => ‖X.Lval 0 N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
    refine StochDom.of_le_left
      (ξ' := fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        ‖X.Lval 0 N p.1 ω (pmLoop p.2.1 p.2.2)‖) ?_ ?_
    · intro N p ω
      by_cases hp : ω ∈ Step1.goodEv X 0 N p.1
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        exact norm_nonneg _
    · simpa only [Φ, Step1.aprioriRhs, Step45.pmData_idx, Nat.reduceSub, pow_one]
        using h2pm
  have hind := h1.lemma41 Φ hΦ0 hin
  have h58 := Step1.eq58 X (κ := 1) (by norm_num) (by norm_num)
    hB hs0 hst ht1 hc h1.scaling (by norm_num) (h1.lift 2 (by norm_num))
  have hweak := Step1.weakLaw_highProb X (by norm_num : |(0 : ℝ)| < 2)
    hB hs0 hst ht1 hc hc0 hreg h58 h1.lemma41 h1.cont
  have hgood : HighProb B.P (fun N =>
      {ω | ∀ u : TimeIcc s t N, ω ∈ Step1.goodEv X 0 N (u : ℝ)}) := by
    refine hweak.mono ?_
    filter_upwards [Step1.eventually_scale_facts (B := B)
      (by norm_num : |(0 : ℝ)| < 2) hst ht1 hc hreg,
      eventually_ge_atTop 1] with N hf hN ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA : 0 < B.scale 0 N (u : ℝ) :=
      B.scale_pos' (by norm_num : |(0 : ℝ)| < 2) N
        ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hA1 : 1 ≤ B.scale 0 N (u : ℝ) :=
      (Real.one_le_rpow hN1 hc0.le).trans (hf u).1
    have hpow : (B.scale 0 N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 4) ≤
        (B.scale 0 N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr hA)
        (inv_le_one_of_one_le₀ hA1) (by norm_num)
    exact (hω u).le.trans hpow
  simpa only [s, t, B, d, X, Φ, band] using Step1.stochDom_of_indicator hgood hind

private theorem firstCell_invW_eq_four_psi_sq (N : ℕ) :
    ((Dims.exampleGrow.W N : ℝ))⁻¹ = 4 * firstCellPsi N ^ 2 := by
  have hW : 0 ≤ (Dims.exampleGrow.W N : ℝ) := Nat.cast_nonneg _
  have hp : ((Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 =
      ((Dims.exampleGrow.W N : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
    norm_num only [mul_div_cancel_left₀, mul_one]
    rw [Real.rpow_neg hW, Real.rpow_one]
  unfold firstCellPsi
  rw [div_pow, hp]
  ring

private theorem firstCell_localLawUnifIcc_of_llMax_sq {τ' : ℝ}
    (hraw : StochDom (band Dims.exampleGrow).P
      (fun N (u : TimeIcc (firstCellS τ') (firstCellT τ') N) ω =>
        Step1.llMax (sample Dims.exampleGrow) 0 N (u : ℝ) ω ^ 2)
      (fun N (u : TimeIcc (firstCellS τ') (firstCellT τ') N) _ =>
        (band Dims.exampleGrow).ell N (u : ℝ) /
          (band Dims.exampleGrow).ell N (firstCellS τ' N) *
            ((band Dims.exampleGrow).scale 0 N (u : ℝ))⁻¹ +
          (Dims.exampleGrow.W N : ℝ)⁻¹)) :
    LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi := by
  let d := Dims.exampleGrow
  let B := band d
  let X := sample d
  let s := firstCellS τ'
  let t := firstCellT τ'
  have hidx := hraw.precomp_param
    (fun N (p : TimeIcc s t N × (d.Idx N × d.Idx N)) => p.1)
  have hgreen : StochDom B.P
      (fun N (p : TimeIcc s t N × (d.Idx N × d.Idx N)) ω =>
        ‖green (Hflow d N (p.1 : ℝ) ω) (zt 0 (p.1 : ℝ)) p.2.1 p.2.2 -
          (if p.2.1 = p.2.2 then mE 0 else 0)‖)
      (fun N _ _ => firstCellPsi N) := by
    refine StochDom.of_subset hidx ?_
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    filter_upwards [eventually_le_rpow 12 hε] with N hN
    intro ω hω
    obtain ⟨p, hp⟩ := hω
    refine ⟨p, ?_⟩
    let R : ℝ := (N : ℝ) ^ ε
    let ψ : ℝ := firstCellPsi N
    let M : ℝ := Step1.llMax X 0 N (p.1 : ℝ) ω
    let ζ : ℝ := B.ell N (p.1 : ℝ) / B.ell N (s N) *
      (B.scale 0 N (p.1 : ℝ))⁻¹ + (d.W N : ℝ)⁻¹
    have hR : 12 ≤ R := hN
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    have hψ0 : 0 ≤ ψ := by
      dsimp [ψ, firstCellPsi]
      have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
      positivity
    have hφ := firstCell_phi_le_two_invW N p.1
    have hφ' : B.ell N (p.1 : ℝ) / B.ell N (s N) *
        (B.scale 0 N (p.1 : ℝ))⁻¹ ≤ 2 * (d.W N : ℝ)⁻¹ := by
      simpa only [B, d, s, band] using hφ
    have hWpsi' : (d.W N : ℝ)⁻¹ = 4 * ψ ^ 2 := by
      simpa only [d, ψ] using firstCell_invW_eq_four_psi_sq N
    have hζle : ζ ≤ 12 * ψ ^ 2 := by
      dsimp only [ζ]
      linarith
    have hRcoef : R * 12 ≤ R ^ 2 := by nlinarith
    have hthreshold : R * ζ ≤ (R * ψ) ^ 2 := by
      calc
        R * ζ ≤ R * (12 * ψ ^ 2) := mul_le_mul_of_nonneg_left hζle hR0
        _ = (R * 12) * ψ ^ 2 := by ring
        _ ≤ R ^ 2 * ψ ^ 2 := mul_le_mul_of_nonneg_right hRcoef (sq_nonneg ψ)
        _ = (R * ψ) ^ 2 := by ring
    have hentry : X.llErr 0 N (p.1 : ℝ) ω p.2 ≤ M :=
      Step1.llErr_le_llMax X N (p.1 : ℝ) ω p.2
    have hbad : R * ψ < X.llErr 0 N (p.1 : ℝ) ω p.2 := by
      rw [X.llErr_eq N (p.1 : ℝ) ω p.2]
      convert hp using 1
      simp only [X, Sample.G, sample_H]
      rfl
    have hM0 : 0 ≤ M := Step1.llMax_nonneg X N (p.1 : ℝ) ω
    have hRψ0 : 0 ≤ R * ψ := mul_nonneg hR0 hψ0
    have hsq : (R * ψ) ^ 2 < M ^ 2 := by nlinarith
    change R * ζ < M ^ 2
    exact lt_of_le_of_lt hthreshold hsq
  have hgreen' : StochDom (P d)
      (fun N (p : TimeIcc s t N × (d.Idx N × d.Idx N)) ω =>
        ‖green (Hflow d N (p.1 : ℝ) ω) (zt 0 (p.1 : ℝ)) p.2.1 p.2.2 -
          (if p.2.1 = p.2.2 then mE 0 else 0)‖)
      (fun N _ _ => firstCellPsi N) := by
    simpa only [B, band] using hgreen
  exact unifDomIcc_of_stochDom_timeIcc hgreen'

/-- The actual Step-1 source and sharp entry law share one first-cell grid parameter. -/
theorem firstCell_step1_and_localLaw_same_parameter :
    ∃ τ' : ℝ, 0 < τ' ∧
      Step1.Hyp (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') ∧
      LocalLawUnifIcc Dims.exampleGrow 0
        (firstCellS τ') (firstCellT τ') firstCellPsi := by
  let d := Dims.exampleGrow
  let B := band d
  have hcap : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
    filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop 1] with N hNpow hN
    have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
        ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hNr]
    rw [hEq]
    have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
    norm_num at hInv ⊢
    exact hInv
  obtain ⟨τ', hτ', c, hc0, _n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain B (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  obtain ⟨_, hsteps⟩ := hgrid 0 (by norm_num) (fun _ => (1 / 2 : ℝ))
    (fun _ => by norm_num) hcap
  obtain ⟨hs0, hst, ht1, hcond⟩ := hsteps 0
  change (∀ N, 0 ≤ firstCellS τ' N) at hs0
  change (∀ N, firstCellS τ' N ≤ firstCellT τ' N) at hst
  change (∀ N, firstCellT τ' N < 1) at ht1
  change Cond272Reg B 0 (firstCellS τ') (firstCellT τ') c at hcond
  have hB : BoundsCore (sample d) 0 (firstCellS τ') :=
    (BoundsCore_zero (sample d) (by norm_num : |(0 : ℝ)| ≤ 2)).congr (sample d)
      (Eventually.of_forall fun N => (gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm)
  have h1 : Step1.Hyp (sample d) 0 (firstCellS τ') (firstCellT τ') :=
    step1Hyp_gauss_of_scale'' d (κ := 1) (by norm_num) (by norm_num)
      hB hs0 hst ht1 hcond.1 hc0 hcond.2
  have hraw := firstCell_llMax_sq_stochDom hc0 hB hs0 hst ht1 hcond.1 hcond.2 h1
  exact ⟨τ', hτ', h1, firstCell_localLawUnifIcc_of_llMax_sq hraw⟩

/-- The unchanged first-cell local-law interface. -/
theorem firstCell_localLawUnifIcc_of_step1 :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0
        (firstCellS τ') (firstCellT τ') firstCellPsi := by
  obtain ⟨τ', hτ', _, hll⟩ := firstCell_step1_and_localLaw_same_parameter
  exact ⟨τ', hτ', hll⟩

/-- The same Gaussian first cell has positive duration and one inhabited flow good event. -/
theorem firstCell_step1_localLaw_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0
        (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      ∀ᶠ N : ℕ in atTop,
        firstCellS τ' N < firstCellT τ' N ∧
          (flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
            firstCellDelta N).Nonempty := by
  obtain ⟨τ', hτ', hll⟩ := firstCell_localLawUnifIcc_of_step1
  exact ⟨τ', hτ', hll, first_cell_flowNetEvent_nonempty_of_localLaw hτ' hll⟩

#print axioms firstCell_phi_le_two_invW
#print axioms firstCell_llMax_sq_stochDom
#print axioms firstCell_invW_eq_four_psi_sq
#print axioms firstCell_localLawUnifIcc_of_llMax_sq
#print axioms firstCell_localLawUnifIcc_of_step1
#print axioms firstCell_step1_and_localLaw_same_parameter
#print axioms firstCell_step1_localLaw_witness

end RBM.Gauss
