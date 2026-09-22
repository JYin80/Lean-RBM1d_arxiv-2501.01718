/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellJGCap
import RBM1D.Gauss.APrimeTwoChargeOneLoop
import RBM1D.Gauss.DetAvgIBPFlow

/-!
# First-cell near-`eG` sources on one Gaussian sample
-/

namespace RBM.APrimeFirstCellNearSources

open Filter Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- A bounded deterministic sequence that lies in the T358 interval at every size
and eventually equals the first positive cut-net time. -/
noncomputable def sourceTime (τ' : ℝ) (N : ℕ) : ℝ :=
  min (APrimeFirstCellJGCap.firstTime N) (Gauss.firstCellT τ' N)

theorem sourceTime_mem {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ) :
    sourceTime τ' N ∈ Set.Icc (Gauss.firstCellS τ' N) (Gauss.firstCellT τ' N) := by
  have hs : Gauss.firstCellS τ' N = 0 := by
    unfold Gauss.firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have ht : 0 ≤ Gauss.firstCellT τ' N := by
    change 0 ≤ gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
    rw [← gridT_zero (W := (B.W N : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact gridT_mono (by exact_mod_cast B.one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  constructor
  · rw [hs]
    unfold sourceTime APrimeFirstCellJGCap.firstTime
    exact le_min (by positivity) ht
  · exact min_le_right _ _

theorem sourceTime_lt_one {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ) :
    sourceTime τ' N < 1 := by
  exact (sourceTime_mem hτ' N).2.trans_lt
    ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))

theorem firstCell_localLaw_at_sourceTime {τ' : ℝ}
    (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc d 0 (Gauss.firstCellS τ') (Gauss.firstCellT τ')
      Gauss.firstCellPsi) :
    LocalLawUnifIcc d 0 (sourceTime τ') (sourceTime τ')
      (fun N => 2 * Gauss.firstCellPsi N) := by
  have hsmall : LocalLawUnifIcc d 0 (sourceTime τ') (sourceTime τ')
      Gauss.firstCellPsi := by
    intro ε hε D hD
    filter_upwards [hll ε hε D hD] with N hN v hv ij
    have hu := sourceTime_mem hτ' N
    exact hN v ⟨hu.1.trans hv.1, hv.2.trans hu.2⟩ ij
  exact UnifDomIcc.mono_control hsmall (fun N _ _ _ => by
    have hp : 0 ≤ Gauss.firstCellPsi N := (Gauss.firstCellPsi_pos N).le
    linarith)

private theorem firstCell_right_nonneg {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ) :
    0 ≤ Gauss.firstCellT τ' N := by
  have hu := sourceTime_mem hτ' N
  have hs : Gauss.firstCellS τ' N = 0 := by
    unfold Gauss.firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hmin : 0 ≤ sourceTime τ' N := by rw [← hs]; exact hu.1
  exact hmin.trans hu.2

private theorem firstCell_regime {τ' : ℝ} (hτ' : 0 < τ') :
    ∃ c : ℝ, 0 < c ∧
      Cond272 B 0 (Gauss.firstCellS τ') (Gauss.firstCellT τ') ∧
      (∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ c ≤ B.scale 0 N (Gauss.firstCellT τ' N)) := by
  let t := Gauss.firstCellT τ'
  have ht0 : ∀ N, 0 ≤ t N := firstCell_right_nonneg hτ'
  have htHalf : ∀ N, t N ≤ 1 / 2 := fun N => gridT_le (1 / 2 : ℝ) 1
  have hcap : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - t N := by
    filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop 1] with N hNpow hN
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
        ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hN0]
    rw [hEq]
    have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
    have ht := htHalf N
    norm_num at hInv ⊢
    linarith
  obtain ⟨c, hc0, hregAll⟩ := B.eventually_rpow_le_scale
    (κ := 1) one_pos (by norm_num : (0 : ℝ) < 1 / 2)
  have hreg := hregAll 0 (by norm_num) t ht0 hcap
  have hcond : Cond272 B 0 (Gauss.firstCellS τ') t := by
    have hWlarge := B.eventually_le_W ((2 : ℝ) ^ (31 : ℕ))
    filter_upwards [hWlarge] with N hWN
    have hs : Gauss.firstCellS τ' N = 0 := by
      unfold Gauss.firstCellS
      exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hA : (B.W N : ℝ) / 2 ≤ B.scale 0 N (t N) :=
      Gauss.firstCell_scale_ge_half N ⟨by rw [hs]; exact ht0 N, le_refl _⟩
    have hAmin : (2 : ℝ) ^ (30 : ℕ) ≤ B.scale 0 N (t N) := by
      change (Gauss.Dims.growW N : ℝ) / 2 ≤ B.scale 0 N (t N) at hA
      norm_num at hWN ⊢
      have hWr : (2147483648 : ℝ) ≤ (Gauss.Dims.growW N : ℝ) := by
        exact_mod_cast hWN
      linarith
    have hInv : (B.scale 0 N (t N))⁻¹ ≤ ((2 : ℝ) ^ (30 : ℕ))⁻¹ :=
      inv_anti₀ (by positivity) hAmin
    have hPow : ((2 : ℝ) ^ (30 : ℕ))⁻¹ = ((1 / 2 : ℝ) ^ (30 : ℕ)) := by
      norm_num
    have htLower : (1 / 2 : ℝ) ≤ 1 - t N := by linarith [htHalf N]
    have hPowLe : (1 / 2 : ℝ) ^ (30 : ℕ) ≤ (1 - t N) ^ (30 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) htLower 30
    change (B.scale 0 N (t N))⁻¹ ≤
      ((1 - t N) / (1 - Gauss.firstCellS τ' N)) ^ 30
    rw [hs, sub_zero, div_one]
    exact hInv.trans (hPow ▸ hPowLe)
  exact ⟨c, hc0, hcond, hreg⟩

/-- The `n=3` law is recovered from the Step-1 hypothesis exported with
T358's *same* first-cell parameter. -/
theorem firstCell_raw_three_of_step1 {τ' : ℝ} (hτ' : 0 < τ')
    (h1 : Step1.Hyp (Gauss.sample d) 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ')) :
    Gauss.firstCellRawLoopDom τ' 3 := by
  have hs0 : ∀ N, 0 ≤ Gauss.firstCellS τ' N := fun N => by
    unfold Gauss.firstCellS
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hst : ∀ N, Gauss.firstCellS τ' N ≤ Gauss.firstCellT τ' N :=
    fun N => (sourceTime_mem hτ' N).1.trans (sourceTime_mem hτ' N).2
  have ht1 : ∀ N, Gauss.firstCellT τ' N < 1 := fun N =>
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hB : BoundsCore (Gauss.sample d) 0 (Gauss.firstCellS τ') :=
    (BoundsCore_zero (Gauss.sample d) (by norm_num : |(0 : ℝ)| ≤ 2)).congr
      (Gauss.sample d) (Eventually.of_forall fun N =>
        (gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm)
  obtain ⟨c, hc0, hc, hreg⟩ := firstCell_regime hτ'
  exact Step1.apriori (Gauss.sample d) (κ := 1) (by norm_num) (by norm_num)
    hB hs0 hst ht1 hc hc0 hreg h1 3 (by norm_num)

/-- One T358 witness now supplies the local law and all three raw lengths. -/
theorem firstCell_raw346_localLaw_same_parameter :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc d 0 (sourceTime τ') (sourceTime τ')
        (fun N => 2 * Gauss.firstCellPsi N) ∧
      Gauss.firstCellRawLoopDom τ' 3 ∧
      Gauss.firstCellRawLoopDom τ' 4 ∧
      Gauss.firstCellRawLoopDom τ' 6 := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    Gauss.firstCell_step1_localLaw_raw46_same_parameter
  exact ⟨τ', hτ', firstCell_localLaw_at_sourceTime hτ' hll,
    firstCell_raw_three_of_step1 hτ' h1, h4, h6⟩

theorem eventually_sourceTime_eq_firstTime {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      sourceTime τ' N = APrimeFirstCellJGCap.firstTime N ∧
      0 < sourceTime τ' N := by
  have hWt : Tendsto (fun N : ℕ => ((d.W N : ℝ)) ^ (-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W B)
  have hhalf : ∀ᶠ N : ℕ in atTop, Gauss.firstCellT τ' N = 1 / 2 := by
    filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
      with N hW
    change gridT (B.W N : ℝ) τ' (1 / 2 : ℝ) 1 = 1 / 2
    apply gridT_of_le
    rw [gridS]
    norm_num
    change (d.W N : ℝ) ^ (-τ') < 1 / 2 at hW
    change (Gauss.Dims.growW N : ℝ) ^ (-τ') < 1 / 2 at hW
    linarith
  filter_upwards [hhalf, eventually_ge_atTop 2] with N ht hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (2 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
    calc
      (2 : ℝ) ≤ (N : ℝ) := hNr
      _ ≤ (N : ℝ) ^ (248 : ℕ) := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) (by norm_num : 1 ≤ 248))
  have htime : APrimeFirstCellJGCap.firstTime N ≤ 1 / 2 := by
    unfold APrimeFirstCellJGCap.firstTime
    simpa [one_div] using
      (inv_le_inv₀ (show (0 : ℝ) < (N : ℝ) ^ 248 by positivity)
        (show (0 : ℝ) < 2 by norm_num)).2 hp
  have hpos : 0 < APrimeFirstCellJGCap.firstTime N := by
    unfold APrimeFirstCellJGCap.firstTime
    positivity
  constructor
  · unfold sourceTime
    rw [ht, min_eq_left htime]
  · unfold sourceTime
    rw [ht, min_eq_left htime]
    exact hpos

theorem firstCell_avgOne_stochDom {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc d 0 (sourceTime τ') (sourceTime τ')
      (fun N => 2 * Gauss.firstCellPsi N)) :
    StochDom (Gauss.P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Gauss.Hflow d N (sourceTime τ' N) ω)
          (zt 0 (sourceTime τ' N)) - mE 0 •
            (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => (2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N)) := by
  have hu0 : ∀ N, 0 ≤ sourceTime τ' N := fun N => by
    have hs : Gauss.firstCellS τ' N = 0 := by
      unfold Gauss.firstCellS
      exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← hs]
    exact (sourceTime_mem hτ' N).1
  have hu1 : ∀ N, sourceTime τ' N < 1 := sourceTime_lt_one hτ'
  have hη : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT 0 (sourceTime τ' N) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have ht : sourceTime τ' N ≤ 1 / 2 :=
      (sourceTime_mem hτ' N).2.trans (gridT_le (1 / 2 : ℝ) 1)
    have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 (sourceTime τ' N) := by
      rw [Step2.etaT_eq, mE_zero]
      norm_num
      linarith
    have hInv : (N : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < N)]
      linarith
    rw [Real.rpow_neg_one]
    exact hInv.trans hηhalf
  have hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ 2 * Gauss.firstCellPsi N :=
    Eventually.of_forall fun N => by
      unfold Gauss.firstCellPsi
      convert (le_refl (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2))) using 1
      ring
  have hΨhi : ∀ᶠ N : ℕ in atTop,
      2 * Gauss.firstCellPsi N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) := by
    have hpow : ∀ᶠ N : ℕ in atTop,
        2 * (N : ℝ) ^ (-(1 : ℝ) / 4) ≤
          (N : ℝ) ^ (-(1 : ℝ) / 8) :=
      eventually_const_mul_rpow_le_rpow 2 (by norm_num)
    filter_upwards [Gauss.firstCellPsi_le_rpow_neg_quarter, hpow] with N hΨ hN
    nlinarith
  exact Gauss.detAvgIBP_stochDom_of_localLaw_complete d
    (κ := 1) (a := (1 : ℝ) / 8) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) hu0 hu1
    (by norm_num) (by norm_num) hη hΨlo
    (by simpa only [neg_div] using hΨhi) hll

def rawLoopEvent (τ' ζ : ℝ) (n N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ∀ p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
      LoopData (d.L N) n,
    ‖(Gauss.sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ * Step1.aprioriRhs B 0
        (Gauss.firstCellS τ') (Gauss.firstCellT τ') n N p ω}

def avgOneEvent (τ' ζ : ℝ) (N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ∀ b : ZMod (d.L N),
    ‖Matrix.trace ((green (Gauss.Hflow d N (sourceTime τ' N) ω)
      (zt 0 (sourceTime τ' N)) - mE 0 •
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b)‖ ≤
      (N : ℝ) ^ ζ * ((2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N))}

def jointEvent (τ' ζ₁ ζ₃ : ℝ) (N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)} ∩
    rawLoopEvent τ' ζ₃ 3 N ∩ rawLoopEvent τ' ζ₃ 4 N ∩
    rawLoopEvent τ' ζ₃ 6 N ∩
    Gauss.goodSetFlow d 0 (Gauss.firstCellS τ')
      (Gauss.firstCellT τ') Gauss.firstCellDelta N ∩
    avgOneEvent τ' ζ₁ N

private theorem highProb_firstCell_good {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc d 0 (Gauss.firstCellS τ')
      (Gauss.firstCellT τ') Gauss.firstCellPsi) :
    HighProb (Gauss.P d)
      (Gauss.goodSetFlow d 0 (Gauss.firstCellS τ')
        (Gauss.firstCellT τ') Gauss.firstCellDelta) := by
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, hmargin, _, _, _, _, _, _, _⟩ :=
    Gauss.first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := Gauss.first_cell_polynomial_regime d τ'
  have hs0 : ∀ N, 0 ≤ Gauss.firstCellS τ' N := by
    intro N
    rw [Gauss.firstCellS_eq_zero]
  have ht1 : ∀ N, Gauss.firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, Gauss.firstCellS τ' N ≤ Gauss.firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast B.one_le_W N)
      hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  exact Gauss.highProb_goodSetFlow_of_localLaw d
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hs0 ht1 hst
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)
    hKbig (fun N => (hΨpos N).le) hΨlowLL hll hmargin

/-- One T358 parameter drives every stochastic source event. -/
theorem exists_highProb_jointEvent :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
      HighProb (Gauss.P d) (jointEvent τ' ζ₁ ζ₃) := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    Gauss.firstCell_step1_localLaw_raw46_same_parameter
  have h3 := firstCell_raw_three_of_step1 hτ' h1
  have havg := firstCell_avgOne_stochDom hτ'
    (firstCell_localLaw_at_sourceTime hτ' hll)
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₃
  have h3p : HighProb (Gauss.P d) (rawLoopEvent τ' ζ₃ 3) :=
    (show Gauss.firstCellRawLoopDom τ' 3 from h3).highProb hζ₃
  have h4p : HighProb (Gauss.P d) (rawLoopEvent τ' ζ₃ 4) :=
    (show Gauss.firstCellRawLoopDom τ' 4 from h4).highProb hζ₃
  have h6p : HighProb (Gauss.P d) (rawLoopEvent τ' ζ₃ 6) :=
    (show Gauss.firstCellRawLoopDom τ' 6 from h6).highProb hζ₃
  have havgp : HighProb (Gauss.P d) (avgOneEvent τ' ζ₁) := havg.highProb hζ₁
  exact (((((Gauss.highProb_norm_Xmat_le d).inter h3p).inter h4p).inter h6p).inter
    (highProb_firstCell_good hτ' hll)).inter havgp

private theorem rawLoopEvent_isClosed (τ' ζ : ℝ) (n N : ℕ) :
    IsClosed (rawLoopEvent τ' ζ n N) := by
  have heq : rawLoopEvent τ' ζ n N =
      ⋂ p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
        LoopData (d.L N) n,
        {ω : Gauss.Ω d |
          ‖(Gauss.sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ * Step1.aprioriRhs B 0
              (Gauss.firstCellS τ') (Gauss.firstCellT τ') n N p ω} := by
    ext ω
    simp [rawLoopEvent]
  rw [heq]
  apply isClosed_iInter
  intro p
  have ht : Gauss.firstCellT τ' N < 1 :=
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hu : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt ht
  have hcont : Continuous (fun ω : Gauss.Ω d =>
      ‖(Gauss.sample d).Lval 0 N p.1 ω p.2.idx‖) := by
    simpa only [Gauss.sample_Lval] using
      (Gauss.continuous_gloop_Hflow d N (p.1 : ℝ)
        (Gauss.zt_im_ne_zero_of_lt_one (by norm_num : |(0 : ℝ)| < 2) hu)
        p.2.idx).norm
  exact isClosed_le hcont (by dsimp [Step1.aprioriRhs]; fun_prop)

private theorem firstCell_goodSet_isClosed (τ' : ℝ) (N : ℕ) :
    IsClosed (Gauss.goodSetFlow d 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ') Gauss.firstCellDelta N) := by
  have heq : Gauss.goodSetFlow d 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ') Gauss.firstCellDelta N =
      ⋂ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
        ⋂ x : d.Idx N, ⋂ y : d.Idx N,
          {ω : Gauss.Ω d |
            ‖green (Gauss.Hflow d N (u : ℝ) ω) (zt 0 (u : ℝ)) x y -
              (if x = y then mE 0 else 0)‖ ≤ Gauss.firstCellDelta N} := by
    ext ω
    simp [Gauss.goodSetFlow, GoodEvent]
  rw [heq]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  have ht : Gauss.firstCellT τ' N < 1 :=
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hu : (u : ℝ) < 1 := u.2.2.trans_lt ht
  have hmat : Continuous (fun ω : Gauss.Ω d =>
      green (Gauss.Hflow d N (u : ℝ) ω) (zt 0 (u : ℝ))) :=
    Gauss.continuous_green_comp (Gauss.continuous_Hflow d N (u : ℝ))
      (Gauss.Hflow_isHermitian d N (u : ℝ))
      (Gauss.zt_im_ne_zero_of_lt_one (by norm_num : |(0 : ℝ)| < 2) hu)
  exact isClosed_le ((Continuous.matrix_elem hmat x y).sub continuous_const).norm
    continuous_const

private theorem avgOneEvent_isClosed {τ' : ℝ} (hτ' : 0 < τ') (ζ : ℝ) (N : ℕ) :
    IsClosed (avgOneEvent τ' ζ N) := by
  have heq : avgOneEvent τ' ζ N =
      ⋂ b : ZMod (d.L N),
        {ω : Gauss.Ω d |
          ‖Matrix.trace ((green (Gauss.Hflow d N (sourceTime τ' N) ω)
            (zt 0 (sourceTime τ' N)) - mE 0 •
              (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b)‖ ≤
            (N : ℝ) ^ ζ * ((2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N))} := by
    ext ω
    simp [avgOneEvent]
  rw [heq]
  apply isClosed_iInter
  intro b
  have hu := sourceTime_lt_one hτ' N
  have hmat : Continuous (fun ω : Gauss.Ω d =>
      green (Gauss.Hflow d N (sourceTime τ' N) ω) (zt 0 (sourceTime τ' N))) :=
    Gauss.continuous_green_comp (Gauss.continuous_Hflow d N (sourceTime τ' N))
      (Gauss.Hflow_isHermitian d N (sourceTime τ' N))
      (Gauss.zt_im_ne_zero_of_lt_one (by norm_num : |(0 : ℝ)| < 2) hu)
  have htrace : Continuous (fun ω : Gauss.Ω d =>
      Matrix.trace ((green (Gauss.Hflow d N (sourceTime τ' N) ω)
        (zt 0 (sourceTime τ' N)) - mE 0 •
          (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) b)) :=
    Gauss.continuous_matrixTrace.comp
      ((hmat.sub continuous_const).mul continuous_const)
  exact isClosed_le htrace.norm continuous_const

theorem jointEvent_measurable {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ : ℝ) (N : ℕ) : MeasurableSet (jointEvent τ' ζ₁ ζ₃ N) := by
  unfold jointEvent
  exact (((((Gauss.measurableSet_normX_le d N).inter
    (rawLoopEvent_isClosed τ' ζ₃ 3 N).measurableSet).inter
    (rawLoopEvent_isClosed τ' ζ₃ 4 N).measurableSet).inter
    (rawLoopEvent_isClosed τ' ζ₃ 6 N).measurableSet).inter
    (firstCell_goodSet_isClosed τ' N).measurableSet).inter
    (avgOneEvent_isClosed hτ' ζ₁ N).measurableSet

/-- The two honest source losses are retained at one time and one sample. -/
theorem jointEvent_near_sources {τ' ζ₁ ζ₃ : ℝ}
    {N : ℕ} {ω : Gauss.Ω d} (hω : ω ∈ jointEvent τ' ζ₁ ζ₃ N) :
    (∀ σ (b : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N (sourceTime τ' N) ω)
          (zt 0 (sourceTime τ' N)) σ - mSigma 0 σ •
            (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ ζ₁ *
          ((2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N))) ∧
    (∀ p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
        LoopData (d.L N) 3,
      ‖(Gauss.sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
        (N : ℝ) ^ ζ₃ * Step1.aprioriRhs B 0
          (Gauss.firstCellS τ') (Gauss.firstCellT τ') 3 N p ω) := by
  have havg : ω ∈ avgOneEvent τ' ζ₁ N := hω.2
  have hraw : ω ∈ rawLoopEvent τ' ζ₃ 3 N := hω.1.1.1.1.2
  constructor
  · apply APrimeTwoChargeOneLoop.gaussian_centered_oneLoop_twoCharge_le d N
      (sourceTime τ' N) ω
    intro b
    simpa only [avgOneEvent, Set.mem_ofPred_eq, Gsig_true, mSigma_true] using havg b
  · exact hraw

/-- At `E=s=0`, the T335 scale `W⁻¹` fits the paper's one-loop
`(ℓ_u/ℓ_s)/A_u` scale at the positive first cut-net time. -/
theorem avgOne_scale_le_ratio {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ) :
    (2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N) ≤
      (B.ell N (sourceTime τ' N) /
        B.ell N (Gauss.firstCellS τ' N)) *
          (B.scale 0 N (sourceTime τ' N))⁻¹ := by
  let u := sourceTime τ' N
  have hu := sourceTime_mem hτ' N
  have hs : Gauss.firstCellS τ' N = 0 := by
    unfold Gauss.firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hu0 : 0 ≤ u := by rw [← hs]; exact hu.1
  have hu1 : u < 1 := sourceTime_lt_one hτ' N
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N u := by
    have hℓ1 : 1 ≤ B.ell N u :=
      one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega) hu0 hu1
    linarith
  have hℓs : B.ell N (Gauss.firstCellS τ' N) = 1 := by
    rw [hs]
    exact ellHat_zero (B.L N) (B.three_le_L N)
  have hη : 0 < etaT 0 u := etaT_pos_of_lt_one (by norm_num) hu1
  have hη1 : etaT 0 u ≤ 1 := etaT_le_one (by norm_num) hu0
  have hψ : (2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N) =
      ((B.W N : ℝ))⁻¹ := by
    have hr : (((B.W N : ℝ)) ^ (-(1 : ℝ) / 2)) ^ 2 = ((B.W N : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
      norm_num [Real.rpow_neg_one]
    unfold Gauss.firstCellPsi
    change (2 * (((B.W N : ℝ)) ^ (-(1 : ℝ) / 2) / 2)) *
      (2 * (((B.W N : ℝ)) ^ (-(1 : ℝ) / 2) / 2)) = _
    nlinarith [hr]
  have hratio :
      (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
        (B.scale 0 N u)⁻¹ = ((B.W N : ℝ))⁻¹ * (etaT 0 u)⁻¹ := by
    rw [hℓs]
    change B.ell N u / 1 *
      (((B.W N : ℝ)) * B.ell N u * etaT 0 u)⁻¹ = _
    field_simp
  rw [hψ, hratio]
  have hηinv : 1 ≤ (etaT 0 u)⁻¹ := by
    exact one_le_inv_iff₀.mpr ⟨hη, hη1⟩
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hηinv (inv_nonneg.mpr hW.le))

theorem jointEvent_oneLoop_paper_scale {τ' ζ₁ ζ₃ : ℝ} (hτ' : 0 < τ')
    {N : ℕ} {ω : Gauss.Ω d} (hω : ω ∈ jointEvent τ' ζ₁ ζ₃ N) :
    ∀ σ (b : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N (sourceTime τ' N) ω)
          (zt 0 (sourceTime τ' N)) σ - mSigma 0 σ •
            (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ ζ₁ *
          ((B.ell N (sourceTime τ' N) /
            B.ell N (Gauss.firstCellS τ' N)) *
              (B.scale 0 N (sourceTime τ' N))⁻¹) := by
  intro σ b
  have hone := (jointEvent_near_sources hω).1 σ b
  exact hone.trans (mul_le_mul_of_nonneg_left
    (avgOne_scale_le_ratio hτ' N)
    (Real.rpow_nonneg (Nat.cast_nonneg N) ζ₁))

theorem eventually_jointEvent_jG_cap {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ jointEvent τ' ζ₁ ζ₃ N,
      APrimeJG.jG (Gauss.sample d) 0 N (sourceTime τ' N) ω
        (B.ell N (sourceTime τ' N))
        (etaT 0 (sourceTime τ' N)) 60 ≤ (N : ℝ) := by
  filter_upwards [eventually_sourceTime_eq_firstTime hτ',
    APrimeFirstCellJGCap.eventually_jG_le_N_of_norm] with N htime hcap ω hω
  have hX : ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) := hω.1.1.1.1.1
  rw [htime.1]
  exact hcap ω hX

/-- One actual positive-time Gaussian sample carries all event components,
both charge bounds, the raw three-loop bound, and the `jG` cap. -/
theorem exists_positive_joint_near_source_sample :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Gauss.Ω d,
        ω ∈ jointEvent τ' ζ₁ ζ₃ N ∧
        0 < sourceTime τ' N ∧
        sourceTime τ' N = APrimeFirstCellJGCap.firstTime N ∧
        0 < B.scale 0 N (sourceTime τ' N) ∧
        0 < 2 * Gauss.firstCellPsi N ∧
        APrimeJG.jG (Gauss.sample d) 0 N (sourceTime τ' N) ω
          (B.ell N (sourceTime τ' N))
          (etaT 0 (sourceTime τ' N)) 60 ≤ (N : ℝ) ∧
        (∀ σ (b : ZMod (d.L N)),
          ‖Matrix.trace ((Gsig (Gauss.Hflow d N (sourceTime τ' N) ω)
              (zt 0 (sourceTime τ' N)) σ - mSigma 0 σ •
                (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
                  Eblk (d.L N) (d.W N) b)‖ ≤
            (N : ℝ) ^ ζ₁ *
              ((2 * Gauss.firstCellPsi N) * (2 * Gauss.firstCellPsi N))) ∧
        (∀ p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
            LoopData (d.L N) 3,
          ‖(Gauss.sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ₃ * Step1.aprioriRhs B 0
              (Gauss.firstCellS τ') (Gauss.firstCellT τ') 3 N p ω) := by
  obtain ⟨τ', hτ', hHP⟩ := exists_highProb_jointEvent
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₃
  have hne := HighProb.nonempty (by simp) (hHP ζ₁ ζ₃ hζ₁ hζ₃)
  filter_upwards [hne, eventually_sourceTime_eq_firstTime hτ',
    eventually_jointEvent_jG_cap hτ' ζ₁ ζ₃] with N hne htime hcap
  obtain ⟨ω, hω⟩ := hne
  have hscale : 0 < B.scale 0 N (sourceTime τ' N) :=
    B.scale_pos' (by norm_num : |(0 : ℝ)| < 2) N
      (by
        have hs : Gauss.firstCellS τ' N = 0 := by
          unfold Gauss.firstCellS
          exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [← hs]
        exact (sourceTime_mem hτ' N).1)
      (sourceTime_lt_one hτ' N)
  obtain ⟨hone, hthree⟩ := jointEvent_near_sources hω
  exact ⟨ω, hω, htime.2, htime.1, hscale,
    by linarith [Gauss.firstCellPsi_pos N], hcap ω hω, hone, hthree⟩

#print axioms sourceTime_mem
#print axioms firstCell_localLaw_at_sourceTime
#print axioms firstCell_raw_three_of_step1
#print axioms firstCell_raw346_localLaw_same_parameter
#print axioms eventually_sourceTime_eq_firstTime
#print axioms firstCell_avgOne_stochDom
#print axioms exists_highProb_jointEvent
#print axioms jointEvent_measurable
#print axioms jointEvent_near_sources
#print axioms avgOne_scale_le_ratio
#print axioms jointEvent_oneLoop_paper_scale
#print axioms eventually_jointEvent_jG_cap
#print axioms exists_positive_joint_near_source_sample

end RBM.APrimeFirstCellNearSources
