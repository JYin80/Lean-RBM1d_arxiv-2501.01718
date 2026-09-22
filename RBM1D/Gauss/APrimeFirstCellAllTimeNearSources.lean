/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellNearSources
import RBM1D.Gauss.APrimeFirstCellSourceAllTime
import RBM1D.Gauss.DetAvgIBPTimeNet

/-! # One first-cell event for the running near-`eG` sources -/

namespace RBM.APrimeFirstCellAllTimeNearSources

open Filter Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

def good (τ' ζ₁ ζ₃ : ℝ) (N : ℕ) : Set (Gauss.Ω d) :=
  APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N ∩
    Gauss.DetAvgIBPTimeNet.good τ' (ζ₁ / 4) N

theorem measurableSet_good {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ : ℝ) (N : ℕ) : MeasurableSet (good τ' ζ₁ ζ₃ N) :=
  (APrimeFirstCellNearSources.jointEvent_measurable hτ' ζ₁ ζ₃ N).inter
    (Gauss.DetAvgIBPTimeNet.measurableSet_good τ' (ζ₁ / 4) N)

private theorem highProb_firstCell_flowGood {τ' : ℝ} (hτ' : 0 < τ')
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

theorem highProb_good_of_inputs {τ' : ℝ} (hτ' : 0 < τ')
    (h1 : Step1.Hyp (Gauss.sample d) 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ'))
    (hll : LocalLawUnifIcc d 0 (Gauss.firstCellS τ')
      (Gauss.firstCellT τ') Gauss.firstCellPsi)
    (h4 : Gauss.firstCellRawLoopDom τ' 4)
    (h6 : Gauss.firstCellRawLoopDom τ' 6)
    {ζ₁ ζ₃ : ℝ} (hζ₁ : 0 < ζ₁) (hζ₃ : 0 < ζ₃) :
    HighProb (Gauss.P d) (good τ' ζ₁ ζ₃) := by
  have h3 := APrimeFirstCellNearSources.firstCell_raw_three_of_step1 hτ' h1
  have havg := APrimeFirstCellNearSources.firstCell_avgOne_stochDom hτ'
    (APrimeFirstCellNearSources.firstCell_localLaw_at_sourceTime hτ' hll)
  have h3p : HighProb (Gauss.P d)
      (APrimeFirstCellNearSources.rawLoopEvent τ' ζ₃ 3) := h3.highProb hζ₃
  have h4p : HighProb (Gauss.P d)
      (APrimeFirstCellNearSources.rawLoopEvent τ' ζ₃ 4) := h4.highProb hζ₃
  have h6p : HighProb (Gauss.P d)
      (APrimeFirstCellNearSources.rawLoopEvent τ' ζ₃ 6) := h6.highProb hζ₃
  have havgp : HighProb (Gauss.P d)
      (APrimeFirstCellNearSources.avgOneEvent τ' ζ₁) := havg.highProb hζ₁
  have hjoint : HighProb (Gauss.P d)
      (APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃) :=
    (((((Gauss.highProb_norm_Xmat_le d).inter h3p).inter h4p).inter h6p).inter
      (highProb_firstCell_flowGood hτ' hll)).inter havgp
  have hI := Gauss.DetAvgIBPTimeNet.ibpDom_of_localLaw hτ' hll
  obtain ⟨hR, hB⟩ := Gauss.DetFlucAvgTimeNet.simultaneous_of_localLaw hτ' hll
  have htime := Gauss.DetAvgIBPTimeNet.highProb_good hI hR hB
    (by linarith : 0 < ζ₁ / 4)
  exact hjoint.inter htime

theorem raw_three_on_good {τ' ζ₁ ζ₃ : ℝ} {N : ℕ}
    {ω : Gauss.Ω d} (hω : ω ∈ good τ' ζ₁ ζ₃ N) :
    ∀ p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
      LoopData (d.L N) 3,
      ‖(Gauss.sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
        (N : ℝ) ^ ζ₃ * Step1.aprioriRhs B 0
          (Gauss.firstCellS τ') (Gauss.firstCellT τ') 3 N p ω :=
  (APrimeFirstCellNearSources.jointEvent_near_sources hω.1).2

theorem raw_three_paper_scale {τ' ζ₁ ζ₃ : ℝ} {N : ℕ}
    {ω : Gauss.Ω d} (hω : ω ∈ good τ' ζ₁ ζ₃ N)
    (u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N)
    (a₁ a₂ b : ZMod (d.L N)) :
    ‖gloop (d.L N) (d.W N) (Gauss.Hflow d N u ω) (zt 0 u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (N : ℝ) ^ ζ₃ *
        (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
          ((B.scale 0 N u) ^ 2)⁻¹ := by
  let v : LoopData (d.L N) 3 := (![false, true, true], ![a₂, b, a₁])
  let p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
      LoopData (d.L N) 3 := (u, v)
  have hraw := raw_three_on_good hω p
  have hidx : v.idx = (⟨[false, true, true], [a₂, b, a₁]⟩ :
      LoopIdx (ZMod (d.L N))) := by
    simp [v, LoopData.idx, List.ofFn_succ]
  have hRhs : Step1.aprioriRhs B 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ') 3 N p ω =
      (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
        ((B.scale 0 N u) ^ 2)⁻¹ := by
    change (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ (3 - 1) *
      (B.scale 0 N u)⁻¹ ^ (3 - 1) = _
    simp only [Nat.reduceSub, inv_pow]
  rw [hRhs, Gauss.sample_Lval, hidx] at hraw
  simpa only [p, mul_assoc] using hraw

private theorem Phi_le_twice_paper_scale {τ' : ℝ} (N : ℕ)
    (u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N) :
    Gauss.DetAvgIBPTimeNet.Phi N u ≤
      2 * ((B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
        (B.scale 0 N u)⁻¹) := by
  have hs : Gauss.firstCellS τ' N = 0 := Gauss.firstCellS_eq_zero τ' N
  have hu0 : 0 ≤ (u : ℝ) := by rw [← hs]; exact u.property.1
  have hu1 : (u : ℝ) < 1 :=
    u.property.2.trans_lt ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
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
  have hratio :
      (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
        (B.scale 0 N u)⁻¹ = ((B.W N : ℝ))⁻¹ * (etaT 0 u)⁻¹ := by
    rw [hℓs]
    change B.ell N u / 1 *
      (((B.W N : ℝ)) * B.ell N u * etaT 0 u)⁻¹ = _
    field_simp
  have hphi : Gauss.DetAvgIBPTimeNet.Phi N u =
      ((B.W N : ℝ))⁻¹ * (etaT 0 u)⁻¹ + ((B.W N : ℝ))⁻¹ := by
    unfold Gauss.DetAvgIBPTimeNet.Phi
    change 1 / ((B.W N : ℝ) * (1 - (u : ℝ))) + ((B.W N : ℝ))⁻¹ = _
    have hηeq : etaT 0 (u : ℝ) = 1 - (u : ℝ) := by
      rw [Step2.etaT_eq, mE_zero]
      norm_num
    rw [hηeq]
    field_simp
  rw [hratio, hphi]
  have hηinv : 1 ≤ (etaT 0 u)⁻¹ := one_le_inv_iff₀.mpr ⟨hη, hη1⟩
  have hWinv : 0 ≤ ((B.W N : ℝ))⁻¹ := inv_nonneg.mpr hW.le
  nlinarith [mul_le_mul_of_nonneg_left hηinv hWinv]

theorem eventually_avg_oneLoop_on_good {τ' ζ₁ : ℝ} (hζ₁ : 0 < ζ₁)
    (ζ₃ : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good τ' ζ₁ ζ₃ N,
      ∀ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
        ∀ σ (b : ZMod (d.L N)),
          ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) σ -
            mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b)‖ ≤
            (N : ℝ) ^ ζ₁ *
              ((B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
                (B.scale 0 N u)⁻¹) := by
  have hhalf : 0 < ζ₁ / 2 := by linarith
  filter_upwards [Gauss.DetAvgIBPTimeNet.eventually_trace_le_on_good
      (τ' := τ') hhalf, eventually_le_rpow 2 hhalf,
    eventually_ge_atTop 1] with N htrace htwo hN ω hω u σ b
  let R : ℝ := (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
    (B.scale 0 N u)⁻¹
  have hu1 : (u : ℝ) < 1 :=
    u.property.2.trans_lt ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hden : 0 < (B.W N : ℝ) * (1 - (u : ℝ)) :=
    mul_pos hW (by linarith)
  have hPhi0 : 0 ≤ Gauss.DetAvgIBPTimeNet.Phi N u := by
    unfold Gauss.DetAvgIBPTimeNet.Phi
    change 0 ≤ 1 / ((B.W N : ℝ) * (1 - (u : ℝ))) + ((B.W N : ℝ))⁻¹
    positivity
  have hPhi := Phi_le_twice_paper_scale N u
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpow : (N : ℝ) ^ (ζ₁ / 2) * (N : ℝ) ^ (ζ₁ / 2) =
      (N : ℝ) ^ ζ₁ := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hcoef : (N : ℝ) ^ (ζ₁ / 2) * 2 ≤ (N : ℝ) ^ ζ₁ := by
    calc
      _ = 2 * (N : ℝ) ^ (ζ₁ / 2) := by ring
      _ ≤ (N : ℝ) ^ (ζ₁ / 2) * (N : ℝ) ^ (ζ₁ / 2) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hNpos.le _)
      _ = _ := hpow
  have htrue : ∀ b : ZMod (d.L N),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) true -
        mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤ (N : ℝ) ^ ζ₁ * R := by
    intro b
    let q : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
      ZMod (d.L N) := (u, b)
    have hmem : ω ∈ Gauss.DetAvgIBPTimeNet.good τ' ((ζ₁ / 2) / 2) N := by
      simpa only [show ζ₁ / 2 / 2 = ζ₁ / 4 by ring] using hω.2
    have ht := htrace ω hmem q
    have ht' : ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) true -
        mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ (ζ₁ / 2) * Gauss.DetAvgIBPTimeNet.Phi N u := by
      simpa only [Gsig_true, mSigma_true] using ht
    calc
      _ ≤ (N : ℝ) ^ (ζ₁ / 2) * Gauss.DetAvgIBPTimeNet.Phi N u := ht'
      _ ≤ (N : ℝ) ^ (ζ₁ / 2) * (2 * R) :=
        mul_le_mul_of_nonneg_left hPhi (Real.rpow_nonneg hNpos.le _)
      _ = ((N : ℝ) ^ (ζ₁ / 2) * 2) * R := by ring
      _ ≤ (N : ℝ) ^ ζ₁ * R := mul_le_mul_of_nonneg_right hcoef hR0
  exact APrimeTwoChargeOneLoop.gaussian_centered_oneLoop_twoCharge_le
    d N u ω htrue σ b

theorem sourceEvent_on_good {τ' ζ₁ ζ₃ : ℝ} {N : ℕ} (hN : 0 < N)
    (u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N)
    {ω : Gauss.Ω d} (hω : ω ∈ good τ' ζ₁ ζ₃ N) :
    APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (u : ℝ) ω
      (APrimeFirstCellSourceAllTime.ellSource ζ₃ N)
      (APrimeFirstCellSourceAllTime.sourceC4 ζ₃ N u) := by
  have hj := hω.1
  have hc : ω ∈ APrimeFirstCellSourceAllTime.commonEvent τ' ζ₃ N := by
    rcases hj with ⟨⟨⟨⟨⟨hX, _h3⟩, h4⟩, h6⟩, hgood⟩, _havg⟩
    exact ⟨⟨⟨hX, h4⟩, h6⟩, hgood⟩
  exact APrimeFirstCellSourceAllTime.sourceEvent_of_common hN u hc

/-- The centered one-loop source is exactly zero at the initial endpoint. -/
theorem centered_oneLoop_zero (N : ℕ) (ω : Gauss.Ω d)
    (σ : Bool) (b : ZMod (d.L N)) :
    Matrix.trace ((Gsig (Gauss.Hflow d N 0 ω) (zt 0 0) σ -
      mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) b) = 0 := by
  cases σ with
  | true =>
      simpa only [Gsig_true, mSigma_true] using
        Gauss.DetAvgIBPTimeNet.trace_at_zero N ω b
  | false =>
      have hnorm := APrimeTwoChargeOneLoop.gaussian_centered_oneLoop_false_norm_eq_true
        d N 0 ω b
      have htrue : ‖Matrix.trace ((Gsig (Gauss.Hflow d N 0 ω) (zt 0 0) true -
          mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖ = 0 := by
        simpa only [Gsig_true, mSigma_true,
          Gauss.DetAvgIBPTimeNet.trace_at_zero, norm_zero]
      rw [htrue] at hnorm
      exact norm_eq_zero.mp hnorm

theorem eGpm_zero (N : ℕ) (ω : Gauss.Ω d)
    (a₁ a₂ : ZMod (d.L N)) :
    EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
      (Gauss.Hflow d N 0 ω) (zt 0 0) a₁ a₂ = 0 := by
  unfold EGDef.eGpm
  simp only [centered_oneLoop_zero, zero_mul]
  simp

/-- All running-time sources live on the same nonempty measurable event. -/
theorem exists_highProb_good :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
        HighProb (Gauss.P d) (good τ' ζ₁ ζ₃) ∧
        (∀ N, MeasurableSet (good τ' ζ₁ ζ₃ N)) ∧
        ∀ᶠ N : ℕ in atTop,
          (good τ' ζ₁ ζ₃ N).Nonempty ∧
          ∀ ω ∈ good τ' ζ₁ ζ₃ N,
            ∀ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
              APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (u : ℝ) ω
                (APrimeFirstCellSourceAllTime.ellSource ζ₃ N)
                (APrimeFirstCellSourceAllTime.sourceC4 ζ₃ N u) ∧
              (∀ a₁ a₂ b : ZMod (d.L N),
                ‖gloop (d.L N) (d.W N) (Gauss.Hflow d N u ω) (zt 0 u)
                  ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
                  (N : ℝ) ^ ζ₃ *
                    (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
                      ((B.scale 0 N u) ^ 2)⁻¹) ∧
              (∀ σ (b : ZMod (d.L N)),
                ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) σ -
                  mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
                    Eblk (d.L N) (d.W N) b)‖ ≤
                  (N : ℝ) ^ ζ₁ *
                    ((B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
                      (B.scale 0 N u)⁻¹)) := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    Gauss.firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₃
  have hp := highProb_good_of_inputs hτ' h1 hll h4 h6 hζ₁ hζ₃
  refine ⟨hp, measurableSet_good hτ' ζ₁ ζ₃, ?_⟩
  have hne := HighProb.nonempty (by simp) hp
  filter_upwards [hne, eventually_avg_oneLoop_on_good hζ₁ ζ₃,
    eventually_ge_atTop 1] with N hne havg hN
  refine ⟨hne, ?_⟩
  intro ω hω u
  have hNpos : 0 < N := by omega
  exact ⟨sourceEvent_on_good hNpos u hω,
    (fun a₁ a₂ b => raw_three_paper_scale hω u a₁ a₂ b),
    havg ω hω u⟩

/-- One sample from the common event carries all three sources at an actual
positive time, while the event theorem above supplies them throughout the cell. -/
theorem exists_positive_time_sample :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
        ∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ good τ' ζ₁ ζ₃ N,
            ∃ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
              0 < (u : ℝ) ∧
              (u : ℝ) = APrimeFirstCellJGCap.firstTime N ∧
              APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (u : ℝ) ω
                (APrimeFirstCellSourceAllTime.ellSource ζ₃ N)
                (APrimeFirstCellSourceAllTime.sourceC4 ζ₃ N u) ∧
              (∀ a₁ a₂ b : ZMod (d.L N),
                ‖gloop (d.L N) (d.W N) (Gauss.Hflow d N u ω) (zt 0 u)
                  ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
                  (N : ℝ) ^ ζ₃ *
                    (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
                      ((B.scale 0 N u) ^ 2)⁻¹) ∧
              (∀ σ (b : ZMod (d.L N)),
                ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) σ -
                  mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
                    Eblk (d.L N) (d.W N) b)‖ ≤
                  (N : ℝ) ^ ζ₁ *
                    ((B.ell N u / B.ell N (Gauss.firstCellS τ' N)) *
                      (B.scale 0 N u)⁻¹)) := by
  obtain ⟨τ', hτ', hsource⟩ := exists_highProb_good
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₃
  obtain ⟨_, _, hall⟩ := hsource ζ₁ ζ₃ hζ₁ hζ₃
  filter_upwards [hall,
    APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime hτ']
    with N hgood htime
  obtain ⟨hne, hsources⟩ := hgood
  obtain ⟨ω, hω⟩ := hne
  let u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N :=
    ⟨APrimeFirstCellNearSources.sourceTime τ' N,
      APrimeFirstCellNearSources.sourceTime_mem hτ' N⟩
  obtain ⟨h4, h3, h1⟩ := hsources ω hω u
  exact ⟨ω, hω, u, htime.2, htime.1, h4, h3, h1⟩

#print axioms highProb_good_of_inputs
#print axioms raw_three_on_good
#print axioms raw_three_paper_scale
#print axioms Phi_le_twice_paper_scale
#print axioms eventually_avg_oneLoop_on_good
#print axioms sourceEvent_on_good
#print axioms centered_oneLoop_zero
#print axioms eGpm_zero
#print axioms exists_highProb_good
#print axioms exists_positive_time_sample

end RBM.APrimeFirstCellAllTimeNearSources
