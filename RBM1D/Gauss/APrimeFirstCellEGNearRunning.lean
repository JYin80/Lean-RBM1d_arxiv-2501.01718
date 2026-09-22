/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellAllTimeNearSources
import RBM1D.Gauss.APrimeFirstCellSourceSupport
import RBM1D.Gauss.APrimeFirstCellEGNearSmall

/-! # Active-support running near-`eGpm` bound on the first cell -/

namespace RBM.APrimeFirstCellEGNearRunning

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

noncomputable def sourceLoss (ν : ℝ) : ℝ := min (ν / 8) (1 / 2)

def good (τ' ν : ℝ) (N : ℕ) : Set (Gauss.Ω d) :=
  APrimeFirstCellAllTimeNearSources.good τ' (sourceLoss ν) (sourceLoss ν) N ∩
    APrimeFirstCellSourceSupport.jointEvent τ' (sourceLoss ν) N

theorem measurableSet_good {τ' : ℝ} (hτ' : 0 < τ')
    (ν : ℝ) (N : ℕ) : MeasurableSet (good τ' ν N) :=
  (APrimeFirstCellAllTimeNearSources.measurableSet_good hτ'
    (sourceLoss ν) (sourceLoss ν) N).inter
      (APrimeFirstCellSourceSupport.measurableSet_jointEvent τ' (sourceLoss ν) N)

theorem highProb_good_of_inputs {τ' ν : ℝ} (hτ' : 0 < τ') (hν : 0 < ν)
    (h1 : Step1.Hyp (Gauss.sample d) 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ'))
    (hll : LocalLawUnifIcc d 0 (Gauss.firstCellS τ')
      (Gauss.firstCellT τ') Gauss.firstCellPsi)
    (h4 : Gauss.firstCellRawLoopDom τ' 4)
    (h6 : Gauss.firstCellRawLoopDom τ' 6) :
    HighProb (Gauss.P d) (good τ' ν) := by
  have hζ : 0 < sourceLoss ν := lt_min (by positivity) (by norm_num)
  exact (APrimeFirstCellAllTimeNearSources.highProb_good_of_inputs
    hτ' h1 hll h4 h6 hζ hζ).inter
      (APrimeFirstCellSourceSupport.highProb_jointEvent_at hτ' hζ hll h4 h6)

/-- The deterministic first-cell scale package is uniform in the running time. -/
theorem eventually_running_scales {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      ∀ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
        Real.exp 1 ≤ (d.W N : ℝ) ∧
        4 ≤ Real.log (d.W N : ℝ) ∧
        (4 * (60 : ℝ)) ^ 2 ≤ Real.log (d.W N : ℝ) ∧
        1 ≤ (N : ℝ) ∧
        1 ≤ B.ell N u ∧
        B.ell N (Gauss.firstCellS τ' N) = 1 ∧
        1 ≤ B.ell N u / B.ell N (Gauss.firstCellS τ' N) ∧
        0 < etaT 0 u ∧
        (etaT 0 u)⁻¹ ≤ (N : ℝ) ∧
        1 ≤ (d.W N : ℝ) * B.ell N u * etaT 0 u ∧
        (d.W N : ℝ) * B.ell N u * etaT 0 u ≤ (N : ℝ) ∧
        (d.L N : ℝ) ≤ (N : ℝ) ∧
        (N : ℝ) ≤ (d.W N : ℝ) ^ 2 ∧
        4 * (1 : ℝ) ≤ (d.W N : ℝ) := by
  filter_upwards [APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    eventually_ge_atTop 2] with N hs hN u
  rcases hs with ⟨hW, hlog4, hlog, hN1, _, _, _, hWL, hNW⟩
  have hs0 : Gauss.firstCellS τ' N = 0 := Gauss.firstCellS_eq_zero τ' N
  have hu0 : 0 ≤ (u : ℝ) := by rw [← hs0]; exact u.property.1
  have huHalf : (u : ℝ) ≤ 1 / 2 :=
    u.property.2.trans (gridT_le (1 / 2 : ℝ) 1)
  have hu1 : (u : ℝ) < 1 := by linarith
  have hℓ : 1 ≤ B.ell N u :=
    one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega) hu0 hu1
  have hℓs : B.ell N (Gauss.firstCellS τ' N) = 1 := by
    rw [hs0]
    exact ellHat_zero (B.L N) (B.three_le_L N)
  have hr : 1 ≤ B.ell N u / B.ell N (Gauss.firstCellS τ' N) := by
    rw [hℓs, div_one]
    exact hℓ
  have hη : 0 < etaT 0 u := etaT_pos_of_lt_one (by norm_num) hu1
  have hηeq : etaT 0 (u : ℝ) = 1 - (u : ℝ) := by
    rw [Step2.etaT_eq, mE_zero]
    norm_num
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 u := by rw [hηeq]; linarith
  have hηinv2 : (etaT 0 u)⁻¹ ≤ (2 : ℝ) := by
    have hi := (inv_le_inv₀ hη (by norm_num : (0 : ℝ) < 1 / 2)).2 hηhalf
    norm_num at hi ⊢
    exact hi
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hηinv : (etaT 0 u)⁻¹ ≤ (N : ℝ) := hηinv2.trans hNr
  have hscaleHalf := Gauss.firstCell_scale_ge_half N u.property
  have hA1 : 1 ≤ (d.W N : ℝ) * B.ell N u * etaT 0 u := by
    have hW2 : (2 : ℝ) ≤ d.W N := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      exact he.trans hW
    change 1 ≤ B.scale 0 N u
    linarith
  have hηℓ : etaT 0 u * B.ell N u ≤ 1 :=
    etaT_mul_ellHat_le (L := d.L N) (d.three_le_L N)
      (by norm_num : |(0 : ℝ)| ≤ 2) hu0 hu1
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hL1 : (1 : ℝ) ≤ d.L N := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hWle : (d.W N : ℝ) ≤ (N : ℝ) := by
    nlinarith [mul_nonneg hWpos.le (sub_nonneg.mpr hL1)]
  have hA : (d.W N : ℝ) * B.ell N u * etaT 0 u ≤ (N : ℝ) := by
    calc
      _ = (d.W N : ℝ) * (etaT 0 u * B.ell N u) := by ring
      _ ≤ (d.W N : ℝ) * 1 := mul_le_mul_of_nonneg_left hηℓ hWpos.le
      _ ≤ (N : ℝ) := by simpa using hWle
  have hL : (d.L N : ℝ) ≤ (N : ℝ) := by
    have hW1 : (1 : ℝ) ≤ d.W N := (Real.one_le_exp (by norm_num)).trans hW
    nlinarith [mul_nonneg (sub_nonneg.mpr hW1) (Nat.cast_nonneg (d.L N))]
  have hW4 : 4 * (1 : ℝ) ≤ (d.W N : ℝ) := by
    have hp : (4 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp (4 : ℝ)]
    have hexp : Real.exp 4 ≤ (d.W N : ℝ) := by
      simpa only [Real.exp_log hWpos] using
        (Real.exp_le_exp.mpr hlog4)
    nlinarith
  exact ⟨hW, hlog4, hlog, hN1, hℓ, hℓs, hr, hη, hηinv,
    hA1, hA, hL, hNW, hW4⟩

theorem eventually_cNear_le_running {τ' : ℝ} (hτ' : 0 < τ')
    {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop,
      ∀ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
        Lemma57.cNear (d.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ (ν / 4) := by
  have hθ : (0 : ℝ) < ν / 8 := by positivity
  have hlogR : ∀ᶠ W : ℝ in atTop,
      4 * Real.log W ^ (3 : ℝ) ≤ W ^ (ν / 8) := by
    have hsmall := (Asymptotics.isLittleO_iff_nat_mul_le'.1
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hθ)) 4
    filter_upwards [hsmall, eventually_ge_atTop 1] with W hsmall hW1
    have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
    have hp0 : 0 ≤ Real.log W ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
    have hwp0 : 0 ≤ W ^ (ν / 8) := Real.rpow_nonneg (by linarith : 0 ≤ W) _
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg hp0,
      abs_of_nonneg hwp0] using hsmall
  have hlog := (Step2.tendsto_W B).eventually hlogR
  have hExp := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 1 hθ)
  have hPow4 : ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) ≤ (d.W N : ℝ) ^ (ν / 8) :=
    ((tendsto_rpow_atTop hθ).comp (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [eventually_running_scales hτ', d.dim, hlog, hExp, hPow4]
    with N hs hdim hlog hExp hPow4 u
  rcases hs u with ⟨hW, _, _, _, hℓ, _, _, _, _, _, _, _, _, _⟩
  let W : ℝ := d.W N
  let ell : ℝ := B.ell N u
  have hWpos : 0 < W := by
    change (0 : ℝ) < (d.W N : ℝ)
    exact_mod_cast d.W_pos N
  have hL1 : (1 : ℝ) ≤ d.L N := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have hWle : W ≤ (N : ℝ) := by
    change (d.W N : ℝ) ≤ (N : ℝ)
    nlinarith [mul_nonneg hWpos.le (sub_nonneg.mpr hL1)]
  have hdiv : 2 / ell ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by dsimp [ell]; linarith)).2
    dsimp [ell]
    nlinarith
  change 4 * Real.log W ^ (3 : ℝ) ≤ W ^ (ν / 8) at hlog
  change (4 : ℝ) ≤ W ^ (ν / 8) at hPow4
  have hExp' : Real.exp (Real.log W ^ (3 / 4 : ℝ)) ≤ W ^ (ν / 8) := by
    change Real.exp (1 * Real.log W ^ (3 / 4 : ℝ)) ≤ W ^ (ν / 8) at hExp
    simpa only [one_mul] using hExp
  have hpoly : 2 * Real.log W ^ (3 : ℝ) + 2 / ell ≤ W ^ (ν / 8) := by
    nlinarith
  have hc : Lemma57.cNear W ell ≤ W ^ (ν / 8) * W ^ (ν / 8) := by
    unfold Lemma57.cNear
    exact mul_le_mul hpoly hExp' (Real.exp_pos _).le
      (Real.rpow_nonneg hWpos.le _)
  calc
    Lemma57.cNear W ell ≤ W ^ (ν / 8) * W ^ (ν / 8) := hc
    _ = W ^ (ν / 4) := by
      rw [← Real.rpow_add hWpos]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ (ν / 4) :=
      Real.rpow_le_rpow hWpos.le hWle (by positivity)

/-- On positive literal prefix support, the actual running near drift has an
arbitrarily small polynomial loss, uniformly over the whole active prefix. -/
theorem eventually_near_on_active_support {τ' ν : ℝ}
    (hτ' : 0 < τ') (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good τ' ν N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100) (Gauss.firstCellT τ')
          N0 p N k m ω →
        ∀ u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
          (u : ℝ) ∈ Set.Icc (0 : ℝ)
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) →
          ∀ a₁ a₂ : ZMod (d.L N),
            let ellu := B.ell N u
            let ells := B.ell N (Gauss.firstCellS τ' N)
            let etau := etaT 0 u
            let rr := ellu / ells
            let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
            ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
                (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
                (if dd ≤ ellStar (d.W N : ℝ) ellu then 1 else 0) ≤
              (N : ℝ) ^ ν * etau⁻¹ * rr ^ 3 *
                tailT (d.W N : ℝ) ellu etau 60 dd *
                (if dd ≤ ellStar (d.W N : ℝ) ellu then 1 else 0) := by
  have hζ0 : 0 < sourceLoss ν := lt_min (by positivity) (by norm_num)
  have hζ1 : sourceLoss ν ≤ 1 :=
    (min_le_right _ _).trans (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (ν / 2) :=
    eventually_le_rpow 4 (by positivity)
  filter_upwards [eventually_running_scales hτ',
    eventually_cNear_le_running hτ' hν, hlarge,
    APrimeFirstCellAllTimeNearSources.eventually_avg_oneLoop_on_good
      (τ' := τ') hζ0 (sourceLoss ν),
    APrimeSupportRunning.eventually_jG_le_eighth_on_support hτ'] with
    N hscales hcNear hlarge havg hcap ω hω N0 p k m hN0 hp hm hk hkT hw
      u hu a₁ a₂
  dsimp only
  rcases hscales u with ⟨hW, hlog4, hlog, hN, hEll, hElls, hrr,
    hEta, hEtaInv, hA1, hA, hL, hNW, hW4⟩
  let ellu : ℝ := B.ell N u
  let ells : ℝ := B.ell N (Gauss.firstCellS τ' N)
  let etau : ℝ := etaT 0 u
  let rr : ℝ := ellu / ells
  let dd : ℝ := (zdist (d.L N) (a₂ - a₁) : ℝ)
  let L3 : ZMod (d.L N) → ℝ := fun b =>
    ‖gloop (d.L N) (d.W N) (Gauss.Hflow d N u ω) (zt 0 u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖
  let EG : ℝ := ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
    (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖
  have hJ8 := hcap N0 p k m hN0 hp hm hk hkT ω hω.2.2 hw (u : ℝ) hu
  have hJpow : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) := by
    have hb := Real.rpow_le_rpow_of_exponent_le hN
      (by norm_num : (1 : ℝ) / 8 ≤ 1)
    simpa only [Real.rpow_one] using hb
  have hJle : APrimeJG.jG (Gauss.sample d) 0 N u ω ellu etau 60 ≤
      (N : ℝ) := hJ8.trans hJpow
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hJ0 : 0 ≤ APrimeJG.jG (Gauss.sample d) 0 N u ω ellu etau 60 :=
    (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (APrimeJG.one_le_jG (Gauss.sample d) 0 N u ω
        (ℓu := ellu) (ηu := etau) (D := 60) hWpos))
  have hL3 : ∀ b, L3 b ≤ 1 * (N : ℝ) ^ (sourceLoss ν) * rr ^ 2 *
      (((d.W N : ℝ) * ellu * etau) ^ 2)⁻¹ := by
    intro b
    have hb := APrimeFirstCellAllTimeNearSources.raw_three_paper_scale
      hω.1 u a₁ a₂ b
    change ‖gloop (d.L N) (d.W N) (Gauss.Hflow d N u ω) (zt 0 u)
        ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (N : ℝ) ^ (sourceLoss ν) *
        (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
          ((B.scale 0 N u) ^ 2)⁻¹ at hb
    have hWsame : (B.W N : ℝ) = (d.W N : ℝ) := rfl
    rw [show B.scale 0 N u = (B.W N : ℝ) * B.ell N u * etaT 0 u from rfl,
      hWsame] at hb
    simpa only [one_mul, Band.scale, mul_assoc, L3, rr, ellu, ells, etau]
      using hb
  have hone : ∀ sigma (b : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) sigma -
        mSigma 0 sigma • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ (sourceLoss ν) * (rr * (B.scale 0 N u)⁻¹) := by
    intro sigma b
    simpa only [rr, ellu, ells, mul_assoc] using havg ω hω.1 u sigma b
  have hEG : EG ≤ (2 * (1 : ℝ) * (N : ℝ) ^ (sourceLoss ν) * rr) *
      (ellu * etau)⁻¹ * ∑ b : ZMod (d.L N), L3 b := by
    let c : ℝ := (N : ℝ) ^ (sourceLoss ν) * (rr * (B.scale 0 N u)⁻¹)
    have hbase := EGDef.norm_eGpm_le (d.three_le_L N)
      (Gauss.Hflow_isHermitian d N u ω) (mSigma 0) hone a₁ a₂
    have hcoef : 2 * (d.W N : ℝ) * c =
        (2 * (N : ℝ) ^ (sourceLoss ν) * rr) * (ellu * etau)⁻¹ := by
      dsimp [c]
      rw [show B.scale 0 N u = (d.W N : ℝ) * ellu * etau from rfl]
      field_simp
      have hWsame : (Gauss.Dims.growW N : ℝ) = (d.W N : ℝ) := rfl
      rw [hWsame]
      ring
    rw [hcoef] at hbase
    simpa only [one_mul, EG, L3, c, mul_assoc] using hbase
  have hu1 : (u : ℝ) < 1 :=
    u.property.2.trans_lt ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have h554 : dd ≤ ellStar (d.W N : ℝ) ellu →
      ∀ b, Lemma57.ellStarStar (d.W N : ℝ) ellu <
        (zdist (d.L N) (a₂ - b) : ℝ) →
        L3 b ≤ etau⁻¹ *
          APrimeJG.jG (Gauss.sample d) 0 N u ω ellu etau 60 *
          tailT (d.W N : ℝ) ellu etau 60
            (APrimeDriftNearAbsorb.gap (d.W N : ℝ) ellu) := by
    intro hnear b hfar
    have hb := APrimeDriftNearTriple.gaussian_three_near_far_le d
      (by norm_num : |(0 : ℝ)| < 2) N hu1 ω (D := 60)
      (by dsimp [ellu]; linarith) hlog4 a₁ a₂ b hnear hfar
    simpa only [L3, ellu, etau, APrimeDriftNearAbsorb.gap,
      Gauss.sample_H] using hb
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  have hsplit := APrimeEGNearScaled.eG_near_indicator_le_scaled_absorb
    (d.L N) hW hEll (by rw [hElls]; norm_num) hEta hN
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    hζ0.le hζ1 hζ0.le hJ0 hJle hrr hA1 hA hL hEtaInv hNW
    hlog hW4 a₂ a₁ hL3 h554 hEG
  let coef : ℝ :=
    2 * (N : ℝ) ^ (sourceLoss ν + sourceLoss ν) *
      Lemma57.cNear (d.W N : ℝ) ellu + (d.W N : ℝ)⁻¹
  let profile : ℝ := etau⁻¹ * rr ^ 3 *
    tailT (d.W N : ℝ) ellu etau 60 dd *
      (if dd ≤ ellStar (d.W N : ℝ) ellu then 1 else 0)
  have hbase : EG * (if dd ≤ ellStar (d.W N : ℝ) ellu then 1 else 0) ≤
      coef * profile := by
    convert hsplit using 1 <;>
      simp only [one_mul, mul_one, L3, EG, dd, rr, ellu, ells, etau,
        coef, profile, APrimeDriftNearAbsorb.nearRate] <;> ring
  have hcoef : coef ≤ (N : ℝ) ^ ν := by
    apply APrimeFirstCellEGNearSmall.coefficient_le_rpow hν hN
      ((Real.one_le_exp (by norm_num)).trans hW)
    · simpa only [ellu] using hcNear u
    · exact hlarge
  have hprofile : 0 ≤ profile := by
    dsimp [profile]
    have htail : 0 ≤ tailT (d.W N : ℝ) ellu etau 60 dd :=
      (tailT_pos hWpos dd).le
    have hrr0 : 0 ≤ rr := by linarith
    positivity
  have hfinal := hbase.trans (mul_le_mul_of_nonneg_right hcoef hprofile)
  convert hfinal using 1 <;> simp only [EG, dd, rr, ellu, ells, etau, profile] <;> ring

theorem eGpm_zero (N : ℕ) (ω : Gauss.Ω d)
    (a₁ a₂ : ZMod (d.L N)) :
    EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
      (Gauss.Hflow d N 0 ω) (zt 0 0) a₁ a₂ = 0 :=
  APrimeFirstCellAllTimeNearSources.eGpm_zero N ω a₁ a₂

/-- One Step-1 parameter is selected before the requested loss exponent. -/
theorem exists_highProb_good :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet (good τ' ν N)) ∧
        HighProb (Gauss.P d) (good τ' ν) ∧
        ∀ᶠ N : ℕ in atTop, (good τ' ν N).Nonempty := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    Gauss.firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ν hν
  have hp := highProb_good_of_inputs hτ' hν h1 hll h4 h6
  exact ⟨measurableSet_good hτ' ν, hp, hp.nonempty (by simp)⟩

def nearBoundAt (ν : ℝ) (N : ℕ)
    (u : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N)
    (ω : Gauss.Ω d) : Prop :=
  ∀ a₁ a₂ : ZMod (d.L N),
    let ellu := B.ell N u
    let ells := B.ell N (Gauss.firstCellS τ' N)
    let etau := etaT 0 u
    let rr := ellu / ells
    let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
        (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
        (if dd ≤ ellStar (d.W N : ℝ) ellu then 1 else 0) ≤
      (N : ℝ) ^ ν * etau⁻¹ * rr ^ 3 *
        tailT (d.W N : ℝ) ellu etau 60 dd *
        (if dd ≤ ellStar (d.W N : ℝ) ellu then 1 else 0)

/-- The common event has a same-sample active `k=2` witness. Its first
positive grid point is `N⁻²⁴⁸`, and the running near bound holds there. -/
theorem exists_positive_active_sample :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ν : ℝ, 0 < ν →
        ∀ᶠ N : ℕ in atTop, ∃ ω ∈ good τ' ν N,
          ∃ u1 : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N,
            0 < (u1 : ℝ) ∧
            (u1 : ℝ) = (N : ℝ) ^ (-(248 : ℝ)) ∧
            2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
              APrimeSmoothTransition.transitionMesh N ∧
            (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
              (Gauss.firstCellT τ') 2 p N 2 N ω = 1) ∧
            nearBoundAt (τ' := τ') ν N u1 ω := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    Gauss.firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ν hν
  have hpGood := highProb_good_of_inputs hτ' hν h1 hll h4 h6
  have hpSupport := APrimeSupportRunning.highProb_good hτ'
    (by norm_num : (0 : ℝ) < 1 / 100) hll
  filter_upwards [hpGood.nonempty (by simp),
    APrimeSupportRunning.positive_plateau_on_good hτ'
      (by norm_num : (0 : ℝ) < 1 / 100) hpSupport,
    APrimeFirstCellCommon.eventually_active_weight_two_one hτ'
      (by norm_num : (0 : ℝ) < 1 / 100),
    eventually_near_on_active_support hτ' hν,
    eventually_ge_atTop 2] with N hne hplat hweight hnear hN
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨_, _, hpos, hmem, hkT, _⟩ := hplat
  have hnorm : ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) := hω.2.1.1.1.1
  have hw : ∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
      (Gauss.firstCellT τ') 2 p N 2 N ω = 1 := by
    intro p
    have hh := hweight ω hnorm p
    rw [APrimeSupportRunning.firstS_eq] at hh
    exact hh
  have hs0 : Gauss.firstCellS τ' N = 0 := Gauss.firstCellS_eq_zero τ' N
  have hu1mem : (APrimeSmoothTransition.transitionMesh N)⁻¹ ∈
      Set.Icc (Gauss.firstCellS τ' N) (Gauss.firstCellT τ' N) := by
    rw [hs0]
    exact hmem
  let u1 : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N :=
    ⟨(APrimeSmoothTransition.transitionMesh N)⁻¹, hu1mem⟩
  have hmesh : APrimeSmoothTransition.transitionMesh N =
      (N : ℝ) ^ (248 : ℕ) := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    simp [APrimeSmoothTransition.transitionMesh, max_eq_right hn]
  have hu1eq : (u1 : ℝ) = (N : ℝ) ^ (-(248 : ℝ)) := by
    change (APrimeSmoothTransition.transitionMesh N)⁻¹ = _
    rw [hmesh, Real.rpow_neg (Nat.cast_nonneg N)]
    norm_num [Real.rpow_natCast]
  have huSupport : (u1 : ℝ) ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2) := by
    constructor
    · exact hpos.le
    · change (APrimeSmoothTransition.transitionMesh N)⁻¹ ≤
        (0 : ℝ) + (2 : ℝ) / APrimeSmoothTransition.transitionMesh N
      rw [zero_add, inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right (APrimeSupportRunning.mesh_pos N)).2
        (by norm_num)
  have hbound : nearBoundAt (τ' := τ') ν N u1 ω := by
    intro a₁ a₂
    exact hnear ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hkT (by rw [hw 1]; norm_num) u1 huSupport a₁ a₂
  exact ⟨ω, hω, u1, hpos, hu1eq, hkT, hw, hbound⟩

#print axioms highProb_good_of_inputs
#print axioms eventually_running_scales
#print axioms eventually_cNear_le_running
#print axioms eventually_near_on_active_support
#print axioms eGpm_zero
#print axioms exists_highProb_good
#print axioms exists_positive_active_sample

end RBM.APrimeFirstCellEGNearRunning
