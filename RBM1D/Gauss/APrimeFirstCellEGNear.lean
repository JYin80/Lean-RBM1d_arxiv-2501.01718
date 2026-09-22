/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellNearSources
import RBM1D.Gauss.APrimeEGNearScaled

/-!
# Actual near-output `eG` at the first positive cut-net time
-/

namespace RBM.APrimeFirstCellEGNear

open Filter Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- All deterministic first-time scales and the block multiplier cap hold on
the same event that supplies the one-loop and raw three-loop estimates. -/
theorem eventually_source_scales {τ' : ℝ} (hτ' : 0 < τ') (ζ₁ ζ₃ : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      let u := APrimeFirstCellNearSources.sourceTime τ' N
      0 < u ∧
      u = APrimeFirstCellJGCap.firstTime N ∧
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
      4 * (1 : ℝ) ≤ (d.W N : ℝ) ∧
      ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
        0 ≤ APrimeJG.jG (Gauss.sample d) 0 N u ω
          (B.ell N u) (etaT 0 u) 60 ∧
        APrimeJG.jG (Gauss.sample d) 0 N u ω
          (B.ell N u) (etaT 0 u) 60 ≤ (N : ℝ) := by
  filter_upwards [APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime hτ',
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    APrimeFirstCellNearSources.eventually_jointEvent_jG_cap hτ' ζ₁ ζ₃]
    with N htime hscale hJ
  rcases hscale with ⟨hW, hlog4, hlog, hN, hηN, hA1, hA, hWL, hNW⟩
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  have hu0 : 0 ≤ u := htime.2.le
  have hu1 : u < 1 := APrimeFirstCellNearSources.sourceTime_lt_one hτ' N
  have hℓ : 1 ≤ B.ell N u :=
    one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega) hu0 hu1
  have hs : Gauss.firstCellS τ' N = 0 := by
    unfold Gauss.firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hℓs : B.ell N (Gauss.firstCellS τ' N) = 1 := by
    rw [hs]
    exact ellHat_zero (B.L N) (B.three_le_L N)
  have hηpos : 0 < etaT 0 u := etaT_pos_of_lt_one (by norm_num) hu1
  have hηinv : (etaT 0 u)⁻¹ ≤ (N : ℝ) := by
    change (etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N))⁻¹ ≤ (N : ℝ)
    rw [htime.1]
    have hηpos' : 0 < etaT 0 (APrimeFirstCellJGCap.firstTime N) := by
      rw [← htime.1]
      exact hηpos
    have h := (inv_le_inv₀ hηpos'
      (by positivity : (0 : ℝ) < (N : ℝ)⁻¹)).2 hηN
    simpa using h
  have hL : (d.L N : ℝ) ≤ (N : ℝ) := by
    have hW1 : (1 : ℝ) ≤ d.W N :=
      (Real.one_le_exp (by norm_num)).trans hW
    have hL0 : (0 : ℝ) ≤ d.L N := Nat.cast_nonneg _
    nlinarith
  have hW4 : 4 * (1 : ℝ) ≤ (d.W N : ℝ) := by
    have hp : (4 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp (4 : ℝ)]
    have hexp : Real.exp 4 ≤ (d.W N : ℝ) := by
      have hwpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
      change 4 ≤ Real.log (d.W N : ℝ) at hlog4
      simpa only [Real.exp_log hwpos] using (Real.exp_le_exp.mpr hlog4)
    nlinarith
  refine ⟨htime.2, htime.1, hW, hlog4, hlog, hN, hℓ, hℓs, ?_,
    hηpos, hηinv, ?_, ?_, hL, hNW, hW4, ?_⟩
  · rw [hℓs, div_one]
    exact hℓ
  · simpa only [u, htime.1] using hA1
  · simpa only [u, htime.1] using hA
  · intro ω hω
    have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast B.W_pos N
    exact ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (APrimeJG.one_le_jG (Gauss.sample d) 0 N u ω
        (ℓu := B.ell N u) (ηu := etaT 0 u) (D := 60) hWpos),
      hJ ω hω⟩

/-- The length-three row of the common source event, at its actual sample and
actual output orientation. -/
theorem raw_three_source_bound {τ' ζ₁ ζ₃ : ℝ} (hτ' : 0 < τ')
    {N : ℕ} {ω : Gauss.Ω d}
    (hω : ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N)
    (a₁ a₂ b : ZMod (d.L N)) :
    ‖gloop (d.L N) (d.W N)
        (Gauss.Hflow d N (APrimeFirstCellNearSources.sourceTime τ' N) ω)
        (zt 0 (APrimeFirstCellNearSources.sourceTime τ' N))
        ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (N : ℝ) ^ ζ₃ *
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N) /
          B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
        (((d.W N : ℝ) *
          B.ell N (APrimeFirstCellNearSources.sourceTime τ' N) *
          etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N)) ^ 2)⁻¹ := by
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  let v : LoopData (d.L N) 3 := (![false, true, true], ![a₂, b, a₁])
  have hu : u ∈ Set.Icc (Gauss.firstCellS τ' N) (Gauss.firstCellT τ' N) :=
    APrimeFirstCellNearSources.sourceTime_mem hτ' N
  let p : TimeIcc (Gauss.firstCellS τ') (Gauss.firstCellT τ') N ×
      LoopData (d.L N) 3 := (⟨u, hu⟩, v)
  have hraw := (APrimeFirstCellNearSources.jointEvent_near_sources hω).2 p
  have hidx : v.idx = (⟨[false, true, true], [a₂, b, a₁]⟩ :
      LoopIdx (ZMod (d.L N))) := by
    simp [v, LoopData.idx, List.ofFn_succ]
  have hRhs : Step1.aprioriRhs B 0
      (Gauss.firstCellS τ') (Gauss.firstCellT τ') 3 N p ω =
      (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ 2 *
        (((d.W N : ℝ) * B.ell N u * etaT 0 u) ^ 2)⁻¹ := by
    change (B.ell N u / B.ell N (Gauss.firstCellS τ' N)) ^ (3 - 1) *
      (B.scale 0 N u)⁻¹ ^ (3 - 1) = _
    simp only [Nat.reduceSub]
    rw [show B.scale 0 N u = (d.W N : ℝ) * B.ell N u * etaT 0 u from rfl]
    rw [inv_pow]
  rw [hRhs, Gauss.sample_Lval, hidx] at hraw
  simpa only [p, u, mul_assoc] using hraw

/-- T379's two-charge trace event controls the actual `eGpm` drift without
changing either output label. -/
theorem norm_eGpm_source_bound {τ' ζ₁ ζ₃ : ℝ} (hτ' : 0 < τ')
    {N : ℕ} {ω : Gauss.Ω d}
    (hω : ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N)
    (hℓ : 0 < B.ell N (APrimeFirstCellNearSources.sourceTime τ' N))
    (hη : 0 < etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N))
    (a₁ a₂ : ZMod (d.L N)) :
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
      (Gauss.Hflow d N (APrimeFirstCellNearSources.sourceTime τ' N) ω)
      (zt 0 (APrimeFirstCellNearSources.sourceTime τ' N)) a₁ a₂‖ ≤
      (2 * (N : ℝ) ^ ζ₁ *
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N) /
          B.ell N (Gauss.firstCellS τ' N))) *
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N) *
          etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N))⁻¹ *
        ∑ b : ZMod (d.L N),
          ‖gloop (d.L N) (d.W N)
            (Gauss.Hflow d N (APrimeFirstCellNearSources.sourceTime τ' N) ω)
            (zt 0 (APrimeFirstCellNearSources.sourceTime τ' N))
            ⟨[false, true, true], [a₂, b, a₁]⟩‖ := by
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  let r := B.ell N u / B.ell N (Gauss.firstCellS τ' N)
  let c := (N : ℝ) ^ ζ₁ * (r * (B.scale 0 N u)⁻¹)
  have hone : ∀ σ (b : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) σ -
        mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤ c :=
    APrimeFirstCellNearSources.jointEvent_oneLoop_paper_scale hτ' hω
  have hbase := EGDef.norm_eGpm_le (d.three_le_L N)
    (Gauss.Hflow_isHermitian d N u ω) (mSigma 0) hone a₁ a₂
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hcoef : 2 * (d.W N : ℝ) * c =
      (2 * (N : ℝ) ^ ζ₁ * r) * (B.ell N u * etaT 0 u)⁻¹ := by
    dsimp [c]
    rw [show B.scale 0 N u = (d.W N : ℝ) * B.ell N u * etaT 0 u from rfl]
    field_simp
    have hWsame : (Gauss.Dims.growW N : ℝ) = (d.W N : ℝ) := rfl
    rw [hWsame]
    ring
  rw [hcoef] at hbase
  simpa only [u, r, mul_assoc] using hbase

/-- The actual Gaussian near-output branch of (5.35), on the single T379
source event. Both stochastic losses and the near indicator remain visible. -/
theorem eventually_near_indicator_le {τ' : ℝ} (hτ' : 0 < τ')
    {ζ₁ ζ₃ : ℝ} (hζ₁0 : 0 < ζ₁) (hζ₁1 : ζ₁ ≤ 1) (hζ₃ : 0 < ζ₃) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
        ∀ a₁ a₂ : ZMod (d.L N),
          let u := APrimeFirstCellNearSources.sourceTime τ' N
          let ℓu := B.ell N u
          let ℓs := B.ell N (Gauss.firstCellS τ' N)
          let ηu := etaT 0 u
          let r := ℓu / ℓs
          let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
          ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
              (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
              (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0) ≤
            (2 * (N : ℝ) ^ (ζ₁ + ζ₃) * ηu⁻¹ * r ^ 3 *
                Lemma57.cNear (d.W N : ℝ) ℓu *
                tailT (d.W N : ℝ) ℓu ηu 60 dd +
              (d.W N : ℝ)⁻¹ *
                APrimeDriftNearAbsorb.nearRate (d.W N : ℝ) ℓu ηu 60 r dd) *
              (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0) := by
  filter_upwards [eventually_source_scales hτ' ζ₁ ζ₃] with N hscales ω hω a₁ a₂
  dsimp only at hscales ⊢
  rcases hscales with ⟨hu0, htime, hW, hlog4, hlog, hN, hℓ, hℓs,
    hr, hη, hηinv, hA1, hA, hL, hNW, hW4, hJcap⟩
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  let ℓu := B.ell N u
  let ℓs := B.ell N (Gauss.firstCellS τ' N)
  let ηu := etaT 0 u
  let r := ℓu / ℓs
  let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
  let L3 : ZMod (d.L N) → ℝ := fun b =>
    ‖gloop (d.L N) (d.W N) (Gauss.Hflow d N u ω) (zt 0 u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖
  let EG : ℝ := ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
    (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖
  have hJ := hJcap ω hω
  have hL3 : ∀ b, L3 b ≤ 1 * (N : ℝ) ^ ζ₃ * r ^ 2 *
      (((d.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹ := by
    intro b
    have hb := raw_three_source_bound hτ' hω a₁ a₂ b
    simpa only [one_mul, mul_assoc, L3, r, ℓu, ℓs, ηu, u] using hb
  have hEG : EG ≤ (2 * (1 : ℝ) * (N : ℝ) ^ ζ₁ * r) *
      (ℓu * ηu)⁻¹ * ∑ b : ZMod (d.L N), L3 b := by
    have hb := norm_eGpm_source_bound hτ' hω (by linarith : 0 < ℓu) hη a₁ a₂
    simpa [EG, L3, r, ℓu, ℓs, ηu, u, mul_assoc] using hb
  have h554 : dd ≤ ellStar (d.W N : ℝ) ℓu →
      ∀ b, Lemma57.ellStarStar (d.W N : ℝ) ℓu <
        (zdist (d.L N) (a₂ - b) : ℝ) →
        L3 b ≤ ηu⁻¹ *
          APrimeJG.jG (Gauss.sample d) 0 N u ω ℓu ηu 60 *
          tailT (d.W N : ℝ) ℓu ηu 60
            (APrimeDriftNearAbsorb.gap (d.W N : ℝ) ℓu) := by
    intro hnear b hfar
    have hb := APrimeDriftNearTriple.gaussian_three_near_far_le d
      (by norm_num : |(0 : ℝ)| < 2) N
      (APrimeFirstCellNearSources.sourceTime_lt_one hτ' N) ω
      (D := 60) (by linarith : 0 < ℓu) hlog4 a₁ a₂ b hnear hfar
    simpa only [L3, u, ℓu, ηu, APrimeDriftNearAbsorb.gap,
      Gauss.sample_H] using hb
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  have hsplit := APrimeEGNearScaled.eG_near_indicator_le_scaled_absorb
    (d.L N) hW hℓ (by
      change 0 < B.ell N (Gauss.firstCellS τ' N)
      rw [hℓs]
      norm_num) hη hN
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    hζ₁0.le hζ₁1 hζ₃.le hJ.1 hJ.2 hr hA1 hA hL hηinv hNW
    hlog hW4 a₂ a₁ hL3 h554 hEG
  simpa only [one_mul, mul_one, L3, EG, dd, r, ℓu, ℓs, ηu, u] using hsplit

/-- The principal `cNear` loss and the absorbed `W⁻¹` remainder share the
same near profile. -/
theorem eventually_near_indicator_le_factored {τ' : ℝ} (hτ' : 0 < τ')
    {ζ₁ ζ₃ : ℝ} (hζ₁0 : 0 < ζ₁) (hζ₁1 : ζ₁ ≤ 1) (hζ₃ : 0 < ζ₃) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
        ∀ a₁ a₂ : ZMod (d.L N),
          let u := APrimeFirstCellNearSources.sourceTime τ' N
          let ℓu := B.ell N u
          let ℓs := B.ell N (Gauss.firstCellS τ' N)
          let ηu := etaT 0 u
          let r := ℓu / ℓs
          let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
          ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
              (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
              (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0) ≤
            (2 * (N : ℝ) ^ (ζ₁ + ζ₃) * Lemma57.cNear (d.W N : ℝ) ℓu +
                (d.W N : ℝ)⁻¹) *
              ηu⁻¹ * r ^ 3 * tailT (d.W N : ℝ) ℓu ηu 60 dd *
              (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0) := by
  filter_upwards [eventually_near_indicator_le hτ' hζ₁0 hζ₁1 hζ₃]
    with N hN ω hω a₁ a₂
  have hb := hN ω hω a₁ a₂
  dsimp only at hb ⊢
  convert hb using 1
  unfold APrimeDriftNearAbsorb.nearRate
  ring

/-- Event-local, all-output near branch at the single positive source time. -/
def nearBound (τ' ζ₁ ζ₃ : ℝ) (N : ℕ) (ω : Gauss.Ω d) : Prop :=
  ∀ a₁ a₂ : ZMod (d.L N),
    let u := APrimeFirstCellNearSources.sourceTime τ' N
    let ℓu := B.ell N u
    let ℓs := B.ell N (Gauss.firstCellS τ' N)
    let ηu := etaT 0 u
    let r := ℓu / ℓs
    let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
        (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
        (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0) ≤
      (2 * (N : ℝ) ^ (ζ₁ + ζ₃) * Lemma57.cNear (d.W N : ℝ) ℓu +
          (d.W N : ℝ)⁻¹) *
        ηu⁻¹ * r ^ 3 * tailT (d.W N : ℝ) ℓu ηu 60 dd *
        (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0)

/-- One parameter chosen before the source losses gives a measurable high
probability event on which the actual near bound holds for every output pair.
The event has an actual sample at a strictly positive first cut-net time. -/
theorem exists_highProb_near_event :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → ζ₁ ≤ 1 → 0 < ζ₃ →
        HighProb (Gauss.P d)
          (APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃) ∧
        ∀ᶠ N : ℕ in atTop,
          0 < APrimeFirstCellNearSources.sourceTime τ' N ∧
          APrimeFirstCellNearSources.sourceTime τ' N =
            APrimeFirstCellJGCap.firstTime N ∧
          MeasurableSet (APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N) ∧
          (∃ ω : Gauss.Ω d,
            ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N) ∧
          ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
            nearBound τ' ζ₁ ζ₃ N ω := by
  obtain ⟨τ', hτ', hHP⟩ :=
    APrimeFirstCellNearSources.exists_highProb_jointEvent
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₁1 hζ₃
  have hp := hHP ζ₁ ζ₃ hζ₁ hζ₃
  have hne := HighProb.nonempty (by simp) hp
  have hnear := eventually_near_indicator_le_factored hτ' hζ₁ hζ₁1 hζ₃
  refine ⟨hp, ?_⟩
  filter_upwards [APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime hτ',
    hne, hnear] with N htime hne hnear
  refine ⟨htime.2, htime.1,
    APrimeFirstCellNearSources.jointEvent_measurable hτ' ζ₁ ζ₃ N,
    hne, ?_⟩
  intro ω hω
  exact hnear ω hω

#print axioms exists_highProb_near_event
#print axioms eventually_near_indicator_le_factored

#print axioms eventually_source_scales
#print axioms raw_three_source_bound
#print axioms norm_eGpm_source_bound
#print axioms eventually_near_indicator_le

end RBM.APrimeFirstCellEGNear
