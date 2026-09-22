/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGFar
import RBM1D.Gauss.APrimeFirstCellAllTimeNearSources
import RBM1D.Gauss.APrimeFirstCellQVRunningProfile

/-!
# Active-support running far-output Green drift in the first cell
-/

namespace RBM.APrimeFirstCellEGFarRunning

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- T400's all-time averaged sources and T395's active-support event, at one
literal value of the first-cell grid parameter. -/
def good (τ' ζ₁ ζ₃ : ℝ) (N : ℕ) : Set (Ω d) :=
  APrimeFirstCellAllTimeNearSources.good τ' ζ₁ ζ₃ N ∩
    APrimeFirstCellSourceSupport.jointEvent τ' ζ₃ N

theorem measurableSet_good {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ : ℝ) (N : ℕ) : MeasurableSet (good τ' ζ₁ ζ₃ N) :=
  (APrimeFirstCellAllTimeNearSources.measurableSet_good hτ' ζ₁ ζ₃ N).inter
    (APrimeFirstCellSourceSupport.measurableSet_jointEvent τ' ζ₃ N)

theorem highProb_good_of_inputs {τ' : ℝ} (hτ' : 0 < τ')
    (h1 : Step1.Hyp (sample d) 0 (firstCellS τ') (firstCellT τ'))
    (hll : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ') firstCellPsi)
    (h4 : firstCellRawLoopDom τ' 4) (h6 : firstCellRawLoopDom τ' 6)
    {ζ₁ ζ₃ : ℝ} (hζ₁ : 0 < ζ₁) (hζ₃ : 0 < ζ₃) :
    HighProb (P d) (good τ' ζ₁ ζ₃) :=
  (APrimeFirstCellAllTimeNearSources.highProb_good_of_inputs
    hτ' h1 hll h4 h6 hζ₁ hζ₃).inter
      (APrimeFirstCellSourceSupport.highProb_jointEvent_at
        hτ' hζ₃ hll h4 h6)

private theorem running_mem_firstCell {τ' : ℝ} (hτ' : 0 < τ')
    {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    r ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  rw [APrimeSupportRunning.firstS_eq]
  exact ⟨hr.1, hr.2.trans htop.2⟩

/-- Both orientations of (5.57), at every running time, follow from the
all-time `firstCellDelta` component of the same event. -/
theorem block_averages_on_good {τ' ζ₁ ζ₃ : ℝ} {N : ℕ} {ω : Ω d}
    (hω : ω ∈ good τ' ζ₁ ζ₃ N)
    (u : TimeIcc (firstCellS τ') (firstCellT τ') N) :
    (∀ (x y : ZMod (d.L N)) (p : ZMod (d.L N) × Fin (d.W N)),
      p.1 = y →
      ∑ r : ZMod (d.L N) × Fin (d.W N),
        Lemma57.blkW (d.L N) (d.W N) r x *
          ‖green (Hflow d N u ω) (zt 0 u) r p‖ ≤
        firstCellDelta N + (d.W N : ℝ)⁻¹) ∧
    (∀ (x y : ZMod (d.L N)) (r : ZMod (d.L N) × Fin (d.W N)),
      r.1 = x →
      ∑ p : ZMod (d.L N) × Fin (d.W N),
        Lemma57.blkW (d.L N) (d.W N) p y *
          ‖green (Hflow d N u ω) (zt 0 u) r p‖ ≤
        firstCellDelta N + (d.W N : ℝ)⁻¹) := by
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  have hGE : GoodEvent (green (Hflow d N u ω) (zt 0 u))
      (mE 0) (firstCellDelta N) := hω.2.1.2 u u.property
  have hm : ‖mE 0‖ = 1 := norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)
  constructor
  · intro x y p _
    exact APrimeFirstCellEGFar.goodEvent_column_block_average hGE hm x p
  · intro x y r _
    exact APrimeFirstCellEGFar.goodEvent_row_block_average hGE hm y r

/-- The simultaneous averaged source from T400 gives the actual running
`eGpm` prefactor `κ₁ = 2 N^ζ₁ (ell_u/ell_0)`. -/
theorem norm_eGpm_running_bound {τ' ζ₁ ζ₃ : ℝ} {N : ℕ} {ω : Ω d}
    (hω : ω ∈ good τ' ζ₁ ζ₃ N)
    (u : TimeIcc (firstCellS τ') (firstCellT τ') N)
    (havg : ∀ σ (b : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig (Hflow d N u ω) (zt 0 u) σ -
        mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ ζ₁ *
          ((B.ell N u / B.ell N (firstCellS τ' N)) *
            (B.scale 0 N u)⁻¹))
    (a₁ a₂ : ZMod (d.L N)) :
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
      (Hflow d N u ω) (zt 0 u) a₁ a₂‖ ≤
      (2 * (N : ℝ) ^ ζ₁ *
        (B.ell N u / B.ell N (firstCellS τ' N))) *
        (B.ell N u * etaT 0 u)⁻¹ *
        ∑ b : ZMod (d.L N),
          ‖gloop (d.L N) (d.W N) (Hflow d N u ω) (zt 0 u)
            ⟨[false, true, true], [a₂, b, a₁]⟩‖ := by
  have hu1 : (u : ℝ) < 1 :=
    u.property.2.trans_lt ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hℓ0 : 0 < B.ell N u :=
    (one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega)
      (by rw [← firstCellS_eq_zero τ' N]; exact u.property.1) hu1).trans_lt'
      (by norm_num)
  have hη0 : 0 < etaT 0 u := etaT_pos_of_lt_one (by norm_num) hu1
  have hbase := EGDef.norm_eGpm_le (d.three_le_L N)
    (Hflow_isHermitian d N u ω) (mSigma 0) havg a₁ a₂
  have hcoef :
      2 * (d.W N : ℝ) *
        ((N : ℝ) ^ ζ₁ *
          ((B.ell N u / B.ell N (firstCellS τ' N)) *
            (B.scale 0 N u)⁻¹)) =
      (2 * (N : ℝ) ^ ζ₁ *
        (B.ell N u / B.ell N (firstCellS τ' N))) *
        (B.ell N u * etaT 0 u)⁻¹ := by
    rw [show B.scale 0 N u =
      (d.W N : ℝ) * B.ell N u * etaT 0 u from rfl]
    field_simp
  rw [hcoef] at hbase
  exact hbase

/-- The exact far-output branch at one running time.  The three rows are kept
separate: `cFar·J·κ₂`, `168·J^(3/2)/A`, and the literal `D=60` spatial floor. -/
theorem norm_eGpm_far_running_bound {τ' ζ₁ ζ₃ : ℝ} {N : ℕ} {ω : Ω d}
    (hω : ω ∈ good τ' ζ₁ ζ₃ N)
    (u : TimeIcc (firstCellS τ') (firstCellT τ') N)
    (havg : ∀ σ (b : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig (Hflow d N u ω) (zt 0 u) σ -
        mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ ζ₁ *
          ((B.ell N u / B.ell N (firstCellS τ' N)) *
            (B.scale 0 N u)⁻¹))
    (hW : 1 ≤ (d.W N : ℝ)) (hℓ : 1 ≤ B.ell N u)
    (hη : 0 < etaT 0 u) (hN : 1 ≤ (N : ℝ))
    (hratio : 0 ≤ B.ell N u / B.ell N (firstCellS τ' N))
    (a₁ a₂ : ZMod (d.L N))
    (hfar : ellStar (d.W N : ℝ) (B.ell N u) ≤
      (zdist (d.L N) (a₂ - a₁) : ℝ)) :
    let ℓ := B.ell N u
    let η := etaT 0 u
    let A := (d.W N : ℝ) * ℓ * η
    let J := APrimeSupportRunning.jG N u ω
    let κ₁ := 2 * (N : ℝ) ^ ζ₁ *
      (ℓ / B.ell N (firstCellS τ' N))
    let κ₂ := firstCellDelta N + (d.W N : ℝ)⁻¹
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
      (Hflow d N u ω) (zt 0 u) a₁ a₂‖ ≤
      η⁻¹ * κ₁ *
        (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
          168 * J * Real.sqrt J * A⁻¹ +
          J * Real.sqrt J * (d.L N : ℝ) *
            Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) *
        tailT (d.W N : ℝ) ℓ η 60 (zdist (d.L N) (a₂ - a₁)) := by
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  let ℓ := B.ell N u
  let η := etaT 0 u
  let A := (d.W N : ℝ) * ℓ * η
  let J := APrimeSupportRunning.jG N u ω
  let κ₁ := 2 * (N : ℝ) ^ ζ₁ *
    (ℓ / B.ell N (firstCellS τ' N))
  let κ₂ := firstCellDelta N + (d.W N : ℝ)⁻¹
  let H := Hflow d N u ω
  let z := zt 0 u
  let Gm := APrimeJG.gmBlk (sample d) 0 N u ω
  let L2 : ZMod (d.L N) → ZMod (d.L N) → ℝ :=
    fun x y => (gloop (d.L N) (d.W N) H z
      ⟨[true, false], [x, y]⟩).re
  let L3 : ZMod (d.L N) → ℝ := fun b =>
    ‖gloop (d.L N) (d.W N) H z
      ⟨[false, true, true], [a₂, b, a₁]⟩‖
  have hWpos : (0 : ℝ) < (d.W N : ℝ) := by linarith
  have hJ : 1 ≤ J :=
    APrimeJG.one_le_jG (sample d) 0 N u ω hWpos
  have hJ0 : 0 ≤ J := by linarith
  have hκ₁ : 0 ≤ κ₁ := by dsimp [κ₁]; positivity
  have hκ₂ : 0 ≤ κ₂ := by
    dsimp [κ₂]
    unfold firstCellDelta firstCellPsi
    positivity
  have hGm : ∀ x y, 0 ≤ Gm x y :=
    APrimeJG.gmBlk_nonneg (sample d) 0 N u ω
  have h531 : ∀ x y : ZMod (d.L N),
      ellStar (d.W N : ℝ) ℓ / 2 ≤ (zdist (d.L N) (x - y) : ℝ) →
      L2 x y ≤ J * tailT (d.W N : ℝ) ℓ η 60
        (zdist (d.L N) (x - y)) := by
    intro x y hxy
    exact (APrimeFirstCellEGFar.two_loop_re_le_gsqBlk
      (sample d) 0 N u ω x y).trans
        (APrimeJG.gsqBlk_le_jG_mul_tailT
          (sample d) 0 N u ω hWpos x y hxy)
  have h42 : ∀ x y : ZMod (d.L N),
      ellStar (d.W N : ℝ) ℓ / 2 ≤ (zdist (d.L N) (x - y) : ℝ) →
      Gm x y ≤ Real.sqrt J *
        Real.sqrt (tailT (d.W N : ℝ) ℓ η 60
          (zdist (d.L N) (x - y))) := by
    intro x y hxy
    have h := APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail
      (sample d) 0 N u ω (ℓu := ℓ) (ηu := η) (D := 60) x y hxy
    rw [Real.sqrt_mul hJ0] at h
    convert h using 1 <;> simp only [Gm, J, APrimeSupportRunning.jG,
      Gauss.band_W, Gauss.band_L] <;> rfl
  have h557 := block_averages_on_good hω u
  have h558a : ∀ b, (zdist (d.L N) (a₂ - b) : ℝ) ≤
      ellStar (d.W N : ℝ) ℓ / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * κ₂ := by
    intro b _
    exact Lemma57.gloop_h558a' (d.L N) (d.W N)
      (Hflow_isHermitian d N u ω) a₂ a₁ b hκ₂
      (h557.1 a₂ b) (h557.2 a₂ b)
  have h558b : ∀ b, (zdist (d.L N) (a₁ - b) : ℝ) ≤
      ellStar (d.W N : ℝ) ℓ / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 b a₂) * κ₂ := by
    intro b _
    exact Lemma57.gloop_h558b' (d.L N) (d.W N)
      (Hflow_isHermitian d N u ω) a₂ a₁ b hκ₂
      (h557.1 b a₁) (h557.2 b a₁)
  have h560 : ∀ b, L3 b ≤ Gm a₂ b * Gm a₁ b * Gm a₂ a₁ := by
    intro b
    exact APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk
      (sample d) 0 N u ω a₁ a₂ b
  have hEG :
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0) H z a₁ a₂‖ ≤
        κ₁ * (ℓ * η)⁻¹ * ∑ b : ZMod (d.L N), L3 b := by
    exact norm_eGpm_running_bound hω u havg a₁ a₂
  have hbase := Lemma57.eG_far_le (d.L N) hW hℓ hη hJ hfar
    hκ₁ hκ₂ hGm h531 h42 h558a h558b h560 hEG
  convert hbase using 1 <;> simp only [A, mul_add, add_mul] <;> ring

/-- First checkpoint: on one event and positive active-prefix support, the
exact running far inequality holds for every real prefix time and every far
output pair.  The same sample also has `J ≤ N^(1/8)`. -/
theorem eventually_running_far_exact {τ' ζ₁ ζ₃ : ℝ}
    (hτ' : 0 < τ') (hζ₁ : 0 < ζ₁) :
    ∀ᶠ N : ℕ in atTop, ∀ N0 p k m : ℕ,
      N0 ≤ N → 1 ≤ p → 1 ≤ m → 1 ≤ k →
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ ω ∈ good τ' ζ₁ ζ₃ N,
      0 < APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
        N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
      ∀ a₁ a₂ : ZMod (d.L N),
      ellStar (d.W N : ℝ) (B.ell N r) ≤
        (zdist (d.L N) (a₂ - a₁) : ℝ) →
        let ℓ := B.ell N r
        let η := etaT 0 r
        let A := (d.W N : ℝ) * ℓ * η
        let J := APrimeSupportRunning.jG N r ω
        let κ₁ := 2 * (N : ℝ) ^ ζ₁ *
          (ℓ / B.ell N (firstCellS τ' N))
        let κ₂ := firstCellDelta N + (d.W N : ℝ)⁻¹
        J ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
        ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
          η⁻¹ * κ₁ *
            (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
              168 * J * Real.sqrt J * A⁻¹ +
              J * Real.sqrt J * (d.L N : ℝ) *
                Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ) *
            tailT (d.W N : ℝ) ℓ η 60 (zdist (d.L N) (a₂ - a₁)) := by
  filter_upwards [
    APrimeFirstCellAllTimeNearSources.eventually_avg_oneLoop_on_good hζ₁ ζ₃,
    APrimeSupportRunning.eventually_jG_le_eighth_on_support hτ',
    APrimeFirstCellQVRunningProfile.eventually_running_scales]
    with N havg hcap hscales
  intro N0 p k m hN0 hp hm hk hkT ω hω hw r hr a₁ a₂ hfar
  have hrmem := running_mem_firstCell hτ' hkT hr
  let u : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨r, hrmem⟩
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hrmem.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  obtain ⟨hWexp, hlog4, hlogD, hN, hηN, hA1, hAN, hWL, hNW⟩ :=
    hscales r hrhalf
  have hW : 1 ≤ (d.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hWexp
  have hr1 : r < 1 := by linarith [hrhalf.2]
  have hℓ : 1 ≤ B.ell N r :=
    one_le_ellHat (d.L N) (d.three_le_L N) hr.1 hr1
  have hη : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hℓs : B.ell N (firstCellS τ' N) = 1 := by
    rw [firstCellS_eq_zero]
    exact ellHat_zero (B.L N) (B.three_le_L N)
  have hratio : 0 ≤ B.ell N r / B.ell N (firstCellS τ' N) := by
    rw [hℓs, div_one]
    linarith
  constructor
  · exact hcap N0 p k m hN0 hp hm hk hkT ω hω.2.2 hw r hr
  · have hb := norm_eGpm_far_running_bound hω u
      (havg ω hω.1 u) hW hℓ hη hN hratio a₁ a₂ hfar
    simpa only [u] using hb

/-- Nonvacuity at the first active prefix: one sample of the same event has
the literal `k=2` weight equal to one, a positive second grid time, and the
antipodal far pair with the sharp running block cap. -/
def positiveFarPlateau (τ' ζ₁ ζ₃ : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ good τ' ζ₁ ζ₃ N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
      (firstCellT τ') 2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    (bHalf B N).1 ≠ (bHalf B N).2 ∧
    ellStar (d.W N : ℝ) (B.ell N u2) ≤
      (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) ∧
    APrimeSupportRunning.jG N u2 ω ≤ (N : ℝ) ^ ((1 : ℝ) / 8)

theorem positiveFarPlateau_of_good {τ' ζ₁ ζ₃ : ℝ}
    (hτ' : 0 < τ') (hp : HighProb (P d) (good τ' ζ₁ ζ₃)) :
    positiveFarPlateau τ' ζ₁ ζ₃ := by
  have hsupport : HighProb (P d)
      (APrimeSupportRunning.good τ' (1 / 100)) :=
    hp.mono (Eventually.of_forall fun N ω hω => hω.2.2)
  filter_upwards [hp.nonempty (by simp),
    APrimeSupportRunning.positive_plateau_on_good hτ'
      (by norm_num : (0 : ℝ) < 1 / 100) hsupport,
    APrimeFirstCellCommon.eventually_active_weight_two_one hτ'
      (by norm_num : (0 : ℝ) < 1 / 100),
    APrimeSupportRunning.eventually_jG_le_eighth_on_support hτ',
    twelve_ellStar_le_half_exampleGrow (t₀ := 1 / 2)
      (by norm_num) (by norm_num),
    eventually_ge_atTop 2] with N hne hplat hweight hcap hsep hN
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨_, _, _, _, hk, _⟩ := hplat
  have hnorm : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω.2.1.1.1.1
  have hw : ∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
      (firstCellT τ') 2 p N 2 N ω = 1 := by
    intro p
    have h := hweight ω hnorm p
    rw [APrimeSupportRunning.firstS_eq] at h
    exact h
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hmesh : 0 < APrimeSmoothTransition.transitionMesh N :=
    APrimeSupportRunning.mesh_pos N
  have hu2pos : 0 < u2 := by
    dsimp [u2]
    simp only [cutNetPt, Nat.cast_ofNat, zero_add]
    positivity
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hu2mem : u2 ∈ Set.Icc (0 : ℝ) (firstCellT τ' N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc hwin hmesh _
      (cutNetPt_mem_netFinset hk)
  have h12 : 12 * ellStar (d.W N : ℝ) (B.ell N u2) ≤
      ((d.L N / 2 : ℕ) : ℝ) := by
    change 12 * ellStar (Dims.growW N : ℝ)
      (ellHat (Dims.growL N) (u2 : ℂ)) ≤ ((Dims.growL N / 2 : ℕ) : ℝ)
    exact hsep u2 hu2pos
      (hu2mem.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2)
  have hstar : 0 ≤ ellStar (d.W N : ℝ) (B.ell N u2) := by
    apply Step2FarMart.ellStar_nonneg_of_one_le
    · exact_mod_cast B.one_le_W N
    · have hu21 : u2 < 1 :=
        hu2mem.2.trans_lt ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
      exact (one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega)
        hu2mem.1 hu21).trans' (by norm_num)
  have hdist :
      (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) =
        ((d.L N / 2 : ℕ) : ℝ) := by
    change (zdist (B.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) =
      ((B.L N / 2 : ℕ) : ℝ)
    exact zdist_bHalf B N
  have hfar : ellStar (d.W N : ℝ) (B.ell N u2) ≤
      (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) := by
    rw [hdist]
    linarith
  have hJ : APrimeSupportRunning.jG N u2 ω ≤
      (N : ℝ) ^ ((1 : ℝ) / 8) := by
    exact hcap 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hk ω hω.2.2 (by rw [hw 1]; norm_num) u2
        ⟨hu2pos.le, le_rfl⟩
  exact ⟨ω, hω, hk, hw, hu2pos, hu2mem.2,
    bHalf_fst_ne_snd B N, hfar, hJ⟩

/-- One T358 parameter is chosen before the two source losses.  At that same
parameter the running-far event is measurable, high probability, eventually
nonempty, and has the `k=2` same-sample far witness. -/
theorem exists_running_far_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
        (∀ N, MeasurableSet (good τ' ζ₁ ζ₃ N)) ∧
        HighProb (P d) (good τ' ζ₁ ζ₃) ∧
        (∀ᶠ N : ℕ in atTop, (good τ' ζ₁ ζ₃ N).Nonempty) ∧
        positiveFarPlateau τ' ζ₁ ζ₃ := by
  obtain ⟨τ', hτ', h1, hll, h4, h6⟩ :=
    firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₃
  have hp := highProb_good_of_inputs hτ' h1 hll h4 h6 hζ₁ hζ₃
  exact ⟨measurableSet_good hτ' ζ₁ ζ₃, hp, hp.nonempty (by simp),
    positiveFarPlateau_of_good hτ' hp⟩

#print axioms block_averages_on_good
#print axioms norm_eGpm_running_bound
#print axioms norm_eGpm_far_running_bound
#print axioms eventually_running_far_exact
#print axioms positiveFarPlateau_of_good
#print axioms exists_running_far_with_plateau

end RBM.APrimeFirstCellEGFarRunning
