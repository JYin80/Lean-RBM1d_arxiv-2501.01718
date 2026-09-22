/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellMovingSupport
import RBM1D.Gauss.APrimeFirstCellEGFarSmallRunning

/-!
# T418: same-event all-output running `eGpm` bound on the first cell

The near and far estimates are combined on the literal common event supplied
by T413.  The cutoff loss and the source loss remain distinct.
-/

namespace RBM.APrimeFirstCellEGAllOutputRunning

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The source loss used by T412 when its final exponent is `ν/2`. -/
noncomputable def sourceLoss (ν : ℝ) : ℝ :=
  APrimeFirstCellEGFarSmallRunning.sourceLoss (ν / 2)

/-- Reparameterization of T409 which makes its internal source loss exactly
the T412 source loss above. -/
noncomputable def nearExponent (ν : ℝ) : ℝ := 8 * sourceLoss ν

theorem sourceLoss_pos {ν : ℝ} (hν : 0 < ν) : 0 < sourceLoss ν := by
  unfold sourceLoss APrimeFirstCellEGFarSmallRunning.sourceLoss
  exact lt_min (by positivity) (by norm_num)

theorem sourceLoss_le_half (ν : ℝ) : sourceLoss ν ≤ 1 / 2 := by
  unfold sourceLoss APrimeFirstCellEGFarSmallRunning.sourceLoss
  exact (min_le_right _ _).trans (by norm_num)

theorem near_sourceLoss_eq (ν : ℝ) :
    APrimeFirstCellEGNearRunning.sourceLoss (nearExponent ν) = sourceLoss ν := by
  unfold APrimeFirstCellEGNearRunning.sourceLoss nearExponent
  rw [show 8 * sourceLoss ν / 8 = sourceLoss ν by ring]
  exact min_eq_left (sourceLoss_le_half ν)

theorem nearExponent_pos {ν : ℝ} (hν : 0 < ν) : 0 < nearExponent ν := by
  unfold nearExponent
  exact mul_pos (by norm_num) (sourceLoss_pos hν)

theorem nearExponent_le_half {ν : ℝ} (hν : 0 < ν) : nearExponent ν ≤ ν / 2 := by
  have hsource : sourceLoss ν ≤ (ν / 2) / 64 := by
    unfold sourceLoss APrimeFirstCellEGFarSmallRunning.sourceLoss
    exact min_le_left _ _
  unfold nearExponent
  nlinarith

/-- One literal T413 event supports both T409 and T412. -/
def good (τ' δ ν : ℝ) (N : ℕ) : Set (Ω d) :=
  APrimeFirstCellMovingSupport.commonEvent τ'
    (sourceLoss ν) (sourceLoss ν) (δ / 16) N

def allOutputBound (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ r ∈ Set.Icc (0 : ℝ)
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
      ∀ a₁ a₂ : ZMod (d.L N),
        ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
            (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
          (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
            (B.ell N r / B.ell N 0) ^ 3 *
              tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                (zdist (d.L N) (a₂ - a₁))

/-- On the same sample and active prefix, the near and far estimates cover
every output pair and every real running time, including `r = 0`. -/
theorem eventually_all_output_on_active_support {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν) : allOutputBound τ' δ ν := by
  have hnearExp : 0 < nearExponent ν := nearExponent_pos hν
  have hhalf : 0 < ν / 2 := by positivity
  filter_upwards [
    APrimeFirstCellEGNearRunning.eventually_near_on_active_support
      hτ' hnearExp,
    APrimeFirstCellEGFarSmallRunning.eventually_far_on_active_support
      hτ' hhalf,
    eventually_ge_atTop 1] with N hnear hfar hN
  intro ω hω N0 p k m hN0 hp hm hk hkT hw r hr a₁ a₂
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw100 : 0 < APrimeSupportRunning.weight (1 / 100)
      (firstCellT τ') N0 p N k m ω :=
    APrimeFirstCellMovingSupport.weight_pos_transfer hNr hδ hδ100 hw
  have hωnear : ω ∈ APrimeFirstCellEGNearRunning.good τ'
      (nearExponent ν) N := by
    apply APrimeFirstCellMovingSupport.commonEvent_to_near
    simpa only [good, near_sourceLoss_eq] using hω
  have hωfar : ω ∈ APrimeFirstCellEGFarSmallRunning.good τ' (ν / 2) N := by
    exact APrimeFirstCellMovingSupport.commonEvent_to_far hω
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans htop.2 |>.trans
      (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  have hrone : r < 1 := hrhalf.2.trans_lt (by norm_num)
  have hEll : 1 ≤ B.ell N r :=
    one_le_ellHat_of_nonneg (by
      change 1 ≤ d.L N
      exact (show 1 ≤ d.L N by have := d.three_le_L N; omega))
      hr.1 hrone
  have hEll0 : B.ell N 0 = 1 := ellHat_zero (B.L N) (B.three_le_L N)
  have hrr : 1 ≤ B.ell N r / B.ell N 0 := by
    rw [hEll0, div_one]
    exact hEll
  have hEta : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hrone
  have htail : 0 ≤ tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
      (zdist (d.L N) (a₂ - a₁)) := by
    apply tailT_nonneg
    exact_mod_cast (d.W_pos N).le
  by_cases hnearCase :
      (zdist (d.L N) (a₂ - a₁) : ℝ) ≤
        ellStar (d.W N : ℝ) (B.ell N r)
  · have hs0 : firstCellS τ' N = 0 := firstCellS_eq_zero τ' N
    let u : TimeIcc (firstCellS τ') (firstCellT τ') N := by
      refine ⟨r, ?_⟩
      rw [hs0]
      exact ⟨hr.1, hr.2.trans htop.2⟩
    have hb := hnear ω hωnear N0 p k m hN0 hp hm hk hkT hw100
      u (by simpa only [u] using hr) a₁ a₂
    calc
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
          (N : ℝ) ^ (nearExponent ν) * (etaT 0 r)⁻¹ *
            (B.ell N r / B.ell N 0) ^ 3 *
              tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                (zdist (d.L N) (a₂ - a₁)) := by
            simpa only [u, hs0, if_pos hnearCase, mul_one] using hb
      _ ≤ (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
            (B.ell N r / B.ell N 0) ^ 3 *
              tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                (zdist (d.L N) (a₂ - a₁)) := by
          have hexp : nearExponent ν ≤ ν :=
            (nearExponent_le_half hν).trans (by linarith)
          have hpow : (N : ℝ) ^ (nearExponent ν) ≤ (N : ℝ) ^ ν :=
            Real.rpow_le_rpow_of_exponent_le hNr hexp
          have hrest : 0 ≤ (etaT 0 r)⁻¹ *
              (B.ell N r / B.ell N 0) ^ 3 *
                tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                  (zdist (d.L N) (a₂ - a₁)) := by
            positivity
          calc
            (N : ℝ) ^ (nearExponent ν) * (etaT 0 r)⁻¹ *
                (B.ell N r / B.ell N 0) ^ 3 *
                  tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                    (zdist (d.L N) (a₂ - a₁)) =
                (N : ℝ) ^ (nearExponent ν) *
                  ((etaT 0 r)⁻¹ * (B.ell N r / B.ell N 0) ^ 3 *
                    tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                      (zdist (d.L N) (a₂ - a₁))) := by ring
            _ ≤ (N : ℝ) ^ ν *
                  ((etaT 0 r)⁻¹ * (B.ell N r / B.ell N 0) ^ 3 *
                    tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                      (zdist (d.L N) (a₂ - a₁))) :=
              mul_le_mul_of_nonneg_right hpow hrest
            _ = (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
                (B.ell N r / B.ell N 0) ^ 3 *
                  tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                    (zdist (d.L N) (a₂ - a₁)) := by ring
  · have hfarCase : ellStar (d.W N : ℝ) (B.ell N r) ≤
        (zdist (d.L N) (a₂ - a₁) : ℝ) :=
      (lt_of_not_ge hnearCase).le
    have hb := hfar ω hωfar N0 p k m hN0 hp hm hk hkT hw100
      r hr a₁ a₂ hfarCase
    calc
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N r ω) (zt 0 r) a₁ a₂‖ ≤
          (N : ℝ) ^ (ν / 2) * (etaT 0 r)⁻¹ *
            tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
              (zdist (d.L N) (a₂ - a₁)) := hb
      _ ≤ (N : ℝ) ^ ν * (etaT 0 r)⁻¹ * 1 *
            tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
              (zdist (d.L N) (a₂ - a₁)) := by
          have hpow : (N : ℝ) ^ (ν / 2) ≤ (N : ℝ) ^ ν :=
            Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
          have hrest : 0 ≤ (etaT 0 r)⁻¹ *
              tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                (zdist (d.L N) (a₂ - a₁)) :=
            mul_nonneg (inv_nonneg.mpr hEta.le) htail
          calc
            (N : ℝ) ^ (ν / 2) * (etaT 0 r)⁻¹ *
                tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                  (zdist (d.L N) (a₂ - a₁)) =
                (N : ℝ) ^ (ν / 2) * ((etaT 0 r)⁻¹ *
                  tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                    (zdist (d.L N) (a₂ - a₁))) := by ring
            _ ≤ (N : ℝ) ^ ν * ((etaT 0 r)⁻¹ *
                  tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                    (zdist (d.L N) (a₂ - a₁))) :=
              mul_le_mul_of_nonneg_right hpow hrest
            _ = (N : ℝ) ^ ν * (etaT 0 r)⁻¹ * 1 *
                tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                  (zdist (d.L N) (a₂ - a₁)) := by ring
      _ ≤ (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
            (B.ell N r / B.ell N 0) ^ 3 *
              tailT (d.W N : ℝ) (B.ell N r) (etaT 0 r) 60
                (zdist (d.L N) (a₂ - a₁)) := by
          have hpre : 0 ≤ (N : ℝ) ^ ν * (etaT 0 r)⁻¹ :=
            mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
              (inv_nonneg.mpr hEta.le)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (one_le_pow₀ hrr) hpre) htail

/-- Same-event nonvacuity at the first active prefix, now carrying the
all-output estimate at its positive time. -/
def positiveAllOutputPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ good τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    ∀ a₁ a₂ : ZMod (d.L N),
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N u2 ω) (zt 0 u2) a₁ a₂‖ ≤
        (N : ℝ) ^ ν * (etaT 0 u2)⁻¹ *
          (B.ell N u2 / B.ell N 0) ^ 3 *
            tailT (d.W N : ℝ) (B.ell N u2) (etaT 0 u2) 60
              (zdist (d.L N) (a₂ - a₁))

theorem positiveAllOutputPlateau_of_common {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν)
    (hplat : APrimeFirstCellMovingSupport.positivePlateau τ' δ
      (sourceLoss ν) (sourceLoss ν)) :
    positiveAllOutputPlateau τ' δ ν := by
  filter_upwards [hplat,
    eventually_all_output_on_active_support hτ' hδ hδ100 hν,
    eventually_ge_atTop 2] with N hplat hall hN
  dsimp only [APrimeFirstCellMovingSupport.positivePlateau] at hplat
  obtain ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, _hsource, _hJ⟩ := hplat
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hbound : ∀ a₁ a₂ : ZMod (d.L N),
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
          (Hflow d N u2 ω) (zt 0 u2) a₁ a₂‖ ≤
        (N : ℝ) ^ ν * (etaT 0 u2)⁻¹ *
          (B.ell N u2 / B.ell N 0) ^ 3 *
            tailT (d.W N : ℝ) (B.ell N u2) (etaT 0 u2) 60
              (zdist (d.L N) (a₂ - a₁)) := by
    intro a₁ a₂
    exact hall ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
      (by norm_num) hk (by rw [hwδ 1]; norm_num) u2
      ⟨hu2pos.le, le_rfl⟩ a₁ a₂
  exact ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, hbound⟩

/-- One literal first-cell parameter supplies a measurable high-probability
event, the uniform all-output estimate, and a positive-time resident of that
same event and cutoff support. -/
theorem exists_good_with_all_output :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet (good τ' δ ν N)) ∧
        HighProb (P d) (good τ' δ ν) ∧
        allOutputBound τ' δ ν ∧
        positiveAllOutputPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hcommon⟩ :=
    APrimeFirstCellMovingSupport.exists_commonEvent_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  have hζ : 0 < sourceLoss ν := sourceLoss_pos hν
  obtain ⟨hmeas, hp, _hcons, hplat⟩ :=
    hcommon δ hδ hδ100 (sourceLoss ν) (sourceLoss ν) hζ hζ
  exact ⟨hmeas, hp,
    eventually_all_output_on_active_support hτ' hδ hδ100 hν,
    positiveAllOutputPlateau_of_common hτ' hδ hδ100 hν hplat⟩

#print axioms near_sourceLoss_eq
#print axioms eventually_all_output_on_active_support
#print axioms positiveAllOutputPlateau_of_common
#print axioms exists_good_with_all_output

end RBM.APrimeFirstCellEGAllOutputRunning
