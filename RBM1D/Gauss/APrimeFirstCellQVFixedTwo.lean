/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVSharpMoving

/-!
# T437: full-root QV monotonicity and the fixed-two moving adapter

The near part of `rootProfile` is independent of the block parameter.  Its
far part is monotone in that parameter, and the endpoint kernel multiplying
the far square root is nonnegative.  Thus T436's actual block cap replaces
the running block parameter by the literal constant two without dropping
any row of the full moving profile.
-/

namespace RBM.APrimeFirstCellQVFixedTwo

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The endpoint kernel multiplying the far square-root rate is nonnegative. -/
theorem endpointKernel_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω) (E : ℝ) (N : ℕ) (u v D : ℝ)
    (a : LoopArg (B.L N) 2) (hW : 0 ≤ (B.W N : ℝ)) :
    0 ≤ ((1 - u) / (1 - v)) ^ 2 *
      Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
      Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
  have hT : 0 ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg hW (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 ≤ Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  positivity

/-- The literal full root profile is nonnegative. -/
theorem rootProfile_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω) (E : ℝ) (N : ℕ)
    (u v D ellSource J Smax ε : ℝ) (a : LoopArg (B.L N) 2)
    (hW : 0 ≤ (B.W N : ℝ)) :
    0 ≤ APrimeFullQV.rootProfile B E N u v D ellSource J Smax ε a := by
  have hT : 0 ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg hW (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 ≤ Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
      6 * ellStar (B.W N : ℝ) (B.ell N v) then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hWD : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW _
  unfold APrimeFullQV.rootProfile
  positivity

/-- The full endpoint profile is monotone in the block parameter.  The
source amplitude needs no sign premise: it enters the far rate through
`sqrt Smax`, which is nonnegative for every real `Smax`. -/
theorem rootProfile_mono_J {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω) (E : ℝ) (N : ℕ)
    (u v D ellSource Smax ε : ℝ) (a : LoopArg (B.L N) 2)
    {J J' : ℝ}
    (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < B.ell N u)
    (hηu : 0 < etaT E u) (hJ0 : 0 ≤ J) (hJJ' : J ≤ J') :
    APrimeFullQV.rootProfile B E N u v D ellSource J Smax ε a ≤
      APrimeFullQV.rootProfile B E N u v D ellSource J' Smax ε a := by
  have hfar := APrimeJGWidened.diagFarRate_mono
    (D := D) (Smax := Smax) hW hℓu hηu hJ0 hJJ'
  have hK := endpointKernel_nonneg B E N u v D a (zero_le_one.trans hW)
  unfold APrimeFullQV.rootProfile
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfar) hK) _

/-- The full uncut moving profile with the block slot fixed to `J = 2`.
The near repair and the `W⁻⁶⁰` far leakage remain literal fields of
`rootProfile`. -/
def fixedTwoMovingProfileAt (ν : ℝ) (N : ℕ) (ω : Ω d) (v r : ℝ)
    (a : LoopArg (d.L N) 2) : Prop :=
  APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω ≤
    ((APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ *
      APrimeFullQV.rootProfile B 0 N r v 60
        (APrimeFirstCellSourceAllTime.ellSource
          (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
        2
        (APrimeFirstCellSourceAllTime.sourceC4
          (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N r)
        ((d.W N : ℝ)⁻¹) a) ^ 2

/-- Deterministically replace the actual block parameter in T436's moving
profile by two. -/
theorem fixedTwoMovingProfileAt_of_sharp {ν : ℝ} {N : ℕ} {ω : Ω d}
    {v r : ℝ} {a : LoopArg (d.L N) 2}
    (hW : 1 ≤ (d.W N : ℝ)) (hℓ : 0 < B.ell N r)
    (hη : 0 < etaT 0 r) (hr0 : 0 ≤ r) (hrv : r ≤ v) (hv1 : v < 1)
    (hJ1 : 1 ≤ APrimeSupportRunning.jG N r ω)
    (hJ2 : APrimeSupportRunning.jG N r ω ≤ 2)
    (hraw : APrimeFirstCellQVSharpMoving.sharpMovingProfileAt
      ν N ω v r a) :
    fixedTwoMovingProfileAt ν N ω v r a := by
  have hprof := rootProfile_mono_J B 0 N r v 60
    (APrimeFirstCellSourceAllTime.ellSource
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
    (APrimeFirstCellSourceAllTime.sourceC4
      (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N r)
    ((d.W N : ℝ)⁻¹) a hW hℓ hη
    (zero_le_one.trans hJ1) hJ2
  have hscale : 0 ≤
      (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d
      (by norm_num) (hr0.trans hrv) hv1 N a)).le
  have hroot : 0 ≤ APrimeFullQV.rootProfile B 0 N r v 60
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeSupportRunning.jG N r ω)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N r)
      ((d.W N : ℝ)⁻¹) a :=
    rootProfile_nonneg B 0 N r v 60
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeSupportRunning.jG N r ω)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N r)
      ((d.W N : ℝ)⁻¹) a (zero_le_one.trans hW)
  have hscaled := mul_le_mul_of_nonneg_left hprof hscale
  have hsq := pow_le_pow_left₀ (mul_nonneg hscale hroot) hscaled 2
  unfold fixedTwoMovingProfileAt
  unfold APrimeFirstCellQVSharpMoving.sharpMovingProfileAt at hraw
  unfold APrimeFirstCellQVMovingProfile.movingProfileAt at hraw
  exact hraw.trans hsq

/-- Every positive active prefix on the T434 event carries the fixed-two
full profile at its literal moving endpoint. -/
def fixedTwoRunningMovingProfile (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
        (∀ q ∈ Set.Icc (0 : ℝ) (1 / 2),
          APrimeSupportRunning.jG N q ω ≤ 2) ∧
        ∀ r ∈ Set.Icc (0 : ℝ) v,
          1 ≤ APrimeSupportRunning.jG N r ω ∧
          APrimeSupportRunning.jG N r ω ≤ 2 ∧
            ∀ a : LoopArg (d.L N) 2,
              fixedTwoMovingProfileAt ν N ω v r a

theorem eventually_fixedTwo_running_moving_profile {τ' δ ν : ℝ}
    (hτ' : 0 < τ') : fixedTwoRunningMovingProfile τ' δ ν := by
  filter_upwards [
    APrimeFirstCellQVSharpMoving.eventually_sharp_running_moving_profile hτ'] with
    N hrun
  intro ω hω N0 p k m hN0 hp hm hk1 hk hw
  obtain ⟨hvpos, hvle, hvhalf, hJall, hprof⟩ :=
    hrun ω hω N0 p k m hN0 hp hm hk1 hk hw
  refine ⟨hvpos, hvle, hvhalf, hJall, ?_⟩
  intro r hr
  obtain ⟨hJ2, hraw⟩ := hprof r hr
  have hr1 : r < 1 := hr.2.trans_lt (hvhalf.trans_lt (by norm_num))
  have hℓ : 0 < B.ell N r := by
    have hh := one_le_ellHat (d.L N) (d.three_le_L N) hr.1 hr1
    change 1 ≤ B.ell N r at hh
    linarith
  have hη : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast B.one_le_W N
  have hJ1 : 1 ≤ APrimeSupportRunning.jG N r ω :=
    APrimeJG.one_le_jG (sample d) 0 N r ω (by exact_mod_cast d.W_pos N)
  refine ⟨hJ1, hJ2, ?_⟩
  intro a
  exact fixedTwoMovingProfileAt_of_sharp hW hℓ hη hr.1 hr.2
    (hvhalf.trans_lt (by norm_num)) hJ1 hJ2 (hraw a)

/-- The positive T434 `k = 2` resident carries the fixed-two profile at all
preceding times and at both endpoints explicitly. -/
def positiveFixedTwoMovingProfilePlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT τ' N ∧ v ≤ 1 / 2 ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    APrimeFullQV.SourceEvent (sample d) 0 N v ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N v) ∧
    (∀ q ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N q ω ≤ 2) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) v,
      1 ≤ APrimeSupportRunning.jG N r ω ∧
      APrimeSupportRunning.jG N r ω ≤ 2 ∧
        ∀ a : LoopArg (d.L N) 2,
          fixedTwoMovingProfileAt ν N ω v r a) ∧
    1 ≤ APrimeSupportRunning.jG N 0 ω ∧
    APrimeSupportRunning.jG N 0 ω ≤ 2 ∧
    1 ≤ APrimeSupportRunning.jG N v ω ∧
    APrimeSupportRunning.jG N v ω ≤ 2 ∧
    (∀ a : LoopArg (d.L N) 2,
      fixedTwoMovingProfileAt ν N ω v 0 a) ∧
    ∀ a : LoopArg (d.L N) 2,
      fixedTwoMovingProfileAt ν N ω v v a

theorem positiveFixedTwoMovingProfilePlateau_of_sharp {τ' δ ν : ℝ}
    (hτ' : 0 < τ')
    (hpositive : APrimeFirstCellSharpCommonEvent.positiveSharpPlateau
      τ' δ ν) :
    positiveFixedTwoMovingProfilePlateau τ' δ ν := by
  filter_upwards [hpositive, eventually_fixedTwo_running_moving_profile hτ',
    eventually_ge_atTop 2] with N hpositive hrun hN
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hpositive
  obtain ⟨ω, hω, hk, hw, hvpos, hvle, hTle, hsource,
    _hJallOld, _hJ0Old, _hJvOld⟩ := hpositive
  have hh := hrun ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hw 1]; norm_num)
  obtain ⟨_hvpos, _hvle, _hvhalf, hJall, hprof⟩ := hh
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hvhalf : v ≤ (1 / 2 : ℝ) := hvle.trans hTle
  have hzero := hprof 0 ⟨le_rfl, hvpos.le⟩
  have hend := hprof v ⟨hvpos.le, le_rfl⟩
  exact ⟨ω, hω, hvpos, hvle, hvhalf, hw, hsource, hJall, hprof,
    hzero.1, hzero.2.1, hend.1, hend.2.1, hzero.2.2, hend.2.2⟩

/-- Closed fixed-two producer with the unchanged T434 parameter order. -/
theorem exists_fixedTwo_running_moving_profile_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        fixedTwoRunningMovingProfile τ' δ ν ∧
        positiveFixedTwoMovingProfilePlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_fixedTwo_running_moving_profile hτ',
    positiveFixedTwoMovingProfilePlateau_of_sharp hτ' hpositive⟩

#print axioms endpointKernel_nonneg
#print axioms rootProfile_nonneg
#print axioms rootProfile_mono_J
#print axioms fixedTwoMovingProfileAt_of_sharp
#print axioms eventually_fixedTwo_running_moving_profile
#print axioms positiveFixedTwoMovingProfilePlateau_of_sharp
#print axioms exists_fixedTwo_running_moving_profile_with_plateau

end RBM.APrimeFirstCellQVFixedTwo
