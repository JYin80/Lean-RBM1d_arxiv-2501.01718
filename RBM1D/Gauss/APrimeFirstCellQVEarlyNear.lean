/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVEarlyRaw
import RBM1D.Gauss.APrimeFirstCellQVRunningSmall

/-!
# T443: stored first-cell early-QV near coefficient absorption

Only the `diagNearRate + 2 W⁻¹` scalar in T439 is absorbed.  The T439 raw
bound, including both far powers and the `W⁻⁶⁰` row, is carried unchanged.
-/

namespace RBM.APrimeFirstCellQVEarlyNear

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def xRate (u : ℝ) : ℝ := etaT 0 0 / etaT 0 u

/-- The near row and repaired `W⁻¹` row after the literal T439
`x⁸ N^(4δ)` normalization. -/
def nearRepairAt (δ ν : ℝ) (N : ℕ) (u : ℝ) : Prop :=
  (APrimeQVEndpoint.diagNearRate B N (B.ell N u)
        (APrimeFirstCellSourceAllTime.ellSource
          (APrimeFirstCellEGAllOutputRunning.sourceLoss ν) N)
        (etaT 0 u) + 2 * (d.W N : ℝ)⁻¹) /
      (xRate u ^ 8 * ((N : ℝ) ^ (2 * δ)) ^ 2) ≤
    6 * (N : ℝ) ^ (ν - 4 * δ) * (etaT 0 0)⁻¹ *
      xRate u ^ (-(9 / 2 : ℝ))

theorem sourceLoss_le_one128 (ν : ℝ) :
    APrimeFirstCellEGAllOutputRunning.sourceLoss ν ≤ ν / 128 := by
  unfold APrimeFirstCellEGAllOutputRunning.sourceLoss
    APrimeFirstCellEGFarSmallRunning.sourceLoss
  calc
    min ((ν / 2) / 64) (1 / 64) ≤ (ν / 2) / 64 := min_le_left _ _
    _ = ν / 128 := by ring

private theorem ell_le_sqrt_xRate (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    B.ell N u ≤ Real.sqrt (xRate u) := by
  have hh := Step3.ellHat_le_sqrt_mul
    (L := B.L N) (s := 0) (t := u) hu0 hu1
  have hz : ellHat (B.L N) ((0 : ℝ) : ℂ) = 1 :=
    ellHat_zero (B.L N) (B.three_le_L N)
  rw [hz, mul_one] at hh
  change ellHat (B.L N) (u : ℂ) ≤ _
  simpa only [xRate, etaT, mE_zero,
    Complex.I_im, mul_one, sub_zero, one_mul] using hh

private theorem normalized_near_power_identity {N : ℕ} {δ ν A x : ℝ}
    (hN : 0 < (N : ℝ)) (hx : 0 < x) :
    (6 * A * (N : ℝ) ^ ν * x ^ (7 / 2 : ℝ)) /
        (x ^ 8 * ((N : ℝ) ^ (2 * δ)) ^ 2) =
      6 * (N : ℝ) ^ (ν - 4 * δ) * A * x ^ (-(9 / 2 : ℝ)) := by
  have hNpow : ((N : ℝ) ^ (2 * δ)) ^ 2 = (N : ℝ) ^ (4 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hxpow : x ^ (-(9 / 2 : ℝ)) = x ^ (7 / 2 : ℝ) / x ^ 8 := by
    rw [show -(9 / 2 : ℝ) = 7 / 2 - 8 by ring, Real.rpow_sub hx]
    norm_num only [Real.rpow_ofNat]
  rw [hNpow, Real.rpow_sub hN, hxpow]
  field_simp [(Real.rpow_pos_of_pos hN _).ne',
    (Real.rpow_pos_of_pos hx _).ne']

/-- Deterministic absorption of exactly the near and repaired scalar. -/
theorem nearRepairAt_of_coeff {δ ν : ℝ} (hν : 0 < ν)
    (N : ℕ) {u : ℝ} (hN2 : 2 ≤ N)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hc : Lemma57.cNear2 (d.W N : ℝ) (B.ell N u) ≤
      (N : ℝ) ^ (ν / 4)) : nearRepairAt δ ν N u := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have hηu : 0 < etaT 0 u := Step2.etaT_pos' (by norm_num) hu1
  have hη0 : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hx : 1 ≤ xRate u := by
    simpa only [xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hu.1 hu1)
  have hxpos : 0 < xRate u := zero_lt_one.trans_le hx
  have hell1 : 1 ≤ B.ell N u :=
    one_le_ellHat (d.L N) (d.three_le_L N) hu.1 hu1
  have hell0 : 0 ≤ B.ell N u := zero_le_one.trans hell1
  have hell := ell_le_sqrt_xRate N hu.1 hu1
  let ζ := APrimeFirstCellEGAllOutputRunning.sourceLoss ν
  have hζ0 : 0 ≤ ζ := by
    dsimp [ζ]
    exact (APrimeFirstCellEGAllOutputRunning.sourceLoss_pos hν).le
  have hζle : ζ ≤ ν / 128 := by
    dsimp [ζ]
    exact sourceLoss_le_one128 ν
  have hratioEq :=
    APrimeFirstCellQVEarlyRaw.ell_div_ellSource_pow_five ν N u hNpos
  have hsqrt : (Real.sqrt (xRate u)) ^ (5 : ℕ) =
      xRate u ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hxpos.le]
    norm_num
  have hratio :
      (B.ell N u / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) ≤
        2 * (N : ℝ) ^ ζ *
          xRate u ^ (5 / 2 : ℝ) := by
    rw [show (B.ell N u /
        APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) =
        2 * (N : ℝ) ^ ζ * (B.ell N u) ^ (5 : ℕ) by
      simpa only [ζ] using hratioEq]
    have hp := pow_le_pow_left₀ hell0 hell 5
    gcongr
    simpa only [hsqrt] using hp
  have hηeq : (etaT 0 u)⁻¹ =
      (etaT 0 0)⁻¹ * xRate u := by
    simp [xRate, etaT, mE_zero]
  have hNpow : (N : ℝ) ^ (ν / 4) * (N : ℝ) ^ ζ ≤ (N : ℝ) ^ ν := by
    calc
      _ = (N : ℝ) ^ (ν / 4 + ζ) := by
        rw [Real.rpow_add hNpos]
      _ ≤ (N : ℝ) ^ ν := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        linarith
  have hxmul : xRate u * xRate u ^ (5 / 2 : ℝ) =
        xRate u ^ (7 / 2 : ℝ) := by
    calc
      _ = xRate u ^ (1 : ℝ) * xRate u ^ (5 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = xRate u ^ ((1 : ℝ) + 5 / 2) :=
        (Real.rpow_add hxpos _ _).symm
      _ = _ := by congr 1; ring
  have hW1 : 1 ≤ (d.W N : ℝ) := by exact_mod_cast B.one_le_W N
  have hWpos : 0 < (d.W N : ℝ) := zero_lt_one.trans_le hW1
  have hWinv : (d.W N : ℝ)⁻¹ ≤ (etaT 0 u)⁻¹ := by
    have hηle : etaT 0 u ≤ 1 := by
      simp only [etaT, mE_zero, Complex.I_im, mul_one]
      linarith [hu.1]
    exact ((inv_le_one₀ hWpos).2 hW1).trans ((one_le_inv₀ hηu).2 hηle)
  have hc0 : 0 ≤ Lemma57.cNear2 (d.W N : ℝ) (B.ell N u) :=
    Lemma57.cNear2_nonneg hW1 (lt_of_lt_of_le zero_lt_one hell1)
  have hc' : Lemma57.cNear2 (B.W N : ℝ) (B.ell N u) ≤
      (N : ℝ) ^ (ν / 4) := by
    simpa only [B, d, Gauss.band_W] using hc
  have hellSource : 0 < APrimeFirstCellSourceAllTime.ellSource ζ N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hratio0 : 0 ≤
      (B.ell N u / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) :=
    pow_nonneg (div_nonneg hell0 hellSource.le) _
  have hnear :
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) ≤
        4 * (etaT 0 0)⁻¹ * (N : ℝ) ^ ν *
          xRate u ^ (7 / 2 : ℝ) := by
    unfold APrimeQVEndpoint.diagNearRate
    calc
      _ ≤ 2 * (etaT 0 u)⁻¹ * (N : ℝ) ^ (ν / 4) *
          (2 * (N : ℝ) ^ ζ *
            xRate u ^ (5 / 2 : ℝ)) := by
        gcongr
      _ = 4 * (etaT 0 0)⁻¹ *
          ((N : ℝ) ^ (ν / 4) * (N : ℝ) ^ ζ) *
            (xRate u * xRate u ^ (5 / 2 : ℝ)) := by
        rw [hηeq]
        ring
      _ ≤ 4 * (etaT 0 0)⁻¹ * (N : ℝ) ^ ν *
          xRate u ^ (7 / 2 : ℝ) := by
        rw [hxmul]
        gcongr
  have hNν : 1 ≤ (N : ℝ) ^ ν := Real.one_le_rpow hN hν.le
  have hxx : xRate u ≤ xRate u ^ (7 / 2 : ℝ) := by
    calc
      _ = xRate u ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ xRate u ^ (7 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hrepair : 2 * (d.W N : ℝ)⁻¹ ≤
      2 * (etaT 0 0)⁻¹ * (N : ℝ) ^ ν *
        xRate u ^ (7 / 2 : ℝ) := by
    calc
      _ ≤ 2 * (etaT 0 u)⁻¹ := by gcongr
      _ = 2 * (etaT 0 0)⁻¹ * xRate u := by
        rw [hηeq]
        ring
      _ ≤ 2 * (etaT 0 0)⁻¹ *
          xRate u ^ (7 / 2 : ℝ) := by gcongr
      _ = (2 * (etaT 0 0)⁻¹ * xRate u ^ (7 / 2 : ℝ)) * 1 := by ring
      _ ≤ (2 * (etaT 0 0)⁻¹ * xRate u ^ (7 / 2 : ℝ)) *
          (N : ℝ) ^ ν := by
        exact mul_le_mul_of_nonneg_left hNν (by positivity)
      _ = _ := by ring
  have hnum :
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ ≤
      6 * (etaT 0 0)⁻¹ * (N : ℝ) ^ ν *
        xRate u ^ (7 / 2 : ℝ) := by
    nlinarith
  have hden : 0 < xRate u ^ 8 *
      ((N : ℝ) ^ (2 * δ)) ^ 2 := by positivity
  unfold nearRepairAt
  dsimp only [ζ] at hnum
  calc
    _ ≤ (6 * (etaT 0 0)⁻¹ * (N : ℝ) ^ ν *
        xRate u ^ (7 / 2 : ℝ)) /
          (xRate u ^ 8 *
            ((N : ℝ) ^ (2 * δ)) ^ 2) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = _ := normalized_near_power_identity hNpos hxpos

/-- T439's unchanged raw bound together with the absorbed near scalar at
every stored `j<k`. -/
def nearOnStoredPrefixes (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ j < k,
        let u := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N j
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        u ∈ Set.Icc (0 : ℝ) v ∧
        v ≤ firstCellT τ' N ∧
        1 ≤ xRate u ∧
        nearRepairAt δ ν N u ∧
        ∀ a : LoopArg (d.L N) 2,
          APrimeFirstCellQVEarlyRaw.fixedTwoEarlyRawAt δ ν N ω u a

theorem eventually_near_on_stored_prefixes {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hν : 0 < ν) : nearOnStoredPrefixes τ' δ ν := by
  filter_upwards [
    APrimeFirstCellQVEarlyRaw.eventually_earlyRaw_on_stored_prefixes hτ',
    APrimeFirstCellQVRunningSmall.eventually_coefficients_uniform
      (show 0 < ν / 4 by positivity),
    eventually_ge_atTop 2] with N hraw hcoeff hN2
  intro ω hω N0 p k m hN0 hp hm hk1 hk hw j hjk
  dsimp only
  have hj := hraw ω hω N0 p k m hN0 hp hm hk1 hk hw j hjk
  let u := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
  have hvCell := MomentDuhamelCut.netFinset_subset_Icc
    (APrimeSupportRunning.firstT_bounds hτ' N).1
    (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  have huv : u ≤ v := by
    have hcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk.le
    have hdiv := (div_le_div_iff_of_pos_right
      (APrimeSupportRunning.mesh_pos N)).2 hcast
    simpa only [u, v, cutNetPt, zero_add] using hdiv
  have huHalf : u ∈ Set.Icc (0 : ℝ) (1 / 2) := hj.1
  have hu1 : u < 1 := huHalf.2.trans_lt (by norm_num)
  have hx : 1 ≤ xRate u := by
    simpa only [u, xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) huHalf.1 hu1)
  have hnear := nearRepairAt_of_coeff (δ := δ) hν N hN2 huHalf
    (hcoeff u huHalf).1
  exact ⟨⟨huHalf.1, huv⟩, hvCell.2, hx, hnear, hj.2.2.2.2.2.2⟩

/-- One T434 `k=2` resident carries the absorbed scalar at `j=0` and at
the positive stored time `j=1`, while retaining T439's raw far rows. -/
def positiveNearPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    let u0 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0
    let u1 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
    let u2 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    nearRepairAt δ ν N u0 ∧ nearRepairAt δ ν N u1 ∧
    (∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellQVEarlyRaw.fixedTwoEarlyRawAt δ ν N ω u0 a) ∧
    ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellQVEarlyRaw.fixedTwoEarlyRawAt δ ν N ω u1 a

theorem positiveNearPlateau_of_raw {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hν : 0 < ν)
    (hpositive : APrimeFirstCellQVEarlyRaw.positiveEarlyRawPlateau
      τ' δ ν) : positiveNearPlateau τ' δ ν := by
  filter_upwards [hpositive,
    APrimeFirstCellQVRunningSmall.eventually_coefficients_uniform
      (show 0 < ν / 4 by positivity),
    eventually_ge_atTop 2] with N hpositive hcoeff hN2
  dsimp only [APrimeFirstCellQVEarlyRaw.positiveEarlyRawPlateau] at hpositive
  obtain ⟨ω, hω, hu1pos, hu12, hu2le, hw, hu0,
    _hsource0, _hsource1, _hJ0, _hJ1, _hratio0, _hratio1,
    hraw0, hraw1⟩ := hpositive
  let u0 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0
  let u1 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
  let u2 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
  have hTle : firstCellT τ' N ≤ (1 / 2 : ℝ) :=
    (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hu0Half : u0 ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    dsimp [u0]
    rw [hu0]
    norm_num
  have hu1Half : u1 ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hu1pos.le, hu12.le.trans (hu2le.trans hTle)⟩
  have hnear0 : nearRepairAt δ ν N u0 := nearRepairAt_of_coeff
    (δ := δ) hν N hN2 hu0Half
    (hcoeff u0 hu0Half).1
  have hnear1 : nearRepairAt δ ν N u1 := nearRepairAt_of_coeff
    (δ := δ) hν N hN2 hu1Half
    (hcoeff u1 hu1Half).1
  exact ⟨ω, hω, hu0, hu1pos, hu12, hu2le, hw, hnear0, hnear1,
    hraw0, hraw1⟩

/-- Closed T443 producer with the T434 parameter order unchanged. -/
theorem exists_near_on_stored_prefixes_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        nearOnStoredPrefixes τ' δ ν ∧
        positiveNearPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQVEarlyRaw.exists_earlyRaw_on_stored_prefixes_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hraw, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_near_on_stored_prefixes hτ' hν,
    positiveNearPlateau_of_raw hτ' hν hpositive⟩

#print axioms sourceLoss_le_one128
#print axioms nearRepairAt_of_coeff
#print axioms eventually_near_on_stored_prefixes
#print axioms positiveNearPlateau_of_raw
#print axioms exists_near_on_stored_prefixes_with_plateau

end RBM.APrimeFirstCellQVEarlyNear
