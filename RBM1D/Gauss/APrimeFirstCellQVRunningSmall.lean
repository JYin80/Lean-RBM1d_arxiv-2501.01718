/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVRunningProfile
import RBM1D.Gauss.APrimeFirstCellQVSmall

/-!
# T408: power absorption of the running first-cell QV profile

The five rows are kept separate. In particular, the cubic row retains the
literal inverse scale `A⁻¹`; no `A⁻¹/³ J³` coarsening is used.
-/

namespace RBM.APrimeFirstCellQVRunningSmall

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def capJ (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)

noncomputable def farTwo (N : ℕ) (u S : ℝ) : ℝ :=
  2 * (etaT 0 u)⁻¹ * Lemma57.cFar2 (B.W N : ℝ) (B.ell N u) *
    ((2 * capJ N) ^ (2 : ℕ) *
      (((B.W N : ℝ) * B.ell N u * etaT 0 u) * (2 * √S)))

noncomputable def farThree (N : ℕ) (u : ℝ) : ℝ :=
  2 * (etaT 0 u)⁻¹ * 72 * (2 * capJ N) ^ (3 : ℕ) *
    ((B.W N : ℝ) * B.ell N u * etaT 0 u)⁻¹

noncomputable def farLeak (N : ℕ) : ℝ :=
  4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-(60 : ℝ)) *
    (2 * capJ N) ^ (3 : ℕ)

noncomputable def runningRootProfile (N : ℕ) (u ellSource S : ℝ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  √(APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹) *
      APrimeFirstCellQVSharpJ.nearKernel N u a +
  √(APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹) *
      APrimeFirstCellQVSharpJ.leakKernel N u a +
  √(farTwo N u S) * APrimeFirstCellQVSharpJ.endpointKernel N u a +
  √(farThree N u) * APrimeFirstCellQVSharpJ.endpointKernel N u a +
  √(farLeak N) * APrimeFirstCellQVSharpJ.endpointKernel N u a

private theorem sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  have hxy : 0 ≤ √x * √y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt (add_nonneg hx hy), Real.sqrt_nonneg x,
    Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y)]

theorem rootProfile_le_running (N : ℕ) (u ellSource J S : ℝ)
    (a : LoopArg (d.L N) 2)
    (hW : 1 ≤ (d.W N : ℝ)) (hℓ : 0 < B.ell N u)
    (hη : 0 < etaT 0 u) (hS : 0 ≤ S)
    (hJ0 : 0 ≤ J) (hJ : J ≤ capJ N) :
    APrimeFullQV.rootProfile B 0 N u (1 / 2) 60 ellSource J S
        ((d.W N : ℝ)⁻¹) a ≤ runningRootProfile N u ellSource S a := by
  let An := APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
    2 * (d.W N : ℝ)⁻¹
  let Af := APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 J S
  let K := APrimeFirstCellQVSharpJ.endpointKernel N u a
  let Kn := APrimeFirstCellQVSharpJ.nearKernel N u a
  let Kl := APrimeFirstCellQVSharpJ.leakKernel N u a
  have hcf := Lemma57.cFar2_nonneg hW hℓ
  have hcap0 : 0 ≤ capJ N := by unfold capJ; positivity
  have hscale : 0 < B.scale 0 N u := by unfold Band.scale; positivity
  have hF2 : 0 ≤ farTwo N u S := by
    unfold farTwo
    positivity
  have hF3 : 0 ≤ farThree N u := by
    unfold farThree
    positivity
  have hFL : 0 ≤ farLeak N := by
    unfold farLeak
    positivity
  have hK : 0 ≤ K := by
    dsimp [K, APrimeFirstCellQVSharpJ.endpointKernel, Step2.tT]
    have ht : 0 ≤ tailT (d.W N : ℝ) (B.ell N (1 / 2))
        (etaT 0 (1 / 2)) 60 (zdist (d.L N) (a 0 - a 1)) :=
      tailT_nonneg (by linarith : (0 : ℝ) ≤ (d.W N : ℝ)) _
    have hxi := Step2.xiK_nonneg (d.L N) (d.W N : ℝ) (mE 0).im
    positivity
  have hAf : Af ≤ farTwo N u S + farThree N u + farLeak N := by
    have hm := APrimeJGWidened.diagFarRate_mono (B := B) (N := N)
      (ℓu := B.ell N u) (ηu := etaT 0 u) (D := 60) (Smax := S)
      (J := J) (J' := capJ N) hW hℓ hη hJ0 hJ
    calc
      Af ≤ APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60
          (capJ N) S := hm
      _ = farTwo N u S + farThree N u + farLeak N := by
        unfold APrimeQVEndpoint.diagFarRate farTwo farThree farLeak
        ring
  have hsplit : √Af ≤ √(farTwo N u S) + √(farThree N u) + √(farLeak N) := by
    calc
      √Af ≤ √(farTwo N u S + farThree N u + farLeak N) := Real.sqrt_le_sqrt hAf
      _ ≤ √(farTwo N u S + farThree N u) + √(farLeak N) :=
        sqrt_add_le _ _ (add_nonneg hF2 hF3) hFL
      _ ≤ √(farTwo N u S) + √(farThree N u) + √(farLeak N) := by
        gcongr
        exact sqrt_add_le _ _ hF2 hF3
  change √An * (Kn + Kl) + √Af * K ≤
    √An * Kn + √An * Kl + √(farTwo N u S) * K +
      √(farThree N u) * K + √(farLeak N) * K
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hsplit)]

private theorem cNear2_compare {W ell ell0 : ℝ}
    (hW : 1 ≤ W) (hell : 1 ≤ ell) (hell0 : 0 < ell0) (hell02 : ell0 ≤ 2) :
    Lemma57.cNear2 W ell ≤ 2 * Lemma57.cNear2 W ell0 := by
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have hx : 0 ≤ 2 * Real.log W ^ (3 : ℝ) := by positivity
  have he : 0 < Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) := Real.exp_pos _
  have hdiv : 2 / ell ≤ 2 := (div_le_iff₀ (by linarith : 0 < ell)).2 (by linarith)
  have hdiv0 : 1 ≤ 2 / ell0 := by
    apply (le_div_iff₀ hell0).2
    simpa using hell02
  unfold Lemma57.cNear2
  nlinarith [mul_nonneg
    (show 0 ≤ 2 * (2 * Real.log W ^ (3 : ℝ) + 2 / ell0) -
      (2 * Real.log W ^ (3 : ℝ) + 2 / ell) by linarith) he.le]

private theorem cFar2_compare {W ell ell0 : ℝ}
    (hW : 1 ≤ W) (hell : 1 ≤ ell) (hell0 : 0 < ell0) (hell02 : ell0 ≤ 2) :
    Lemma57.cFar2 W ell ≤ 2 * Lemma57.cFar2 W ell0 := by
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have hx : 0 ≤ 4 * Real.log W ^ (3 / 2 : ℝ) := by positivity
  have he : 0 < Real.exp (Real.log W ^ (3 / 4 : ℝ)) := Real.exp_pos _
  have hdiv : 4 / ell ≤ 4 := (div_le_iff₀ (by linarith : 0 < ell)).2 (by linarith)
  have hdiv0 : 2 ≤ 4 / ell0 := (le_div_iff₀ hell0).2 (by linarith)
  unfold Lemma57.cFar2 Lemma57.loss1
  nlinarith [mul_nonneg
    (show 0 ≤ 2 * (4 * Real.log W ^ (3 / 2 : ℝ) + 4 / ell0) -
      (4 * Real.log W ^ (3 / 2 : ℝ) + 4 / ell) by linarith) he.le]

theorem eventually_coefficients_uniform {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      Lemma57.cNear2 (d.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ τ ∧
      Lemma57.cFar2 (d.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ τ := by
  have ht : 0 < τ / 2 := by positivity
  have hn := APrimeFirstCellQVSmall.eventually_cNear2_le ht
  have hf := APrimeFirstCellQVSmall.eventually_cFar2_le ht
  have htwo := eventually_le_rpow 2 ht
  have htime := APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime
    (τ' := 1) (by norm_num)
  filter_upwards [hn, hf, htwo, htime, eventually_ge_atTop 2] with
    N hn hf htwo htime hN u hu
  change Lemma57.cNear2 (d.W N : ℝ)
    (B.ell N (APrimeFirstCellJGCap.firstTime N)) ≤ (N : ℝ) ^ (τ / 2) at hn
  change Lemma57.cFar2 (d.W N : ℝ)
    (B.ell N (APrimeFirstCellJGCap.firstTime N)) ≤ (N : ℝ) ^ (τ / 2) at hf
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hell : 1 ≤ B.ell N u := by
    change 1 ≤ ellHat (d.L N) (u : ℂ)
    exact one_le_ellHat_of_nonneg (L := d.L N)
      (by have := d.three_le_L N; omega) hu.1
      (hu.2.trans_lt (by norm_num))
  have hft0 : 0 ≤ APrimeFirstCellJGCap.firstTime N := by
    rw [← htime.1]
    exact htime.2.le
  have hmem := APrimeFirstCellNearSources.sourceTime_mem
    (τ' := 1) (by norm_num) N
  have hft : APrimeFirstCellJGCap.firstTime N ≤ 1 / 2 := by
    rw [← htime.1]
    exact hmem.2.trans (gridT_le (1 / 2 : ℝ) 1)
  have hell01 : 1 ≤ B.ell N (APrimeFirstCellJGCap.firstTime N) := by
    change 1 ≤ ellHat (d.L N) (APrimeFirstCellJGCap.firstTime N : ℂ)
    exact one_le_ellHat_of_nonneg (by have := d.three_le_L N; omega)
      hft0 (hft.trans_lt (by norm_num))
  have hell0 : 0 < B.ell N (APrimeFirstCellJGCap.firstTime N) :=
    lt_of_lt_of_le zero_lt_one hell01
  have hell02 : B.ell N (APrimeFirstCellJGCap.firstTime N) ≤ 2 :=
    APrimeFirstCellQVSmall.ell_firstHalf_le_two N hft0 hft
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hn0 : 0 ≤ Lemma57.cNear2 (d.W N : ℝ)
      (B.ell N (APrimeFirstCellJGCap.firstTime N)) :=
    Lemma57.cNear2_nonneg hW hell0
  have hf0 : 0 ≤ Lemma57.cFar2 (d.W N : ℝ)
      (B.ell N (APrimeFirstCellJGCap.firstTime N)) :=
    Lemma57.cFar2_nonneg hW hell0
  constructor
  · calc
      _ ≤ 2 * Lemma57.cNear2 (d.W N : ℝ)
          (B.ell N (APrimeFirstCellJGCap.firstTime N)) :=
        cNear2_compare hW hell hell0 hell02
      _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        exact mul_le_mul htwo hn hn0 (by positivity)
      _ = _ := hpow
  · calc
      _ ≤ 2 * Lemma57.cFar2 (d.W N : ℝ)
          (B.ell N (APrimeFirstCellJGCap.firstTime N)) :=
        cFar2_compare hW hell hell0 hell02
      _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        exact mul_le_mul htwo hf hf0 (by positivity)
      _ = _ := hpow

theorem source_scale_sqrt_le (N : ℕ) (u ζ : ℝ)
    (hN : 1 ≤ (N : ℝ)) (hWgrow : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ))
    (hℓ1 : 1 ≤ B.ell N u) (hℓ2 : B.ell N u ≤ 2)
    (hη : 1 / 2 ≤ etaT 0 u) :
    B.scale 0 N u * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤
      4 * (N : ℝ) ^ (ζ / 2 - 5 / 16) := by
  let A := B.scale 0 N u
  let ell := B.ell N u
  let Q := (N : ℝ) ^ ζ
  have hNpos : (0 : ℝ) < N := by linarith
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hApos : 0 < A := by dsimp [A, Band.scale]; positivity
  have hAhalf : (d.W N : ℝ) / 2 ≤ A := by
    dsimp [A, Band.scale]
    nlinarith [mul_nonneg (sub_nonneg.mpr hℓ1) hWpos.le,
      mul_nonneg (mul_nonneg hWpos.le (by linarith : 0 ≤ ell))
        (sub_nonneg.mpr hη)]
  have hAinv : A⁻¹ ≤ 2 * (d.W N : ℝ)⁻¹ := by
    have hi := inv_anti₀ (by positivity : 0 < (d.W N : ℝ) / 2) hAhalf
    simpa [div_eq_mul_inv] using hi
  have hWinv : (d.W N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hNpos _) hWgrow
    rw [Real.rpow_neg hNpos.le]
    simpa using hi
  have hℓ3 : ell ^ (3 : ℕ) ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℕ) := by gcongr
      _ = 8 := by norm_num
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hS0 : 0 ≤ APrimeFirstCellSourceAllTime.sourceC4 ζ N u := by
    unfold APrimeFirstCellSourceAllTime.sourceC4
    positivity
  have hsource : A ^ (2 : ℕ) *
      APrimeFirstCellSourceAllTime.sourceC4 ζ N u = Q * ell ^ (3 : ℕ) * A⁻¹ := by
    unfold APrimeFirstCellSourceAllTime.sourceC4
    dsimp [A, ell, Q]
    field_simp
  have hx : (A * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u)) ^ (2 : ℕ) =
      A ^ (2 : ℕ) * APrimeFirstCellSourceAllTime.sourceC4 ζ N u := by
    rw [mul_pow, Real.sq_sqrt hS0]
  have hsq : (A * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u)) ^ (2 : ℕ) ≤
      16 * (N : ℝ) ^ (ζ - 5 / 8) := by
    rw [hx, hsource]
    have hqell : Q * ell ^ (3 : ℕ) ≤ Q * 8 := mul_le_mul_of_nonneg_left hℓ3 hQ0
    calc
      Q * ell ^ (3 : ℕ) * A⁻¹ ≤ Q * 8 * (2 * (d.W N : ℝ)⁻¹) := by
        gcongr
      _ ≤ Q * 8 * (2 * (N : ℝ) ^ (-(5 / 8 : ℝ))) := by gcongr
      _ = 16 * (N : ℝ) ^ (ζ - 5 / 8) := by
        dsimp [Q]
        calc
          (N : ℝ) ^ ζ * 8 * (2 * (N : ℝ) ^ (-(5 / 8 : ℝ))) =
              16 * ((N : ℝ) ^ ζ * (N : ℝ) ^ (-(5 / 8 : ℝ))) := by ring
          _ = _ := by rw [← Real.rpow_add hNpos]; congr 1 <;> ring
  have hy : (4 * (N : ℝ) ^ (ζ / 2 - 5 / 16)) ^ (2 : ℕ) =
      16 * (N : ℝ) ^ (ζ - 5 / 8) := by
    calc
      _ = 16 * ((N : ℝ) ^ (ζ / 2 - 5 / 16)) ^ (2 : ℕ) := by ring
      _ = 16 * (N : ℝ) ^ ((ζ / 2 - 5 / 16) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
      _ = _ := by congr 2 <;> ring
  have hx0 : 0 ≤ A * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u) := by positivity
  have hy0 : 0 ≤ 4 * (N : ℝ) ^ (ζ / 2 - 5 / 16) := by positivity
  nlinarith [hsq, hy]

theorem row_bounds (N : ℕ) (u ζ θ : ℝ)
    (hN : 1 ≤ (N : ℝ))
    (hζ : 0 ≤ ζ) (hθ : 0 ≤ θ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hWgrow : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ))
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hcN : Lemma57.cNear2 (d.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ θ)
    (hcF : Lemma57.cFar2 (d.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ θ) :
    APrimeQVEndpoint.diagNearRate B N (B.ell N u)
        (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
          2 * (d.W N : ℝ)⁻¹ ≤ 258 * (N : ℝ) ^ (θ + ζ) ∧
    farTwo N u (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤
      128 * (N : ℝ) ^ (θ + 1 / 4 + ζ / 2 - 5 / 16) ∧
    farThree N u ≤ 4608 * (N : ℝ) ^ ((3 / 8 - 5 / 8 : ℝ)) ∧
    farLeak N ≤ 32 * (N : ℝ) ^ ((1 + 3 / 8 - 15 / 8 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hW1 : 1 ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hη : (1 / 2 : ℝ) ≤ etaT 0 u := by
    rw [show etaT 0 u = 1 - u by norm_num [etaT, Gauss.mE_zero]]
    linarith [hu.2]
  have hηpos : 0 < etaT 0 u := by linarith
  have hηinv : (etaT 0 u)⁻¹ ≤ 2 := by
    simpa using (inv_le_inv₀ hηpos (by norm_num : (0 : ℝ) < 1 / 2)).2 hη
  have hℓ1 : 1 ≤ B.ell N u := by
    change 1 ≤ ellHat (d.L N) (u : ℂ)
    exact one_le_ellHat_of_nonneg (L := d.L N)
      (by have := d.three_le_L N; omega) hu.1 (hu.2.trans_lt (by norm_num))
  have hℓ2 : B.ell N u ≤ 2 :=
    APrimeFirstCellQVSmall.ell_firstHalf_le_two N hu.1 hu.2
  have hWinv : (d.W N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hNpos _) hWgrow
    rw [Real.rpow_neg hNpos.le]
    simpa using hi
  have hθ0 : 0 ≤ (N : ℝ) ^ θ := by positivity
  have hζ0 : 0 ≤ (N : ℝ) ^ ζ := by positivity
  have hcN' : Lemma57.cNear2 (B.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ θ := by
    simpa using hcN
  have hcF' : Lemma57.cFar2 (B.W N : ℝ) (B.ell N u) ≤ (N : ℝ) ^ θ := by
    simpa using hcF
  have hcN0 : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) (B.ell N u) :=
    Lemma57.cNear2_nonneg (by simpa using hW1) (lt_of_lt_of_le zero_lt_one hℓ1)
  have hcF0 : 0 ≤ Lemma57.cFar2 (B.W N : ℝ) (B.ell N u) :=
    Lemma57.cFar2_nonneg (by simpa using hW1) (lt_of_lt_of_le zero_lt_one hℓ1)
  have hratio := APrimeFirstCellQVSmall.source_near_ratio_fifth N ζ (B.ell N u) hNpos
  have hratio' : (B.ell N u /
      APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) ≤
      64 * (N : ℝ) ^ ζ := by
    have heq : (B.ell N u /
        APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) =
        2 * (N : ℝ) ^ ζ * (B.ell N u) ^ (5 : ℕ) := by
      simpa [APrimeFirstCellJGCap.sourceEll,
        APrimeFirstCellSourceAllTime.ellSource] using hratio
    rw [heq]
    have hp : (B.ell N u) ^ (5 : ℕ) ≤ 32 := by
      calc _ ≤ (2 : ℝ) ^ (5 : ℕ) := by gcongr
           _ = 32 := by norm_num
    calc
      2 * (N : ℝ) ^ ζ * (B.ell N u) ^ (5 : ℕ) ≤
          2 * (N : ℝ) ^ ζ * 32 :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hζ0)
      _ = 64 * (N : ℝ) ^ ζ := by ring
  have hratio0 : 0 ≤ (B.ell N u /
      APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) := by
    rw [show (B.ell N u /
      APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) =
        2 * (N : ℝ) ^ ζ * (B.ell N u) ^ (5 : ℕ) by
      simpa [APrimeFirstCellJGCap.sourceEll,
        APrimeFirstCellSourceAllTime.ellSource] using hratio]
    positivity
  have hnear : APrimeQVEndpoint.diagNearRate B N (B.ell N u)
      (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹ ≤ 258 * (N : ℝ) ^ (θ + ζ) := by
    have hmain : APrimeQVEndpoint.diagNearRate B N (B.ell N u)
        (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) ≤
        256 * (N : ℝ) ^ θ * (N : ℝ) ^ ζ := by
      unfold APrimeQVEndpoint.diagNearRate
      calc
        _ ≤ 2 * 2 * (N : ℝ) ^ θ * (64 * (N : ℝ) ^ ζ) := by
          gcongr
        _ = 256 * (N : ℝ) ^ θ * (N : ℝ) ^ ζ := by ring
    have hprod : (N : ℝ) ^ θ * (N : ℝ) ^ ζ = (N : ℝ) ^ (θ + ζ) :=
      Real.rpow_add hNpos θ ζ |>.symm
    have hfloor : 2 * (d.W N : ℝ)⁻¹ ≤ 2 * (N : ℝ) ^ (θ + ζ) := by
      have hone : 1 ≤ (N : ℝ) ^ (θ + ζ) := by
        apply Real.one_le_rpow hN
        linarith
      calc
        2 * (d.W N : ℝ)⁻¹ ≤ 2 * 1 :=
          mul_le_mul_of_nonneg_left ((inv_le_one₀ hWpos).2 hW1) (by norm_num)
        _ ≤ 2 * (N : ℝ) ^ (θ + ζ) :=
          mul_le_mul_of_nonneg_left hone (by norm_num)
    calc
      _ ≤ 256 * (N : ℝ) ^ θ * (N : ℝ) ^ ζ +
          2 * (N : ℝ) ^ (θ + ζ) := add_le_add hmain hfloor
      _ = 256 * ((N : ℝ) ^ θ * (N : ℝ) ^ ζ) +
          2 * (N : ℝ) ^ (θ + ζ) := by ring
      _ = 258 * (N : ℝ) ^ (θ + ζ) := by rw [hprod]; ring
  have hAs := source_scale_sqrt_le N u ζ hN hWgrow hℓ1 hℓ2 hη
  have hJ2 : (capJ N) ^ (2 : ℕ) = (N : ℝ) ^ (1 / 4 : ℝ) := by
    unfold capJ
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hJ3 : (capJ N) ^ (3 : ℕ) = (N : ℝ) ^ (3 / 8 : ℝ) := by
    unfold capJ
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hf2 : farTwo N u (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤
      128 * (N : ℝ) ^ (θ + 1 / 4 + ζ / 2 - 5 / 16) := by
    unfold farTwo
    have hAs' : ((B.W N : ℝ) * B.ell N u * etaT 0 u) *
        √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤
        4 * (N : ℝ) ^ (ζ / 2 - 5 / 16) := by
      simpa only [Band.scale] using hAs
    have hAs2 : ((B.W N : ℝ) * B.ell N u * etaT 0 u) *
        (2 * √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u)) ≤
        8 * (N : ℝ) ^ (ζ / 2 - 5 / 16) := by
      calc
        _ = 2 * (((B.W N : ℝ) * B.ell N u * etaT 0 u) *
            √(APrimeFirstCellSourceAllTime.sourceC4 ζ N u)) := by ring
        _ ≤ 2 * (4 * (N : ℝ) ^ (ζ / 2 - 5 / 16)) := by gcongr
        _ = _ := by ring
    have hpow : (N : ℝ) ^ θ * (N : ℝ) ^ (1 / 4 : ℝ) *
        (N : ℝ) ^ (ζ / 2 - 5 / 16) =
        (N : ℝ) ^ (θ + 1 / 4 + ζ / 2 - 5 / 16) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    rw [mul_pow, hJ2]
    calc
      _ ≤ 2 * 2 * (N : ℝ) ^ θ *
          (((2 : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (1 / 4 : ℝ)) *
            (8 * (N : ℝ) ^ (ζ / 2 - 5 / 16))) := by
        gcongr
      _ = 128 * ((N : ℝ) ^ θ * (N : ℝ) ^ (1 / 4 : ℝ) *
          (N : ℝ) ^ (ζ / 2 - 5 / 16)) := by ring
      _ = _ := by rw [hpow]
  have hAinv : (B.scale 0 N u)⁻¹ ≤
      2 * (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have hAhalf : (d.W N : ℝ) / 2 ≤ B.scale 0 N u := by
      change (d.W N : ℝ) / 2 ≤
        (d.W N : ℝ) * B.ell N u * etaT 0 u
      nlinarith [mul_nonneg (sub_nonneg.mpr hℓ1) hWpos.le,
        mul_nonneg (mul_nonneg hWpos.le (by linarith : 0 ≤ B.ell N u))
          (sub_nonneg.mpr hη)]
    have hi := inv_anti₀ (by positivity : 0 < (d.W N : ℝ) / 2) hAhalf
    calc
      _ ≤ 2 * (d.W N : ℝ)⁻¹ := by simpa [div_eq_mul_inv] using hi
      _ ≤ 2 * (N : ℝ) ^ (-(5 / 8 : ℝ)) := by gcongr
  have hAinv' : ((B.W N : ℝ) * B.ell N u * etaT 0 u)⁻¹ ≤
      2 * (N : ℝ) ^ (-(5 / 8 : ℝ)) := by
    simpa only [Band.scale] using hAinv
  have hf3 : farThree N u ≤ 4608 * (N : ℝ) ^ ((3 / 8 - 5 / 8 : ℝ)) := by
    unfold farThree
    rw [mul_pow, hJ3]
    have hp : (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ (-(5 / 8 : ℝ)) =
        (N : ℝ) ^ ((3 / 8 - 5 / 8 : ℝ)) := by
      calc
        _ = (N : ℝ) ^ ((3 / 8 : ℝ) + (-(5 / 8 : ℝ))) :=
          (Real.rpow_add hNpos _ _).symm
        _ = _ := by norm_num
    calc
      _ ≤ 2 * 2 * 72 * ((2 : ℝ) ^ (3 : ℕ) *
          (N : ℝ) ^ (3 / 8 : ℝ)) *
          (2 * (N : ℝ) ^ (-(5 / 8 : ℝ))) := by gcongr
      _ = 4608 * ((N : ℝ) ^ (3 / 8 : ℝ) *
          (N : ℝ) ^ (-(5 / 8 : ℝ))) := by ring
      _ = _ := by rw [hp]
  have hWneg3 : (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
      (N : ℝ) ^ (-(15 / 8 : ℝ)) := by
    have hmono : (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
        (d.W N : ℝ) ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    have hi3 : (d.W N : ℝ)⁻¹ ^ (3 : ℕ) ≤
        ((N : ℝ) ^ (-(5 / 8 : ℝ))) ^ (3 : ℕ) := by gcongr
    calc
      _ ≤ (d.W N : ℝ) ^ (-(3 : ℝ)) := hmono
      _ = (d.W N : ℝ)⁻¹ ^ (3 : ℕ) := by
        rw [Real.rpow_neg hWpos.le, show (3 : ℝ) = (3 : ℕ) by norm_num,
          Real.rpow_natCast, inv_pow]
      _ ≤ ((N : ℝ) ^ (-(5 / 8 : ℝ))) ^ (3 : ℕ) := hi3
      _ = (N : ℝ) ^ (-(15 / 8 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
  have hfL : farLeak N ≤ 32 * (N : ℝ) ^ ((1 + 3 / 8 - 15 / 8 : ℝ)) := by
    unfold farLeak
    rw [mul_pow, hJ3]
    have hpow : (N : ℝ) * (N : ℝ) ^ (-(15 / 8 : ℝ)) *
        (N : ℝ) ^ (3 / 8 : ℝ) =
        (N : ℝ) ^ ((1 + 3 / 8 - 15 / 8 : ℝ)) := by
      calc
        _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(15 / 8 : ℝ)) *
            (N : ℝ) ^ (3 / 8 : ℝ) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + (-(15 / 8 : ℝ))) *
            (N : ℝ) ^ (3 / 8 : ℝ) := by
          exact congrArg (fun x => x * (N : ℝ) ^ (3 / 8 : ℝ))
            (Real.rpow_add hNpos (1 : ℝ) (-(15 / 8 : ℝ))).symm
        _ = (N : ℝ) ^ (((1 : ℝ) + (-(15 / 8 : ℝ))) + 3 / 8) := by
          exact (Real.rpow_add hNpos
            ((1 : ℝ) + (-(15 / 8 : ℝ))) (3 / 8 : ℝ)).symm
        _ = _ := by norm_num
    have hWL' : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
      simpa using hWL
    have hWneg3' : (B.W N : ℝ) ^ (-(60 : ℝ)) ≤
        (N : ℝ) ^ (-(15 / 8 : ℝ)) := by
      simpa using hWneg3
    calc
      _ = 4 * ((B.W N : ℝ) * (B.L N : ℝ)) *
          (B.W N : ℝ) ^ (-(60 : ℝ)) *
          ((2 : ℝ) ^ (3 : ℕ) * (N : ℝ) ^ (3 / 8 : ℝ)) := by ring
      _ ≤ 4 * (N : ℝ) * (N : ℝ) ^ (-(15 / 8 : ℝ)) *
          ((2 : ℝ) ^ (3 : ℕ) * (N : ℝ) ^ (3 / 8 : ℝ)) := by gcongr
      _ = 32 * ((N : ℝ) * (N : ℝ) ^ (-(15 / 8 : ℝ)) *
          (N : ℝ) ^ (3 / 8 : ℝ)) := by ring
      _ = _ := by rw [hpow]
  exact ⟨hnear, hf2, hf3, hfL⟩

set_option maxHeartbeats 1000000 in
theorem eventually_rows_le_power {ν : ℝ} (hν : 0 < ν) :
    let ζ := min (ν / 256) (1 / 128)
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      let M := (N : ℝ) ^ (ν / 16)
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
            2 * (d.W N : ℝ)⁻¹ ≤ M ∧
      farTwo N u (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤ M ∧
      farThree N u ≤ M ∧ farLeak N ≤ M ∧
      Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im ≤ M ∧
      256 * Real.exp 3 ≤ M ∧ 25 ≤ M := by
  dsimp only
  let ζ : ℝ := min (ν / 256) (1 / 128)
  have hζ : 0 < ζ := by
    dsimp [ζ]
    exact lt_min (by positivity) (by norm_num)
  have hζν : ζ ≤ ν / 256 := by exact min_le_left _ _
  have hζc : ζ ≤ 1 / 128 := by exact min_le_right _ _
  have hcoeff := eventually_coefficients_uniform hζ
  have hscale := APrimeFirstCellQVRunningProfile.eventually_running_scales
  have hWgrow := Dims.bandwidth_grow
  have hxi := Step2FarInputs.eventually_xiK_le B (mE 0).im (by positivity : 0 < ν / 16)
  have hlarge := eventually_le_rpow (max (5000 : ℝ) (256 * Real.exp 3))
    (by positivity : 0 < ν / 32)
  filter_upwards [hcoeff, hscale, hWgrow, hxi, hlarge,
    eventually_ge_atTop 2] with N hcoeff hscale hWgrow hxi hlarge hN2 u hu
  obtain ⟨_, _, _, hN, _, _, _, hWL, _⟩ := hscale u hu
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hbase : (1 : ℝ) ≤ N := by linarith
  have hWgrow' : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ) := by
    convert hWgrow using 1 <;> norm_num
  obtain ⟨hcN, hcF⟩ := hcoeff u hu
  obtain ⟨hn, hf2, hf3, hfL⟩ := row_bounds N u ζ ζ hN hζ.le hζ.le hu
    hWgrow' hWL hcN hcF
  let M : ℝ := (N : ℝ) ^ (ν / 16)
  have hC : max (5000 : ℝ) (256 * Real.exp 3) ≤ (N : ℝ) ^ (ν / 32) := hlarge
  have h5000 : (5000 : ℝ) ≤ (N : ℝ) ^ (ν / 32) :=
    (le_max_left _ _).trans hC
  have hexp : 256 * Real.exp 3 ≤ (N : ℝ) ^ (ν / 32) :=
    (le_max_right _ _).trans hC
  have hp32M : (N : ℝ) ^ (ν / 32) ≤ M := by
    dsimp [M]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hζpow : (N : ℝ) ^ (ζ + ζ) ≤ (N : ℝ) ^ (ν / 32) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase
    linarith
  have hMM : (N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32) = M := by
    dsimp [M]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hnM : APrimeQVEndpoint.diagNearRate B N (B.ell N u)
      (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ ≤ M := by
    calc
      _ ≤ 258 * (N : ℝ) ^ (ζ + ζ) := hn
      _ ≤ (N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32) := by
        exact mul_le_mul (by linarith [h5000]) hζpow (by positivity) (by positivity)
      _ = M := hMM
  have he2 : ζ + 1 / 4 + ζ / 2 - 5 / 16 ≤ 0 := by
    linarith
  have hpow2 : (N : ℝ) ^ (ζ + 1 / 4 + ζ / 2 - 5 / 16) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase he2
  have hf2M : farTwo N u (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤ M := by
    calc
      _ ≤ 128 * (N : ℝ) ^ (ζ + 1 / 4 + ζ / 2 - 5 / 16) := hf2
      _ ≤ 128 := by nlinarith
      _ ≤ (N : ℝ) ^ (ν / 32) := by linarith [h5000]
      _ ≤ M := hp32M
  have hpow3 : (N : ℝ) ^ ((3 / 8 - 5 / 8 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase
      (by norm_num : (3 / 8 - 5 / 8 : ℝ) ≤ 0)
  have hf3M : farThree N u ≤ M := by
    calc
      _ ≤ 4608 * (N : ℝ) ^ ((3 / 8 - 5 / 8 : ℝ)) := hf3
      _ ≤ 4608 := by nlinarith
      _ ≤ (N : ℝ) ^ (ν / 32) := by linarith [h5000]
      _ ≤ M := hp32M
  have hpowL : (N : ℝ) ^ ((1 + 3 / 8 - 15 / 8 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase
      (by norm_num : (1 + 3 / 8 - 15 / 8 : ℝ) ≤ 0)
  have hfLM : farLeak N ≤ M := by
    calc
      _ ≤ 32 * (N : ℝ) ^ ((1 + 3 / 8 - 15 / 8 : ℝ)) := hfL
      _ ≤ 32 := by nlinarith
      _ ≤ (N : ℝ) ^ (ν / 32) := by linarith [h5000]
      _ ≤ M := hp32M
  exact ⟨hnM, hf2M, hf3M, hfLM, hxi, hexp.trans hp32M,
    (by linarith [h5000, hp32M])⟩

set_option maxHeartbeats 1000000 in
theorem normalized_running_le (N : ℕ) (u ellSource S M : ℝ)
    (a : LoopArg (d.L N) 2)
    (hu0 : 0 ≤ u) (huv : u ≤ 1 / 2)
    (hW : 1 ≤ (d.W N : ℝ)) (hM : 1 ≤ M)
    (hn : APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹ ≤ M)
    (hf2 : farTwo N u S ≤ M) (hf3 : farThree N u ≤ M)
    (hfL : farLeak N ≤ M)
    (hxi : Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im ≤ M)
    (hconst : 256 * Real.exp 3 ≤ M) :
    (16 * Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)))⁻¹ *
        runningRootProfile N u ellSource S a ≤ 5 * M * √M := by
  let T : ℝ := Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1))
  let R : ℝ := ((1 - u) / (1 - (1 / 2 : ℝ))) ^ (2 : ℕ)
  let Xi : ℝ := Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im
  let χ : ℝ := if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
      6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then 1 else 0
  let An : ℝ := APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource
      (etaT 0 u) + 2 * (d.W N : ℝ)⁻¹
  let F2 : ℝ := farTwo N u S
  let F3 : ℝ := farThree N u
  let FL : ℝ := farLeak N
  have hT : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos (by linarith : 0 < (d.W N : ℝ)) _
  have hProf : runningRootProfile N u ellSource S a =
      T * R * (√An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi) := by
    dsimp [runningRootProfile, APrimeFirstCellQVSharpJ.nearKernel,
      APrimeFirstCellQVSharpJ.leakKernel,
      APrimeFirstCellQVSharpJ.endpointKernel]
    change √An * (R * Xi * T * χ) +
        √An * (256 * Real.exp 3 * R * (d.W N : ℝ) ^ (-(60 : ℝ)) * T) +
        √F2 * (R * Xi * T) + √F3 * (R * Xi * T) +
        √FL * (R * Xi * T) =
      T * R * (√An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi)
    ring
  have hEq : (16 * T)⁻¹ * runningRootProfile N u ellSource S a =
      R / 16 * (√An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi) := by
    rw [hProf]
    field_simp
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRle : R / 16 ≤ 1 := by
    dsimp [R]
    have hu1 : 0 ≤ 1 - u := by linarith
    have hu2 : 1 - u ≤ 1 := by linarith
    norm_num
    nlinarith [sq_nonneg (1 - u)]
  have hχ0 : 0 ≤ χ := by
    change 0 ≤ (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
        6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  have hχ1 : χ ≤ 1 := by
    change (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
        6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then (1 : ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  have hXi0 : 0 ≤ Xi := Step2.xiK_nonneg _ _ _
  have hXiLe : Xi ≤ M := hxi
  have hWpow0 : 0 ≤ (d.W N : ℝ) ^ (-(60 : ℝ)) := by positivity
  have hWpow1 : (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ 1 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hW
      (by norm_num : (-(60 : ℝ)) ≤ 0)
    simpa using hp
  have hLeakC : 256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ M := by
    calc
      _ ≤ 256 * Real.exp 3 * 1 := by gcongr
      _ ≤ M := by simpa using hconst
  have hM0 : 0 ≤ M := by linarith
  have hn' : √An ≤ √M := Real.sqrt_le_sqrt hn
  have hf2' : √F2 ≤ √M := Real.sqrt_le_sqrt hf2
  have hf3' : √F3 ≤ √M := Real.sqrt_le_sqrt hf3
  have hfL' : √FL ≤ √M := Real.sqrt_le_sqrt hfL
  have h1 : √An * Xi * χ ≤ M * √M := by
    calc
      _ ≤ √An * Xi * 1 :=
        mul_le_mul_of_nonneg_left hχ1 (mul_nonneg (Real.sqrt_nonneg _) hXi0)
      _ ≤ √M * M := by
        simpa using mul_le_mul hn' hXiLe hXi0 (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h2 : √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) ≤
      M * √M := by
    calc
      _ ≤ √M * M := mul_le_mul hn' hLeakC (by positivity) (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h3 : √F2 * Xi ≤ M * √M := by
    calc
      _ ≤ √M * M := mul_le_mul hf2' hXiLe hXi0 (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h4 : √F3 * Xi ≤ M * √M := by
    calc
      _ ≤ √M * M := mul_le_mul hf3' hXiLe hXi0 (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h5 : √FL * Xi ≤ M * √M := by
    calc
      _ ≤ √M * M := mul_le_mul hfL' hXiLe hXi0 (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have hsum : √An * Xi * χ +
      √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
      √F2 * Xi + √F3 * Xi + √FL * Xi ≤ 5 * M * √M := by
    linarith [h1, h2, h3, h4, h5]
  have hsum0 : 0 ≤ √An * Xi * χ +
      √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
      √F2 * Xi + √F3 * Xi + √FL * Xi := by positivity
  rw [hEq]
  calc
    R / 16 * (√An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi) ≤
      √An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hRle) hsum0]
    _ ≤ 5 * M * √M := hsum

set_option maxHeartbeats 1000000 in
theorem eventually_normalized_running_le {ν : ℝ} (hν : 0 < ν) :
    let ζ := min (ν / 256) (1 / 128)
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ a : LoopArg (d.L N) 2,
      (16 * Step2.tT B 0 N 60 (1 / 2)
        (zdist (d.L N) (a 0 - a 1)))⁻¹ *
          runningRootProfile N u
            (APrimeFirstCellSourceAllTime.ellSource ζ N)
            (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) a ≤
        (N : ℝ) ^ (ν / 4) := by
  dsimp only
  let ζ : ℝ := min (ν / 256) (1 / 128)
  have hrows := eventually_rows_le_power hν
  have hscale := APrimeFirstCellQVRunningProfile.eventually_running_scales
  filter_upwards [hrows, hscale, eventually_ge_atTop 2] with
    N hrows hscale hN2 u hu a
  dsimp only at hrows
  obtain ⟨hn, hf2, hf3, hfL, hxi, hconst, h25⟩ := hrows u hu
  obtain ⟨hW, _, _, hN, _, _, _, _, _⟩ := hscale u hu
  have hW1 : 1 ≤ (d.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hW
  let M : ℝ := (N : ℝ) ^ (ν / 16)
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact Real.one_le_rpow hN (by positivity)
  have hbase := normalized_running_le N u
    (APrimeFirstCellSourceAllTime.ellSource ζ N)
    (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) M a
    hu.1 hu.2 hW1 hM1 hn hf2 hf3 hfL hxi hconst
  have hsqrt5 : (5 : ℝ) ≤ √M := by
    nlinarith [Real.sq_sqrt hM0, Real.sqrt_nonneg M]
  have hfive : 5 * √M ≤ M := by
    nlinarith [Real.sq_sqrt hM0,
      mul_nonneg (sub_nonneg.mpr hsqrt5) (Real.sqrt_nonneg M)]
  have hproduct : 5 * M * √M ≤ M ^ (2 : ℕ) := by
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hfive)]
  have hMpow : M ^ (2 : ℕ) = (N : ℝ) ^ (ν / 8) := by
    dsimp [M]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have hpow : (N : ℝ) ^ (ν / 8) ≤ (N : ℝ) ^ (ν / 4) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N)
    linarith
  exact hbase.trans (hproduct.trans (hMpow.le.trans hpow))

theorem normalized_running_nonneg (N : ℕ) (u ellSource S : ℝ)
    (a : LoopArg (d.L N) 2) (hW : 0 ≤ (d.W N : ℝ)) :
    0 ≤ (16 * Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)))⁻¹ *
        runningRootProfile N u ellSource S a := by
  have hT : 0 ≤ Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)) := by
    dsimp [Step2.tT]
    exact tailT_nonneg hW _
  have hXi : 0 ≤ Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im :=
    Step2.xiK_nonneg _ _ _
  have hWpow : 0 ≤ (d.W N : ℝ) ^ (-(60 : ℝ)) :=
    Real.rpow_nonneg hW _
  have hchi : 0 ≤ (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
      6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  unfold runningRootProfile APrimeFirstCellQVSharpJ.nearKernel
    APrimeFirstCellQVSharpJ.leakKernel APrimeFirstCellQVSharpJ.endpointKernel
  positivity

private theorem running_mem_firstCell {τ' : ℝ} (hτ' : 0 < τ')
    {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    r ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
  have hwin : (fun _ : ℕ => (0 : ℝ)) N ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hmesh := APrimeSupportRunning.mesh_pos N
  have htop := MomentDuhamelCut.netFinset_subset_Icc hwin hmesh _
    (cutNetPt_mem_netFinset hk)
  rw [APrimeSupportRunning.firstS_eq]
  exact ⟨hr.1, hr.2.trans htop.2⟩

private theorem qvAt_le_rpow_of_profile {ν ζ : ℝ} (hν : 0 < ν)
    {N : ℕ} {ω : Ω d} {r : ℝ} (a : LoopArg (d.L N) 2)
    (hN : 1 ≤ (N : ℝ)) (hr : r ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hcap : APrimeSupportRunning.jG N r ω ≤ capJ N)
    (hprof : APrimeFirstCellQVRunningProfile.profileAt ζ N ω r a)
    (hnorm : (16 * Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)))⁻¹ *
        runningRootProfile N r
          (APrimeFirstCellSourceAllTime.ellSource ζ N)
          (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) a ≤
      (N : ℝ) ^ (ν / 4)) :
    APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2) r ω ≤
      (N : ℝ) ^ ν := by
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hℓ : 0 < B.ell N r := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_ellHat_of_nonneg (by
          have h : 3 ≤ B.L N := by simpa using d.three_le_L N
          omega)
        hr.1 (hr.2.trans_lt (by norm_num)))
  have hη : 0 < etaT 0 r := by
    rw [show etaT 0 r = 1 - r by norm_num [etaT, Gauss.mE_zero]]
    linarith [hr.2]
  have hS : 0 ≤ APrimeFirstCellSourceAllTime.sourceC4 ζ N r := by
    unfold APrimeFirstCellSourceAllTime.sourceC4 Band.scale
    positivity
  have hJ0 : 0 ≤ APrimeSupportRunning.jG N r ω := by
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (APrimeJG.one_le_jG (sample d) 0 N r ω
        (by exact_mod_cast d.W_pos N))
  have hroot := rootProfile_le_running N r
    (APrimeFirstCellSourceAllTime.ellSource ζ N)
    (APrimeSupportRunning.jG N r ω)
    (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) a
    hW hℓ hη hS hJ0 hcap
  have hT : 0 < Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)) := by
    dsimp [Step2.tT]
    exact tailT_pos (by linarith : 0 < (d.W N : ℝ)) _
  have hscaled :
      (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2))⁻¹ *
        APrimeFullQV.rootProfile B 0 N r (1 / 2) 60
          (APrimeFirstCellSourceAllTime.ellSource ζ N)
          (APrimeSupportRunning.jG N r ω)
          (APrimeFirstCellSourceAllTime.sourceC4 ζ N r)
          ((d.W N : ℝ)⁻¹) a ≤
      (16 * Step2.tT B 0 N 60 (1 / 2)
        (zdist (d.L N) (a 0 - a 1)))⁻¹ *
          runningRootProfile N r
            (APrimeFirstCellSourceAllTime.ellSource ζ N)
            (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) a := by
    rw [APrimeFirstCellQVSharpJ.driftScale_eq_sixteen]
    exact mul_le_mul_of_nonneg_left hroot (by positivity)
  have hroot0 : 0 ≤ APrimeFullQV.rootProfile B 0 N r (1 / 2) 60
      (APrimeFirstCellSourceAllTime.ellSource ζ N)
      (APrimeSupportRunning.jG N r ω)
      (APrimeFirstCellSourceAllTime.sourceC4 ζ N r)
      ((d.W N : ℝ)⁻¹) a := by
    have htail : 0 ≤ Step2.tT B 0 N 60 (1 / 2)
        (zdist (d.L N) (a 0 - a 1)) := hT.le
    have hxi : 0 ≤ Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im :=
      Step2.xiK_nonneg _ _ _
    have hchi : 0 ≤ (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
        6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    unfold APrimeFullQV.rootProfile
    positivity
  have hscale0 : 0 ≤
      (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2))⁻¹ := by
    rw [APrimeFirstCellQVSharpJ.driftScale_eq_sixteen]
    positivity
  have hleft0 : 0 ≤
      (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2))⁻¹ *
        APrimeFullQV.rootProfile B 0 N r (1 / 2) 60
          (APrimeFirstCellSourceAllTime.ellSource ζ N)
          (APrimeSupportRunning.jG N r ω)
          (APrimeFirstCellSourceAllTime.sourceC4 ζ N r)
          ((d.W N : ℝ)⁻¹) a := mul_nonneg hscale0 hroot0
  have hsq1 := pow_le_pow_left₀ hleft0 hscaled 2
  have hnorm0 := normalized_running_nonneg N r
    (APrimeFirstCellSourceAllTime.ellSource ζ N)
    (APrimeFirstCellSourceAllTime.sourceC4 ζ N r) a
    ((by norm_num : (0 : ℝ) ≤ 1).trans hW)
  have hsq2 := pow_le_pow_left₀ hnorm0 hnorm 2
  have hpow : ((N : ℝ) ^ (ν / 4)) ^ (2 : ℕ) ≤ (N : ℝ) ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    apply Real.rpow_le_rpow_of_exponent_le hN
    linarith
  exact hprof.trans (hsq1.trans (hsq2.trans hpow))

set_option maxHeartbeats 1000000 in
theorem eventually_running_qv_le {τ' ν : ℝ} (hτ' : 0 < τ') (hν : 0 < ν) :
    let ζ := min (ν / 256) (1 / 128)
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight (1 / 100)
          (firstCellT τ') N0 p N k m ω →
        ∀ r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k),
          ∀ a : LoopArg (d.L N) 2,
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2) r ω ≤
            (N : ℝ) ^ ν := by
  dsimp only
  let ζ : ℝ := min (ν / 256) (1 / 128)
  have hprof := APrimeFirstCellQVRunningProfile.eventually_running_profile
    (ζ := ζ) hτ'
  have hnorm := eventually_normalized_running_le hν
  filter_upwards [hprof, hnorm, eventually_ge_atTop 1] with N hprof hnorm hNnat ω hω
    N0 p k m hN0 hp hm hk1 hk hw r hr a
  obtain ⟨hcap, hraw⟩ := hprof ω hω N0 p k m hN0 hp hm hk1 hk hw r hr
  have hrmem := running_mem_firstCell hτ' hk hr
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hrmem.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  have hN : 1 ≤ (N : ℝ) := by
    exact_mod_cast hNnat
  exact qvAt_le_rpow_of_profile hν a hN hrhalf hcap (hraw a) (hnorm r hrhalf a)

def positiveSmallPlateau (τ' ν : ℝ) : Prop :=
  let ζ := min (ν / 256) (1 / 128)
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈ APrimeFirstCellSourceSupport.jointEvent τ' ζ N,
    ∃ u1 u2 : TimeIcc (firstCellS τ') (firstCellT τ') N,
      0 < (u1 : ℝ) ∧
      (u1 : ℝ) = (N : ℝ) ^ (-(248 : ℝ)) ∧
      (u2 : ℝ) = 2 * (N : ℝ) ^ (-(248 : ℝ)) ∧
      (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100)
        (firstCellT τ') 2 p N 2 N ω = 1) ∧
      APrimeFullQV.SourceEvent (sample d) 0 N (u1 : ℝ) ω
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N u1) ∧
      APrimeFullQV.SourceEvent (sample d) 0 N (u2 : ℝ) ω
        (APrimeFirstCellSourceAllTime.ellSource ζ N)
        (APrimeFirstCellSourceAllTime.sourceC4 ζ N u2) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) (u2 : ℝ),
        APrimeSupportRunning.jG N r ω ≤ capJ N ∧
        ∀ a : LoopArg (d.L N) 2,
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2) r ω ≤
            (N : ℝ) ^ ν

set_option maxHeartbeats 1000000 in
theorem positiveSmallPlateau_of_profile {τ' ν : ℝ}
    (hτ' : 0 < τ') (hν : 0 < ν)
    (hp : APrimeFirstCellQVRunningProfile.positiveProfilePlateau τ'
      (min (ν / 256) (1 / 128))) :
    positiveSmallPlateau τ' ν := by
  let ζ : ℝ := min (ν / 256) (1 / 128)
  have hnorm := eventually_normalized_running_le hν
  filter_upwards [hp, hnorm, eventually_ge_atTop 1] with N hp hnorm hNnat
  obtain ⟨ω, hω, u1, u2, hu1pos, hu1eq, hu2eq, hw,
    hsource1, hsource2, hprof⟩ := hp
  refine ⟨ω, hω, u1, u2, hu1pos, hu1eq, hu2eq, hw,
    hsource1, hsource2, ?_⟩
  intro r hr
  obtain ⟨hcap, hraw⟩ := hprof r hr
  refine ⟨hcap, ?_⟩
  intro a
  have hu2half : (u2 : ℝ) ≤ 1 / 2 :=
    u2.property.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hrhalf : r ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hr.1, hr.2.trans hu2half⟩
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast hNnat
  exact qvAt_le_rpow_of_profile hν a hN hrhalf hcap (hraw a) (hnorm r hrhalf a)

/-- A single T395 event supports the positive two-point active plateau and
the uniform running first-cell quadratic-variation bound. -/
theorem exists_running_qv_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ν : ℝ, 0 < ν →
      let ζ := min (ν / 256) (1 / 128)
      (∀ N, MeasurableSet (APrimeFirstCellSourceSupport.jointEvent τ' ζ N)) ∧
      HighProb (P d) (APrimeFirstCellSourceSupport.jointEvent τ' ζ) ∧
      positiveSmallPlateau τ' ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQVRunningProfile.exists_running_profile_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro ν hν
  dsimp only
  have hζ : 0 < min (ν / 256) (1 / 128) :=
    lt_min (by positivity) (by norm_num)
  obtain ⟨hmeas, hp, hplat⟩ := hall _ hζ
  exact ⟨hmeas, hp, positiveSmallPlateau_of_profile hτ' hν hplat⟩

#print axioms eventually_coefficients_uniform
#print axioms source_scale_sqrt_le
#print axioms row_bounds
#print axioms eventually_rows_le_power
#print axioms normalized_running_le
#print axioms eventually_normalized_running_le
#print axioms eventually_running_qv_le
#print axioms positiveSmallPlateau_of_profile
#print axioms exists_running_qv_with_plateau

end RBM.APrimeFirstCellQVRunningSmall
