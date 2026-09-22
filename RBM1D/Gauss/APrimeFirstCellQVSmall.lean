/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVSharpJ
import RBM1D.Gauss.APrimeFirstCellEGNearSmall

/-! T397: power absorption of the actual first-cut-time evolved QV. -/

namespace RBM.APrimeFirstCellQVSmall

open Filter Gauss APrimeFirstCellJGCap APrimeFirstCellQVSharpJ
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- The stronger near coefficient is controlled by the fourth power of the
one-loop coefficient on the bounded first-cell scale. -/
theorem cNear2_le_cNear_pow_four {W ell : ℝ}
    (hW : 1 ≤ W) (hℓ : 0 < ell) (hℓ2 : ell ≤ 2) :
    Lemma57.cNear2 W ell ≤ Lemma57.cNear W ell ^ (4 : ℕ) := by
  let x : ℝ := Real.log W ^ (3 / 4 : ℝ)
  let P : ℝ := 2 * Real.log W ^ (3 : ℝ) + 2 / ell
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have hP : 1 ≤ P := by
    have hdiv : 1 ≤ 2 / ell := (le_div_iff₀ hℓ).2 (by linarith)
    dsimp [P]
    have hp : 0 ≤ Real.log W ^ (3 : ℝ) := Real.rpow_nonneg hlog _
    linarith
  have hPpow : P ≤ P ^ (4 : ℕ) := by
    nlinarith [sq_nonneg (P - 1), sq_nonneg (P ^ 2 - 1)]
  have he : Real.exp (4 * x) = Real.exp x ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    ring
  unfold Lemma57.cNear2 Lemma57.cNear
  change P * Real.exp (4 * x) ≤ (P * Real.exp x) ^ (4 : ℕ)
  rw [he, mul_pow]
  exact mul_le_mul_of_nonneg_right hPpow (by positivity)

/-- The far logarithmic coefficient is bounded by twice the stronger near
coefficient once `log W≥1`. -/
theorem cFar2_le_two_cNear2 {W ell : ℝ}
    (hW : Real.exp 1 ≤ W) (hℓ : 0 < ell) :
    Lemma57.cFar2 W ell ≤ 2 * Lemma57.cNear2 W ell := by
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hlog1 : 1 ≤ Real.log W := by
    have := Real.log_le_log (Real.exp_pos 1) hW
    simpa using this
  let x : ℝ := Real.log W ^ (3 / 4 : ℝ)
  let y : ℝ := Real.log W ^ (3 / 2 : ℝ)
  have hxy : y ^ (2 : ℕ) = Real.log W ^ (3 : ℝ) := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log W)]
    norm_num
  have hy1 : 1 ≤ y := by
    dsimp [y]
    exact Real.one_le_rpow hlog1 (by norm_num)
  have hpoly : 4 * y + 4 / ell ≤ 2 * (2 * Real.log W ^ (3 : ℝ) + 2 / ell) := by
    rw [← hxy]
    have hsq : y ≤ y ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (by linarith : 0 ≤ y)]
    linear_combination 4 * hsq
  have hexp : Real.exp x ≤ Real.exp (4 * x) := by
    apply Real.exp_le_exp.mpr
    have hx : 0 ≤ x := Real.rpow_nonneg (Real.log_nonneg hW1) _
    linarith
  have hp0 : 0 ≤ 2 * Real.log W ^ (3 : ℝ) + 2 / ell := by positivity
  unfold Lemma57.cFar2 Lemma57.cNear2 Lemma57.loss1
  change (4 * y + 4 / ell) * Real.exp x ≤
    2 * ((2 * Real.log W ^ (3 : ℝ) + 2 / ell) * Real.exp (4 * x))
  nlinarith [mul_nonneg (sub_nonneg.mpr hpoly) (Real.exp_pos x).le,
    mul_nonneg hp0 (sub_nonneg.mpr hexp)]

/-- On the first half-cell the spatial scale never exceeds two. -/
theorem ell_firstHalf_le_two (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) : B.ell N u ≤ 2 := by
  have hu1 : u < 1 := hu.trans_lt (by norm_num)
  have hh := Step3.ellHat_le_sqrt_mul (L := d.L N) (s := 0) (t := u) hu0 hu1
  have hz : ellHat (d.L N) ((0 : ℝ) : ℂ) = 1 := by
    simpa using ellHat_zero (d.L N) (d.three_le_L N)
  rw [hz, mul_one] at hh
  have hden : 0 < 1 - u := by linarith
  have hfrac : (1 : ℝ) / (1 - u) ≤ 2 :=
    (div_le_iff₀ hden).2 (by linarith)
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_nonneg (2 : ℝ)]
  have hsq : Real.sqrt ((1 : ℝ) / (1 - u)) ≤ 2 :=
    (Real.sqrt_le_sqrt hfrac).trans hsqrt2
  have hresult := hh.trans (by simpa only [sub_zero] using hsq)
  change ellHat (d.L N) (u : ℂ) ≤ 2
  exact hresult

/-- The complete squared-QV near coefficient is subpolynomial at the
literal first cut time. -/
theorem eventually_cNear2_le {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop,
      Lemma57.cNear2 (d.W N : ℝ) (B.ell N (firstTime N)) ≤
        (N : ℝ) ^ τ := by
  have htime := APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime
    (τ' := 1) (by norm_num)
  have hc := APrimeFirstCellEGNearSmall.eventually_cNear_le
    (τ' := 1) (by norm_num) hτ
  filter_upwards [htime, hc, eventually_ge_atTop 1] with N htime hc hN
  have hmem := APrimeFirstCellNearSources.sourceTime_mem
    (τ' := 1) (by norm_num) N
  have ht : APrimeFirstCellNearSources.sourceTime 1 N ≤ 1 / 2 :=
    hmem.2.trans (gridT_le (1 / 2 : ℝ) 1)
  have hs : Gauss.firstCellS 1 N = 0 := by
    unfold Gauss.firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hu0 : 0 ≤ APrimeFirstCellNearSources.sourceTime 1 N := by
    rw [← hs]
    exact hmem.1
  have hℓ2 := ell_firstHalf_le_two N hu0 ht
  have hℓ : 0 < B.ell N (APrimeFirstCellNearSources.sourceTime 1 N) := by
    have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
    have hh := one_le_ellHat_of_nonneg hL hu0 (ht.trans_lt (by norm_num))
    change 1 ≤ B.ell N (APrimeFirstCellNearSources.sourceTime 1 N) at hh
    linarith
  have hW : 1 ≤ (d.W N : ℝ) := by
    exact_mod_cast d.W_pos N
  have hpow := cNear2_le_cNear_pow_four hW hℓ hℓ2
  rw [htime.1] at hc hpow
  rw [htime.1] at hℓ
  have hcn0 := Lemma57.cNear_nonneg hW hℓ
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc
    _ ≤ Lemma57.cNear (d.W N : ℝ) (B.ell N (firstTime N)) ^ (4 : ℕ) := hpow
    _ ≤ ((N : ℝ) ^ (τ / 4)) ^ (4 : ℕ) := by gcongr
    _ = (N : ℝ) ^ τ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr]
      congr 1
      ring

theorem eventually_cFar2_le {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop,
      Lemma57.cFar2 (d.W N : ℝ) (B.ell N (firstTime N)) ≤
        (N : ℝ) ^ τ := by
  have hτ2 : 0 < τ / 2 := by positivity
  have hc := eventually_cNear2_le hτ2
  have htwo := eventually_le_rpow 2 hτ2
  have htime := APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime
    (τ' := 1) (by norm_num)
  filter_upwards [hc, htwo, htime,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales]
    with N hc htwo htime hsc
  obtain ⟨hW, _, _, hN, _, _, _, _, _⟩ := hsc
  have hℓ : 0 < B.ell N (firstTime N) := by
    have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
    have hu0 : 0 ≤ firstTime N := by rw [← htime.1]; exact htime.2.le
    have hu1 : firstTime N < 1 := by
      rw [← htime.1]
      exact APrimeFirstCellNearSources.sourceTime_lt_one (by norm_num) N
    have hh := one_le_ellHat_of_nonneg hL hu0 hu1
    change 1 ≤ B.ell N (firstTime N) at hh
    linarith
  have hcf := cFar2_le_two_cNear2 hW hℓ
  have hNpos : (0 : ℝ) < N := by
    linarith
  have hc0 : 0 ≤ Lemma57.cNear2 (d.W N : ℝ) (B.ell N (firstTime N)) :=
    Lemma57.cNear2_nonneg ((Real.one_le_exp (by norm_num)).trans hW) hℓ
  calc
    _ ≤ 2 * Lemma57.cNear2 (d.W N : ℝ) (B.ell N (firstTime N)) := hcf
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by gcongr
    _ = (N : ℝ) ^ τ := by rw [← Real.rpow_add hNpos]; ring

private theorem sourceEll_fifth (N : ℕ) (ζ : ℝ) (hN : 0 < (N : ℝ)) :
    (sourceEll ζ N) ^ (5 : ℕ) = (2 * (N : ℝ) ^ ζ)⁻¹ := by
  unfold sourceEll
  have hx : 0 ≤ 2 * (N : ℝ) ^ ζ := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  rw [Real.rpow_neg_one, mul_inv_rev]
  ring

/-- The six-loop source factor has exactly one `N^ζ` loss. -/
theorem source_near_ratio_fifth (N : ℕ) (ζ ell : ℝ)
    (hN : 0 < (N : ℝ)) :
    (ell / sourceEll ζ N) ^ (5 : ℕ) =
      2 * (N : ℝ) ^ ζ * ell ^ (5 : ℕ) := by
  have hs := sourceEll_fifth N ζ hN
  have hsp : 0 < sourceEll ζ N := by
    unfold sourceEll
    positivity
  rw [div_pow, hs]
  field_simp

/-- The factor `A sqrt(Smax)` in the J² row cancels two of the three
inverse powers of the actual source scale `A`. -/
theorem source_far_square (N : ℕ) (ζ : ℝ) (hN : 2 ≤ N) :
    (B.scale 0 N (firstTime N)) ^ (2 : ℕ) *
        sourceC4 ζ N =
      (N : ℝ) ^ ζ * (B.ell N (firstTime N)) ^ (3 : ℕ) *
        (B.scale 0 N (firstTime N))⁻¹ := by
  unfold sourceC4
  have hA : 0 < B.scale 0 N (firstTime N) := by
    have hu0 : 0 ≤ firstTime N := by unfold firstTime; positivity
    have hu1 : firstTime N < 1 := by
      unfold firstTime
      have hn : (1 : ℝ) < N := by exact_mod_cast hN
      have hp : 1 < (N : ℝ) ^ (248 : ℕ) := one_lt_pow₀ hn (by norm_num)
      have hi := (inv_lt_one₀ (by positivity : 0 < (N : ℝ) ^ (248 : ℕ))).2 hp
      exact hi
    exact B.scale_pos' (by norm_num) N hu0 hu1
  field_simp

/-- A deliberately coarse but uniform power bound for the quadratic block
source. The exact identity above retains the useful inverse `A` factor. -/
theorem source_A_sqrt_le (N : ℕ) (ζ : ℝ) (hN : 2 ≤ N)
    (hA : 1 ≤ B.scale 0 N (firstTime N))
    (hℓ0 : 0 ≤ B.ell N (firstTime N))
    (hℓ2 : B.ell N (firstTime N) ≤ 2)
    (hQ : 1 ≤ (N : ℝ) ^ ζ) :
    B.scale 0 N (firstTime N) * √(sourceC4 ζ N) ≤
      3 * (N : ℝ) ^ ζ := by
  let A := B.scale 0 N (firstTime N)
  let ℓ := B.ell N (firstTime N)
  let Q := (N : ℝ) ^ ζ
  have hApos : 0 < A := by dsimp [A]; linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; linarith
  have hS : 0 ≤ sourceC4 ζ N := by
    unfold sourceC4
    positivity
  have hℓ3 : ℓ ^ (3 : ℕ) ≤ 8 := by
    calc
      ℓ ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) := by gcongr
      _ = 8 := by norm_num
  have hInv : A⁻¹ ≤ 1 := (inv_le_one₀ hApos).2 hA
  have hEq : A ^ (2 : ℕ) * sourceC4 ζ N = Q * ℓ ^ (3 : ℕ) * A⁻¹ :=
    source_far_square N ζ hN
  have hBound : A ^ (2 : ℕ) * sourceC4 ζ N ≤ 8 * Q := by
    rw [hEq]
    calc
      Q * ℓ ^ (3 : ℕ) * A⁻¹ ≤ Q * ℓ ^ (3 : ℕ) * 1 := by
        gcongr
      _ ≤ Q * 8 := by simpa using mul_le_mul_of_nonneg_left hℓ3 hQ0
      _ = 8 * Q := by ring
  have hSq : (A * √(sourceC4 ζ N)) ^ (2 : ℕ) =
      A ^ (2 : ℕ) * sourceC4 ζ N := by
    rw [mul_pow, Real.sq_sqrt hS]
  have hQsq : 8 * Q ≤ (3 * Q) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hQ0]
  nlinarith [hSq, hBound, hQsq, Real.sqrt_nonneg (sourceC4 ζ N)]

/-- Uniform deterministic bounds for every row of T392's profile. The
spatial leakage retains the literal `W⁻⁶⁰` before `N≤W²` is used. -/
theorem row_coefficients_le (N : ℕ) (ζ τ : ℝ) (hN : 2 ≤ N)
    (hW : 1 ≤ (d.W N : ℝ))
    (hℓ1 : 1 ≤ B.ell N (firstTime N))
    (hℓ2 : B.ell N (firstTime N) ≤ 2)
    (hη : 1 / 2 ≤ etaT 0 (firstTime N))
    (hA : 1 ≤ B.scale 0 N (firstTime N))
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ (2 : ℕ))
    (hQ : 1 ≤ (N : ℝ) ^ ζ)
    (hP : 1 ≤ (N : ℝ) ^ τ)
    (hcN : Lemma57.cNear2 (d.W N : ℝ) (B.ell N (firstTime N)) ≤
      (N : ℝ) ^ τ)
    (hcF : Lemma57.cFar2 (d.W N : ℝ) (B.ell N (firstTime N)) ≤
      (N : ℝ) ^ τ) :
    APrimeQVEndpoint.diagNearRate B N (B.ell N (firstTime N))
      (sourceEll ζ N) (etaT 0 (firstTime N)) +
        2 * (d.W N : ℝ)⁻¹ ≤ 258 * (N : ℝ) ^ τ * (N : ℝ) ^ ζ ∧
    farTwo N (firstTime N) (sourceC4 ζ N) ≤
      384 * (N : ℝ) ^ τ * (N : ℝ) ^ ζ ∧
    farThree N (firstTime N) ≤ 18432 ∧
    farLeak N (firstTime N) ≤ 256 := by
  let u := firstTime N
  let ell := B.ell N u
  let eta := etaT 0 u
  let A := B.scale 0 N u
  let Q := (N : ℝ) ^ ζ
  let P := (N : ℝ) ^ τ
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hetaPos : 0 < eta := by dsimp [eta]; linarith
  have hetaInv : eta⁻¹ ≤ 2 := by
    simpa using (inv_le_inv₀ hetaPos (by norm_num : (0 : ℝ) < 1 / 2)).2 hη
  have hApos : 0 < A := by dsimp [A]; linarith
  have hAinv : A⁻¹ ≤ 1 := (inv_le_one₀ hApos).2 hA
  have hWInv : (d.W N : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith : 0 < (d.W N : ℝ))).2 hW
  have hWneg : (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ 1 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hW (by norm_num : (-(60 : ℝ)) ≤ 0)
    simpa using hp
  have hℓ5 : ell ^ (5 : ℕ) ≤ 32 := by
    calc
      ell ^ (5 : ℕ) ≤ (2 : ℝ) ^ (5 : ℕ) := by gcongr
      _ = 32 := by norm_num
  have hratio : (ell / sourceEll ζ N) ^ (5 : ℕ) ≤ 64 * Q := by
    rw [source_near_ratio_fifth N ζ ell hNr]
    have hQ0 : 0 ≤ Q := by dsimp [Q]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hℓ5) hQ0]
  have hnear0 : 0 ≤ Lemma57.cNear2 (d.W N : ℝ) ell :=
    Lemma57.cNear2_nonneg hW (by dsimp [ell]; linarith)
  have hfar0 : 0 ≤ Lemma57.cFar2 (d.W N : ℝ) ell :=
    Lemma57.cFar2_nonneg hW (by dsimp [ell]; linarith)
  have hP0 : 0 ≤ P := by dsimp [P]; linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; linarith
  have hPQ : 1 ≤ P * Q := by nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hQ)]
  have hNear : APrimeQVEndpoint.diagNearRate B N ell (sourceEll ζ N) eta +
        2 * (d.W N : ℝ)⁻¹ ≤ 258 * P * Q := by
    unfold APrimeQVEndpoint.diagNearRate
    have hratio0 : 0 ≤ (ell / sourceEll ζ N) ^ (5 : ℕ) := by
      have hspos : 0 < sourceEll ζ N := by unfold sourceEll; positivity
      have hellpos : 0 < ell := by dsimp [ell]; linarith
      positivity
    have hmain : 2 * eta⁻¹ * Lemma57.cNear2 (d.W N : ℝ) ell *
        (ell / sourceEll ζ N) ^ (5 : ℕ) ≤ 256 * P * Q := by
      calc
        _ ≤ 2 * 2 * P * (64 * Q) := by gcongr
        _ = 256 * P * Q := by ring
    calc
      2 * eta⁻¹ * Lemma57.cNear2 (d.W N : ℝ) ell *
          (ell / sourceEll ζ N) ^ (5 : ℕ) + 2 * (d.W N : ℝ)⁻¹ ≤
        256 * P * Q + 2 := by linarith
      _ ≤ 258 * P * Q := by nlinarith [hPQ]
  have hAS : A * √(sourceC4 ζ N) ≤ 3 * Q :=
    source_A_sqrt_le N ζ hN hA (by linarith) hℓ2 hQ
  have hF2 : farTwo N u (sourceC4 ζ N) ≤ 384 * P * Q := by
    unfold farTwo
    change 2 * eta⁻¹ * Lemma57.cFar2 (d.W N : ℝ) ell *
      (4 ^ (2 : ℕ) * (A * (2 * √(sourceC4 ζ N)))) ≤ 384 * P * Q
    have hprod : A * (2 * √(sourceC4 ζ N)) ≤ 6 * Q := by nlinarith [hAS]
    calc
      _ ≤ 2 * 2 * P * ((4 : ℝ) ^ (2 : ℕ) * (6 * Q)) := by gcongr
      _ = 384 * P * Q := by norm_num; ring
  have hF3 : farThree N u ≤ 18432 := by
    unfold farThree
    change 2 * eta⁻¹ * 72 * 4 ^ (3 : ℕ) * A⁻¹ ≤ 18432
    calc
      _ ≤ 2 * 2 * 72 * (4 : ℝ) ^ (3 : ℕ) * 1 := by gcongr
      _ = 18432 := by norm_num
  have hFL : farLeak N u ≤ 256 := by
    unfold farLeak
    have hWL' : (d.W N : ℝ) * (d.L N : ℝ) ≤ (d.W N : ℝ) ^ (2 : ℕ) :=
      hWL.trans hNW
    have hWfloor : (d.W N : ℝ) ^ (2 : ℕ) *
        (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ 1 := by
      have hw2 : 0 ≤ (d.W N : ℝ) ^ (2 : ℕ) := by positivity
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : 0 < (d.W N : ℝ))]
      have hp := Real.rpow_le_rpow_of_exponent_le hW
        (by norm_num : (2 : ℝ) + (-(60 : ℝ)) ≤ 0)
      simpa using hp
    have hprod : (d.W N : ℝ) * (d.L N : ℝ) *
        (d.W N : ℝ) ^ (-(60 : ℝ)) ≤ 1 := by
      calc
        _ ≤ (d.W N : ℝ) ^ (2 : ℕ) * (d.W N : ℝ) ^ (-(60 : ℝ)) := by
          gcongr
        _ ≤ 1 := hWfloor
    nlinarith
  exact ⟨hNear, hF2, hF3, hFL⟩

set_option maxHeartbeats 1000000 in
-- The default heartbeat limit is insufficient for the expanded eventual filter arithmetic.
/-- Every row has strict power slack at the first cut time. The proof uses
the literal `W⁻⁶⁰` tail floor in `farLeak`; the stronger negative exponents
from T376 are not needed for this uniform upper bound. -/
theorem eventually_rows_le_power {ν : ℝ} (hν : 0 < ν) :
    let ζ := ν / 32
    ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (ν / 8)
      APrimeQVEndpoint.diagNearRate B N (B.ell N (firstTime N))
        (sourceEll ζ N) (etaT 0 (firstTime N)) +
          2 * (d.W N : ℝ)⁻¹ ≤ M ∧
      farTwo N (firstTime N) (sourceC4 ζ N) ≤ M ∧
      farThree N (firstTime N) ≤ M ∧
      farLeak N (firstTime N) ≤ M ∧
      Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im ≤ M ∧
      256 * Real.exp 3 ≤ M ∧
      25 ≤ M := by
  dsimp only
  have hζ : 0 < ν / 32 := by positivity
  have hν16 : 0 < ν / 16 := by positivity
  have hν8 : 0 < ν / 8 := by positivity
  have hnear := eventually_cNear2_le hζ
  have hfar := eventually_cFar2_le hζ
  have hxi := Step2FarInputs.eventually_xiK_le B (mE 0).im hν8
  have hlarge := eventually_le_rpow (max (20000 : ℝ) (256 * Real.exp 3)) hν16
  have htime := APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime
    (τ' := 1) (by norm_num)
  filter_upwards [hnear, hfar, hxi, hlarge, htime,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    eventually_ge_atTop 2] with N hnear hfar hxi hlarge htime hsc hN2
  obtain ⟨hW, _, _, hN1, _, hA1, _, hWL, hNW⟩ := hsc
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hW1 : 1 ≤ (d.W N : ℝ) := (Real.one_le_exp (by norm_num)).trans hW
  have hu0 : 0 ≤ firstTime N := by rw [← htime.1]; exact htime.2.le
  have hmem := APrimeFirstCellNearSources.sourceTime_mem
    (τ' := 1) (by norm_num) N
  have huv : firstTime N ≤ 1 / 2 := by
    rw [← htime.1]
    exact hmem.2.trans (gridT_le (1 / 2 : ℝ) 1)
  have hℓ1 : 1 ≤ B.ell N (firstTime N) :=
    one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega)
      hu0 (huv.trans_lt (by norm_num))
  have hℓ2 : B.ell N (firstTime N) ≤ 2 := ell_firstHalf_le_two N hu0 huv
  have hη : (1 / 2 : ℝ) ≤ etaT 0 (firstTime N) := by
    rw [show etaT 0 (firstTime N) = 1 - firstTime N by
      norm_num [etaT, Gauss.mE_zero]]
    linarith
  have hA : 1 ≤ B.scale 0 N (firstTime N) := by
    change 1 ≤ (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N)
    exact hA1
  have hQ : 1 ≤ (N : ℝ) ^ (ν / 32) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hn, hf2, hf3, hfL⟩ := row_coefficients_le N (ν / 32) (ν / 32)
    hN2 hW1 hℓ1 hℓ2 hη hA hWL hNW hQ hQ hnear hfar
  have hPow : (N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32) =
      (N : ℝ) ^ (ν / 16) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hM : (N : ℝ) ^ (ν / 8) =
      (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hp1 : 1 ≤ (N : ℝ) ^ (ν / 16) :=
    Real.one_le_rpow (by linarith) (by positivity)
  have hlarge' : (20000 : ℝ) ≤ (N : ℝ) ^ (ν / 16) :=
    (le_max_left _ _).trans hlarge
  have hconst : 256 * Real.exp 3 ≤ (N : ℝ) ^ (ν / 16) :=
    (le_max_right _ _).trans hlarge
  have hnearM : APrimeQVEndpoint.diagNearRate B N (B.ell N (firstTime N))
      (sourceEll (ν / 32) N) (etaT 0 (firstTime N)) +
        2 * (d.W N : ℝ)⁻¹ ≤ (N : ℝ) ^ (ν / 8) := by
    calc
      _ ≤ 258 * (N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32) := hn
      _ = 258 * (N : ℝ) ^ (ν / 16) := by
        calc
          _ = 258 * ((N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32)) := by ring
          _ = _ := by rw [hPow]
      _ ≤ (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
        gcongr
        linarith
      _ = (N : ℝ) ^ (ν / 8) := hM.symm
  have hf2M : farTwo N (firstTime N) (sourceC4 (ν / 32) N) ≤
      (N : ℝ) ^ (ν / 8) := by
    calc
      _ ≤ 384 * (N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32) := hf2
      _ = 384 * (N : ℝ) ^ (ν / 16) := by
        calc
          _ = 384 * ((N : ℝ) ^ (ν / 32) * (N : ℝ) ^ (ν / 32)) := by ring
          _ = _ := by rw [hPow]
      _ ≤ (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
        gcongr
        linarith
      _ = (N : ℝ) ^ (ν / 8) := hM.symm
  have hf3M : farThree N (firstTime N) ≤ (N : ℝ) ^ (ν / 8) := by
    have hprod : (N : ℝ) ^ (ν / 16) ≤
        (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1)
        (by positivity : 0 ≤ (N : ℝ) ^ (ν / 16))]
    exact hf3.trans ((by linarith : (18432 : ℝ) ≤ (N : ℝ) ^ (ν / 16)).trans
      (hprod.trans hM.symm.le))
  have hfLM : farLeak N (firstTime N) ≤ (N : ℝ) ^ (ν / 8) := by
    have hprod : (N : ℝ) ^ (ν / 16) ≤
        (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1)
        (by positivity : 0 ≤ (N : ℝ) ^ (ν / 16))]
    exact hfL.trans ((by linarith : (256 : ℝ) ≤ (N : ℝ) ^ (ν / 16)).trans
      (hprod.trans hM.symm.le))
  have hconstM : 256 * Real.exp 3 ≤ (N : ℝ) ^ (ν / 8) := by
    have hprod : (N : ℝ) ^ (ν / 16) ≤
        (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1)
        (by positivity : 0 ≤ (N : ℝ) ^ (ν / 16))]
    exact hconst.trans (hprod.trans hM.symm.le)
  have h25 : (25 : ℝ) ≤ (N : ℝ) ^ (ν / 8) := by
    calc (25 : ℝ) ≤ (N : ℝ) ^ (ν / 16) :=
        (by norm_num : (25 : ℝ) ≤ 20000).trans hlarge'
      _ ≤ (N : ℝ) ^ (ν / 16) * (N : ℝ) ^ (ν / 16) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hp1)
          (by positivity : 0 ≤ (N : ℝ) ^ (ν / 16))]
      _ = (N : ℝ) ^ (ν / 8) := hM.symm
  exact ⟨hnearM, hf2M, hf3M, hfLM, hxi, hconstM, h25⟩

set_option maxHeartbeats 1000000 in
-- The default heartbeat limit is insufficient when five rows and the endpoint tail are unfolded.
/-- The endpoint tail cancels before any power is estimated. Each of the
five rows is then at most `M sqrt M` when all coefficients and `xiK` are
bounded by `M`. -/
theorem normalized_sharp_le (N : ℕ) (u ellSource S M : ℝ)
    (a : LoopArg (d.L N) 2)
    (hu0 : 0 ≤ u) (huv : u ≤ 1 / 2)
    (hW : 1 ≤ (d.W N : ℝ)) (hM : 1 ≤ M)
    (hn : APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹ ≤ M)
    (hf2 : farTwo N u S ≤ M) (hf3 : farThree N u ≤ M)
    (hfL : farLeak N u ≤ M)
    (hxi : Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im ≤ M)
    (hconst : 256 * Real.exp 3 ≤ M) :
    (16 * Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)))⁻¹ *
        sharpRootProfile N u ellSource S a ≤ 5 * M * √M := by
  let T : ℝ := Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1))
  let R : ℝ := ((1 - u) / (1 - (1 / 2 : ℝ))) ^ (2 : ℕ)
  let Xi : ℝ := Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im
  let χ : ℝ := if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
      6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then 1 else 0
  let An : ℝ := APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource
      (etaT 0 u) + 2 * (d.W N : ℝ)⁻¹
  let F2 : ℝ := farTwo N u S
  let F3 : ℝ := farThree N u
  let FL : ℝ := farLeak N u
  have hT : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos (by linarith : 0 < (d.W N : ℝ)) _
  have hProf : sharpRootProfile N u ellSource S a =
      T * R * (√An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi) := by
    dsimp [sharpRootProfile, nearKernel, leakKernel, endpointKernel]
    change √An * (R * Xi * T * χ) +
        √An * (256 * Real.exp 3 * R * (d.W N : ℝ) ^ (-(60 : ℝ)) * T) +
        √F2 * (R * Xi * T) + √F3 * (R * Xi * T) +
        √FL * (R * Xi * T) =
      T * R * (√An * Xi * χ +
        √An * (256 * Real.exp 3 * (d.W N : ℝ) ^ (-(60 : ℝ))) +
        √F2 * Xi + √F3 * Xi + √FL * Xi)
    ring
  have hEq : (16 * T)⁻¹ * sharpRootProfile N u ellSource S a =
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
      _ ≤ √M * M :=
        mul_le_mul hn' hLeakC (by positivity) (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h3 : √F2 * Xi ≤ M * √M := by
    calc _ ≤ √M * M :=
          mul_le_mul hf2' hXiLe hXi0 (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h4 : √F3 * Xi ≤ M * √M := by
    calc _ ≤ √M * M :=
          mul_le_mul hf3' hXiLe hXi0 (Real.sqrt_nonneg M)
      _ = M * √M := by ring
  have h5 : √FL * Xi ≤ M * √M := by
    calc _ ≤ √M * M :=
          mul_le_mul hfL' hXiLe hXi0 (Real.sqrt_nonneg M)
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
-- The default heartbeat limit is insufficient for combining the eventual rowwise power bounds.
/-- Uniform endpoint-label absorption for the exact five-row profile.
The source loss is selected before choosing the T348 sample. -/
theorem eventually_normalized_sharp_le {ν : ℝ} (hν : 0 < ν) :
    let ζ := ν / 32
    ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
      (16 * Step2.tT B 0 N 60 (1 / 2)
        (zdist (d.L N) (a 0 - a 1)))⁻¹ *
          sharpRootProfile N (firstTime N) (sourceEll ζ N)
            (sourceC4 ζ N) a ≤ (N : ℝ) ^ (ν / 4) := by
  dsimp only
  have hrows := eventually_rows_le_power hν
  have htime := APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime
    (τ' := 1) (by norm_num)
  filter_upwards [hrows, htime,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales] with N hrows htime hsc a
  dsimp only at hrows
  obtain ⟨hn, hf2, hf3, hfL, hxi, hconst, h25⟩ := hrows
  obtain ⟨hW, _, _, hN, _, _, _, _, _⟩ := hsc
  have hW1 : 1 ≤ (d.W N : ℝ) := (Real.one_le_exp (by norm_num)).trans hW
  have hu0 : 0 ≤ firstTime N := by rw [← htime.1]; exact htime.2.le
  have hmem := APrimeFirstCellNearSources.sourceTime_mem
    (τ' := 1) (by norm_num) N
  have huv : firstTime N ≤ 1 / 2 := by
    rw [← htime.1]
    exact hmem.2.trans (gridT_le (1 / 2 : ℝ) 1)
  let M : ℝ := (N : ℝ) ^ (ν / 8)
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; linarith
  have hbase := normalized_sharp_le N (firstTime N) (sourceEll (ν / 32) N)
    (sourceC4 (ν / 32) N) M a hu0 huv hW1 hM1
    hn hf2 hf3 hfL hxi hconst
  have hsqrt5 : (5 : ℝ) ≤ √M := by
    nlinarith [Real.sq_sqrt hM0, Real.sqrt_nonneg M]
  have hfive : 5 * √M ≤ M := by
    nlinarith [Real.sq_sqrt hM0,
      mul_nonneg (sub_nonneg.mpr hsqrt5) (Real.sqrt_nonneg M)]
  have hproduct : 5 * M * √M ≤ M ^ (2 : ℕ) := by
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hfive)]
  have hpow : M ^ (2 : ℕ) = (N : ℝ) ^ (ν / 4) := by
    dsimp [M]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  exact hbase.trans (hproduct.trans_eq hpow)

theorem normalized_sharp_nonneg (N : ℕ) (u ellSource S : ℝ)
    (a : LoopArg (d.L N) 2) (hW : 0 ≤ (d.W N : ℝ)) :
    0 ≤ (16 * Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)))⁻¹ *
        sharpRootProfile N u ellSource S a := by
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
  unfold sharpRootProfile nearKernel leakKernel endpointKernel
  positivity

set_option maxHeartbeats 1000000 in
-- The default heartbeat limit is insufficient for the nested witness and its large conjunction.
/-- For each `ν>0`, the same positive-time Gaussian sample carries the T348
source, T385 block cap and active smooth weight, and the actual uncut evolved
quadratic variation is at most `N^ν` for every endpoint label. -/
theorem exists_positive_firstTime_qvAt_le_rpow :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ν : ℝ, 0 < ν → ∀ δ : ℝ, 0 < δ →
      let ζ := ν / 32
      ∀ᶠ N : ℕ in atTop, ∃ ω : Gauss.Ω d,
        ‖Xmat d N ω‖ ≤ (N : ℝ) ∧
        0 < firstTime N ∧
        firstTime N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) ∧
        0 < sourceEll ζ N ∧ 0 < sourceC4 ζ N ∧
        (∀ p : ℕ, APrimeSmoothWeightActual.weight d 0 60 δ
          (firstCellS τ') (firstCellT τ')
          (fun M => (max 1 M : ℝ) ^ (248 : ℕ)) 2 p N 2 N ω = 1) ∧
        APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (firstTime N) ω
          (sourceEll ζ N) (sourceC4 ζ N) ∧
        APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
          (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤ 2 ∧
        ∀ a : LoopArg (d.L N) 2,
          0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2) ∧
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2)
            (firstTime N) ω ≤ (N : ℝ) ^ ν := by
  obtain ⟨τ', hτ', hw⟩ :=
    APrimeFirstCellQVSharpJ.exists_positive_firstTime_sharp_qv
  refine ⟨τ', hτ', ?_⟩
  intro ν hν δ hδ
  dsimp only
  have hζ : 0 < ν / 32 := by positivity
  filter_upwards [hw (ν / 32) hζ δ hδ,
    eventually_normalized_sharp_le hν,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    eventually_ge_atTop 2] with N hwN hnorm hsc hN2
  obtain ⟨ω, hX, hpos, hmem, hell, _hellLt, hS, hweight,
    hsource, hJ, hqv⟩ := hwN
  obtain ⟨hW, _, _, hN, _, _, _, _, _⟩ := hsc
  have hW0 : 0 ≤ (d.W N : ℝ) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans ((Real.one_le_exp (by norm_num)).trans hW)
  have hNpos : 0 < (N : ℝ) := by linarith
  refine ⟨ω, hX, hpos, hmem, hell, hS, hweight, hsource, hJ, ?_⟩
  intro a
  obtain ⟨hscale, _hscaleEq, hraw⟩ := hqv a
  refine ⟨hscale, ?_⟩
  have hnorm0 := normalized_sharp_nonneg N (firstTime N)
    (sourceEll (ν / 32) N) (sourceC4 (ν / 32) N) a hW0
  have hsq := pow_le_pow_left₀ hnorm0 (hnorm a) 2
  have hpow : ((N : ℝ) ^ (ν / 4)) ^ (2 : ℕ) ≤ (N : ℝ) ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ (N : ℝ))
    linarith
  exact hraw.trans (hsq.trans hpow)

#print axioms cNear2_le_cNear_pow_four
#print axioms cFar2_le_two_cNear2
#print axioms eventually_cNear2_le
#print axioms eventually_cFar2_le
#print axioms source_near_ratio_fifth
#print axioms source_far_square
#print axioms source_A_sqrt_le
#print axioms row_coefficients_le
#print axioms eventually_rows_le_power
#print axioms normalized_sharp_le
#print axioms eventually_normalized_sharp_le
#print axioms exists_positive_firstTime_qvAt_le_rpow

end RBM.APrimeFirstCellQVSmall
