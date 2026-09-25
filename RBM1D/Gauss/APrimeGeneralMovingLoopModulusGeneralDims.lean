/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingWindowFloor
import RBM1D.Gauss.APrimeGeneralMovingPrefixSupport

/-!
# T1383: arbitrary-Dims actual normalized-loop modulus and running cap

The bare paper condition (2.72) supplies the endpoint floor needed to
polynomially control the coefficients in the actual normalized-loop modulus.
The bound holds for every dimension schedule and admissible moving window.
-/

namespace RBM.APrimeGeneralMovingLoopModulusGeneralDims

open Filter Set Real Gauss Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A fixed bulk-energy constant which dominates all coefficients left after
the endpoint singularity has been bounded by powers of `N`. -/
noncomputable def loopModulusConst (E : ℝ) : ℝ :=
  let m := (mE E).im⁻¹
  let A := m ^ 2 + 1
  let T := 2 * m ^ 2 + 2 * m ^ 3 + m ^ 2 / 2
  15 / 96 * A + A * T + 4 * m ^ 4 + 1 + 4 * A + 4

theorem loopModulusConst_pos {E : ℝ} (hE : |E| < 2) :
    0 < loopModulusConst E := by
  have hm : 0 < (mE E).im⁻¹ := inv_pos.mpr (mE_im_pos hE)
  simp only [loopModulusConst]
  positivity

/-- The bare paper condition (2.72) already gives a polynomial endpoint
floor: it forces the terminal scale to be at least one, while the dimension
bound gives `scale ≤ N * (1-t_N)`. -/
theorem eventually_endpoint_floor (d : Dims) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg : Cond272 (band d) E s t) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ ≤ 1 - t N ∧ 1 - t N ≤ 1 - s N := by
  filter_upwards [hreg, d.dim, eventually_ge_atTop 1]
    with N hcond hdim hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith [hst N, ht1 N]
  have hratio0 : 0 ≤ (1 - t N) / (1 - s N) :=
    div_nonneg h1t.le h1s.le
  have hratio1 : (1 - t N) / (1 - s N) ≤ 1 := by
    rw [div_le_iff₀ h1s]
    linarith [hst N]
  have hratioPow : ((1 - t N) / (1 - s N)) ^ 30 ≤ 1 := by
    exact (pow_le_one₀ hratio0 hratio1)
  have hscaleInv : ((band d).scale E N (t N))⁻¹ ≤ 1 :=
    hcond.trans hratioPow
  have hscalePos : 0 < (band d).scale E N (t N) :=
    (band d).scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have hscale1 : 1 ≤ (band d).scale E N (t N) :=
    (inv_le_one₀ hscalePos).1 hscaleInv
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have hηle : etaT E (t N) ≤ 1 - t N := by
    show (1 - t N) * (mE E).im ≤ 1 - t N
    have him : (mE E).im ≤ 1 := le_trans (le_abs_self _)
      (by
        have hnorm := Complex.abs_im_le_norm (mE E)
        rwa [norm_mE hE.le] at hnorm)
    nlinarith
  have hscaleUpper : (band d).scale E N (t N) ≤
      (N : ℝ) * (1 - t N) := by
    rw [Band.scale]
    have hℓL : (band d).ell N (t N) ≤ (d.L N : ℝ) := min_le_right _ _
    have hW : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
    have hη : 0 ≤ etaT E (t N) := (etaT_pos_of_lt_one' hE (ht1 N)).le
    calc
      (d.W N : ℝ) * (band d).ell N (t N) * etaT E (t N)
          ≤ (d.W N : ℝ) * (d.L N : ℝ) * etaT E (t N) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hℓL hW) hη
      _ ≤ (N : ℝ) * etaT E (t N) :=
        mul_le_mul_of_nonneg_right hWL hη
      _ ≤ (N : ℝ) * (1 - t N) :=
        mul_le_mul_of_nonneg_left hηle (Nat.cast_nonneg _)
  have hfloor : (N : ℝ)⁻¹ ≤ 1 - t N := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hN0).2
    nlinarith [hscale1, hscaleUpper]
  exact ⟨hfloor, by linarith [hst N]⟩

set_option maxHeartbeats 1000000 in
-- The expanded coefficient has nested real powers whose monotonicity proof
-- needs more than the project default heartbeat limit during elaboration.
/-- Deterministic coefficient estimate at one endpoint.  The extra final
power of `N` is deliberately left out here; it absorbs the fixed energy
constant in the eventual statement below. -/
theorem jTotNormEv_le_const_mul (d : Dims) {E D t₀ : ℝ} {N : ℕ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hN1 : (1 : ℝ) ≤ (N : ℝ))
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ))
    (hrN : (1 - t₀)⁻¹ ≤ (N : ℝ)) :
    APrimeSlotFields.jTotNormEv d N E D t₀ ≤
      loopModulusConst E * (N : ℝ) ^ (2 * D + 6) := by
  let n : ℝ := N
  let m : ℝ := (mE E).im⁻¹
  let r : ℝ := (1 - t₀)⁻¹
  let q : ℝ := (etaT E t₀)⁻¹
  let Cp : ℝ := (2 * √(1 - t₀))⁻¹
  let A : ℝ := m ^ 2 + 1
  let T : ℝ := 2 * m ^ 2 + 2 * m ^ 3 + m ^ 2 / 2
  let P : ℝ := n ^ (2 * D + 6)
  have hn1 : 1 ≤ n := hN1
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hm0 : 0 < m := inv_pos.mpr (mE_im_pos hE)
  have hδ0 : 0 < 1 - t₀ := by linarith
  have hδ1 : 1 - t₀ ≤ 1 := by linarith
  have hr0 : 0 < r := inv_pos.mpr hδ0
  have hr1 : 1 ≤ r := by
    rw [show r = (1 - t₀)⁻¹ by rfl, one_le_inv₀ hδ0]
    exact hδ1
  have hrn : r ≤ n := hrN
  have hq : q = r * m := by
    simp only [q, r, m, etaT, mul_inv]
  have hq0 : 0 < q := by rw [hq]; positivity
  have hCp : Cp ≤ r := by
    have hs0 : 0 < √(1 - t₀) := Real.sqrt_pos.2 hδ0
    have hδsqrt : 1 - t₀ ≤ √(1 - t₀) := by
      apply (Real.le_sqrt hδ0.le hδ0.le).2
      nlinarith
    have hinv : (√(1 - t₀))⁻¹ ≤ r := by
      exact inv_anti₀ hδ0 hδsqrt
    rw [show Cp = (2 : ℝ)⁻¹ * (√(1 - t₀))⁻¹ by simp [Cp]; ring]
    calc
      (2 : ℝ)⁻¹ * (√(1 - t₀))⁻¹ ≤ 1 * (√(1 - t₀))⁻¹ := by gcongr <;> norm_num
      _ ≤ r := by simpa using hinv
  have hCpN : Cp ≤ n := hCp.trans hrn
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hL1 : (1 : ℝ) ≤ (d.L N : ℝ) := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hW0 : (0 : ℝ) < (d.W N : ℝ) := lt_of_lt_of_le zero_lt_one hW1
  have hL0 : (0 : ℝ) < (d.L N : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hWinv : ((d.W N : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hW1
  have hWN : (d.W N : ℝ) ≤ n := by nlinarith
  have hLN : (d.L N : ℝ) ≤ n := by nlinarith
  have hD0 : 0 ≤ D := by linarith
  have hWD : (d.W N : ℝ) ^ D ≤ n ^ D :=
    Real.rpow_le_rpow hW0.le hWN hD0
  have hW2D : (d.W N : ℝ) ^ (2 * D) ≤ n ^ (2 * D) :=
    Real.rpow_le_rpow hW0.le hWN (by linarith)
  have hP0 : 0 < P := Real.rpow_pos_of_pos hn0 _
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hrpow (k : ℕ) : r ^ k ≤ n ^ k := pow_le_pow_left₀ hr0.le hrn k
  have hq2 : q ^ 2 ≤ m ^ 2 * n ^ 2 := by
    rw [hq]
    nlinarith [hrpow 2]
  have hq3 : q ^ 3 ≤ m ^ 3 * n ^ 3 := by
    calc
      q ^ 3 = m ^ 3 * r ^ 3 := by rw [hq]; ring
      _ ≤ m ^ 3 * n ^ 3 :=
        mul_le_mul_of_nonneg_left (hrpow 3) (pow_nonneg hm0.le 3)
  have hq4 : q ^ 4 ≤ m ^ 4 * n ^ 4 := by
    calc
      q ^ 4 = m ^ 4 * r ^ 4 := by rw [hq]; ring
      _ ≤ m ^ 4 * n ^ 4 :=
        mul_le_mul_of_nonneg_left (hrpow 4) (pow_nonneg hm0.le 4)
  have hcrude : crudeLk d N E t₀ ≤ A * n ^ 2 := by
    rw [crudeLk]
    have hr2 : r ≤ n ^ 2 := by
      calc r ≤ n := hrn
        _ ≤ n ^ 2 := by nlinarith
    have hsum : q * q + r ≤ A * n ^ 2 := by
      have hq2' : q * q ≤ m ^ 2 * n ^ 2 := by simpa [pow_two] using hq2
      dsimp [A]
      nlinarith
    have hsum0 : 0 ≤ q * q + r := by nlinarith [sq_nonneg q]
    exact (mul_le_mul hWinv hsum hsum0 (by norm_num)).trans_eq (one_mul _)
  have htail : tailLip d N E t₀ ≤ T * n ^ 4 := by
    rw [tailLip]
    have hn2n4 : n ^ 2 ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by omega)
    have hn3n4 : n ^ 3 ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by omega)
    have h1 : 2 * Cp * q ^ 2 ≤ 2 * m ^ 2 * n ^ 4 := by
      calc
        2 * Cp * q ^ 2 ≤ 2 * n * (m ^ 2 * n ^ 2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hCpN (by norm_num)) hq2
            (sq_nonneg q) (by positivity)
        _ ≤ 2 * m ^ 2 * n ^ 4 := by nlinarith
    have h2 : 2 * q ^ 3 ≤ 2 * m ^ 3 * n ^ 4 := by
      have hc : (0 : ℝ) ≤ 2 * m ^ 3 :=
        mul_nonneg (by norm_num) (pow_nonneg hm0.le 3)
      calc
        2 * q ^ 3 ≤ 2 * (m ^ 3 * n ^ 3) :=
          mul_le_mul_of_nonneg_left hq3 (by norm_num)
        _ = (2 * m ^ 3) * n ^ 3 := by ring
        _ ≤ (2 * m ^ 3) * n ^ 4 := mul_le_mul_of_nonneg_left hn3n4 hc
    have h3 : q ^ 2 * ((d.L N : ℝ) / 2) * Cp ≤ m ^ 2 / 2 * n ^ 4 := by
      calc
        q ^ 2 * ((d.L N : ℝ) / 2) * Cp
            ≤ (m ^ 2 * n ^ 2) * (n / 2) * n := by
              gcongr
        _ = m ^ 2 / 2 * n ^ 4 := by ring
    dsimp [T]
    calc
      2 * Cp * q ^ 2 + 2 * q ^ 3 + q ^ 2 * ((d.L N : ℝ) / 2) * Cp
          ≤ 2 * m ^ 2 * n ^ 4 + 2 * m ^ 3 * n ^ 4 + m ^ 2 / 2 * n ^ 4 :=
        add_le_add (add_le_add h1 h2) h3
      _ = (2 * m ^ 2 + 2 * m ^ 3 + m ^ 2 / 2) * n ^ 4 := by ring
  have hpowD4 : n ^ (D + 4) ≤ P := by
    dsimp [P]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpow2D6 : n ^ (2 * D + 6) = P := rfl
  have hpowD6 : n ^ (D + 6) ≤ P := by
    dsimp [P]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpowD3 : n ^ (D + 3) ≤ P := by
    dsimp [P]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpowD2 : n ^ (D + 2) ≤ P := by
    dsimp [P]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hnP : n ≤ P := by
    calc n = n ^ (1 : ℝ) := (Real.rpow_one n).symm
      _ ≤ P := by
        dsimp [P]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpowD4eq : n ^ (D + 4) = n ^ D * n ^ 4 := by
    rw [show D + 4 = D + (4 : ℝ) by ring, Real.rpow_add hn0]
    norm_num [Real.rpow_natCast]
  have hpowD6eq : n ^ (D + 6) = n ^ D * n ^ 6 := by
    rw [show D + 6 = D + (6 : ℝ) by ring, Real.rpow_add hn0]
    norm_num [Real.rpow_natCast]
  have hpowD3eq : n ^ (D + 3) = n ^ D * n ^ 3 := by
    rw [show D + 3 = D + (3 : ℝ) by ring, Real.rpow_add hn0]
    norm_num [Real.rpow_natCast]
  have hpowD2eq : n ^ (D + 2) = n ^ D * n ^ 2 := by
    rw [show D + 2 = D + (2 : ℝ) by ring, Real.rpow_add hn0]
    norm_num [Real.rpow_natCast]
  have hb1 :
      15 / 8 * ((d.L N : ℝ) / 12 * Cp) *
          (crudeLk d N E t₀ * (d.W N : ℝ) ^ D)
        ≤ 15 / 96 * A * P := by
    have hcr0 := crudeLk_nonneg d N hE ht₀
    have hLCp : (d.L N : ℝ) / 12 * Cp ≤ n / 12 * n := by
      exact mul_le_mul (div_le_div_of_nonneg_right hLN (by norm_num)) hCpN
        (by positivity) (by positivity)
    have hcrWD : crudeLk d N E t₀ * (d.W N : ℝ) ^ D
        ≤ (A * n ^ 2) * n ^ D := by
      exact mul_le_mul hcrude hWD (Real.rpow_nonneg hW0.le D)
        (mul_nonneg hA0.le (sq_nonneg n))
    calc
      15 / 8 * ((d.L N : ℝ) / 12 * Cp) *
          (crudeLk d N E t₀ * (d.W N : ℝ) ^ D)
        ≤ 15 / 8 * (n / 12 * n) * ((A * n ^ 2) * n ^ D) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hLCp (by norm_num)) hcrWD
            (mul_nonneg hcr0 (Real.rpow_nonneg hW0.le D)) (by positivity)
      _ = 15 / 96 * A * n ^ (D + 4) := by
        rw [hpowD4eq]
        ring
      _ ≤ 15 / 96 * A * P := mul_le_mul_of_nonneg_left hpowD4 (by positivity)
  have hb2 :
      crudeLk d N E t₀ *
          (tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D))
        ≤ A * T * P := by
    calc
      crudeLk d N E t₀ *
          (tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D))
        ≤ (A * n ^ 2) * ((T * n ^ 4) * n ^ (2 * D)) := by
          have hc0 := crudeLk_nonneg d N hE ht₀
          have ht0 := tailLip_nonneg d N hE ht₀
          gcongr
      _ = A * T * n ^ (2 * D + 6) := by
        rw [show n ^ (2 * D + 6) = n ^ (2 * D) * n ^ (6 : ℝ) by rw [Real.rpow_add hn0]]
        norm_num [Real.rpow_natCast]
        ring
      _ = A * T * P := by rw [hpow2D6]
  have hlk1 :
      (d.L N : ℝ) * (d.W N : ℝ) * 2 * q ^ 2 * ((n + 1) * (q * q)) *
          (d.W N : ℝ) ^ D ≤ 4 * m ^ 4 * P := by
    have hnadd : n + 1 ≤ 2 * n := by linarith
    have hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ n := by simpa [mul_comm] using hWL
    have hq2' : q * q ≤ m ^ 2 * n ^ 2 := by simpa [pow_two] using hq2
    have hleft : (d.L N : ℝ) * (d.W N : ℝ) * 2 * q ^ 2
        ≤ n * 2 * (m ^ 2 * n ^ 2) := by
      have h0 : 0 ≤ (d.L N : ℝ) * (d.W N : ℝ) := by positivity
      have hn20 : 0 ≤ n * 2 := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_right hLW (by norm_num)) hq2
        (sq_nonneg q) hn20
    have hright : (n + 1) * (q * q) ≤ (2 * n) * (m ^ 2 * n ^ 2) := by
      exact mul_le_mul hnadd hq2' (by nlinarith [sq_nonneg q]) (by positivity)
    have hprod :
        ((d.L N : ℝ) * (d.W N : ℝ) * 2 * q ^ 2) * ((n + 1) * (q * q)) *
            (d.W N : ℝ) ^ D
          ≤ (n * 2 * (m ^ 2 * n ^ 2)) * ((2 * n) * (m ^ 2 * n ^ 2)) * n ^ D := by
      have hrightprod0 : 0 ≤
          (n * 2 * (m ^ 2 * n ^ 2)) * ((2 * n) * (m ^ 2 * n ^ 2)) := by
        positivity
      have hleftR0 : 0 ≤ (n + 1) * (q * q) := by positivity
      have hrightL0 : 0 ≤ n * 2 * (m ^ 2 * n ^ 2) := by positivity
      have hboth := mul_le_mul hleft hright hleftR0 hrightL0
      exact mul_le_mul hboth hWD
        (Real.rpow_nonneg hW0.le D) hrightprod0
    calc
      (d.L N : ℝ) * (d.W N : ℝ) * 2 * q ^ 2 * ((n + 1) * (q * q)) *
          (d.W N : ℝ) ^ D
        ≤ n * 2 * (m ^ 2 * n ^ 2) * ((2 * n) * (m ^ 2 * n ^ 2)) * n ^ D := by
          simpa only [mul_assoc] using hprod
      _ = 4 * m ^ 4 * n ^ (D + 6) := by
        rw [hpowD6eq]
        ring
      _ ≤ 4 * m ^ 4 * P := mul_le_mul_of_nonneg_left hpowD6 (by positivity)
  have hlk2 :
      (d.W N : ℝ)⁻¹ * (r * r) * (d.W N : ℝ) ^ D ≤ P := by
    calc
      (d.W N : ℝ)⁻¹ * (r * r) * (d.W N : ℝ) ^ D
        ≤ 1 * (n ^ 2) * n ^ D := by
          have hrr : r * r ≤ n ^ 2 := by simpa [pow_two] using hrpow 2
          exact mul_le_mul (mul_le_mul hWinv hrr (by positivity) (by norm_num)) hWD
            (Real.rpow_nonneg hW0.le D) (by positivity)
      _ = n ^ (D + 2) := by
        rw [hpowD2eq]
        ring
      _ ≤ P := hpowD2
  have hb3 : lkLipEv d N E t₀ * (d.W N : ℝ) ^ D
      ≤ (4 * m ^ 4 + 1) * P := by
    rw [lkLipEv]
    change ((d.L N : ℝ) * (d.W N : ℝ) * 2 * q ^ 2 * ((n + 1) * (q * q)) +
        (d.W N : ℝ)⁻¹ * (r * r)) * (d.W N : ℝ) ^ D ≤ _
    rw [add_mul]
    exact (add_le_add hlk1 hlk2).trans_eq (by ring)
  have hnorm :
      4 * r * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)
        ≤ (4 * A + 4) * P := by
    have hmain : r * ((d.W N : ℝ) ^ D * crudeLk d N E t₀)
        ≤ A * P := by
      have hinside : (d.W N : ℝ) ^ D * crudeLk d N E t₀
          ≤ n ^ D * (A * n ^ 2) := by
        exact mul_le_mul hWD hcrude (crudeLk_nonneg d N hE ht₀)
          (Real.rpow_nonneg hn0.le D)
      have hinside0 : 0 ≤ (d.W N : ℝ) ^ D * crudeLk d N E t₀ :=
        mul_nonneg (Real.rpow_nonneg hW0.le D) (crudeLk_nonneg d N hE ht₀)
      calc
        r * ((d.W N : ℝ) ^ D * crudeLk d N E t₀)
          ≤ n * (n ^ D * (A * n ^ 2)) :=
            mul_le_mul hrn hinside hinside0 hn0.le
        _ = A * n ^ (D + 3) := by
          rw [hpowD3eq]
          ring
        _ ≤ A * P := mul_le_mul_of_nonneg_left hpowD3 hA0.le
    nlinarith [hnP]
  rw [APrimeSlotFields.jTotNormEv, jSfarSmLip]
  change
    15 / 8 * ((d.L N : ℝ) / 12 * Cp) *
          (crudeLk d N E t₀ * (d.W N : ℝ) ^ D) +
        crudeLk d N E t₀ *
          (tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D)) +
      lkLipEv d N E t₀ * (d.W N : ℝ) ^ D +
      4 * r * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)
      ≤ loopModulusConst E * P
  dsimp [loopModulusConst, A, T, m]
  dsimp [A, T, m] at hb1 hb2 hb3 hnorm
  nlinarith [hb1, hb2, hb3, hnorm, hP0.le]

/-- The actual spectral-norm event used by the modulus. -/
def normEvent (d : Dims) (N : ℕ) : Set (Ω d) :=
  {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- The full normalized loop is uniformly half-Hölder on every admissible
moving window, on the fixed spectral-norm event. -/
theorem eventually_jSnorm_modulus (d : Dims) {E D : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg : Cond272 (band d) E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ normEvent d N,
      ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
      |Step2Moment.jSnorm (sample d) E D s N v ω -
          Step2Moment.jSnorm (sample d) E D s N w ω| ≤
        (N : ℝ) ^ (2 * D + 7) * |v - w| ^ ((1 : ℝ) / 2) := by
  have hK0 := loopModulusConst_pos hE
  have hbig : ∀ᶠ N : ℕ in atTop, max 1 (loopModulusConst E) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_endpoint_floor d hE hs0 hst ht1 hreg,
    d.dim, eventually_one_le_log_W d, hbig] with N hfloor hdim hlogW hbigN
  intro ω hω v hv w hw
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := (le_max_left _ _).trans hbigN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hKN : loopModulusConst E ≤ (N : ℝ) := (le_max_right _ _).trans hbigN
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have ht0 : 0 ≤ t N := (hs0 N).trans (hst N)
  have hδ0 : 0 < 1 - t N := by linarith [ht1 N]
  have hrN : (1 - t N)⁻¹ ≤ (N : ℝ) :=
    (inv_le_comm₀ hδ0 hN0).2 hfloor.1
  have hcoef := jTotNormEv_le_const_mul d hE (by linarith : 1 ≤ D)
    ht0 (ht1 N) hN1 hWL hrN
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hw0 : 0 ≤ w := (hs0 N).trans hw.1
  have hv1 : v ≤ 1 := hv.2.trans (ht1 N).le
  have hw1 : w ≤ 1 := hw.2.trans (ht1 N).le
  have hlen : |v - w| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hpoint := APrimeSlotFields.abs_jSnorm_sub_le_event d N ω
    (D := D) (t₀ := t N) (s := s) hE (hs0 N) hv.1 hw.1 hv.2 hw.2
    (ht1 N) ht0 hlen hlogW hω
  have hp0 : 0 ≤ |v - w| ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hpow0 : 0 ≤ (N : ℝ) ^ (2 * D + 6) := Real.rpow_nonneg hN0.le _
  have hpow : (N : ℝ) ^ (2 * D + 7) =
      (N : ℝ) * (N : ℝ) ^ (2 * D + 6) := by
    rw [show 2 * D + 7 = 1 + (2 * D + 6) by ring,
      Real.rpow_add hN0, Real.rpow_one]
  calc
    |Step2Moment.jSnorm (sample d) E D s N v ω -
        Step2Moment.jSnorm (sample d) E D s N w ω|
      ≤ |v - w| ^ ((1 : ℝ) / 2) *
          APrimeSlotFields.jTotNormEv d N E D (t N) := hpoint
    _ ≤ |v - w| ^ ((1 : ℝ) / 2) *
          (loopModulusConst E * (N : ℝ) ^ (2 * D + 6)) :=
      mul_le_mul_of_nonneg_left hcoef hp0
    _ ≤ |v - w| ^ ((1 : ℝ) / 2) *
          ((N : ℝ) * (N : ℝ) ^ (2 * D + 6)) := by
      gcongr
    _ = (N : ℝ) ^ (2 * D + 7) * |v - w| ^ ((1 : ℝ) / 2) := by
      rw [hpow]
      ring

theorem measurableSet_normEvent (d : Dims) (N : ℕ) :
    MeasurableSet (normEvent d N) := by
  simpa only [normEvent] using Gauss.measurableSet_normX_le d N

theorem zero_mem_normEvent (d : Dims) (N : ℕ) :
    (0 : Ω d) ∈ normEvent d N := by
  simpa only [normEvent] using APrimeSlotFields.zero_mem_normX_le d N

/-- The actual normalized-loop state, kept explicit in the positive-weight
prefix theorem. -/
noncomputable abbrev actualJ (d : Dims) (E D : ℝ) (s : ℕ → ℝ) :
    ℕ → ℝ → Ω d → ℝ :=
  fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω

/-- Exact target-mesh arithmetic. Since the mesh is `N^(4D+18)` for positive
`N`, the modulus cost is exactly `N⁻²`. -/
theorem target_mesh_fine_eq_inv_sq (D : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (2 * D + 7) *
      (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) =
        (N : ℝ) ^ (-(2 : ℝ)) := by
  simpa only [APrimeGeneralMovingMesh.targetMesh] using
    (APrimeGeneralMovingMesh.mesh_fine_eq_inv_sq (K := 2 * D + 7) (N := N) hN)

/-- On the same actual Gaussian norm event as the modulus, positivity of the
widened running-prefix weight controls the normalized loop throughout that
prefix.  The loss `δ` and moment order `p` are fixed before the eventual `N`.
-/
theorem eventually_running_prefix_cap (d : Dims) {E D δ : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg : Cond272 (band d) E s t) (hδ : 0 < δ)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k → k ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ ω ∈ normEvent d N,
        0 < APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t
            (APrimeGeneralMovingMesh.targetMesh D)) 1
          (actualJ d E D s) s t
          (APrimeGeneralMovingMesh.targetMesh D) δ p N k ω →
        ∀ u ∈ Icc (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          actualJ d E D s N u ω ≤
            (4 * Real.exp 1 + 2) * (N : ℝ) ^ (2 * δ) := by
  have hmodAll := eventually_jSnorm_modulus d hE hD hs0 hst ht1 hreg
  have hfineAll := APrimeGeneralMovingMesh.eventually_target_mesh_fine D
  filter_upwards [hmodAll, hfineAll, eventually_ge_atTop 1]
    with N hmod hfine hN
  intro k hk hkTop ω hω hwide u hu
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J := actualJ d E D s
  let r := APrimeWeight.canonicalR s t mesh
  let θ := 2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N
  have hactive : k ≤ cutNetTop s t mesh N ∧ 1 ≤ N := ⟨hkTop, hN⟩
  have hpne : 2 * p ≠ 0 := by omega
  have hprefix : APrimeWeight.prefixSoftW (r N) J s mesh N k θ ω ≠ 0 := by
    intro hz
    have hwide' := hwide
    rw [APrimeWeight.widenedW, if_pos hactive] at hwide'
    change 0 < (APrimeWeight.prefixSoftW (r N) J s mesh N k θ ω) ^ (2 * p) at hwide'
    rw [hz, zero_pow hpne] at hwide'
    exact (lt_irrefl 0) hwide'
  have hθ : 0 < θ := by
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (APrimePrior.priorLevel_pos hN (by simp))
  have hr : 1 ≤ r N := by simp [r, APrimeWeight.canonicalR]
  have hmod : ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
      |J N v ω - J N w ω| ≤ (N : ℝ) ^ (2 * D + 7) *
        |v - w| ^ ((1 : ℝ) / 2) := by
    intro v hv w hw
    exact hmod ω hω v hv w hw
  have hmeshPos : 0 < mesh N := by
    exact APrimeGeneralMovingMesh.targetMesh_pos D N
  have hNcast : 1 ≤ N := by exact_mod_cast hN
  have hmeshEq := target_mesh_fine_eq_inv_sq D hNcast
  have hmeshFine : (N : ℝ) ^ (2 * D + 7) *
      (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ 1 := by
    have hmeshEq' : (N : ℝ) ^ (2 * D + 7) *
        (1 / mesh N) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ (-(2 : ℝ)) := by
      simpa only [mesh] using hmeshEq
    exact hmeshEq'.le.trans
      (APrimeGeneralMovingMesh.inv_sq_le_one hNcast)
  have hbase := APrimeWeight.le_of_prefixSoftW_ne_zero_of_modulus
    (r := r N) hr (J := J) (s := s) (t := t) (mesh := mesh)
    (N := N) (k := k) (Kmod := 2 * D + 7)
    (γ := (1 : ℝ) / 2) (θ := θ) (Θ := 1)
    (by norm_num) hθ (hst N) hmeshPos hk hkTop hprefix hmod hmeshFine u hu
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ (2 * δ) :=
    Real.one_le_rpow hNreal (by linarith)
  calc
    J N u ω ≤ 2 * θ + 1 := hbase
    _ = 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) + 1 := by
      simp [θ, APrimePrior.priorLevel]
      ring
    _ ≤ (4 * Real.exp 1 + 2) * (N : ℝ) ^ (2 * δ) := by
      have hexp : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith

/-- A positive-length first-cell witness lies in the actual norm event and
has active `k=1` with positive widened weight.  Its running cap is supplied by
the general same-event prefix theorem above. -/
theorem positive_length_same_norm_running_cap_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      let s := Gauss.firstCellS τ'
      let t := Gauss.firstCellT τ'
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272 (band Dims.exampleGrow) 0 s t ∧
      ∀ᶠ N : ℕ in atTop,
        s N < t N ∧
        ∃ ω ∈ normEvent Dims.exampleGrow N,
          1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N ∧
          0 < APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t
              (APrimeGeneralMovingMesh.targetMesh 60)) 1
            (actualJ Dims.exampleGrow 0 60 s) s t
            (APrimeGeneralMovingMesh.targetMesh 60) 1 1 N 1 ω ∧
          ∀ u ∈ Icc (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh 60) N 1),
            actualJ Dims.exampleGrow 0 60 s N u ω ≤
              (4 * Real.exp 1 + 2) * (N : ℝ) ^ 2 := by
  obtain ⟨τ', hτ', c, hc, hs0, hst, ht1, hreg, hsupport⟩ :=
    APrimeGeneralMovingPrefixSupport.positive_length_same_good_support_witness
  let s := Gauss.firstCellS τ'
  let t := Gauss.firstCellT τ'
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  have hregPaper : Cond272 (band Dims.exampleGrow) 0 s t :=
    hreg.toCond272
  have hcap := eventually_running_prefix_cap Dims.exampleGrow
    (E := 0) (D := 60) (δ := 1) (s := s) (t := t)
    (by norm_num) (by norm_num) hs0 hst ht1 hregPaper (by norm_num) 1 (by norm_num)
  refine ⟨τ', hτ', hs0, hst, ht1, hregPaper, ?_⟩
  filter_upwards [hsupport, hcap] with N hsN hcapN
  obtain ⟨ω, hgood, hactive, hweights⟩ := hsN.2
  have hω : ω ∈ normEvent Dims.exampleGrow N := by
    simpa [normEvent, APrimeGeneralMovingGoodMesh.good] using hgood
  have hweight : APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t
        (APrimeGeneralMovingMesh.targetMesh 60)) 1
      (actualJ Dims.exampleGrow 0 60 s) s t
      (APrimeGeneralMovingMesh.targetMesh 60) 1 1 N 1 ω = 1 := by
    simpa only [actualJ, APrimeGeneralMovingDetFields.J] using hweights 1 (by norm_num)
  have hweightPos : 0 < APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t
        (APrimeGeneralMovingMesh.targetMesh 60)) 1
      (actualJ Dims.exampleGrow 0 60 s) s t
      (APrimeGeneralMovingMesh.targetMesh 60) 1 1 N 1 ω := by
    rw [hweight]
    norm_num
  have hcapω := hcapN 1 (by norm_num) hactive ω hω hweightPos
  refine ⟨hsN.1, ω, hω, hactive, hweightPos, ?_⟩
  simpa [s, actualJ, pow_two] using hcapω

#print axioms loopModulusConst_pos
#print axioms eventually_endpoint_floor
#print axioms jTotNormEv_le_const_mul
#print axioms eventually_jSnorm_modulus
#print axioms measurableSet_normEvent
#print axioms zero_mem_normEvent
#print axioms target_mesh_fine_eq_inv_sq
#print axioms eventually_running_prefix_cap
#print axioms positive_length_same_norm_running_cap_witness

end
end RBM.APrimeGeneralMovingLoopModulusGeneralDims
