/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingWindowFloor

/-!
# T475: the normalized-loop modulus on general moving windows

The endpoint floor supplied by `Cond272Reg` makes every singular coefficient
in the public pointwise normalized-loop modulus polynomial in `N`.  Keeping the
fixed bulk-energy factor separate gives the exponent `2D+7` uniformly on an
arbitrary admissible moving window.
-/

namespace RBM.APrimeGeneralMovingLoopModulus

open Filter Set Real Gauss
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

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

set_option maxHeartbeats 1000000 in
-- The expanded coefficient has nested real powers whose monotonicity proof
-- needs more than the project default heartbeat limit during elaboration.
/-- Deterministic coefficient estimate at one endpoint.  The extra final
power of `N` is deliberately left out here; it absorbs the fixed energy
constant in the eventual statement below. -/
theorem jTotNormEv_le_const_mul {E D t₀ : ℝ} {N : ℕ}
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

/-- The full normalized loop is uniformly half-Hölder on every admissible
moving window, on the fixed spectral-norm event. -/
theorem eventually_jSnorm_modulus {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)},
      ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
      |Step2Moment.jSnorm (sample d) E D s N v ω -
          Step2Moment.jSnorm (sample d) E D s N w ω| ≤
        (N : ℝ) ^ (2 * D + 7) * |v - w| ^ ((1 : ℝ) / 2) := by
  have hK0 := loopModulusConst_pos hE
  have hbig : ∀ᶠ N : ℕ in atTop, max 1 (loopModulusConst E) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [APrimeGeneralMovingWindowFloor.eventually_endpoint_floor
      hE hs0 hst ht1 hc hreg,
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
  have hcoef := jTotNormEv_le_const_mul hE (by linarith : 1 ≤ D)
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

/-- Anti-vacuity: there is a positive-length admissible moving window, and
the norm event used by the modulus is eventually nonempty under the standard
Gaussian trace-moment input. -/
theorem positive_window_and_nonempty_norm_event
    (hTM : TraceMomentBound d) :
    (∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ ∀ᶠ N : ℕ in atTop, s N < t N) ∧
    (∀ᶠ N : ℕ in atTop,
      {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}.Nonempty) :=
  ⟨APrimeGeneralMovingWindowFloor.positive_length_grid_window_witness,
    Gauss.eventually_nonempty_normX_le d hTM⟩

#print axioms loopModulusConst_pos
#print axioms jTotNormEv_le_const_mul
#print axioms eventually_jSnorm_modulus
#print axioms positive_window_and_nonempty_norm_event

end
end RBM.APrimeGeneralMovingLoopModulus
