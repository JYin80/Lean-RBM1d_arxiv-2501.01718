/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingEarlyPrefixTransitionExclusion
import RBM1D.Gauss.APrimeGeneralMovingTargetTransitionExists
import RBM1D.Gauss.APrimeSmoothTransition

/-!
# T1213: far-index transition on the norm-good scalar ray

The target is the literal T995 first-cell mesh and canonical smoothing order.
-/

namespace RBM.APrimeGeneralMovingFirstCellFarGoodTransitionExistsRepair

open Filter Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh 60
private noncomputable abbrev s : ℕ → ℝ := Gauss.firstCellS 1
private noncomputable abbrev t : ℕ → ℝ := Gauss.firstCellT 1
private noncomputable abbrev δw : ℝ :=
  APrimeGeneralMovingSlotLossSchedule.deltaWeight (1 / 200)
private noncomputable abbrev ω : Gauss.Ω d :=
  APrimeSmoothTransition.scalarSample d (4 * Real.sqrt 2)

private theorem scalar_parameter :
    (4 : ℝ) * Real.sqrt 2 = 2 / Real.sqrt (1 / 8 : ℝ) := by
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs8 : Real.sqrt (1 / 8 : ℝ) = Real.sqrt 2 / 4 := by
    have hs8sq : (Real.sqrt (1 / 8 : ℝ)) ^ 2 = 1 / 8 := by norm_num
    have hs8pos : 0 ≤ Real.sqrt (1 / 8 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  rw [hs8]
  field_simp
  nlinarith

private theorem sample_norm (N : ℕ) :
    ‖Gauss.Xmat d N ω‖ = 4 * Real.sqrt 2 := by
  rw [APrimeSmoothTransition.Xmat_scalarSample]
  rw [norm_smul, norm_one, mul_one, Complex.norm_real]
  exact abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))

private theorem card_factor_le_nine_eighths (q m : ℕ)
    (hq : 1 ≤ q) (hm : 4 * q ≤ m) :
    (q : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) ≤ 9 / 8 := by
  have hm0 : 0 < m := by omega
  have hqR : (q : ℝ) ≤ 1 + ((2 * m : ℕ) : ℝ) * (1 / 8 : ℝ) := by
    have hmr : (4 : ℝ) * q ≤ m := by exact_mod_cast hm
    push_cast
    linarith
  have hbern : 1 + ((2 * m : ℕ) : ℝ) * (1 / 8 : ℝ) ≤
      (9 / 8 : ℝ) ^ (2 * m) := by
    convert (one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 8) (2 * m))
      using 1
    norm_num
  have hpow : (q : ℝ) ≤ (9 / 8 : ℝ) ^ (2 * m) := hqR.trans hbern
  have hpos : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hexp : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) := by positivity
  have hr := Real.rpow_le_rpow hpos hpow hexp
  have hn : (2 * (m : ℝ)) ≠ 0 := by positivity
  convert hr using 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9 / 8)]
  push_cast
  rw [mul_div_cancel₀ 1 hn, Real.rpow_one]

private theorem softMax_range_succ_le (m k : ℕ) (hm : 1 ≤ m)
    (f : ℕ → ℝ) :
    softMax m (Finset.range (k + 1)) f ≤
      (3 / 2 : ℝ) * max (softMax m (Finset.range k) f) |f k| := by
  let B := max (softMax m (Finset.range k) f) |f k|
  have hB : 0 ≤ B := le_trans (softMax_nonneg m (Finset.range k) f) (le_max_left _ _)
  have hn : 0 < 2 * m := by omega
  have he : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range k, f i ^ (2 * m) :=
    sum_even_pow_nonneg _ _ _
  have hpowP : (softMax m (Finset.range k) f) ^ (2 * m) =
      ∑ i ∈ Finset.range k, f i ^ (2 * m) := by
    unfold softMax
    convert Real.rpow_inv_natCast_pow hsum0 (show 2 * m ≠ 0 by omega) using 1
    push_cast
    ring
  have hpowf : f k ^ (2 * m) = |f k| ^ (2 * m) := by
    exact (abs_even_pow (f k) m).symm
  have hsum : ∑ i ∈ Finset.range (k + 1), f i ^ (2 * m) ≤
      2 * B ^ (2 * m) := by
    rw [Finset.sum_range_succ, ← hpowP, hpowf]
    have hP : (softMax m (Finset.range k) f) ^ (2 * m) ≤ B ^ (2 * m) :=
      pow_le_pow_left₀ (softMax_nonneg m _ _) (le_max_left _ _) _
    have hf : |f k| ^ (2 * m) ≤ B ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _
    linarith
  have hr := Real.rpow_le_rpow (sum_even_pow_nonneg (Finset.range (k + 1)) f m)
    hsum he.le
  have htwo : (2 : ℝ) ^ (1 / (2 * (m : ℝ))) ≤ 3 / 2 := by
    have he' : (1 : ℝ) / (2 * (m : ℝ)) ≤ 1 / 2 := by
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))
        (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he'
    have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
      have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
      have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      nlinarith
    have hs' : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 2 := by
      simpa only [Real.sqrt_eq_rpow] using hs
    exact h.trans hs'
  have hroot : (B ^ (2 * m)) ^ (1 / (2 * (m : ℝ))) = B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    have hmR : (2 * (m : ℝ)) ≠ 0 := by positivity
    push_cast
    rw [mul_div_cancel₀ 1 hmR, Real.rpow_one]
  change (∑ i ∈ Finset.range (k + 1), f i ^ (2 * m)) ^
      (1 / (2 * (m : ℝ))) ≤ _
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hB _), hroot] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right htwo hB)

/-- A finite first-crossing lemma for the actual even-power soft maximum.
Only adjacent `J` values are compared; no global early-time estimate is used. -/
private theorem softMax_first_strict_crossing
    (m k₀ kH : ℕ) (hm : 1 ≤ m) (hk₀ : 1 ≤ k₀)
    (hkH : k₀ < kH) (Θ ε : ℝ) (hΘ : 8 ≤ Θ)
    (hεsmall : ε ≤ 1 / 2)
    (J f : ℕ → ℝ)
    (hf0 : ∀ j < kH, 0 ≤ f j)
    (hJf : ∀ j < kH, J j ≤ f j)
    (hfJ : ∀ j < kH, f j ≤ (9 / 8 : ℝ) * (J j + ε))
    (hadj : ∀ j, j + 1 < kH → J (j + 1) ≤ J j + 1 / 2)
    (hlow : softMax m (Finset.range k₀) f ≤ Θ)
    (hhigh : Θ < softMax m (Finset.range kH) f) :
    ∃ k : ℕ, k₀ < k ∧ k ≤ kH ∧
      Θ < softMax m (Finset.range k) f ∧
      softMax m (Finset.range k) f < 2 * Θ := by
  let Q : ℕ → Prop := fun k => k₀ < k ∧ k ≤ kH ∧ Θ < softMax m (Finset.range k) f
  have hex : ∃ k, Q k := ⟨kH, hkH, le_rfl, hhigh⟩
  let k := Nat.find hex
  have hk : Q k := Nat.find_spec hex
  have hkprev : softMax m (Finset.range (k - 1)) f ≤ Θ := by
    by_cases hkeq : k = k₀ + 1
    · simpa [hkeq] using hlow
    · have hlt : k - 1 < k := by omega
      have hnQ : ¬ Q (k - 1) := Nat.find_min hex hlt
      have hk₀prev : k₀ < k - 1 := by omega
      have hktop : k - 1 ≤ kH := by omega
      exact le_of_not_gt (fun h => hnQ ⟨hk₀prev, hktop, h⟩)
  have hk2 : k - 2 < k - 1 := by omega
  have hk2H : k - 2 < kH := by omega
  have hk1H : k - 1 < kH := by omega
  have hnode : J (k - 2) ≤ Θ := by
    calc
      J (k - 2) ≤ f (k - 2) := hJf _ hk2H
      _ ≤ |f (k - 2)| := le_abs_self _
      _ ≤ softMax m (Finset.range (k - 1)) f :=
        le_softMax hm (Finset.mem_range.mpr hk2)
      _ ≤ Θ := hkprev
  have hnext : J (k - 1) ≤ Θ + 1 / 2 := by
    have h := hadj (k - 2) (by omega)
    have heq : k - 2 + 1 = k - 1 := by omega
    rw [heq] at h
    linarith
  have hfnext : f (k - 1) ≤ (81 / 64 : ℝ) * Θ := by
    have h := hfJ _ hk1H
    have hεJ : J (k - 1) + ε ≤ Θ + 1 := by linarith
    have hconst : Θ + 1 ≤ (9 / 8 : ℝ) * Θ := by linarith
    nlinarith
  have hmax : max (softMax m (Finset.range (k - 1)) f) |f (k - 1)| ≤
      (81 / 64 : ℝ) * Θ := by
    rw [abs_of_nonneg (hf0 _ hk1H)]
    exact max_le (hkprev.trans (by nlinarith)) hfnext
  have hk1 : k - 1 + 1 = k := by omega
  have hsoft := softMax_range_succ_le m (k - 1) hm f
  rw [hk1] at hsoft
  have htop : softMax m (Finset.range k) f < 2 * Θ := by
    calc
      _ ≤ (3 / 2 : ℝ) * max (softMax m (Finset.range (k - 1)) f) |f (k - 1)| := hsoft
      _ ≤ (3 / 2 : ℝ) * ((81 / 64 : ℝ) * Θ) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ < 2 * Θ := by nlinarith
  exact ⟨k, hk.1, hk.2.1, hk.2.2, htop⟩

private theorem firstCellS_zero (N : ℕ) : s N = 0 := by
  change Gauss.firstCellS 1 N = 0
  unfold Gauss.firstCellS
  exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem eventually_firstCellT_half :
    ∀ᶠ N : ℕ in atTop, t N = 1 / 2 := by
  have ht : Tendsto (fun N : ℕ => (Gauss.Dims.exampleGrow.W N : ℝ)^(-(1 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      (Step2.tendsto_W (Gauss.band Gauss.Dims.exampleGrow))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hN
  change gridT ((Gauss.band Gauss.Dims.exampleGrow).W N : ℝ) 1 (1 / 2) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Gauss.Dims.growW N : ℝ)^(-(1 : ℝ)) < 1 / 2 at hN
  linarith

private theorem eventual_mesh_eq (N : ℕ) (hN : 0 < N) :
    mesh N = (N : ℝ) ^ (258 : ℕ) := by
  dsimp [mesh, APrimeGeneralMovingMesh.targetMesh]
  rw [APrimeGeneralMovingMesh.polynomialMesh_eq_of_pos hN]
  norm_num

private theorem even_eighth_divides (N : ℕ) (hEven : Even N) :
    8 ∣ N ^ 258 := by
  obtain ⟨n, rfl⟩ := hEven
  have hpow : 8 ∣ 2 ^ 258 := by
    convert (pow_dvd_pow 2 (by omega : 3 ≤ 258)) using 1
  have heq : n + n = 2 * n := by omega
  rw [heq, mul_pow]
  exact dvd_mul_of_dvd_left hpow _

private theorem high_node_arithmetic (N : ℕ) (hN : 2 ≤ N) (hEven : Even N)
    (ht : t N = 1 / 2) :
    let jH := N ^ 258 / 8
    cutNetPt s mesh N jH = 1 / 8 ∧
    N ^ 10 < jH + 1 ∧
    jH + 1 ≤ cutNetTop s t mesh N := by
  let jH := N ^ 258 / 8
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmesh : mesh N = (N : ℝ) ^ (258 : ℕ) := eventual_mesh_eq N hNpos
  have hdiv : 8 ∣ N ^ 258 := even_eighth_divides N hEven
  have hmul : jH * 8 = N ^ 258 := Nat.div_mul_cancel hdiv
  have hmulR : (jH : ℝ) * 8 = (N : ℝ) ^ (258 : ℕ) := by
    exact_mod_cast hmul
  have hpow : N ^ 10 < jH := by
    have hn2 : 2 ≤ N := hN
    have hn8 : 8 * N ^ 10 < N ^ 258 := by
      have hpow248 : 8 < N ^ 248 := by
        have h : 2 ^ 4 ≤ N ^ 248 := by
          calc
            2 ^ 4 ≤ N ^ 4 := pow_le_pow_left₀ (by omega) hn2 _
            _ ≤ N ^ 248 := pow_le_pow_right₀ (by omega) (by omega)
        norm_num at h
        omega
      have hpow10 : 0 < N ^ 10 := pow_pos hNpos _
      calc
        8 * N ^ 10 < N ^ 248 * N ^ 10 := Nat.mul_lt_mul_of_pos_right hpow248 hpow10
        _ = N ^ 258 := by rw [← pow_add]
    omega
  have htime : cutNetPt s mesh N jH = 1 / 8 := by
    simp only [cutNetPt, firstCellS_zero, zero_add, hmesh]
    apply (div_eq_iff (pow_ne_zero _ (by positivity : (N : ℝ) ≠ 0))).2
    nlinarith [hmulR]
  have htop : jH + 1 ≤ cutNetTop s t mesh N := by
    unfold cutNetTop
    apply Nat.le_floor
    rw [ht, firstCellS_zero, hmesh]
    have hj : (jH : ℝ) + 1 ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (258 : ℕ) := by
      have hpow8 : (8 : ℝ) ≤ (N : ℝ) ^ (258 : ℕ) := by
        have h : (2 : ℝ) ^ (4 : ℕ) ≤ (N : ℝ) ^ (258 : ℕ) := by
          calc
            (2 : ℝ) ^ (4 : ℕ) ≤ (N : ℝ) ^ (4 : ℕ) :=
              pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hN) _
            _ ≤ (N : ℝ) ^ (258 : ℕ) :=
              pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ N by omega)) (by omega)
        norm_num at h
        linarith
      nlinarith [hmulR]
    simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using hj
  exact ⟨htime, by omega, htop⟩

private theorem eventually_large_bandwidth :
    ∀ᶠ N : ℕ in atTop,
      1024 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (1 / 10000 : ℝ) <
        (d.W N : ℝ) := by
  have hexp : (0 : ℝ) < 5 / 8 - 1 / 10000 := by norm_num
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (5 / 8 - 1 / 10000 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  filter_upwards [Gauss.Dims.bandwidth_grow,
    ht.eventually_gt_atTop (1024 * (Real.exp 1) ^ 2),
    eventually_ge_atTop (1 : ℕ)] with N hW hlarge hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW' : (N : ℝ) ^ (5 / 8 : ℝ) ≤ (d.W N : ℝ) := by
    have he : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
    simpa only [he, d, Gauss.Dims.exampleGrow_W] using hW
  have hmul := mul_lt_mul_of_pos_right hlarge
    (Real.rpow_pos_of_pos hNpos (1 / 10000 : ℝ))
  rw [← Real.rpow_add hNpos] at hmul
  have he : (5 / 8 : ℝ) - 1 / 10000 + 1 / 10000 = 5 / 8 := by ring
  rw [he] at hmul
  exact hmul.trans_le hW'

private theorem adjacent_coefficient_small (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) ^ (122 : ℝ) *
      |(1 : ℝ) / (N : ℝ) ^ (258 : ℕ)| ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hsqrt : |(1 : ℝ) / (N : ℝ) ^ (258 : ℕ)| ^ (1 / 2 : ℝ) =
      ((N : ℝ) ^ (129 : ℕ))⁻¹ := by
    have hpow : (N : ℝ) ^ (258 : ℕ) = ((N : ℝ) ^ (129 : ℕ)) ^ 2 := by
      rw [← pow_mul]
    rw [hpow]
    have hp : (0 : ℝ) < (N : ℝ) ^ (129 : ℕ) := pow_pos hNpos _
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ (129 : ℕ)) ^ 2)]
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hp]
    simp only [one_div]
  rw [hsqrt, Real.rpow_ofNat]
  have hpow : (N : ℝ) ^ (129 : ℕ) =
      (N : ℝ) ^ (122 : ℕ) * (N : ℝ) ^ (7 : ℕ) := by
    rw [← pow_add]
  rw [hpow]
  have hp122 : (N : ℝ) ^ (122 : ℕ) ≠ 0 := (pow_pos hNpos _).ne'
  have heq : (N : ℝ) ^ (122 : ℕ) *
      ((N : ℝ) ^ (122 : ℕ) * (N : ℝ) ^ (7 : ℕ))⁻¹ =
      ((N : ℝ) ^ (7 : ℕ))⁻¹ := by field_simp
  rw [heq]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
  apply (inv_le_inv₀ (pow_pos hNpos _) (by norm_num : (0 : ℝ) < 2)).2
  have hpow2 : (2 : ℝ) ≤ (N : ℝ) ^ (7 : ℕ) := by
    calc
      (2 : ℝ) ≤ N := hNr
      _ ≤ (N : ℝ) ^ (7 : ℕ) := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N)
          (by omega : 1 ≤ 7)
  exact hpow2

set_option maxHeartbeats 1000000 in
-- The concrete first-cell specialization expands both nested soft maxima and floor arithmetic.
/-- The same explicit norm-good scalar sample crosses the literal strict band
at an active index beyond the early-prefix exclusion range. -/
theorem eventually_even_far_good_transition :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ k : ℕ, N ^ 10 < k ∧
        k ≤ cutNetTop (Gauss.firstCellS 1) (Gauss.firstCellT 1)
          (APrimeGeneralMovingMesh.targetMesh 60) N ∧
        ‖Gauss.Xmat Dims.exampleGrow N
          (APrimeSmoothTransition.scalarSample Dims.exampleGrow (4 * Real.sqrt 2))‖ ≤
          (N : ℝ) ∧
        APrimeSmoothTransition.scalarSample Dims.exampleGrow (4 * Real.sqrt 2) ∈
          APrimeCrossJointSplit.transition Dims.exampleGrow 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight (1 / 200))
            (Gauss.firstCellS 1) (APrimeGeneralMovingMesh.targetMesh 60) N k
            (APrimeSmoothWeightActual.canonicalM Dims.exampleGrow
              (Gauss.firstCellS 1) (Gauss.firstCellT 1)
              (APrimeGeneralMovingMesh.targetMesh 60) N) := by
  change ∀ᶠ N : ℕ in atTop, Even N →
    ∃ k : ℕ, N ^ 10 < k ∧ k ≤ cutNetTop s t mesh N ∧
      ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) ∧
      ω ∈ APrimeCrossJointSplit.transition d 0 60 δw s mesh N k
        (APrimeSmoothWeightActual.canonicalM d s t mesh N)
  have hmod := APrimeSlotFields.eventually_modulus_jSnorm_event d
    (E := 0) (D := 60) (t₀ := 1 / 2)
    (s := s) (t := t)
    (Good := fun N => {ω : Gauss.Ω d | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)})
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun N => by rw [firstCellS_zero])
    (fun N => by
      change Gauss.firstCellT 1 N ≤ 1 / 2
      unfold Gauss.firstCellT
      exact gridT_le (1 / 2 : ℝ) 1)
    (fun _ _ hω => hω)
  have hlow :=
    APrimeGeneralMovingEarlyPrefixTransitionExclusion.eventually_early_prefix_transition_exclusion
    (τ' := 1) (c := 1) (δ := 1 / 200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_firstCellT_half, eventually_large_bandwidth,
    hmod, hlow, eventually_ge_atTop (8 : ℕ),
    APrimeGeneralMovingMesh.eventually_targetMesh_eq (60 : ℝ)]
    with N ht hW hmodN hlowN hN8 hmeshEq
  intro hEven
  let k₀ : ℕ := N ^ 10
  let jH : ℕ := N ^ 258 / 8
  let kH : ℕ := jH + 1
  letI : NeZero (d.L N) := ⟨by
    have hL := d.three_le_L N
    omega⟩
  let q : ℕ := Fintype.card (LoopArg (d.L N) 2)
  let m : ℕ := APrimeSmoothWeightActual.canonicalM d s t mesh N
  let Θ : ℝ := APrimeSmoothWeightActual.threshold δw N
  let ε : ℝ := (N : ℝ) ^ (-(10 : ℝ))
  let J : ℕ → ℝ := fun j => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N
    (cutNetPt s mesh N j) ω
  let f : ℕ → ℝ := fun j => APrimeSmoothPrefix.smoothJS d 0 60 s N
    (cutNetPt s mesh N j) (APrimeSmoothWeightActual.epsilon d 60 N) m ω
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmesh : mesh N = (N : ℝ) ^ (258 : ℕ) := by
    change APrimeGeneralMovingMesh.targetMesh 60 N = _
    rw [hmeshEq]
    norm_num
  have hmeshpos : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  have hs : s N = 0 := firstCellS_zero N
  have hsfun : s = fun _ => 0 := by
    funext n
    exact firstCellS_zero n
  have hst : s N ≤ t N := by rw [hs, ht]; norm_num
  have ht1 : t N < 1 := by rw [ht]; norm_num
  have hm : 1 ≤ m := APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hq : 1 ≤ q := by
    change 0 < Fintype.card (LoopArg (d.L N) 2)
    exact Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  obtain ⟨huh, hk₀H, hkHtop⟩ := high_node_arithmetic N hN2 hEven ht
  have hk₀top : k₀ ≤ cutNetTop s t mesh N := by omega
  have hnorm : ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) := by
    rw [sample_norm]
    have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
      have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
      have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      nlinarith
    have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN8
    nlinarith
  have hΘeq : Θ = 8 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (1 / 10000 : ℝ) := by
    dsimp [Θ, APrimeSmoothWeightActual.threshold, δw,
      APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    norm_num
  have hΘ8 : 8 ≤ Θ := by
    have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10000 : ℝ) :=
      Real.one_le_rpow hNr (by norm_num)
    rw [hΘeq]
    nlinarith
  have hP : ∀ k : ℕ,
      APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N k m ω =
        softMax m (Finset.range k) f := by
    intro k
    unfold APrimeSmoothWeightActual.prefixSample APrimeSmoothWeightActual.prefixMatrix
    apply congrArg (fun g : ℕ → ℝ => softMax m (Finset.range k) g)
    funext j
    exact APrimeSmoothPrefix.smoothJSMatrix_flow d 0 60 s N
      (cutNetPt s mesh N j) (APrimeSmoothWeightActual.epsilon d 60 N) m ω
  have hlowP : softMax m (Finset.range k₀) f ≤ Θ := by
    have h := (hlowN k₀ hk₀top (by rfl) ω hnorm).1.2
    rw [← hP]
    exact (div_le_one (APrimeSmoothWeightActual.threshold_pos hNpos)).1 h.le
  have hhighP : Θ < softMax m (Finset.range kH) f := by
    have hlower : (d.W N : ℝ) / 64 ≤ J jH := by
      have hparam : ω = APrimeSmoothTransition.scalarSample d
          (2 / Real.sqrt (1 / 8 : ℝ)) := by
        dsimp [ω]
        rw [scalar_parameter]
      dsimp [J]
      rw [huh, hsfun, hparam]
      exact APrimeSmoothTransition.jSnorm_transition_lower d N
        (by norm_num : (0 : ℝ) < 1 / 8)
        (by norm_num : (1 / 8 : ℝ) ≤ 1 / 8)
        (by norm_num : (2 : ℝ) ≤ 60)
    have hJprefix : J jH ≤ softMax m (Finset.range kH) f := by
      rw [← hP]
      dsimp [J]
      rw [hsfun]
      exact APrimeSmoothTransition.jSnorm_net_le_prefixSample d
        hNpos hm (by omega : jH < kH) (by rw [← hsfun, huh]; norm_num) ω
    have hΘW : Θ < (d.W N : ℝ) / 64 := by
      rw [hΘeq]
      nlinarith [hW]
    exact hΘW.trans_le (hlower.trans hJprefix)
  have htop4 : 4 ≤ cutNetTop s t mesh N := by
    have hk₀large : 4 ≤ k₀ := by
      dsimp [k₀]
      have h := pow_le_pow_right₀ (show 1 ≤ N by omega) (by omega : 1 ≤ 10)
      have h8 : 4 ≤ N := by omega
      exact h8.trans (by simpa only [pow_one] using h)
    omega
  have hmq : 4 * q ≤ m := by
    have h := Nat.mul_le_mul_right q htop4
    dsimp [m, APrimeSmoothWeightActual.canonicalM]
    dsimp [q] at h ⊢
    omega
  have hA : (q : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) ≤ 9 / 8 :=
    card_factor_le_nine_eighths q m hq hmq
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hεsmall : ε ≤ 1 / 2 := by
    have h : ε ≤ (N : ℝ) ^ (-(1 : ℝ)) := by
      dsimp [ε]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
    have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hInv : (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one]
      simpa only [one_div] using
        ((inv_le_inv₀ (by linarith : (0 : ℝ) < N)
          (by norm_num : (0 : ℝ) < 2)).2 hN2r)
    exact h.trans hInv
  have hnodeIcc (j : ℕ) (hj : j < kH) :
      cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) := by
    have hjTop : j ≤ cutNetTop s t mesh N := by omega
    exact MomentDuhamelCut.netFinset_subset_Icc hst hmeshpos _
      (cutNetPt_mem_netFinset hjTop)
  have hf0 : ∀ j < kH, 0 ≤ f j := by
    intro j hj
    dsimp [f]
    exact (APrimeSmoothPrefix.smoothJS_pos d (by norm_num) (by rw [hs]; norm_num)
      ((hnodeIcc j hj).2.trans_lt ht1) m ω).le
  have hJf : ∀ j < kH, J j ≤ f j := by
    intro j hj
    dsimp [J, f]
    exact APrimeSmoothPrefix.jSnorm_le_smoothJS d (by norm_num)
      (by rw [hs]; norm_num) ((hnodeIcc j hj).2.trans_lt ht1)
      (APrimeSmoothWeightActual.epsilon_pos d 60 hNpos).le hm ω
  have hfJ : ∀ j < kH, f j ≤ (9 / 8 : ℝ) * (J j + ε) := by
    intro j hj
    have hu := hnodeIcc j hj
    have hinner := APrimeSmoothWeightActual.smoothJS_le_card_mul_jSnorm_add d
      (E := 0) (D := 60) (u := cutNetPt s mesh N j) (s := s) (N := N) (m := m)
      (by norm_num) hu.1 (hu.2.trans_lt ht1) hNpos hm ω
    have hJnonneg : 0 ≤ J j := by
      dsimp [J]
      exact Step2Moment.jSnorm_nonneg (Gauss.sample d) (by norm_num)
        (by rw [hs]; norm_num) (hu.2.trans_lt ht1) ω
    calc
      f j ≤ (q : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) * (J j + ε) := by
        simpa only [f, J, q, ε] using hinner
      _ ≤ (9 / 8 : ℝ) * (J j + ε) :=
        mul_le_mul_of_nonneg_right hA (by linarith)
  have hadj : ∀ j, j + 1 < kH → J (j + 1) ≤ J j + 1 / 2 := by
    intro j hj
    have hu1 := hnodeIcc (j + 1) hj
    have hu0 := hnodeIcc j (by omega)
    have hmodVal := hmodN ω hnorm (cutNetPt s mesh N (j + 1)) hu1
      (cutNetPt s mesh N j) hu0
    have htime : cutNetPt s mesh N (j + 1) - cutNetPt s mesh N j =
        1 / mesh N := by
      simp only [cutNetPt, Nat.cast_add, Nat.cast_one]
      ring
    have hsmall : (N : ℝ) ^ (122 : ℝ) *
        |cutNetPt s mesh N (j + 1) - cutNetPt s mesh N j| ^ (1 / 2 : ℝ) ≤
        1 / 2 := by
      rw [htime, hmesh]
      exact adjacent_coefficient_small N hN2
    have hmodVal' : |J (j + 1) - J j| ≤ 1 / 2 := by
      have h' : |J (j + 1) - J j| ≤ (N : ℝ) ^ (122 : ℝ) *
          |cutNetPt s mesh N (j + 1) - cutNetPt s mesh N j| ^ (1 / 2 : ℝ) := by
        simpa [J, show (2 : ℝ) + 2 * 60 = 122 by norm_num] using hmodVal
      exact h'.trans hsmall
    linarith [(abs_le.mp hmodVal').2]
  obtain ⟨k, hk₀, hkH, hcrossLow, hcrossHigh⟩ :=
    softMax_first_strict_crossing m k₀ kH hm (by
      dsimp [k₀]
      have hp : 0 < N ^ 10 := pow_pos hNpos _
      omega)
      hk₀H Θ ε hΘ8 hεsmall J f hf0 hJf hfJ hadj hlowP hhighP
  have hkTop : k ≤ cutNetTop s t mesh N := hkH.trans hkHtop
  have hΘpos : 0 < Θ := by linarith
  have hratioLow : 1 < softMax m (Finset.range k) f / Θ :=
    (one_lt_div hΘpos).2 hcrossLow
  have hratioHigh : softMax m (Finset.range k) f / Θ < 2 :=
    (div_lt_iff₀ hΘpos).2 hcrossHigh
  refine ⟨k, hk₀, hkTop, hnorm, ?_⟩
  change 1 < APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N k m ω / Θ ∧
    APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N k m ω / Θ < 2
  rw [hP]
  exact ⟨hratioLow, hratioHigh⟩

#print axioms eventually_even_far_good_transition

end RBM.APrimeGeneralMovingFirstCellFarGoodTransitionExistsRepair
