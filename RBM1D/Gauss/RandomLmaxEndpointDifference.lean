/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxFirstFace
import RBM1D.Gauss.RandomLmaxMinorEndpointRows

/-!
# Actual first-cell endpoint differences at random `Lmax`

On the accepted variable-loss `flowNetEvent`, one fresh deletion changes both normalized
endpoint row and column square sums by at most `320 N^(b+2β) Lmax^2`.  The sums stay on the
original block coordinates; `gEnt` supplies zero on deleted coordinates.
-/

namespace RBM.Gauss

open Filter MeasureTheory
open scoped BigOperators

/-- Eventually the accepted endpoint threshold is small enough for the finite-budget minor
good bounds.  The loss `b` and budget `M` are fixed before `N` tends to infinity. -/
private theorem firstCellEndpointDifferenceDelta_small {b : ℝ} (M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      firstCellMinorEndpointDelta b N ≤ 1 / 4 ∧
        8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 := by
  have hbeta := firstCellMinorEndpointBeta_le_one_sixteenth b
  have hpsi := firstCellPsi_le_rpow_neg_quarter
  have hMpow : ∀ᶠ N : ℕ in atTop,
      8 * (M : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow _ (by norm_num)
  have hfourpow : ∀ᶠ N : ℕ in atTop,
      4 ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow 4 (by norm_num)
  filter_upwards [hpsi, hMpow, hfourpow, eventually_ge_atTop 1]
    with N hpsiN hMpowN hfourpowN hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hδle : firstCellMinorEndpointDelta b N ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
    have hmul := mul_le_mul_of_nonneg_left hpsiN
      (Real.rpow_nonneg (Nat.cast_nonneg N) (firstCellMinorEndpointBeta b))
    have hpow : (N : ℝ) ^ firstCellMinorEndpointBeta b *
        (N : ℝ) ^ (-(1 : ℝ) / 4) =
          (N : ℝ) ^ (firstCellMinorEndpointBeta b - 1 / 4) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      firstCellMinorEndpointDelta b N =
          (N : ℝ) ^ firstCellMinorEndpointBeta b * firstCellPsi N := rfl
      _ ≤ (N : ℝ) ^ firstCellMinorEndpointBeta b *
          (N : ℝ) ^ (-(1 : ℝ) / 4) := hmul
      _ = (N : ℝ) ^ (firstCellMinorEndpointBeta b - 1 / 4) := hpow
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        linarith
  have hnegpow : (N : ℝ) ^ (-(3 : ℝ) / 16) =
      ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ := by
    rw [show -(3 : ℝ) / 16 = -((3 : ℝ) / 16) by ring,
      Real.rpow_neg (Nat.cast_nonneg N)]
  have hquarter : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ 1 / 4 := by
    rw [hnegpow]
    have hpos : (0 : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 16) := Real.rpow_pos_of_pos hN0 _
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hfourpowN
    norm_num at hinv ⊢
    exact hinv
  have hsmall : firstCellMinorEndpointDelta b N ≤ 1 / 4 := hδle.trans hquarter
  have hbudget : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMpos : (0 : ℝ) < 8 * (M : ℝ) := by
        exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
      have hpowpos : (0 : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 16) :=
        Real.rpow_pos_of_pos hN0 _
      have hinv : ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ ≤ (8 * (M : ℝ))⁻¹ :=
        inv_anti₀ hMpos hMpowN
      have hdeltaInv : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ (8 * (M : ℝ))⁻¹ := by
        rw [hnegpow]
        exact hinv
      calc
        8 * (M : ℝ) * firstCellMinorEndpointDelta b N
            ≤ 8 * (M : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 16) :=
              mul_le_mul_of_nonneg_left hδle (by positivity)
        _ ≤ 8 * (M : ℝ) * (8 * (M : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left hdeltaInv (by positivity)
        _ = 1 := by field_simp
  exact ⟨hsmall, hbudget⟩

/-- Both normalized endpoint difference sums for one fresh deletion, on the original block
coordinates.  The endpoint in the freely summed coordinate is allowed to equal either pivot
or to belong to `S`; the rank-one identity is used before any coordinate restriction. -/
theorem firstCell_randomLmax_minor_endpoint_difference_row_column_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N)) (hS : S.card + 1 ≤ M)
    (j k : Dims.exampleGrow.Idx N) (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k)
    (a : ZMod (Dims.exampleGrow.L N)) :
    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k S -
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (insert j S)‖ ^ 2) ≤
      320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2) ∧
    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) S -
            gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (insert j S)‖ ^ 2) ≤
      320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2) := by
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N := hω.1
  have ht1 : firstCellT τ' N < 1 := (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ht1
  have hz : (zt 0 u).im ≠ 0 := zt_im_ne_zero_of_lt_one (by norm_num) hu1
  have hδ0 : 0 ≤ firstCellMinorEndpointDelta b N := by
    unfold firstCellMinorEndpointDelta
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (firstCellPsi_pos N).le
  have hG : GoodEvent (green (Hflow Dims.exampleGrow N u ω) (zt 0 u)) (mE 0)
      (firstCellMinorEndpointDelta b N) := hflow u hu
  have hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M :=
    minorGoodLe_of_goodEvent_flow (by norm_num) hz hδ0 hδquarter hMδ hG
  have hSle : S.card ≤ M := by omega
  have hInsCard : (insert j S).card ≤ M := by
    rw [Finset.card_insert_of_notMem hj]
    exact hS
  have hrowcolj := firstCell_randomLmax_minor_endpoint_row_column_le
    hω hb hδquarter hMδ hN hu S hSle j hj a
  have hoff := hg.off_le S hSle j k hjk
  have hinv := hg.inv_le S hSle j
  have hoffSq : ‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 ≤
      (2 * firstCellMinorEndpointDelta b N) ^ 2 := by
    nlinarith [hoff, norm_nonneg (gEnt Dims.exampleGrow N u (zt 0 u) ω j k S)]
  have hinvSq : ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 ≤ 2 ^ 2 := by
    nlinarith [hinv, norm_nonneg ((gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹)]
  have hfactor :
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
          ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 ≤
        16 * firstCellMinorEndpointDelta b N ^ 2 := by
    calc
      _ ≤ (2 * firstCellMinorEndpointDelta b N) ^ 2 *
          ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hoffSq (sq_nonneg _)
      _ ≤ (2 * firstCellMinorEndpointDelta b N) ^ 2 * 2 ^ 2 :=
        mul_le_mul_of_nonneg_left hinvSq (sq_nonneg _)
      _ = 16 * firstCellMinorEndpointDelta b N ^ 2 := by ring
  have hWlow := inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellMinorEndpointDelta b) (E := 0)
    (by norm_num) (hδquarter.trans (by norm_num)) hflow hu
  have hpsiSq := firstCellPsi_sq_eq_invW_div_four N
  have hdeltaSq : firstCellMinorEndpointDelta b N ^ 2 =
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        ((Dims.exampleGrow.W N : ℝ)⁻¹) / 4 := by
    rw [firstCellMinorEndpointDelta, mul_pow]
    have hp : ((N : ℝ) ^ firstCellMinorEndpointBeta b) ^ 2 =
        (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1 <;> ring
    rw [hp, hpsiSq]
    ring
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hdeltaL : firstCellMinorEndpointDelta b N ^ 2 ≤
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
    rw [hdeltaSq]
    have hpow0 : 0 ≤ (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) :=
      Real.rpow_nonneg (Nat.cast_nonneg N) _
    nlinarith [hWlow]
  have hL0 : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
    Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hfactor0 : 0 ≤
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
        ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 := by positivity
  have hbase0 : 0 ≤ 20 * (N : ℝ) ^ b *
      Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by positivity
  have hcolFactor (f : Dims.exampleGrow.Idx N → ℂ)
      (hrow : ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2) ≤
          20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
      (hentry : ∀ r : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k S -
          gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (insert j S)‖ ^ 2 =
        ‖f (a, r)‖ ^ 2 *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2)) :
      ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k S -
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (insert j S)‖ ^ 2) ≤
        320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by
    have hsum :
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k S -
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (insert j S)‖ ^ 2) =
        (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2) *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2) := by
      calc
        _ = ∑ r : Fin (Dims.exampleGrow.W N),
            (‖f (a, r)‖ ^ 2 *
              (‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
                ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2)) := by
              apply Finset.sum_congr rfl
              intro r _
              exact hentry r
        _ = _ := by rw [Finset.sum_mul]
    calc
      _ = (((Dims.exampleGrow.W N : ℝ)⁻¹) *
          (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2)) *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2) := by
              rw [hsum]
              ring
      _ ≤ (20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) *
          (16 * firstCellMinorEndpointDelta b N ^ 2) := by
            exact le_trans
              (mul_le_mul_of_nonneg_right hrow hfactor0)
              (mul_le_mul_of_nonneg_left hfactor hbase0)
      _ = 320 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) *
          firstCellMinorEndpointDelta b N ^ 2 := by ring
      _ ≤ 320 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) *
          ((N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
            Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
            exact mul_le_mul_of_nonneg_left hdeltaL
              (by positivity)
      _ = 320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by
            calc
              _ = 320 * ((N : ℝ) ^ b *
                    (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b)) *
                  (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by ring
              _ = _ := by rw [Real.rpow_add hNpos]
  have hcolTerm (r : Fin (Dims.exampleGrow.W N)) :
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k S -
          gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (insert j S)‖ ^ 2 =
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) j S‖ ^ 2 *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω j k S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2) := by
    rw [gEnt_sub_insert_rankOne Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M S j (a, r) k hg hInsCard]
    simp only [norm_mul]
    ring
  have hrowTerm (r : Fin (Dims.exampleGrow.W N)) :
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) S -
          gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (insert j S)‖ ^ 2 =
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω j (a, r) S‖ ^ 2 *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2) := by
    rw [gEnt_sub_insert_rankOne Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M S j k (a, r) hg hInsCard]
    simp only [norm_mul]
    ring
  have hcol := hcolFactor
    (fun x => gEnt Dims.exampleGrow N u (zt 0 u) ω x j S)
    hrowcolj.1 hcolTerm
  have hoffRow := hg.off_le S hSle k j (Ne.symm hjk)
  have hoffRowSq : ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 ≤
      (2 * firstCellMinorEndpointDelta b N) ^ 2 := by
    nlinarith [hoffRow, norm_nonneg (gEnt Dims.exampleGrow N u (zt 0 u) ω k j S)]
  have hrowFactor :
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
          ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 ≤
        16 * firstCellMinorEndpointDelta b N ^ 2 := by
    calc
      _ ≤ (2 * firstCellMinorEndpointDelta b N) ^ 2 *
          ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hoffRowSq (sq_nonneg _)
      _ ≤ (2 * firstCellMinorEndpointDelta b N) ^ 2 * 2 ^ 2 :=
        mul_le_mul_of_nonneg_left hinvSq (sq_nonneg _)
      _ = 16 * firstCellMinorEndpointDelta b N ^ 2 := by ring
  have hrowFactor0 : 0 ≤
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
        ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2 := by positivity
  have hrow (f : Dims.exampleGrow.Idx N → ℂ)
      (hbound : ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2) ≤
          20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
      (hentry : ∀ r : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) S -
          gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (insert j S)‖ ^ 2 =
        ‖f (a, r)‖ ^ 2 *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2)) :
      ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) S -
            gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (insert j S)‖ ^ 2) ≤
        320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by
    have hsum :
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) S -
            gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (insert j S)‖ ^ 2) =
        (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2) *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2) := by
      calc
        _ = ∑ r : Fin (Dims.exampleGrow.W N),
            (‖f (a, r)‖ ^ 2 *
              (‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
                ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2)) := by
              apply Finset.sum_congr rfl
              intro r _
              exact hentry r
        _ = _ := by rw [Finset.sum_mul]
    calc
      _ = (((Dims.exampleGrow.W N : ℝ)⁻¹) *
          (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2)) *
          (‖gEnt Dims.exampleGrow N u (zt 0 u) ω k j S‖ ^ 2 *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω j j S)⁻¹‖ ^ 2) := by
              rw [hsum]
              ring
      _ ≤ (20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) *
          (16 * firstCellMinorEndpointDelta b N ^ 2) := by
            exact le_trans
              (mul_le_mul_of_nonneg_right hbound hrowFactor0)
              (mul_le_mul_of_nonneg_left hrowFactor hbase0)
      _ = 320 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) *
          firstCellMinorEndpointDelta b N ^ 2 := by ring
      _ ≤ 320 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) *
          ((N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
            Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
            exact mul_le_mul_of_nonneg_left hdeltaL (by positivity)
      _ = 320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by
            calc
              _ = 320 * ((N : ℝ) ^ b *
                    (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b)) *
                  (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by ring
              _ = _ := by rw [Real.rpow_add hNpos]
  refine ⟨hcol, ?_⟩
  exact hrow (fun x => gEnt Dims.exampleGrow N u (zt 0 u) ω j x S)
    hrowcolj.2 hrowTerm

/-- A positive-time actual Gaussian witness for the endpoint difference theorem.  The same
resident sample belongs to the accepted variable-loss event, supplies the pointwise row and
column estimates, and has positive diagonal second moment at the chosen interior time. -/
theorem firstCell_randomLmax_actual_endpoint_difference_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      ∀ b : ℝ, 0 < b → ∀ M : ℕ,
        ∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
              (firstCellMinorEndpointDelta b) N,
            ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
              0 < u ∧ u < firstCellT τ' N ∧
                (∀ i : Dims.exampleGrow.Idx N,
                  0 < ∫ ω', ‖Hflow Dims.exampleGrow N u ω' i i‖ ^ 2
                    ∂(P Dims.exampleGrow)) ∧
                ∀ S : Finset (Dims.exampleGrow.Idx N), S.card + 1 ≤ M →
                  ∀ j k : Dims.exampleGrow.Idx N, j ∉ S → k ∉ S → j ≠ k →
                    ∀ a : ZMod (Dims.exampleGrow.L N),
                      (((Dims.exampleGrow.W N : ℝ)⁻¹) *
                          (∑ r : Fin (Dims.exampleGrow.W N),
                            ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k S -
                              gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k
                                (insert j S)‖ ^ 2) ≤
                        320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
                          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2) ∧
                      (((Dims.exampleGrow.W N : ℝ)⁻¹) *
                          (∑ r : Fin (Dims.exampleGrow.W N),
                            ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) S -
                              gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r)
                                (insert j S)‖ ^ 2) ≤
                        320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
                          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2) := by
  obtain ⟨τ', hτ', hll, _⟩ := firstCell_randomLmax_actual_nondegenerate_witness
  refine ⟨τ', hτ', hll, ?_⟩
  intro b hb M
  have hHP := firstCell_randomLmax_minor_endpoint_flowNetEvent_highProb hτ' hb hll
  have hnonempty := hHP.nonempty measure_univ
  have hwindow := first_cell_window_nondegenerate Dims.exampleGrow hτ'
  have hsmall := firstCellEndpointDifferenceDelta_small (b := b) M
  filter_upwards [hnonempty, hwindow, hsmall, eventually_ge_atTop 1]
    with N hnon hwindowN hsmallN hN
  rcases hnon with ⟨ω, hω⟩
  obtain ⟨u, hu, hu0, hut⟩ := firstCell_positive_interior_time hwindowN
  have hN1 : 1 ≤ N := hN
  refine ⟨ω, hω, u, hu, hu0, hut, ?_, ?_⟩
  · intro i
    exact firstCell_positive_diag_flow_second_moment i hu0
  · intro S hS j k hj hk hjk a
    exact firstCell_randomLmax_minor_endpoint_difference_row_column_le hω hb
      hsmallN.1 hsmallN.2 hN1 hu S hS j k hj hk hjk a

#print axioms firstCell_randomLmax_minor_endpoint_difference_row_column_le
#print axioms firstCell_randomLmax_actual_endpoint_difference_witness

end RBM.Gauss
