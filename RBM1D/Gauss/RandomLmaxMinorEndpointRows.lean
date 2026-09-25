/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxFirstCellEntry

/-!
# Actual first-cell minor endpoint rows at random `Lmax`

For every fixed loss `b > 0`, a variable threshold `N^β firstCellPsi` with
`β = min (b/8) (1/16)` gives an actual first-cell flow-net event.  On that same
sample, the finite-budget minor bounds control both normalized original-block
endpoint row and column square sums by `20 N^b Lmax`.
-/

namespace RBM.Gauss

open Filter MeasureTheory
open scoped BigOperators

/-- The exponent reserved for the arbitrary small polynomial loss. -/
noncomputable def firstCellMinorEndpointBeta (b : ℝ) : ℝ := min (b / 8) (1 / 16)

/-- The first-cell event threshold for endpoint loss `b`. -/
noncomputable def firstCellMinorEndpointDelta (b : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ firstCellMinorEndpointBeta b * firstCellPsi N

theorem firstCellMinorEndpointBeta_pos {b : ℝ} (hb : 0 < b) :
    0 < firstCellMinorEndpointBeta b := by
  unfold firstCellMinorEndpointBeta
  exact lt_min (by positivity) (by norm_num)

theorem firstCellMinorEndpointBeta_le_b_div_eight (b : ℝ) :
    firstCellMinorEndpointBeta b ≤ b / 8 := min_le_left _ _

theorem firstCellMinorEndpointBeta_le_one_sixteenth (b : ℝ) :
    firstCellMinorEndpointBeta b ≤ 1 / 16 := min_le_right _ _

private theorem firstCellMinorEndpointDelta_small {b : ℝ} (M : ℕ) :
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

/-- The actual time-and-entry-uniform first-cell good event at the arbitrary
small-loss threshold is high probability.  The net/index lift is the accepted
`highProb_goodSetFlow_of_localLaw`, with strict margin exponent `β/2 < β`. -/
theorem firstCell_randomLmax_minor_endpoint_flowNetEvent_highProb
    {τ' b : ℝ} (hτ' : 0 < τ') (hb : 0 < b)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi) :
    HighProb (P Dims.exampleGrow)
      (flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
        (firstCellMinorEndpointDelta b)) := by
  let d := Dims.exampleGrow
  let β := firstCellMinorEndpointBeta b
  have hβ : 0 < β := firstCellMinorEndpointBeta_pos hb
  have hβhalf : 0 < β / 2 := by positivity
  have hβmargin : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (β / 2) * firstCellPsi N ≤ firstCellMinorEndpointDelta b N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow : (N : ℝ) ^ (β / 2) ≤ (N : ℝ) ^ β := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      linarith
    rw [firstCellMinorEndpointDelta]
    exact mul_le_mul_of_nonneg_right hpow (firstCellPsi_pos N).le
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le
      (1 / 2 : ℝ) (Nat.zero_le 1)
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, _, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := first_cell_polynomial_regime d τ'
  have hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ')
        (firstCellMinorEndpointDelta b)) := by
    exact highProb_goodSetFlow_of_localLaw d
      (τ := β / 2) (E := 0) (s := firstCellS τ') (t := firstCellT τ')
      (δ := firstCellMinorEndpointDelta b) (Ψ := firstCellPsi)
      (K := 3) (B := 2) hβhalf (by norm_num) hs0 ht1 hst
      (by norm_num) (by norm_num) hKbig
      (fun N => (hΨpos N).le) hΨlowLL hll hβmargin
  exact highProb_flowNetEvent d hΩ

private theorem firstCell_minor_endpoint_entry_sq_bound
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {b : ℝ} {M : ℕ}
    {S : Finset (Dims.exampleGrow.Idx N)} {κ x : Dims.exampleGrow.Idx N}
    (hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M)
    (hS : S.card ≤ M) (hκ : κ ∉ S)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hxκ : x = κ) :
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω x κ S‖ ^ 2 ≤ 4 := by
  subst x
  have hdiag := hg.diag_sub_le S hS κ hκ
  have hm : ‖mE 0‖ = 1 := norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)
  have hnorm : ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖ ≤ 2 := by
    calc
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖ =
          ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S - mE 0) + mE 0‖ := by
            congr 1
            ring
      _ ≤ ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S - mE 0‖ + ‖mE 0‖ :=
        norm_add_le _ _
      _ ≤ 2 * firstCellMinorEndpointDelta b N + 1 := by
        nlinarith [hdiag, hm]
      _ ≤ 2 := by nlinarith
  have hnorm0 : 0 ≤ ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖ := norm_nonneg _
  nlinarith [mul_nonneg (by linarith : 0 ≤
      2 - ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖)
    (by linarith : 0 ≤ 2 + ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖)]

private theorem firstCell_minor_endpoint_entry_sq_bound_col
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {b : ℝ} {M : ℕ}
    {S : Finset (Dims.exampleGrow.Idx N)} {κ x : Dims.exampleGrow.Idx N}
    (hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M)
    (hS : S.card ≤ M) (hκ : κ ∉ S)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hxκ : x = κ) :
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ x S‖ ^ 2 ≤ 4 := by
  subst x
  have hdiag := hg.diag_sub_le S hS κ hκ
  have hm : ‖mE 0‖ = 1 := norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)
  have hnorm : ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖ ≤ 2 := by
    calc
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖ =
          ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S - mE 0) + mE 0‖ := by
            congr 1
            ring
      _ ≤ ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S - mE 0‖ + ‖mE 0‖ :=
        norm_add_le _ _
      _ ≤ 2 * firstCellMinorEndpointDelta b N + 1 := by
        nlinarith [hdiag, hm]
      _ ≤ 2 := by nlinarith
  have hnorm0 : 0 ≤ ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖ := norm_nonneg _
  nlinarith [mul_nonneg (by linarith : 0 ≤
      2 - ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖)
    (by linarith : 0 ≤ 2 + ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S‖)]

private theorem firstCell_minor_endpoint_normalized_sum_bound
    {τ' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {b : ℝ} {M : ℕ}
    {κ : Dims.exampleGrow.Idx N}
    {a : ZMod (Dims.exampleGrow.L N)}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hb : 0 < b) (hN : 1 ≤ N)
    (f : Dims.exampleGrow.Idx N → ℂ)
    (hterm : ∀ r : Fin (Dims.exampleGrow.W N),
      ‖f (a, r)‖ ^ 2 ≤ 4 * firstCellMinorEndpointDelta b N ^ 2 +
        4 * (if (a, r) = κ then 1 else 0)) :
    ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2) ≤
      20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N := hω.1
  have hδ0 : 0 ≤ firstCellMinorEndpointDelta b N := by
    unfold firstCellMinorEndpointDelta
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (firstCellPsi_pos N).le
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hz : (zt 0 u).im ≠ 0 := zt_im_ne_zero_of_lt_one (by norm_num) hu1
  have hG : GoodEvent (green (Hflow Dims.exampleGrow N u ω) (zt 0 u)) (mE 0)
      (firstCellMinorEndpointDelta b N) := hflow u hu
  have hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M :=
    minorGoodLe_of_goodEvent_flow (by norm_num) hz hδ0 hδquarter hMδ hG
  have hsingle : ∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2 ≤
      ((Dims.exampleGrow.W N : ℕ) : ℝ) * (4 * firstCellMinorEndpointDelta b N ^ 2) + 4 := by
    have hdiag : (∑ r : Fin (Dims.exampleGrow.W N),
        if (a, r) = κ then (1 : ℝ) else 0) ≤ 1 := by
      by_cases ha : a = κ.1
      · subst a
        have hpair : ∀ r : Fin (Dims.exampleGrow.W N),
            ((κ.1, r) = κ) ↔ r = κ.2 := by
          intro r
          cases κ with
          | mk block off =>
              change ((block, r) = (block, off)) ↔ r = off
              constructor
              · intro h
                exact congrArg Prod.snd h
              · intro h
                cases h
                rfl
        have heq : (∑ r : Fin (Dims.exampleGrow.W N),
            if (κ.1, r) = κ then (1 : ℝ) else 0) = 1 := by
          calc
            (∑ r : Fin (Dims.exampleGrow.W N),
                if (κ.1, r) = κ then (1 : ℝ) else 0) =
              ∑ r : Fin (Dims.exampleGrow.W N), if r = κ.2 then (1 : ℝ) else 0 := by
                cases κ with
                | mk block off =>
                    apply Finset.sum_congr rfl
                    intro r _
                    simp only [hpair r]
            _ = 1 := by
              rw [Finset.sum_ite_eq' Finset.univ κ.2]
              exact if_pos (Finset.mem_univ _)
        rw [heq]
      · have hne : ∀ r : Fin (Dims.exampleGrow.W N), (a, r) ≠ κ := by
          intro r hr
          exact ha (congrArg Prod.fst hr)
        calc
          (∑ r : Fin (Dims.exampleGrow.W N),
              if (a, r) = κ then (1 : ℝ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro r _
            rw [if_neg (hne r)]
          _ ≤ 1 := by norm_num
    calc
      ∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2
          ≤ ∑ r : Fin (Dims.exampleGrow.W N),
              (4 * firstCellMinorEndpointDelta b N ^ 2 +
                4 * (if (a, r) = κ then 1 else 0)) :=
            Finset.sum_le_sum fun r _ => hterm r
      _ = ((Dims.exampleGrow.W N : ℕ) : ℝ) *
            (4 * firstCellMinorEndpointDelta b N ^ 2) +
            4 * (∑ r : Fin (Dims.exampleGrow.W N),
              if (a, r) = κ then (1 : ℝ) else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      _ ≤ ((Dims.exampleGrow.W N : ℕ) : ℝ) *
            (4 * firstCellMinorEndpointDelta b N ^ 2) + 4 := by nlinarith
  have hWpos : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hWlow := inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellMinorEndpointDelta b) (E := 0)
    (by norm_num) (hδquarter.trans (by norm_num)) hflow hu
  have hsumNorm : ((Dims.exampleGrow.W N : ℝ)⁻¹) *
      (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2) ≤
        4 * firstCellMinorEndpointDelta b N ^ 2 +
          4 * ((Dims.exampleGrow.W N : ℝ)⁻¹) := by
    calc
      ((Dims.exampleGrow.W N : ℝ)⁻¹) *
          (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2)
          ≤ ((Dims.exampleGrow.W N : ℝ)⁻¹) *
              (((Dims.exampleGrow.W N : ℝ) *
                  (4 * firstCellMinorEndpointDelta b N ^ 2)) + 4) :=
            mul_le_mul_of_nonneg_left hsingle (inv_nonneg.mpr hWpos.le)
      _ = 4 * firstCellMinorEndpointDelta b N ^ 2 +
          4 * ((Dims.exampleGrow.W N : ℝ)⁻¹) := by field_simp
  have hψsq := firstCellPsi_sq_eq_invW_div_four N
  have hβloss : 2 * firstCellMinorEndpointBeta b ≤ b := by
    have := firstCellMinorEndpointBeta_le_b_div_eight b
    linarith
  have hpowle : (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) ≤ (N : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hβloss
  have hNpow : 1 ≤ (N : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hN) hb.le
  have hdeltaSq : firstCellMinorEndpointDelta b N ^ 2 =
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        ((Dims.exampleGrow.W N : ℝ)⁻¹) / 4 := by
    rw [firstCellMinorEndpointDelta, mul_pow]
    have hp : ((N : ℝ) ^ firstCellMinorEndpointBeta b) ^ 2 =
        (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1 <;> ring
    rw [hp, hψsq]
    ring
  have hL0 : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
    Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hdiagL : 4 * ((Dims.exampleGrow.W N : ℝ)⁻¹) ≤
      16 * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by nlinarith
  have hoffL : 4 * firstCellMinorEndpointDelta b N ^ 2 ≤
      4 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
    rw [hdeltaSq]
    have h1 : (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        ((Dims.exampleGrow.W N : ℝ)⁻¹) ≤
          (N : ℝ) ^ b * (4 * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
      calc
        (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
            ((Dims.exampleGrow.W N : ℝ)⁻¹)
            ≤ (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
                (4 * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) :=
              mul_le_mul_of_nonneg_left hWlow
                (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        _ ≤ (N : ℝ) ^ b *
              (4 * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) :=
              mul_le_mul_of_nonneg_right hpowle (by positivity)
    nlinarith
  calc
    ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N), ‖f (a, r)‖ ^ 2)
        ≤ 4 * firstCellMinorEndpointDelta b N ^ 2 +
            4 * ((Dims.exampleGrow.W N : ℝ)⁻¹) := hsumNorm
    _ ≤ 4 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) +
          16 * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
        add_le_add hoffL hdiagL
    _ ≤ 20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hNpow) hL0]

/-- Both normalized endpoint sums are controlled by the same sample's full-matrix
`Lmax`.  Deleted endpoints stay in the original `Fin W` sums through the zero
embedding `gEnt`. -/
theorem firstCell_randomLmax_minor_endpoint_row_column_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N)) (hS : S.card ≤ M)
    (κ : Dims.exampleGrow.Idx N) (hκ : κ ∉ S)
    (a : ZMod (Dims.exampleGrow.L N)) :
    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) κ S‖ ^ 2) ≤
      20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ∧
    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (a, r) S‖ ^ 2) ≤
      20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
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
  have hrowterm (r : Fin (Dims.exampleGrow.W N)) :
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) κ S‖ ^ 2 ≤
        4 * firstCellMinorEndpointDelta b N ^ 2 +
          4 * (if (a, r) = κ then 1 else 0) := by
    by_cases hr : (a, r) = κ
    · have hdiag := firstCell_minor_endpoint_entry_sq_bound hg hS hκ hδquarter hr
      have hval : ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) κ S‖ ^ 2 ≤ 4 := by
        simpa [hr] using hdiag
      rw [if_pos hr]
      nlinarith [sq_nonneg (firstCellMinorEndpointDelta b N)]
    · have hne : (a, r) ≠ κ := hr
      have hoff := hg.off_le S hS (a, r) κ hne
      rw [if_neg hr]
      have hx0 : 0 ≤ ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) κ S‖ :=
        norm_nonneg _
      have hfirst : 0 ≤ 2 * firstCellMinorEndpointDelta b N -
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) κ S‖ :=
        sub_nonneg.mpr hoff
      have hsecond : 0 ≤ 2 * firstCellMinorEndpointDelta b N +
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) κ S‖ := by positivity
      nlinarith [mul_nonneg hfirst hsecond]
  have hcolterm (r : Fin (Dims.exampleGrow.W N)) :
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (a, r) S‖ ^ 2 ≤
        4 * firstCellMinorEndpointDelta b N ^ 2 +
          4 * (if (a, r) = κ then 1 else 0) := by
    by_cases hr : (a, r) = κ
    · have hdiag := firstCell_minor_endpoint_entry_sq_bound_col hg hS hκ hδquarter hr
      have hval : ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (a, r) S‖ ^ 2 ≤ 4 := by
        simpa [hr] using hdiag
      rw [if_pos hr]
      nlinarith [sq_nonneg (firstCellMinorEndpointDelta b N)]
    · have hne : κ ≠ (a, r) := Ne.symm hr
      have hoff := hg.off_le S hS κ (a, r) hne
      rw [if_neg hr]
      have hx0 : 0 ≤ ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (a, r) S‖ :=
        norm_nonneg _
      have hfirst : 0 ≤ 2 * firstCellMinorEndpointDelta b N -
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (a, r) S‖ :=
        sub_nonneg.mpr hoff
      have hsecond : 0 ≤ 2 * firstCellMinorEndpointDelta b N +
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (a, r) S‖ := by positivity
      nlinarith [mul_nonneg hfirst hsecond]
  constructor
  · refine firstCell_minor_endpoint_normalized_sum_bound
      (τ' := τ') (N := N) (u := u) (ω := ω) (b := b) (M := M)
      (κ := κ) (a := a) hω hu hδquarter hMδ hb hN
      (fun x => gEnt Dims.exampleGrow N u (zt 0 u) ω x κ S) ?_
    intro r
    simpa using hrowterm r
  · refine firstCell_minor_endpoint_normalized_sum_bound
      (τ' := τ') (N := N) (u := u) (ω := ω) (b := b) (M := M)
      (κ := κ) (a := a) hω hu hδquarter hMδ hb hN
      (fun x => gEnt Dims.exampleGrow N u (zt 0 u) ω κ x S) ?_
    intro r
    simpa using hcolterm r

/-- A fresh nonempty same-sample first-cell event, with a positive interior
time, and both endpoint bounds at every time in the cell. -/
theorem firstCell_randomLmax_minor_endpoint_eventually
    {τ' b : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi)
    (hb : 0 < b) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
          (firstCellMinorEndpointDelta b) N,
        ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
          0 < u ∧ u < firstCellT τ' N ∧
            ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
              ∀ S : Finset (Dims.exampleGrow.Idx N), S.card ≤ M →
              ∀ κ : Dims.exampleGrow.Idx N, κ ∉ S →
              ∀ a : ZMod (Dims.exampleGrow.L N),
                let row := ((Dims.exampleGrow.W N : ℝ)⁻¹) *
                  (∑ r : Fin (Dims.exampleGrow.W N),
                    ‖gEnt Dims.exampleGrow N v (zt 0 v) ω (a, r) κ S‖ ^ 2)
                let col := ((Dims.exampleGrow.W N : ℝ)⁻¹) *
                  (∑ r : Fin (Dims.exampleGrow.W N),
                    ‖gEnt Dims.exampleGrow N v (zt 0 v) ω κ (a, r) S‖ ^ 2)
                row ≤ 20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N v ω) (zt 0 v) ∧
                col ≤ 20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N v ω) (zt 0 v) := by
  have hHP := firstCell_randomLmax_minor_endpoint_flowNetEvent_highProb hτ' hb hll
  have hnonempty := hHP.nonempty measure_univ
  have hwindow := first_cell_window_nondegenerate Dims.exampleGrow hτ'
  have hsmall := firstCellMinorEndpointDelta_small (b := b) M
  filter_upwards [hnonempty, hwindow, hsmall, eventually_ge_atTop 1]
    with N hnon hwindowN hsmallN hN
  rcases hnon with ⟨ω, hω⟩
  obtain ⟨u, hu, hu0, hut⟩ := firstCell_positive_interior_time hwindowN
  have hN1 : 1 ≤ N := hN
  refine ⟨ω, hω, u, hu, hu0, hut, ?_⟩
  intro v hv S hS κ hκ a
  have hrowcol := firstCell_randomLmax_minor_endpoint_row_column_le hω hb
    hsmallN.1 hsmallN.2 hN1 hv S hS κ hκ a
  exact hrowcol

/-- Actual Gaussian nondegeneracy and arbitrary-loss endpoint control, with
fixed `b` and `M` chosen before eventual `N`.  The witness event and positive
interior time belong to one fresh sample from the variable-threshold event. -/
theorem firstCell_randomLmax_actual_minor_endpoint_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      ∀ b : ℝ, 0 < b → ∀ M : ℕ,
        ∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
              (firstCellMinorEndpointDelta b) N,
            ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
              0 < u ∧ u < firstCellT τ' N ∧
                ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
                  ∀ S : Finset (Dims.exampleGrow.Idx N), S.card ≤ M →
                  ∀ κ : Dims.exampleGrow.Idx N, κ ∉ S →
                  ∀ a : ZMod (Dims.exampleGrow.L N),
                    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
                        (∑ r : Fin (Dims.exampleGrow.W N),
                          ‖gEnt Dims.exampleGrow N v (zt 0 v) ω (a, r) κ S‖ ^ 2) ≤
                      20 * (N : ℝ) ^ b *
                        Lmax (Hflow Dims.exampleGrow N v ω) (zt 0 v)) ∧
                    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
                        (∑ r : Fin (Dims.exampleGrow.W N),
                          ‖gEnt Dims.exampleGrow N v (zt 0 v) ω κ (a, r) S‖ ^ 2) ≤
                      20 * (N : ℝ) ^ b *
                        Lmax (Hflow Dims.exampleGrow N v ω) (zt 0 v)) := by
  obtain ⟨τ', hτ', hll, _⟩ := firstCell_randomLmax_actual_nondegenerate_witness
  refine ⟨τ', hτ', hll, ?_⟩
  intro b hb M
  filter_upwards [firstCell_randomLmax_minor_endpoint_eventually hτ' hll hb M]
    with N hN
  rcases hN with ⟨ω, hω, u, hu, hu0, hut, hrows⟩
  exact ⟨ω, hω, u, hu, hu0, hut, hrows⟩

#print axioms firstCellMinorEndpointBeta_pos
#print axioms firstCellMinorEndpointBeta_le_b_div_eight
#print axioms firstCellMinorEndpointBeta_le_one_sixteenth
#print axioms firstCell_randomLmax_minor_endpoint_flowNetEvent_highProb
#print axioms firstCell_randomLmax_minor_endpoint_row_column_le
#print axioms firstCell_randomLmax_minor_endpoint_eventually
#print axioms firstCell_randomLmax_actual_minor_endpoint_witness

end RBM.Gauss
