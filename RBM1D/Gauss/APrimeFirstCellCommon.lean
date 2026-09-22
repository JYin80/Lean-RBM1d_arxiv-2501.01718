/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFullQV
import RBM1D.Gauss.APrimeSmoothWeightActual
import RBM1D.Gauss.FirstCellStep1LocalLaw

/-!
# The actual Gaussian first active prefix

This module works on one positive subcell of the first paper grid cell. The
same Gaussian sample is used in the norm event, the two-loop observable and
the smooth cutoff.
-/

namespace RBM.APrimeFirstCellCommon

open Filter MeasureTheory Step2Bootstrap CutHypTheta
open Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable def mesh (N : ℕ) : ℝ := (max 1 N : ℝ) ^ (248 : ℕ)

private noncomputable def h (N : ℕ) : ℝ := (mesh N)⁻¹

private noncomputable def J (N : ℕ) (u : ℝ) (ω : Gauss.Ω Gauss.Dims.exampleGrow) : ℝ :=
  Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow) 0 60 (fun _ => 0) N u ω

theorem J_zero (N : ℕ) (ω : Gauss.Ω Gauss.Dims.exampleGrow) : J N 0 ω = 1 := by
  have hlk : ∀ a : LoopArg (Gauss.Dims.exampleGrow.L N) 2,
      Step2.lk (Gauss.sample Gauss.Dims.exampleGrow) 0 N 0 ω a = 0 := by
    intro a
    exact lk_zero (Gauss.sample Gauss.Dims.exampleGrow) (by norm_num) N ω a
  have hj : Step2.jS (Gauss.sample Gauss.Dims.exampleGrow) 0 60 N 0 ω = 1 := by
    unfold Step2.jS Step2.jStar
    apply add_eq_right.mpr
    apply le_antisymm
    · apply Finset.sup'_le
      intro a ha
      simp [hlk a]
    · have ha : (Finset.univ : Finset (LoopArg (Gauss.Dims.exampleGrow.L N) 2)).Nonempty :=
        Finset.univ_nonempty
      let a := ha.choose
      have hle := Finset.le_sup'
        (s := (Finset.univ : Finset (LoopArg (Gauss.Dims.exampleGrow.L N) 2)))
        (fun a => ‖Step2.lk (Gauss.sample Gauss.Dims.exampleGrow) 0 N 0 ω a‖ /
          tailT (Gauss.Dims.growW N) ((Gauss.band Gauss.Dims.exampleGrow).ell N 0)
            (etaT 0 0) 60 (zdist (Gauss.Dims.growL N) (a 0 - a 1)))
        (Finset.mem_univ a)
      calc
        (0 : ℝ) = ‖Step2.lk (Gauss.sample Gauss.Dims.exampleGrow) 0 N 0 ω a‖ /
            tailT (Gauss.Dims.growW N) ((Gauss.band Gauss.Dims.exampleGrow).ell N 0)
              (etaT 0 0) 60 (zdist (Gauss.Dims.growL N) (a 0 - a 1)) := by
                simp [hlk a]
        _ ≤ _ := hle
  have hη : etaT 0 0 ≠ 0 := (Step2.etaT_pos' (by norm_num) (by norm_num)).ne'
  simp [J, Step2Moment.jSnorm, Step2Moment.ratR, hj, hη]

#print axioms J_zero

private theorem h_eq (N : ℕ) (hN : 1 ≤ N) :
    h N = ((N : ℝ) ^ (248 : ℕ))⁻¹ := by
  simp [h, mesh, hN]

private theorem h_mem (N : ℕ) (hN : 2 ≤ N) : h N ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  rw [h_eq N (by omega)]
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (2 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
    calc (2 : ℝ) ≤ (N : ℝ) := hNr
      _ ≤ (N : ℝ) ^ (248 : ℕ) := by
        calc (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := by simp
          _ ≤ (N : ℝ) ^ (248 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
  constructor
  · positivity
  · simpa [one_div] using
      (inv_le_inv₀ (show (0 : ℝ) < (N : ℝ) ^ 248 by linarith)
        (show (0 : ℝ) < 2 by norm_num)).2 hp

private theorem modulus_at_h :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Gauss.Ω Gauss.Dims.exampleGrow,
      ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ) →
      |J N (h N) ω - J N 0 ω| ≤
        (N : ℝ) ^ (122 : ℝ) * |h N - 0| ^ ((1 : ℝ) / 2) := by
  have hm := APrimeSlotFields.eventually_modulus_jSnorm_event Gauss.Dims.exampleGrow
    (E := 0) (D := 60) (t₀ := 1 / 2)
    (s := fun _ => 0) (t := fun _ => 1 / 2)
    (Good := fun N => {ω : Gauss.Ω Gauss.Dims.exampleGrow |
      ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ)})
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => subset_rfl)
  filter_upwards [hm, eventually_ge_atTop 2] with N hmN hN ω hω
  simpa only [J, show (2 : ℝ) + 2 * 60 = 122 by norm_num] using
    hmN ω hω (h N) (h_mem N hN) 0 (by constructor <;> norm_num)

#print axioms modulus_at_h

private theorem modulus_scale (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (122 : ℝ) * |h N - 0| ^ ((1 : ℝ) / 2) =
      ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnz : (N : ℝ) ≠ 0 := hpos.ne'
  have hsqrt : (h N) ^ ((1 : ℝ) / 2) = ((N : ℝ) ^ (124 : ℕ))⁻¹ := by
    rw [← Real.sqrt_eq_rpow, h_eq N hN]
    have he : (N : ℝ) ^ (248 : ℕ) = ((N : ℝ) ^ (124 : ℕ)) ^ (2 : ℕ) := by
      rw [← pow_mul]
    rw [he, Real.sqrt_inv, Real.sqrt_sq (by positivity)]
  have hh0 : 0 ≤ h N := by rw [h_eq N hN]; positivity
  simp only [sub_zero, abs_of_nonneg hh0, hsqrt]
  rw [Real.rpow_ofNat (N : ℝ) 122]
  have he : (N : ℝ) ^ (124 : ℕ) = (N : ℝ) ^ (122 : ℕ) * (N : ℝ) ^ (2 : ℕ) := by
    rw [← pow_add]
  rw [he]
  field_simp

theorem eventually_norm_J_h_abs :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Gauss.Ω Gauss.Dims.exampleGrow,
      ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ) →
      |J N (h N) ω - 1| ≤ ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
  filter_upwards [modulus_at_h, eventually_ge_atTop 2] with N hm hN ω hω
  simpa only [J_zero, modulus_scale N (by omega)] using hm ω hω

#print axioms eventually_norm_J_h_abs

theorem eventually_norm_J_h_le :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Gauss.Ω Gauss.Dims.exampleGrow,
      ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ) →
      J N (h N) ω ≤ 1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
  filter_upwards [modulus_at_h, eventually_ge_atTop 2] with N hm hN ω hω
  have hs := hm ω hω
  rw [modulus_scale N (by omega), J_zero] at hs
  exact le_trans (le_add_of_sub_left_le (le_abs_self _ |>.trans hs)) le_rfl

#print axioms eventually_norm_J_h_le

/-- The two actual hard values in the first active prefix. -/
def F₂ (δ : ℝ) (N : ℕ) (ω : Gauss.Ω Gauss.Dims.exampleGrow) : Prop :=
  J N 0 ω ≤ (N : ℝ) ^ δ ∧ J N (h N) ω ≤ (N : ℝ) ^ δ

theorem eventually_norm_F₂ (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Gauss.Ω Gauss.Dims.exampleGrow,
      ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ) → F₂ δ N ω := by
  filter_upwards [eventually_norm_J_h_le, eventually_ge_atTop 1,
    eventually_le_rpow 2 hδ] with N hJ hN hpow ω hω
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hinv : ((N : ℝ) ^ (2 : ℕ))⁻¹ ≤ 1 :=
    (inv_le_one₀ (pow_pos (by linarith) _)).2 (one_le_pow₀ hn)
  constructor
  · rw [J_zero]
    linarith
  · exact (hJ ω hω).trans (by linarith)

#print axioms eventually_norm_F₂

private theorem eventually_firstCellT_half {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, Gauss.firstCellT τ' N = 1 / 2 := by
  have hWt : Tendsto (fun N : ℕ => ((Gauss.Dims.exampleGrow.W N : ℝ)) ^ (-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W (Gauss.band Gauss.Dims.exampleGrow))
  filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hW
  change gridT ((Gauss.band Gauss.Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Gauss.Dims.growW N : ℝ) ^ (-τ') < 1 / 2 at hW
  linarith

private theorem eventually_active_two {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ CutHypTheta.cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ') mesh N := by
  filter_upwards [eventually_firstCellT_half hτ', eventually_ge_atTop 2] with N ht hN
  have hs : Gauss.firstCellS τ' N = 0 := by
    change gridT ((Gauss.band Gauss.Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow2 : (4 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hpow : (4 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) :=
    hpow2.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  unfold CutHypTheta.cutNetTop
  rw [hs, ht]
  apply Nat.le_floor
  simp only [sub_zero, mesh]
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ N)]
  nlinarith

#print axioms eventually_active_two

/-- The actual Step-1 hypothesis at a positive-duration first cell. -/
theorem firstCell_step1_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      Step1.Hyp (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') := by
  obtain ⟨τ', hτ', h1, _⟩ := Gauss.firstCell_step1_and_localLaw_same_parameter
  exact ⟨τ', hτ', h1⟩

#print axioms firstCell_step1_witness

private theorem eventually_calibrated_two :
    ∀ᶠ N : ℕ in atTop,
      (((2 * Fintype.card (LoopArg (Dims.exampleGrow.L N) 2) : ℕ) : ℝ) ^
        ((1 : ℝ) / (2 * (N : ℝ)))) ≤ Real.exp 1 := by
  filter_upwards [eventually_ge_atTop 81] with N hN
  have hNr : (81 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : (1 : ℝ) ≤ Dims.growL N := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) (Dims.three_le_growL N))
  have hL4 : (Dims.growL N : ℝ) ^ (4 : ℕ) ≤ N := by
    exact_mod_cast Dims.growL_pow_le N hN
  have hL2 : (Dims.growL N : ℝ) ^ (2 : ℕ) ≤ N :=
    (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 4)).trans hL4
  have hL3 := Dims.three_le_growL N
  haveI : NeZero (Dims.growL N) := ⟨by omega⟩
  have hcard : Fintype.card (LoopArg (Dims.exampleGrow.L N) 2) =
      (Dims.growL N) ^ (2 : ℕ) := by
    change (Finset.univ : Finset (LoopArg (Dims.growL N) 2)).card = _
    exact Gauss.card_loopArg_two
  have hc0 : (0 : ℝ) < ((2 * Fintype.card (LoopArg (Dims.exampleGrow.L N) 2) : ℕ) : ℝ) := by
    rw [hcard]
    positivity
  have hc : ((2 * Fintype.card (LoopArg (Dims.exampleGrow.L N) 2) : ℕ) : ℝ) ≤
      (N : ℝ) ^ (2 : ℝ) := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Real.rpow_ofNat]
    nlinarith
  have hq : (2 : ℝ) * Real.log N ≤ 2 * (N : ℝ) := by
    have := Real.log_le_self (show (0 : ℝ) ≤ N by positivity)
    linarith
  exact Step2Bootstrap.rpow_card_le_exp_one hc0 (by omega : 2 ≤ N)
    hc (by norm_num) hq

#print axioms eventually_calibrated_two

private theorem firstCellS_eq_zero (τ' : ℝ) :
    firstCellS τ' = fun _ => 0 := by
  funext N
  change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 = 0
  exact gridT_zero (by norm_num)

private theorem cutNetPt_one (N : ℕ) :
    cutNetPt (fun _ => (0 : ℝ)) mesh N 1 = h N := by
  simp [CutHypTheta.cutNetPt, h]

theorem eventually_active_weight_two_one {τ' δ : ℝ} (hτ' : 0 < τ')
    (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω Dims.exampleGrow,
      ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ) → ∀ p : ℕ,
        APrimeSmoothWeightActual.weight Dims.exampleGrow 0 60 δ
          (firstCellS τ') (firstCellT τ') mesh 2 p N 2 N ω = 1 := by
  filter_upwards [eventually_active_two hτ', eventually_calibrated_two,
    eventually_norm_J_h_le, eventually_ge_atTop 81] with N hk hcal hJh hN ω hω p
  have hNr : (81 : ℝ) ≤ N := by exact_mod_cast hN
  have hmesh : 0 < mesh N := by unfold mesh; positivity
  have ht : firstCellT τ' N < 1 :=
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hsfun := firstCellS_eq_zero τ'
  have hst : (0 : ℝ) ≤ firstCellT τ' N := by
    have hW : (1 : ℝ) ≤ (band Dims.exampleGrow).W N := by
      exact_mod_cast (band Dims.exampleGrow).one_le_W N
    change 0 ≤ gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1
    rw [← gridT_zero (W := ((band Dims.exampleGrow).W N : ℝ))
      (τ' := τ') (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact gridT_mono hW hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  have hJ : ∀ j < 2, Step2Moment.jSnorm (sample Dims.exampleGrow) 0 60
      (fun _ => 0) N (cutNetPt (fun _ => 0) mesh N j) ω ≤
      1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
    intro j hj
    interval_cases j
    · have hp : (0 : ℝ) ≤ ((N : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
      simp only [CutHypTheta.cutNetPt, Nat.cast_zero, zero_div, add_zero]
      change J N 0 ω ≤ _
      rw [J_zero]
      linarith
    · simpa only [cutNetPt_one, J] using hJh ω hω
  have hB0 : (0 : ℝ) ≤ 1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
  have hS := APrimeSmoothWeightActual.prefixSample_le_of_jSnorm_bound
    Dims.exampleGrow (E := 0) (D := 60)
    (B := 1 + ((N : ℝ) ^ (2 : ℕ))⁻¹)
    (s := fun _ => 0) (t := firstCellT τ') (mesh := mesh)
    (N := N) (k := 2) (m := N) (by norm_num) hst ht hmesh
    (by omega) (by omega) (by simpa only [hsfun] using hk) hB0 ω hJ
  have hinv2 : ((N : ℝ) ^ (2 : ℕ))⁻¹ ≤ 1 :=
    (inv_le_one₀ (pow_pos (by linarith : (0 : ℝ) < N) _)).2
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ N))
  have hinv10 : (N : ℝ) ^ (-(10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1 : ℝ) ≤ N) (by norm_num)
  have hq : (0 : ℝ) ≤
      1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ + (N : ℝ) ^ (-(10 : ℝ)) := by positivity
  have he0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hS3 : APrimeSmoothWeightActual.prefixSample Dims.exampleGrow 0 60
      (fun _ => 0) mesh N 2 N ω ≤ 3 * Real.exp 1 := by
    calc
      _ ≤ Real.exp 1 * (1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ + (N : ℝ) ^ (-(10 : ℝ))) := hS.trans
        (mul_le_mul_of_nonneg_right hcal hq)
      _ ≤ 3 * Real.exp 1 := by nlinarith
  have hnδ : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hΘ : 3 * Real.exp 1 ≤ APrimeSmoothWeightActual.threshold δ N := by
    unfold APrimeSmoothWeightActual.threshold
    nlinarith [sq_nonneg (Real.exp 1 - 1), mul_nonneg (show (0 : ℝ) ≤
      8 * (Real.exp 1) ^ 2 by positivity) (sub_nonneg.mpr hnδ)]
  have hΘpos := APrimeSmoothWeightActual.threshold_pos (δ := δ)
    (N := N) (by omega : 0 < N)
  have hcut : APrimeSmoothWeightActual.cutoff Dims.exampleGrow 0 60 δ
      (fun _ => 0) mesh N 2 N ω = 1 := by
    unfold APrimeSmoothWeightActual.cutoff
    apply Cutoff.cutChi_eq_one
    exact (div_le_one hΘpos).2 (hS3.trans hΘ)
  rw [hsfun]
  unfold APrimeSmoothWeightActual.weight
  simp [hcut]

#print axioms eventually_active_weight_two_one

private theorem highProb_firstCell_good {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    HighProb (P Dims.exampleGrow)
      (goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellDelta) := by
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, hmargin, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := first_cell_polynomial_regime Dims.exampleGrow τ'
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    rw [firstCellS_eq_zero]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
      hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  exact highProb_goodSetFlow_of_localLaw Dims.exampleGrow
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hs0 ht1 hst
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)
    hKbig (fun N => (hΨpos N).le) hΨlowLL hll hmargin

#print axioms highProb_firstCell_good

private def rawLoopEvent (τ' ζ : ℝ) (n N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω | ∀ p : TimeIcc (firstCellS τ') (firstCellT τ') N ×
      LoopData (Dims.exampleGrow.L N) n,
    ‖(sample Dims.exampleGrow).Lval 0 N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ *
        Step1.aprioriRhs (band Dims.exampleGrow) 0
          (firstCellS τ') (firstCellT τ') n N p ω}

private def commonEvent (τ' ζ : ℝ) (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)} ∩
    rawLoopEvent τ' ζ 4 N ∩ rawLoopEvent τ' ζ 6 N ∩
    goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellDelta N

theorem exists_highProb_firstCell_common :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      HighProb (P Dims.exampleGrow) (commonEvent τ' ζ) := by
  obtain ⟨τ', hτ', _, hll, h4, h6⟩ :=
    firstCell_step1_localLaw_raw46_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  have h4p : HighProb (P Dims.exampleGrow) (rawLoopEvent τ' ζ 4) :=
    (show firstCellRawLoopDom τ' 4 from h4).highProb hζ
  have h6p : HighProb (P Dims.exampleGrow) (rawLoopEvent τ' ζ 6) :=
    (show firstCellRawLoopDom τ' 6 from h6).highProb hζ
  exact (((highProb_norm_Xmat_le Dims.exampleGrow).inter h4p).inter h6p).inter
    (highProb_firstCell_good hτ' hll)

theorem exists_nonempty_firstCell_common :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ N : ℕ in atTop, (commonEvent τ' ζ N).Nonempty := by
  obtain ⟨τ', hτ', hp⟩ := exists_highProb_firstCell_common
  exact ⟨τ', hτ', fun ζ hζ =>
    HighProb.nonempty (by simp) (hp ζ hζ)⟩

#print axioms exists_highProb_firstCell_common
#print axioms exists_nonempty_firstCell_common

private theorem rawLoopEvent_isClosed (τ' ζ : ℝ) (n N : ℕ) :
    IsClosed (rawLoopEvent τ' ζ n N) := by
  have heq : rawLoopEvent τ' ζ n N =
      ⋂ p : TimeIcc (firstCellS τ') (firstCellT τ') N ×
        LoopData (Dims.exampleGrow.L N) n,
        {ω : Ω Dims.exampleGrow |
          ‖(sample Dims.exampleGrow).Lval 0 N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ * Step1.aprioriRhs (band Dims.exampleGrow) 0
              (firstCellS τ') (firstCellT τ') n N p ω} := by
    ext ω
    simp [rawLoopEvent]
  rw [heq]
  apply isClosed_iInter
  intro p
  have ht : firstCellT τ' N < 1 :=
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hu : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt ht
  have hcont : Continuous (fun ω : Ω Dims.exampleGrow =>
      ‖(sample Dims.exampleGrow).Lval 0 N p.1 ω p.2.idx‖) := by
    simpa only [sample_Lval] using
      (continuous_gloop_Hflow Dims.exampleGrow N (p.1 : ℝ)
        (zt_im_ne_zero_of_lt_one (by norm_num : |(0 : ℝ)| < 2) hu)
        p.2.idx).norm
  exact isClosed_le hcont (by dsimp [Step1.aprioriRhs]; fun_prop)

#print axioms rawLoopEvent_isClosed

private theorem firstCell_goodSet_isClosed (τ' : ℝ) (N : ℕ) :
    IsClosed (goodSetFlow Dims.exampleGrow 0
      (firstCellS τ') (firstCellT τ') firstCellDelta N) := by
  have heq : goodSetFlow Dims.exampleGrow 0
      (firstCellS τ') (firstCellT τ') firstCellDelta N =
      ⋂ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
        ⋂ x : Dims.exampleGrow.Idx N, ⋂ y : Dims.exampleGrow.Idx N,
          {ω : Ω Dims.exampleGrow |
            ‖green (Hflow Dims.exampleGrow N (u : ℝ) ω) (zt 0 (u : ℝ)) x y -
              (if x = y then mE 0 else 0)‖ ≤ firstCellDelta N} := by
    ext ω
    simp [goodSetFlow, GoodEvent]
  rw [heq]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  have ht : firstCellT τ' N < 1 :=
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hu : (u : ℝ) < 1 := u.2.2.trans_lt ht
  have hmat : Continuous (fun ω : Ω Dims.exampleGrow =>
      green (Hflow Dims.exampleGrow N (u : ℝ) ω) (zt 0 (u : ℝ))) :=
    continuous_green_comp (continuous_Hflow Dims.exampleGrow N (u : ℝ))
      (Hflow_isHermitian Dims.exampleGrow N (u : ℝ))
      (zt_im_ne_zero_of_lt_one (by norm_num : |(0 : ℝ)| < 2) hu)
  exact isClosed_le ((Continuous.matrix_elem hmat x y).sub continuous_const).norm
    continuous_const

theorem commonEvent_measurable (τ' ζ : ℝ) (N : ℕ) :
    MeasurableSet (commonEvent τ' ζ N) := by
  unfold commonEvent
  exact (((measurableSet_normX_le Dims.exampleGrow N).inter
    (rawLoopEvent_isClosed τ' ζ 4 N).measurableSet).inter
    (rawLoopEvent_isClosed τ' ζ 6 N).measurableSet).inter
    (firstCell_goodSet_isClosed τ' N).measurableSet

#print axioms commonEvent_measurable

private noncomputable def sourceC4 (ζ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ζ * (band Dims.exampleGrow).ell N (h N) ^ (3 : ℕ) *
    ((band Dims.exampleGrow).scale 0 N (h N))⁻¹ ^ (3 : ℕ)

private noncomputable def sourceC6 (ζ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ζ * (band Dims.exampleGrow).ell N (h N) ^ (5 : ℕ) *
    ((band Dims.exampleGrow).scale 0 N (h N))⁻¹ ^ (5 : ℕ)

private noncomputable def ellSource (ζ : ℝ) (N : ℕ) : ℝ :=
  (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ))

private theorem source_level_identity {ell A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    2 * (q * ell ^ 5 * (A⁻¹) ^ 5) =
      (ell / (2 * q) ^ (-(1 / 5 : ℝ))) ^ 5 * (((A ^ 2)⁻¹) ^ 2) * A⁻¹ := by
  have hb : 0 < 2 * q := by positivity
  have hr : ((2 * q) ^ (-(1 / 5 : ℝ))) ^ 5 = (2 * q)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hb.le]
    norm_num [Real.rpow_neg_one]
  rw [div_pow, hr]
  field_simp

#print axioms source_level_identity

theorem sourceEvent_of_common {τ' ζ : ℝ}
    {N : ℕ} (hN : 2 ≤ N) (ht : firstCellT τ' N = 1 / 2)
    {ω : Ω Dims.exampleGrow} (hω : ω ∈ commonEvent τ' ζ N) :
    APrimeFullQV.SourceEvent (sample Dims.exampleGrow) 0 N (h N) ω
      (ellSource ζ N) (sourceC4 ζ N) := by
  have hu : h N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
    rw [firstCellS_eq_zero, ht]
    exact h_mem N hN
  let u : TimeIcc (firstCellS τ') (firstCellT τ') N := ⟨h N, hu⟩
  have hℓs : (band Dims.exampleGrow).ell N (firstCellS τ' N) = 1 := by
    rw [firstCellS_eq_zero]
    exact ellHat_zero _ ((band Dims.exampleGrow).three_le_L N)
  rcases hω with ⟨⟨⟨_, h4ev⟩, h6ev⟩, _⟩
  have h4 : ∀ p : LoopData ((band Dims.exampleGrow).L N) 4,
      ‖(sample Dims.exampleGrow).Lval 0 N (h N) ω p.idx‖ ≤ sourceC4 ζ N := by
    intro p
    have hp := h4ev (u, p)
    convert hp using 1 <;> simp [Step1.aprioriRhs, hℓs, sourceC4, u, mul_assoc]
  have h6 : ∀ p : LoopData ((band Dims.exampleGrow).L N) 6,
      ‖(sample Dims.exampleGrow).Lval 0 N (h N) ω p.idx‖ ≤ sourceC6 ζ N := by
    intro p
    have hp := h6ev (u, p)
    convert hp using 1 <;> simp [Step1.aprioriRhs, hℓs, sourceC6, u, mul_assoc]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hq : (0 : ℝ) < (N : ℝ) ^ ζ := Real.rpow_pos_of_pos hN0 _
  have hA : 0 < (band Dims.exampleGrow).scale 0 N (h N) :=
    (band Dims.exampleGrow).scale_pos' (by norm_num) N (h_mem N hN).1
      ((h_mem N hN).2.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have hlevel : 2 * sourceC6 ζ N ≤
      ((band Dims.exampleGrow).ell N (h N) / ellSource ζ N) ^ 5 *
        (((((band Dims.exampleGrow).W N : ℝ) *
          (band Dims.exampleGrow).ell N (h N) * etaT 0 (h N)) ^ 2)⁻¹) ^ 2 *
        (((band Dims.exampleGrow).W N : ℝ) *
          (band Dims.exampleGrow).ell N (h N) * etaT 0 (h N))⁻¹ := by
    unfold sourceC6 ellSource
    exact le_of_eq (by simpa only [Band.scale] using
      (source_level_identity (ell := (band Dims.exampleGrow).ell N (h N))
        (A := (band Dims.exampleGrow).scale 0 N (h N))
        (q := (N : ℝ) ^ ζ) hA hq))
  exact APrimeFullQV.sourceEvent_of_step1 (sample Dims.exampleGrow) 0 N
    (h N) ω h4 h6 hlevel

#print axioms sourceEvent_of_common

/-- One actual Gaussian sample carries the positive first-prefix cutoff and
the Step-1 length-four/six QV source at the same positive time. -/
theorem exists_positive_time_firstCell_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Ω Dims.exampleGrow,
        ω ∈ commonEvent τ' ζ N ∧
        MeasurableSet (commonEvent τ' ζ N) ∧
        0 < h N ∧ h N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) ∧
        ellSource ζ N < 1 ∧
        (∀ p : ℕ, APrimeSmoothWeightActual.weight Dims.exampleGrow 0 60 δ
          (firstCellS τ') (firstCellT τ') mesh 2 p N 2 N ω = 1) ∧
        APrimeFullQV.SourceEvent (sample Dims.exampleGrow) 0 N (h N) ω
          (ellSource ζ N) (sourceC4 ζ N) := by
  obtain ⟨τ', hτ', hp⟩ := exists_highProb_firstCell_common
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ δ hδ
  have hne := HighProb.nonempty (by simp) (hp ζ hζ)
  filter_upwards [hne, eventually_active_weight_two_one hτ' hδ,
    eventually_firstCellT_half hτ', eventually_ge_atTop 81] with
    N hneN hweight ht hN
  obtain ⟨ω, hω⟩ := hneN
  have hnorm : ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ) := hω.1.1.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hhpos : 0 < h N := by
    rw [h_eq N (by omega)]
    positivity
  have hhmem : h N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
    rw [firstCellS_eq_zero, ht]
    exact h_mem N (by omega)
  have hbase : (1 : ℝ) < 2 * (N : ℝ) ^ ζ := by
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hNr hζ.le
    linarith
  have hell : ellSource ζ N < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hbase (by norm_num)
  exact ⟨ω, hω, commonEvent_measurable τ' ζ N, hhpos, hhmem, hell,
    hweight ω hnorm, sourceEvent_of_common (by omega) ht hω⟩

#print axioms exists_positive_time_firstCell_witness

end RBM.APrimeFirstCellCommon
