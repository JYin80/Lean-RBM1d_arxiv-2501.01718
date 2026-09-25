/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeSmoothTransitionGradient
import RBM1D.Gauss.APrimeCrossJointSplit

/-!
# T1051: strict smooth-prefix transition on the target mesh

For the T995 loss schedule, the actual scalar-ray endpoint construction still
works on the general-moving target mesh, with the exact canonical moment order.
This gives a sample in the literal strict transition set; no common-event
membership is asserted.
-/

namespace RBM.APrimeGeneralMovingTargetTransitionExists

open Filter Real CutHypTheta

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private abbrev s : ℕ → ℝ := fun _ => 0
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60

private theorem eventually_firstCellT_half {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, Gauss.firstCellT τ N = 1 / 2 := by
  have ht : Tendsto (fun N : ℕ => (Gauss.Dims.exampleGrow.W N : ℝ)^(-τ))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ).comp
      (Step2.tendsto_W (Gauss.band Gauss.Dims.exampleGrow))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hN
  change gridT ((Gauss.band Gauss.Dims.exampleGrow).W N : ℝ) τ (1 / 2) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Gauss.Dims.growW N : ℝ)^(-τ) < 1 / 2 at hN
  linarith

private theorem eventually_large_threshold {δ : ℝ}
    (hδ1 : δ ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      1024 * (Real.exp 1)^2 * (N : ℝ)^(2 *
        APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) <
        (d.W N : ℝ) := by
  have hexp : 0 < (5 / 8 : ℝ) -
      2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    nlinarith
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^((5 / 8 : ℝ) -
      2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  filter_upwards [Gauss.Dims.bandwidth_grow,
    ht.eventually_gt_atTop (1024 * (Real.exp 1)^2),
    eventually_ge_atTop (1 : ℕ)] with N hW hlarge hN
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hW' : (N : ℝ)^(5 / 8 : ℝ) ≤ (d.W N : ℝ) := by
    have he : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
    simpa only [he, d, Gauss.Dims.exampleGrow_W] using hW
  have hmul := mul_lt_mul_of_pos_right hlarge
    (Real.rpow_pos_of_pos hNpos
      (2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ))
  rw [← Real.rpow_add hNpos] at hmul
  have he : (5 / 8 : ℝ) -
      2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ +
      2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ = 5 / 8 := by ring
  rw [he] at hmul
  exact hmul.trans_le hW'

private theorem eventual_mesh_eq (N : ℕ) (hN : 0 < N) :
    mesh N = (N : ℝ)^258 := by
  dsimp [mesh, APrimeGeneralMovingMesh.targetMesh]
  rw [APrimeGeneralMovingMesh.polynomialMesh_eq_of_pos hN]
  norm_num

/-- A concrete nonempty T995 parameter range. -/
theorem explicit_parameter_witness :
    ∃ τ c δ : ℝ, 0 < τ ∧ 0 < c ∧ 0 < δ ∧ δ ≤ min 1 (c / 100) := by
  refine ⟨1, 1, 1 / 200, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/- At the exact T995 target mesh and canonical order, a scalar-ray sample lies
in the literal `APrimeCrossJointSplit.transition` set at the active prefix `k=2`.
The window has positive limiting length, and the strict ratio is for one and the
same sample. -/
set_option maxHeartbeats 1000000 in
-- The actual soft-prefix endpoint theorem expands a large finite supremum.
theorem eventually_exampleGrow_target_transition {τ c δ : ℝ}
    (hτ : 0 < τ) (hc : 0 < c) (hδ : 0 < δ)
    (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      Gauss.firstCellS τ N = 0 ∧
      Gauss.firstCellT τ N = 1 / 2 ∧
      2 ≤ cutNetTop s (Gauss.firstCellT τ) mesh N ∧
      ∃ x ∈ Set.Ioo 0 (2 / Real.sqrt ((mesh N)⁻¹)),
        let ω := APrimeSmoothTransition.scalarSample d x
        ω ∈ APrimeCrossJointSplit.transition d 0 60
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s mesh N 2
          (APrimeSmoothWeightActual.canonicalM d s
            (Gauss.firstCellT τ) mesh N) ∧
        1 < APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N 2
              (APrimeSmoothWeightActual.canonicalM d s
                (Gauss.firstCellT τ) mesh N) ω /
          APrimeSmoothWeightActual.threshold
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N ∧
        APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N 2
              (APrimeSmoothWeightActual.canonicalM d s
                (Gauss.firstCellT τ) mesh N) ω /
      APrimeSmoothWeightActual.threshold
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N < 2 := by
  have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have hrooms := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  have hδweight : 0 < APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := hrooms.1
  filter_upwards [eventually_firstCellT_half hτ,
    eventually_large_threshold hδ1,
    Gauss.Dims.dim_grow, eventually_ge_atTop 81] with N ht hlarge hdim hN81
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmesh : mesh N = (N : ℝ)^258 := eventual_mesh_eq N hNpos
  have hmeshpos : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  have hs : Gauss.firstCellS τ N = 0 := by
    unfold Gauss.firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have ht0 : 0 ≤ Gauss.firstCellT τ N := by rw [ht]; norm_num
  have ht1 : Gauss.firstCellT τ N < 1 := by rw [ht]; norm_num
  have hk : 2 ≤ cutNetTop s (Gauss.firstCellT τ) mesh N := by
    unfold cutNetTop
    rw [ht]
    apply Nat.le_floor
    simp only [s, sub_zero, hmesh]
    have hNpow : (4 : ℝ) ≤ (N : ℝ)^258 := by
      calc
        (4 : ℝ) ≤ N := by
          have hN4 : (4 : ℕ) ≤ N := by omega
          exact_mod_cast hN4
        _ ≤ (N : ℝ)^258 := by
          simpa only [pow_one] using pow_le_pow_right₀ hNR1 (by norm_num : 1 ≤ 258)
    linarith
  let m := APrimeSmoothWeightActual.canonicalM d s (Gauss.firstCellT τ) mesh N
  have hm : 1 ≤ m := by
    dsimp [m]
    exact APrimeSmoothWeightActual.canonicalM_pos d s (Gauss.firstCellT τ) mesh N
  have hcard :
      (((2 * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) ≤ Real.exp 1 := by
    simpa only [m] using
      APrimeSmoothWeightActual.canonicalM_calibration d s
        (Gauss.firstCellT τ) mesh N 2 hk
  have hWle : (d.W N : ℝ) ≤ N := by
    have hprod : (d.W N : ℝ) * (Gauss.Dims.growL N : ℝ) ≤ N := by
      exact_mod_cast hdim.1
    have hL1 : (1 : ℝ) ≤ (Gauss.Dims.growL N : ℝ) := by
      exact_mod_cast
        (le_trans (by norm_num : 1 ≤ 3) (Gauss.Dims.three_le_growL N))
    nlinarith [mul_nonneg (Nat.cast_nonneg (d.W N)) (sub_nonneg.mpr hL1)]
  have hN10 : (10 : ℝ) ≤ N := by
    have hN10Nat : (10 : ℕ) ≤ N := by omega
    exact_mod_cast hN10Nat
  have hWpow : (d.W N : ℝ)^(59 : ℕ) ≤ (N : ℝ)^59 :=
    pow_le_pow_left₀ (by positivity) hWle 59
  have hnum : 10 * (d.W N : ℝ)^(59 : ℕ) ≤ (N : ℝ)^258 := by
    calc
      _ ≤ 10 * (N : ℝ)^59 := mul_le_mul_of_nonneg_left hWpow (by norm_num)
      _ ≤ (N : ℝ) * (N : ℝ)^59 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (N : ℝ)^60 := by ring
      _ ≤ (N : ℝ)^258 := by
        exact pow_le_pow_right₀ hNR1 (by norm_num)
  have hsmall :
      10 * (mesh N)⁻¹ * (d.W N : ℝ)^((60 : ℝ) - 1) ≤ 1 := by
    rw [hmesh, show (60 : ℝ) - 1 = 59 by norm_num, Real.rpow_ofNat]
    have hNpowpos : 0 < (N : ℝ)^258 := by positivity
    rw [inv_eq_one_div]
    calc
      10 * (1 / (N : ℝ)^258) * (d.W N : ℝ)^59 =
          (10 * (d.W N : ℝ)^59) / (N : ℝ)^258 := by ring
      _ ≤ 1 := (div_le_one hNpowpos).2 hnum
  have hends := APrimeSmoothTransition.finite_transition d
    (N0 := 2) (p := 1) (m := m)
    hN2 (by omega) (by omega) hm hδweight (by norm_num)
    ht0 ht1 hmeshpos hk hsmall hcard hlarge
  have hhh : (mesh N)⁻¹ < 1 := by
    rw [hmesh]
    have hNpow : (1 : ℝ) < (N : ℝ)^258 := by
      calc
        (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
        _ ≤ (N : ℝ)^258 := by
          simpa only [pow_one] using pow_le_pow_right₀ hNR1 (by norm_num : 1 ≤ 258)
    exact (inv_lt_one₀ (by positivity)).2 hNpow
  obtain ⟨x, hx, hw0, hw1, _, _⟩ :=
    APrimeSmoothTransitionGradient.transition_of_endpoints d
      (N0 := 2) (p := 1) (m := m) hNpos hm hmeshpos hhh hends
  let ω := APrimeSmoothTransition.scalarSample d x
  let q := APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N 2 m ω /
    APrimeSmoothWeightActual.threshold
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N
  let χ := Cutoff.cutChi q
  have hweight :
      APrimeSmoothWeightActual.weight d 0 60
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        s (Gauss.firstCellT τ) mesh 2 1 N 2 m ω =
        χ^2 := by
    change APrimeSmoothTransitionGradient.rayWeight d 60
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (Gauss.firstCellT τ) mesh 2 1 N m x = _
    rw [APrimeSmoothTransitionGradient.rayWeight]
    unfold APrimeSmoothWeightActual.weight
    rw [if_pos ⟨hk, by omega⟩]
    rfl
  have hchi0 : 0 < χ := by
    have hpow : 0 < χ^2 := by
      rw [← hweight]
      exact hw0
    have hnonneg : 0 ≤ χ := Cutoff.cutChi_nonneg q
    nlinarith
  have hchi1 : χ < 1 := by
    have hpow : χ^2 < 1 := by
      rw [← hweight]
      exact hw1
    have hnonneg : 0 ≤ χ := Cutoff.cutChi_nonneg q
    nlinarith
  have hratio_lo : 1 < q := by
    by_contra h
    have hle : q ≤ 1 := le_of_not_gt h
    change Cutoff.cutChi q < 1 at hchi1
    rw [Cutoff.cutChi_eq_one hle] at hchi1
    linarith
  have hratio_hi : q < 2 := by
    by_contra h
    have hle : 2 ≤ q := le_of_not_gt h
    change Cutoff.cutChi q > 0 at hchi0
    rw [Cutoff.cutChi_eq_zero hle] at hchi0
    linarith
  have hratio_lo' : 1 <
      APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N 2 m ω /
        APrimeSmoothWeightActual.threshold
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N := by
    simpa [q] using hratio_lo
  have hratio_hi' :
      APrimeSmoothWeightActual.prefixSample d 0 60 s mesh N 2 m ω /
        APrimeSmoothWeightActual.threshold
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N < 2 := by
    simpa [q] using hratio_hi
  refine ⟨hs, ht, hk, x, hx, ?_, hratio_lo', hratio_hi'⟩
  change (1 < q ∧ q < 2)
  exact ⟨hratio_lo, hratio_hi⟩

#print axioms explicit_parameter_witness
#print axioms eventually_exampleGrow_target_transition

end RBM.APrimeGeneralMovingTargetTransitionExists
