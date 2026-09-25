/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeFirstCellCommon
import RBM1D.Gauss.APrimeFirstCellLoopCap
import RBM1D.Gauss.APrimeSlotFields

/-!
# T1101: the norm event excludes every polynomially early prefix

At the literal D = 60 target mesh, the modulus exponent 2 + 2D = 122
combined with mesh = N^(4D+18) = N^258 controls all prefix times
j < k ≤ N^10 by N^-2 relative to the exact initial value jSnorm(0)=1.
The canonical smooth prefix is therefore uniformly below its strict transition
threshold on the fixed norm event. This is an internal transition obstruction,
not a statement about the stopped process in (5.43)–(5.44).
-/

namespace RBM.APrimeGeneralMovingEarlyPrefixTransitionExclusion

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh 60

private theorem early_time_sqrt_bound {N j : ℕ} (hN : 1 ≤ N)
    (hj : j ≤ N ^ 10) :
    |(j : ℝ) / (N : ℝ) ^ (258 : ℕ)| ^ ((1 : ℝ) / 2) ≤
      ((N : ℝ) ^ (124 : ℕ))⁻¹ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow258 : (N : ℝ) ^ (258 : ℕ) =
      (N : ℝ) ^ (248 : ℕ) * (N : ℝ) ^ (10 : ℕ) := by
    rw [← pow_add]
  have hpow248 : (N : ℝ) ^ (248 : ℕ) =
      ((N : ℝ) ^ (124 : ℕ)) ^ 2 := by
    rw [← pow_mul]
  have hjR : (j : ℝ) ≤ (N : ℝ) ^ (10 : ℕ) := by
    exact_mod_cast hj
  have hden : 0 < (N : ℝ) ^ (258 : ℕ) := pow_pos hNr _
  have htime0 : 0 ≤ (j : ℝ) / (N : ℝ) ^ (258 : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have htime : (j : ℝ) / (N : ℝ) ^ (258 : ℕ) ≤
      ((N : ℝ) ^ (124 : ℕ))⁻¹ ^ 2 := by
    rw [hpow258]
    calc
      (j : ℝ) / ((N : ℝ) ^ (248 : ℕ) * (N : ℝ) ^ (10 : ℕ)) ≤
          (N : ℝ) ^ (10 : ℕ) /
            ((N : ℝ) ^ (248 : ℕ) * (N : ℝ) ^ (10 : ℕ)) :=
        div_le_div_of_nonneg_right hjR (by positivity)
      _ = ((N : ℝ) ^ (124 : ℕ))⁻¹ ^ 2 := by
        rw [hpow248]
        field_simp [ne_of_gt hNr]
  have hsqrt : Real.sqrt ((j : ℝ) / (N : ℝ) ^ (258 : ℕ)) ≤
      ((N : ℝ) ^ (124 : ℕ))⁻¹ :=
    (Real.sqrt_le_iff).2 ⟨inv_nonneg.mpr (pow_pos hNr _).le, htime⟩
  rw [abs_of_nonneg htime0, ← Real.sqrt_eq_rpow]
  exact hsqrt

private theorem firstCellS_zero (τ' : ℝ) (N : ℕ) :
    Gauss.firstCellS τ' N = 0 := by
  unfold Gauss.firstCellS
  exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem firstCellT_nonneg {τ' : ℝ} (hτ' : 0 < τ') (N : ℕ) :
    0 ≤ Gauss.firstCellT τ' N := by
  have hW : (1 : ℝ) ≤ ((Gauss.band d).W N : ℝ) :=
    (Gauss.band d).one_le_W N
  have hmono := gridT_mono hW hτ'.le (1 / 2 : ℝ)
  have hst : Gauss.firstCellS τ' N ≤ Gauss.firstCellT τ' N := by
    simpa [Gauss.firstCellS, Gauss.firstCellT] using
      hmono (show 0 ≤ 1 by omega)
  simpa [firstCellS_zero] using hst

private theorem firstCellT_le_half (τ' : ℝ) (N : ℕ) :
    Gauss.firstCellT τ' N ≤ 1 / 2 := by
  unfold Gauss.firstCellT
  exact gridT_le (1 / 2 : ℝ) 1

/-- On the literal T995 schedule, every target-mesh prefix of length at most
N^10 lies strictly below the transition band for every sample in the fixed
matrix-norm event. The first conjunct gives the exact uniform ratio bound;
the final conjunct states the literal transition exclusion. -/
theorem eventually_early_prefix_transition_exclusion
    {τ' c δ : ℝ} (hτ' : 0 < τ') (hc : 0 < c) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ,
        k ≤ CutHypTheta.cutNetTop (Gauss.firstCellS τ')
          (Gauss.firstCellT τ') mesh N →
        k ≤ N ^ 10 →
        ∀ ω : Gauss.Ω d,
          ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) →
          (APrimeSmoothWeightActual.prefixSample d 0 60
              (Gauss.firstCellS τ') mesh N k
              (APrimeSmoothWeightActual.canonicalM d (Gauss.firstCellS τ')
                (Gauss.firstCellT τ') mesh N) ω /
            APrimeSmoothWeightActual.threshold
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N ≤
              3 / (8 * Real.exp 1) ∧
            APrimeSmoothWeightActual.prefixSample d 0 60
              (Gauss.firstCellS τ') mesh N k
              (APrimeSmoothWeightActual.canonicalM d (Gauss.firstCellS τ')
                (Gauss.firstCellT τ') mesh N) ω /
            APrimeSmoothWeightActual.threshold
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N < 1) ∧
          ω ∉ APrimeCrossJointSplit.transition d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (Gauss.firstCellS τ') mesh N k
            (APrimeSmoothWeightActual.canonicalM d (Gauss.firstCellS τ')
              (Gauss.firstCellT τ') mesh N) := by
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hsmall
  have hδw : 0 < APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := hroom.1
  have hmod := APrimeSlotFields.eventually_modulus_jSnorm_event d
    (E := 0) (D := 60) (t₀ := 1 / 2)
    (s := Gauss.firstCellS τ') (t := Gauss.firstCellT τ')
    (Good := fun N => {ω : Gauss.Ω d | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)})
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun N => by
      rw [firstCellS_zero])
    (fun N => firstCellT_le_half τ' N)
    (fun _ _ hω => hω)
  filter_upwards [hmod, APrimeGeneralMovingMesh.eventually_targetMesh_eq (60 : ℝ),
      Filter.eventually_ge_atTop 1] with N hmodN hmeshN hN
  intro k hkTop hkSmall ω hω
  let m := APrimeSmoothWeightActual.canonicalM d (Gauss.firstCellS τ')
    (Gauss.firstCellT τ') mesh N
  have hm : 1 ≤ m := by
    dsimp [m]
    exact APrimeSmoothWeightActual.canonicalM_pos d (Gauss.firstCellS τ')
      (Gauss.firstCellT τ') mesh N
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hs : Gauss.firstCellS τ' N = 0 := firstCellS_zero τ' N
  have hsfun : Gauss.firstCellS τ' = fun _ => 0 := by
    funext n
    exact firstCellS_zero τ' n
  have ht0 : 0 ≤ Gauss.firstCellT τ' N := firstCellT_nonneg hτ' N
  have hst : Gauss.firstCellS τ' N ≤ Gauss.firstCellT τ' N := by
    rw [hs]
    exact ht0
  have ht1 : Gauss.firstCellT τ' N < 1 :=
    (firstCellT_le_half τ' N).trans_lt (by norm_num)
  have hmeshPos : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (Gauss.firstCellS τ' N)
      (Gauss.firstCellT τ' N) := by
    rw [hs]
    exact ⟨le_rfl, ht0⟩
  have hprefixBound :
      APrimeSmoothWeightActual.prefixSample d 0 60 (Gauss.firstCellS τ')
          mesh N k m ω ≤ 3 * Real.exp 1 := by
    by_cases hk0 : k = 0
    · subst k
      rw [APrimeSmoothWeightActual.prefixSample_zero d 0 60
        (Gauss.firstCellS τ') mesh N m hm ω]
      positivity
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hJzero : Step2Moment.jSnorm (Gauss.sample d) 0 60
          (Gauss.firstCellS τ') N 0 ω = 1 := by
        rw [hsfun]
        simpa only [Step2Moment.jSnorm, Step2Moment.ratR, etaT, mE_zero,
          Complex.I_im, mul_one, sub_zero, div_one, one_pow] using
          APrimeFirstCellLoopCap.loopJ_zero N ω
      have hJbound : ∀ j < k,
          Step2Moment.jSnorm (Gauss.sample d) 0 60
            (Gauss.firstCellS τ') N
            (CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j) ω ≤ 2 := by
        intro j hj
        have hjTop : j ≤ CutHypTheta.cutNetTop (Gauss.firstCellS τ')
            (Gauss.firstCellT τ') mesh N := by omega
        have hnet := CutHypTheta.cutNetPt_mem_netFinset hjTop
        have hu := MomentDuhamelCut.netFinset_subset_Icc hst hmeshPos _ hnet
        have hu0 : CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j ∈
            Set.Icc (Gauss.firstCellS τ' N) (Gauss.firstCellT τ' N) := hu
        have hjN : j ≤ N ^ 10 := (Nat.le_of_lt hj).trans hkSmall
        have hmeshNat : mesh N = (N : ℝ) ^ (258 : ℕ) := by
          change APrimeGeneralMovingMesh.targetMesh 60 N =
            (N : ℝ) ^ (258 : ℕ)
          rw [hmeshN]
          norm_num
        have htimeEq : CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j =
            (j : ℝ) / (N : ℝ) ^ (258 : ℕ) := by
          simp [CutHypTheta.cutNetPt, hs, hmeshNat]
        have hmodVal := hmodN ω hω
          (CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j) hu0
          0 hzeroMem
        have hmodVal' :
            |Step2Moment.jSnorm (Gauss.sample d) 0 60 (Gauss.firstCellS τ') N
                (CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j) ω -
              Step2Moment.jSnorm (Gauss.sample d) 0 60 (Gauss.firstCellS τ') N 0 ω|
              ≤ (N : ℝ) ^ (122 : ℝ) *
                |(j : ℝ) / (N : ℝ) ^ (258 : ℕ)| ^ ((1 : ℝ) / 2) := by
          simpa [htimeEq, show (2 : ℝ) + 2 * 60 = 122 by norm_num]
            using hmodVal
        have hsmallModulus :
            (N : ℝ) ^ (122 : ℝ) *
                |(j : ℝ) / (N : ℝ) ^ (258 : ℕ)| ^ ((1 : ℝ) / 2) ≤ 1 := by
          calc
            _ ≤ (N : ℝ) ^ (122 : ℝ) * ((N : ℝ) ^ (124 : ℕ))⁻¹ :=
              mul_le_mul_of_nonneg_left
                (early_time_sqrt_bound hN hjN) (by positivity)
            _ = ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
              rw [Real.rpow_ofNat (N : ℝ) 122]
              have hfactor : (N : ℝ) ^ (124 : ℕ) =
                  (N : ℝ) ^ (122 : ℕ) * (N : ℝ) ^ (2 : ℕ) := by
                rw [← pow_add]
              rw [hfactor]
              field_simp
            _ ≤ 1 := by
              apply (inv_le_one₀ (pow_pos hNpos _)).2
              exact one_le_pow₀ hNreal
        have hdiff : |Step2Moment.jSnorm (Gauss.sample d) 0 60
            (Gauss.firstCellS τ') N
            (CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j) ω - 1| ≤ 1 := by
          calc
            _ = |Step2Moment.jSnorm (Gauss.sample d) 0 60
                  (Gauss.firstCellS τ') N
                  (CutHypTheta.cutNetPt (Gauss.firstCellS τ') mesh N j) ω -
                Step2Moment.jSnorm (Gauss.sample d) 0 60
                  (Gauss.firstCellS τ') N 0 ω| := by rw [hJzero]
            _ ≤ 1 := hmodVal'.trans hsmallModulus
        have hupper := (abs_le.mp hdiff).2
        linarith
      have hsample := APrimeSmoothWeightActual.prefixSample_le_of_jSnorm_bound d
        (E := 0) (D := 60) (B := 2) (s := Gauss.firstCellS τ')
        (t := Gauss.firstCellT τ') (mesh := mesh) (N := N) (k := k) (m := m)
        (by norm_num) hst ht1 hmeshPos (by omega) hm hkTop (by norm_num) ω hJbound
      have hcal := APrimeSmoothWeightActual.canonicalM_calibration d
        (Gauss.firstCellS τ') (Gauss.firstCellT τ') mesh N k hkTop
      have hn10 : (N : ℝ) ^ (-(10 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hNreal (by norm_num)
      have hsum : 2 + (N : ℝ) ^ (-(10 : ℝ)) ≤ 3 := by linarith
      calc
        _ ≤ (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
              ((1 : ℝ) / (2 * (m : ℝ)))) *
              (2 + (N : ℝ) ^ (-(10 : ℝ))) := hsample
        _ ≤ Real.exp 1 * (2 + (N : ℝ) ^ (-(10 : ℝ))) :=
          mul_le_mul_of_nonneg_right hcal (by positivity)
        _ ≤ 3 * Real.exp 1 :=
          (mul_le_mul_of_nonneg_left hsum (Real.exp_pos 1).le).trans_eq
            (by ring)
  have hthresholdPos : 0 < APrimeSmoothWeightActual.threshold
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N :=
    APrimeSmoothWeightActual.threshold_pos (by omega)
  have hthresholdLower : 8 * (Real.exp 1) ^ 2 ≤
      APrimeSmoothWeightActual.threshold
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N := by
    unfold APrimeSmoothWeightActual.threshold
    have hNp : (1 : ℝ) ≤ (N : ℝ) ^
        (2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) :=
      Real.one_le_rpow hNreal (by positivity)
    calc
      8 * (Real.exp 1) ^ 2 = (8 * (Real.exp 1) ^ 2) * 1 := by ring
      _ ≤ (8 * (Real.exp 1) ^ 2) *
          (N : ℝ) ^ (2 * APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) :=
        mul_le_mul_of_nonneg_left hNp
          (by positivity : 0 ≤ 8 * (Real.exp 1) ^ 2)
  have hratio :
      APrimeSmoothWeightActual.prefixSample d 0 60 (Gauss.firstCellS τ')
          mesh N k m ω /
        APrimeSmoothWeightActual.threshold
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N ≤
          3 / (8 * Real.exp 1) := by
    calc
      _ ≤ (3 * Real.exp 1) /
          APrimeSmoothWeightActual.threshold
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N :=
        div_le_div_of_nonneg_right hprefixBound hthresholdPos.le
      _ ≤ (3 * Real.exp 1) / (8 * (Real.exp 1) ^ 2) :=
        (div_le_div_iff₀ hthresholdPos (by positivity)).2
          (mul_le_mul_of_nonneg_left hthresholdLower (by positivity))
      _ = 3 / (8 * Real.exp 1) := by field_simp
  have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hratioLt :
      APrimeSmoothWeightActual.prefixSample d 0 60 (Gauss.firstCellS τ')
          mesh N k m ω /
        APrimeSmoothWeightActual.threshold
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) N < 1 :=
    hratio.trans_lt (by
      apply (div_lt_one (by positivity : 0 < 8 * Real.exp 1)).2
      nlinarith)
  refine ⟨⟨hratio, hratioLt⟩, ?_⟩
  intro htransition
  exact (not_lt_of_ge hratioLt.le) htransition.1

#print axioms eventually_early_prefix_transition_exclusion

end RBM.APrimeGeneralMovingEarlyPrefixTransitionExclusion
