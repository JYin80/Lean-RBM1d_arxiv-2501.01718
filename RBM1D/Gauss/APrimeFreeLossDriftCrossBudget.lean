/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossDriftAssembly
import RBM1D.Gauss.APrimeFreeLossCrossAssembly
import RBM1D.Gauss.APrimeFreeLossRootInterface

/-!
# T1327: assemble the corrected-loss actual drift and full cross budget

The T1313 actual-drift integral and T1315 full positive-time cross integral
have the same corrected actual weight loss. T1325 supplies the complete
absorbed-root input to T1315 with a fixed positive constant. This file adds
the two integral estimates, retaining the full cross budget and its
integrability, in the exact conditional hbudget form consumed by T1319.
-/

namespace RBM.APrimeFreeLossDriftCrossBudget

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- A fixed coefficient for the sum of the T1313 and T1315 integral bounds. -/
noncomputable def combinedBudgetConst (E : ℝ) (p : ℕ) (C_A : ℝ) : ℝ :=
  2 * (|APrimeFreeLossDriftAssembly.assemblyConstant E| +
    APrimeFreeLossCrossAssembly.fullCrossBudgetConst E p C_A)

theorem combinedBudgetConst_pos {E C_A : ℝ} (hE : |E| < 2)
    (hCA : 0 < C_A) (p : ℕ) (hp : 1 ≤ p) :
    0 < combinedBudgetConst E p C_A := by
  have hcross :=
    APrimeFreeLossCrossAssembly.fullCrossBudgetConst_pos hE hCA p hp
  unfold combinedBudgetConst
  positivity

/-- Assemble the actual-drift and complete positive-time cross integrals
under the T1315 absorbed-root input. The constant is fixed before the
eventual index. -/
theorem eventually_actual_drift_plus_full_cross_hbudget_of_absorbed_root
    {E D c lambda C_A : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : ℝ) (c / 10000))
    (hCA : 0 < C_A) (p : ℕ) (hp : 1 ≤ p)
    (hAbsorbed : ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      let v := cutNetPt s (mesh D) N k
      ∀ u ∈ Icc (s N) v,
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
          (lambda / 1000) N u v D
          (APrimeFreeLossCrossIntegral.profileCap E s (lambda / 1000)
            (2 * lambda) N u) a ≤
        C_A * (N : ℝ)^(2 * (lambda / 1000)) *
          (etaT E (s N))^(-(1 / 2 : ℝ)) *
          Step2Moment.ratR E s N v^(-(2 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, 1 ≤ k →
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      let v := cutNetPt s (mesh D) N k
      let R := Step2Moment.ratR E s N v
      2 * (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a u) ≤
      combinedBudgetConst E p C_A * (N : ℝ)^(4 * (lambda / 1000)) *
        R^(-(2 : ℝ)) := by
  have hDrift :=
    APrimeFreeLossDriftAssembly.eventually_full_profile_and_actual_drift_integrals_le
      hE hD hs0 hst ht1 hc hreg hB hlambda hsmall p hp
  have hCross :=
    APrimeFreeLossCrossAssembly.eventually_integral_positiveTimeCrossBudget_le_of_uniform_absorbed_root
      hE hD hs0 hst ht1 hc hreg hB hlambda hsmall hCA p hp hAbsorbed
  have hCrossInt :=
    APrimeGeneralMovingCrossBudgetTimeIntegrable.eventually_intervalIntegrable_positive_time_cross_budget
      hE hD hs0 hst ht1 hc hreg (deltaWeight := lambda) hlambda.le p hp
  have hPow :=
    Filter.eventually_ge_atTop (1 : ℕ)
  filter_upwards [hDrift, hCross, hCrossInt, hPow] with
      N hDriftN hCrossN hCrossIntN hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hExp : 0 < lambda / 1000 := by positivity
  have hPowCompare : (N : ℝ)^(3 * (lambda / 1000)) ≤
      (N : ℝ)^(4 * (lambda / 1000)) :=
    Real.rpow_le_rpow_of_exponent_le hNreal (by nlinarith)
  intro k hkpos hk a
  let v := cutNetPt s (mesh D) N k
  let R := Step2Moment.ratR E s N v
  have hWindow : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hVlt : v < 1 := hWindow.2.trans_lt (ht1 N)
  have hSlt : s N < 1 := hWindow.1.trans_lt hVlt
  have hRpos : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos hE hSlt hVlt
  have hRnonneg : 0 ≤ R^(-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hNpow : 0 ≤ (N : ℝ)^(4 * (lambda / 1000)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hFactor : 0 ≤ (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) :=
    mul_nonneg hNpow hRnonneg
  have hDriftCell := hDriftN k hk a
  have hDriftBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) ≤
      APrimeFreeLossDriftAssembly.assemblyConstant E *
        (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) := by
    simpa [v, R, mesh,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      APrimeFreeLossDriftAssembly.sourceLoss] using hDriftCell.2
  have hCrossBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a u) ≤
      APrimeFreeLossCrossAssembly.fullCrossBudgetConst E p C_A *
        (N : ℝ)^(3 * (lambda / 1000)) * R^(-(2 : ℝ)) := by
    simpa [v, R, mesh] using hCrossN k hk a
  have hDriftAbs :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) ≤
      |APrimeFreeLossDriftAssembly.assemblyConstant E| *
        (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) :=
    hDriftBound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hNpow) hRnonneg)
  have hCrossExp :
      APrimeFreeLossCrossAssembly.fullCrossBudgetConst E p C_A *
          (N : ℝ)^(3 * (lambda / 1000)) * R^(-(2 : ℝ)) ≤
        APrimeFreeLossCrossAssembly.fullCrossBudgetConst E p C_A *
          (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPowCompare
        (APrimeFreeLossCrossAssembly.fullCrossBudgetConst_pos hE hCA p hp).le)
      hRnonneg
  have hCrossFinal := hCrossBound.trans hCrossExp
  have hIntegrableDrift :=
    APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
      (deltaWeight := lambda) (p := p) hE hs0 hst ht1 (by omega) hk a
  have hIntegrableCross := hCrossIntN k hk a
  have hIntegralAdd := intervalIntegral.integral_add hIntegrableDrift hIntegrableCross
  have hIntegralAddV :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a u) =
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) +
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a u) := by
    simpa [v, mesh, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hIntegralAdd
  have hsum := add_le_add hDriftAbs hCrossFinal
  change 2 * (∫ u in (s N)..v,
    APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
      APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D lambda s t N k p a u) ≤ _
  rw [hIntegralAddV]
  calc
    2 * ((∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u) +
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a u))
        ≤ 2 * (|APrimeFreeLossDriftAssembly.assemblyConstant E| *
            (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) +
          APrimeFreeLossCrossAssembly.fullCrossBudgetConst E p C_A *
            (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = combinedBudgetConst E p C_A *
        (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) := by
      simp [combinedBudgetConst]
      ring

/-- T1313, T1315, and the public T1325 root interface give a fixed positive
constant before the eventual index, in the exact hbudget shape required by
T1319. The actual weight loss is lambda; the source loss is lambda/1000. -/
theorem exists_positive_C_eventually_actual_drift_plus_full_cross_hbudget
    {E D c lambda : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : ℝ) (c / 10000))
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ k : ℕ, 1 ≤ k →
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
        let v := cutNetPt s (mesh D) N k
        let R := Step2Moment.ratR E s N v
        2 * (∫ u in (s N)..v,
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t lambda p N k a u +
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D lambda s t N k p a u) ≤
        C * (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ)) := by
  obtain ⟨C_A, hCA, hAbsorbed⟩ :=
    APrimeFreeLossRootInterface.exists_positive_C_A_eventually_absorbed_root_le
      hE hD hs0 hst ht1 hc hreg hlambda hsmall
  refine ⟨combinedBudgetConst E p C_A,
    combinedBudgetConst_pos hE hCA p hp, ?_⟩
  exact eventually_actual_drift_plus_full_cross_hbudget_of_absorbed_root
    hE hD hs0 hst ht1 hc hreg hB hlambda hsmall hCA p hp hAbsorbed

/-- A single positive-window Gaussian witness carries both the quantitative
drift-plus-cross conclusion and a nonempty common event. It specializes to
E = 0, D = 60, and p = 1; the sample has the T1325 widened-weight plateau on
an eventually positive-length active cell. -/
theorem joint_positive_window_quantitative_witness :
    ∃ c : ℝ, 0 < c ∧
    ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∃ lambda : ℝ,
        0 < lambda ∧
        lambda ≤ min (1 / 10000 : ℝ) (c / 10000) ∧
        0 < lambda / 1000 ∧
        0 < 2 * lambda ∧
        lambda + lambda = 2 * lambda ∧
        lambda / 1000 ≤ (2 * lambda) / 16 ∧
        2 * lambda ≤ c / 20 ∧
        lambda / 1000 + 2 * (lambda + lambda) + (2 : ℝ) / 15 < 1 ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ N : ℕ in atTop,
            (∀ k : ℕ, 1 ≤ k →
              k ≤ cutNetTop s t (mesh 60) N →
              ∀ a : LoopArg (d.L N) 2,
              let v := cutNetPt s (mesh 60) N k
              let R := Step2Moment.ratR 0 s N v
              2 * (∫ u in (s N)..v,
                APrimeGeneralMovingSmoothDriftNormBudget.g
                  0 60 s t lambda 1 N k a u +
                APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
                  0 60 lambda s t N k 1 a u) ≤
              C * (N : ℝ)^(4 * (lambda / 1000)) * R^(-(2 : ℝ))) ∧
            s N < t N ∧
            ∃ omega,
              omega ∈ APrimeGeneralMovingCommonSources.commonEvent
                0 60 s t (lambda / 1000) (lambda / 1000) (lambda / 1000) N ∧
              1 ≤ cutNetTop s t (mesh 60) N ∧
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t (mesh 60)) 1
                (fun N u omega => Step2Moment.jSnorm (Gauss.sample d)
                  0 60 s N u omega)
                s t (mesh 60) (2 * lambda) 1 N 1 omega = 1 := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
      lambda, hlambda, hsmall, hsource, hcap, hcapEq, hcapTau, hcapC,
      hroom, _C_A, _hCA, hjoint⟩ :=
    APrimeFreeLossRootInterface.free_loss_root_interface_joint_witness
  have hBudget :=
    exists_positive_C_eventually_actual_drift_plus_full_cross_hbudget
      (E := 0) (D := 60) (c := c) (lambda := lambda) (s := s) (t := t)
      (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB hlambda hsmall
      1 (by omega)
  obtain ⟨C, hC, hBudgetEv⟩ := hBudget
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    lambda, hlambda, hsmall, hsource, hcap, hcapEq, hcapTau, hcapC,
    hroom, C, hC, ?_⟩
  filter_upwards [hBudgetEv, hjoint] with N hBudgetN hjointN
  rcases hjointN with ⟨_hrootN, hlen, omega, hcommon, hactive, hwide⟩
  exact ⟨hBudgetN, hlen, omega, hcommon, hactive, hwide⟩

#print axioms combinedBudgetConst_pos
#print axioms eventually_actual_drift_plus_full_cross_hbudget_of_absorbed_root
#print axioms exists_positive_C_eventually_actual_drift_plus_full_cross_hbudget
#print axioms joint_positive_window_quantitative_witness

end
end RBM.APrimeFreeLossDriftCrossBudget
