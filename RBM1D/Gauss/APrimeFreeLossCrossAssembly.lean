/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossPrefixGradient
import RBM1D.Gauss.APrimeFreeLossCrossIntegral
import RBM1D.Gauss.APrimeFreeLossCrossEventSplit

/-!
# T1315: conditional free-loss full cross-budget assembly

This module composes the corrected-loss transition rate, the conditional
integral of the complete absorbed root profile, and the event-split bound for
the literal positive-time cross budget.  The absorbed-root estimate remains a
named conditional input; this module does not claim its producer.
-/

namespace RBM.APrimeFreeLossCrossAssembly

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The coefficient in the assembled full positive-time cross-budget bound. -/
noncomputable def fullCrossBudgetConst (E : Real) (p : Nat) (C_A : Real) : Real :=
  (15 * (p : Real) / 4) *
    (APrimeFreeLossPrefixGradient.freeLossRateConst * C_A / (mE E).im + 2)

theorem fullCrossBudgetConst_pos {E C_A : Real} (hE : |E| < 2)
    (hCA : 0 < C_A) (p : Nat) (hp : 1 ≤ p) :
    0 < fullCrossBudgetConst E p C_A := by
  unfold fullCrossBudgetConst
  have him : 0 < (mE E).im := mE_im_pos hE
  have hrate := APrimeFreeLossPrefixGradient.freeLossRateConst_pos
  positivity

/-- If the complete literal absorbed root profile is uniformly bounded on
every closed active cell at the corrected losses, then the full positive-time
cross budget is bounded on each active cell and output by
`C(E,p,C_A) N^(3h) R_v^(-2)`, where `h = lambda / 1000` and
`R_v = etaT(E,s_N) / etaT(E,v)`.  The two inverse-`N` payments from the
event split are both absorbed using (2.72), the `Cond272Reg` scale bound, and
`W_N ell_N(v) etaT(E,v) ≤ N`.  The profile hypothesis is the conditional
input intended for the separate absorbed-root producer.

The case `k = 0` is included; its cross budget integral is over a degenerate
interval.  No positivity assumption on `s_N` is imposed, so `s_N = 0` is
allowed.
-/
theorem eventually_integral_positiveTimeCrossBudget_le_of_uniform_absorbed_root
    {E D c lambda C_A : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000))
    (hCA : 0 < C_A) (p : Nat) (hp : 1 ≤ p)
    (hAbsorbed : ∀ᶠ N : Nat in atTop,
      ∀ k : Nat, k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      let v := cutNetPt s (mesh D) N k
      ∀ u ∈ Icc (s N) v,
        APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
          (lambda / 1000) N u v D
          (APrimeFreeLossCrossIntegral.profileCap E s (lambda / 1000)
            (2 * lambda) N u) a ≤
        C_A * (N : Real)^(2 * (lambda / 1000)) *
          (etaT E (s N))^(-(1 / 2 : Real)) *
          Step2Moment.ratR E s N v^(-(2 : Real))) :
    ∀ᶠ N : Nat in atTop,
      ∀ k : Nat, k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      let v := cutNetPt s (mesh D) N k
      (∫ r in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a r) ≤
        fullCrossBudgetConst E p C_A * (N : Real)^(3 * (lambda / 1000)) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
  let h : Real := lambda / 1000
  let K : Real := 15 * (p : Real) / 4
  have hRatePositive :=
    APrimeFreeLossPrefixGradient.eventually_transitionPrefixGradientRate_le_free_loss
      hE hD hs0 hst ht1 hc hreg hlambda hsmall
  have hRate : ∀ᶠ N : Nat in atTop,
      ∀ k : Nat, k ≤ cutNetTop s t (mesh D) N →
        APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
            E D s t (lambda / 1000) (lambda / 1000) lambda N k ≤
          APrimeFreeLossPrefixGradient.freeLossRateConst * (N : Real)^h *
            (etaT E (s N))^(-(1 / 2 : Real)) := by
    filter_upwards [hRatePositive] with N hRateN
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      have hz :=
        APrimeFreeLossPrefixGradient.transitionPrefixGradientRate_zero
          E D lambda s t N
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      have hS : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
      have hNpow : 0 ≤ (N : Real)^h := Real.rpow_nonneg (Nat.cast_nonneg N) h
      have hSneg : 0 ≤ (etaT E (s N))^(-(1 / 2 : Real)) :=
        Real.rpow_nonneg hS.le _
      have hCT : 0 ≤ APrimeFreeLossPrefixGradient.freeLossRateConst :=
        APrimeFreeLossPrefixGradient.freeLossRateConst_pos.le
      have hzero :
          APrimeGeneralMovingTransitionPrefixGradient.transitionPrefixGradientRate
              E D s t (lambda / 1000) (lambda / 1000) lambda N 0 = 0 := by
        simpa [APrimeFreeLossPrefixGradient.zetaSrc,
          APrimeFreeLossPrefixGradient.tauG,
          APrimeFreeLossPrefixGradient.deltaWeight,
          APrimeFreeLossPrefixGradient.sourceLoss] using hz
      rw [hzero]
      exact mul_nonneg (mul_nonneg hCT hNpow) hSneg
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hpos := hRateN k hkpos hk
      simpa [h, APrimeFreeLossPrefixGradient.zetaSrc,
        APrimeFreeLossPrefixGradient.tauG,
        APrimeFreeLossPrefixGradient.deltaWeight,
        APrimeFreeLossPrefixGradient.sourceLoss] using hpos

  have hProfile :=
    APrimeFreeLossCrossIntegral.eventually_integral_crossProfile_le_of_uniform_profiles
      hE (le_trans (by norm_num : (0 : Real) ≤ 60) hD) hs0 hst ht1 hc hlambda hsmall
      APrimeFreeLossPrefixGradient.freeLossRateConst_pos hCA hRate hAbsorbed
  have hFull :=
    APrimeFreeLossCrossEventSplit.eventually_integral_positiveTimeCrossBudget_le_freeLossProfile_add_two_payments
      hE hD hs0 hst ht1 hc hreg hB hlambda hsmall p hp
  have hMargin := hreg.1.pow_thirty_le hE hst ht1
  have hDim := B.dim

  filter_upwards [hProfile, hFull, hMargin, hDim, eventually_ge_atTop 1]
    with N hProfileN hFullN hMarginN hDimN hN
  have hNreal : (1 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hNpos : (0 : Real) < (N : Real) := by linarith
  have hNinv0 : 0 ≤ (N : Real)^(-(1 : Real)) := by positivity
  have hNsmall : 0 ≤ (3 * h) := by positivity
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hv.1 hv1
  have hR30 : Step2Moment.ratR E s N v ^ (30 : Nat) ≤
      B.scale E N v := by
    let vv : TimeIcc s t N := ⟨v, hv⟩
    have hh := hMarginN vv
    simpa only [Step2Moment.ratR] using hh
  have hscaleN : B.scale E N v ≤ (N : Real) := by
    let vv : TimeIcc s t N := ⟨v, hv⟩
    obtain ⟨_, _, heta1, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N vv
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast (hDimN.1 : B.W N * B.L N ≤ N)
    change (B.W N : Real) * B.ell N v * etaT E v ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hR30N : Step2Moment.ratR E s N v ^ (30 : Nat) ≤ (N : Real) :=
    hR30.trans hscaleN
  have hRtwo : Step2Moment.ratR E s N v ^ (2 : Real) ≤
      (N : Real) ^ ((1 : Real) / 15) := by
    have hh := RBM.rpow_mul_rpow_le_of_pow_thirty
      (A := (N : Real)) (R := Step2Moment.ratR E s N v)
      (Nr := (N : Real)) (c := 1) (e := 0) (b := 2)
      (a := (1 : Real) / 15)
      hNreal hR1 (by norm_num) (by norm_num) (by norm_num)
      hR30N (by simp) (by norm_num)
    simpa using hh
  have hmulBound :
      (N : Real)^(-(1 : Real)) *
          Step2Moment.ratR E s N v ^ (2 : Real) ≤
        (N : Real)^(3 * h) := by
    calc
      _ ≤ (N : Real)^(-(1 : Real)) * (N : Real)^((1 : Real) / 15) :=
        mul_le_mul_of_nonneg_left hRtwo hNinv0
      _ = (N : Real)^(-(14 : Real) / 15) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
      _ ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hNreal (by norm_num)
      _ ≤ (N : Real)^(3 * h) := Real.one_le_rpow hNreal hNsmall
  have hRtwoPos : 0 < Step2Moment.ratR E s N v ^ (2 : Real) :=
    Real.rpow_pos_of_pos hR _
  have hPaymentScale :
      (N : Real)^(-(1 : Real)) ≤
        (N : Real)^(3 * h) * Step2Moment.ratR E s N v^(-(2 : Real)) := by
    calc
      _ ≤ (N : Real)^(3 * h) /
          Step2Moment.ratR E s N v ^ (2 : Real) :=
        (le_div_iff₀ hRtwoPos).2 hmulBound
      _ = _ := by
        rw [Real.rpow_neg hR.le, div_eq_mul_inv]
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hdelta0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hv.1)
  have hdelta1 : Real.sqrt v - Real.sqrt (s N) ≤ 1 := by
    have hsqrtv : Real.sqrt v ≤ 1 :=
      Real.sqrt_le_one.mpr ((hv.2.trans_lt (ht1 N)).le)
    have hsqrts : 0 ≤ Real.sqrt (s N) := Real.sqrt_nonneg _
    linarith
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hPayment :
      K * (N : Real)^(-(1 : Real)) *
          (Real.sqrt v - Real.sqrt (s N)) ≤
        K * (N : Real)^(3 * h) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
    calc
      _ = K * ((N : Real)^(-(1 : Real)) *
          (Real.sqrt v - Real.sqrt (s N))) := by ring
      _ ≤ K * (N : Real)^(-(1 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        calc
          _ ≤ (N : Real)^(-(1 : Real)) * 1 :=
            mul_le_mul_of_nonneg_left hdelta1 hNinv0
          _ = _ := by ring
      _ ≤ K * ((N : Real)^(3 * h) *
          Step2Moment.ratR E s N v^(-(2 : Real))) :=
        mul_le_mul_of_nonneg_left hPaymentScale hK0
      _ = _ := by ring
  have hFullBound :
      (∫ r in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D lambda s t N k p a r) ≤
        K * (∫ r in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (lambda / 1000) (lambda / 1000) lambda (2 * lambda) N k a r) +
          K * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N)) +
          K * (N : Real)^(-(1 : Real)) *
            (Real.sqrt v - Real.sqrt (s N)) := by
    convert hFullN k hk a using 1 <;> rfl
  have hProfileBound :
      (∫ r in (s N)..v,
        APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
          (lambda / 1000) (lambda / 1000) lambda (2 * lambda) N k a r) ≤
        (APrimeFreeLossPrefixGradient.freeLossRateConst * C_A / (mE E).im) *
          (N : Real)^(3 * h) *
            Step2Moment.ratR E s N v^(-(2 : Real)) := by
    simpa [v, h] using hProfileN k hk a
  calc
    _ ≤ K * (∫ r in (s N)..v,
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
            (lambda / 1000) (lambda / 1000) lambda (2 * lambda) N k a r) +
        K * (N : Real)^(-(1 : Real)) *
          (Real.sqrt v - Real.sqrt (s N)) +
        K * (N : Real)^(-(1 : Real)) *
          (Real.sqrt v - Real.sqrt (s N)) := hFullBound
    _ ≤ K * ((APrimeFreeLossPrefixGradient.freeLossRateConst * C_A /
          (mE E).im) * (N : Real)^(3 * h) *
            Step2Moment.ratR E s N v^(-(2 : Real))) +
        K * (N : Real)^(3 * h) *
          Step2Moment.ratR E s N v^(-(2 : Real)) +
        K * (N : Real)^(3 * h) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hProfileBound hK0)
          hPayment)
        hPayment
    _ = fullCrossBudgetConst E p C_A * (N : Real)^(3 * h) *
          Step2Moment.ratR E s N v^(-(2 : Real)) := by
      simp [fullCrossBudgetConst, K, h]
      ring

/-! The underlying model/window hypotheses have a same-sample witness at
`E = 0`, `D = 60`, `s_N = 0`, with an eventually active positive cell and a
positive actual smooth weight.  This witness does not discharge the
quantitative absorbed-root premise above. -/
noncomputable abbrev nondegenerate_geometry_witness :=
  APrimeFreeLossCrossEventSplit.nondegenerate_free_loss_positive_cell_witness

#print axioms fullCrossBudgetConst_pos
#print axioms eventually_integral_positiveTimeCrossBudget_le_of_uniform_absorbed_root
#print axioms nondegenerate_geometry_witness

end
end RBM.APrimeFreeLossCrossAssembly
