/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormBad
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeGeneralMovingJointMeasurable
import RBM1D.Gauss.APrimeQVRateTime

/-!
# T1199: integrated p=1 norm-bad cross-budget component

This file integrates only the exact norm-bad restriction of the general-moving
p=1 cross budget.  Its time measurability comes from the literal joint-rate
measurability with one additional fixed measurable indicator; its integrable
majorant is the inverse-square-root profile supplied by T1185.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetNormBadIntegral

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The exact T1185 norm-bad joint rate is jointly measurable in the running
time and Gaussian sample on each active closed target cell.  The bad event is
fixed in time and measurable under the same Gaussian model. -/
private theorem measurable_normBadJointRate_on_window
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ} {N k : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (mesh D) N)
    (a : LoopArg (d.L N) 2) :
    Measurable (fun q :
      (Icc (s N) (cutNetPt s (mesh D) N k)) × Ω d =>
        APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
          E D deltaWeight s t N k a q.1.1 q.2) := by
  let v := cutNetPt s (mesh D) N k
  let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
  let S := Icc (s N) v
  let pref := APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
    (mesh D) N k m
  let trans := APrimeCrossJointSplit.transition d E D deltaWeight s
    (mesh D) N k m
  let bad := (APrimeGeneralMovingGoodMesh.good N)ᶜ
  have hwindow : v ∈ Icc (s N) (t N) :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hv1 : v < 1 := hwindow.2.trans_lt (ht1 N)
  have hpref : Measurable pref := by
    exact (APrimeGeneralMovingJointMeasurable.continuous_prefixGradient
      (deltaWeight := deltaWeight) hE hst ht1 hN hk).measurable
  have htrans : MeasurableSet trans :=
    APrimeGeneralMovingJointMeasurable.measurableSet_transition
      (deltaWeight := deltaWeight) hE hst ht1 hN hk
  have hbad : MeasurableSet bad :=
    (APrimeGeneralMovingGoodMesh.measurableSet_good N).compl
  have hqv : Measurable (fun q : S × Ω d =>
      APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v q.1.1 q.2) := by
    exact APrimeQVRateTime.measurable_qvAt_on_window d E D N Step2.sigPM a
      hE (hs0 N) hwindow.1 hv1
  let raw : S × Ω d → ℝ := fun q =>
    pref q.2 * √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a
      (s N) v q.1.1 q.2)
  have hraw : Measurable raw :=
    (hpref.comp measurable_snd).mul hqv.sqrt
  let transProd : Set (S × Ω d) := {q | q.2 ∈ trans}
  have htransProd : MeasurableSet transProd := htrans.preimage measurable_snd
  let badProd : Set (S × Ω d) := {q | q.2 ∈ bad}
  have hbadProd : MeasurableSet badProd := hbad.preimage measurable_snd
  let rate : S × Ω d → ℝ := fun q =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
      Step2.sigPM a v q.1.1 q.2
  have hrate : rate = transProd.indicator raw := by
    funext q
    by_cases hq : q.2 ∈ trans
    · simp [rate, transProd, raw, pref, trans, v, m, hq,
        APrimeCrossJointSplit.jointRate]
    · simp [rate, transProd, raw, pref, trans, v, m, hq,
        APrimeCrossJointSplit.jointRate]
  let badRate : S × Ω d → ℝ := fun q =>
    APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
      E D deltaWeight s t N k a q.1.1 q.2
  have hbadRate : badRate = badProd.indicator rate := by
    funext q
    change (APrimeGeneralMovingGoodMesh.good N)ᶜ.indicator
        (fun ω => APrimeCrossJointSplit.jointRate d E D deltaWeight s
          (mesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
          Step2.sigPM a (cutNetPt s (mesh D) N k) q.1.1 ω) q.2 =
      badProd.indicator rate q
    by_cases hgood : q.2 ∈ APrimeGeneralMovingGoodMesh.good N
    · simp [badProd, bad, hgood, rate, m, v]
    · simp [badProd, bad, hgood, rate, m, v]
  rw [show (fun q : S × Ω d =>
      APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
        E D deltaWeight s t N k a q.1.1 q.2) = badRate by rfl]
  rw [hbadRate, hrate]
  exact (hraw.indicator htransProd).indicator hbadProd

/-- The L² moment norm of the exact norm-bad joint rate is measurable in
time. -/
private theorem measurable_momNorm_normBadJointRate_on_window
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ} {N k : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (mesh D) N)
    (a : LoopArg (d.L N) 2) :
    Measurable (fun r : Icc (s N) (cutNetPt s (mesh D) N k) =>
      MomentDuhamel.momNorm (Gauss.P d) 2
        (APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
          E D deltaWeight s t N k a r.1)) := by
  classical
  let S := Icc (s N) (cutNetPt s (mesh D) N k)
  let Z : S → Ω d → ℝ := fun r ω =>
    APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
      E D deltaWeight s t N k a r.1 ω
  have hZ : Measurable (fun q : S × Ω d => Z q.1 q.2) := by
    exact measurable_normBadJointRate_on_window hE hs0 hst ht1 hN hk a
  have hpow : Measurable (fun q : S × Ω d => |Z q.1 q.2| ^ (2 : ℕ)) :=
    (continuous_abs.measurable.comp hZ).pow_const 2
  have hInt : StronglyMeasurable (fun r : S =>
      ∫ ω, |Z r ω| ^ (2 : ℕ) ∂(Gauss.P d)) :=
    hpow.stronglyMeasurable.integral_prod_right'
  have hpowMeas : Measurable (fun r : S =>
      (∫ ω, |Z r ω| ^ (2 : ℕ) ∂(Gauss.P d)) ^
        ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
    exact (Real.continuous_rpow_const (by positivity)).measurable.comp
      hInt.measurable
  change Measurable (fun r : S =>
    MomentDuhamel.momNorm (Gauss.P d) 2 (Z r))
  simpa [MomentDuhamel.momNorm, Z, S, Nat.cast_ofNat] using hpowMeas

/-- The exact norm-bad p=1 cross budget is interval-integrable on every
active closed target cell, uniformly after one cutoff in N.  At `r = 0`, its
division by `sqrt r` is assigned the real field value zero. -/
theorem eventually_intervalIntegrable_normBadCrossBudget
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
            E D deltaWeight s t N k a)
          volume (s N) (cutNetPt s (mesh D) N k) := by
  have hpoint :=
    APrimeGeneralMovingCrossBudgetNormBad.eventually_normBad_p1_crossBudget_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hintRate :=
    APrimeGeneralMovingCrossBudgetNormBad.eventually_integrable_normBadJointRate_sq
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  filter_upwards [hpoint, hintRate, eventually_ge_atTop 1]
    with N hpointN _hintRateN hN
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  let S := Icc (s N) v
  let K : ℝ := (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ))
  let major : ℝ → ℝ := fun r => K / √r
  have hwindow : v ∈ Icc (s N) (t N) :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hwindow.1
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajor : IntervalIntegrable major volume (s N) v := by
    exact APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      K (s N) v (hs0 N) hsv
  have hmajorOn : IntegrableOn major (Icc (s N) v) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).1 hmajor
  let μ : Measure S := volume.comap ((↑) : S → ℝ)
  have hmajorSub : Integrable (fun r : S => major r.1) μ :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hmajorOn
  let budget : S → ℝ := fun r =>
    APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
      E D deltaWeight s t N k a r.1
  have hbudgetMeas : Measurable budget := by
    have hnorm := measurable_momNorm_normBadJointRate_on_window
      (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1 hNpos hk a
    have hsqrt : Measurable (fun r : S => √r.1) :=
      Real.continuous_sqrt.measurable.comp continuous_subtype_val.measurable
    have hcoeff : Measurable (fun r : S =>
        APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
          (4 * (1 : ℝ) * √r.1)) :=
      measurable_const.div (measurable_const.mul hsqrt)
    change Measurable (fun r : S =>
      (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
        (4 * (1 : ℝ) * √r.1)) *
        MomentDuhamel.momNorm (Gauss.P d) 2
          (APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate
            E D deltaWeight s t N k a r.1))
    exact hcoeff.mul hnorm
  have hbudget_le : ∀ r : S, ‖budget r‖ ≤ major r.1 := by
    intro r
    have hr0 : 0 ≤ r.1 := (hs0 N).trans r.2.1
    have hbudget0 : 0 ≤ budget r := by
      change 0 ≤ APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
        E D deltaWeight s t N k a r.1
      unfold APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
      rw [APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff_one]
      exact mul_nonneg
        (div_nonneg (by norm_num) (by positivity))
        (MomentDuhamel.momNorm_nonneg _ _ _)
    by_cases hrpos : 0 < r.1
    · have hle := hpointN k hk a r.1 r.2 hrpos
      have hle' : budget r ≤ major r.1 := by
        change APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
            E D deltaWeight s t N k a r.1 ≤ K / √r.1
        simpa [K, major] using hle
      rw [Real.norm_eq_abs, abs_of_nonneg hbudget0]
      exact hle'
    · have hrEq : r.1 = 0 := le_antisymm (le_of_not_gt hrpos) hr0
      have hzero : budget r = 0 := by
        change APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
          E D deltaWeight s t N k a r.1 = 0
        simp [APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget, hrEq]
      rw [hzero, Real.norm_eq_abs, abs_zero]
      simp [major, K, hrEq]
  have hbudgetSub : Integrable budget μ :=
    hmajorSub.mono' hbudgetMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbudget_le)
  have hbudgetOn : IntegrableOn
      (APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
        E D deltaWeight s t N k a)
      (Icc (s N) v) volume := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).2 hbudgetSub
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).2 hbudgetOn

/-- Integrating the exact bad-restricted p=1 coefficient gives the sharper
moving-cell bound `(15/4) N⁻¹ (sqrt(v) - sqrt(s_N))`, and hence the requested
`(15/4) N⁻¹ sqrt(v)` estimate.  One eventual N works for every active cell
and output. -/
theorem eventually_integral_normBadCrossBudget_le
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        (∫ r in (s N)..(cutNetPt s (mesh D) N k),
          APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
            E D deltaWeight s t N k a r) ≤
          (15 / 4 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
            (√(cutNetPt s (mesh D) N k) - √(s N)) := by
  have hint := eventually_intervalIntegrable_normBadCrossBudget
    hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hpoint :=
    APrimeGeneralMovingCrossBudgetNormBad.eventually_normBad_p1_crossBudget_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  filter_upwards [hint, hpoint, eventually_ge_atTop 1]
    with N hintN hpointN hN
  have hNpos : 0 < N := by omega
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  let K : ℝ := (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ))
  let major : ℝ → ℝ := fun r => K / √r
  have hwindow : v ∈ Icc (s N) (t N) :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hwindow.1
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajor : IntervalIntegrable major volume (s N) v := by
    exact APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      K (s N) v (hs0 N) hsv
  have hpointwise : ∀ r ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
        E D deltaWeight s t N k a r ≤ major r := by
    intro r hr
    have hr0 : 0 ≤ r := (hs0 N).trans hr.1
    by_cases hrpos : 0 < r
    · have h := hpointN k hk a r hr hrpos
      simpa [major, K] using h
    · have hrEq : r = 0 := le_antisymm (le_of_not_gt hrpos) hr0
      subst r
      have hzero :
          APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget
            E D deltaWeight s t N k a 0 = 0 := by
        simp [APrimeGeneralMovingCrossBudgetNormBad.normBadCrossBudget]
      rw [hzero]
      simp [major, K]
  have hmono := intervalIntegral.integral_mono_on hsv
    (hintN k hk a) hmajor hpointwise
  have hmajorEq :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      K (s N) v (hs0 N) hsv
  rw [show (15 / 4 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) *
        (√v - √(s N)) = 2 * K * (√v - √(s N)) by
          dsimp [K]
          ring]
  simpa [major] using hmono.trans_eq hmajorEq

/-! T1185's explicit active `k=2`, positive-time witness is retained here,
with the same model parameters and exact strict transition resident. -/

noncomputable abbrev nondegenerate_active_k2_witness :=
  APrimeGeneralMovingCrossBudgetNormBad.nondegenerate_active_k2_witness

#print axioms measurable_normBadJointRate_on_window
#print axioms measurable_momNorm_normBadJointRate_on_window
#print axioms eventually_intervalIntegrable_normBadCrossBudget
#print axioms eventually_integral_normBadCrossBudget_le
#print axioms nondegenerate_active_k2_witness

end
end RBM.APrimeGeneralMovingCrossBudgetNormBadIntegral
