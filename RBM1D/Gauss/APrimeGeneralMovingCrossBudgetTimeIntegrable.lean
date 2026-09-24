/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetPoly
import RBM1D.Gauss.APrimeGeneralMovingJointMeasurable
import RBM1D.Gauss.APrimeQVRateTime

/-!
# T1123: local integrability of the positive-time cross budget

For each fixed moment order, the actual positive-time cross budget is
integrable on every active closed target-mesh cell, eventually in the matrix
size.  The proof uses the exact joint-rate measurability on time × sample
space, the accepted all-sample polynomial cap, and the integrable `r^(-1/2)`
majorant.  At `r = 0` the original budget formula evaluates to zero by the
field convention for division by zero.
-/

#check @RBM.APrimeDriftTimeFamily.qvAt_eq_evolved
#check @RBM.Gauss.continuous_Hflow_time
#check @RBM.APrimeDriftTimeFamily.continuousOn_momNormW_of_envelope
#check @intervalIntegral.intervalIntegrable_rpow'

namespace RBM.APrimeGeneralMovingCrossBudgetTimeIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- Joint measurability in running time and sample of the exact transition-
indicated `jointRate` used by `positiveTimeCrossBudget`.  The time component
is the literal evolved `qvAt`; its joint measurability is obtained from the
actual `coordAt` family and `Hflow`, not from the polynomial majorant. -/
private theorem measurable_jointRate_on_window
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ} {N k : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    Measurable (fun q :
      (Icc (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) × Ω d =>
        APrimeCrossJointSplit.jointRate d E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N)
          Step2.sigPM a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
          q.1.1 q.2) := by
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  let m := APrimeSmoothWeightActual.canonicalM d s t
    (APrimeGeneralMovingMesh.targetMesh D) N
  let S := Icc (s N) v
  let pref := APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
    (APrimeGeneralMovingMesh.targetMesh D) N k m
  let trans := APrimeCrossJointSplit.transition d E D deltaWeight s
    (APrimeGeneralMovingMesh.targetMesh D) N k m
  have hwindow : v ∈ Icc (s N) (t N) :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hv1 : v < 1 := hwindow.2.trans_lt (ht1 N)
  have hpref : Measurable pref := by
    exact (APrimeGeneralMovingJointMeasurable.continuous_prefixGradient
      (deltaWeight := deltaWeight) hE hst ht1 hN hk).measurable
  have htrans : MeasurableSet trans := by
    exact APrimeGeneralMovingJointMeasurable.measurableSet_transition
      (deltaWeight := deltaWeight) hE hst ht1 hN hk
  have hqv : Measurable (fun q : S × Ω d =>
      APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v q.1.1 q.2) := by
    exact APrimeQVRateTime.measurable_qvAt_on_window d E D N Step2.sigPM a
      hE (hs0 N) hwindow.1 hv1
  let raw : S × Ω d → ℝ := fun q =>
    pref q.2 * √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a
      (s N) v q.1.1 q.2)
  have hraw : Measurable raw := by
    exact (hpref.comp measurable_snd).mul hqv.sqrt
  let transProd : Set (S × Ω d) := {q | q.2 ∈ trans}
  have htransProd : MeasurableSet transProd := htrans.preimage measurable_snd
  have hrate : (fun q : S × Ω d =>
      APrimeCrossJointSplit.jointRate d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k m Step2.sigPM a v q.1.1 q.2) =
      transProd.indicator raw := by
    funext q
    by_cases hq : q.2 ∈ trans
    · simp [transProd, raw, pref, trans, v, m, hq,
        APrimeCrossJointSplit.jointRate]
    · simp [transProd, raw, pref, trans, v, m, hq,
        APrimeCrossJointSplit.jointRate]
  rw [hrate]
  exact hraw.indicator htransProd

/-- The actual `L^(2p)` moment norm of that same joint rate is measurable in
time.  This is the product-measure route from T618; it needs no continuity of
the rate's samplewise derivative in the time parameter. -/
private theorem measurable_momNorm_jointRate_on_window
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ} {N k p : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    Measurable (fun r : Icc (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) =>
        MomentDuhamel.momNorm (Gauss.P d) (2 * p)
          (APrimeCrossJointSplit.jointRate d E D deltaWeight s
            (APrimeGeneralMovingMesh.targetMesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N)
            Step2.sigPM a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
            r.1)) := by
  classical
  let S := Icc (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
  let Z : S → Ω d → ℝ := fun r ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      Step2.sigPM a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
      r.1 ω
  have hZ : Measurable (fun q : S × Ω d => Z q.1 q.2) :=
    measurable_jointRate_on_window hE hs0 hst ht1 hN hk a
  have hpow : Measurable (fun q : S × Ω d => |Z q.1 q.2| ^ (2 * p)) :=
    (continuous_abs.measurable.comp hZ).pow_const (2 * p)
  have hInt : StronglyMeasurable (fun r : S =>
      ∫ ω, |Z r ω| ^ (2 * p) ∂(Gauss.P d)) :=
    hpow.stronglyMeasurable.integral_prod_right'
  have hpowMeas : Measurable (fun r : S =>
      (∫ ω, |Z r ω| ^ (2 * p) ∂(Gauss.P d)) ^
        ((1 : ℝ) / ((2 * p : ℕ) : ℝ))) := by
    exact (Real.continuous_rpow_const (by positivity)).measurable.comp hInt.measurable
  change Measurable (fun r : S =>
    MomentDuhamel.momNorm (Gauss.P d) (2 * p) (Z r))
  simpa [MomentDuhamel.momNorm, Z, S, Nat.cast_mul] using hpowMeas

/-- For every fixed `p ≥ 1`, the literal positive-time cross budget is
interval-integrable on all active closed target cells, eventually in `N`.
At `k=0` the interval may be degenerate, which the same argument includes. -/
theorem eventually_intervalIntegrable_positive_time_cross_budget
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a)
          volume (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) := by
  have hpoly :=
    APrimeGeneralMovingCrossBudgetPoly.eventually_positive_time_cross_budget_le_polynomial
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hpoly, eventually_ge_atTop 1] with N hpolyN hN
  have hNpos : 0 < N := by omega
  intro k hk a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  let S := Icc (s N) v
  let K : ℝ :=
    APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
      (4 * (p : ℝ)) * (N : ℝ) ^ (2 * D + 17)
  let sing : ℝ → ℝ := fun r => r ^ (-(1 / 2 : ℝ))
  have hwindow : v ∈ Icc (s N) (t N) :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hwindow.1
  have hbase : IntervalIntegrable sing volume (s N) v := by
    exact intervalIntegral.intervalIntegrable_rpow' (a := s N) (b := v)
      (by norm_num : -1 < -(1 / 2 : ℝ))
  have hmajor : IntervalIntegrable (fun r => K * sing r) volume (s N) v :=
    hbase.const_mul K
  have hmajorOn : IntegrableOn (fun r => K * sing r) (Icc (s N) v) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).1 hmajor
  let μ : Measure S := volume.comap ((↑) : S → ℝ)
  have hmajorSub : Integrable (fun r : S => K * sing r.1) μ := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hmajorOn
  let budget : S → ℝ := fun r =>
    APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
      E D deltaWeight s t N k p a r.1
  have hbudgetMeas : Measurable budget := by
    have hnorm := measurable_momNorm_jointRate_on_window
      (deltaWeight := deltaWeight) (p := p) hE hs0 hst ht1 hNpos hk a
    have hsqrt : Measurable (fun r : S => √r.1) :=
      Real.continuous_sqrt.measurable.comp continuous_subtype_val.measurable
    have hcoeff : Measurable (fun r : S =>
        APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r.1)) :=
      measurable_const.div (measurable_const.mul hsqrt)
    change Measurable (fun r : S =>
      (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r.1)) *
      MomentDuhamel.momNorm (Gauss.P d) (2 * p)
        (APrimeCrossJointSplit.jointRate d E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N)
          Step2.sigPM a v r.1))
    exact hcoeff.mul hnorm
  have hK0 : 0 ≤ K := by
    dsimp [K, APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff]
    positivity
  have hbudget_le : ∀ r : S, ‖budget r‖ ≤ K * sing r.1 := by
    intro r
    have hr0 : 0 ≤ r.1 := (hs0 N).trans r.2.1
    by_cases hrpos : 0 < r.1
    · obtain ⟨hbudget0, hbudgetPoly⟩ := hpolyN k hk a r.1 r.2 hrpos
      have hpR : 0 < (p : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hp)
      have hsqrtPos : 0 < √r.1 := Real.sqrt_pos.2 hrpos
      have hsqrtInv : (√r.1)⁻¹ = r.1 ^ (-(1 / 2 : ℝ)) := by
        calc
          (√r.1)⁻¹ = (r.1 ^ (1 / 2 : ℝ))⁻¹ := by rw [Real.sqrt_eq_rpow]
          _ = r.1 ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_neg hr0 (1 / 2 : ℝ)]
      have hrewrite :
          APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
              (4 * (p : ℝ) * √r.1) * (N : ℝ) ^ (2 * D + 17) =
            K * sing r.1 := by
        dsimp [K, sing]
        calc
          APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
              (4 * (p : ℝ) * √r.1) * (N : ℝ) ^ (2 * D + 17) =
              APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ)) * (√r.1)⁻¹ * (N : ℝ) ^ (2 * D + 17) := by
                  field_simp [hpR.ne', hsqrtPos.ne']
          _ = APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ)) * r.1 ^ (-(1 / 2 : ℝ)) *
                  (N : ℝ) ^ (2 * D + 17) := by rw [hsqrtInv]
          _ = APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ)) * (N : ℝ) ^ (2 * D + 17) *
                  r.1 ^ (-(1 / 2 : ℝ)) := by ring
      have hle : budget r ≤ K * sing r.1 := by
        change APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k p a r.1 ≤ _
        calc
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D deltaWeight s t N k p a r.1 ≤
              APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ) * √r.1) * (N : ℝ) ^ (2 * D + 17) :=
              hbudgetPoly
          _ = K * sing r.1 := hrewrite
      rw [Real.norm_eq_abs, abs_of_nonneg hbudget0]
      exact hle
    · have hrEq : r.1 = 0 := by linarith
      have hbudget0 : budget r = 0 := by
        simp [budget, APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget,
          hrEq]
      rw [hbudget0, Real.norm_eq_abs, abs_zero]
      simp [sing, hrEq]
  have hbudgetSub : Integrable budget μ :=
    hmajorSub.mono' hbudgetMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbudget_le)
  have hbudgetOn : IntegrableOn
      (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D deltaWeight s t N k p a) (Icc (s N) v) volume := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).2 hbudgetSub
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).2 hbudgetOn

/-- The accepted T995 witness for a nondegenerate admissible positive cell. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingCrossHcrossPositive.t995_positive_cell_witness

#print axioms measurable_jointRate_on_window
#print axioms measurable_momNorm_jointRate_on_window
#print axioms eventually_intervalIntegrable_positive_time_cross_budget
#print axioms t995_positive_cell_witness

end
end RBM.APrimeGeneralMovingCrossBudgetTimeIntegrable
