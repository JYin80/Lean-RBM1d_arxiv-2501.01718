/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodReduction
import RBM1D.Gauss.APrimeGeneralMovingJointGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingJointMeasurable
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormBadIntegral
import RBM1D.Gauss.APrimeQVRateTime

/-!
# T1205: time integrability of the norm-good general-moving cross budget

For each fixed positive integer moment order, the literal norm-good term from
T1201 is interval-integrable on every active moving target cell, eventually
in the matrix size.  The proof keeps the exact Gaussian rate and uses the
all-sample polynomial envelope together with product measurability.  It makes
no small-budget or full A-prime claim.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- Joint measurability of the literal T1201 norm-good rate on one closed
moving cell and the same Gaussian sample space. -/
private theorem measurable_normGoodJointRate_on_window
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ} {N k : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (mesh D) N)
    (a : LoopArg (d.L N) 2) :
    Measurable (fun q : (Icc (s N) (cutNetPt s (mesh D) N k)) × Ω d =>
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
        E D deltaWeight s t N k a q.1.1 q.2) := by
  let v := cutNetPt s (mesh D) N k
  let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
  let S := Icc (s N) v
  let pref := APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
    (mesh D) N k m
  let trans := APrimeCrossJointSplit.transition d E D deltaWeight s
    (mesh D) N k m
  have hwindow : v ∈ Icc (s N) (t N) :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hv1 : v < 1 := hwindow.2.trans_lt (ht1 N)
  have hpref : Measurable pref := by
    exact (APrimeGeneralMovingJointMeasurable.continuous_prefixGradient
      (deltaWeight := deltaWeight) hE hst ht1 hN hk).measurable
  have htrans : MeasurableSet trans :=
    APrimeGeneralMovingJointMeasurable.measurableSet_transition
      (deltaWeight := deltaWeight) hE hst ht1 hN hk
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
  have hrateMeas : Measurable rate := by
    rw [hrate]
    exact hraw.indicator htransProd
  let good := APrimeGeneralMovingGoodMesh.good N
  let goodProd : Set (S × Ω d) := {q | q.2 ∈ good}
  have hgood : MeasurableSet good :=
    APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hgoodProd : MeasurableSet goodProd := hgood.preimage measurable_snd
  have hgoodRate :
      (fun q : S × Ω d =>
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N k a q.1.1 q.2) =
        goodProd.indicator rate := by
    funext q
    by_cases hq : q.2 ∈ good
    · simp [goodProd, good, rate,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hq, v, m]
    · simp [goodProd, good, rate,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hq, v, m]
  rw [hgoodRate]
  exact hrateMeas.indicator hgoodProd

/-- The exact `2p` Gaussian moment norm of the norm-good rate is measurable
in running time.  This is product measurability on the same time-sample
window, followed by integration against `Gauss.P d`. -/
private theorem measurable_momNorm_normGoodJointRate_on_window
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ} {N k p : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (mesh D) N)
    (a : LoopArg (d.L N) 2) (hp : 1 ≤ p) :
    Measurable (fun r : Icc (s N) (cutNetPt s (mesh D) N k) =>
      MomentDuhamel.momNorm (Gauss.P d) (2 * p)
        (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N k a r.1)) := by
  classical
  let S := Icc (s N) (cutNetPt s (mesh D) N k)
  let Z : S → Ω d → ℝ := fun r ω =>
    APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
      E D deltaWeight s t N k a r.1 ω
  have hZ : Measurable (fun q : S × Ω d => Z q.1 q.2) := by
    exact measurable_normGoodJointRate_on_window hE hs0 hst ht1 hN hk a
  have hpow : Measurable (fun q : S × Ω d => |Z q.1 q.2| ^ (2 * p)) :=
    (continuous_abs.measurable.comp hZ).pow_const (2 * p)
  have hInt : StronglyMeasurable (fun r : S =>
      ∫ ω, |Z r ω| ^ (2 * p) ∂(Gauss.P d)) :=
    hpow.stronglyMeasurable.integral_prod_right'
  have hexp : 0 < (1 : ℝ) / ((2 * p : ℕ) : ℝ) := by
    positivity
  have hpowMeas : Measurable (fun r : S =>
      (∫ ω, |Z r ω| ^ (2 * p) ∂(Gauss.P d)) ^
        ((1 : ℝ) / ((2 * p : ℕ) : ℝ))) :=
    (Real.continuous_rpow_const hexp.le).measurable.comp hInt.measurable
  change Measurable (fun r : S =>
    MomentDuhamel.momNorm (Gauss.P d) (2 * p) (Z r))
  simpa [MomentDuhamel.momNorm, Z, S, Nat.cast_mul] using hpowMeas

/-- For every fixed `p ≥ 1`, the literal T1201 norm-good cross budget is
interval-integrable on all active closed target cells, eventually in `N`.
The proof includes `r = 0`, `k = 0`, and degenerate cells. -/
theorem eventually_intervalIntegrable_normGoodCrossBudget
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a)
          volume (s N) (cutNetPt s (mesh D) N k) := by
  have hProduct :=
    APrimeGeneralMovingJointGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hEnvelope :=
    APrimeGeneralMovingJointGlobalPoly.eventually_jointEnvelope_le_rpow hD
  filter_upwards [hProduct, hEnvelope, eventually_ge_atTop 1]
    with N hProductN hEnvelopeN hN
  have hNpos : 0 < N := by omega
  haveI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  intro k hk a
  let v := cutNetPt s (mesh D) N k
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
    APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
      E D deltaWeight s t N k p a r.1
  have hbudgetMeas : Measurable budget := by
    have hnorm := measurable_momNorm_normGoodJointRate_on_window
      (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1 hNpos hk a hp
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
        (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N k a r.1))
    exact hcoeff.mul hnorm
  have hbudget_le : ∀ r : S, ‖budget r‖ ≤ K * sing r.1 := by
    intro r
    have hr0 : 0 ≤ r.1 := (hs0 N).trans r.2.1
    have hbudget0 : 0 ≤ budget r := by
      change 0 ≤
        (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r.1)) *
          MomentDuhamel.momNorm (Gauss.P d) (2 * p)
            (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
              E D deltaWeight s t N k a r.1)
      exact mul_nonneg
        (div_nonneg
          (by
            unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
            positivity)
          (by positivity))
        (MomentDuhamel.momNorm_nonneg _ _ _)
    by_cases hrpos : 0 < r.1
    · let m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N
      let Y : Ω d → ℝ := fun ω =>
        APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k m
          Step2.sigPM a v r.1 ω
      have hProduct : ∀ ω : Ω d,
          APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
              (mesh D) N k m ω *
            √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a
              (s N) v r.1 ω) ≤
            APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
        intro ω
        simpa [m] using hProductN k hk Step2.sigPM a r.1 r.2 ω
      have hEnv0 :
          0 ≤ APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N :=
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope_nonneg D N
      have hY0 : ∀ ω, 0 ≤ Y ω := by
        intro ω
        exact APrimeCrossJointSplit.jointRate_nonneg d E D deltaWeight s
          (mesh D) N k m Step2.sigPM a v r.1 hNpos ω
      have hYbound : ∀ ω, |Y ω| ≤
          APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
        intro ω
        change |APrimeCrossJointSplit.jointRate d E D deltaWeight s
          (mesh D) N k m Step2.sigPM a v r.1 ω| ≤ _
        rw [abs_of_nonneg (hY0 ω)]
        by_cases htrans : ω ∈ APrimeCrossJointSplit.transition d E D
            deltaWeight s (mesh D) N k m
        · simpa only [Y, APrimeCrossJointSplit.jointRate,
            Set.indicator_of_mem htrans] using hProduct ω
        · simpa only [Y, APrimeCrossJointSplit.jointRate,
            Set.indicator_of_notMem htrans] using hEnv0
      let Z : Ω d → ℝ := fun ω =>
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
          E D deltaWeight s t N k a r.1 ω
      have hZ0 : ∀ ω, 0 ≤ Z ω := by
        intro ω
        by_cases hgood : ω ∈ APrimeGeneralMovingGoodMesh.good N
        · simpa [Z,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hgood]
            using hY0 ω
        · simp [Z,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hgood]
      have hZbound : ∀ ω, |Z ω| ≤
          APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
        intro ω
        by_cases hgood : ω ∈ APrimeGeneralMovingGoodMesh.good N
        · simpa [Z,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hgood,
            Y] using hYbound ω
        · simp [Z,
            APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate, hgood,
            hEnv0]
      let C : ℝ :=
        APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N ^ (2 * p)
      have hZpowMeas : Measurable (fun ω : Ω d => |Z ω| ^ (2 * p)) := by
        -- Obtain sample measurability by fixing the time coordinate in the
        -- already established product-measurable family.
        have hprod := measurable_normGoodJointRate_on_window
          (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1 hNpos hk a
        have hZmeas : Measurable Z := by
          have hh : Measurable (fun ω : Ω d =>
              APrimeGeneralMovingCrossBudgetGoodReduction.normGoodJointRate
                E D deltaWeight s t N k a r.1 ω) := by
            convert hprod.comp (measurable_const.prodMk measurable_id) using 1
            ext ω <;> rfl
          simpa [Z] using hh
        exact (continuous_abs.measurable.comp hZmeas).pow_const (2 * p)
      have hZpowBound : ∀ ω : Ω d, |Z ω| ^ (2 * p) ≤ C := by
        intro ω
        simpa [C] using pow_le_pow_left₀ (abs_nonneg _) (hZbound ω) (2 * p)
      have hZint : Integrable (fun ω : Ω d => |Z ω| ^ (2 * p)) (Gauss.P d) := by
        apply Integrable.of_bound hZpowMeas.aestronglyMeasurable C
        filter_upwards [] with ω
        change ‖|Z ω| ^ (2 * p)‖ ≤ C
        rw [Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact hZpowBound ω
      have hConstInt : Integrable (fun _ : Ω d => C) (Gauss.P d) :=
        integrable_const _
      have hIntegral := integral_mono hZint hConstInt hZpowBound
      have hConstIntegral :
          (∫ _ω : Ω d, C ∂(Gauss.P d)) = C := by
        simp [integral_const, C]
      have hMoment :
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤
            APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
        unfold MomentDuhamel.momNorm
        have hInt0 : 0 ≤ ∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d) :=
          integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
        calc
          (∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d)) ^
              ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) ≤
              C ^ ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) :=
            Real.rpow_le_rpow hInt0 (hIntegral.trans_eq hConstIntegral)
              (by positivity)
          _ = APrimeGeneralMovingJointGlobalPoly.jointEnvelope D N := by
            rw [one_div]
            have hq : 2 * p ≠ 0 := by omega
            exact Real.pow_rpow_inv_natCast hEnv0 hq
      have hMomentPoly :
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤
            (N : ℝ) ^ (2 * D + 17) := hMoment.trans hEnvelopeN
      have hCoeffNonneg :
          0 ≤ APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √r.1) := by
        unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
        have hpR : 0 < (p : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hp)
        exact div_nonneg (by positivity) (by positivity)
      have hbudgetPoly : budget r ≤
          APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √r.1) * (N : ℝ) ^ (2 * D + 17) := by
        change
          (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √r.1)) *
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤ _
        exact mul_le_mul_of_nonneg_left hMomentPoly hCoeffNonneg
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
      have hle : budget r ≤ K * sing r.1 := hbudgetPoly.trans_eq hrewrite
      rw [Real.norm_eq_abs, abs_of_nonneg hbudget0]
      exact hle
    · have hrEq : r.1 = 0 := by linarith
      have hbudget0 : budget r = 0 := by
        simp [budget,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget, hrEq]
      rw [hbudget0, Real.norm_eq_abs, abs_zero]
      simp [sing, hrEq]
  have hbudgetSub : Integrable budget μ :=
    hmajorSub.mono' hbudgetMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbudget_le)
  have hbudgetOn : IntegrableOn
      (APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
        E D deltaWeight s t N k p a) (Icc (s N) v) volume := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).2 hbudgetSub
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).2 hbudgetOn

/-- The explicit T1185 nondegenerate positive-time active-`k=2` witness is
re-exported unchanged. -/
noncomputable abbrev nondegenerate_active_k2_witness :=
  APrimeGeneralMovingCrossBudgetNormBadIntegral.nondegenerate_active_k2_witness

#print axioms measurable_normGoodJointRate_on_window
#print axioms measurable_momNorm_normGoodJointRate_on_window
#print axioms eventually_intervalIntegrable_normGoodCrossBudget
#print axioms nondegenerate_active_k2_witness

end
end RBM.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
