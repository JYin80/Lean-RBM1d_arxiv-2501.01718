/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral

/-!
# T1285: all-order norm-good cross integral with a strict exponent

For each fixed `p ≥ 1`, integrate the literal norm-good T1201 budget over the
prefix ending at any active T995 cell.  T1277 supplies its pointwise split;
T1245 bounds the literal T1029 cross profile with exponent `13δ/640`, which
is strictly below `δ/8`.
-/

namespace RBM.APrimeGeneralMovingNormGoodCrossAllOrdersStrictExponent

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.APrimeGeneralMovingCrossBudgetGoodReduction
open RBM.APrimeGeneralMovingCrossEnvelopeIntegral
open RBM.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise
open RBM.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
open RBM.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- T995's nondegenerate same-event witness, including positive actual smooth
weight on an eventually active cell. -/
noncomputable abbrev nondegenerate_scheduled_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

set_option maxHeartbeats 1000000 in
-- The imported pointwise inputs carry several nested eventual-event arguments.
/-- For each fixed `p ≥ 1`, the literal T1201 norm-good cross budget has an
integrated bound on every active T995 prefix, including `k = 0`.  The main
term retains the exact endpoint transport `ratR(v)⁻²`; the strict exponent
comes from `13δ/640 < δ/8`. -/
theorem eventually_integral_normGoodCrossBudget_le_delta_eighth
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ u in (s N)..v,
            normGoodCrossBudget E D
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k p a u) ≤
            (15 * (p : ℝ) / 2) *
                APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ)^(δ / 8) * (etaT E (s N))⁻¹ *
                Step2Moment.ratR E s N v^(-(2 : ℝ)) *
                (Real.sqrt v - Real.sqrt (s N)) +
              (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
                (Real.sqrt v - Real.sqrt (s N)) := by
  have hdeltaWeight :
      0 ≤ APrimeGeneralMovingSlotLossSchedule.deltaWeight δ := by
    dsimp [APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hpoint :=
    eventually_normGoodCrossBudget_le_crossProfile_add_bad_allOrders_pointwise
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hprofile :=
    eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (c := c) (s := s) (t := t) (δ := δ)
      hE (by linarith) hs0 hst ht1 hc hreg hδ hδsmall
  have hintegrable :=
    eventually_intervalIntegrable_normGoodCrossBudget
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hpoint, hprofile, hintegrable, eventually_ge_atTop 1]
    with N hpointN hprofileN hintegrableN hN
  have hNnat : 1 ≤ N := by omega
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < N := by linarith
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 0 < p by omega)
  have hAlpha : (13 * δ / 640 : ℝ) < δ / 8 := by
    nlinarith [hδ]
  have hNpow : (N : ℝ)^(13 * δ / 640) ≤ (N : ℝ)^(δ / 8) :=
    Real.rpow_le_rpow_of_exponent_le hN hAlpha.le
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hsv : s N ≤ v := hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hv0 : 0 ≤ v := (hs0 N).trans hsv
  have hEtaS : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hEtaInv0 : 0 ≤ (etaT E (s N))⁻¹ := inv_nonneg.mpr hEtaS.le
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE ((hst N).trans_lt (ht1 N)) hv1
  have hRpow0 : 0 ≤ Step2Moment.ratR E s N v^(-(2 : ℝ)) :=
    Real.rpow_nonneg hRpos.le _
  have hGap0 : 0 ≤ Real.sqrt v - Real.sqrt (s N) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  let K : ℝ :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst
  let alpha := 13 * δ / 640
  let R := Step2Moment.ratR E s N v
  let Cprof := (15 * (p : ℝ) / 4) *
    (K * (N : ℝ)^alpha * (etaT E (s N))⁻¹ * R^(-(2 : ℝ)))
  let Cbad := (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)
  let Cgood := Cprof + Cbad
  have hKpos : 0 < K := by
    dsimp [K]
    exact APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hCprof0 : 0 ≤ Cprof := by
    dsimp [Cprof, K, R, alpha]
    positivity
  have hCbad0 : 0 ≤ Cbad := by
    dsimp [Cbad]
    positivity
  have hCgood0 : 0 ≤ Cgood := add_nonneg hCprof0 hCbad0
  have hgoodPointwise :
      ∀ u ∈ Icc (s N) v,
        normGoodCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u ≤ Cgood / Real.sqrt u := by
    intro u hu
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    by_cases huPos : 0 < u
    · have hgood := hpointN k hk a u hu huPos
      have hprof := hprofileN k hk a u hu huPos
      have hprof' :
          APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
            K * (N : ℝ)^alpha * (etaT E (s N))⁻¹ *
              R^(-(2 : ℝ)) / Real.sqrt u := by
        simpa [K, alpha, R, v, mesh] using hprof
      have hprofScaled :
          (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
            Cprof / Real.sqrt u := by
        calc
          _ ≤ (15 * (p : ℝ) / 4) *
                (K * (N : ℝ)^alpha * (etaT E (s N))⁻¹ *
                  R^(-(2 : ℝ)) / Real.sqrt u) :=
            mul_le_mul_of_nonneg_left hprof' (by positivity)
          _ = Cprof / Real.sqrt u := by
            dsimp [Cprof, K, R, alpha]
            ring
      calc
        _ ≤ (15 * (p : ℝ) / 4) *
              APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u +
              (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt u := hgood
        _ ≤ Cprof / Real.sqrt u + Cbad / Real.sqrt u :=
            add_le_add hprofScaled (le_of_eq rfl)
        _ = Cgood / Real.sqrt u := by
            dsimp [Cgood]
            rw [add_div]
    · have huEq : u = 0 := le_antisymm (le_of_not_gt huPos) hu0
      have hgood0 :
          normGoodCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a u = 0 := by
        simp [normGoodCrossBudget,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget, huEq]
      have hgood0' :
          normGoodCrossBudget E D
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            s t N k p a 0 = 0 := by
        rw [huEq] at hgood0
        exact hgood0
      simp [huEq, hgood0']
  have hgoodInt := hintegrableN k hk a
  have hEnvelopeInt :
      IntervalIntegrable (fun u => Cgood / Real.sqrt u) volume (s N) v :=
    intervalIntegrable_invSqrtEnvelope Cgood (s N) v (hs0 N) hsv
  have hgoodIntegral :
      (∫ u in (s N)..v,
        normGoodCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u) ≤
        2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ ∫ u in (s N)..v, Cgood / Real.sqrt u :=
        intervalIntegral.integral_mono_on hsv hgoodInt hEnvelopeInt hgoodPointwise
      _ = 2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) :=
        integral_invSqrtEnvelope Cgood (s N) v (hs0 N) hsv
  have hmainFactor0 :
      0 ≤ (15 * (p : ℝ) / 2) * K *
        (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
        (Real.sqrt v - Real.sqrt (s N)) := by
    positivity
  have hmain :
      2 * Cprof * (Real.sqrt v - Real.sqrt (s N)) ≤
        (15 * (p : ℝ) / 2) * K * (N : ℝ)^(δ / 8) *
          (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ = ((15 * (p : ℝ) / 2) * K *
            (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N))) *
            (N : ℝ)^alpha := by
              dsimp [Cprof, K, R, alpha]
              ring
      _ ≤ ((15 * (p : ℝ) / 2) * K *
            (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
            (Real.sqrt v - Real.sqrt (s N))) *
            (N : ℝ)^(δ / 8) :=
          mul_le_mul_of_nonneg_left hNpow hmainFactor0
      _ = _ := by
        ring
  have hsplit : 2 * Cgood * (Real.sqrt v - Real.sqrt (s N)) =
      2 * Cprof * (Real.sqrt v - Real.sqrt (s N)) +
      2 * Cbad * (Real.sqrt v - Real.sqrt (s N)) := by
    dsimp [Cgood]
    ring
  have hbad :
      2 * Cbad * (Real.sqrt v - Real.sqrt (s N)) =
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (Real.sqrt v - Real.sqrt (s N)) := by
    dsimp [Cbad]
    ring
  have hfinal := hgoodIntegral.trans (le_of_eq hsplit)
  have hresult :
      (∫ u in (s N)..v,
        normGoodCrossBudget E D
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s t N k p a u) ≤
        (15 * (p : ℝ) / 2) * K * (N : ℝ)^(δ / 8) *
          (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ 2 * Cprof * (Real.sqrt v - Real.sqrt (s N)) +
          2 * Cbad * (Real.sqrt v - Real.sqrt (s N)) := hfinal
      _ ≤ (15 * (p : ℝ) / 2) * K * (N : ℝ)^(δ / 8) *
          (etaT E (s N))⁻¹ * R^(-(2 : ℝ)) *
          (Real.sqrt v - Real.sqrt (s N)) +
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (Real.sqrt v - Real.sqrt (s N)) :=
        add_le_add hmain (le_of_eq hbad)
  simpa [v, mesh, K, R] using hresult

#print axioms eventually_integral_normGoodCrossBudget_le_delta_eighth
#print axioms nondegenerate_scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingNormGoodCrossAllOrdersStrictExponent
