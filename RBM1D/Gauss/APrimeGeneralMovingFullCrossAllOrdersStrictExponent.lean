/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetGoodIntegralReduction
import RBM1D.Gauss.APrimeGeneralMovingNormGoodCrossAllOrdersPointwise
import RBM1D.Gauss.APrimeGeneralMovingCrossProfilePointwiseMicroscopic
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossEnvelopeIntegral
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1287: all-order full positive-time cross integral at strict δ/8

For each fixed `p ≥ 1`, the literal unrestricted positive-time full cross
budget is integrated on every active T995 target endpoint. The strict profile
term keeps the terminal `ratR(v)⁻²`; the norm-good pointwise payment and the
full-to-norm-good payment remain as separate inverse-`N` terms.
-/

namespace RBM.APrimeGeneralMovingFullCrossAllOrdersStrictExponent

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The main fixed-`p`, fixed-energy coefficient in T1287. -/
noncomputable def fullCrossIntegralConst (E : ℝ) (p : ℕ) : ℝ :=
  (15 * (p : ℝ) / 2) *
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst /
      (mE E).im

theorem fullCrossIntegralConst_pos {E : ℝ} (hE : |E| < 2) {p : ℕ}
    (hp : 1 ≤ p) : 0 < fullCrossIntegralConst E p := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  unfold fullCrossIntegralConst
  exact div_pos
    (mul_pos (by positivity : 0 < (15 : ℝ) * (p : ℝ) / 2)
      (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos))
    (mE_im_pos hE)

private theorem eta_inv_mul_sqrt_gap_le
    {E s v : ℝ} (hE : |E| < 2) (hs : 0 ≤ s) (hsv : s ≤ v)
    (hv : v < 1) :
    (etaT E s)⁻¹ * (Real.sqrt v - Real.sqrt s) ≤ (mE E).im⁻¹ := by
  have hs1 : s ≤ 1 := hsv.trans hv.le
  have hsqrtS1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1
  have hsSqrt : s ≤ Real.sqrt s := by
    have hnonneg : 0 ≤ Real.sqrt s * (1 - Real.sqrt s) :=
      mul_nonneg (Real.sqrt_nonneg s) (by linarith [hsqrtS1])
    nlinarith [Real.sq_sqrt hs]
  have hvSqrt1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv.le
  have hgap : Real.sqrt v - Real.sqrt s ≤ 1 - s := by linarith
  have h1s : 0 < 1 - s := by linarith
  have him : 0 < (mE E).im := mE_im_pos hE
  have heta : etaT E s = (1 - s) * (mE E).im := Step2.etaT_eq E s
  have hratio : (Real.sqrt v - Real.sqrt s) / (1 - s) ≤ 1 := by
    rw [div_le_iff₀ h1s]
    nlinarith [hgap]
  calc
    (etaT E s)⁻¹ * (Real.sqrt v - Real.sqrt s) =
        (mE E).im⁻¹ * ((Real.sqrt v - Real.sqrt s) / (1 - s)) := by
      rw [heta]
      field_simp [ne_of_gt him, ne_of_gt h1s]
      <;> ring
    _ ≤ (mE E).im⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr him.le)
    _ = (mE E).im⁻¹ := by ring

set_option maxHeartbeats 1000000 in
/-- For each fixed `p ≥ 1`, one eventual cutoff works for every active T995
target endpoint (including `k = 0`) and every output loop argument. The
literal unrestricted positive-time full cross budget is bounded by a strict
`δ/8` endpoint-scale term and the two original inverse-`N` payments. -/
theorem eventually_integral_positiveTimeCrossBudget_le_delta_eighth
    {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100))
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        k ≤ cutNetTop s t (mesh D) N →
        ∀ a : LoopArg (d.L N) 2,
          let v := cutNetPt s (mesh D) N k
          (∫ u in (s N)..v,
            APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
              s t N k p a u) ≤
            C * (N : ℝ)^(δ / 8) *
                Step2Moment.ratR E s N v ^ (-(2 : ℝ)) +
              (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
                (Real.sqrt v - Real.sqrt (s N)) +
              (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
                (Real.sqrt v - Real.sqrt (s N)) := by
  let C : ℝ := fullCrossIntegralConst E p
  have hCpos : 0 < C := by
    exact fullCrossIntegralConst_pos hE hp
  refine ⟨C, hCpos, ?_⟩
  let deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ
  have hdeltaWeight : 0 ≤ deltaWeight := by
    dsimp [deltaWeight, APrimeGeneralMovingSlotLossSchedule.deltaWeight]
    positivity
  have hReduced :=
    APrimeGeneralMovingCrossBudgetGoodIntegralReduction.eventually_integral_positiveTimeCrossBudget_le_normGood_add_error
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hGoodInt :=
    APrimeGeneralMovingCrossBudgetNormGoodTimeIntegrable.eventually_intervalIntegrable_normGoodCrossBudget
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hNormPoint :=
    APrimeGeneralMovingNormGoodCrossAllOrdersPointwise.eventually_normGoodCrossBudget_le_crossProfile_add_bad_allOrders_pointwise
      (E := E) (D := D) (c := c) (δ := δ) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hB hδ hδsmall p hp
  have hProfilePoint :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.eventually_pointwise_T1029_crossProfile_le_microscopic
      (E := E) (D := D) (c := c) (s := s) (t := t)
      hE (by linarith : 0 ≤ D) hs0 hst ht1 hc hreg hδ hδsmall
  filter_upwards [hReduced, hGoodInt, hNormPoint, hProfilePoint,
      eventually_ge_atTop 1]
    with N hReducedN hGoodIntN hNormPointN hProfilePointN hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro k hk a
  let v := cutNetPt s (mesh D) N k
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, mesh]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hsv : s N ≤ v := hv.1
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hsv.trans_lt hv1) hv1
  have hsqrtGap : 0 ≤ Real.sqrt v - Real.sqrt (s N) := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hsv)
  have hEtaGap := eta_inv_mul_sqrt_gap_le hE (hs0 N) hsv hv1
  let rpowV := Step2Moment.ratR E s N v ^ (-(2 : ℝ))
  let alpha : ℝ := 13 * δ / 640
  let profCoeff : ℝ :=
    (15 * (p : ℝ) / 4) *
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
      (N : ℝ)^alpha * (etaT E (s N))⁻¹ * rpowV
  let badCoeff : ℝ := (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ)
  let profEnvelope : ℝ → ℝ := fun u => profCoeff / Real.sqrt u
  let badEnvelope : ℝ → ℝ := fun u => badCoeff / Real.sqrt u
  have hKpt : 0 <
      APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst :=
    APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst_pos
  have hEtaS : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hNpowNonneg : 0 ≤ (N : ℝ)^alpha :=
    Real.rpow_nonneg (by exact_mod_cast hNpos.le) _
  have hRpowNonneg : 0 ≤ rpowV := by
    dsimp [rpowV]
    exact Real.rpow_nonneg hRpos.le _
  have hProfCoeff : 0 ≤ profCoeff := by
    dsimp [profCoeff, rpowV, alpha]
    positivity
  have hBadCoeff : 0 ≤ badCoeff := by
    dsimp [badCoeff]
    positivity
  have hPointwise : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k p a u ≤ profEnvelope u + badEnvelope u := by
    intro u hu
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    by_cases huPos : 0 < u
    · have hGood := hNormPointN k hk a u hu huPos
      have hProfile := hProfilePointN k hk a u hu huPos
      have hProfileTerm :
          (15 * (p : ℝ) / 4) *
              RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                (APrimeGeneralMovingSlotLossSchedule.tauG δ) deltaWeight
                (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
            profCoeff / Real.sqrt u := by
        have hcoef : 0 ≤ (15 * (p : ℝ) / 4) := by positivity
        change
          RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ) deltaWeight
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u ≤
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
              (N : ℝ)^alpha * (etaT E (s N))⁻¹ * rpowV / Real.sqrt u at hProfile
        calc
          _ ≤ (15 * (p : ℝ) / 4) *
              (APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
                (N : ℝ)^alpha * (etaT E (s N))⁻¹ * rpowV / Real.sqrt u) :=
            mul_le_mul_of_nonneg_left hProfile hcoef
          _ = profCoeff / Real.sqrt u := by
            dsimp [profCoeff]
            ring
      calc
        _ ≤
            (15 * (p : ℝ) / 4) *
                RBM.APrimeGeneralMovingCrossProfileSlot.crossProfile E D s t
                  (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
                  (APrimeGeneralMovingSlotLossSchedule.tauG δ) deltaWeight
                  (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u +
              (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt u := hGood
        _ ≤ profCoeff / Real.sqrt u +
              (15 * (p : ℝ) / 8) * (N : ℝ)^(-1 : ℝ) / Real.sqrt u :=
          add_le_add hProfileTerm le_rfl
        _ = profEnvelope u + badEnvelope u := by
          dsimp [profEnvelope, badEnvelope, badCoeff]
          <;> ring
    · have huEq : u = 0 := le_antisymm (le_of_not_gt huPos) hu0
      have hGoodZero :
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
              E D deltaWeight s t N k p a u = 0 := by
        simp [APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget, huEq]
      rw [hGoodZero]
      simp [profEnvelope, badEnvelope, huEq]
  have hProfInt : IntervalIntegrable profEnvelope volume (s N) v := by
    exact APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      profCoeff (s N) v (hs0 N) hsv
  have hBadInt : IntervalIntegrable badEnvelope volume (s N) v := by
    exact APrimeGeneralMovingCrossEnvelopeIntegral.intervalIntegrable_invSqrtEnvelope
      badCoeff (s N) v (hs0 N) hsv
  have hGoodIntegralInt := hGoodIntN k hk a
  have hEnvInt : IntervalIntegrable (fun u => profEnvelope u + badEnvelope u)
      volume (s N) v := hProfInt.add hBadInt
  have hMono := intervalIntegral.integral_mono_on hsv hGoodIntegralInt hEnvInt hPointwise
  have hProfEval :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      profCoeff (s N) v (hs0 N) hsv
  have hBadEval :=
    APrimeGeneralMovingCrossEnvelopeIntegral.integral_invSqrtEnvelope
      badCoeff (s N) v (hs0 N) hsv
  have hProfBound :
      (∫ u in (s N)..v, profEnvelope u) ≤
        C * (N : ℝ)^(δ / 8) * rpowV := by
    have hFactor0 : 0 ≤
        (15 * (p : ℝ) / 2) *
          APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
          (N : ℝ)^alpha * rpowV := by
      positivity
    have hConst0 : 0 ≤ C := le_of_lt hCpos
    have hExponent : alpha ≤ δ / 8 := by
      dsimp [alpha]
      nlinarith [hδ]
    have hNpow : (N : ℝ)^alpha ≤ (N : ℝ)^(δ / 8) :=
      Real.rpow_le_rpow_of_exponent_le hNreal hExponent
    have hRpow0 : 0 ≤ rpowV := by
      dsimp [rpowV]
      exact Real.rpow_nonneg hRpos.le _
    calc
      _ =
          (15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ)^alpha * rpowV *
              ((etaT E (s N))⁻¹ *
                (Real.sqrt v - Real.sqrt (s N))) := by
        rw [hProfEval]
        dsimp [profEnvelope, profCoeff]
        ring
      _ ≤
          (15 * (p : ℝ) / 2) *
            APrimeGeneralMovingCrossProfilePointwiseMicroscopic.crossProfilePointwiseConst *
            (N : ℝ)^alpha * rpowV * (mE E).im⁻¹ :=
        mul_le_mul_of_nonneg_left hEtaGap hFactor0
      _ = C * (N : ℝ)^alpha * rpowV := by
        dsimp [C, fullCrossIntegralConst]
        ring
      _ ≤ C * (N : ℝ)^(δ / 8) * rpowV := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNpow hConst0) hRpow0
  have hBadIntegralEq :
      (∫ u in (s N)..v, badEnvelope u) =
        (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
          (Real.sqrt v - Real.sqrt (s N)) := by
    rw [hBadEval]
    dsimp [badEnvelope, badCoeff]
    ring
  have hGoodBound :
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
          E D deltaWeight s t N k p a u) ≤
        C * (N : ℝ)^(δ / 8) * rpowV +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) := by
    calc
      _ ≤ ∫ u in (s N)..v, profEnvelope u + badEnvelope u := hMono
      _ = (∫ u in (s N)..v, profEnvelope u) +
            (∫ u in (s N)..v, badEnvelope u) :=
        intervalIntegral.integral_add hProfInt hBadInt
      _ ≤ C * (N : ℝ)^(δ / 8) * rpowV +
            (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
              (Real.sqrt v - Real.sqrt (s N)) := by
        rw [hBadIntegralEq]
        exact add_le_add hProfBound le_rfl
  have hReducedBound := hReducedN k hk a
  change
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a u) ≤
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a u) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) at hReducedBound
  change
      (∫ u in (s N)..v,
        APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
          E D deltaWeight s t N k p a u) ≤
        C * (N : ℝ)^(δ / 8) * rpowV +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N))
  calc
    _ ≤
        (∫ u in (s N)..v,
          APrimeGeneralMovingCrossBudgetGoodReduction.normGoodCrossBudget
            E D deltaWeight s t N k p a u) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) := hReducedBound
    _ ≤
        (C * (N : ℝ)^(δ / 8) * rpowV +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N))) +
          (15 * (p : ℝ) / 4) * (N : ℝ)^(-1 : ℝ) *
            (Real.sqrt v - Real.sqrt (s N)) :=
      add_le_add hGoodBound le_rfl
    _ = _ := by ring

/-! The inherited T995 same-sample common-event witness makes the scheduled
window and its positive actual smooth weight jointly nondegenerate. -/

noncomputable abbrev nondegenerate_scheduled_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms fullCrossIntegralConst_pos
#print axioms eventually_integral_positiveTimeCrossBudget_le_delta_eighth
#print axioms nondegenerate_scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingFullCrossAllOrdersStrictExponent
