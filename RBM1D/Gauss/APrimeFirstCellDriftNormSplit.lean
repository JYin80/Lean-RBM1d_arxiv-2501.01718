/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeBadSplit
import RBM1D.Gauss.APrimeFirstCellDriftGlobalPoly
import RBM1D.Gauss.APrimeFirstCellDriftWeightedGood
import RBM1D.Gauss.APrimeFirstCellSampleRegularity

/-!
# T460: support-aware weighted drift moment split on the first cell

The favorable pointwise input is imposed only after multiplication by the
actual smooth weight.  This is the form produced by T456: where the weight
vanishes the root-scaled random variable is literally zero, while on positive
support the weight can be cancelled before applying the usual event split.
-/

namespace RBM.APrimeFirstCellDriftNormSplit

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

variable {Omega : Type*} [MeasurableSpace Omega]
  {P0 : Measure Omega} [IsProbabilityMeasure P0]

/-- Root-scaled event split when the favorable estimate is known only after
multiplication by the weight.  The zero-weight branch is exactly zero. -/
theorem weighted_norm_le_of_weighted_event {q : Nat} (hq : q ≠ 0)
    {W Z : Omega -> Real}
    (hW0 : ∀ omega, 0 <= W omega) (hW1 : ∀ omega, W omega <= 1)
    (hZi : Integrable (fun omega => W omega * |Z omega| ^ q) P0)
    {E : Set Omega} (hE : MeasurableSet E) {good Env pr : Real}
    (hgood : 0 <= good) (hEnv : 0 <= Env) (hpr : 0 <= pr)
    (hZgood : ∀ omega ∈ E, W omega * |Z omega| <= W omega * good)
    (hZall : ∀ omega, |Z omega| <= Env)
    (hP : (P0 Eᶜ).toReal <= pr) :
    (∫ omega, W omega * |Z omega| ^ q ∂P0) ^ ((1 : Real) / q) <=
      good + Env * pr ^ ((1 : Real) / q) := by
  let Zr : Omega -> Real := fun omega => W omega ^ ((1 : Real) / q) * Z omega
  have hZi' : Integrable (fun omega => |Zr omega| ^ q) P0 := by
    apply hZi.congr
    filter_upwards [] with omega
    dsimp [Zr]
    symm
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 omega) _), mul_pow]
    have he : ((1 : Real) / q) * q = 1 := by
      have hq' : (q : Real) ≠ 0 := by exact_mod_cast hq
      field_simp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hW0 omega), he, Real.rpow_one]
  have hroot : ∀ omega, W omega ^ ((1 : Real) / q) <= 1 := by
    intro omega
    calc
      W omega ^ ((1 : Real) / q) <= (1 : Real) ^ ((1 : Real) / q) :=
        Real.rpow_le_rpow (hW0 omega) (hW1 omega) (by positivity)
      _ = 1 := by simp
  have hZrgood : ∀ omega ∈ E, |Zr omega| <= good := by
    intro omega homega
    by_cases hWz : W omega = 0
    · have hq' : (q : Real) ≠ 0 := by exact_mod_cast hq
      have hexp : (1 : Real) / (q : Real) ≠ 0 := div_ne_zero one_ne_zero hq'
      dsimp [Zr]
      rw [hWz, Real.zero_rpow hexp, zero_mul, abs_zero]
      exact hgood
    · have hWpos : 0 < W omega := lt_of_le_of_ne (hW0 omega) (Ne.symm hWz)
      have hZA : |Z omega| <= good := by
        nlinarith [hZgood omega homega]
      dsimp [Zr]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 omega) _)]
      calc
        W omega ^ ((1 : Real) / q) * |Z omega| <= 1 * |Z omega| :=
          mul_le_mul_of_nonneg_right (hroot omega) (abs_nonneg _)
        _ = |Z omega| := one_mul _
        _ <= good := hZA
  have hZrall : ∀ omega, |Zr omega| <= Env := by
    intro omega
    dsimp [Zr]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 omega) _)]
    calc
      W omega ^ ((1 : Real) / q) * |Z omega| <= 1 * |Z omega| :=
        mul_le_mul_of_nonneg_right (hroot omega) (abs_nonneg _)
      _ = |Z omega| := one_mul _
      _ <= Env := hZall omega
  have hbase := RBM.Gauss.momNorm_le_affine_on_event (P := P0) hq
    (Y := fun _ => (0 : Real)) (Z := Zr) (Ξ := E)
    (c := 0) (d := good) (Env := Env) (pr := pr)
    (by simp) (by simp) hZi' hE (by simp) hgood hEnv hpr
    (by intro omega homega; simpa using hZrgood omega homega) hZrall hP
  simp only [zero_mul, zero_add] at hbase
  exact (APrimeBadSplit.momNorm_root_eq (P := P0) hq hW0).symm.le.trans hbase

/-- The support-aware version of the drift estimate used by the first-cell
specialization. -/
theorem drift_norm_le_of_weighted_event {p : Nat} (hp : 1 <= p)
    {W G : Omega -> Real}
    (hW0 : ∀ omega, 0 <= W omega) (hW1 : ∀ omega, W omega <= 1)
    (hGi : Integrable (fun omega => W omega * |G omega| ^ (2 * p)) P0)
    {E : Set Omega} (hE : MeasurableSet E) {A Env pr : Real}
    (hA : 0 <= A) (hEnv : 0 <= Env) (hpr : 0 <= pr)
    (hGgood : ∀ omega ∈ E, W omega * |G omega| <= W omega * A)
    (hGall : ∀ omega, |G omega| <= Env)
    (hP : (P0 Eᶜ).toReal <= pr) :
    momNormW P0 W p G <= A + Env * pr ^ ((1 : Real) / (2 * p)) := by
  have hq : 2 * p ≠ 0 := by omega
  simpa [momNormW, Nat.cast_mul] using
    weighted_norm_le_of_weighted_event (P0 := P0) hq hW0 hW1 hGi hE
      hA hEnv hpr hGgood hGall hP

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The exact actual first-cell drift norm estimate.  The moment order is an
argument of the property and is therefore fixed before the eventual cutoff. -/
def actualDriftNormSplit (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∀ k : Nat, 1 <= k ->
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      let v := APrimeFirstCellSampleRegularity.endpoint N k
      ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
        momNormW (P d)
            (APrimeFirstCellSampleRegularity.weight tauPrime delta p N k) p
            (APrimeFirstCellSampleRegularity.G N k a r) <=
          APrimeFirstCellDriftCoefficient.endpointCoefficient
              delta (2 * alpha) N v r +
            APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) *
              ((P d)
                (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
                  tauPrime delta alpha N)ᶜ).toReal ^
                ((1 : Real) / (2 * p))

private theorem endpointCoefficient_nonneg {N : Nat} (hN : 0 < N)
    {delta alpha v r : Real} (hr0 : 0 <= r) (hrv : r <= v)
    (hvhalf : v <= 1 / 2) :
    0 <= APrimeFirstCellDriftCoefficient.endpointCoefficient
      delta (2 * alpha) N v r := by
  have hv0 : 0 <= v := hr0.trans hrv
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hr1 : r < 1 := hrv.trans_lt hv1
  have heta0 : 0 < etaT 0 0 := etaT_pos_of_lt_one (by norm_num) (by norm_num)
  have hetar : 0 < etaT 0 r := etaT_pos_of_lt_one (by norm_num) hr1
  have hetav : 0 < etaT 0 v := etaT_pos_of_lt_one (by norm_num) hv1
  have hxr : 0 < APrimeFirstCellLoopCap.xRate r := by
    unfold APrimeFirstCellLoopCap.xRate
    positivity
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    positivity
  have hAv : 0 < APrimeFirstCellLoopCap.endpointScale N v := by
    exact (Gauss.band d).scale_pos' (by norm_num) N hv0 hv1
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hC : 0 <= APrimeFirstCellDriftCoefficient.coefficientConstant :=
    APrimeFirstCellDriftCoefficient.coefficientConstant_pos.le
  unfold APrimeFirstCellDriftCoefficient.endpointCoefficient
  positivity

/-- T456 and T450 close the actual support-aware split on one literal event.
T451 supplies the fixed-size integrability needed by the root-scaled split. -/
theorem actualDriftNormSplit_of_inputs {tauPrime delta alpha : Real}
    (htau : 0 < tauPrime) {p : Nat} (hp : 1 <= p)
    (hweighted : APrimeFirstCellDriftWeightedGood.weightedDriftGood
      tauPrime delta alpha)
    (hglobal : APrimeFirstCellDriftGlobalPoly.globalMovingDriftPoly tauPrime) :
    actualDriftNormSplit tauPrime delta alpha p := by
  filter_upwards [hweighted, hglobal, eventually_ge_atTop (2 : Nat)]
      with N hweightedN hglobalN hN
  intro k hk1 hk
  let v := APrimeFirstCellSampleRegularity.endpoint N k
  change ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
    momNormW (P d)
        (APrimeFirstCellSampleRegularity.weight tauPrime delta p N k) p
        (APrimeFirstCellSampleRegularity.G N k a r) <=
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N v r +
        APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) *
          ((P d)
            (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
              tauPrime delta alpha N)ᶜ).toReal ^
            ((1 : Real) / (2 * p))
  have ht := APrimeSupportRunning.firstT_bounds htau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _
      (cutNetPt_mem_netFinset hk)
  have hvhalf : v <= 1 / 2 := hv.2.trans ht.2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  intro r hr a
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v :=
    APrimeDriftTimeFamily.driftScale_pos d (by norm_num) hv.1 hv1 N a
  have hG0 : ∀ omega,
      0 <= APrimeFirstCellSampleRegularity.G N k a r omega := by
    intro omega
    unfold APrimeFirstCellSampleRegularity.G APrimeDriftTimeFamily.driftAt
    exact div_nonneg (norm_nonneg _) hscale.le
  have hW0 : ∀ omega,
      0 <= APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega := by
    intro omega
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hW1 : ∀ omega,
      APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega <= 1 := by
    intro omega
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hGi : Integrable (fun omega =>
      APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
        |APrimeFirstCellSampleRegularity.G N k a r omega| ^ (2 * p)) (P d) := by
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity
      htau hp (by omega) hk a hr).hGi
  have hA : 0 <= APrimeFirstCellDriftCoefficient.endpointCoefficient
      delta (2 * alpha) N v r :=
    endpointCoefficient_nonneg (by omega) hr.1 hr.2 hvhalf
  have hEnv : 0 <=
      APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) :=
    mul_nonneg APrimeFirstCellDriftGlobalPoly.driftConstant_pos.le (by positivity)
  have hpr : 0 <= ((P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N)ᶜ).toReal := ENNReal.toReal_nonneg
  have hgood : ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha N,
      APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
          |APrimeFirstCellSampleRegularity.G N k a r omega| <=
        APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
          APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N v r := by
    intro omega homega
    have hh := hweightedN omega homega 2 p k m (by omega) hp hm hk1 hk r hr a
    rw [abs_of_nonneg (hG0 omega)]
    simpa only [v, m, APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint,
      APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight,
      APrimeFirstCellSampleRegularity.G,
      APrimeSupportRunning.weight] using hh
  have hGall : ∀ omega,
      |APrimeFirstCellSampleRegularity.G N k a r omega| <=
        APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) := by
    intro omega
    rw [abs_of_nonneg (hG0 omega)]
    simpa only [v, APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint,
      APrimeFirstCellSampleRegularity.G] using hglobalN k hk r hr a omega
  exact drift_norm_le_of_weighted_event (P0 := P d) hp hW0 hW1 hGi
    (APrimeFirstCellSharpCommonEvent.measurableSet_sharpCommonEvent
      htau delta alpha N) hA hEnv hpr hgood hGall le_rfl

/-- The empty prefix is an exact zero-window statement.  T456 gives weight
one, and the transported drift itself vanishes, so no event payment is used
to prove the left-hand side is zero. -/
theorem actualDriftNormSplit_k_zero (tauPrime delta alpha : Real)
    {p N : Nat} (hp : 1 <= p) (hN : 0 < N)
    (a : LoopArg (d.L N) 2) :
    (∀ omega,
      APrimeFirstCellSampleRegularity.weight tauPrime delta p N 0 omega = 1) ∧
    momNormW (P d)
        (APrimeFirstCellSampleRegularity.weight tauPrime delta p N 0) p
        (APrimeFirstCellSampleRegularity.G N 0 a 0) <=
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N
            (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
        APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) *
          ((P d)
            (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
              tauPrime delta alpha N)ᶜ).toReal ^
            ((1 : Real) / (2 * p)) := by
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hw : ∀ omega,
      APrimeFirstCellSampleRegularity.weight tauPrime delta p N 0 omega = 1 := by
    intro omega
    have hz := APrimeFirstCellDriftWeightedGood.weightedDrift_zero_prefix
      tauPrime delta alpha 2 p N m hm omega a
    simpa only [m, APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight,
      APrimeSupportRunning.weight] using hz.1
  refine ⟨hw, ?_⟩
  have hGzero : APrimeFirstCellSampleRegularity.G N 0 a 0 = fun _ => 0 := by
    funext omega
    simpa only [APrimeFirstCellSampleRegularity.G,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using
      (APrimeFirstCellDriftTransportRaw.driftAt_cutNet_zero N omega a)
  have hnorm : momNormW (P d)
      (APrimeFirstCellSampleRegularity.weight tauPrime delta p N 0) p
      (APrimeFirstCellSampleRegularity.G N 0 a 0) = 0 := by
    rw [hGzero]
    unfold momNormW
    have hq : 2 * p ≠ 0 := by omega
    simp only [abs_zero, zero_pow hq, mul_zero, integral_zero]
    exact Real.zero_rpow (ne_of_gt (by positivity))
  rw [hnorm]
  have hA : 0 <= APrimeFirstCellDriftCoefficient.endpointCoefficient
      delta (2 * alpha) N
        (APrimeFirstCellSampleRegularity.endpoint N 0) 0 := by
    simpa only [APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero] using
      (endpointCoefficient_nonneg hN (delta := delta) (alpha := alpha)
        (v := 0) (r := 0) (by norm_num) (by norm_num) (by norm_num))
  have hEnv : 0 <=
      APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) :=
    mul_nonneg APrimeFirstCellDriftGlobalPoly.driftConstant_pos.le (by positivity)
  have hpr : 0 <= ((P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N)ᶜ).toReal := ENNReal.toReal_nonneg
  positivity

/-- A nondegenerate same-event resident for the norm split.  The resident
retains T456's literal weight-one statement at smoothing order `m = N`, while
the norm estimate itself uses the canonical smooth weight from T451. -/
def positiveActualDriftNormResident
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      (∀ p0 : Nat, APrimeSupportRunning.weight delta (firstCellT tauPrime)
        2 p0 N 2 N omega = 1) ∧
      let v := APrimeFirstCellSampleRegularity.endpoint N 2
      0 < v ∧ v <= firstCellT tauPrime N ∧ firstCellT tauPrime N <= 1 / 2 ∧
      ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
        momNormW (P d)
            (APrimeFirstCellSampleRegularity.weight tauPrime delta p N 2) p
            (APrimeFirstCellSampleRegularity.G N 2 a r) <=
          APrimeFirstCellDriftCoefficient.endpointCoefficient
              delta (2 * alpha) N v r +
            APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat) *
              ((P d)
                (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
                  tauPrime delta alpha N)ᶜ).toReal ^
                ((1 : Real) / (2 * p))

theorem positiveActualDriftNormResident_of_inputs
    {tauPrime delta alpha : Real} {p : Nat}
    (hsplit : actualDriftNormSplit tauPrime delta alpha p)
    (hpositive : APrimeFirstCellDriftWeightedGood.positiveWeightedDriftPlateau
      tauPrime delta alpha) :
    positiveActualDriftNormResident tauPrime delta alpha p := by
  filter_upwards [hsplit, hpositive] with N hsplitN hpositiveN
  dsimp only [APrimeFirstCellDriftWeightedGood.positiveWeightedDriftPlateau]
    at hpositiveN
  obtain ⟨omega, homega, hk, hvpos, hvle, hvhalf, hw,
    _hweighted, _hzero, _hend⟩ := hpositiveN
  have hnorm := hsplitN 2 (by norm_num) hk
  refine ⟨omega, homega, hk, hw, ?_⟩
  simpa only [APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint] using
    And.intro hvpos (And.intro hvle (And.intro hvhalf hnorm))

/-- Closed producer: one choice of the first-cell parameter supplies the
measurable high-probability event, the exact canonical weighted norm split
for every fixed moment order, and a same-sample positive `k = 2` resident. -/
theorem exists_actualDriftNormSplit_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ alpha : Real, 0 < alpha ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        ∀ p : Nat, 1 <= p ->
          actualDriftNormSplit tauPrime delta alpha p ∧
          positiveActualDriftNormResident tauPrime delta alpha p := by
  obtain ⟨tauPrime, htau, hall⟩ :=
    APrimeFirstCellDriftWeightedGood.exists_weightedDriftGood_with_plateau
  refine ⟨tauPrime, htau, ?_⟩
  intro delta hdelta hdelta100 alpha halpha
  obtain ⟨hmeas, hprob, hweighted, hpositive⟩ :=
    hall delta hdelta hdelta100 alpha halpha
  refine ⟨hmeas, hprob, ?_⟩
  intro p hp
  have hsplit := actualDriftNormSplit_of_inputs htau hp hweighted
    (APrimeFirstCellDriftGlobalPoly.eventually_globalMovingDriftPoly htau)
  exact ⟨hsplit,
    positiveActualDriftNormResident_of_inputs hsplit hpositive⟩

end

end RBM.APrimeFirstCellDriftNormSplit

#print axioms RBM.APrimeFirstCellDriftNormSplit.weighted_norm_le_of_weighted_event
#print axioms RBM.APrimeFirstCellDriftNormSplit.drift_norm_le_of_weighted_event
#print axioms RBM.APrimeFirstCellDriftNormSplit.actualDriftNormSplit_of_inputs
#print axioms RBM.APrimeFirstCellDriftNormSplit.actualDriftNormSplit_k_zero
#print axioms RBM.APrimeFirstCellDriftNormSplit.positiveActualDriftNormResident_of_inputs
#print axioms RBM.APrimeFirstCellDriftNormSplit.exists_actualDriftNormSplit_with_resident
