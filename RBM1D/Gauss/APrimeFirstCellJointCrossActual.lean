/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellPrefixAbsorbed
import RBM1D.Gauss.APrimeFirstCellJointCrossRegularity
import RBM1D.Gauss.APrimeFirstCellCrossBadPayment

/-!
# T468: actual first-cell full joint-cross adapter

The exact T361 event consumer is instantiated with the literal common event,
the moving favorable prefix rate, and the moving current-QV rate.
-/

namespace RBM.APrimeFirstCellJointCrossActual

open Filter MeasureTheory Set Real Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable abbrev delta : ℝ := APrimeFirstCellFarRowAbsorb.delta
noncomputable abbrev tau : ℝ := APrimeFirstCellFarRowAbsorb.tau

noncomputable def favorableRate (alpha : ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  (16 * Real.sqrt 3 / Real.exp 1) * Real.sqrt v *
    (N : ℝ) ^ (alpha / 2 - 2 * delta)

noncomputable def currentRate (alpha : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  APrimeFirstCellQVCurrentRows.currentRate delta tau alpha N v r

noncomputable def jointEnvelope (N : ℕ) : ℝ :=
  APrimeFirstCellCrossBadPayment.jointEnvelope N

noncomputable def rho (tauPrime alpha : ℝ) (N : ℕ) : ℝ :=
  APrimeFirstCellCrossBadPayment.rho tauPrime delta alpha N

theorem favorableRate_nonneg {alpha : ℝ} {N : ℕ} {v : ℝ} (_hv : 0 ≤ v) :
    0 ≤ favorableRate alpha N v := by
  unfold favorableRate
  positivity

theorem currentRate_nonneg {alpha : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2) :
    0 ≤ currentRate alpha N v r := by
  have hr1 : r < 1 := hrv.trans hvhalf |>.trans_lt (by norm_num)
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have heta : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxr : 0 < APrimeFirstCellLoopCap.xRate r := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num)) heta
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  have hAv : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
    B.scale_pos' (by norm_num) N hv0 hv1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold currentRate APrimeFirstCellQVCurrentRows.currentRate
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg APrimeFirstCellQVCurrentRows.currentConstant_pos.le
          (Real.rpow_nonneg hNr.le _))
        (inv_nonneg.mpr heta.le))
      (Real.rpow_nonneg hxv.le _))
    (add_nonneg
      (add_nonneg (Real.rpow_nonneg hxr.le _)
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hNr.le _)
            (Real.rpow_nonneg hAv.le _))
          (Real.rpow_nonneg hxr.le _)))
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hNr.le _) (inv_nonneg.mpr hAv.le))
        (Real.rpow_nonneg hxr.le _)))

theorem jointEnvelope_nonneg (N : ℕ) : 0 ≤ jointEnvelope N := by
  unfold jointEnvelope APrimeFirstCellCrossBadPayment.jointEnvelope
  positivity

theorem rho_nonneg (tauPrime alpha : ℝ) (N : ℕ) :
    0 ≤ rho tauPrime alpha N := by
  exact ENNReal.toReal_nonneg

/-- The accepted T361 coefficient is strictly larger than the coefficient
requested in T468.  Their ratio is `2p` for every `p ≥ 1`. -/
theorem requested_coefficient_lt_t361 {p : ℕ} (hp : 1 ≤ p) :
    15 * (p : ℝ) / 8 <
      (1 / 2 : ℝ) * (((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  push_cast
  nlinarith [sq_nonneg ((p : ℝ) - 1)]

/-- The exact fixed-moment T361 conclusion on the actual moving first cell. -/
def actualJointCrossBound (tauPrime alpha : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
      k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      ∀ (a : LoopArg (d.L N) 2),
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Ioc (0 : ℝ) v,
        APrimeDuhamelModel.crossPart d N
            (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0 v)
            (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
              (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
              2 p N k
              (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
                (firstCellT tauPrime)
                APrimeSmoothTransition.transitionMesh N)) r ≤
          (1 / (2 * Real.sqrt r)) *
            (((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)) *
            (∫ omega,
              |APrimeSmoothWeightActual.cutoff d 0 60 delta (fun _ => 0)
                APrimeSmoothTransition.transitionMesh N k
                (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
                  (firstCellT tauPrime)
                  APrimeSmoothTransition.transitionMesh N) omega *
                ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v r
                  (Gauss.Hflow d N r omega)‖| ^ (2 * p) ∂(P d)) ^
                ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
            (favorableRate alpha N v * Real.sqrt (currentRate alpha N v r) +
              jointEnvelope N *
                rho tauPrime alpha N ^ ((1 : ℝ) / (2 * (p : ℝ))))

/-- The literal T361 cross estimate at an active moving endpoint and positive
current time.  The moment order is selected before the eventual matrix size. -/
theorem eventually_crossPart_le {tauPrime alpha : ℝ}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha)
    (p : ℕ) (hp : 1 ≤ p) :
    actualJointCrossBound tauPrime alpha p := by
  filter_upwards [
    APrimeFirstCellPrefixAbsorbed.eventually_prefixGradient_le hTau hAlpha,
    APrimeFirstCellQVCurrentRows.eventually_currentRowsBound
      hTau APrimeFirstCellFarRowAbsorb.delta_pos.le hAlpha,
    APrimeFirstCellJointGlobalPoly.eventually_t361_hAll
      hTau APrimeFirstCellFarRowAbsorb.delta_pos.le,
    APrimeFirstCellJointCrossRegularity.eventually_actual_jointCrossSampleRegularity
      hTau APrimeFirstCellFarRowAbsorb.delta_pos.le p hp,
    eventually_ge_atTop 2] with N hprefix hcurrent hAll hreg hN2
  intro k hk1 hk a
  dsimp only
  intro r hr
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hN : 0 < N := by omega
  have hm : 1 ≤ m := APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hvcell : v ∈ Icc (0 : ℝ) (firstCellT tauPrime N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 := hvcell.2.trans ht.2
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hri : r ∈ Icc (0 : ℝ) v := ⟨hr.1.le, hr.2⟩
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hb : 0 ≤ favorableRate alpha N v :=
    favorableRate_nonneg hvcell.1
  have hq : 0 ≤ currentRate alpha N v r :=
    currentRate_nonneg hN hri.1 hri.2 hvhalf
  have hBgood : ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N ∩
        APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k m,
      APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m omega ≤
          favorableRate alpha N v := by
    intro omega homega
    exact hprefix omega homega.1 k hk1 hk homega.2
  have hQgood : ∀ omega ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N ∩
        APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k m,
      APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r omega ≤
        currentRate alpha N v r := by
    intro omega homega
    have hw : 0 < APrimeSupportRunning.weight delta (firstCellT tauPrime)
        2 1 N k m omega :=
      APrimeFirstCellPrefixGoodRows.actualWeight_pos_of_transition
        hN2 hk homega.2
    have hrows := hcurrent omega homega.1 2 1 k m hN2
      (by norm_num) hm hk1 hk hw
    simpa only [currentRate, tau, APrimeFirstCellFarRowAbsorb.tau] using
      ((hrows.2.2.2.2 r hri).2.2 a)
  have hP : ((P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N)ᶜ).toReal ≤ rho tauPrime alpha N := by
    rfl
  have hregular := hreg k hk a r hri
  exact APrimeCrossJointSplit.crossPart_active_le_jointEvent
    d 0 60 delta (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh 2 N k m p Step2.sigPM a v r
    (by norm_num) (by norm_num) (by norm_num) hv1 hri hr.1 hN hm hu hk hN2 hp
    (APrimeFirstCellSharpCommonEvent.measurableSet_sharpCommonEvent
      hTau delta alpha N)
    hb hq (jointEnvelope_nonneg N) (rho_nonneg tauPrime alpha N)
    hBgood hQgood (hAll k hk a r hri) hP
    hregular.hYm hregular.hZm hregular.hYi hregular.hZi hregular.hProdInt

/-- The zero-length cell is kept outside the singular positive-time theorem. -/
theorem crossPart_zero_k0 (tauPrime : ℝ) (N p : ℕ)
    (a : LoopArg (d.L N) 2) :
    APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0 0)
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N 0
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)) 0 = 0 := by
  exact APrimeCrossJointSplit.crossPart_zero_k0 d 0 60 delta (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh 2 N _ p
    (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) _ 0

/-- Same-event nondegenerate `k=2` geometry with all five T361 sample fields.
No strict-transition inhabitance or weight-one conclusion is retained. -/
def positiveTwoJointCrossGeometry (tauPrime alpha : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    let u0 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    let u1 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 1
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v ≤ firstCellT tauPrime N ∧
    2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) v,
      APrimeFirstCellJointCrossRegularity.JointCrossSampleRegularity p
        (APrimeFirstCellJointCrossRegularity.Ycut
          tauPrime delta N 2 a r)
        (APrimeFirstCellJointCrossRegularity.jointRate
          tauPrime delta N 2 a r)

theorem positiveTwoJointCrossGeometry_of_prefix
    {tauPrime alpha : ℝ} {p : ℕ} (hTau : 0 < tauPrime)
    (hprefix : APrimeFirstCellPrefixAbsorbed.positiveTwoAbsorbedGeometry
      tauPrime alpha) (hp : 1 ≤ p) :
    positiveTwoJointCrossGeometry tauPrime alpha p := by
  filter_upwards [hprefix,
    APrimeFirstCellJointCrossRegularity.eventually_actual_jointCrossSampleRegularity
      hTau APrimeFirstCellFarRowAbsorb.delta_pos.le p hp] with N hgeom hreg
  obtain ⟨omega, homega, hu0, hu1, hu12, hv, hk2,
    _hb0, _hb1, _hb2⟩ := hgeom
  exact ⟨omega, homega, hu0, hu1, hu12, hv, hk2, hreg 2 hk2⟩

/-- Closed fixed-moment producer for the literal event and actual cross term. -/
theorem exists_actualJointCrossBound :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∀ alpha : ℝ, 0 < alpha → ∀ p : ℕ, 1 ≤ p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualJointCrossBound tauPrime alpha p ∧
        positiveTwoJointCrossGeometry tauPrime alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellPrefixAbsorbed.exists_absorbedTransitionPrefixBound
  refine ⟨tauPrime, hTau, ?_⟩
  intro alpha hAlpha p hp
  obtain ⟨hmeas, hprob, _hbound, hpositive⟩ := hall alpha hAlpha
  exact ⟨hmeas, hprob, eventually_crossPart_le hTau hAlpha p hp,
    positiveTwoJointCrossGeometry_of_prefix hTau hpositive hp⟩

#print axioms favorableRate_nonneg
#print axioms currentRate_nonneg
#print axioms requested_coefficient_lt_t361
#print axioms eventually_crossPart_le
#print axioms crossPart_zero_k0
#print axioms positiveTwoJointCrossGeometry_of_prefix
#print axioms exists_actualJointCrossBound

end RBM.APrimeFirstCellJointCrossActual
