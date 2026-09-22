/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellJointGlobalPoly
import RBM1D.Gauss.APrimeFirstCellScaleFloors
import RBM1D.Gauss.APrimeFirstCellSharpCommonEvent

/-!
# T463: literal first-cell joint-cross bad-event payment

The all-sample joint envelope of T454 is multiplied by the complement
probability of the one literal T434 event.  High probability pays this term
after the moment order is fixed, and T458 supplies the moving ratio floor.
-/

namespace RBM.APrimeFirstCellCrossBadPayment

open Filter Set Real Gauss CutHypTheta MeasureTheory

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The literal all-sample envelope from T454. -/
noncomputable def jointEnvelope (N : Nat) : Real :=
  2 ^ (26 : Nat) * (N : Real) ^ (130 : Nat)

/-- Complement probability of the one literal T434 event. -/
noncomputable def rho (tauPrime delta alpha : Real) (N : Nat) : Real :=
  ((P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
    tauPrime delta alpha N)ᶜ).toReal

/-- The Hölder payment at the fixed moment order `p`. -/
noncomputable def badPayment (tauPrime delta alpha : Real) (p N : Nat) : Real :=
  jointEnvelope N * rho tauPrime delta alpha N ^
    ((1 : Real) / (2 * p : Nat))

theorem eventually_jointEnvelope_le :
    ∀ᶠ N : Nat in atTop, jointEnvelope N <= (N : Real) ^ (131 : Real) := by
  filter_upwards [eventually_ge_atTop (2 ^ (26 : Nat))] with N hN
  have hNreal : (2 : Real) ^ (26 : Nat) <= (N : Real) := by exact_mod_cast hN
  have hN0 : 0 <= (N : Real) ^ (130 : Nat) := by positivity
  calc
    jointEnvelope N = (2 : Real) ^ (26 : Nat) * (N : Real) ^ (130 : Nat) := rfl
    _ <= (N : Real) * (N : Real) ^ (130 : Nat) :=
      mul_le_mul_of_nonneg_right hNreal hN0
    _ = (N : Real) ^ (131 : Nat) := by rw [← pow_succ']
    _ = (N : Real) ^ (131 : Real) := by norm_num [Real.rpow_natCast]

theorem eventually_badPayment_le_decay {tauPrime delta alpha : Real}
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha))
    (p : Nat) (hp : 1 <= p) (hdelta : 0 < delta) :
    ∀ᶠ N : Nat in atTop,
      badPayment tauPrime delta alpha p N <=
        (N : Real) ^ (-(2 * delta + 2)) := by
  have h := Gauss.eventually_env_mul_prob_rpow_le_moment
    (Ξ := APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha)
    (Env := jointEnvelope) (Cenv := 131) hprob (by norm_num)
    eventually_jointEnvelope_le p hp (2 * delta + 2) (by linarith)
  simpa only [badPayment, rho] using h

private theorem rpow_neg_two_lower {R : Real} (hR0 : 0 < R) (hR2 : R <= 2) :
    (1 / 4 : Real) <= R ^ (-(2 : Real)) := by
  have hsq : R ^ (2 : Nat) <= (2 : Real) ^ (2 : Nat) :=
    pow_le_pow_left₀ hR0.le hR2 2
  have hinv : ((2 : Real) ^ (2 : Nat))⁻¹ <= (R ^ (2 : Nat))⁻¹ :=
    inv_anti₀ (pow_pos hR0 2) hsq
  rw [Real.rpow_neg hR0.le]
  norm_num at hinv ⊢
  exact hinv

private theorem rpow_neg_two_nat_le_quarter {N : Nat} (hN : 2 <= N) :
    (N : Real) ^ (-(2 : Real)) <= 1 / 4 := by
  have hNreal : (2 : Real) <= (N : Real) := by exact_mod_cast hN
  have hsq : (2 : Real) ^ (2 : Nat) <= (N : Real) ^ (2 : Nat) :=
    pow_le_pow_left₀ (by norm_num) hNreal 2
  have hinv : ((N : Real) ^ (2 : Nat))⁻¹ <= ((2 : Real) ^ (2 : Nat))⁻¹ :=
    inv_anti₀ (by positivity) hsq
  rw [Real.rpow_neg (by positivity : 0 <= (N : Real))]
  norm_num at hinv ⊢
  exact hinv

/-- The paid complement term fits the literal moving ratio target, uniformly
over every actual first-cell endpoint after `p` is fixed. -/
theorem eventually_badPayment_le_moving_rate {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha))
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, ∀ k,
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      badPayment tauPrime delta alpha p N <=
        (N : Real) ^ (alpha - 2 * delta) *
          APrimeFirstCellLoopCap.xRate
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) ^
              (-(2 : Real)) := by
  filter_upwards [eventually_badPayment_le_decay hprob p hp hDelta,
    APrimeFirstCellScaleFloors.eventually_scalePackage hTau,
    eventually_ge_atTop 2] with N hpay hscale hN
  intro k hk
  have hs := hscale k hk
  let R := APrimeFirstCellLoopCap.xRate
    (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hs.one_le_ratio
  have hRinv : (1 / 4 : Real) <= R ^ (-(2 : Real)) :=
    rpow_neg_two_lower hR0 hs.ratio_le_two
  have hNneg : (N : Real) ^ (-(2 : Real)) <= 1 / 4 :=
    rpow_neg_two_nat_le_quarter hN
  have hNa : 1 <= (N : Real) ^ alpha :=
    Real.one_le_rpow (by exact_mod_cast (show 1 <= N by omega)) hAlpha.le
  have hsmall : (N : Real) ^ (-(2 : Real)) <=
      (N : Real) ^ alpha * R ^ (-(2 : Real)) := by
    calc
      _ <= 1 / 4 := hNneg
      _ <= R ^ (-(2 : Real)) := hRinv
      _ <= (N : Real) ^ alpha * R ^ (-(2 : Real)) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hNa (Real.rpow_nonneg hR0.le _)
  have hNpos : 0 < (N : Real) := by positivity
  calc
    badPayment tauPrime delta alpha p N <=
        (N : Real) ^ (-(2 * delta + 2)) := hpay
    _ = (N : Real) ^ (-2 * delta) * (N : Real) ^ (-(2 : Real)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring_nf
    _ <= (N : Real) ^ (-2 * delta) *
        ((N : Real) ^ alpha * R ^ (-(2 : Real))) :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hNpos.le _)
    _ = (N : Real) ^ (alpha - 2 * delta) * R ^ (-(2 : Real)) := by
      rw [← mul_assoc, ← Real.rpow_add hNpos]
      congr 1
      ring_nf

/-- Named fixed-moment version of the uniform moving-endpoint payment. -/
def badPaymentBound (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k,
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    badPayment tauPrime delta alpha p N <=
      (N : Real) ^ (alpha - 2 * delta) *
        APrimeFirstCellLoopCap.xRate
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) ^
            (-(2 : Real))

/-- At `k=0`, the endpoint and ratio are exactly zero and one respectively. -/
theorem eventually_badPayment_zero_endpoint {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha))
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop,
      cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0 = 0 ∧
      badPayment tauPrime delta alpha p N <=
        (N : Real) ^ (alpha - 2 * delta) := by
  filter_upwards [eventually_badPayment_le_moving_rate
    hTau hDelta hAlpha hprob p hp] with N hN
  have hpay := hN 0 (Nat.zero_le _)
  refine ⟨cutNetPt_zero _ _ _, ?_⟩
  simpa only [cutNetPt_zero, APrimeFirstCellLoopCap.xRate, etaT, mE_zero,
    Complex.I_im, mul_one, sub_zero, div_one, Real.one_rpow, mul_one] using hpay

/-- The `k=0` joint rate is exactly zero while its complement payment obeys
the corresponding ratio-one target. -/
theorem eventually_zero_jointRate_and_badPayment {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha))
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, ∀ (a : LoopArg (d.L N) 2) (omega : Ω d),
      APrimeCrossJointSplit.jointRate d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 0
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)
        Step2.sigPM a
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0) 0 omega = 0 ∧
      cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0 = 0 ∧
      badPayment tauPrime delta alpha p N <=
        (N : Real) ^ (alpha - 2 * delta) := by
  filter_upwards [eventually_badPayment_zero_endpoint
    hTau hDelta hAlpha hprob p hp] with N hpay
  intro a omega
  exact ⟨APrimeFirstCellJointGlobalPoly.jointRate_zero_k0
    tauPrime delta N a omega, hpay⟩

/-- A nondegenerate same-event `k=2` resident carrying the fixed-moment
bad-event payment.  Transition-set inhabitance is not asserted. -/
def positiveTwoBadPayment (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      APrimeSupportRunning.weight delta (firstCellT tauPrime)
        2 p N 2 N omega = 1 ∧
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧ v <= firstCellT tauPrime N ∧
      badPayment tauPrime delta alpha p N <=
        (N : Real) ^ (alpha - 2 * delta) *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : Real)) ∧
      ∀ (a : LoopArg (d.L N) 2) (r : Real), r ∈ Set.Icc (0 : Real) v ->
        APrimeCrossJointSplit.jointRate d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 2
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)
          Step2.sigPM a v r omega <= jointEnvelope N

theorem positiveTwoBadPayment_of_plateau {tauPrime delta alpha : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta alpha))
    (hpositive : APrimeFirstCellSharpCommonEvent.positiveSharpPlateau
      tauPrime delta alpha)
    (p : Nat) (hp : 1 <= p) :
    positiveTwoBadPayment tauPrime delta alpha p := by
  filter_upwards [hpositive, eventually_badPayment_le_moving_rate
    hTau hDelta hAlpha hprob p hp,
    APrimeFirstCellJointGlobalPoly.eventually_jointRate_bounds hTau hDelta.le]
      with N hpositive hpay hjoint
  obtain ⟨omega, homega, hk, hw, hvpos, hvle, _hvhalf,
    _hsource, _hJall, _hJ0, _hJv⟩ := hpositive
  refine ⟨omega, homega, hk, hw p, hvpos, hvle, hpay 2 hk, ?_⟩
  intro a r hr
  exact (hjoint 2 hk a r hr omega).2

/-- Closed T463 producer.  `tauPrime` is chosen by T434; for every fixed
moment order the literal event, its same-sample positive resident, and the
moving bad-event payment are retained together. -/
theorem exists_badPaymentBound_with_positive_two :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ alpha : Real, 0 < alpha ->
      ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        badPaymentBound tauPrime delta alpha p ∧
        positiveTwoBadPayment tauPrime delta alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 alpha hAlpha p hp
  obtain ⟨hmeas, hprob, hpositive⟩ :=
    hall delta hDelta hDelta100 alpha hAlpha
  refine ⟨hmeas, hprob, ?_,
    positiveTwoBadPayment_of_plateau hTau hDelta hAlpha hprob hpositive p hp⟩
  simpa only [badPaymentBound] using
    (eventually_badPayment_le_moving_rate hTau hDelta hAlpha hprob p hp)

#print axioms eventually_jointEnvelope_le
#print axioms eventually_badPayment_le_decay
#print axioms eventually_badPayment_le_moving_rate
#print axioms eventually_badPayment_zero_endpoint
#print axioms eventually_zero_jointRate_and_badPayment
#print axioms positiveTwoBadPayment_of_plateau
#print axioms exists_badPaymentBound_with_positive_two

end RBM.APrimeFirstCellCrossBadPayment
