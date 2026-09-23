/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDriftNormSplit

/-!
# T538: variable-delta first-cell drift bad-event payment

The exact complement term in T460 is paid with the `HighProb` property of
the same literal sharp common event.  The small exponent `delta`, the moment
order, and the requested decay exponent are all fixed before the eventual
cutoff.
-/

namespace RBM.APrimeFirstCellDeltaDriftBadPayment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T450's literal all-sample drift envelope. -/
noncomputable def driftEnvelope (N : Nat) : Real :=
  APrimeFirstCellDriftGlobalPoly.driftConstant * (N : Real) ^ (61 : Nat)

/-- Complement mass of the one literal T434 event. -/
noncomputable def rho (tauPrime delta alpha : Real) (N : Nat) : Real :=
  ((P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
    tauPrime delta alpha N)ᶜ).toReal

/-- The exact complement contribution appearing in T460. -/
noncomputable def badPayment
    (tauPrime delta alpha : Real) (p N : Nat) : Real :=
  driftEnvelope N * rho tauPrime delta alpha N ^ ((1 : Real) / (2 * p : Nat))

/-- The fixed coefficient in T450 is eventually absorbed by one additional
power of `N`. -/
theorem eventually_driftEnvelope_le :
    ∀ᶠ N : Nat in atTop, driftEnvelope N <= (N : Real) ^ (62 : Real) := by
  obtain ⟨N0, hN0⟩ :=
    exists_nat_ge APrimeFirstCellDriftGlobalPoly.driftConstant
  filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
  have hN0N : N0 <= N := le_trans (Nat.le_max_left _ _) hN
  have hN1 : 1 <= N := le_trans (Nat.le_max_right _ _) hN
  have hCN : APrimeFirstCellDriftGlobalPoly.driftConstant <= (N : Real) := by
    exact hN0.trans (by exact_mod_cast hN0N)
  have hpow0 : 0 <= (N : Real) ^ (61 : Nat) := by positivity
  calc
    driftEnvelope N = APrimeFirstCellDriftGlobalPoly.driftConstant *
        (N : Real) ^ (61 : Nat) := rfl
    _ <= (N : Real) * (N : Real) ^ (61 : Nat) :=
      mul_le_mul_of_nonneg_right hCN hpow0
    _ = (N : Real) ^ (62 : Nat) := by rw [← pow_succ']
    _ = (N : Real) ^ (62 : Real) := by norm_num [Real.rpow_natCast]

/-- High probability pays the exact T460 complement term.  The order is
`delta`, `p`, `beta`, then eventual `N`; there is no uniform cutoff. -/
theorem eventually_badPayment_le {tauPrime delta alpha : Real}
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha))
    (p : Nat) (hp : 1 <= p) (beta : Real) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop,
      badPayment tauPrime delta alpha p N <= (N : Real) ^ (-beta) := by
  have h := Gauss.eventually_env_mul_prob_rpow_le_moment
    (Ξ := APrimeFirstCellSharpCommonEvent.sharpCommonEvent
      tauPrime delta alpha)
    (Env := driftEnvelope) (Cenv := 62) hprob (by norm_num)
    eventually_driftEnvelope_le p hp beta hbeta
  simpa only [badPayment, driftEnvelope, rho] using h

/-- The paid actual first-cell drift estimate with explicit `delta`. -/
def actualDriftNormPaid
    (tauPrime delta alpha beta : Real) (p : Nat) : Prop :=
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
            (N : Real) ^ (-beta)

theorem actualDriftNormPaid_of_inputs
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hsplit : APrimeFirstCellDriftNormSplit.actualDriftNormSplit
      tauPrime delta alpha p)
    (hpay : ∀ᶠ N : Nat in atTop,
      badPayment tauPrime delta alpha p N <= (N : Real) ^ (-beta)) :
    actualDriftNormPaid tauPrime delta alpha beta p := by
  filter_upwards [hsplit, hpay] with N hsplitN hpayN
  intro k hk1 hk
  let v := APrimeFirstCellSampleRegularity.endpoint N k
  change ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
    momNormW (P d)
        (APrimeFirstCellSampleRegularity.weight tauPrime delta p N k) p
        (APrimeFirstCellSampleRegularity.G N k a r) <=
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N v r +
        (N : Real) ^ (-beta)
  intro r hr a
  have hnorm := hsplitN k hk1 hk r hr a
  have hpayN' : APrimeFirstCellDriftGlobalPoly.driftConstant *
        (N : Real) ^ (61 : Nat) *
        ((P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N)ᶜ).toReal ^
          ((1 : Real) / (2 * p)) <= (N : Real) ^ (-beta) := by
    simpa only [badPayment, driftEnvelope, rho, Nat.cast_mul,
      Nat.cast_ofNat] using hpayN
  have hadd : APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N v r +
        APrimeFirstCellDriftGlobalPoly.driftConstant *
          (N : Real) ^ (61 : Nat) *
          ((P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)ᶜ).toReal ^
            ((1 : Real) / (2 * p)) <=
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N v r + (N : Real) ^ (-beta) :=
    add_le_add_right hpayN' _
  simpa only [v] using hnorm.trans hadd

/-- The empty prefix keeps its exact zero endpoint and weight-one identity;
the same event payment replaces T460's exact complement term. -/
theorem eventually_actualDriftNormPaid_k_zero
    {tauPrime delta alpha beta : Real}
    (hprob : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha))
    (p : Nat) (hp : 1 <= p) (hbeta : 0 < beta) :
    ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
      (∀ omega,
        APrimeFirstCellSampleRegularity.weight tauPrime delta p N 0 omega = 1) ∧
      momNormW (P d)
          (APrimeFirstCellSampleRegularity.weight tauPrime delta p N 0) p
          (APrimeFirstCellSampleRegularity.G N 0 a 0) <=
        APrimeFirstCellDriftCoefficient.endpointCoefficient
            delta (2 * alpha) N
              (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
          (N : Real) ^ (-beta) := by
  filter_upwards [eventually_badPayment_le hprob p hp beta hbeta,
    eventually_ge_atTop (1 : Nat)] with N hpay hN
  intro a
  have hzero := APrimeFirstCellDriftNormSplit.actualDriftNormSplit_k_zero
    tauPrime delta alpha hp (by omega) a
  refine ⟨by simp only [APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero], hzero.1, ?_⟩
  have hpay' : APrimeFirstCellDriftGlobalPoly.driftConstant *
        (N : Real) ^ (61 : Nat) *
        ((P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta alpha N)ᶜ).toReal ^
          ((1 : Real) / (2 * p)) <= (N : Real) ^ (-beta) := by
    simpa only [badPayment, driftEnvelope, rho, Nat.cast_mul,
      Nat.cast_ofNat] using hpay
  have hadd : APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N
            (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
        APrimeFirstCellDriftGlobalPoly.driftConstant *
          (N : Real) ^ (61 : Nat) *
          ((P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)ᶜ).toReal ^
            ((1 : Real) / (2 * p)) <=
      APrimeFirstCellDriftCoefficient.endpointCoefficient
          delta (2 * alpha) N
            (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
        (N : Real) ^ (-beta) := add_le_add_right hpay' _
  exact hzero.2.trans hadd

/-- A same-event positive `k = 2` resident carrying the paid norm estimate.
Its weight-one field is the accepted support weight at smoothing order `m = N`. -/
def positiveActualDriftPaidResident
    (tauPrime delta alpha beta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      APrimeSupportRunning.weight delta (firstCellT tauPrime)
        2 p N 2 N omega = 1 ∧
      let v := APrimeFirstCellSampleRegularity.endpoint N 2
      0 < v ∧ v <= firstCellT tauPrime N ∧ firstCellT tauPrime N <= 1 / 2 ∧
      ∀ r ∈ Icc (0 : Real) v, ∀ a : LoopArg (d.L N) 2,
        momNormW (P d)
            (APrimeFirstCellSampleRegularity.weight tauPrime delta p N 2) p
            (APrimeFirstCellSampleRegularity.G N 2 a r) <=
          APrimeFirstCellDriftCoefficient.endpointCoefficient
              delta (2 * alpha) N v r +
            (N : Real) ^ (-beta)

theorem positiveActualDriftPaidResident_of_inputs
    {tauPrime delta alpha beta : Real} {p : Nat}
    (hpaid : actualDriftNormPaid tauPrime delta alpha beta p)
    (hresident : APrimeFirstCellDriftNormSplit.positiveActualDriftNormResident
      tauPrime delta alpha p) :
    positiveActualDriftPaidResident tauPrime delta alpha beta p := by
  filter_upwards [hpaid, hresident] with N hpaidN hresidentN
  obtain ⟨omega, homega, hk, hw, hvpos, hvle, hvhalf, _hnorm⟩ := hresidentN
  have hnorm := hpaidN 2 (by norm_num) hk
  exact ⟨omega, homega, hk, hw p, hvpos, hvle, hvhalf, hnorm⟩

/-- Closed T538 producer.  One `tauPrime` works for every permitted `delta`;
the same sharp common event pays every fixed `p` and `beta`. -/
theorem exists_actualDriftNormPaid_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ alpha : Real, 0 < alpha ->
      ∀ p : Nat, 1 <= p ->
      ∀ beta : Real, 0 < beta ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualDriftNormPaid tauPrime delta alpha beta p ∧
        (∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
          APrimeFirstCellSampleRegularity.endpoint N 0 = 0 ∧
          (∀ omega,
            APrimeFirstCellSampleRegularity.weight
              tauPrime delta p N 0 omega = 1) ∧
          momNormW (P d)
              (APrimeFirstCellSampleRegularity.weight
                tauPrime delta p N 0) p
              (APrimeFirstCellSampleRegularity.G N 0 a 0) <=
            APrimeFirstCellDriftCoefficient.endpointCoefficient
                delta (2 * alpha) N
                  (APrimeFirstCellSampleRegularity.endpoint N 0) 0 +
              (N : Real) ^ (-beta)) ∧
        positiveActualDriftPaidResident tauPrime delta alpha beta p := by
  obtain ⟨tauPrime, htau, hall⟩ :=
    APrimeFirstCellDriftNormSplit.exists_actualDriftNormSplit_with_resident
  refine ⟨tauPrime, htau, ?_⟩
  intro delta hdelta hdelta100 alpha halpha p hp beta hbeta
  obtain ⟨hmeas, hprob, hmoment⟩ :=
    hall delta hdelta hdelta100 alpha halpha
  obtain ⟨hsplit, hresident⟩ := hmoment p hp
  have hpay := eventually_badPayment_le hprob p hp beta hbeta
  have hpaid := actualDriftNormPaid_of_inputs hsplit hpay
  exact ⟨hmeas, hprob, hpaid,
    eventually_actualDriftNormPaid_k_zero hprob p hp hbeta,
    positiveActualDriftPaidResident_of_inputs hpaid hresident⟩

end

end RBM.APrimeFirstCellDeltaDriftBadPayment

#print axioms RBM.APrimeFirstCellDeltaDriftBadPayment.eventually_driftEnvelope_le
#print axioms RBM.APrimeFirstCellDeltaDriftBadPayment.eventually_badPayment_le
#print axioms RBM.APrimeFirstCellDeltaDriftBadPayment.actualDriftNormPaid_of_inputs
#print axioms RBM.APrimeFirstCellDeltaDriftBadPayment.eventually_actualDriftNormPaid_k_zero
#print axioms RBM.APrimeFirstCellDeltaDriftBadPayment.positiveActualDriftPaidResident_of_inputs
#print axioms RBM.APrimeFirstCellDeltaDriftBadPayment.exists_actualDriftNormPaid_with_resident
