/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellJointCrossActual
import RBM1D.Gauss.APrimeFirstCellFullCrossBudget

/-!
# T476: exact actual `hcross` adapter

T468's literal T361 estimate is put into the exact `hcross` shape consumed by
`APrimeDuhamelModel.momFlowDeriv_le`.  The consumer rate is T469's
`literalBfull`; its enlarged `BcrossActual = 2p * literalBfull` is not used.
-/

#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.APrimeFirstCellJointCrossActual.eventually_crossPart_le
#check @RBM.APrimeFirstCellFullCrossBudget.literalBfull
#check @RBM.APrimeCrossJointSplit.crossPart_zero_r0
#check @RBM.APrimeFirstCellJointCrossActual.crossPart_zero_k0
#check @RBM.APrimeFirstCellFullCrossBudget.integral_literalBfull_k0

namespace RBM.APrimeFirstCellHcrossExact

open Filter MeasureTheory Set Real Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The common fixed value `delta = 1/2000`. -/
noncomputable abbrev delta : Real := APrimeFirstCellJointCrossActual.delta

noncomputable def endpoint (N k : Nat) : Real :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

noncomputable def canonicalM (tauPrime : Real) (N : Nat) : Nat :=
  APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh N

/-- The literal `hcross` proposition expected by `momFlowDeriv_le`, with
`Bc = literalBfull`. -/
def exactHcrossAt (tauPrime alpha : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Prop :=
  APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0
        (endpoint N k))
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k (canonicalM tauPrime N)) r <=
    2 * (p : Real) *
      (∫ omega,
        APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
          |APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
              (endpoint N k)) r omega| ^ (2 * p) ∂(P d)) ^
        ((2 * (p : Real) - 1) / (2 * (p : Real))) *
      APrimeFirstCellFullCrossBudget.literalBfull
        tauPrime alpha p N (endpoint N k) r

/-- The moment order is fixed before the eventual matrix size, uniformly in
all active moving endpoints, outputs, and positive times. -/
def actualHcrossExact (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Ioc (0 : Real) (endpoint N k),
      exactHcrossAt tauPrime alpha p N k a r

theorem delta_eq_one_over_two_thousand : delta = 1 / 2000 := by
  rfl

/-- T462's pointwise identity, exposed in the exact form needed to replace
T468's cut-off moment by the canonical weighted moment. -/
theorem ycut_moment_eq_weighted_actual_moment
    {tauPrime : Real} {p N k : Nat}
    (hN : 2 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) (r : Real) :
    (∫ omega,
      |APrimeSmoothWeightActual.cutoff d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k (canonicalM tauPrime N) omega *
        ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
          (endpoint N k) r (Gauss.Hflow d N r omega)‖| ^ (2 * p) ∂(P d)) =
      ∫ omega,
        APrimeFirstCellSampleRegularity.weight tauPrime delta p N k omega *
          |APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
              (endpoint N k)) r omega| ^ (2 * p) ∂(P d) := by
  apply integral_congr_ae
  filter_upwards [] with omega
  have hactive : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧ 2 <= N := ⟨hk, hN⟩
  let c := APrimeSmoothWeightActual.cutoff d 0 60 delta (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k (canonicalM tauPrime N) omega
  let y := ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
    (endpoint N k) r (Gauss.Hflow d N r omega)‖
  have hc0 : 0 <= c := Cutoff.cutChi_nonneg _
  have hy0 : 0 <= y := norm_nonneg _
  simp only [APrimeFirstCellSampleRegularity.weight,
    APrimeFirstCellGeneratorHle.canonicalWeight,
    APrimeFirstCellGeneratorHle.actualWeight,
    APrimeSmoothWeightActual.weight, if_pos hactive,
    APrimeDuhamelModel.flowY]
  change |c * y| ^ (2 * p) = c ^ (2 * p) * |y| ^ (2 * p)
  rw [abs_of_nonneg (mul_nonneg hc0 hy0), abs_of_nonneg hy0, mul_pow]

/-- The T468 coefficient is exactly the outer `2p` required by
`momFlowDeriv_le` times T469's literal consumer rate. -/
theorem t361_rhs_eq_two_p_literalBfull
    (tauPrime alpha : Real) (p N : Nat) (v r momentFactor : Real) :
    (1 / (2 * Real.sqrt r)) *
        (((2 * p : Nat) : Real) ^ 2 * (15 / 8 : Real)) *
        momentFactor *
        (APrimeFirstCellJointCrossActual.favorableRate alpha N v *
            Real.sqrt (APrimeFirstCellJointCrossActual.currentRate alpha N v r) +
          APrimeFirstCellJointCrossActual.jointEnvelope N *
            APrimeFirstCellJointCrossActual.rho tauPrime alpha N ^
              ((1 : Real) / (2 * (p : Real)))) =
      2 * (p : Real) * momentFactor *
        APrimeFirstCellFullCrossBudget.literalBfull
          tauPrime alpha p N v r := by
  unfold APrimeFirstCellFullCrossBudget.literalBfull
    APrimeFirstCellFullCrossIntegrability.Bfull
    APrimeFirstCellFullCrossBudget.prefixRate
    APrimeFirstCellJointCrossActual.favorableRate
    APrimeFirstCellJointCrossActual.currentRate
    APrimeFirstCellJointCrossActual.jointEnvelope
    APrimeFirstCellJointCrossActual.rho
    APrimeFirstCellFullCrossBudget.delta
    APrimeFirstCellJointCrossActual.delta
    APrimeFirstCellJointCrossActual.tau
    APrimeFirstCellFarRowAbsorb.tau
  push_cast
  ring

/-- T468 specialized to the verbatim `momFlowDeriv_le` cross premise. -/
theorem eventually_exactHcrossAt {tauPrime alpha : Real}
    (hTau : 0 < tauPrime) (hAlpha : 0 < alpha)
    (p : Nat) (hp : 1 <= p) :
    actualHcrossExact tauPrime alpha p := by
  filter_upwards [
    APrimeFirstCellJointCrossActual.eventually_crossPart_le
      hTau hAlpha p hp,
    eventually_ge_atTop 2] with N hcross hN
  intro k hk1 hk a r hr
  have hraw := hcross k hk1 hk a r hr
  have hmoment := ycut_moment_eq_weighted_actual_moment
    (tauPrime := tauPrime) (p := p) hN hk a r
  unfold exactHcrossAt
  change APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0
        (endpoint N k))
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k (canonicalM tauPrime N)) r <= _
  have hraw' : APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0
        (endpoint N k))
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k (canonicalM tauPrime N)) r <=
      (1 / (2 * Real.sqrt r)) *
        (((2 * p : Nat) : Real) ^ 2 * (15 / 8 : Real)) *
        (∫ omega,
          |APrimeSmoothWeightActual.cutoff d 0 60 delta (fun _ => 0)
              APrimeSmoothTransition.transitionMesh N k
              (canonicalM tauPrime N) omega *
            ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
              (endpoint N k) r (Gauss.Hflow d N r omega)‖| ^
                (2 * p) ∂(P d)) ^
          ((2 * (p : Real) - 1) / (2 * (p : Real))) *
        (APrimeFirstCellJointCrossActual.favorableRate alpha N (endpoint N k) *
            Real.sqrt (APrimeFirstCellJointCrossActual.currentRate
              alpha N (endpoint N k) r) +
          APrimeFirstCellJointCrossActual.jointEnvelope N *
            APrimeFirstCellJointCrossActual.rho tauPrime alpha N ^
              ((1 : Real) / (2 * (p : Real)))) := by
    simpa only [endpoint, canonicalM, delta,
      APrimeFirstCellJointCrossActual.delta] using hraw
  calc
    _ <= _ := hraw'
    _ = _ := by
      rw [hmoment]
      exact t361_rhs_eq_two_p_literalBfull tauPrime alpha p N
        (endpoint N k) r _

/-- The exact consumer inequality at the totalized left endpoint.  Both the
cross term and `literalBfull` vanish there. -/
theorem exactHcrossAt_zero_r0 (tauPrime alpha : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) :
    exactHcrossAt tauPrime alpha p N k a 0 := by
  unfold exactHcrossAt
  rw [APrimeCrossJointSplit.crossPart_zero_r0]
  simp [APrimeFirstCellFullCrossBudget.literalBfull,
    APrimeFirstCellFullCrossIntegrability.Bfull]

/-- The empty `k = 0` cell retains the existing exact cross-term zero and
literal-rate integral zero statements. -/
theorem k_zero_cross_and_budget (tauPrime alpha : Real) (p N : Nat)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧
      APrimeDuhamelModel.crossPart d N
        (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0 0)
        (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
          2 p N 0 (canonicalM tauPrime N)) 0 = 0 ∧
      (∫ r in (0 : Real)..endpoint N 0,
        APrimeFirstCellFullCrossBudget.literalBfull
          tauPrime alpha p N (endpoint N 0) r) = 0 := by
  refine ⟨by simp only [endpoint, cutNetPt_zero], ?_, ?_⟩
  · simpa only [canonicalM, delta,
      APrimeFirstCellJointCrossActual.delta] using
      (APrimeFirstCellJointCrossActual.crossPart_zero_k0
        tauPrime N p a)
  · simpa only [endpoint, cutNetPt_zero] using
      (APrimeFirstCellFullCrossBudget.integral_literalBfull_k0
        tauPrime alpha p N)

/-- A positive `k = 2` resident in the same literal sharp event, carrying
T468's sample fields and the exact consumer `hcross` inequality. -/
def positiveTwoExactHcrossResident
    (tauPrime alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
    let u0 := endpoint N 0
    let u1 := endpoint N 1
    let v := endpoint N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v <= firstCellT tauPrime N ∧
    2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : Real) v,
      APrimeFirstCellJointCrossRegularity.JointCrossSampleRegularity p
        (APrimeFirstCellJointCrossRegularity.Ycut
          tauPrime delta N 2 a r)
        (APrimeFirstCellJointCrossRegularity.jointRate
          tauPrime delta N 2 a r)) ∧
    (∀ a : LoopArg (d.L N) 2,
      exactHcrossAt tauPrime alpha p N 2 a 0) ∧
    ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Ioc (0 : Real) v,
      exactHcrossAt tauPrime alpha p N 2 a r

theorem positiveTwoExactHcrossResident_of_inputs
    {tauPrime alpha : Real} {p : Nat}
    (hgeometry : APrimeFirstCellJointCrossActual.positiveTwoJointCrossGeometry
      tauPrime alpha p)
    (hcross : actualHcrossExact tauPrime alpha p) :
    positiveTwoExactHcrossResident tauPrime alpha p := by
  filter_upwards [hgeometry, hcross] with N hgeometryN hcrossN
  obtain ⟨omega, homega, hu0, hu1, hu12, hv, hk, hregular⟩ := hgeometryN
  refine ⟨omega, homega, hu0, hu1, hu12, hv, hk, hregular, ?_, ?_⟩
  · intro a
    exact exactHcrossAt_zero_r0 tauPrime alpha p N 2 a
  · exact hcrossN 2 (by norm_num) hk

/-- Closed T476 producer.  It keeps T468's literal event and fixed-moment
quantifier order, and stops at the `hcross` premise itself. -/
theorem exists_exactHcross_with_resident :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ alpha : Real, 0 < alpha -> ∀ p : Nat, 1 <= p ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta alpha) ∧
        actualHcrossExact tauPrime alpha p ∧
        (∀ N, ∀ a : LoopArg (d.L N) 2,
          endpoint N 0 = 0 ∧
          APrimeDuhamelModel.crossPart d N
            (APrimeDriftTimeFamily.momentAt
              d 0 60 N p Step2.sigPM a 0 0)
            (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
              (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
              2 p N 0 (canonicalM tauPrime N)) 0 = 0 ∧
          (∫ r in (0 : Real)..endpoint N 0,
            APrimeFirstCellFullCrossBudget.literalBfull
              tauPrime alpha p N (endpoint N 0) r) = 0) ∧
        positiveTwoExactHcrossResident tauPrime alpha p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellJointCrossActual.exists_actualJointCrossBound
  refine ⟨tauPrime, hTau, ?_⟩
  intro alpha hAlpha p hp
  obtain ⟨hmeas, hprob, _hraw, hgeometry⟩ := hall alpha hAlpha p hp
  have hcross := eventually_exactHcrossAt hTau hAlpha p hp
  exact ⟨hmeas, hprob, hcross,
    fun N a => k_zero_cross_and_budget tauPrime alpha p N a,
    positiveTwoExactHcrossResident_of_inputs hgeometry hcross⟩

end

end RBM.APrimeFirstCellHcrossExact

namespace RBM.APrimeFirstCellHcrossExact

#print axioms delta_eq_one_over_two_thousand
#print axioms ycut_moment_eq_weighted_actual_moment
#print axioms t361_rhs_eq_two_p_literalBfull
#print axioms eventually_exactHcrossAt
#print axioms exactHcrossAt_zero_r0
#print axioms k_zero_cross_and_budget
#print axioms positiveTwoExactHcrossResident_of_inputs
#print axioms exists_exactHcross_with_resident

end RBM.APrimeFirstCellHcrossExact
