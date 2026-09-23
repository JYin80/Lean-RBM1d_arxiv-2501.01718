/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaCommonBudgetPackage

/-!
# T559: common-event positive two-weight plateau

The single `tauPrime` selected by T555 is reused.  Event nonemptiness at the
positive `k = 2` prefix is combined with the target- and canonical-weight
plateau theorems, both of which hold for every sample of the same literal
sharp common event.

No stochastic budget resident is attached to the selected sample.
-/

namespace RBM.APrimeFirstCellDeltaCommonWeightPlateau

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

/-- On one sample of the literal event, the target weight at order `p` and
the canonical weight at `highOrder delta p` are simultaneously one at the
strictly positive active endpoint `k = 2`. -/
def positiveCommonWeightPlateau
    (tauPrime delta : Real) (p : Nat) : Prop :=
  let alpha := delta / 16
  let q := APrimeFirstCellDeltaTargetWeight.highOrder delta p
  ∀ᶠ N : Nat in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta alpha N,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧
        2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh N ∧
        v ≤ 1 / 2 ∧
        APrimeFirstCellDeltaTargetWeight.targetWeight
          tauPrime delta p N 2 omega = 1 ∧
        APrimeFirstCellCanonicalPlateau.canonicalWeight
          tauPrime delta q N 2 omega = 1

/-- T555's event nonemptiness supplies one sample.  Since both plateau
theorems are universal over samples of that exact event, they apply to the
same chosen sample without intersecting event witnesses. -/
theorem positiveCommonWeightPlateau_of_geometry
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) (p : Nat)
    (hgeometry :
      APrimeFirstCellDeltaCommonBudgetPackage.eventNonemptyPositiveTwoGeometry
        tauPrime delta (delta / 16)) :
    positiveCommonWeightPlateau tauPrime delta p := by
  have hAlpha : 0 < delta / 16 := by positivity
  have htarget :=
    APrimeFirstCellDeltaTargetWeight.eventually_targetWeight_two_one_on_sharpCommonEvent
      (alpha := delta / 16) hTau hDelta
  have hcanonical :=
    APrimeFirstCellCanonicalPlateau.eventually_canonicalWeight_one_on_sharpCommonEvent
      hTau hDelta hAlpha
  filter_upwards [hgeometry, htarget, hcanonical]
      with N hgeom htargetN hcanonicalN
  obtain ⟨⟨omega, homega⟩, hvpos, hscale⟩ := hgeom
  refine ⟨omega, homega, hvpos, hscale.resident, hscale.time_le_half, ?_, ?_⟩
  · exact htargetN omega homega p
  · exact hcanonicalN omega homega
      (APrimeFirstCellDeltaTargetWeight.highOrder delta p)

/-- Closed producer using exactly T555's one `tauPrime`.  Only the common
two-weight plateau is retained; none of T555's cross, QV, drift, or initial
resident predicates is transferred to the selected sample. -/
theorem exists_commonWeightPlateau :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta → delta ≤ 1 / 100 →
      ∀ p : Nat, 1 ≤ p →
        positiveCommonWeightPlateau tauPrime delta p := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellDeltaCommonBudgetPackage.exists_commonBudgetPackage
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 p hp
  have hpackage := hall delta hDelta hDelta100 p hp
  dsimp only at hpackage
  obtain ⟨_hmeas, _hprob, _hq, _hactive, _hzero, hgeometry⟩ := hpackage
  exact positiveCommonWeightPlateau_of_geometry hTau hDelta p hgeometry

#print axioms positiveCommonWeightPlateau
#print axioms positiveCommonWeightPlateau_of_geometry
#print axioms exists_commonWeightPlateau

end

end RBM.APrimeFirstCellDeltaCommonWeightPlateau
