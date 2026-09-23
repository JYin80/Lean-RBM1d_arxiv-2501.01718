/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellPrefixGoodRows
import RBM1D.Gauss.APrimeFirstCellDeltaFarRowAbsorb

/-!
# T539: absorbed favorable prefix gradient on the moving first cell

The stored three-row bracket is absorbed in the literal favorable prefix
bound, uniformly over every actual moving first-cell endpoint.
-/

namespace RBM.APrimeFirstCellDeltaPrefixAbsorbed

open Filter Set Real Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow

theorem earlyRows_eq_storedBracket (delta : ℝ) (N : ℕ) (v u : ℝ) :
    APrimeFirstCellPrefixGoodRows.earlyRows delta N v u =
      APrimeFirstCellDeltaFarRowAbsorb.storedBracket delta N v u := by
  simp only [APrimeFirstCellPrefixGoodRows.earlyRows,
    APrimeFirstCellDeltaFarRowAbsorb.storedBracket,
    APrimeFirstCellDeltaFarRowAbsorb.storedNear,
    APrimeFirstCellDeltaFarRowAbsorb.storedQuad,
    APrimeFirstCellDeltaFarRowAbsorb.storedCubic,
    APrimeFirstCellDeltaFarRowAbsorb.tau, Real.rpow_neg_one]

/-- The finite maximum in `bSharp` costs no net-cardinality factor. -/
theorem eventually_bSharp_le {tauPrime delta nu : ℝ} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) (hDelta100 : delta ≤ 1 / 100) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      APrimeFirstCellPrefixGoodRows.bSharp delta nu N k ≤
        (16 * Real.sqrt 3 / Real.exp 1) * Real.sqrt v *
          (N : ℝ) ^ (nu / 2 - 2 * delta) := by
  filter_upwards [APrimeFirstCellDeltaFarRowAbsorb.eventually_storedBracket_le_three
    hTau hDelta hDelta100] with N hrows
  intro k hkTop
  dsimp only
  by_cases hk : 0 < k
  · rw [APrimeFirstCellPrefixGoodRows.bSharp, dite_eq_left hk]
    have hmesh : 0 < APrimeSmoothTransition.transitionMesh N :=
      APrimeSupportRunning.mesh_pos N
    have hmax :
        (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
          Real.sqrt (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N j) *
            Real.sqrt (APrimeFirstCellPrefixGoodRows.earlyRows delta N
              (cutNetPt (fun _ => 0)
                APrimeSmoothTransition.transitionMesh N k)
              (cutNetPt (fun _ => 0)
                APrimeSmoothTransition.transitionMesh N j))) ≤
          Real.sqrt (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k) * Real.sqrt 3 := by
      apply Finset.sup'_le
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hu : cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N j ∈
          Icc (0 : ℝ) (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k) := by
        simpa only using Step2Bootstrap.cutNetPt_mem_Icc
          (s := fun _ => (0 : ℝ)) hmesh hjk.le
      have hE : APrimeFirstCellPrefixGoodRows.earlyRows delta N
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ≤ 3 := by
        rw [earlyRows_eq_storedBracket]
        exact hrows k hkTop _ hu
      exact mul_le_mul (Real.sqrt_le_sqrt hu.2) (Real.sqrt_le_sqrt hE)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hcoef : 0 ≤ (16 / Real.exp 1) *
        (N : ℝ) ^ (nu / 2 - 2 * delta) := by positivity
    calc
      (16 / Real.exp 1) * (N : ℝ) ^ (nu / 2 - 2 * delta) *
          (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
            Real.sqrt (cutNetPt (fun _ => 0)
              APrimeSmoothTransition.transitionMesh N j) *
              Real.sqrt (APrimeFirstCellPrefixGoodRows.earlyRows delta N
                (cutNetPt (fun _ => 0)
                  APrimeSmoothTransition.transitionMesh N k)
                (cutNetPt (fun _ => 0)
                  APrimeSmoothTransition.transitionMesh N j))) ≤
          (16 / Real.exp 1) * (N : ℝ) ^ (nu / 2 - 2 * delta) *
            (Real.sqrt (cutNetPt (fun _ => 0)
              APrimeSmoothTransition.transitionMesh N k) * Real.sqrt 3) :=
        mul_le_mul_of_nonneg_left hmax hcoef
      _ = (16 * Real.sqrt 3 / Real.exp 1) *
          Real.sqrt (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k) *
            (N : ℝ) ^ (nu / 2 - 2 * delta) := by ring
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simp [APrimeFirstCellPrefixGoodRows.bSharp, cutNetPt_zero]

/-- The literal sharp event and the exact strict transition imply the absorbed
favorable prefix-gradient estimate. -/
theorem eventually_prefixGradient_le {tauPrime delta nu : ℝ}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (hDelta100 : delta ≤ 1 / 100) (hNu : 0 < nu) :
    ∀ᶠ N : ℕ in atTop,
      ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta nu N,
      ∀ k, 1 ≤ k →
        k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh N →
        omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega ≤
          (16 * Real.sqrt 3 / Real.exp 1) * Real.sqrt v *
            (N : ℝ) ^ (nu / 2 - 2 * delta) := by
  filter_upwards [
    APrimeFirstCellPrefixGoodRows.eventually_prefixGradient_le_bSharp
      hTau hDelta.le hNu,
    eventually_bSharp_le (nu := nu) hTau hDelta hDelta100] with N hraw habs
  intro omega homega k hk hkTop htrans
  exact (hraw omega homega k hk hkTop htrans).trans (habs k hkTop)

/-- Named closed predicate for the absorbed transition-sample conclusion. -/
def absorbedTransitionPrefixBound (tauPrime delta nu : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta nu N,
    ∀ k, 1 ≤ k →
      k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega ≤
        (16 * Real.sqrt 3 / Real.exp 1) * Real.sqrt v *
          (N : ℝ) ^ (nu / 2 - 2 * delta)

/-- The empty prefix has exactly zero absorbed favorable rate. -/
theorem bSharp_zero (delta nu : ℝ) (N : ℕ) :
    APrimeFirstCellPrefixGoodRows.bSharp delta nu N 0 = 0 :=
  APrimeFirstCellPrefixGoodRows.bSharp_zero delta nu N

/-- The first prefix has exactly zero absorbed favorable rate. -/
theorem bSharp_one (delta nu : ℝ) (N : ℕ) :
    APrimeFirstCellPrefixGoodRows.bSharp delta nu N 1 = 0 :=
  APrimeFirstCellPrefixGoodRows.bSharp_one delta nu N

/-- The actual empty-prefix gradient is exactly zero at the canonical order. -/
theorem prefixGradient_zero (tauPrime delta : ℝ) (N : ℕ) (omega : Ω d) :
    APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega = 0 := by
  exact APrimeFirstCellPrefixGoodRows.prefixGradient_zero delta N _
    (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega

/-- On the literal event and strict transition, the actual first prefix is
exactly zero. -/
theorem eventually_prefixGradient_one_eq_zero {tauPrime delta nu : ℝ}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hNu : 0 < nu) :
    ∀ᶠ N : ℕ in atTop,
      ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta nu N,
      1 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N →
      omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 1
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) →
      APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 1
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega = 0 := by
  exact APrimeFirstCellPrefixGoodRows.eventually_prefixGradient_one_eq_zero
    hTau hDelta.le hNu

/-- A positive `k=2` endpoint on the same literal event, retaining only the
geometry and absorbed favorable rate.  No transition inhabitance or weight-one
claim is part of this predicate. -/
def positiveTwoAbsorbedGeometry (tauPrime delta nu : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
        tauPrime delta nu N,
    let u0 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    let u1 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 1
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v ≤ firstCellT tauPrime N ∧
    2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ∧
    APrimeFirstCellPrefixGoodRows.bSharp delta nu N 0 = 0 ∧
    APrimeFirstCellPrefixGoodRows.bSharp delta nu N 1 = 0 ∧
    APrimeFirstCellPrefixGoodRows.bSharp delta nu N 2 ≤
      (16 * Real.sqrt 3 / Real.exp 1) * Real.sqrt v *
        (N : ℝ) ^ (nu / 2 - 2 * delta)

theorem positiveTwoAbsorbedGeometry_of_rows {tauPrime delta nu : ℝ}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (hDelta100 : delta ≤ 1 / 100)
    (hpositive : APrimeFirstCellQVEarlyRows.positiveRowsPlateau
      tauPrime delta nu) :
    positiveTwoAbsorbedGeometry tauPrime delta nu := by
  filter_upwards [
    APrimeFirstCellPrefixGoodRows.positive_two_same_event_geometry hpositive,
    eventually_bSharp_le (nu := nu) hTau hDelta hDelta100] with N hgeom habs
  obtain ⟨omega, homega, hu0, hu1, hu12, hv, hk2, hb0, hb1,
    _hrow0, _hrow1⟩ := hgeom
  exact ⟨omega, homega, hu0, hu1, hu12, hv, hk2, hb0, hb1,
    habs 2 hk2⟩

/-- Closed producer with measurable high-probability event, the absorbed
transition bound, and a positive same-event `k=2` resident. -/
theorem exists_absorbedTransitionPrefixBound :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
      ∀ nu : ℝ, 0 < nu →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta nu N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            tauPrime delta nu) ∧
        absorbedTransitionPrefixBound tauPrime delta nu ∧
        positiveTwoAbsorbedGeometry tauPrime delta nu := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellPrefixGoodRows.exists_transitionPrefixBound_with_plateau
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 nu hNu
  obtain ⟨hmeas, hprob, _hraw, hpositive⟩ :=
    hall delta hDelta hDelta100 nu hNu
  exact ⟨hmeas, hprob,
    by simpa only [absorbedTransitionPrefixBound] using
      (eventually_prefixGradient_le hTau hDelta hDelta100 hNu),
    positiveTwoAbsorbedGeometry_of_rows hTau hDelta hDelta100 hpositive⟩

#print axioms earlyRows_eq_storedBracket
#print axioms eventually_bSharp_le
#print axioms eventually_prefixGradient_le
#print axioms absorbedTransitionPrefixBound
#print axioms bSharp_zero
#print axioms bSharp_one
#print axioms prefixGradient_zero
#print axioms eventually_prefixGradient_one_eq_zero
#print axioms positiveTwoAbsorbedGeometry
#print axioms positiveTwoAbsorbedGeometry_of_rows
#print axioms exists_absorbedTransitionPrefixBound

end RBM.APrimeFirstCellDeltaPrefixAbsorbed
