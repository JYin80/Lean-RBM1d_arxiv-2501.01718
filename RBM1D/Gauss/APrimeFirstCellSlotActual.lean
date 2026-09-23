/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellWeightedMomentActual
import RBM1D.Gauss.APrimeFirstCellPiecewiseWeightFields
import RBM1D.Gauss.APrimeSlotFields

/-!
# T576: restricted actual first-cell `APrimeHypOn` and slot

Conditional on T571's exact `WeightedMoment`, this file constructs only the
`E = 0`, `D = 60`, `s = 0`, first-cell instance, with the literal
`transitionMesh` and p-independent `piecewiseW`.  It does not construct a
general moving-window family or an all-energy/all-decay A-prime slot.
-/

namespace RBM.APrimeFirstCellSlotActual

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The single norm event used by the restricted first-cell slot. -/
def firstCellGood (N : ℕ) : Set (Ω d) :=
  {omega | ‖Xmat d N omega‖ ≤ (N : ℝ)}

/-- T573's weight is definitionally the p-independent weight used by T571. -/
theorem piecewiseWeight_eq (tauPrime delta : ℝ) (N k : ℕ) :
    APrimeFirstCellPiecewiseWeightFields.weight tauPrime delta N k =
      APrimeFirstCellWeightedMomentActual.firstCellWeight
        tauPrime delta N k := by
  rfl

/-- Exact fineness of the literal mesh at `Kmod = 122`, `gamma = 1/2`. -/
theorem eventually_transitionMesh_fine :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * (60 : ℝ)) *
          (1 / APrimeSmoothTransition.transitionMesh N) ^ ((1 : ℝ) / 2) ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsmall : (N : ℝ) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  rw [show (2 : ℝ) + 2 * 60 = 122 by norm_num,
    APrimeSupportRunning.mesh_error hN]
  exact hsmall

/-- The first-cell net has eventually at most polynomial cardinality exponent `249`. -/
theorem eventually_firstCell_card_le {tauPrime : ℝ} (hTau : 0 < tauPrime) :
    ∀ᶠ N : ℕ in atTop,
      (firstCellT tauPrime N - 0) * APrimeSmoothTransition.transitionMesh N + 2 ≤
        (N : ℝ) ^ (249 : ℝ) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNr3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have ht := (APrimeSupportRunning.firstT_bounds hTau N).2
  have hmesh : APrimeSmoothTransition.transitionMesh N = (N : ℝ) ^ (248 : ℕ) := by
    unfold APrimeSmoothTransition.transitionMesh
    rw [max_eq_right hNr1]
  have hmesh1 : (1 : ℝ) ≤ APrimeSmoothTransition.transitionMesh N := by
    rw [hmesh]
    exact one_le_pow₀ hNr1
  have hnonneg : 0 ≤ APrimeSmoothTransition.transitionMesh N :=
    (APrimeSupportRunning.mesh_pos N).le
  have ht1 : firstCellT tauPrime N - 0 ≤ 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right ht1 hnonneg
  calc
    (firstCellT tauPrime N - 0) * APrimeSmoothTransition.transitionMesh N + 2
        ≤ APrimeSmoothTransition.transitionMesh N + 2 := by
          simpa using add_le_add_right hmul 2
    _ ≤ (N : ℝ) * APrimeSmoothTransition.transitionMesh N := by
          nlinarith
    _ = (N : ℝ) ^ (249 : ℝ) := by
          rw [hmesh, show (249 : ℝ) = (249 : ℕ) by norm_num,
            Real.rpow_natCast]
          ring

/-- T571's positive resident simultaneously has a positive first-cell window,
belongs to the slot's norm event, and has p-independent weight one. -/
def positiveGoodWeightOnePackage (tauPrime delta : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ omega ∈ firstCellGood N,
      0 < firstCellT tauPrime N ∧
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧
      2 ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      v ≤ 1 / 2 ∧
      APrimeFirstCellWeightedMomentActual.firstCellWeight
        tauPrime delta N 2 omega = 1

/-- The same sample exported by T571 is in the literal norm event. -/
theorem positiveGoodWeightOnePackage_of_piecewise
    {tauPrime delta : ℝ} (hTau : 0 < tauPrime)
    (hpositive :
      APrimeFirstCellWeightedMomentActual.positiveTwoPiecewiseWeightPackage
        tauPrime delta) :
    positiveGoodWeightOnePackage tauPrime delta := by
  filter_upwards [hpositive,
    Gauss.first_cell_window_nondegenerate d hTau] with N hpositiveN hwindow
  obtain ⟨omega, homega, hvpos, hk, hvhalf, hweight⟩ := hpositiveN
  have hcommon : omega ∈ APrimeFirstCellMovingSupport.commonEvent tauPrime
      (APrimeFirstCellEGAllOutputRunning.sourceLoss (delta / 16))
      (APrimeFirstCellEGAllOutputRunning.sourceLoss (delta / 16))
      (delta / 16) N := homega.2
  have hdyn :=
    APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hcommon
  have hraw := APrimeSupportRunning.good_subset tauPrime (delta / 16) N hdyn
  have hgood : omega ∈ firstCellGood N := by
    simpa only [firstCellGood] using hraw.1.1.1
  have htpos : 0 < firstCellT tauPrime N := by
    have hzero :
        gridT ((band d).W N : ℝ) tauPrime (1 / 2 : ℝ) 0 = 0 :=
      gridT_zero (by norm_num)
    rw [hzero] at hwindow
    simpa only [firstCellT] using hwindow
  exact ⟨omega, hgood, htpos, hvpos, hk, hvhalf, hweight⟩

/-- The exact restricted first-cell `APrimeHypOn`, conditional only on T571's
literal `WeightedMoment`. -/
noncomputable def firstCellAPrimeHypOn_of_weightedMoment
    {tauPrime : ℝ} (hTau : 0 < tauPrime)
    (hmom : APrimeFirstCellWeightedMomentActual.firstCellWeightedMoment tauPrime) :
    APrimeHypOn (P d)
      APrimeFirstCellWeightedMomentActual.firstCellJ
      (fun _ => 0) (firstCellT tauPrime)
      (fun _ _ => 1) (fun _ => 1) firstCellGood := by
  have hfields := APrimeFirstCellPiecewiseWeightFields.fields tauPrime
  exact APrimeSlotFields.aprimeHypOn_jSnorm_event d
    (E := 0) (D := 60) (t₀ := 1 / 2)
    (s := fun _ => 0) (t := firstCellT tauPrime) (Good := firstCellGood)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => le_rfl)
    (fun N => (APrimeSupportRunning.firstT_bounds hTau N).2)
    (fun N => (APrimeSupportRunning.firstT_bounds hTau N).1)
    (fun N => by simpa only [firstCellGood] using
      (show {omega : Ω d | ‖Xmat d N omega‖ ≤ (N : ℝ)} ⊆
          {omega : Ω d | ‖Xmat d N omega‖ ≤ (N : ℝ)} from subset_rfl))
    (fun N => by simpa only [firstCellGood] using
      (Gauss.measurableSet_normX_le d N))
    (1 / 100) (by norm_num)
    APrimeSmoothTransition.transitionMesh APrimeSupportRunning.mesh_pos
    eventually_transitionMesh_fine 249 (eventually_firstCell_card_le hTau)
    (APrimeFirstCellWeightedMomentActual.firstCellWeight tauPrime)
    (by simpa [d, piecewiseWeight_eq] using hfields.1)
    (by simpa [d, piecewiseWeight_eq] using hfields.2.1)
    (by simpa [d, piecewiseWeight_eq] using hfields.2.2.1)
    (by simpa [d, piecewiseWeight_eq] using hfields.2.2.2)
    hmom

/-- Projection guard for all exact deterministic and weight identities. -/
theorem firstCellAPrimeHypOn_fields
    {tauPrime : ℝ} (hTau : 0 < tauPrime)
    (hmom : APrimeFirstCellWeightedMomentActual.firstCellWeightedMoment tauPrime) :
    let H := firstCellAPrimeHypOn_of_weightedMoment hTau hmom
    H.mesh = APrimeSmoothTransition.transitionMesh ∧
      H.Kmod = 122 ∧ H.γ = 1 / 2 ∧ H.Ccard = 249 ∧
      H.δ₀ = 1 / 100 ∧
      H.W = APrimeFirstCellWeightedMomentActual.firstCellWeight tauPrime := by
  dsimp only [firstCellAPrimeHypOn_of_weightedMoment,
    APrimeSlotFields.aprimeHypOn_jSnorm_event]
  norm_num

/-- The honest three-field wrapper at the same fixed energy, decay exponent,
window, event, mesh and weight. -/
noncomputable def firstCellAPrimeSlotAtD60_of_weightedMoment
    {tauPrime : ℝ} (hTau : 0 < tauPrime)
    (hmom : APrimeFirstCellWeightedMomentActual.firstCellWeightedMoment tauPrime) :
    APrimeSlotFields.APrimeSlot' (sample d) 0
      (fun _ => 0) (firstCellT tauPrime) 60 where
  Good := firstCellGood
  hyp := firstCellAPrimeHypOn_of_weightedMoment hTau hmom
  good := by
    change HighProb (P d)
      (fun N => {omega : Ω d | ‖Xmat d N omega‖ ≤ (N : ℝ)})
    exact Gauss.highProb_norm_Xmat_le d

/-- Consume T571 without widening any quantifier: one first-cell slot and its
same-sample positive Good/weight-one witness. -/
theorem exists_firstCellAPrimeSlotAtD60 :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
      ∃ S : APrimeSlotFields.APrimeSlot' (sample d) 0
          (fun _ => 0) (firstCellT tauPrime) 60,
        (∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
          positiveGoodWeightOnePackage tauPrime delta) ∧
        S.Good = firstCellGood ∧
        S.hyp.mesh = APrimeSmoothTransition.transitionMesh ∧
        S.hyp.Kmod = 122 ∧ S.hyp.γ = 1 / 2 ∧
        S.hyp.Ccard = 249 ∧ S.hyp.δ₀ = 1 / 100 ∧
        S.hyp.W = APrimeFirstCellWeightedMomentActual.firstCellWeight tauPrime := by
  obtain ⟨tauPrime, hTau, hmom, hpositive⟩ :=
    APrimeFirstCellWeightedMomentActual.exists_firstCellWeightedMomentActual
  let S := firstCellAPrimeSlotAtD60_of_weightedMoment hTau hmom
  refine ⟨tauPrime, hTau, S, ?_, rfl, ?_⟩
  · intro delta hDelta hDelta100
    exact positiveGoodWeightOnePackage_of_piecewise hTau
      (hpositive delta hDelta hDelta100)
  · simp [S, firstCellAPrimeSlotAtD60_of_weightedMoment,
      firstCellAPrimeHypOn_fields hTau hmom]

#print axioms firstCellGood
#print axioms piecewiseWeight_eq
#print axioms eventually_transitionMesh_fine
#print axioms eventually_firstCell_card_le
#print axioms positiveGoodWeightOnePackage
#print axioms positiveGoodWeightOnePackage_of_piecewise
#print axioms firstCellAPrimeHypOn_of_weightedMoment
#print axioms firstCellAPrimeHypOn_fields
#print axioms firstCellAPrimeSlotAtD60_of_weightedMoment
#print axioms exists_firstCellAPrimeSlotAtD60

end

end RBM.APrimeFirstCellSlotActual
