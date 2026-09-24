/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftFarInvScaleSlotRepair
import RBM1D.Gauss.APrimeGeneralMovingDriftFarLeakageSlotRepair

/-!
# T1039: the complete nonlinear bracket in the T615 far source

This module adds the two accepted nonlinear far rows at the same T995
schedule.  Its claim concerns the literal T615 profile in Lean; it does not
identify that decomposition with the schematic far term printed in (5.41).
-/

namespace RBM.APrimeGeneralMovingDriftFarNonlinearSlot

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The sum of the two accepted nonlinear T615 far summands, with their
unchanged endpoint normalization and the actual T586 block cap. -/
noncomputable def normalizedFarNonlinear (E D : Real) (s : Nat → Real)
    (zeta tau delta : Real) (N : Nat) (v u : Real) : Real :=
  APrimeGeneralMovingDriftFarInvScaleSlotRepair.normalizedFarInvScale
      E s zeta tau delta N v u +
    APrimeGeneralMovingDriftFarLeakageSlotRepair.normalizedFarLeakage
      E D s zeta tau delta N v u

/-- Expanding the sum gives exactly the two positive spatial coefficients
inside the nonlinear `Jbar * sqrt Jbar` bracket of T615's `farSourceCoeff`.
Both `xiK` and both endpoint `ratR` factors remain explicit. -/
theorem normalizedFarNonlinear_eq_T615_bracket
    (E D : Real) (s _t : Nat → Real) (zeta tau delta : Real)
    (N : Nat) (v u : Real) :
    normalizedFarNonlinear E D s zeta tau delta N v u =
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N u ^ (-2 : Real) *
        Step2Moment.ratR E s N v ^ (-2 : Real) *
        ((etaT E u)⁻¹ * (4 * (N : Real)^zeta *
          (B.ell N u / B.ell N (s N))) *
          (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
            Real.sqrt (APrimeGeneralMovingDriftSource.blockCap E s tau delta N u) *
            (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ +
              (d.L N : Real) * Real.sqrt ((d.W N : Real)^(-D)) /
                B.ell N u))) := by
  dsimp [normalizedFarNonlinear,
    APrimeGeneralMovingDriftFarInvScaleSlotRepair.normalizedFarInvScale,
    APrimeGeneralMovingDriftFarLeakageSlotRepair.normalizedFarLeakage]
  ring

/-- The same sum is obtained by removing exactly T615's separate linear
far-source term from the complete `farSourceCoeff`. -/
theorem normalizedFarNonlinear_eq_T615_residual
    (E D : Real) (s t : Nat → Real) (zeta tau delta : Real)
    (N : Nat) (v u : Real) :
    normalizedFarNonlinear E D s zeta tau delta N v u =
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N u ^ (-2 : Real) *
        Step2Moment.ratR E s N v ^ (-2 : Real) *
        (APrimeGeneralMovingDriftAtProfile.farSourceCoeff
            E D s t zeta tau delta N u -
          (etaT E u)⁻¹ * (4 * (N : Real)^zeta *
            (B.ell N u / B.ell N (s N))) *
            (Lemma57.cFar (d.W N : Real) (B.ell N u) *
              APrimeGeneralMovingDriftSource.blockCap E s tau delta N u *
              (flowDelta d E t N + (d.W N : Real)⁻¹))) := by
  dsimp [normalizedFarNonlinear,
    APrimeGeneralMovingDriftFarInvScaleSlotRepair.normalizedFarInvScale,
    APrimeGeneralMovingDriftFarLeakageSlotRepair.normalizedFarLeakage,
    APrimeGeneralMovingDriftAtProfile.farSourceCoeff]
  ring

/-- The sum is interval integrable on every valid cell, including a zero
cell. -/
theorem intervalIntegrable_normalizedFarNonlinear
    {E D : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zeta tau delta : Real) :
    IntervalIntegrable
      (fun u => normalizedFarNonlinear E D s zeta tau delta N v u)
      volume (s N) v := by
  have hInv :=
    APrimeGeneralMovingDriftFarInvScaleSlotRepair.intervalIntegrable_normalizedFarInvScale
      hE hs0 hsv hv1 zeta tau delta
  have hLeak :=
    APrimeGeneralMovingDriftFarLeakageSlotRepair.intervalIntegrable_normalizedFarLeakage
      (D := D) hE hs0 hsv hv1 zeta tau delta
  simpa [normalizedFarNonlinear] using hInv.add hLeak

/-- T995's δ-dependent schedule bounds the complete nonlinear T615 bracket
on every cell `0 ≤ k ≤ cutNetTop`, including `k=0`. -/
theorem eventually_far_nonlinear_integral_le_small_slot
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedFarNonlinear E D s
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        (1 / (mE E).im + 1) * (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
  have hInv :=
    APrimeGeneralMovingDriftFarInvScaleSlotRepair.eventually_far_inv_scale_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hLeak :=
    APrimeGeneralMovingDriftFarLeakageSlotRepair.eventually_far_spatial_leakage_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  filter_upwards [hInv, hLeak] with N hInvN hLeakN
  intro k hk
  dsimp only
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hInvInt :=
    APrimeGeneralMovingDriftFarInvScaleSlotRepair.intervalIntegrable_normalizedFarInvScale
      hE (hs0 N) hv.1 (hv.2.trans_lt (ht1 N))
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
  have hLeakInt :=
    APrimeGeneralMovingDriftFarLeakageSlotRepair.intervalIntegrable_normalizedFarLeakage
      (D := D) hE (hs0 N) hv.1 (hv.2.trans_lt (ht1 N))
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
  have hsum := add_le_add (hInvN k hk) (hLeakN k hk)
  change (∫ u in (s N)..v,
      (APrimeGeneralMovingDriftFarInvScaleSlotRepair.normalizedFarInvScale E s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u +
       APrimeGeneralMovingDriftFarLeakageSlotRepair.normalizedFarLeakage E D s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u)) ≤ _
  calc
    _ = (∫ u in (s N)..v,
          APrimeGeneralMovingDriftFarInvScaleSlotRepair.normalizedFarInvScale E s
            (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) +
        ∫ u in (s N)..v,
          APrimeGeneralMovingDriftFarLeakageSlotRepair.normalizedFarLeakage E D s
            (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u := by
      rw [intervalIntegral.integral_add hInvInt hLeakInt]
    _ ≤ (1 / (mE E).im) * (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) +
        (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := hsum
    _ = (1 / (mE E).im + 1) * (N : Real)^(5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by ring

/-- The shared T995 same-resident positive-cell witness accompanies the
integrated estimate and verifies nondegeneracy of its scheduled hypotheses. -/
noncomputable abbrev scheduled_positive_cell_witness :=
  APrimeGeneralMovingDriftFarLeakageSlotRepair.scheduled_positive_cell_witness

#print axioms normalizedFarNonlinear
#print axioms normalizedFarNonlinear_eq_T615_bracket
#print axioms normalizedFarNonlinear_eq_T615_residual
#print axioms intervalIntegrable_normalizedFarNonlinear
#print axioms eventually_far_nonlinear_integral_le_small_slot
#print axioms scheduled_positive_cell_witness

end RBM.APrimeGeneralMovingDriftFarNonlinearSlot
