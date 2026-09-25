/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossPositive

/-!
# T1111: the literal time-zero cross premise for the actual moving weight

At `r = 0`, the cross-part convention in the Gaussian generator makes the
left side zero. The exact T615 actual-weight `hcross` premise therefore holds
with `Bc = 0` on every closed target cell containing zero, including positive
prefixes whose left endpoint is zero. This is a time-zero input only.
-/

namespace RBM.APrimeGeneralMovingCrossHcrossTimeZero

open MeasureTheory Set Gauss CutHypTheta APrimeDuhamelModel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual T615 smooth weight on the general-moving target mesh, with the
same canonical smoothing order and `N₀ = 2` as the positive-time producer. -/
noncomputable def actualWeight (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k p : ℕ) : Gauss.Ω d → ℝ :=
  APrimeSmoothWeightActual.weight d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

/-- The coordinate derivative of that same literal actual weight. -/
noncomputable def actualWeightD (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k p : ℕ) :
    (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ :=
  APrimeSmoothWeightActual.weightD d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

/-- The exact `hcross` inequality at `r = 0`, with explicit `Bc = 0`.
The cell-membership and active-index hypotheses state precisely when this
boundary point belongs to a cell to which the moving-mesh consumer applies. -/
theorem actual_hcross_r0
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k p : ℕ)
    (hp : 1 ≤ p)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (hzero : (0 : ℝ) ∈ Set.Icc (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k))
    (a : LoopArg (d.L N) 2) :
    APrimeDuhamelModel.crossPart d N
        (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k))
        (actualWeightD E D deltaWeight s t N k p) 0 ≤
      2 * (p : ℝ) *
        (∫ ω, actualWeight E D deltaWeight s t N k p ω *
          |APrimeDuhamelModel.flowY d N
            (fun u M => APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
              (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
              u M) 0 ω| ^ (2 * p) ∂(Gauss.P d)) ^
            ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (0 : ℝ) := by
  have hzeroCross := APrimeCrossJointSplit.crossPart_zero_r0 d N
    (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k))
    (actualWeightD E D deltaWeight s t N k p)
  simpa using hzeroCross.le

/-- Nonnegativity of the explicit zero budget. -/
theorem zeroBudget_nonneg : 0 ≤ (0 : ℝ) := le_rfl

/-- T995's nondegenerate model witness, reused without changing its losses,
event, sample, or actual smooth weight. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms actual_hcross_r0
#print axioms zeroBudget_nonneg
#print axioms t995_positive_cell_witness

end

end RBM.APrimeGeneralMovingCrossHcrossTimeZero
