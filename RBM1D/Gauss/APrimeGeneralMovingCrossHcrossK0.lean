/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1091: the literal zero-boundary cross premise on the first moving cell

At `k = 0`, the target mesh endpoint is exactly `s N`.  The actual smooth
T615 weight has constant value one on this zero-length prefix, so its
coordinate derivative vanishes.  This proves the `momFlowDeriv_le` cross
premise with `Bc = 0`; it does not claim a positive-duration first cell.
-/

namespace RBM.APrimeGeneralMovingCrossHcrossK0

open MeasureTheory Set Gauss CutHypTheta APrimeDuhamelModel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The moving target mesh endpoint for `k = 0` is the left endpoint. -/
theorem firstCell_endpoint (s : ℕ → ℝ) (D : ℝ) (N : ℕ) :
    cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0 = s N := by
  exact cutNetPt_zero s (APrimeGeneralMovingMesh.targetMesh D) N

/-- Consequently the closed first cell is the singleton `{s N}`. -/
theorem firstCell_closedCell_eq_singleton (s : ℕ → ℝ) (D : ℝ) (N : ℕ) :
    Set.Icc (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) =
      {s N} := by
  rw [firstCell_endpoint s D N]
  ext r
  simp only [Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · intro h
    subst r
    exact ⟨le_rfl, le_rfl⟩

/-- The actual T615 smooth weight, with its canonical soft maximum and
`Step2.sigPM` charge, on the general-moving mesh. -/
noncomputable def actualWeight (E D δ : ℝ) (s t : ℕ → ℝ)
    (p N k : ℕ) : Gauss.Ω d → ℝ :=
  APrimeSmoothWeightActual.weight d E D δ s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

/-- The coordinate derivative of that same literal actual weight. -/
noncomputable def actualWeightD (E D δ : ℝ) (s t : ℕ → ℝ)
    (p N k : ℕ) :
    (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ :=
  APrimeSmoothWeightActual.weightD d E D δ s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)

/-- The right-hand side of `momFlowDeriv_le`'s cross premise is exactly zero
when `Bc = 0`, including when the moment integral itself is zero. -/
theorem actual_hcross_rhs_eq_zero (E D δ : ℝ) (s t : ℕ → ℝ)
    (N p : ℕ) (a : LoopArg (d.L N) 2) (u : ℝ) :
    2 * (p : ℝ) *
      (∫ ω, actualWeight E D δ s t p N 0 ω *
        |APrimeDuhamelModel.flowY d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) (s N))
          u ω| ^ (2 * p) ∂(Gauss.P d)) ^
            ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (0 : ℝ) = 0 := by
  simp

/-- In particular, the exact zero-boundary right-hand side is nonnegative,
even if its moment integral is zero. -/
theorem actual_hcross_rhs_nonneg (E D δ : ℝ) (s t : ℕ → ℝ)
    (N p : ℕ) (a : LoopArg (d.L N) 2) (u : ℝ) :
    0 ≤ 2 * (p : ℝ) *
      (∫ ω, actualWeight E D δ s t p N 0 ω *
        |APrimeDuhamelModel.flowY d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) (s N))
          u ω| ^ (2 * p) ∂(Gauss.P d)) ^
            ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (0 : ℝ) := by
  rw [actual_hcross_rhs_eq_zero]

/-- T615's actual smooth weight discharges the exact `momFlowDeriv_le`
cross premise at `k = 0`, for every `p ≥ 1`, output `a`, and real time `u`.
The time interval in the first cell is a singleton, but the bound here is
algebraic and does not assert positive duration. -/
theorem actual_hcross_k0 (E D δ : ℝ) (s t : ℕ → ℝ)
    (N p : ℕ) (_hp : 1 ≤ p) (a : LoopArg (d.L N) 2) (u : ℝ) :
    APrimeDuhamelModel.crossPart d N
        (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N) (s N))
        (actualWeightD E D δ s t p N 0) u ≤
      2 * (p : ℝ) *
        (∫ ω, actualWeight E D δ s t p N 0 ω *
          |APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) (s N))
            u ω| ^ (2 * p) ∂(Gauss.P d)) ^
              ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (0 : ℝ) := by
  have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N :=
    APrimeSmoothWeightActual.canonicalM_pos d s t
      (APrimeGeneralMovingMesh.targetMesh D) N
  have hzero := APrimeCrossJointSplit.crossPart_zero_k0 d E D δ s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 N
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N) p hm
    (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N) (s N)) u
  simpa [actualWeightD] using hzero.le

/-- The cross term itself vanishes on the zero prefix. -/
theorem actual_crossPart_k0_eq_zero (E D δ : ℝ) (s t : ℕ → ℝ)
    (N p : ℕ) (_hp : 1 ≤ p) (a : LoopArg (d.L N) 2) (u : ℝ) :
    APrimeDuhamelModel.crossPart d N
        (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N) (s N))
        (actualWeightD E D δ s t p N 0) u = 0 := by
  have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N :=
    APrimeSmoothWeightActual.canonicalM_pos d s t
      (APrimeGeneralMovingMesh.targetMesh D) N
  have hzero := APrimeCrossJointSplit.crossPart_zero_k0 d E D δ s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 N
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N) p hm
    (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N) (s N)) u
  simpa [actualWeightD] using hzero

/-- T995's explicit nondegenerate witness for the wider positive-cell model.
It concerns its first positive cell `k = 1`, not positive duration at `k = 0`.
-/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms actual_hcross_k0
#print axioms actual_hcross_rhs_nonneg
#print axioms actual_crossPart_k0_eq_zero
#print axioms t995_positive_cell_witness

end

end RBM.APrimeGeneralMovingCrossHcrossK0
