/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGeneratorConditional
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossPositive

/-!
# T1109: unconditional positive-time general-moving generator seam

Combines the literal p=1 generator consumer with the accepted positive-time
cross producer, using the producer's explicit `positiveTimeCrossBudget` at
the identical endpoint, sample, charge, and closed-cell time.
-/

namespace RBM.APrimeGeneralMovingGeneratorPositive

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

private noncomputable def endpoint (s : Nat → Real) (D : Real) (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

private noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight 1 N k

private noncomputable def coordinate (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a s v

private noncomputable def moment (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) :
    Real → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  APrimeDriftTimeFamily.momentAt d E D N 1 Step2.sigPM a s v

private noncomputable def drift (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a s v

private noncomputable def qv (E D : Real) (N : Nat)
    (a : LoopArg (d.L N) 2) (s v : Real) : Real → Ω d → Real :=
  APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v

/-- For p=1, every active general-moving target cell and every positive time
in its closed cell satisfies the literal `momFlowDeriv_le` conclusion, with
the explicit cross budget from the positive-time producer. All parameters in
the cross estimate and derivative remain the same. -/
theorem eventually_actual_momFlowDeriv_le
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (s N) (endpoint s D N k),
      0 < r →
      APrimeDuhamelModel.momFlowDeriv d N
          (moment E D N a (s N) (endpoint s D N k))
          (weight E D s t deltaWeight N k)
          (APrimeSmoothWeightActual.weightD d E D deltaWeight s t
            (APrimeGeneralMovingMesh.targetMesh D) 2 1 N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N)) r ≤
        2 * (1 : Real) *
            (∫ ω, weight E D s t deltaWeight N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s D N k)) r ω| ^ (2 * 1)
                ∂(P d)) ^ ((2 * (1 : Real) - 1) / (2 * (1 : Real))) *
            (MomentDuhamel.momNormW (P d) (weight E D s t deltaWeight N k)
              1 (drift E D N a (s N) (endpoint s D N k) r) +
              APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
                E D deltaWeight s t N k 1 a r) +
          (1 : Real) * (2 * (1 : Real) - 1) *
            (∫ ω, weight E D s t deltaWeight N k ω *
              |APrimeDuhamelModel.flowY d N
                (coordinate E D N a (s N) (endpoint s D N k)) r ω| ^ (2 * 1)
                ∂(P d)) ^ (((1 : Real) - 1) / (1 : Real)) *
            APrimeModel.rateNormW (P d) (weight E D s t deltaWeight N k)
              1 (qv E D N a (s N) (endpoint s D N k) r) := by
  have hderiv :=
    APrimeGeneralMovingGeneratorConditional.eventually_actual_momFlowDeriv_le_of_hcross
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg
  have hcross :=
    APrimeGeneralMovingCrossHcrossPositive.eventually_positive_time_hcross
      (E := E) (D := D) (c := c) hE hD hs0 hst ht1 hc hreg
      hdeltaWeight 1 (by norm_num : 1 ≤ (1 : Nat))
  filter_upwards [hderiv, hcross] with N hderivN hcrossN
  intro k hk a r hr hrpos
  obtain ⟨hBc, hcrossBound⟩ := hcrossN k hk a r hr hrpos
  have hmomentEq :
      (∫ ω, weight E D s t deltaWeight N k ω *
        |APrimeDuhamelModel.flowY d N
          (coordinate E D N a (s N) (endpoint s D N k)) r ω| ^ (2 * 1)
        ∂(P d)) =
        APrimeGeneralMovingCrossHcrossPositive.actualWeightedMoment
          E D deltaWeight s t N k 1 a r := by
    rw [APrimeGeneralMovingCrossHcrossPositive.actualWeightedMoment]
    apply integral_congr_ae
    filter_upwards with ω
    simp [APrimeGeneralMovingCrossHcrossPositive.actualFlowY,
      weight, coordinate, endpoint, APrimeDriftTimeFamily.coordAt,
      APrimeGeneralMovingSmoothDriftNormBudget.weight] <;> aesop
  have hcrossAligned :
      APrimeDuhamelModel.crossPart d N
          (moment E D N a (s N) (endpoint s D N k))
          (APrimeSmoothWeightActual.weightD d E D deltaWeight s t
            (APrimeGeneralMovingMesh.targetMesh D) 2 1 N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N)) r ≤
        2 * (1 : Real) *
          (∫ ω, weight E D s t deltaWeight N k ω *
            |APrimeDuhamelModel.flowY d N
              (coordinate E D N a (s N) (endpoint s D N k)) r ω| ^ (2 * 1)
              ∂(P d)) ^ ((2 * (1 : Real) - 1) / (2 * (1 : Real))) *
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
            E D deltaWeight s t N k 1 a r := by
    rw [hmomentEq]
    simpa [moment, endpoint, APrimeDriftTimeFamily.momentAt] using hcrossBound
  exact hderivN k hk a r hr
    (APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
      E D deltaWeight s t N k 1 a r) hBc hcrossAligned

/-- The standing context and positive-cell weight hypotheses have a
nondegenerate witness from T995 (`E=0`, `D=60`). This witnesses the model
context only; the theorem's positive-time cross estimate is supplied by its
producer above. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_momFlowDeriv_le
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingGeneratorPositive
