/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeNormalizedGenerator
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1083: the actual-weight pointwise generator input

The fixed-endpoint normalized generator bridge is multiplied by T615's literal
nonnegative actual smooth weight.  The resulting inequality is exactly the
`hle` premise of `APrimeDuhamelModel.momFlowDeriv_le`, on the closed moving
cell and for any sign vector.
-/

namespace RBM.APrimeGeneralMovingGeneratorHle

open MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (s t : Nat → Real) (D : Real) (N k : Nat) : Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k

noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight p N k

/-- Literal membership of every target-net endpoint in the outer window. -/
theorem endpoint_mem_window
    {D : Real} {s t : Nat → Real} {N k : Nat}
    (hst : ∀ N, s N ≤ t N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    endpoint s t D N k ∈ Icc (s N) (t N) := by
  exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
    (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)

/-- The exact pointwise `hle` input with T615's actual smooth weight and
same-endpoint normalized drift and QV.  The sign vector is arbitrary; the
model-specific application uses `Step2.sigPM`.  Time is allowed at either
closed-cell endpoint, including zero when `k = 0`. -/
theorem actual_weight_hle
    {E D deltaWeight : Real} {s t : Nat → Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) (σ : Fin 2 → Bool)
    {r : Real} (hr : r ∈ Icc (s N) (endpoint s t D N k))
    (hp : 1 ≤ p) :
    ∀ ω : Ω d,
      weight E D s t deltaWeight p N k ω *
        ((Gauss.timeD1 (APrimeDriftTimeFamily.momentAt d E D N p σ a
          (s N) (endpoint s t D N k)) r (Gauss.Hflow d N r ω)).re +
          APrimeDuhamelModel.genPt d N
            (APrimeDriftTimeFamily.momentAt d E D N p σ a
              (s N) (endpoint s t D N k) r)
            (Gauss.Hflow d N r ω))
      ≤ weight E D s t deltaWeight p N k ω *
        (2 * (p : Real) *
          (|APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d E D N σ a
                (s N) (endpoint s t D N k)) r ω| ^ (2 * p - 1) *
            |APrimeDriftTimeFamily.driftAt d E D N σ a
              (s N) (endpoint s t D N k) r ω|) +
        (p : Real) * (2 * (p : Real) - 1) *
          (|APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d E D N σ a
                (s N) (endpoint s t D N k)) r ω| ^ (2 * p - 2) *
            APrimeDriftTimeFamily.qvAt d E D N σ a
              (s N) (endpoint s t D N k) r ω)) := by
  intro ω
  have hv := endpoint_mem_window (D := D) hst hk
  have hv1 : endpoint s t D N k < 1 := hv.2.trans_lt (ht1 N)
  have hr0 : 0 ≤ r := (hs0 N).trans hr.1
  have hbridge := APrimeNormalizedGenerator.normalizedGeneratorBridge
    d E D N p σ a (s := s N) (v := endpoint s t D N k) (r := r)
    hE (hs0 N) hr.1 hr.2 hv1 hp
  have hw0 : 0 ≤ weight E D s t deltaWeight p N k ω :=
    APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
      E D s t deltaWeight p N k ω
  have hmul := mul_le_mul_of_nonneg_left (hbridge ω) hw0
  simpa only [weight, endpoint] using hmul

/-- The T995 same-resident positive-cell witness records that the actual
smooth-weight context used by this pointwise lemma is nondegenerate. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms endpoint_mem_window
#print axioms actual_weight_hle
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingGeneratorHle
