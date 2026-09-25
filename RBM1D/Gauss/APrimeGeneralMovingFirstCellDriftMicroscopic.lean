/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualDriftSlotAnyD

/-!
# T1249: microscopic p=1 actual weighted-drift integral on the first cell

The all-sample polynomial drift envelope and the exact target-mesh length give
a microscopic bound for the literal T615 actual-smooth weighted integrand.
This is one input to the first-positive-cell N1 consumer only.
-/

namespace RBM.APrimeGeneralMovingFirstCellDriftMicroscopic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- T995's same-event, positive-actual-weight witness at `E=0`, `D=60`,
`p=1`, and the scheduled first positive cell. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- At `p=1`, the literal T615 `g` integral over `k=1` is bounded by the
all-sample drift envelope times the exact microscopic mesh length. -/
theorem eventually_integral_g_le_microscopic
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (_hB : BoundsCore (Gauss.sample d) E s)
    (_hδ : 0 < δ) (_hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop,
      1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a)
          volume (s N)
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1) ∧
        (∫ u in (s N)..
            (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1),
          APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u)
          ≤ (N : Real) ^ (-3 * D - 10) := by
  have henv := APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [henv, Filter.eventually_ge_atTop 2,
      APrimeGeneralMovingMesh.eventually_targetMesh_eq D] with N henvN hN hmesh
  intro hk a
  have hNpos : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hv : APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1 ∈
      Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N)
      _ (cutNetPt_mem_netFinset hk)
  have hv1 : APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1 < 1 :=
    hv.2.trans_lt (ht1 N)
  have hgi := APrimeGeneralMovingSmoothDriftNormBudget.intervalIntegrable_g
    (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
    (p := 1) hE (hs0) hst ht1 (by omega) hk a
  have hpoint : ∀ u ∈ Icc (s N)
      (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1),
      APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u
          ≤ (N : Real) ^ (D + 8) := by
    intro u hu
    have henvPoint := henvN 1 hk u hu a
    letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
    have hnorm := APrimeModel.momNormW_le_of_le_on
      (P := Gauss.P d)
      (W := APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1)
      (Y := APrimeGeneralMovingSmoothDriftNormBudget.drift E D s t N 1 a u)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1)
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1)
      (p := 1) (by norm_num) (c := (N : Real) ^ (D + 8)) (by positivity)
      (G := Set.univ)
      (by intro ω _; simpa [APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
        APrimeGeneralMovingSmoothDriftNormBudget.drift] using henvPoint ω)
      (by intro ω hω; exact (hω (Set.mem_univ ω)).elim)
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.g,
      APrimeGeneralMovingSmoothDriftNormBudget.drift] using hnorm
  have hmono := intervalIntegral.integral_mono_on hv.1 hgi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : Real => (N : Real) ^ (D + 8)) volume (s N)
        (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1))
    (fun u hu => hpoint u hu)
  refine ⟨hgi, ?_⟩
  calc
    (∫ u in (s N)..
        (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1),
      APrimeGeneralMovingSmoothDriftNormBudget.g E D s t
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 a u)
      ≤ (APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N 1 - s N) *
          (N : Real) ^ (D + 8) := by
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hmono
    _ = ((1 : Real) / APrimeGeneralMovingMesh.targetMesh D N) *
          (N : Real) ^ (D + 8) := by
        simp [APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
          CutHypTheta.cutNetPt]
    _ = (N : Real) ^ (-3 * D - 10) := by
      rw [hmesh, one_div, ← Real.rpow_neg hNpos.le,
        ← Real.rpow_add hNpos]
      congr 1
      ring

end

#print axioms eventually_integral_g_le_microscopic
#print axioms nondegenerate_positive_cell_witness

end RBM.APrimeGeneralMovingFirstCellDriftMicroscopic
