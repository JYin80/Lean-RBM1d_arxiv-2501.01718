/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDuhamelModel
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1075: exact moving actual-weighted generator measurability inputs

This file supplies the two weighted strong-measurability premises consumed by
`APrimeDuhamelModel.momFlowDeriv_le`, with the literal T615 smooth weight,
normalized drift, and fixed-charge Step2 QV rate.
-/

namespace RBM.APrimeGeneralMovingWeightedRateMeasurable

open MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (s t : Nat → Real) (D : Real) (N k : Nat) : Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k

noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight p N k

noncomputable def drift (E D : Real) (s t : Nat → Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.drift E D s t N k a u

noncomputable def qv (E D : Real) (s t : Nat → Real) (N k : Nat)
    (a : LoopArg (d.L N) 2) (u : Real) : Ω d → Real :=
  APrimeGeneralMovingActualSmoothQVNormBudget.qv E D s t N k a u

private theorem measurable_weight
    {E D : Real} {s t : Nat → Real} {deltaWeight : Real} {p N k : Nat}
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    Measurable (weight E D s t deltaWeight p N k) := by
  exact APrimeGeneralMovingSmoothDriftNormBudget.measurable_weight
    (deltaWeight := deltaWeight) hE hst ht1 hN hk

private theorem weight_nonneg (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) (ω : Ω d) :
    0 ≤ weight E D s t deltaWeight p N k ω :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
    E D s t deltaWeight p N k ω

private theorem drift_measurable
    {E D : Real} {s t : Nat → Real} {N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k)) :
    Measurable (drift E D s t N k a u) := by
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint s t D N k < 1 := hv.2.trans_lt (ht1 N)
  have hdrift : Measurable (drift E D s t N k a u) := by
    have hf := (Gauss.continuous_uker_driftF_omega d E N
      (Gauss.window_im_ne_zero hE hv1 u hu)
      (Gauss.window_norm_mul_lt hE.le (hs0 N) hv1 u hu)
      Step2.sigPM a (((endpoint s t D N k : Real) : Complex))).norm.div_const
        (APrimeDriftTimeFamily.driftScale d E D N a
          (s N) (endpoint s t D N k))
    unfold drift APrimeGeneralMovingSmoothDriftNormBudget.drift
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint
      APrimeDriftTimeFamily.driftAt
    exact hf.measurable
  exact hdrift

theorem hGm
    {E D : Real} {s t : Nat → Real} {deltaWeight : Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k)) (hp : 1 ≤ p) :
    AEStronglyMeasurable
      (APrimeDuhamelModel.wscale (weight E D s t deltaWeight p N k) p
        (drift E D s t N k a u)) (P d) := by
  have hw := measurable_weight (deltaWeight := deltaWeight) (p := p)
    hE hst ht1 hN hk
  have hg := drift_measurable hE hs0 hst ht1 hk a hu
  have hp0 : (0 : Real) < (p : Real) := by
    have hp' : (1 : Real) ≤ (p : Real) := by exact_mod_cast hp
    linarith
  have hwr : Measurable (fun ω : Ω d =>
      weight E D s t deltaWeight p N k ω ^ ((1 : Real) / (2 * (p : Real)))) :=
    (Real.continuous_rpow_const (by positivity :
      (0 : Real) ≤ (1 : Real) / (2 * (p : Real)))).measurable.comp hw
  have hprod : Measurable (fun ω : Ω d =>
      weight E D s t deltaWeight p N k ω ^ ((1 : Real) / (2 * (p : Real))) *
        drift E D s t N k a u ω) := hwr.mul hg
  exact hprod.aestronglyMeasurable

theorem hQm
    {E D : Real} {s t : Nat → Real} {deltaWeight : Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k)) (hp : 1 ≤ p) :
    AEStronglyMeasurable
      (APrimeDuhamelModel.wscaleQ (weight E D s t deltaWeight p N k) p
        (qv E D s t N k a u)) (P d) := by
  let uu : Icc (s N) (endpoint s t D N k) := ⟨u, hu⟩
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hq : Measurable (qv E D s t N k a u) := by
    have hembed : Measurable (fun ω : Ω d => (uu, ω)) :=
      measurable_const.prodMk measurable_id
    have hjoint := APrimeQVRateTime.measurable_qvAt_on_window
      d E D N Step2.sigPM a hE (hs0 N) hv.1 (hv.2.trans_lt (ht1 N))
    have hcomp := hjoint.comp hembed
    simpa only [uu, qv, APrimeGeneralMovingActualSmoothQVNormBudget.qv,
      APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingQVNormBudget.endpoint,
      APrimeGeneralMovingSmoothDriftNormBudget.endpoint,
      endpoint,
      Function.comp_def] using hcomp
  have hw := measurable_weight (deltaWeight := deltaWeight) (p := p)
    hE hst ht1 hN hk
  have hp0 : (0 : Real) < (p : Real) := by
    have hp' : (1 : Real) ≤ (p : Real) := by exact_mod_cast hp
    linarith
  have hwrQ : Measurable (fun ω : Ω d =>
      weight E D s t deltaWeight p N k ω ^ ((1 : Real) / (p : Real))) :=
    (Real.continuous_rpow_const (by positivity :
      (0 : Real) ≤ (1 : Real) / (p : Real))).measurable.comp hw
  exact (hwrQ.mul hq).aestronglyMeasurable

/-- Re-export the accepted T995 same-resident positive-cell witness, so the
actual-weight context used alongside these measurability inputs remains
explicitly nondegenerate. -/
noncomputable abbrev t995_nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms hGm
#print axioms hQm
#print axioms t995_nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingWeightedRateMeasurable
