/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1069: exact actual-weighted drift integrability for the moving `hGi` slot

This module proves the literal full-Gaussian-space integrability hypothesis
consumed as `hGi` by `APrimeDuhamelModel.momFlowDeriv_le`, with T615's actual
smooth weight and exact normalized drift.  The bound is uniform over all
active target cells (including `k = 0`), outputs, and times in the closed
running cell, after fixing `p ≥ 1`.
-/

namespace RBM.APrimeGeneralMovingWeightedDriftIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

private noncomputable def endpoint (s t : Nat → Real) (D : Real)
    (N k : Nat) : Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t D N k

private noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight
    E D s t deltaWeight p N k

private noncomputable def drift (E D : Real) (s t : Nat → Real)
    (N k : Nat) (a : LoopArg (d.L N) 2) (u : Real) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.drift E D s t N k a u

private theorem integrable_weighted_drift_pow
    {E D : Real} {s t : Nat → Real} {deltaWeight : Real}
    {p N k : Nat} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hsv : s N ≤ endpoint s t D N k)
    (hv1 : endpoint s t D N k < 1)
    (a : LoopArg (d.L N) 2) {u : Real}
    (hu : u ∈ Icc (s N) (endpoint s t D N k))
    (henv : ∀ ω : Ω d, |drift E D s t N k a u ω| ≤ (N : Real) ^ (D + 8))
    (hw : Measurable (weight E D s t deltaWeight p N k)) :
    Integrable (fun ω => weight E D s t deltaWeight p N k ω *
      |drift E D s t N k a u ω| ^ (2 * p)) (P d) := by
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d E D N a
      (s N) (endpoint s t D N k) :=
    APrimeDriftTimeFamily.driftScale_pos d hE hsv hv1 N a
  have hdrift : Measurable (drift E D s t N k a u) := by
    have hf := (Gauss.continuous_uker_driftF_omega d E N
      (Gauss.window_im_ne_zero hE hv1 u hu)
      (Gauss.window_norm_mul_lt hE.le hs0 hv1 u hu)
      Step2.sigPM a (((endpoint s t D N k : Real) : Complex))).norm.div_const
        (APrimeDriftTimeFamily.driftScale d E D N a
          (s N) (endpoint s t D N k))
    unfold drift APrimeGeneralMovingSmoothDriftNormBudget.drift
      APrimeDriftTimeFamily.driftAt
    exact hf.measurable
  have hmeas : Measurable (fun ω =>
      weight E D s t deltaWeight p N k ω *
        |drift E D s t N k a u ω| ^ (2 * p)) :=
    hw.mul ((continuous_abs.measurable.comp hdrift).pow_const (2 * p))
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (((N : Real) ^ (D + 8)) ^ (2 * p))
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    change |weight E D s t deltaWeight p N k ω *
      |drift E D s t N k a u ω| ^ (2 * p)| ≤ _
    have hprod : 0 ≤ weight E D s t deltaWeight p N k ω *
        |drift E D s t N k a u ω| ^ (2 * p) := mul_nonneg
      (APrimeGeneralMovingSmoothDriftNormBudget.weight_nonneg
        E D s t deltaWeight p N k ω)
      (pow_nonneg (abs_nonneg _) _)
    calc
      |weight E D s t deltaWeight p N k ω *
          |drift E D s t N k a u ω| ^ (2 * p)| =
          weight E D s t deltaWeight p N k ω *
            |drift E D s t N k a u ω| ^ (2 * p) := abs_of_nonneg hprod
      _ ≤ 1 * |drift E D s t N k a u ω| ^ (2 * p) :=
        mul_le_mul_of_nonneg_right
          (APrimeGeneralMovingSmoothDriftNormBudget.weight_le_one
            E D s t deltaWeight p N k ω)
          (pow_nonneg (abs_nonneg _) _)
      _ ≤ ((N : Real) ^ (D + 8)) ^ (2 * p) := by
        simpa only [one_mul] using
          pow_le_pow_left₀ (abs_nonneg _) (henv ω) (2 * p)

/-- For fixed `p ≥ 1`, the exact T615 actual-smooth weight times the exact
normalized drift moment is integrable on the full Gaussian space, eventually
uniformly over every active target-mesh cell (including `k = 0`), output, and
time in the closed cell.  This is precisely the `hGi` integrand in
`APrimeDuhamelModel.momFlowDeriv_le` under the general-moving specialization. -/
theorem eventually_actual_weighted_drift_integrable
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (s N)
        (endpoint s t D N k),
        Integrable
          (fun ω => weight E D s t deltaWeight p N k ω *
            |drift E D s t N k a r ω| ^ (2 * p)) (P d) := by
  have henv :=
    APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
      hE hD hs0 hst ht1 hc hreg
  filter_upwards [henv, eventually_ge_atTop 2] with N henvN hN2
  intro k hk a r hr
  have hv : endpoint s t D N k ∈ Icc (s N) (t N) := by
    simpa [endpoint, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)
  have hw : Measurable (weight E D s t deltaWeight p N k) := by
    apply APrimeGeneralMovingSmoothDriftNormBudget.measurable_weight
    · exact hE
    · exact hst
    · exact ht1
    · omega
    · simpa [endpoint, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hk
  have hbound : ∀ ω : Ω d,
      |drift E D s t N k a r ω| ≤ (N : Real) ^ (D + 8) := by
    intro ω
    have h := henvN k (by simpa [endpoint] using hk) r
      (by simpa [endpoint, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using hr) a ω
    simpa [drift, APrimeGeneralMovingSmoothDriftNormBudget.drift,
      endpoint, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using h
  have hsv : s N ≤ endpoint s t D N k := hv.1
  exact integrable_weighted_drift_pow hE (hs0 N) hsv
    (hv.2.trans_lt (ht1 N)) a hr hbound hw

/-- T995 supplies a nondegenerate same-resident positive-weight context for
this full-space integrability result. -/
noncomputable abbrev t995_nondegenerate_positive_weight_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_weighted_drift_integrable
#print axioms t995_nondegenerate_positive_weight_witness

end
end RBM.APrimeGeneralMovingWeightedDriftIntegrable
