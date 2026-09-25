/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossYRegularity
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeNormalizedTestFun

/-!
# T1067: exact actual-weighted coordinate integrability for the moving hYi slot

The consumer integrand is exactly the `2p`-th power of T1043's cutoff-times-
coordinate observable: on the active branch, `weight = cutoff^(2p)`, and
`flowY` of the normalized moving test function is the norm of that same
coordinate at `Hflow`. The finite-size full-space bound from T1043 therefore
proves the consumer's literal `hYi` integrability, without replacing its
integrand by a weaker cutoff-weighted expression.
-/

namespace RBM.APrimeGeneralMovingWeightedCoordinateIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- For a fixed `p ≥ 1`, the literal T615 actual weight times the moment of
the normalized moving coordinate is integrable on the full Gaussian space,
eventually uniformly over active target cells (including `k = 0`), charges,
outputs, and the entire closed running cell. The accompanying bridge is the
exact `TestFunT₁` proposition used when this coordinate enters
`APrimeDuhamelModel.momFlowDeriv_le`. -/
theorem eventually_actual_weighted_flowY_integrable
    {E D deltaWeight : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall σ : Fin 2 -> Bool, forall a : LoopArg (d.L N) 2,
      ∀ r ∈ Set.Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          APrimeDriftTimeFamily.NormalizedTestFunBridge d E D N p σ a
            (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ∧
          Integrable
            (fun ω =>
              APrimeGeneralMovingSmoothDriftNormBudget.weight
                  E D s t deltaWeight p N k ω *
                |APrimeDuhamelModel.flowY d N
                  (APrimeDriftTimeFamily.coordAt d E D N σ a (s N)
                    (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k))
                  r ω| ^ (2 * p))
            (P d) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  intro k hk σ a r hr
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let v := cutNetPt s mesh N k
  let m := APrimeSmoothWeightActual.canonicalM d s t mesh N
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hsv : s N ≤ v := hr.1.trans hr.2
  have hbridge :
      APrimeDriftTimeFamily.NormalizedTestFunBridge d E D N p σ a (s N) v :=
    APrimeNormalizedTestFun.normalizedTestFunBridge d E D N p σ a hE
      (hs0 N) hsv hv1
  have hweight :
      APrimeGeneralMovingSmoothDriftNormBudget.weight
          E D s t deltaWeight p N k =
        fun ω =>
          (APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω) ^
            (2 * p) := by
    funext ω
    simp [APrimeGeneralMovingSmoothDriftNormBudget.weight,
      APrimeSmoothWeightActual.weight, mesh, m, hk, hN]
  have hcut0 : ∀ ω,
      0 ≤ APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω := by
    intro ω
    exact Cutoff.cutChi_nonneg _
  have hregular :=
    APrimeGeneralMovingCrossYRegularity.actualY_hYm_hYi d
      (E := E) (D := D) (deltaWeight := deltaWeight) (s := s) (t := t)
      hE hs0 hst ht1 (p := p) (N := N) (k := k) hp hNpos hk σ a
      (r := r) (by simpa [v, mesh] using hr)
  have hintegrand : ∀ ω : Gauss.Ω d,
      APrimeGeneralMovingSmoothDriftNormBudget.weight
          E D s t deltaWeight p N k ω *
        |APrimeDuhamelModel.flowY d N
          (APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v) r ω| ^
            (2 * p) =
      |APrimeGeneralMovingCrossYRegularity.actualY
          d E D deltaWeight s t N k σ a r ω| ^ (2 * p) := by
    intro ω
    rw [hweight, APrimeDuhamelModel.flowY]
    unfold APrimeGeneralMovingCrossYRegularity.actualY
    rw [abs_of_nonneg (mul_nonneg (hcut0 ω) (norm_nonneg _)), mul_pow]
    rw [abs_of_nonneg (norm_nonneg _)]
  refine ⟨hbridge, ?_⟩
  exact hregular.2.congr
    (Filter.Eventually.of_forall fun ω => (hintegrand ω).symm)

/-- T995's accepted nondegenerate same-resident witness remains available
alongside this full-space integrability result. -/
noncomputable abbrev t995_nondegenerate_positive_weight_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_weighted_flowY_integrable
#print axioms t995_nondegenerate_positive_weight_witness

end
end RBM.APrimeGeneralMovingWeightedCoordinateIntegrable
