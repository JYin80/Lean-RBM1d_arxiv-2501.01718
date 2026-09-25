/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeQVRateTime
import RBM1D.Gauss.APrimeGeneralMovingMesh

/-!
# T618: general-moving measurability of the literal joint rate

This module proves the finite-size continuity and measurability layer needed
for the smooth-prefix covariance term behind (5.42).  It uses the literal
target mesh, canonical smoothing order, strict transition set, and evolved
quadratic variation.  No favorable event or first-cell regularity package is
imported.
-/

namespace RBM.APrimeGeneralMovingJointMeasurable

open MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- Every active target-mesh endpoint lies in the original moving window. -/
theorem target_endpoint_mem_window {D : ℝ} {s t : ℕ → ℝ}
    (hst : ∀ N, s N ≤ t N) {N k : ℕ}
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈ Icc (s N) (t N) := by
  exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
    (APrimeGeneralMovingMesh.targetMesh_pos D N) _
    (cutNetPt_mem_netFinset hk)

/-- Every active target-mesh endpoint stays strictly below the singular time
`1` under the moving-window endpoint hypothesis. -/
theorem target_endpoint_lt_one {D : ℝ} {s t : ℕ → ℝ}
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {N k : ℕ}
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k < 1 := by
  exact (target_endpoint_mem_window hst hk).2.trans_lt (ht1 N)

/-- Every time stored in an active prefix is strictly below `1`. -/
theorem stored_time_lt_one {D : ℝ} {s t : ℕ → ℝ}
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {N k j : ℕ}
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (hj : j < k) :
    cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j < 1 := by
  exact target_endpoint_lt_one hst ht1 (show
    j ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N by omega)

/-- The literal canonical smoothing order is positive at every size. -/
theorem canonicalM_pos {D : ℝ} {s t : ℕ → ℝ} (N : ℕ) :
    1 ≤ APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N := by
  exact APrimeSmoothWeightActual.canonicalM_pos d s t
    (APrimeGeneralMovingMesh.targetMesh D) N

private theorem continuous_quadVar_of_contDiff {N : ℕ}
    {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    Continuous (Gauss.quadVar d N F) := by
  unfold Gauss.quadVar
  apply continuous_finsetSum
  intro q _
  have hcoord : Continuous (fun M => Gauss.coordD1 d N F M q) := by
    change Continuous (fun M => fderiv ℝ F M
      (Gauss.Bmat d N q.1 q.2.1 q.2.2))
    exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact continuous_const.mul (hcoord.norm.pow 2)

/-- The literal canonical prefix gradient is continuous on Gaussian sample
space for every active target-mesh prefix, including the empty prefix. -/
theorem continuous_prefixGradient {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    Continuous (APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)) := by
  let g := APrimeSmoothWeightActual.prefixMatrix d E D s
    (APrimeGeneralMovingMesh.targetMesh D) N k
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
  let F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun M => (g M : ℂ)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu : ∀ j < k,
      cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j < 1 := by
    intro j hj
    exact stored_time_lt_one hst ht1 hk hj
  have hg : ContDiff ℝ 1 g :=
    APrimeSmoothWeightActual.contDiff_prefixMatrix d
      (E := E) (D := D) (s := s)
      (mesh := APrimeGeneralMovingMesh.targetMesh D)
      (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      hE hs1 hN (canonicalM_pos N) hu
  have hF : ContDiff ℝ 1 F := Complex.ofRealCLM.contDiff.comp hg
  have hqv := continuous_quadVar_of_contDiff hF
  change Continuous (fun omega =>
    √(Gauss.quadVar d N F (Gauss.Xmat d N omega)) /
      APrimeSmoothWeightActual.threshold deltaWeight N)
  exact ((hqv.comp (Gauss.continuous_Xmat d N)).sqrt).div_const _

/-- The literal strict transition predicate is a measurable set for every
active target-mesh prefix. -/
theorem measurableSet_transition {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    MeasurableSet (APrimeCrossJointSplit.transition d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)) := by
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu : ∀ j < k,
      cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j < 1 := by
    intro j hj
    exact stored_time_lt_one hst ht1 hk hj
  have hp : Continuous (APrimeSmoothWeightActual.prefixSample d E D s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)) := by
    exact (APrimeSmoothWeightActual.contDiff_prefixMatrix d
      (E := E) (D := D) (s := s)
      (mesh := APrimeGeneralMovingMesh.targetMesh D)
      (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      hE hs1 hN (canonicalM_pos N) hu).continuous.comp
        (Gauss.continuous_Xmat d N)
  have hratio := hp.measurable.div_const
    (APrimeSmoothWeightActual.threshold deltaWeight N)
  change MeasurableSet ({omega | (1 : ℝ) <
      APrimeSmoothWeightActual.prefixSample d E D s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) omega /
          APrimeSmoothWeightActual.threshold deltaWeight N} ∩
    {omega | APrimeSmoothWeightActual.prefixSample d E D s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) omega /
          APrimeSmoothWeightActual.threshold deltaWeight N < (2 : ℝ)})
  exact (measurableSet_lt measurable_const hratio).inter
    (measurableSet_lt hratio measurable_const)

/-- At every fixed running time in the closed target cell, the literal
uncut evolved quadratic variation is measurable in the Gaussian sample. -/
theorem measurable_qvAt {E D : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {N k : ℕ}
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (sigma : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {r : ℝ}
    (hr : r ∈ Icc (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) :
    Measurable (fun omega => APrimeDriftTimeFamily.qvAt d E D N sigma a
      (s N) (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
      r omega) := by
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) := target_endpoint_mem_window hst hk
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  let rr : Icc (s N) v := ⟨r, hr⟩
  have hembed : Measurable (fun omega : Ω d => (rr, omega)) :=
    measurable_const.prodMk measurable_id
  have h := APrimeQVRateTime.measurable_qvAt_on_window d E D N sigma a
    hE (hs0 N) hv.1 hv1
  have hcomp := h.comp hembed
  have heq : (fun omega : Ω d =>
      APrimeDriftTimeFamily.qvAt d E D N sigma a (s N) v r omega) =
      (fun omega : Ω d =>
        APrimeDriftTimeFamily.qvAt d E D N sigma a (s N) v rr.1 omega) := by
    rfl
  rw [heq]
  simpa only [Function.comp_def] using hcomp

/-- The canonical prefix gradient and literal strict-transition joint rate
are measurable for every charge word, output, active prefix, and closed
running time.  The statement includes `k = 0`. -/
theorem measurable_prefixGradient_and_jointRate
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (sigma : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {r : ℝ}
    (hr : r ∈ Icc (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) :
    Measurable (APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N)) ∧
      Measurable (APrimeCrossJointSplit.jointRate d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N)
        sigma a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r) := by
  have hprefix :=
    (continuous_prefixGradient (deltaWeight := deltaWeight)
      hE hst ht1 hN hk).measurable
  have hq := measurable_qvAt hE hs0 hst ht1 hk sigma a hr
  have htransition := measurableSet_transition (deltaWeight := deltaWeight)
    hE hst ht1 hN hk
  refine ⟨hprefix, ?_⟩
  exact (hprefix.mul hq.sqrt).indicator htransition

/-- Uniform finite-size form of the complete canonical measurability layer. -/
theorem measurable_canonical_layer
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {N : ℕ} (hN : 0 < N) :
    ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      Continuous (APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N)) ∧
      MeasurableSet (APrimeCrossJointSplit.transition d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N)) ∧
      ∀ sigma : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
        ∀ r ∈ Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          Measurable (APrimeCrossJointSplit.jointRate d E D deltaWeight s
            (APrimeGeneralMovingMesh.targetMesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N)
            sigma a (cutNetPt s
              (APrimeGeneralMovingMesh.targetMesh D) N k) r) := by
  intro k hk
  have hcont := continuous_prefixGradient (deltaWeight := deltaWeight)
    hE hst ht1 hN hk
  have htrans := measurableSet_transition (deltaWeight := deltaWeight)
    hE hst ht1 hN hk
  refine ⟨hcont, htrans, ?_⟩
  intro sigma a r hr
  exact (measurable_prefixGradient_and_jointRate
    (deltaWeight := deltaWeight) hE hs0 hst ht1 hN hk sigma a hr).2

/-- At `k = 0` the literal strict transition is empty. -/
theorem transition_k_zero_eq_empty {E D deltaWeight : ℝ}
    {s t : ℕ → ℝ} {N : ℕ} (hN : 0 < N) :
    APrimeCrossJointSplit.transition d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N 0
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) = ∅ := by
  have _hTheta : 0 < APrimeSmoothWeightActual.threshold deltaWeight N :=
    APrimeSmoothWeightActual.threshold_pos hN
  ext omega
  simp only [APrimeCrossJointSplit.transition, mem_ofPred_eq, mem_empty_iff_false,
    iff_false]
  rw [APrimeSmoothWeightActual.prefixSample_zero d E D s
    (APrimeGeneralMovingMesh.targetMesh D) N
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    (canonicalM_pos N) omega]
  simp

/-- Consequently the literal joint rate vanishes on the zero cell for every
charge word, output, endpoint parameter, and running time. -/
theorem jointRate_k_zero {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    {N : ℕ} (hN : 0 < N) (sigma : Fin 2 → Bool)
    (a : LoopArg (d.L N) 2) (v r : ℝ) :
    APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N 0
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) sigma a v r = 0 := by
  funext omega
  rw [APrimeCrossJointSplit.jointRate, transition_k_zero_eq_empty hN]
  simp

/-! ## Nondegenerate geometry witness -/

/-- The hypotheses used by the measurability layer have an explicit
positive-duration realization at the fixed Gaussian model: `E = 0`,
`s = 0`, `t = 1/2`, `N = 1`, and the active empty prefix `k = 0`. -/
theorem sample_hypotheses_witness (D : ℝ) :
    |(0 : ℝ)| < 2 ∧
    (∀ N, 0 ≤ APrimeGeneralMovingMesh.sampleStart N) ∧
    (∀ N, APrimeGeneralMovingMesh.sampleStart N ≤
      APrimeGeneralMovingMesh.sampleEnd N) ∧
    (∀ N, APrimeGeneralMovingMesh.sampleEnd N < 1) ∧
    (∀ N, APrimeGeneralMovingMesh.sampleStart N <
      APrimeGeneralMovingMesh.sampleEnd N) ∧
    0 < APrimeGeneralMovingMesh.targetMesh D 1 ∧
    (0 : ℕ) < 1 ∧
    0 ≤ cutNetTop APrimeGeneralMovingMesh.sampleStart
      APrimeGeneralMovingMesh.sampleEnd
      (APrimeGeneralMovingMesh.targetMesh D) 1 := by
  have hgeom := APrimeGeneralMovingMesh.sample_window_geometry
  exact ⟨by norm_num, fun N => (hgeom N).1,
    fun N => (hgeom N).2.1.le, fun N => (hgeom N).2.2,
    fun N => (hgeom N).2.1,
    APrimeGeneralMovingMesh.targetMesh_pos D 1, by norm_num, Nat.zero_le _⟩

/-!
The positive-duration fixed window `sampleStart = 0`, `sampleEnd = 1/2`
and the literal target mesh are jointly realized by
`APrimeGeneralMovingMesh.sample_target_mesh_fields`.  The theorems above do
not assume or assert that any sample belongs to an intersection of a common
event with the strict transition set.
-/

#print axioms target_endpoint_mem_window
#print axioms target_endpoint_lt_one
#print axioms stored_time_lt_one
#print axioms canonicalM_pos
#print axioms continuous_prefixGradient
#print axioms measurableSet_transition
#print axioms measurable_qvAt
#print axioms measurable_prefixGradient_and_jointRate
#print axioms measurable_canonical_layer
#print axioms transition_k_zero_eq_empty
#print axioms jointRate_k_zero
#print axioms sample_hypotheses_witness

end

end RBM.APrimeGeneralMovingJointMeasurable
