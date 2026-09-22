/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSampleRegularity

/-!
# T459: sample measurability of the actual first-cell joint rate
-/

namespace RBM.APrimeFirstCellJointMeasurable

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (N k : ℕ) : ℝ :=
  APrimeFirstCellSampleRegularity.endpoint N k

noncomputable def canonicalM (τ' : ℝ) (N : ℕ) : ℕ :=
  APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N

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

/-- The literal actual prefix gradient is continuous on Gaussian sample space. -/
theorem continuous_prefixGradient {τ' δ : ℝ} {N k : ℕ}
    (hτ' : 0 < τ') (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    Continuous (APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)) := by
  let g := APrimeSmoothWeightActual.prefixMatrix d 0 60 (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)
  let F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun M => (g M : ℂ)
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hm : 1 ≤ canonicalM τ' N := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hg : ContDiff ℝ 1 g :=
    APrimeSmoothWeightActual.contDiff_prefixMatrix d
      (E := 0) (D := 60) (s := fun _ => 0)
      (mesh := APrimeSmoothTransition.transitionMesh)
      (N := N) (k := k) (m := canonicalM τ' N)
      (by norm_num) (by norm_num) hN hm hu
  have hF : ContDiff ℝ 1 F := Complex.ofRealCLM.contDiff.comp hg
  have hqv := continuous_quadVar_of_contDiff hF
  change Continuous (fun ω =>
    √(Gauss.quadVar d N F (Gauss.Xmat d N ω)) /
      APrimeSmoothWeightActual.threshold δ N)
  exact ((hqv.comp (Gauss.continuous_Xmat d N)).sqrt).div_const _

/-- The strict transition predicate is a measurable set. -/
theorem measurableSet_transition {τ' δ : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    MeasurableSet (APrimeCrossJointSplit.transition d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)) := by
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hm : 1 ≤ canonicalM τ' N := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hp : Continuous (APrimeSmoothWeightActual.prefixSample d 0 60
      (fun _ => 0) APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)) := by
    exact (APrimeSmoothWeightActual.contDiff_prefixMatrix d
      (E := 0) (D := 60) (s := fun _ => 0)
      (mesh := APrimeSmoothTransition.transitionMesh)
      (N := N) (k := k) (m := canonicalM τ' N)
      (by norm_num) (by norm_num) hN hm hu).continuous.comp
        (Gauss.continuous_Xmat d N)
  have hratio := hp.measurable.div_const (APrimeSmoothWeightActual.threshold δ N)
  change MeasurableSet ({ω | (1 : ℝ) <
      APrimeSmoothWeightActual.prefixSample d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N) ω /
          APrimeSmoothWeightActual.threshold δ N} ∩
    {ω | APrimeSmoothWeightActual.prefixSample d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N) ω /
          APrimeSmoothWeightActual.threshold δ N < (2 : ℝ)})
  exact (measurableSet_lt measurable_const hratio).inter
    (measurableSet_lt hratio measurable_const)

private theorem measurable_actual_qvAt {τ' : ℝ} (hτ' : 0 < τ')
    {N k : ℕ} (_hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (endpoint N k)) :
    Measurable (fun ω => APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a
      0 (endpoint N k) r ω) := by
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : endpoint N k ∈ Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  let rr : Icc (0 : ℝ) (endpoint N k) := ⟨r, hr⟩
  have hembed : Measurable (fun ω : Ω d => (rr, ω)) :=
    measurable_const.prodMk measurable_id
  have h := APrimeQVRateTime.measurable_qvAt_on_window d 0 60 N Step2.sigPM a
    (by norm_num) (by norm_num) hv.1 hv1
  have hcomp := h.comp hembed
  have heq : (fun ω : Ω d =>
      APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
        (endpoint N k) r ω) =
      (fun ω : Ω d =>
        APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
          (endpoint N k) rr.1 ω) := by rfl
  rw [heq]
  simpa only [Function.comp_def] using hcomp

/-- Actual canonical prefix gradient and joint rate are measurable at fixed
positive size and every running time in the moving first-cell interval. -/
theorem measurable_actual_prefixGradient_and_jointRate {τ' δ : ℝ}
    (hτ' : 0 < τ') {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (endpoint N k)) :
    Measurable (APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)) ∧
      Measurable (APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)
        Step2.sigPM a (endpoint N k) r) := by
  have hprefix :=
    (continuous_prefixGradient (τ' := τ') (δ := δ) hτ' hN hk).measurable
  have hq := measurable_actual_qvAt hτ' hN hk a hr
  have htransition := measurableSet_transition (δ := δ) hτ' hN hk
  refine ⟨hprefix, ?_⟩
  exact (hprefix.mul hq.sqrt).indicator htransition

/-- At `k = 0` the strict transition is empty. -/
theorem transition_k_zero_eq_empty {τ' δ : ℝ} {N : ℕ} (hN : 0 < N) :
    APrimeCrossJointSplit.transition d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 (canonicalM τ' N) = ∅ := by
  have hm : 1 ≤ canonicalM τ' N := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have _hΘ : 0 < APrimeSmoothWeightActual.threshold δ N :=
    APrimeSmoothWeightActual.threshold_pos hN
  ext ω
  simp only [APrimeCrossJointSplit.transition, mem_setOf_eq, mem_empty_iff_false,
    iff_false]
  rw [APrimeSmoothWeightActual.prefixSample_zero d 0 60 (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N (canonicalM τ' N) hm ω]
  simp

/-- Consequently the literal joint rate vanishes on the zero cell. -/
theorem jointRate_k_zero {τ' δ : ℝ} {N : ℕ} (hN : 0 < N)
    (a : LoopArg (d.L N) 2) (r : ℝ) :
    APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 (canonicalM τ' N)
      Step2.sigPM a 0 r = 0 := by
  funext ω
  rw [APrimeCrossJointSplit.jointRate, transition_k_zero_eq_empty hN]
  simp

/-- Measurability on the zero cell, stated separately from the active range. -/
theorem measurable_actual_k_zero {τ' δ : ℝ} (hτ' : 0 < τ')
    {N : ℕ} (hN : 0 < N) (a : LoopArg (d.L N) 2) :
    Measurable (APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 0 (canonicalM τ' N)) ∧
      Measurable (APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 0 (canonicalM τ' N)
        Step2.sigPM a 0 0) := by
  have hv : endpoint N 0 = 0 := by
    simp only [endpoint, APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero]
  have hr : (0 : ℝ) ∈ Icc 0 (endpoint N 0) := by
    rw [hv]
    exact ⟨le_rfl, le_rfl⟩
  have h := measurable_actual_prefixGradient_and_jointRate
    (δ := δ) hτ' hN (Nat.zero_le _) a hr
  exact ⟨h.1, by simpa only [hv] using h.2⟩

/-- T434's same-event nonzero resident together with the two global
measurability conclusions.  No transition nonemptiness is asserted. -/
def PositiveJointMeasurableResident (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeFirstCellGeneratorHle.actualWeight τ' δ 2 p N 2 N ω = 1) ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    Measurable (APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2 (canonicalM τ' N)) ∧
    ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) (endpoint N 2),
      Measurable (APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2 (canonicalM τ' N)
        Step2.sigPM a (endpoint N 2) r)

theorem positiveJointMeasurableResident_of_generator {τ' δ ν : ℝ}
    (hτ' : 0 < τ')
    (hresident : APrimeFirstCellGeneratorHle.positiveActualWeightResident τ' δ ν) :
    PositiveJointMeasurableResident τ' δ ν := by
  filter_upwards [hresident, eventually_ge_atTop (1 : ℕ)] with N hres hN
  obtain ⟨ω, hω, hk, hw, hu2, hu2T, _⟩ := hres
  have hpref := (continuous_prefixGradient (τ' := τ') (δ := δ)
    hτ' (by omega) hk).measurable
  refine ⟨ω, hω, hk, hw, hu2, hu2T, hpref, ?_⟩
  intro a r hr
  exact (measurable_actual_prefixGradient_and_jointRate hτ' (by omega) hk a hr).2

/-- Closed producer retaining the measurable high-probability event and the
actual-weight `k = 2` resident. -/
theorem exists_sharpCommonEvent_with_jointMeasurable :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        PositiveJointMeasurableResident τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellGeneratorHle.exists_sharpCommonEvent_with_generatorHle
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hresident⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, positiveJointMeasurableResident_of_generator hτ' hresident⟩

#print axioms continuous_prefixGradient
#print axioms measurableSet_transition
#print axioms measurable_actual_prefixGradient_and_jointRate
#print axioms transition_k_zero_eq_empty
#print axioms jointRate_k_zero
#print axioms measurable_actual_k_zero
#print axioms positiveJointMeasurableResident_of_generator
#print axioms exists_sharpCommonEvent_with_jointMeasurable

end

end RBM.APrimeFirstCellJointMeasurable
