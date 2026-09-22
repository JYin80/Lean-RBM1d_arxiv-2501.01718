/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellPrefixGlobalPoly

/-!
# T454: actual first-cell T361 `hAll` and `jointRate` adapter

The transition indicator only either keeps the nonnegative prefix/QV product
or replaces it by zero.  No event probability or `Good` hypothesis enters.
-/

namespace RBM.APrimeFirstCellJointGlobalPoly

open Filter Set Real CutHypTheta

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow

/-- A pointwise product envelope passes through the transition indicator. -/
theorem jointRate_le_of_product_le {E D δ Eall : ℝ} {s mesh : ℕ → ℝ}
    {N k m : ℕ} {σ : Fin 2 → Bool} {a : LoopArg (d.L N) 2} {v r : ℝ}
    {ω : Gauss.Ω d} (hEall : 0 ≤ Eall)
    (hprod : APrimeCrossJointSplit.prefixGradient d E D δ s mesh N k m ω *
      √(APrimeDriftTimeFamily.qvAt d E D N σ a (s N) v r ω) ≤ Eall) :
    APrimeCrossJointSplit.jointRate d E D δ s mesh N k m σ a v r ω ≤ Eall := by
  by_cases hω : ω ∈ APrimeCrossJointSplit.transition d E D δ s mesh N k m
  · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_mem hω]
    exact hprod
  · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_notMem hω]
    exact hEall

/-- The literal all-sample `hAll` argument used by T361, with the explicit
choice `Eall = 2^26 N^130`. -/
theorem eventually_t361_hAll {τ' δ : ℝ} (hτ' : 0 < τ') (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ (a : LoopArg (d.L N) 2)
        (r : ℝ), r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) →
      ∀ ω : Gauss.Ω d,
        APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω *
          √(APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω) ≤
          2 ^ (26 : ℕ) * (N : ℝ) ^ (130 : ℕ) := by
  filter_upwards
    [APrimeFirstCellPrefixGlobalPoly.eventually_prefixGradient_mul_sqrt_qvAt_le_poly
      hτ' hδ] with N hN
  intro k hk a r hr ω
  simpa [APrimeFirstCellPrefixGlobalPoly.jointConst] using hN k hk a r hr ω

/-- On the actual first cell, `jointRate` lies between zero and the same
explicit all-sample envelope. -/
theorem eventually_jointRate_bounds {τ' δ : ℝ} (hτ' : 0 < τ') (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ (a : LoopArg (d.L N) 2)
        (r : ℝ), r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) →
      ∀ ω : Gauss.Ω d,
        0 ≤ APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
          Step2.sigPM a
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω ∧
        APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
          Step2.sigPM a
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω ≤
            2 ^ (26 : ℕ) * (N : ℝ) ^ (130 : ℕ) := by
  filter_upwards [eventually_t361_hAll hτ' hδ,
    eventually_ge_atTop 1] with N hAll hN
  intro k hk a r hr ω
  have hNpos : 0 < N := by omega
  have hprod := hAll k hk a r hr ω
  constructor
  · exact APrimeCrossJointSplit.jointRate_nonneg d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
      Step2.sigPM a
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r hNpos ω
  · exact jointRate_le_of_product_le (by positivity) hprod

/-- The zero prefix gives an exactly zero `jointRate`, independently of the
transition predicate. -/
theorem jointRate_zero_k0 (τ' δ : ℝ) (N : ℕ) (a : LoopArg (d.L N) 2)
    (ω : Gauss.Ω d) :
    APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
      Step2.sigPM a
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0) 0 ω = 0 := by
  have hp := APrimeFirstCellPrefixGlobalPoly.prefixGradient_zero δ N
    (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
      (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
    (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω
  by_cases hω : ω ∈ APrimeCrossJointSplit.transition d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
  · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_mem hω, hp, zero_mul]
  · rw [APrimeCrossJointSplit.jointRate, Set.indicator_of_notMem hω]

/-- The endpoint cases `r=0` and `r=v` are included explicitly in the moving
first-cell joint-rate envelope. -/
theorem eventually_jointRate_endpoint_bounds {τ' δ : ℝ} (hτ' : 0 < τ')
    (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ (a : LoopArg (d.L N) 2) (ω : Gauss.Ω d),
        (0 ≤ APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
            Step2.sigPM a
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) 0 ω ∧
          APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
            Step2.sigPM a
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) 0 ω ≤
              2 ^ (26 : ℕ) * (N : ℝ) ^ (130 : ℕ)) ∧
        (0 ≤ APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
            Step2.sigPM a
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) ω ∧
          APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
            Step2.sigPM a
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) ω ≤
              2 ^ (26 : ℕ) * (N : ℝ) ^ (130 : ℕ)) := by
  filter_upwards [eventually_jointRate_bounds hτ' hδ] with N hN
  intro k hk a ω
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  exact ⟨hN k hk a 0 ⟨le_rfl, hv.1⟩ ω,
    hN k hk a _ ⟨hv.1, le_rfl⟩ ω⟩

/-- The positive `k=2` geometry is nonvacuous, while the bound remains
pointwise over every sample; no inhabitance of the transition region is
asserted. -/
theorem eventually_positive_two_jointRate_bounds {τ' δ : ℝ} (hτ' : 0 < τ')
    (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop,
      0 < cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1 ∧
      2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N ∧
      ∀ (a : LoopArg (d.L N) 2)
        (r : ℝ), r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2) →
      ∀ ω : Gauss.Ω d,
        0 ≤ APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 2
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
          Step2.sigPM a
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2) r ω ∧
        APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 2
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
          Step2.sigPM a
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2) r ω ≤
            2 ^ (26 : ℕ) * (N : ℝ) ^ (130 : ℕ) := by
  filter_upwards
    [APrimeFirstCellPrefixGlobalPoly.eventually_positive_two_prefix_le_poly hτ' hδ,
      eventually_jointRate_bounds hτ' hδ] with N hgeo hbound
  exact ⟨hgeo.1, hgeo.2.1, hbound 2 hgeo.2.1⟩

#print axioms jointRate_le_of_product_le
#print axioms eventually_t361_hAll
#print axioms eventually_jointRate_bounds
#print axioms jointRate_zero_k0
#print axioms eventually_jointRate_endpoint_bounds
#print axioms eventually_positive_two_jointRate_bounds

end RBM.APrimeFirstCellJointGlobalPoly
