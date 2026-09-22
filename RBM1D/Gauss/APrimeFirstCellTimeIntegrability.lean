/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeTimeIntegrability
import RBM1D.Gauss.APrimeQVRateTime
import RBM1D.Gauss.APrimeNormalizedTestFun
import RBM1D.Gauss.APrimeSupportRunning
import RBM1D.Gauss.APrimeSmoothWeightActual

/-!
# Actual first-cell time-integrability package

This module packages the three time-integrability premises of
`MomentDuhamel.weightedMinkowski_of_deriv_le` for the actual normalized
Gaussian coordinate at a literal moving first-cell net endpoint and the
canonical smooth prefix weight.
-/

namespace RBM.APrimeFirstCellTimeIntegrability

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The literal moving right endpoint of the first-cell prefix. -/
noncomputable def endpoint (N k : ℕ) : ℝ :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

/-- The canonical actual smooth prefix weight used at moment order `p`. -/
noncomputable def weight (τ' δ : ℝ) (N₀ p N k : ℕ) : Ω d → ℝ :=
  APrimeSmoothWeightActual.weight d 0 60 δ (fun _ => 0) (firstCellT τ')
    APrimeSmoothTransition.transitionMesh N₀ p N k
    (APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)

/-- The derivative of the canonical actual smooth prefix weight. -/
noncomputable def weightD (τ' δ : ℝ) (N₀ p N k : ℕ) :
    (d.Idx N × d.Idx N × Bool) → Ω d → ℝ :=
  APrimeSmoothWeightActual.weightD d 0 60 δ (fun _ => 0) (firstCellT τ')
    APrimeSmoothTransition.transitionMesh N₀ p N k
    (APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)

/-- The actual normalized evolved coordinate on the moving first-cell window. -/
noncomputable def Y (N k : ℕ) (a : LoopArg (d.L N) 2)
    (r : ℝ) (ω : Ω d) : ℝ :=
  APrimeDuhamelModel.flowY d N
    (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 (endpoint N k)) r ω

/-- The weighted norm of the actual normalized transported drift. -/
noncomputable def Adr (τ' δ : ℝ) (N₀ p N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  MomentDuhamel.momNormW (Gauss.P d) (weight τ' δ N₀ p N k) p
    (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r)

/-- The deterministic near-field cross rate, including its integrable
`r⁻¹/²` first-cell singularity. -/
noncomputable def Bcr (κ : ℝ) (N k : ℕ) (r : ℝ) : ℝ :=
  APrimeDriftTimeFamily.crossAt 0 0 (endpoint N k) κ r

/-- The weighted rate norm of the actual uncut evolved QV. -/
noncomputable def g (τ' δ : ℝ) (N₀ p N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeModel.rateNormW (Gauss.P d) (weight τ' δ N₀ p N k) p
    (APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r)

/-- At a literal moving first-cell endpoint, the actual smooth weight and
actual coordinate supply all three time-integrability premises required by
weighted Minkowski. -/
theorem actual_weightedMinkowski_integrability {τ' δ κ : ℝ}
    (hτ' : 0 < τ') {N₀ p N k : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable
        (fun r => Adr τ' δ N₀ p N k a r + Bcr κ N k r)
        volume 0 (endpoint N k) ∧
      IntervalIntegrable (g τ' δ N₀ p N k a) volume 0 (endpoint N k) ∧
      ∀ u ∈ Icc (0 : ℝ) (endpoint N k),
        IntervalIntegrable
          (fun r => MomentDuhamel.momNormW (Gauss.P d)
              (weight τ' δ N₀ p N k) p (Y N k a r) *
            (Adr τ' δ N₀ p N k a r + Bcr κ N k r))
          volume 0 u := by
  let v := endpoint N k
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT τ')
    APrimeSmoothTransition.transitionMesh N
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : v ∈ Icc (0 : ℝ) (firstCellT τ' N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hu : ∀ j < k,
      cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hwC1 : Gauss.WeightC1 d N (weight τ' δ N₀ p N k)
      (weightD τ' δ N₀ p N k) := by
    unfold weight weightD
    exact APrimeSmoothWeightActual.weightC1 d (E := 0) (D := 60)
      (δ := δ) (s := fun _ => 0) (t := firstCellT τ')
      (mesh := APrimeSmoothTransition.transitionMesh) (N₀ := N₀)
      (p := p) (N := N) (k := k) (m := m)
      (by norm_num) (by norm_num) hN
      (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
        (firstCellT τ') APrimeSmoothTransition.transitionMesh N) hu
  have hw0 : ∀ ω, 0 ≤ weight τ' δ N₀ p N k ω := by
    intro ω
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N₀ p N k m ω
  have hw1 : ∀ ω, weight τ' δ N₀ p N k ω ≤ 1 := by
    intro ω
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N₀ p N k m ω
  have hAB : IntervalIntegrable
      (fun r => Adr τ' δ N₀ p N k a r + Bcr κ N k r) volume 0 v := by
    unfold Adr Bcr
    exact APrimeDriftTimeFamily.intervalIntegrable_drift_add_cross d 0 60 κ N
      Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
      (weight τ' δ N₀ p N k) hwC1.cont.measurable hw0 hw1 p
  have hg : IntervalIntegrable (g τ' δ N₀ p N k a) volume 0 v := by
    unfold g
    exact APrimeQVRateTime.intervalIntegrable_rateNormW_qvAt d 0 60 N p
      Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1 hp
      (weight τ' δ N₀ p N k) hwC1.cont.measurable hw0 hw1
  refine ⟨hAB, hg, ?_⟩
  intro u huI
  unfold Y
  exact APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
    hv.1 (Set.Subset.rfl) hp
    (APrimeNormalizedTestFun.normalizedTestFunBridge d 0 60 N p Step2.sigPM a
      (by norm_num) (by norm_num) hv.1 hv1)
    hwC1
    (APrimeDriftTimeFamily.momentAt_isModulusPow d 0 60 N p Step2.sigPM a 0 v)
    hAB huI

/-- A nondegenerate actual first-cell instance: the endpoint is positive,
the window has positive length, and the same three integrability statements
hold for the canonical smooth weight. -/
theorem positive_actual_witness {τ' δ : ℝ} (hτ' : 0 < τ') (N : ℕ)
    (hN : 1 ≤ N)
    (hk : 1 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) :
    0 < endpoint N 1 ∧
      IntervalIntegrable
        (fun r => Adr τ' δ 1 1 N 1 a r + Bcr 1 N 1 r)
        volume 0 (endpoint N 1) ∧
      IntervalIntegrable (g τ' δ 1 1 N 1 a) volume 0 (endpoint N 1) ∧
      ∀ u ∈ Icc (0 : ℝ) (endpoint N 1),
        IntervalIntegrable
          (fun r => MomentDuhamel.momNormW (Gauss.P d)
              (weight τ' δ 1 1 N 1) 1 (Y N 1 a r) *
            (Adr τ' δ 1 1 N 1 a r + Bcr 1 N 1 r))
          volume 0 u := by
  have hvpos : 0 < endpoint N 1 := by
    simp only [endpoint, cutNetPt, zero_add]
    exact div_pos (by norm_num) (APrimeSupportRunning.mesh_pos N)
  have hpack := actual_weightedMinkowski_integrability (δ := δ) (κ := 1) hτ'
    (N₀ := 1) (p := 1) (N := N) (k := 1) (by omega) (by norm_num) hk a
  exact ⟨hvpos, hpack.1, hpack.2.1, hpack.2.2⟩

/-- The structural hypotheses of `positive_actual_witness` hold for the
actual growing Gaussian first-cell family.  The choice is `k=p=N₀=κ=1`, and
the endpoint has strictly positive length. -/
theorem eventually_positive_actual_witness {τ' δ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ4 : δ < 1 / 4) :
    ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
      0 < endpoint N 1 ∧
        IntervalIntegrable
          (fun r => Adr τ' δ 1 1 N 1 a r + Bcr 1 N 1 r)
          volume 0 (endpoint N 1) ∧
        IntervalIntegrable (g τ' δ 1 1 N 1 a) volume 0 (endpoint N 1) ∧
        ∀ u ∈ Icc (0 : ℝ) (endpoint N 1),
          IntervalIntegrable
            (fun r => MomentDuhamel.momNormW (Gauss.P d)
                (weight τ' δ 1 1 N 1) 1 (Y N 1 a r) *
              (Adr τ' δ 1 1 N 1 a r + Bcr 1 N 1 r))
            volume 0 u := by
  filter_upwards [APrimeSmoothTransition.eventually_exampleGrow_transition
    hτ' hδ hδ4, eventually_ge_atTop 1] with N htransition hN
  intro a
  exact positive_actual_witness hτ' N hN (by omega) a

#print axioms actual_weightedMinkowski_integrability
#print axioms positive_actual_witness
#print axioms eventually_positive_actual_witness

end

end RBM.APrimeFirstCellTimeIntegrability
