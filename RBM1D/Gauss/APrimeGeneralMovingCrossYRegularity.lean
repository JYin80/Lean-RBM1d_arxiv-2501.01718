/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1043: general-moving sample regularity for the actual cross observable

The cutoff times the norm of the same evolved coordinate used by the active
cross consumer.  At each positive finite size this field is continuous and
bounded on the Gaussian sample space, uniformly over the closed time cell.
The bounds may depend on the finite-size parameters; no event restriction or
moment estimate uniform in `N` is asserted.
-/

namespace RBM.APrimeGeneralMovingCrossYRegularity

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The exact unweighted sample observable in the `hYm` and `hYi` slots of
`APrimeCrossJointSplit.crossPart_active_le_jointEvent`. -/
noncomputable def actualY (d : Gauss.Dims) (E D deltaWeight : ℝ)
    (s t : ℕ → ℝ) (N k : ℕ) (σ : Fin 2 → Bool)
    (a : LoopArg (d.L N) 2) (r : ℝ) : Gauss.Ω d → ℝ :=
  fun ω =>
    APrimeSmoothWeightActual.cutoff d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) ω *
    ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r
      (Gauss.Hflow d N r ω)‖

private theorem contDiff_coordAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v r : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hv1 : v < 1)
    (hr : r ∈ Set.Icc s v) :
    ContDiff ℝ 1 (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) := by
  obtain ⟨cK, _, hK, _⟩ := Gauss.exists_bdd_Kval_Kprim
    (d := d) E N hE.le hs0 hv1 σ
  have hη := Gauss.window_eta_pos hE hv1
  have hz := Gauss.window_im_ne_zero hE hv1 r hr
  have hzη := Gauss.window_le_abs_im hE hv1 r hr
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn σ) (m := 2) hη hz hzη (List.length_ofFn)
    (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a
    (hK r hr)
  unfold APrimeDriftTimeFamily.coordAt
  exact (hraw.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).div_const _

/-- At every positive finite size, the literal `Y` has the exact full-space
`hYm` and `hYi` regularity required by the active cross consumer.  The raw
Gaussian observable is bounded by compactness on `[s_N, v_k]`, with the same
sample and time throughout. -/
theorem actualY_hYm_hYi (d : Gauss.Dims)
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {p N k : ℕ} (_hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {r : ℝ}
    (hr : r ∈ Set.Icc (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) :
    AEStronglyMeasurable
      (actualY d E D deltaWeight s t N k σ a r) (Gauss.P d) ∧
    Integrable
      (fun ω => |actualY d E D deltaWeight s t N k σ a r ω| ^ (2 * p))
      (Gauss.P d) := by
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let v := cutNetPt s mesh N k
  let m := APrimeSmoothWeightActual.canonicalM d s t mesh N
  let Y := actualY d E D deltaWeight s t N k σ a r
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hsv : s N ≤ v := hr.1.trans hr.2
  have hm : 1 ≤ m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hu : ∀ j < k, cutNetPt s mesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop s t mesh N := by
      calc
        j ≤ k := hj.le
        _ ≤ cutNetTop s t mesh N := hk
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht1 N)
  have hcut : Continuous
      (APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m) :=
    APrimeSmoothWeightActual.continuous_cutoff d
      (E := E) (D := D) (δ := deltaWeight) (s := s) (mesh := mesh)
      (N := N) (k := k) (m := m) hE hs1 hN hm hu
  have hcoord : ContDiff ℝ 1
      (APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r) :=
    contDiff_coordAt d E D N σ a hE (hs0 N) hv1 hr
  have hcoordC : Continuous fun ω : Gauss.Ω d =>
      APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
        (Gauss.Hflow d N r ω) :=
    hcoord.continuous.comp (Gauss.continuous_Hflow d N r)
  have hYc : Continuous Y := by
    change Continuous (fun ω =>
      APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖)
    exact hcut.mul hcoordC.norm
  have hYmeas : Measurable Y := hYc.measurable
  have hYm : AEStronglyMeasurable Y (Gauss.P d) :=
    hYmeas.aestronglyMeasurable
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d E D N a (s N) v :=
    APrimeDriftTimeFamily.driftScale_pos d hE hsv hv1 N a
  obtain ⟨cK, hcK, hK, _hKprim⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) E N hE.le (hs0 N) hv1 σ
  have hKwindow : ∀ u ∈ Icc (s N) v, ∀ b : LoopArg (d.L N) 2,
      ‖(Gauss.band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK :=
    fun u hu b => hK u hu b
  obtain ⟨cRaw, hcRaw, hRaw⟩ :=
    Gauss.exists_bdd₀_ukerObsT (d := d) (N := N) E
      (σ := List.ofFn σ) (m := 2) List.length_ofFn
      (by norm_num : 1 ≤ 2)
      (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a
      (u₀ := s N) (u₁ := v)
      (Gauss.window_eta_pos hE hv1) hcK
      (Gauss.window_le_abs_im hE hv1) hKwindow
  have hcoordBound : ∀ ω : Gauss.Ω d,
      ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
        (Gauss.Hflow d N r ω)‖ ≤
        cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v := by
    intro ω
    rw [APrimeDriftTimeFamily.coordAt, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hscale]
    exact div_le_div_of_nonneg_right
      (hRaw r hr (Gauss.Hflow d N r ω)) hscale.le
  have hYnonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    change 0 ≤ APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω * _
    exact mul_nonneg (Cutoff.cutChi_nonneg _) (norm_nonneg _)
  have hYbound : ∀ ω, |Y ω| ≤
      cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v := by
    intro ω
    rw [abs_of_nonneg (hYnonneg ω)]
    change APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖ ≤ _
    calc
      _ ≤ 1 * ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖ :=
        mul_le_mul_of_nonneg_right (Cutoff.cutChi_le_one _)
          (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ _ := hcoordBound ω
  have hCY : 0 ≤
      cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v :=
    div_nonneg hcRaw hscale.le
  have hYpowMeas : Measurable (fun ω => |Y ω| ^ (2 * p)) :=
    (continuous_abs.measurable.comp hYmeas).pow_const (2 * p)
  have hYi : Integrable (fun ω => |Y ω| ^ (2 * p)) (Gauss.P d) := by
    apply Integrable.of_bound
      hYpowMeas.aestronglyMeasurable
      ((cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v) ^ (2 * p))
    filter_upwards with ω
    change ‖|Y ω| ^ (2 * p)‖ ≤ _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYbound ω) (2 * p)
  exact ⟨hYm, hYi⟩

/-- For each fixed `p ≥ 1`, regularity holds eventually for every active
target-net prefix, including `k = 0`, every charge and output, and every time
in the closed cell `[s_N, v_k]`.  The full interval quantifier includes both
closed-cell endpoints. -/
theorem eventually_actualY_hYm_hYi (d : Gauss.Dims)
    {E D deltaWeight : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Set.Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        AEStronglyMeasurable
          (actualY d E D deltaWeight s t N k σ a r) (Gauss.P d) ∧
        Integrable
          (fun ω =>
            |actualY d E D deltaWeight s t N k σ a r ω| ^ (2 * p))
          (Gauss.P d) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := by omega
  intro k hk σ a r hr
  exact actualY_hYm_hYi d hE hs0 hst ht1 hp hNpos hk σ a hr

/-- The accepted T995 nondegenerate witness is available alongside this
regularity result: on a genuine moving window it supplies an eventual active
positive cell and a sample with strictly positive actual smooth weight. -/
noncomputable abbrev t995_nondegenerate_positive_weight_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms actualY
#print axioms actualY_hYm_hYi
#print axioms eventually_actualY_hYm_hYi
#print axioms t995_nondegenerate_positive_weight_witness

end
end RBM.APrimeGeneralMovingCrossYRegularity
