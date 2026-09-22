/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVGlobalPoly
import RBM1D.Gauss.APrimeFirstCellSharpCommonEvent

/-!
# T450: all-sample first-cell normalized drift polynomial envelope

The estimates in this file are deterministic and hold for every Gaussian
sample.  The sharp first-cell event is used only to retain a nondegenerate
positive `k = 2` resident of the moving geometry.
-/

namespace RBM.APrimeFirstCellDriftGlobalPoly

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- A fixed quantitative witness for the length-two `Kval` window envelope. -/
noncomputable def kvalConstant : ℝ :=
  Classical.choose (Gauss.exists_norm_Kval_le_win B
    (by norm_num : |(0 : ℝ)| < 2) 2)

theorem kvalConstant_nonneg : 0 ≤ kvalConstant := by
  exact (Classical.choose_spec (Gauss.exists_norm_Kval_le_win B
    (by norm_num : |(0 : ℝ)| < 2) 2)).1

theorem kvalConstant_spec (N : ℕ) {r v : ℝ}
    (hr0 : 0 ≤ r) (hrv : r ≤ v) (hv1 : v < 1)
    (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF)
    (hJ2 : 2 ≤ J.length) (hJle : J.length ≤ 2) :
    ‖B.Kval 0 N r J‖ ≤ kvalConstant * (etaT 0 v)⁻¹ ^ 2 := by
  exact (Classical.choose_spec (Gauss.exists_norm_Kval_le_win B
    (by norm_num : |(0 : ℝ)| < 2) 2)).2
      N r v hr0 hrv hv1 J hJ hJ2 hJle

/-- The fixed coefficient left by T445's counted two-loop crude drift. -/
noncomputable def driftConstant : ℝ :=
  144 + 16 * (4 * kvalConstant * (8 + 4 * kvalConstant)) +
    4 * (8 + 4 * kvalConstant) ^ 2

theorem driftConstant_pos : 0 < driftConstant := by
  have hK := kvalConstant_nonneg
  unfold driftConstant
  positivity

/-- On the first half-cell, the unpropagated two-loop drift costs one factor
`W L`, hence at most one power of `N`. -/
theorem norm_driftF_le_constant_mul_N (N : ℕ) {r v : ℝ}
    (hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2)
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ))
    (ω : Ω d) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    ‖DriftDef.driftF B 0 N r ((sample d).H N r ω) σ a‖ ≤
      driftConstant * (N : ℝ) := by
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hηv : 0 < etaT 0 v := etaT_pos_of_lt_one (by norm_num) hv1
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 v := by
    simp only [etaT, mE_zero, Complex.I_im, mul_one]
    linarith
  have hηinv : (etaT 0 v)⁻¹ ≤ 2 := by
    have hi := (inv_le_inv₀ hηv (by norm_num : (0 : ℝ) < 1 / 2)).2 hηhalf
    norm_num at hi ⊢
    exact hi
  have hG : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      1 ≤ J.length → J.length ≤ 3 →
      ‖gloop (B.L N) (B.W N) ((sample d).H N r ω) (zt 0 r) J‖ ≤ 8 := by
    intro J hJ hJ1 hJ3
    have hh := Gauss.norm_gloop_le_win
      (Gauss.Hflow_isHermitian d N r ω)
      (by norm_num : |(0 : ℝ)| < 2) hr0 hrv hv1 3 J hJ hJ1 hJ3
    calc
      _ ≤ (etaT 0 v)⁻¹ ^ (3 : ℕ) := hh
      _ ≤ 2 ^ (3 : ℕ) := pow_le_pow_left₀ (inv_nonneg.mpr hηv.le) hηinv 3
      _ = 8 := by norm_num
  have hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 →
      ‖B.Kval 0 N r J‖ ≤ 4 * kvalConstant := by
    intro J hJ hJ2 hJle
    have hh := kvalConstant_spec N hr0 hrv hv1 J hJ hJ2 hJle
    have hp : (etaT 0 v)⁻¹ ^ (2 : ℕ) ≤ 2 ^ (2 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr hηv.le) hηinv 2
    calc
      _ ≤ kvalConstant * (etaT 0 v)⁻¹ ^ (2 : ℕ) := hh
      _ ≤ kvalConstant * 2 ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hp kvalConstant_nonneg
      _ = 4 * kvalConstant := by ring
  have hraw := Gauss.norm_driftF_le_crude B 0 N
    (by norm_num : |(0 : ℝ)| < 2) r ((sample d).H N r ω)
    (n := 0) σ a (MG := 8) (MK := 4 * kvalConstant)
    (by norm_num) (mul_nonneg (by norm_num) kvalConstant_nonneg) hG hK
  calc
    _ ≤ (B.W N : ℝ) * (((0 : ℝ) + 2)) *
          ((B.L N : ℝ) * ((8 + 1) * 8)) +
        (((0 : ℝ) + 2)) *
          (2 * ((B.W N : ℝ) * (((0 : ℝ) + 2)) ^ 2 *
            ((B.L N : ℝ) *
              ((4 * kvalConstant) * (8 + 4 * kvalConstant))))) +
        (B.W N : ℝ) * (((0 : ℝ) + 2)) ^ 2 *
          ((B.L N : ℝ) *
            ((8 + 4 * kvalConstant) * (8 + 4 * kvalConstant))) := by
      simpa using hraw
    _ = ((B.W N : ℝ) * (B.L N : ℝ)) * driftConstant := by
      unfold driftConstant
      ring
    _ ≤ (N : ℝ) * driftConstant :=
      mul_le_mul_of_nonneg_right hWL driftConstant_pos.le
    _ = driftConstant * (N : ℝ) := by ring

/-- The quantitative pointwise envelope for the actual normalized drift.
It is uniform in the sample, the two-loop label, and both moving times. -/
theorem driftAt_le_poly (N : ℕ) (hN : 1 ≤ (N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ))
    (hWN : (d.W N : ℝ) ≤ (N : ℝ))
    {v r : ℝ} (hr0 : 0 ≤ r) (hrv : r ≤ v) (hvhalf : v ≤ 1 / 2)
    (ω : Ω d) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.driftAt d 0 60 N σ a 0 v r ω ≤
      driftConstant * (N : ℝ) ^ (61 : ℕ) := by
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hraw : ∀ b : LoopArg (d.L N) 2,
      ‖DriftDef.driftF B 0 N r ((sample d).H N r ω) σ b‖ ≤
        driftConstant * (N : ℝ) :=
    fun b => norm_driftF_le_constant_mul_N N hr0 hrv hvhalf hWL ω σ b
  have hU := Gauss.norm_Uker_apply_le_ukerRow
    (xiOf (mSigma 0) σ) (v : ℂ) r
    (DriftDef.driftF B 0 N r ((sample d).H N r ω) σ) a hraw
  have hscale := APrimeQVGlobalPoly.inv_driftScale_mul_ukerRow_le d
    (E := 0) (D := 60) (s := 0) (u := r) (v := v)
    (by norm_num) (by norm_num) (by norm_num) hr0 hrv hv1 N hWN σ a
  have hscale' :
      (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ *
          Gauss.ukerRow (xiOf (mSigma 0) σ) (v : ℂ) a r ≤
        (N : ℝ) ^ (60 : ℕ) := by
    simpa only [Real.rpow_ofNat] using hscale
  have hspos : 0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v :=
    APrimeDriftTimeFamily.driftScale_pos d (by norm_num) hv0 hv1 N a
  have hC0 : 0 ≤ driftConstant * (N : ℝ) :=
    mul_nonneg driftConstant_pos.le (by positivity)
  calc
    APrimeDriftTimeFamily.driftAt d 0 60 N σ a 0 v r ω =
        (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ *
          ‖Uker (d.L N) (xiOf (mSigma 0) σ) (r : ℂ) (v : ℂ)
            (DriftDef.driftF B 0 N r ((sample d).H N r ω) σ) a‖ := by
      unfold APrimeDriftTimeFamily.driftAt
      rw [div_eq_inv_mul]
    _ ≤ (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ *
          (Gauss.ukerRow (xiOf (mSigma 0) σ) (v : ℂ) a r *
            (driftConstant * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hU (inv_nonneg.mpr hspos.le)
    _ = ((APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)⁻¹ *
          Gauss.ukerRow (xiOf (mSigma 0) σ) (v : ℂ) a r) *
            (driftConstant * (N : ℝ)) := by ring
    _ ≤ (N : ℝ) ^ (60 : ℕ) * (driftConstant * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hscale' hC0
    _ = driftConstant * (N : ℝ) ^ (61 : ℕ) := by ring

/-- The all-sample polynomial bound at every actual first-cell moving
endpoint, including `k = 0`. -/
def globalMovingDriftPoly (τ' : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ k : ℕ, k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
        APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
          driftConstant * (N : ℝ) ^ (61 : ℕ)

theorem eventually_globalMovingDriftPoly {τ' : ℝ} (hτ' : 0 < τ') :
    globalMovingDriftPoly τ' := by
  filter_upwards [d.dim, eventually_ge_atTop 1] with N hdim hNnat
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have hL1 : 1 ≤ (d.L N : ℝ) := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hW0 : 0 ≤ (d.W N : ℝ) := by positivity
  have hWN : (d.W N : ℝ) ≤ (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 hW0]
  intro k hk
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  change ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
    APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      driftConstant * (N : ℝ) ^ (61 : ℕ)
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hvCell := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 :=
    hvCell.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  intro r hr a ω
  exact driftAt_le_poly N hN hWL hWN hr.1 hr.2 hvhalf ω Step2.sigPM a

/-- The two closed-interval endpoints are explicit consequences of the
global moving bound. -/
theorem eventually_globalMovingDriftEndpoints {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      ∀ k : ℕ, k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        (∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
          APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v 0 ω ≤
            driftConstant * (N : ℝ) ^ (61 : ℕ)) ∧
        ∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
          APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v v ω ≤
            driftConstant * (N : ℝ) ^ (61 : ℕ) := by
  filter_upwards [eventually_globalMovingDriftPoly hτ'] with N hglobal
  intro k hk
  have hprof := hglobal k hk
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hv0 : 0 ≤ v := by
    have hwin := (APrimeSupportRunning.firstT_bounds hτ' N).1
    exact (MomentDuhamelCut.netFinset_subset_Icc hwin
      (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)).1
  exact ⟨fun a ω => hprof 0 ⟨le_rfl, hv0⟩ a ω,
    fun a ω => hprof v ⟨hv0, le_rfl⟩ a ω⟩

/-- A same-event positive `k = 2` resident, used only to certify that the
moving first-cell geometry supporting the global bound is nonempty. -/
def positiveGlobalMovingDriftPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < v ∧ v ≤ firstCellT τ' N ∧ firstCellT τ' N ≤ 1 / 2 ∧
    (∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
        driftConstant * (N : ℝ) ^ (61 : ℕ)) ∧
    (∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v 0 ω ≤
        driftConstant * (N : ℝ) ^ (61 : ℕ)) ∧
    ∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v v ω ≤
        driftConstant * (N : ℝ) ^ (61 : ℕ)

theorem positiveGlobalMovingDriftPlateau_of_sharp {τ' δ ν : ℝ}
    (hglobal : globalMovingDriftPoly τ')
    (hpositive :
      APrimeFirstCellSharpCommonEvent.positiveSharpPlateau τ' δ ν) :
    positiveGlobalMovingDriftPlateau τ' δ ν := by
  filter_upwards [hglobal, hpositive] with N hglobal hpositive
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hpositive
  obtain ⟨ω, hω, hk, hw, hvpos, hvle, hvhalf, _hsource,
    _hJall, _hJ0, _hJv⟩ := hpositive
  have hprof := hglobal 2 hk
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  change ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
    APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      driftConstant * (N : ℝ) ^ (61 : ℕ) at hprof
  have hv0 : 0 ≤ v := hvpos.le
  have hprofω : ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
        driftConstant * (N : ℝ) ^ (61 : ℕ) :=
    fun r hr a => hprof r hr a ω
  refine ⟨ω, hω, hk, hw, hvpos, hvle, hvhalf,
    (by simpa only [v] using hprofω), ?_, ?_⟩
  · intro a
    exact hprof 0 ⟨le_rfl, hv0⟩ a ω
  · intro a
    exact hprof v ⟨hv0, le_rfl⟩ a ω

/-- Closed all-sample drift producer together with a nondegenerate resident
of the accepted sharp event. -/
theorem exists_globalMovingDriftPoly_with_positive_plateau :
    0 < driftConstant ∧
    ∃ τ' : ℝ, 0 < τ' ∧ globalMovingDriftPoly τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        positiveGlobalMovingDriftPlateau τ' δ ν := by
  refine ⟨driftConstant_pos, ?_⟩
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  have hglobal := eventually_globalMovingDriftPoly hτ'
  refine ⟨τ', hτ', hglobal, ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp,
    positiveGlobalMovingDriftPlateau_of_sharp hglobal hpositive⟩

end RBM.APrimeFirstCellDriftGlobalPoly

#print axioms RBM.APrimeFirstCellDriftGlobalPoly.kvalConstant_spec
#print axioms RBM.APrimeFirstCellDriftGlobalPoly.norm_driftF_le_constant_mul_N
#print axioms RBM.APrimeFirstCellDriftGlobalPoly.driftAt_le_poly
#print axioms RBM.APrimeFirstCellDriftGlobalPoly.eventually_globalMovingDriftPoly
#print axioms RBM.APrimeFirstCellDriftGlobalPoly.eventually_globalMovingDriftEndpoints
#print axioms RBM.APrimeFirstCellDriftGlobalPoly.positiveGlobalMovingDriftPlateau_of_sharp
#print axioms RBM.APrimeFirstCellDriftGlobalPoly.exists_globalMovingDriftPoly_with_positive_plateau
