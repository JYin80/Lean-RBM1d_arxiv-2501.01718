/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellJointMeasurable
import RBM1D.Gauss.APrimeFirstCellJointGlobalPoly

/-!
# T462: actual first-cell T361 joint-cross sample regularity
-/

namespace RBM.APrimeFirstCellJointCrossRegularity

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (N k : ℕ) : ℝ :=
  APrimeFirstCellJointMeasurable.endpoint N k

noncomputable def canonicalM (τ' : ℝ) (N : ℕ) : ℕ :=
  APrimeFirstCellJointMeasurable.canonicalM τ' N

noncomputable def cutoff (τ' δ : ℝ) (N k : ℕ) : Ω d → ℝ :=
  APrimeSmoothWeightActual.cutoff d 0 60 δ (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)

noncomputable def actualY (N k : ℕ) (a : LoopArg (d.L N) 2)
    (r : ℝ) : Ω d → ℝ :=
  APrimeFirstCellSampleRegularity.Y N k a r

noncomputable def Ycut (τ' δ : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : Ω d → ℝ :=
  fun ω => cutoff τ' δ N k ω * actualY N k a r ω

noncomputable def jointRate (τ' δ : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : Ω d → ℝ :=
  APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k (canonicalM τ' N)
    Step2.sigPM a (endpoint N k) r

/-- The five sample fields consumed verbatim by T361's actual joint-event
cross estimate. -/
structure JointCrossSampleRegularity (p : ℕ) (Y Z : Ω d → ℝ) : Prop where
  hZm : AEStronglyMeasurable Z (P d)
  hZi : Integrable (fun ω => |Z ω| ^ (2 * p)) (P d)
  hYm : AEStronglyMeasurable Y (P d)
  hYi : Integrable (fun ω => |Y ω| ^ (2 * p)) (P d)
  hProdInt : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |Z ω|) (P d)

private theorem pow_pred_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {n : ℕ} (hn : 1 ≤ n) : x ^ (n - 1) * y ≤ x ^ n + y ^ n := by
  rcases le_total y x with hyx | hxy
  · have h1 : x ^ (n - 1) * y ≤ x ^ (n - 1) * x :=
      mul_le_mul_of_nonneg_left hyx (pow_nonneg hx _)
    have h2 : x ^ (n - 1) * x = x ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      x ^ (n - 1) * y ≤ x ^ (n - 1) * x := h1
      _ = x ^ n := h2
      _ ≤ x ^ n + y ^ n := le_add_of_nonneg_right (pow_nonneg hy _)
  · have h1 : x ^ (n - 1) * y ≤ y ^ (n - 1) * y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy _) hy
    have h2 : y ^ (n - 1) * y = y ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      x ^ (n - 1) * y ≤ y ^ (n - 1) * y := h1
      _ = y ^ n := h2
      _ ≤ x ^ n + y ^ n := le_add_of_nonneg_left (pow_nonneg hx _)

private theorem integrable_abs_pow_of_bound {f : Ω d → ℝ} (n : ℕ)
    (hf : Measurable f) {C : ℝ} (_hC0 : 0 ≤ C)
    (hfC : ∀ ω, 0 ≤ f ω ∧ f ω ≤ C) :
    Integrable (fun ω => |f ω| ^ n) (P d) := by
  apply Integrable.of_bound
    ((continuous_abs.measurable.comp hf).pow_const n).aestronglyMeasurable (C ^ n)
  exact Filter.Eventually.of_forall fun ω => by
    change ‖|f ω| ^ n‖ ≤ C ^ n
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (hfC ω).1]
    exact pow_le_pow_left₀ (hfC ω).1 (hfC ω).2 n

private theorem integrable_mixed_of_moments {p : ℕ} (hp : 1 ≤ p)
    {Y Z : Ω d → ℝ}
    (hYm : AEStronglyMeasurable Y (P d))
    (hZm : AEStronglyMeasurable Z (P d))
    (hYi : Integrable (fun ω => |Y ω| ^ (2 * p)) (P d))
    (hZi : Integrable (fun ω => |Z ω| ^ (2 * p)) (P d)) :
    Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |Z ω|) (P d) := by
  have hm : AEStronglyMeasurable
      (fun ω => |Y ω| ^ (2 * p - 1) * |Z ω|) (P d) := by
    have hraw := (hYm.norm.pow (2 * p - 1)).mul hZm.norm
    exact hraw.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.pow_apply, Pi.mul_apply, Real.norm_eq_abs])
  apply Integrable.mono' (hYi.add hZi) hm
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (abs_nonneg _))]
    exact pow_pred_mul_le (abs_nonneg _) (abs_nonneg _) (by omega : 1 ≤ 2 * p)

/-- For a fixed moment order chosen first, all five actual T361 sample fields
hold eventually in matrix size, uniformly over the moving first-cell mesh. -/
theorem eventually_actual_jointCrossSampleRegularity {τ' δ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N,
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) (endpoint N k),
        JointCrossSampleRegularity p (Ycut τ' δ N k a r)
          (jointRate τ' δ N k a r) := by
  intro p hp
  filter_upwards
    [APrimeFirstCellJointGlobalPoly.eventually_jointRate_bounds hτ' hδ,
      eventually_ge_atTop (2 : ℕ)] with N hZbound hN
  intro k hk a r hr
  have hNpos : 0 < N := by omega
  have hNtwo : 2 ≤ N := hN
  let c := cutoff τ' δ N k
  let y := actualY N k a r
  let Yc := Ycut τ' δ N k a r
  let Z := jointRate τ' δ N k a r
  have hreg := APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity
    (δ := δ) hτ' hp hNpos hk a hr
  have hmeas :=
    APrimeFirstCellJointMeasurable.measurable_actual_prefixGradient_and_jointRate
      (δ := δ) hτ' hNpos hk a hr
  have hZm : AEStronglyMeasurable Z (P d) := by
    exact hmeas.2.aestronglyMeasurable
  have hZC : ∀ ω, 0 ≤ Z ω ∧ Z ω ≤ 2 ^ (26 : ℕ) * (N : ℝ) ^ (130 : ℕ) := by
    intro ω
    exact hZbound k hk a r hr ω
  have hZi : Integrable (fun ω => |Z ω| ^ (2 * p)) (P d) := by
    exact integrable_abs_pow_of_bound (2 * p) hmeas.2 (by positivity) hZC
  have hc0 : ∀ ω, 0 ≤ c ω := by
    intro ω
    exact Cutoff.cutChi_nonneg _
  have hy0 : ∀ ω, 0 ≤ y ω := by
    intro ω
    change 0 ≤ ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r (Gauss.Hflow d N r ω)‖
    exact norm_nonneg _
  have hactive : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧ 2 ≤ N := ⟨hk, hNtwo⟩
  have hw : ∀ ω, APrimeFirstCellSampleRegularity.weight τ' δ p N k ω =
      c ω ^ (2 * p) := by
    intro ω
    simp only [APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellGeneratorHle.canonicalWeight,
      APrimeFirstCellGeneratorHle.actualWeight,
      APrimeSmoothWeightActual.weight, if_pos hactive, c, cutoff,
      canonicalM, APrimeFirstCellJointMeasurable.canonicalM]
  have hroot : ∀ ω,
      (APrimeFirstCellSampleRegularity.weight τ' δ p N k ω ^
        ((1 : ℝ) / (2 * (p : ℝ)))) = c ω := by
    intro ω
    rw [hw]
    have h := Real.pow_rpow_inv_natCast (hc0 ω) (by omega : 2 * p ≠ 0)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, one_div] using h
  have hscale : APrimeDuhamelModel.wscale
      (APrimeFirstCellSampleRegularity.weight τ' δ p N k) p y = Yc := by
    funext ω
    simp only [APrimeDuhamelModel.wscale, hroot, Yc, Ycut, c, y]
  have hYm : AEStronglyMeasurable Yc (P d) := by
    rw [← hscale]
    exact hreg.hYm
  have hYi : Integrable (fun ω => |Yc ω| ^ (2 * p)) (P d) := by
    exact hreg.hYi.congr (Filter.Eventually.of_forall fun ω => by
      change APrimeFirstCellSampleRegularity.weight τ' δ p N k ω *
          |y ω| ^ (2 * p) = |Yc ω| ^ (2 * p)
      rw [hw]
      change c ω ^ (2 * p) * |y ω| ^ (2 * p) =
        |c ω * y ω| ^ (2 * p)
      rw [abs_of_nonneg (mul_nonneg (hc0 ω) (hy0 ω)), mul_pow,
        abs_of_nonneg (hy0 ω)])
  exact ⟨hZm, hZi, hYm, hYi,
    integrable_mixed_of_moments hp hYm hZm hYi hZi⟩

/-- Both endpoints of every moving first-cell interval carry the five-field
package. -/
theorem eventually_actual_jointCrossSampleRegularity_endpoints {τ' δ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N,
      ∀ a : LoopArg (d.L N) 2,
        JointCrossSampleRegularity p (Ycut τ' δ N k a 0)
            (jointRate τ' δ N k a 0) ∧
          JointCrossSampleRegularity p
            (Ycut τ' δ N k a (endpoint N k))
            (jointRate τ' δ N k a (endpoint N k)) := by
  intro p hp
  filter_upwards [eventually_actual_jointCrossSampleRegularity hτ' hδ p hp]
    with N hN
  intro k hk a
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : endpoint N k ∈ Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  exact ⟨hN k hk a 0 ⟨le_rfl, hv.1⟩,
    hN k hk a (endpoint N k) ⟨hv.1, le_rfl⟩⟩

/-- The literal actual joint rate vanishes on the zero cell. -/
theorem jointRate_k_zero {τ' δ : ℝ} {N : ℕ} (hN : 0 < N)
    (a : LoopArg (d.L N) 2) : jointRate τ' δ N 0 a 0 = 0 := by
  simpa only [jointRate, endpoint, APrimeFirstCellJointMeasurable.endpoint,
    APrimeFirstCellSampleRegularity.endpoint,
    APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero,
    canonicalM, APrimeFirstCellJointMeasurable.canonicalM] using
      (APrimeFirstCellJointMeasurable.jointRate_k_zero
        (τ' := τ') (δ := δ) hN a 0)

/-- The zero cell is included separately in the eventual package. -/
theorem eventually_actual_jointCrossSampleRegularity_k_zero {τ' δ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ a : LoopArg (d.L N) 2,
        JointCrossSampleRegularity p (Ycut τ' δ N 0 a 0)
          (jointRate τ' δ N 0 a 0) := by
  intro p hp
  filter_upwards [eventually_actual_jointCrossSampleRegularity hτ' hδ p hp]
    with N hN
  intro a
  have hv : endpoint N 0 = 0 := by
    simp only [endpoint, APrimeFirstCellJointMeasurable.endpoint,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero]
  exact hN 0 (Nat.zero_le _) a 0 (by rw [hv]; exact ⟨le_rfl, le_rfl⟩)

/-- T459's same-event nonzero resident, augmented by all five sample fields
for one moment order selected before the eventual matrix size. -/
def PositiveJointCrossRegularityResident (τ' δ ν : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ q : ℕ, APrimeFirstCellGeneratorHle.actualWeight τ' δ 2 q N 2 N ω = 1) ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) (endpoint N 2),
      JointCrossSampleRegularity p (Ycut τ' δ N 2 a r)
        (jointRate τ' δ N 2 a r)

theorem positiveJointCrossRegularityResident_of_measurable {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) {p : ℕ} (hp : 1 ≤ p)
    (hresident : APrimeFirstCellJointMeasurable.PositiveJointMeasurableResident
      τ' δ ν) :
    PositiveJointCrossRegularityResident τ' δ ν p := by
  filter_upwards
    [hresident, eventually_actual_jointCrossSampleRegularity hτ' hδ p hp]
      with N hres hreg
  obtain ⟨ω, hω, hk, hw, hu2, hu2T, _hprefix, _hjoint⟩ := hres
  exact ⟨ω, hω, hk, hw, hu2, hu2T, hreg 2 hk⟩

/-- Closed producer retaining T459's measurable high-probability event and
the actual-weight `k = 2` resident. -/
theorem exists_sharpCommonEvent_with_jointCrossRegularity :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        ∀ p : ℕ, 1 ≤ p → PositiveJointCrossRegularityResident τ' δ ν p := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellJointMeasurable.exists_sharpCommonEvent_with_jointMeasurable
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hprob, hresident⟩ := hall δ hδ hδ100 ν hν
  refine ⟨hmeas, hprob, ?_⟩
  intro p hp
  exact positiveJointCrossRegularityResident_of_measurable
    hτ' hδ.le hp hresident

#print axioms eventually_actual_jointCrossSampleRegularity
#print axioms eventually_actual_jointCrossSampleRegularity_endpoints
#print axioms jointRate_k_zero
#print axioms eventually_actual_jointCrossSampleRegularity_k_zero
#print axioms positiveJointCrossRegularityResident_of_measurable
#print axioms exists_sharpCommonEvent_with_jointCrossRegularity

end

end RBM.APrimeFirstCellJointCrossRegularity
