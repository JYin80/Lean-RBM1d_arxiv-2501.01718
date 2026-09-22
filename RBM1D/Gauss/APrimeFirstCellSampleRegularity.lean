/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellGeneratorHle
import RBM1D.Gauss.APrimeCrossJointSplit

/-!
# T451: fixed-size sample regularity for the actual first-cell fields
-/

namespace RBM.APrimeFirstCellSampleRegularity

open Filter MeasureTheory Set Gauss CutHypTheta APrimeDuhamelModel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (N k : ℕ) : ℝ :=
  APrimeFirstCellGeneratorHle.endpoint N k

noncomputable def weight (τ' δ : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  APrimeFirstCellGeneratorHle.canonicalWeight τ' δ p N k

noncomputable def Y (N k : ℕ) (a : LoopArg (d.L N) 2)
    (r : ℝ) : Ω d → ℝ :=
  APrimeDuhamelModel.flowY d N
    (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 (endpoint N k)) r

noncomputable def G (N k : ℕ) (a : LoopArg (d.L N) 2)
    (r : ℝ) : Ω d → ℝ :=
  APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 (endpoint N k) r

noncomputable def Q (N k : ℕ) (a : LoopArg (d.L N) 2)
    (r : ℝ) : Ω d → ℝ :=
  APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (endpoint N k) r

/-- The three measurability and five sample-integrability premises appearing
verbatim in `APrimeDuhamelModel.momFlowDeriv_le`. -/
structure GeneratorSampleRegularity (p : ℕ) (w Y G Q : Ω d → ℝ) : Prop where
  hYm : AEStronglyMeasurable (wscale w p Y) (P d)
  hGm : AEStronglyMeasurable (wscale w p G) (P d)
  hQm : AEStronglyMeasurable (wscaleQ w p Q) (P d)
  hYi : Integrable (fun ω => w ω * |Y ω| ^ (2 * p)) (P d)
  hGi : Integrable (fun ω => w ω * |G ω| ^ (2 * p)) (P d)
  hQi : Integrable (fun ω => w ω * |Q ω| ^ p) (P d)
  hm1 : Integrable (fun ω => w ω * |Y ω| ^ (2 * p - 1) * |G ω|) (P d)
  hm2 : Integrable (fun ω => w ω * |Y ω| ^ (2 * p - 2) * Q ω) (P d)

private theorem integrable_of_measurable_bound (f : Ω d → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) :
    Integrable f (P d) := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hC ω

private theorem integrable_weighted_pow {w f : Ω d → ℝ} (n : ℕ)
    (hw : Measurable w) (hf : Measurable f)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1)
    {C : ℝ} (_hC0 : 0 ≤ C) (hfC : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => w ω * |f ω| ^ n) (P d) := by
  apply integrable_of_measurable_bound _
      (hw.mul ((continuous_abs.measurable.comp hf).pow_const n))
      (C ^ n)
  intro ω
  change |w ω * |f ω| ^ n| ≤ C ^ n
  rw [abs_of_nonneg (mul_nonneg (hw0 ω) (pow_nonneg (abs_nonneg _) _))]
  calc
    w ω * |f ω| ^ n ≤ 1 * |f ω| ^ n :=
      mul_le_mul_of_nonneg_right (hw1 ω) (pow_nonneg (abs_nonneg _) _)
    _ ≤ C ^ n := by simpa using pow_le_pow_left₀ (abs_nonneg _) (hfC ω) n

private theorem integrable_weighted_mixed {w f g : Ω d → ℝ} (n : ℕ)
    (hw : Measurable w) (hf : Measurable f) (hg : Measurable g)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (_hCg0 : 0 ≤ Cg)
    (hfC : ∀ ω, |f ω| ≤ Cf) (hgC : ∀ ω, |g ω| ≤ Cg) :
    Integrable (fun ω => w ω * |f ω| ^ n * |g ω|) (P d) := by
  apply integrable_of_measurable_bound _
      ((hw.mul ((continuous_abs.measurable.comp hf).pow_const n)).mul
        (continuous_abs.measurable.comp hg)) (Cf ^ n * Cg)
  intro ω
  change abs (w ω * |f ω| ^ n * |g ω|) ≤ Cf ^ n * Cg
  rw [abs_of_nonneg (mul_nonneg
    (mul_nonneg (hw0 ω) (pow_nonneg (abs_nonneg _) _)) (abs_nonneg _))]
  calc
    w ω * |f ω| ^ n * |g ω| ≤ (1 * |f ω| ^ n) * |g ω| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hw1 ω) (pow_nonneg (abs_nonneg _) _))
        (abs_nonneg _)
    _ = |f ω| ^ n * |g ω| := by ring
    _ ≤ Cf ^ n * Cg := by
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hfC ω) n)
        (hgC ω) (abs_nonneg _) (pow_nonneg hCf0 _)

set_option maxHeartbeats 5000000 in
-- The fixed-size proof elaborates the full concrete Gaussian field bundle and
-- the Gaussian uniform-bound producers have large dependent signatures.
/-- At fixed positive size, every actual field used by the weighted generator
has the required sample regularity under the same Gaussian measure. -/
theorem actual_generator_sampleRegularity {τ' δ : ℝ} (hτ' : 0 < τ')
    {p N k : ℕ} (hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (endpoint N k)) :
    GeneratorSampleRegularity p (weight τ' δ p N k)
      (Y N k a r) (G N k a r) (Q N k a r) := by
  let v := endpoint N k
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  let w := weight τ' δ p N k
  let y := Y N k a r
  let g := G N k a r
  let q := Q N k a r
  change GeneratorSampleRegularity p w y g q
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : v ∈ Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hm : 1 ≤ m := by
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
  have hwc : Continuous w := by
    exact APrimeSmoothWeightActual.continuous_weight d
      (E := 0) (D := 60) (δ := δ) (s := fun _ => 0)
      (t := firstCellT τ') (mesh := APrimeSmoothTransition.transitionMesh)
      (N₀ := 2) (p := p) (N := N) (k := k) (m := m)
      (by norm_num) (by norm_num) hN hm hu
  have hw : Measurable w := hwc.measurable
  have hw0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N k m ω
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 δ (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N k m ω
  have hyc : Continuous y := by
    have hraw := Gauss.continuous_uker_lkT_omega d 0 N
      (Gauss.window_im_ne_zero (E := 0) (by norm_num) hv1 r hr)
      (Gauss.window_norm_mul_lt (E := 0) (by norm_num) (by norm_num) hv1 r hr)
      Step2.sigPM (xiOf (mSigma 0) Step2.sigPM) a (v : ℂ)
    have heq : y = fun ω =>
        ‖Uker (d.L N) (xiOf (mSigma 0) Step2.sigPM) (r : ℂ) (v : ℂ)
          (SumZeroDyn.lkT (Gauss.sample d) 0 N r ω Step2.sigPM) a‖ /
            APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v := by
      funext ω
      exact APrimeDriftTimeFamily.flowY_coordAt d 0 60 N Step2.sigPM a
        (by norm_num) hv.1 hv1 r ω
    rw [heq]
    exact hraw.norm.div_const _
  have hy : Measurable y := hyc.measurable
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v :=
    APrimeDriftTimeFamily.driftScale_pos d (by norm_num) hv.1 hv1 N a
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) 0 N (s := 0) (v := v)
      (by norm_num) (by norm_num) hv1 Step2.sigPM
  obtain ⟨CYraw, hCYraw0, hCYraw⟩ := Gauss.exists_bdd₀_ukerObsT
    (d := d) (N := N) 0 (List.length_ofFn) (by norm_num)
    (xiOf (mSigma 0) Step2.sigPM) (v : ℂ)
    (fun u b => (Gauss.band d).Kval 0 N u (LoopData.idx (Step2.sigPM, b))) a
    (Gauss.window_eta_pos (E := 0) (by norm_num) hv1) hcK
    (Gauss.window_le_abs_im (E := 0) (by norm_num) hv1) hKb
  let CY := CYraw / APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v
  have hCY0 : 0 ≤ CY := div_nonneg hCYraw0 hscale.le
  have hyC : ∀ ω, |y ω| ≤ CY := by
    intro ω
    change |‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v r
      (Gauss.Hflow d N r ω)‖| ≤ CY
    rw [abs_norm, APrimeDriftTimeFamily.coordAt, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
    exact div_le_div_of_nonneg_right
      (hCYraw r hr (Gauss.Hflow d N r ω)) hscale.le
  have hgc : Continuous g := by
    change Continuous (fun ω => ‖Uker (d.L N)
      (xiOf (mSigma 0) Step2.sigPM) (r : ℂ) (v : ℂ)
      (DriftDef.driftF (Gauss.band d) 0 N r ((Gauss.sample d).H N r ω)
        Step2.sigPM) a‖ /
      APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v)
    exact (Gauss.continuous_uker_driftF_omega d 0 N
      (Gauss.window_im_ne_zero (E := 0) (by norm_num) hv1 r hr)
      (Gauss.window_norm_mul_lt (E := 0) (by norm_num) (by norm_num) hv1 r hr)
      Step2.sigPM a (v : ℂ)).norm.div_const _
  have hg : Measurable g := hgc.measurable
  obtain ⟨CGraw, hCGraw0, hCGraw⟩ := Gauss.exists_bdd_uker_driftF
    (Gauss.band d) 0 N Step2.sigPM a (v : ℂ)
    (Gauss.window_eta_pos (E := 0) (by norm_num) hv1)
    (Gauss.window_le_abs_im (E := 0) (by norm_num) hv1) hKb hK'b
    (Gauss.window_norm_mul_lt (E := 0) (by norm_num) (by norm_num) hv1)
    (Gauss.window_norm_xi_lt (E := 0) (by norm_num) (by norm_num) hv1 Step2.sigPM)
    (Gauss.window_norm_xi_lt (E := 0) (by norm_num) (by norm_num) hv1 Step2.sigPM v
      ⟨hv.1, le_rfl⟩)
  let CG := CGraw / APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v
  have hCG0 : 0 ≤ CG := div_nonneg hCGraw0 hscale.le
  have hgC : ∀ ω, |g ω| ≤ CG := by
    intro ω
    rw [show g ω = ‖Uker (d.L N) (xiOf (mSigma 0) Step2.sigPM)
      (r : ℂ) (v : ℂ)
      (DriftDef.driftF (Gauss.band d) 0 N r ((Gauss.sample d).H N r ω)
        Step2.sigPM) a‖ /
      APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v from rfl,
      abs_div, abs_norm, abs_of_pos hscale]
    exact div_le_div_of_nonneg_right
      (hCGraw r hr _ (Gauss.Hflow_isHermitian d N r ω)) hscale.le
  have hq : Measurable q := by
    let rr : Icc (0 : ℝ) v := ⟨r, hr⟩
    have hembed : Measurable (fun ω : Ω d => (rr, ω)) :=
      measurable_const.prodMk measurable_id
    have h := APrimeQVRateTime.measurable_qvAt_on_window
      d 0 60 N Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
    have hcomp := h.comp hembed
    have heq : (fun ω : Ω d =>
        APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω) =
        (fun ω : Ω d =>
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v rr.1 ω) := by
      rfl
    change Measurable (fun ω : Ω d =>
      APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 v r ω)
    rw [heq]
    simpa only [Function.comp_def] using hcomp
  obtain ⟨CQ, hCQ0, hQC⟩ := APrimeQVRateTime.exists_bdd_qvAt
    d 0 60 N Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
  have hq0 : ∀ ω, 0 ≤ q ω := fun ω => (hQC r hr ω).1
  have hqC : ∀ ω, |q ω| ≤ CQ := by
    intro ω
    rw [abs_of_nonneg (hq0 ω)]
    exact (hQC r hr ω).2
  have hwr : Measurable (fun ω => w ω ^ ((1 : ℝ) / (2 * (p : ℝ)))) :=
    (hwc.rpow_const (fun _ => Or.inr (by positivity))).measurable
  have hwrQ : Measurable (fun ω => w ω ^ ((1 : ℝ) / (p : ℝ))) :=
    (hwc.rpow_const (fun _ => Or.inr (by positivity))).measurable
  refine ⟨?_, ?_, ?_,
    integrable_weighted_pow (2 * p) hw hy hw0 hw1 hCY0 hyC,
    integrable_weighted_pow (2 * p) hw hg hw0 hw1 hCG0 hgC,
    integrable_weighted_pow p hw hq hw0 hw1 hCQ0 hqC,
    integrable_weighted_mixed (2 * p - 1) hw hy hg hw0 hw1
      hCY0 hCG0 hyC hgC, ?_⟩
  · exact (hwr.mul hy).aestronglyMeasurable
  · exact (hwr.mul hg).aestronglyMeasurable
  · exact (hwrQ.mul hq).aestronglyMeasurable
  · have hqi := integrable_weighted_mixed (2 * p - 2) hw hy hq hw0 hw1
      hCY0 hCQ0 hyC hqC
    exact hqi.congr (Filter.Eventually.of_forall fun ω => by
      change w ω * |y ω| ^ (2 * p - 2) * |q ω| =
        w ω * |y ω| ^ (2 * p - 2) * q ω
      rw [abs_of_nonneg (hq0 ω)])

/-- The exact remaining T361 sample-space obligation.  The current public
API exports neither measurability nor a global fixed-size bound for
`prefixGradient`; its bound exists only as the private theorem
`APrimeSmoothWeightActual.exists_prefixMatrix_fderiv_bound`. -/
def JointRateSampleObligation (τ' δ : ℝ) (p N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : Prop :=
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  let Z := APrimeCrossJointSplit.jointRate d 0 60 δ (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k m Step2.sigPM a (endpoint N k) r
  AEStronglyMeasurable Z (P d) ∧
    Integrable (fun ω => |Z ω| ^ (2 * p)) (P d) ∧
    Integrable (fun ω =>
      |APrimeSmoothWeightActual.cutoff d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
          (endpoint N k) r (Gauss.Hflow d N r ω)‖| ^ (2 * p - 1) * |Z ω|)
      (P d)

/-- The sample-regularity package at both endpoints of the moving interval. -/
theorem actual_generator_sampleRegularity_endpoints {τ' δ : ℝ} (hτ' : 0 < τ')
    {p N k : ℕ} (hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) :
    GeneratorSampleRegularity p (weight τ' δ p N k)
        (Y N k a 0) (G N k a 0) (Q N k a 0) ∧
      GeneratorSampleRegularity p (weight τ' δ p N k)
        (Y N k a (endpoint N k)) (G N k a (endpoint N k))
        (Q N k a (endpoint N k)) := by
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : endpoint N k ∈ Icc (0 : ℝ) (firstCellT τ' N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  exact ⟨actual_generator_sampleRegularity hτ' hp hN hk a ⟨le_rfl, hv.1⟩,
    actual_generator_sampleRegularity hτ' hp hN hk a ⟨hv.1, le_rfl⟩⟩

/-- The moment order is selected before the eventual matrix size. -/
theorem eventually_actual_generator_sampleRegularity {τ' δ : ℝ} (hτ' : 0 < τ') :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N,
      ∀ a : LoopArg (d.L N) 2, ∀ r ∈ Icc (0 : ℝ) (endpoint N k),
        GeneratorSampleRegularity p (weight τ' δ p N k)
          (Y N k a r) (G N k a r) (Q N k a r) := by
  intro p hp
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  intro k hk a r hr
  exact actual_generator_sampleRegularity hτ' hp (by omega) hk a hr

/-- The degenerate `k = 0` cell is included explicitly. -/
theorem actual_generator_sampleRegularity_k_zero {τ' δ : ℝ} (hτ' : 0 < τ')
    {p N : ℕ} (hp : 1 ≤ p) (hN : 0 < N)
    (a : LoopArg (d.L N) 2) :
    GeneratorSampleRegularity p (weight τ' δ p N 0)
      (Y N 0 a 0) (G N 0 a 0) (Q N 0 a 0) := by
  have hr : (0 : ℝ) ∈ Icc 0 (endpoint N 0) := by
    simp only [endpoint, APrimeFirstCellGeneratorHle.endpoint, cutNetPt_zero,
      mem_Icc, le_refl, and_self]
  exact actual_generator_sampleRegularity hτ' hp hN (Nat.zero_le _) a hr

/-- The nonzero `k = 2` resident keeps the same sharp event and actual-weight
geometry while carrying sample regularity for every moment order. -/
def PositiveSampleRegularityResident (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeFirstCellGeneratorHle.actualWeight τ' δ 2 p N 2 N ω = 1) ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    ∀ p : ℕ, 1 ≤ p → ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (0 : ℝ) (endpoint N 2),
        GeneratorSampleRegularity p (weight τ' δ p N 2)
          (Y N 2 a r) (G N 2 a r) (Q N 2 a r)

theorem positiveSampleRegularityResident_of_generator {τ' δ ν : ℝ}
    (hτ' : 0 < τ')
    (hresident : APrimeFirstCellGeneratorHle.positiveActualWeightResident τ' δ ν) :
    PositiveSampleRegularityResident τ' δ ν := by
  filter_upwards [hresident, eventually_ge_atTop (1 : ℕ)] with N hres hN
  obtain ⟨ω, hω, hk, hw, hu2, hu2T, _⟩ := hres
  refine ⟨ω, hω, hk, hw, hu2, hu2T, ?_⟩
  intro p hp a r hr
  exact actual_generator_sampleRegularity hτ' hp (by omega) hk a hr

/-- Closed producer for the measurable high-probability event and its actual
nonzero-weight sample-regularity resident. -/
theorem exists_sharpCommonEvent_with_sampleRegularity :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        PositiveSampleRegularityResident τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellGeneratorHle.exists_sharpCommonEvent_with_generatorHle
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, hresident⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, positiveSampleRegularityResident_of_generator hτ' hresident⟩

#print axioms actual_generator_sampleRegularity
#print axioms actual_generator_sampleRegularity_endpoints
#print axioms eventually_actual_generator_sampleRegularity
#print axioms actual_generator_sampleRegularity_k_zero
#print axioms positiveSampleRegularityResident_of_generator
#print axioms exists_sharpCommonEvent_with_sampleRegularity

end


end RBM.APrimeFirstCellSampleRegularity
