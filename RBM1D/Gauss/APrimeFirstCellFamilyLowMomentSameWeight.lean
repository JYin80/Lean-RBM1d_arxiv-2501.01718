/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellFamilyHighMoment
import RBM1D.Gauss.APrimeInit

/-!
# T521: lower moments of the first-cell maximum under the same high-order weight

For fixed `1 ≤ p ≤ P` with `P ≥ 8000`, the actual family maximum has the
T512 bound at order `p` under the unchanged canonical order-`P` weight.
The low and fractional-power integrability premises come from the actual
bounded sample envelope, while the high weighted power uses T451/T512.
-/

namespace RBM.APrimeFirstCellFamilyLowMomentSameWeight

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellFamilyHighMoment.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellFamilyHighMoment.alpha

private theorem endpoint_bounds {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    0 ≤ endpoint N k ∧ endpoint N k < 1 := by
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  exact ⟨hv.1, hv.2.trans_lt (ht.2.trans_lt (by norm_num))⟩

/-- The same actual coordinate continuity used in T451, including `k = 0`. -/
theorem continuous_endpoint_Y {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) : Continuous (Y N k a (endpoint N k)) := by
  have hv := endpoint_bounds hτ' hk
  have hr : endpoint N k ∈ Icc (0 : ℝ) (endpoint N k) := ⟨hv.1, le_rfl⟩
  have hraw := Gauss.continuous_uker_lkT_omega d 0 N
    (Gauss.window_im_ne_zero (E := 0) (by norm_num) hv.2 (endpoint N k) hr)
    (Gauss.window_norm_mul_lt (E := 0) (by norm_num) (by norm_num)
      hv.2 (endpoint N k) hr)
    Step2.sigPM (xiOf (mSigma 0) Step2.sigPM) a ((endpoint N k : ℝ) : ℂ)
  have heq : Y N k a (endpoint N k) = fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma 0) Step2.sigPM)
        ((endpoint N k : ℝ) : ℂ) ((endpoint N k : ℝ) : ℂ)
        (SumZeroDyn.lkT (Gauss.sample d) 0 N (endpoint N k) ω Step2.sigPM) a‖ /
          APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (endpoint N k) := by
    funext ω
    exact APrimeDriftTimeFamily.flowY_coordAt d 0 60 N Step2.sigPM a
      (by norm_num) hv.1 hv.2 (endpoint N k) ω
  rw [heq]
  exact hraw.norm.div_const _

theorem continuous_familyMax {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) : Continuous (familyMax N k) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun a _ => (continuous_endpoint_Y hτ' hk a).abs)

/-- Continuity of the literal canonical weight at the high order. -/
theorem continuous_highWeight {τ' : ℝ} (hτ' : 0 < τ') {P N k : ℕ}
    (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) : Continuous (weight τ' P N k) := by
  have hm : 1 ≤ canonicalM τ' N :=
    APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    exact (endpoint_bounds hτ' (show j ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N by omega)).2
  exact APrimeSmoothWeightActual.continuous_weight d
    (E := 0) (D := 60) (δ := delta) (s := fun _ => 0)
    (t := firstCellT τ') (mesh := APrimeSmoothTransition.transitionMesh)
    (N₀ := 2) (p := P) (N := N) (k := k) (m := canonicalM τ' N)
    (by norm_num) (by norm_num) hN hm hu

/-- The actual normalized test-function envelope is bounded at fixed size.
This is the bounded sample-envelope argument underlying T451, here applied
before inserting any weight or choosing a moment order for the weight. -/
theorem integrable_endpoint_Y_pow {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2) (p : ℕ) :
    Integrable (fun ω => |Y N k a (endpoint N k) ω| ^ (2 * p)) (Gauss.P d) := by
  have hv := endpoint_bounds hτ' hk
  have hr : endpoint N k ∈ Icc (0 : ℝ) (endpoint N k) := ⟨hv.1, le_rfl⟩
  have htest := APrimeNormalizedTestFun.normalizedTestFunBridge d 0 60 N p
    Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv.2
  obtain ⟨C, hC⟩ := htest.bdd₀
  have heq : (fun ω => |Y N k a (endpoint N k) ω| ^ (2 * p)) =
      fun ω => ‖APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a
        0 (endpoint N k) (endpoint N k) (Gauss.Hflow d N (endpoint N k) ω)‖ := by
    funext ω
    exact APrimeDuhamelModel.abs_flowY_pow_eq_norm
      (APrimeDriftTimeFamily.momentAt_isModulusPow d 0 60 N p
        Step2.sigPM a 0 (endpoint N k)) (endpoint N k) ω
  rw [heq]
  apply Integrable.of_bound
    ((htest.contDiffM (endpoint N k) hr).continuous.comp
      (Gauss.continuous_Hflow d N (endpoint N k))).norm.aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Function.comp_apply, norm_norm] using hC (endpoint N k) hr
      (Gauss.Hflow d N (endpoint N k) ω)

/-- Finite maxima retain all the actual unweighted even moments. -/
theorem integrable_familyMax_pow {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) (p : ℕ) :
    Integrable (fun ω => |familyMax N k ω| ^ (2 * p)) (Gauss.P d) := by
  have h := APrimeFirstCellFamilyHighMoment.integrable_weighted_finsetMax_pow
    (Gauss.P d) (fun _ => 1) (fun a => Y N k a (endpoint N k)) (2 * p)
    (by intro ω; norm_num) (fun a => by
      simpa only [one_mul] using integrable_endpoint_Y_pow hτ' hk a p)
  simpa only [one_mul, familyMax] using h

/-- Every integrability premise of the same-weight Lyapunov inequality is
discharged for the actual maximum and the canonical high-order weight. -/
theorem sameWeight_integrability {τ' : ℝ} (hτ' : 0 < τ') {p P N k : ℕ}
    (hP : 1 ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    Integrable (fun ω => weight τ' P N k ω * |familyMax N k ω| ^ (2 * p))
        (Gauss.P d) ∧
    Integrable (fun ω => weight τ' P N k ω * |familyMax N k ω| ^ (2 * P))
        (Gauss.P d) ∧
    Integrable (fun ω =>
      |weight τ' P N k ω ^ (((2 * P : ℕ) : ℝ)⁻¹) * familyMax N k ω| ^ (2 * p))
        (Gauss.P d) := by
  have hw0 : ∀ ω, 0 ≤ weight τ' P N k ω := fun ω =>
    APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω
  have hw1 : ∀ ω, weight τ' P N k ω ≤ 1 := fun ω =>
    APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω
  have hwc := continuous_highWeight hτ' hN hk (P := P)
  have hfc := continuous_familyMax hτ' hk
  have hi := integrable_familyMax_pow hτ' hk p
  have hlo : Integrable
      (fun ω => weight τ' P N k ω * |familyMax N k ω| ^ (2 * p)) (Gauss.P d) := by
    apply hi.mono' (hwc.mul (hfc.abs.pow (2 * p))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      change ‖weight τ' P N k ω * |familyMax N k ω| ^ (2 * p)‖ ≤
        |familyMax N k ω| ^ (2 * p)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 ω) (by positivity))]
      exact mul_le_of_le_one_left (by positivity) (hw1 ω)
  have hhi : Integrable
      (fun ω => weight τ' P N k ω * |familyMax N k ω| ^ (2 * P)) (Gauss.P d) := by
    exact APrimeFirstCellFamilyHighMoment.integrable_weighted_finsetMax_pow
      (Gauss.P d) (weight τ' P N k) (fun a => Y N k a (endpoint N k))
      (2 * P) hw0 (fun a =>
        (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
          (δ := delta) hτ' hP hN hk a).2.hYi)
  refine ⟨hlo, hhi, ?_⟩
  have hroot : Continuous (fun ω => weight τ' P N k ω ^ (((2 * P : ℕ) : ℝ)⁻¹)) :=
    hwc.rpow_const (fun _ => Or.inr (by positivity))
  apply hi.mono' ((hroot.mul hfc).abs.pow (2 * p)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    change ‖|weight τ' P N k ω ^ (((2 * P : ℕ) : ℝ)⁻¹) *
      familyMax N k ω| ^ (2 * p)‖ ≤ |familyMax N k ω| ^ (2 * p)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (hw0 ω) _)]
    apply pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (hw0 ω) _) (abs_nonneg _))
    exact mul_le_of_le_one_left (abs_nonneg _)
      (Real.rpow_le_one (hw0 ω) (hw1 ω) (by positivity))

/-- Lyapunov monotonicity without any weight change or loss of a constant. -/
theorem sameWeight_momNormW_le {τ' : ℝ} (hτ' : 0 < τ') {p P N k : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    momNormW (Gauss.P d) (weight τ' P N k) p (familyMax N k) ≤
      momNormW (Gauss.P d) (weight τ' P N k) P (familyMax N k) := by
  obtain ⟨hlo, hhi, hzlo⟩ := sameWeight_integrability hτ' (hp.trans hpP) hN hk
    (p := p)
  exact APrimeInit.momNormW_le_momNormW_of_exponent_le hp hpP
    (fun ω => APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω)
    (fun ω => APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω) hlo hhi hzlo

/-- The low-order target explicitly retains the order-`P` canonical weight. -/
def familyLowMomentAt (τ' : ℝ) (p P N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' P N k) p (familyMax N k) ≤
    (N : ℝ) ^ (delta / 2) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

theorem familyLowMomentAt_of_high {τ' : ℝ} (hτ' : 0 < τ') {p P N k : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hhigh : APrimeFirstCellFamilyHighMoment.familyMomentAt τ' P N k) :
    familyLowMomentAt τ' p P N k :=
  (sameWeight_momNormW_le hτ' hp hpP hN hk).trans hhigh

def actualFamilyLowMoment (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N → familyLowMomentAt τ' p P N k

/-- Both orders are fixed before the size threshold, which is uniform in `k`. -/
theorem actualFamilyLowMoment_of_high {τ' : ℝ} (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P)
    (hhigh : APrimeFirstCellFamilyHighMoment.actualFamilyHighMoment τ' P) :
    actualFamilyLowMoment τ' p P := by
  filter_upwards [hhigh, eventually_ge_atTop 1] with N hhighN hN
  intro k hk1 hk
  exact familyLowMomentAt_of_high hτ' hp hpP (by omega) hk (hhighN k hk1 hk)

def kZeroFamilyLowMoment (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧ familyLowMomentAt τ' p P N 0 ∧
      momNormW (Gauss.P d) (weight τ' P N 0) p (familyMax N 0) ≤
        (N : ℝ) ^ (delta / 2)

/-- The same argument includes the separately recorded zero endpoint. -/
theorem kZeroFamilyLowMoment_of_high {τ' : ℝ} (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P)
    (hzero : APrimeFirstCellFamilyHighMoment.kZeroFamilyHighMoment τ' P) :
    kZeroFamilyLowMoment τ' p P := by
  filter_upwards [hzero, eventually_ge_atTop 1] with N hz hN
  have hmono := sameWeight_momNormW_le hτ' hp hpP (show 0 < N by omega)
    (Nat.zero_le (cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N))
  exact ⟨hz.1, hmono.trans hz.2.1, hmono.trans hz.2.2⟩

def positiveTwoFamilyLowMomentResident (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    weight τ' P N 2 ω = 1 ∧ familyLowMomentAt τ' p P N 2

/-- T512's positive resident is retained with the identical high-order weight. -/
theorem positiveTwoFamilyLowMomentResident_of_high {τ' : ℝ} {p P : ℕ}
    (hresident : APrimeFirstCellFamilyHighMoment.positiveTwoFamilyHighMomentResident τ' P)
    (hlow : actualFamilyLowMoment τ' p P) :
    positiveTwoFamilyLowMomentResident τ' p P := by
  filter_upwards [hresident, hlow] with N hr hl
  obtain ⟨ω, hω, hk, hvpos, hvle, hw, _hhigh⟩ := hr
  exact ⟨ω, hω, hk, hvpos, hvle, hw, hl 2 (by norm_num) hk⟩

/-- One T512 parameter and its literal sharp event supply every fixed pair
`1 ≤ p ≤ P`, `P ≥ 8000`, including the zero branch and a positive resident. -/
theorem exists_familyLowMoment_sameWeight_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ p P : ℕ, 1 ≤ p → p ≤ P → 8000 ≤ P →
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N).Nonempty) ∧
      actualFamilyLowMoment τ' p P ∧ kZeroFamilyLowMoment τ' p P ∧
      positiveTwoFamilyLowMomentResident τ' p P := by
  obtain ⟨τ', hτ', hall⟩ := APrimeFirstCellFamilyHighMoment.exists_familyHighMoment_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro p P hp hpP hP
  obtain ⟨hm, hprob, hne, hhigh, hzero, hresident⟩ := hall P hP
  have hlow := actualFamilyLowMoment_of_high hτ' hp hpP hhigh
  exact ⟨hm, hprob, hne, hlow, kZeroFamilyLowMoment_of_high hτ' hp hpP hzero,
    positiveTwoFamilyLowMomentResident_of_high hresident hlow⟩

#print axioms continuous_endpoint_Y
#print axioms continuous_familyMax
#print axioms continuous_highWeight
#print axioms integrable_endpoint_Y_pow
#print axioms integrable_familyMax_pow
#print axioms sameWeight_integrability
#print axioms sameWeight_momNormW_le
#print axioms familyLowMomentAt_of_high
#print axioms actualFamilyLowMoment_of_high
#print axioms kZeroFamilyLowMoment_of_high
#print axioms positiveTwoFamilyLowMomentResident_of_high
#print axioms exists_familyLowMoment_sameWeight_with_resident

end

end RBM.APrimeFirstCellFamilyLowMomentSameWeight
